#include <stdio.h>   // 표준 입출력 함수 (디버깅용 printf 등)
#include <stdlib.h>  // 표준 라이브러리 함수 (여기서는 직접 구현)
#include <unistd.h>  // POSIX API (mem_sbrk 사용 위함)
#include <string.h>  // 문자열/메모리 처리 함수 (memmove 사용 위함)
#include "mm.h"     // 과제용 헤더 파일 (팀 정보 등)
#include "memlib.h" // 메모리 시스템 시뮬레이션 라이브러리 (mem_sbrk 등 제공)

// --- 기본 매크로 ---

#define ALIGNMENT 8         // 메모리 정렬 기준 (8바이트 배수)
#define WSIZE 4             // 워드 크기 (4바이트)
#define DSIZE 8             // 더블 워드 크기 (8바이트). 헤더, 푸터, 포인터 등의 기본 단위.
#define CHUNKSIZE (1<<12)   // 초기 힙 크기 및 힙 확장 시 기본 증가량 (4KB)
// 최소 블록 크기: 헤더(4)+푸터(4)+이전포인터(8)+다음포인터(8) = 24바이트
#define MIN_BLOCK_SIZE (3 * DSIZE)
#define LISTLIMIT 20        // 분리 가용 리스트의 개수

// --- 크기 및 할당 관련 매크로 ---

#define MAX(x, y) ((x) > (y) ? (x) : (y)) // 최대값 구하기
// size를 ALIGNMENT(8)의 가장 가까운 배수로 올림 (비트 연산 활용)
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)
// 크기(size)와 할당 비트(alloc, 0 또는 1)를 합쳐 헤더/푸터 값 생성
#define PACK(size, alloc) ((size) | (alloc))
// 주소 p에서 워드(4바이트) 읽기
#define GET(p) (*(unsigned int *)(p))
// 주소 p에 워드 val 쓰기
#define PUT(p, val) (*(unsigned int *)(p) = (val))
// 주소 p(헤더/푸터)에서 크기 정보 추출 (마지막 3비트는 0으로 만듦)
#define GET_SIZE(p) (GET(p) & ~0x7)
// 주소 p(헤더/푸터)에서 할당 비트(맨 마지막 비트) 추출
#define GET_ALLOC(p) (GET(p) & 0x1)
// 블록 포인터(bp, 페이로드 시작점)로부터 헤더 주소 계산
#define HDRP(bp) ((char *)(bp) - WSIZE)
// 블록 포인터(bp)로부터 푸터 주소 계산 (헤더에서 크기 읽어옴)
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)
// 현재 블록 포인터(bp)로부터 다음 블록 포인터 계산
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)))
// 현재 블록 포인터(bp)로부터 이전 블록 포인터 계산 (이전 블록의 푸터에서 크기 읽어옴)
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))

// --- 가용 리스트 포인터 매크로 --- (명시적 리스트용)
// 가용 블록 bp의 페이로드 시작 위치에 저장된 이전 가용 블록 포인터 값 읽기/쓰기
#define PRED_PTR(bp) (*(void **)(bp))
// 가용 블록 bp의 (페이로드 시작 + DSIZE) 위치에 저장된 다음 가용 블록 포인터 값 읽기/쓰기
#define SUCC_PTR(bp) (*(void **)(bp + DSIZE))

// --- 전역 변수 ---
// 분리 가용 리스트 배열. 각 배열 요소는 해당 크기 클래스의 가용 리스트 시작점(헤드)을 가리킴.
void *segregated_free_lists[LISTLIMIT];

// --- 함수 프로토타입 ---
// (주요 함수들의 선언. 실제 정의는 아래에 나옴)
static void *extend_heap(size_t words);
static int get_list_index(size_t size);
static void insert_node(void *bp, size_t size);
static void delete_node(void *bp);
static void *coalesce(void *bp);
static void *coalesce_case1(void *bp, size_t size);
static void *coalesce_case2(void *bp, size_t size, void* next_bp, size_t next_size);
static void *coalesce_case3(void *bp, size_t size, void* prev_bp, size_t prev_size);
static void *coalesce_case4(void *bp, size_t size, void* prev_bp, size_t prev_size, void* next_bp, size_t next_size);
static void *find_fit(size_t asize);
static void place(void *bp, size_t asize);
static void *mm_realloc_inplace(void *ptr, size_t oldsize, size_t newsize);
static void *mm_realloc_copy(void *ptr, size_t oldsize, size_t size);

// --- 팀 정보 --- (과제 제출용 정보)
team_t team = {
    "seglist_team_refactored", // 팀 이름
    "your_name",              // 이름
    "your_email@example.com", // 이메일
    "",
    ""
};

// --- 메모리 시스템 초기화 ---
int mm_init(void) {
    char *heap_listp; // 힙 시작 주소

    // 1. 모든 분리 가용 리스트를 NULL로 초기화
    for (int i = 0; i < LISTLIMIT; i++) {
        segregated_free_lists[i] = NULL;
    }

    // 2. 힙의 맨 처음에 작은 공간(16바이트) 요청 (패딩 + 프롤로그 + 에필로그용)
    if ((heap_listp = mem_sbrk(4 * WSIZE)) == (void *)-1) {
        return -1; // 메모리 부족 시 실패
    }

    // 3. 초기 힙 구조 설정
    PUT(heap_listp, 0);                            // [0] 패딩 워드 (정렬용)
    PUT(heap_listp + (1 * WSIZE), PACK(DSIZE, 1)); // [4] 프롤로그 헤더 (크기 8, 할당됨)
    PUT(heap_listp + (2 * WSIZE), PACK(DSIZE, 1)); // [8] 프롤로그 푸터 (크기 8, 할당됨)
    PUT(heap_listp + (3 * WSIZE), PACK(0, 1));     // [12] 에필로그 헤더 (크기 0, 할당됨) - 힙의 끝 표시
    // 프롤로그 블록: 힙의 시작 부분 경계 역할. 병합 시 가장자리 처리 간편화.

    // 4. 초기 가용 공간 확보를 위해 힙 확장 (CHUNKSIZE만큼)
    if (extend_heap(CHUNKSIZE / WSIZE) == NULL) {
        return -1; // 힙 확장 실패 시
    }
    return 0; // 초기화 성공
}

// --- 힙 확장 ---
// words: 확장할 크기 (워드 단위)
static void *extend_heap(size_t words) {
    char *bp;      // 새로 확장된 영역의 블록 포인터
    size_t size;   // 실제 확장할 바이트 크기 (정렬됨)

    // 1. 요청 크기(words)를 짝수 워드로 만들고 바이트 단위로 변환 (8바이트 정렬 유지)
    size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;

    // 2. mem_sbrk 시스템 콜로 힙 크기 늘림
    if ((long)(bp = mem_sbrk(size)) == -1) {
        return NULL; // 메모리 부족 시 실패
    }

    // 3. 새로 생긴 영역을 가용 블록으로 초기화
    PUT(HDRP(bp), PACK(size, 0));             // 새 가용 블록 헤더 (크기 size, 가용 상태 0)
    PUT(FTRP(bp), PACK(size, 0));             // 새 가용 블록 푸터 (크기 size, 가용 상태 0)
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1));   // 새 에필로그 헤더 (원래 에필로그 헤더 위치 덮어씀)

    // 4. 만약 이전 블록이 가용 상태였다면, 새로 만든 블록과 병합
    //    (extend_heap 직전의 블록이 free 상태일 수 있음)
    return coalesce(bp); // 병합된 블록 (또는 원래 블록)의 포인터 반환
}

// --- 리스트 인덱스 계산 헬퍼 ---
// 주어진 크기(size)가 어떤 분리 리스트에 속하는지 계산
static int get_list_index(size_t size) {
    int list_idx = 0;
    // size를 2로 계속 나누면서 인덱스를 증가 (대략 로그 스케일)
    // 예: size 1~2 -> idx 0, 3~4 -> idx 1, 5~8 -> idx 2 ...
    // LISTLIMIT-1 까지만 계산 (마지막 리스트는 나머지 큰 블록들 모두 포함)
    while ((list_idx < LISTLIMIT - 1) && (size > 1)) {
        size >>= 1; // size = size / 2
        list_idx++;
    }
    return list_idx;
}

// --- 가용 블록 리스트에 노드 삽입 (크기 오름차순) ---
// bp: 삽입할 가용 블록, size: 블록 크기
static void insert_node(void *bp, size_t size) {
    int list_idx = get_list_index(size); // 적절한 리스트 인덱스 찾기
    void *search_ptr = segregated_free_lists[list_idx]; // 해당 리스트 시작점부터 탐색
    void *insert_prev = NULL; // 삽입 위치의 이전 노드를 기억할 포인터

    // 1. 리스트 내에서 크기 순서에 맞는 삽입 위치 찾기
    //    (현재 블록(bp)의 size보다 크거나 같은 블록을 만날 때까지 이동)
    while ((search_ptr != NULL) && (size > GET_SIZE(HDRP(search_ptr)))) {
        insert_prev = search_ptr;
        search_ptr = SUCC_PTR(search_ptr); // 다음 노드로
    }

    // 2. 찾은 위치에 bp 삽입 (4가지 경우 처리 - 리스트 맨 앞, 중간, 맨 뒤, 빈 리스트)
    if (search_ptr != NULL) { // 중간 또는 맨 앞에 삽입
        if (insert_prev != NULL) { // 중간 삽입 (insert_prev와 search_ptr 사이)
            SUCC_PTR(bp) = search_ptr;
            PRED_PTR(bp) = insert_prev;
            PRED_PTR(search_ptr) = bp;
            SUCC_PTR(insert_prev) = bp;
        } else { // 맨 앞에 삽입 (list_head가 search_ptr)
            SUCC_PTR(bp) = search_ptr;
            PRED_PTR(bp) = NULL;
            PRED_PTR(search_ptr) = bp;
            segregated_free_lists[list_idx] = bp; // 리스트 헤드 변경
        }
    } else { // 맨 뒤 또는 빈 리스트에 삽입
        if (insert_prev != NULL) { // 맨 뒤 삽입 (insert_prev 다음)
            SUCC_PTR(bp) = NULL;
            PRED_PTR(bp) = insert_prev;
            SUCC_PTR(insert_prev) = bp;
        } else { // 빈 리스트에 삽입 (list_head가 NULL)
            SUCC_PTR(bp) = NULL;
            PRED_PTR(bp) = NULL;
            segregated_free_lists[list_idx] = bp; // 리스트 헤드 변경
        }
    }
}

// --- 가용 블록 리스트에서 노드 삭제 ---
// bp: 삭제할 가용 블록
static void delete_node(void *bp) {
    int list_idx = get_list_index(GET_SIZE(HDRP(bp))); // 해당 리스트 인덱스 찾기
    void *prev_fp = PRED_PTR(bp); // 삭제할 노드의 이전 노드
    void *next_fp = SUCC_PTR(bp); // 삭제할 노드의 다음 노드

    // 이전 노드 처리
    if (prev_fp == NULL) { // 삭제할 노드가 리스트의 헤드인 경우
        segregated_free_lists[list_idx] = next_fp; // 리스트 헤드를 다음 노드로 변경
    } else { // 삭제할 노드가 중간 또는 꼬리인 경우
        SUCC_PTR(prev_fp) = next_fp; // 이전 노드가 다음 노드를 가리키도록 변경
    }

    // 다음 노드 처리 (삭제할 노드가 꼬리가 아닌 경우)
    if (next_fp != NULL) {
        PRED_PTR(next_fp) = prev_fp; // 다음 노드가 이전 노드를 가리키도록 변경
    }
    // bp 내부의 PRED/SUCC 포인터는 이제 업데이트할 필요 없음 (어차피 사용 안 함)
}

// --- 인접 가용 블록 병합 (Dispatcher 역할) ---
// bp: 현재 (막 해제되었거나 새로 생성된) 가용 블록
static void *coalesce(void *bp) {
    // 이전/다음 블록 정보 확인
    void *prev_footer = FTRP(PREV_BLKP(bp)); // 이전 블록 푸터 (정확히는 bp 시작 - DSIZE)
    void *next_header = HDRP(NEXT_BLKP(bp)); // 다음 블록 헤더
    size_t prev_alloc = GET_ALLOC(prev_footer); // 이전 블록 할당 상태
    size_t next_alloc = GET_ALLOC(next_header); // 다음 블록 할당 상태
    size_t size = GET_SIZE(HDRP(bp));           // 현재 블록 크기

    // 이전/다음 블록의 할당 상태에 따라 4가지 경우로 나누어 처리
    if (prev_alloc && next_alloc) {         // Case 1: 둘 다 할당됨 (병합 없음)
        return coalesce_case1(bp, size);
    }
    else if (prev_alloc && !next_alloc) { // Case 2: 다음 블록만 가용
        void *next_bp = NEXT_BLKP(bp);
        size_t next_size = GET_SIZE(HDRP(next_bp));
        return coalesce_case2(bp, size, next_bp, next_size);
    }
    else if (!prev_alloc && next_alloc) { // Case 3: 이전 블록만 가용
        void *prev_bp = PREV_BLKP(bp);
        size_t prev_size = GET_SIZE(HDRP(prev_bp)); // 이전 블록 헤더에서 크기 읽기
        return coalesce_case3(bp, size, prev_bp, prev_size);
    }
    else {                                // Case 4: 둘 다 가용
        void *prev_bp = PREV_BLKP(bp);
        void *next_bp = NEXT_BLKP(bp);
        size_t prev_size = GET_SIZE(HDRP(prev_bp));
        size_t next_size = GET_SIZE(HDRP(next_bp));
        return coalesce_case4(bp, size, prev_bp, prev_size, next_bp, next_size);
    }
}

// --- Coalesce Helper: Case 1 (병합 없음) ---
static void *coalesce_case1(void *bp, size_t size) {
    // 현재 블록(bp)을 가용 리스트에 삽입하기만 함
    insert_node(bp, size);
    return bp; // 현재 블록 포인터 반환
}

// --- Coalesce Helper: Case 2 (다음 블록과 병합) ---
static void *coalesce_case2(void *bp, size_t size, void* next_bp, size_t next_size) {
    delete_node(next_bp);          // 다음 블록을 리스트에서 제거
    size += next_size;             // 크기 합산
    PUT(HDRP(bp), PACK(size, 0));  // 현재 블록 헤더 업데이트
    PUT(FTRP(bp), PACK(size, 0));  // 현재 블록 푸터 업데이트 (새 크기 기준)
    insert_node(bp, size);         // 병합된 블록을 리스트에 삽입
    return bp;                     // 병합된 블록 시작(bp) 반환
}

// --- Coalesce Helper: Case 3 (이전 블록과 병합) ---
static void *coalesce_case3(void *bp, size_t size, void* prev_bp, size_t prev_size) {
    delete_node(prev_bp);          // 이전 블록을 리스트에서 제거
    size += prev_size;             // 크기 합산
    PUT(HDRP(prev_bp), PACK(size, 0)); // 이전 블록 헤더 업데이트
    PUT(FTRP(bp), PACK(size, 0));     // *현재 블록의 푸터* 위치에 새 크기로 업데이트
    insert_node(prev_bp, size);    // 병합된 블록을 리스트에 삽입
    return prev_bp;                // 병합된 블록 시작(prev_bp) 반환
}

// --- Coalesce Helper: Case 4 (양쪽 블록과 병합) ---
static void *coalesce_case4(void *bp, size_t size, void* prev_bp, size_t prev_size, void* next_bp, size_t next_size) {
    delete_node(prev_bp);          // 이전 블록 제거
    delete_node(next_bp);          // 다음 블록 제거
    size += prev_size + next_size; // 세 블록 크기 합산
    PUT(HDRP(prev_bp), PACK(size, 0)); // 이전 블록 헤더 업데이트
    PUT(FTRP(next_bp), PACK(size, 0)); // *다음 블록의 푸터* 위치에 새 크기로 업데이트
    insert_node(prev_bp, size);    // 병합된 블록을 리스트에 삽입
    return prev_bp;                // 병합된 블록 시작(prev_bp) 반환
}


// --- 메모리 할당 ---
void *mm_malloc(size_t size) {
    size_t asize;      // 실제 할당할 블록 크기 (오버헤드 + 정렬)
    size_t extendsize; // 힙 확장 시 크기
    void *bp = NULL;   // 찾거나 할당된 블록 포인터

    if (size == 0) return NULL; // 요청 크기 0이면 NULL

    // 1. 실제 필요한 크기(asize) 계산
    if (size <= (2 * DSIZE)) { // 요청 페이로드가 작으면(16바이트 이하)
        asize = MIN_BLOCK_SIZE; // 최소 블록 크기(24바이트) 할당 (포인터 저장 공간 확보)
    } else {
        // 헤더/푸터(DSIZE) 추가하고 8바이트 정렬
        asize = ALIGN(size + DSIZE);
    }

    // 2. 가용 리스트에서 적합한 블록 검색 (First Fit)
    if ((bp = find_fit(asize)) != NULL) {
        place(bp, asize); // 블록 배치(할당 및 분할)
        return bp;        // 할당된 블록의 페이로드 시작 주소 반환
    }

    // 3. 적합한 블록 없으면 힙 확장
    extendsize = MAX(asize, CHUNKSIZE); // 요청 크기와 CHUNKSIZE 중 큰 값으로 확장
    if ((bp = extend_heap(extendsize / WSIZE)) == NULL) {
        return NULL; // 힙 확장 실패
    }
    place(bp, asize); // 새로 확장된 공간에 블록 배치
    return bp;
}

// --- 적합한 가용 블록 찾기 (First Fit) ---
// asize: 필요한 블록 크기 (정렬됨)
static void *find_fit(size_t asize) {
    int list_idx = get_list_index(asize); // 검색 시작할 리스트 인덱스
    void *bp;

    // 해당 크기 클래스 리스트부터 시작해서 더 큰 크기의 리스트까지 순차 탐색
    for (; list_idx < LISTLIMIT; list_idx++) {
        // 현재 리스트 내의 블록들을 순회
        for (bp = segregated_free_lists[list_idx]; bp != NULL; bp = SUCC_PTR(bp)) {
            // 현재 블록 크기가 요청 크기(asize)보다 크거나 같으면
            if (GET_SIZE(HDRP(bp)) >= asize) {
                return bp; // 첫 번째로 찾은 블록 반환 (First Fit)
            }
        }
    }
    return NULL; // 모든 리스트를 다 찾아도 없으면 NULL 반환
}

// --- 블록 할당 및 분할 ---
// bp: find_fit으로 찾은 가용 블록, asize: 할당할 크기
static void place(void *bp, size_t asize) {
    size_t csize = GET_SIZE(HDRP(bp)); // 찾은 가용 블록의 전체 크기

    // 1. 이 블록은 이제 할당될 것이므로 가용 리스트에서 제거
    delete_node(bp);

    // 2. 블록 분할 결정: 남는 공간이 최소 블록 크기 이상인가?
    if ((csize - asize) >= MIN_BLOCK_SIZE) {
        // 분할 수행
        // a) 앞부분: asize만큼 할당 상태로 설정
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));
        // b) 뒷부분: 나머지(csize - asize)는 새로운 가용 블록으로 설정
        void *next_bp = NEXT_BLKP(bp); // 나머지 블록 시작점
        size_t remainder_size = csize - asize;
        PUT(HDRP(next_bp), PACK(remainder_size, 0));
        PUT(FTRP(next_bp), PACK(remainder_size, 0));
        // c) 새로 생긴 가용 블록(next_bp)을 가용 리스트에 추가
        insert_node(next_bp, remainder_size); // 정렬된 위치에 삽입
    }
    // 3. 분할하지 않는 경우: 블록 전체를 할당 상태로 설정
    else {
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
    }
}

// --- 메모리 해제 ---
// bp: 해제할 블록 포인터
void mm_free(void *bp) {
    if (bp == NULL) return; // NULL 포인터 해제 시 무시

    size_t size = GET_SIZE(HDRP(bp)); // 블록 크기 확인

    // 헤더와 푸터를 가용 상태(0)로 변경
    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));

    // 인접 블록과 병합 시도 및 가용 리스트에 추가
    coalesce(bp);
}

// --- 메모리 재할당 (Dispatcher 역할) ---
// ptr: 재할당할 메모리 블록, size: 새로운 요청 데이터 크기
void *mm_realloc(void *ptr, size_t size) {
    // 특별한 경우 처리
    if (ptr == NULL) return mm_malloc(size); // ptr이 NULL이면 malloc과 동일
    if (size == 0) { mm_free(ptr); return NULL; } // size가 0이면 free와 동일

    void *oldptr = ptr;
    size_t oldsize = GET_SIZE(HDRP(oldptr)); // 원래 블록의 전체 크기
    size_t newsize; // 새로 필요한 블록의 전체 크기 (정렬됨)

    // 1. 새로 필요한 전체 크기(newsize) 계산
    if (size <= (2 * DSIZE)) {
        newsize = MIN_BLOCK_SIZE;
    } else {
        newsize = ALIGN(size + DSIZE);
    }

    // 2. 크기 변경 경우 처리
    // Case A: 새 크기가 원래 크기보다 작거나 같은 경우 (축소 또는 동일)
    if (newsize <= oldsize) {
        // TODO: 이 부분은 최적화 가능. 만약 oldsize - newsize >= MIN_BLOCK_SIZE 이면,
        //       블록을 newsize로 줄이고 남는 부분을 분할하여 mm_free 처리 가능.
        //       현재 코드는 분할 없이 그냥 원래 포인터 반환. 메모리 사용률 손해 가능성.
        return ptr; // 데이터 이동 불필요. 그냥 기존 포인터 반환.
    }
    // Case B: 새 크기가 원래 크기보다 큰 경우 (확장)
    else {
        // B-1: 인접 블록(다음 블록) 병합으로 해결 가능한지 시도 (데이터 이동 없음)
        void *new_ptr_inplace = mm_realloc_inplace(ptr, oldsize, newsize);
        if (new_ptr_inplace != NULL) {
            return new_ptr_inplace; // 병합 성공 시 확장된 포인터 반환
        }
        // B-2: 인접 병합 실패 시, 새로 할당하고 데이터 복사
        else {
            // mm_realloc_copy가 malloc, memmove, free를 수행
            return mm_realloc_copy(ptr, oldsize, size); // size는 사용자 요청 크기
        }
    }
}

// --- Realloc Helper: 인접 병합 시도 (다음 블록만 확인) ---
// ptr: 현재 블록, oldsize: 현재 블록 크기, newsize: 필요한 새 크기
static void *mm_realloc_inplace(void *ptr, size_t oldsize, size_t newsize) {
    void *next_bp = NEXT_BLKP(ptr); // 다음 블록
    size_t next_alloc = GET_ALLOC(HDRP(next_bp)); // 다음 블록 할당 상태
    size_t next_size = GET_SIZE(HDRP(next_bp)); // 다음 블록 크기
    size_t combined_size = oldsize + next_size; // 합쳤을 때 크기

    // 다음 블록이 가용 상태이고, 합친 크기가 요구 크기(newsize) 이상이면 병합
    if (!next_alloc && combined_size >= newsize) {
        delete_node(next_bp); // 다음 블록을 가용 리스트에서 제거
        // 현재 블록(ptr)의 헤더/푸터를 합친 크기로 업데이트 (할당 상태 1 유지)
        PUT(HDRP(ptr), PACK(combined_size, 1));
        PUT(FTRP(ptr), PACK(combined_size, 1)); // FTRP(ptr) 사용!

        // TODO: 여기서도 병합 후 남는 공간 (combined_size - newsize)이 충분하면
        //       분할하여 가용화하는 최적화 가능 (place 함수 로직 참고).

        return ptr; // 병합 성공, 원래 포인터 반환
    }

    // TODO: 이전 블록이 가용 상태일 때 병합 시도 로직 추가 가능 (단, 데이터 이동 필요)
    //       이 코드에는 구현되어 있지 않음.

    return NULL; // 다음 블록 병합으로 해결 불가
}

// --- Realloc Helper: 새로 할당 및 복사 ---
// ptr: 원래 블록, oldsize: 원래 블록 전체 크기, size: 사용자 요청 새 데이터 크기
static void *mm_realloc_copy(void *ptr, size_t oldsize, size_t size) {
    // 1. 새 크기(size)만큼 새 블록 할당
    void *newptr = mm_malloc(size);
    if (newptr == NULL) return NULL; // 할당 실패

    // 2. 복사할 데이터 크기 계산
    size_t copySize = oldsize - DSIZE; // 원래 페이로드 크기
    if (size < copySize) copySize = size; // 새 요청 크기가 더 작으면 그만큼만 복사

    // 3. 데이터 복사 (원래 블록 -> 새 블록)
    //    memmove 사용 (memcpy도 가능하나, memmove가 겹치는 영역도 안전하게 처리)
    memmove(newptr, ptr, copySize);

    // 4. 원래 블록 해제
    mm_free(ptr);

    // 5. 새로 할당된 블록 포인터 반환
    return newptr;
}

/*
 * mm-naive.c - The fastest, least memory-efficient malloc package.
 *
 * In this naive approach, a block is allocated by simply incrementing
 * the brk pointer.  A block is pure payload. There are no headers or
 * footers.  Blocks are never coalesced or reused. Realloc is
 * implemented directly using mm_malloc and mm_free.
 *
 * NOTE TO STUDENTS: Replace this header comment with your own header
 * comment that gives a high level description of your solution.
 */
// #include <stdio.h>
// #include <stdlib.h>
// #include <assert.h>
// #include <unistd.h>
// #include <string.h>

// #include "mm.h"
// #include "memlib.h"

// int mm_init(void);
// static void *extend_heap(size_t words);
// void *mm_malloc(size_t size);
// void mm_free(void *bp);
// static void *coalesce(void *bp);
// static void *find_fit(size_t asize);
// static void place(void *bp, size_t asize);
// void *mm_realloc(void *ptr, size_t size);


// static char *heap_listp = 0; //힙 블록 탐색 시작 포인터

// /* Basic constants and macros */

// /* single word (4) or double word (8) alignment */
// #define ALIGNMENT 8 //8바이트 배수 정렬

// /* rounds up to the nearest multiple of ALIGNMENT */
// #define ALIGN(size) (((size) + (ALIGNMENT - 1)) & ~0x7) //어떤 size라도 8의 배수로 올려줌

// #define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

// #define WSIZE       4       // 워드 크기: 헤더/풋터 4바이트
// #define DSIZE       8       // 더블 워드 크기: 8바이트
// #define CHUNKSIZE  (1<<12)  // 힙 확장 단위(4096바이트)

// #define MAX(x, y)  ((x) > (y) ? (x) : (y)) // 둘 중 큰 값 리턴

// /* Pack a size and allocated bit into a word */
// #define PACK(size, alloc)  ((size) | (alloc)) // 헤더/풋터 워드에 (블록 크기)|(할당 비트) 를 합쳐 저장
// 											  // alloc 은 0 or 1
// /* Read and write a word at address p */
// // 워드 단위로 읽고 쓰기
// #define GET(p)       (*(unsigned int *)(p))
// #define PUT(p, val)  (*(unsigned int *)(p) = (val))

// /* Read the size and allocated fields from address p */
// // 워드에서 크기(상위 비트)와 할당 여부(하위 비트) 추출
// #define GET_SIZE(p)  (GET(p) & ~0x7)
// #define GET_ALLOC(p) (GET(p) & 0x1)

// /* Given block ptr bp, compute address of its header and footer */
// #define HDRP(bp)  ((char *)(bp) - WSIZE) // payload 포인터 bp 에서 4바이트 앞에 있는 헤더 주소 계산
// #define FTRP(bp)  ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE) // payload 끝(bp + size)에서 8바이트 앞에 있는 풋터 주소 계산

// /* Given block ptr bp, compute address of next and previous blocks */
// #define NEXT_BLKP(bp)  ((char *)(bp) + GET_SIZE((char *)(bp) - WSIZE)) // 현재 블록 크기만큼 payload 포인터를 앞으로 이동 → 다음 블록의 payload 시작
// #define PREV_BLKP(bp)  ((char *)(bp) - GET_SIZE((char *)(bp) - DSIZE)) // (풋터-헤더)를 통해 이전 블록으로 이동



// /*********************************************************
//  * NOTE TO STUDENTS: Before you do anything else, please
//  * provide your team information in the following struct.
//  ********************************************************/
// team_t team = {
//     /* Team name */
//     "6",
//     /* First member's full name */
//     "Harry Bovik",
//     /* First member's email address */
//     "bovik@cs.cmu.edu",
//     /* Second member's full name (leave blank if none) */
//     "",
//     /* Second member's email address (leave blank if none) */
//     ""};

// /*
//  * mm_init - initialize the malloc package.
//  */
// int mm_init(void)
// {
	
// 	heap_listp = mem_sbrk(4 * WSIZE); // mem_sbrk(16) 호출해 힙 시작 부분에 16바이트(4 워드) 확보
// 	if(heap_listp == (void *)-1) return -1; 

// 	PUT(heap_listp, 0); //워드0: 패딩(0)
// 	PUT(heap_listp + (1*WSIZE), PACK(DSIZE, 1)); //워드1: 프로로그 헤더(크기=8, 할당)
// 	PUT(heap_listp + (2*WSIZE), PACK(DSIZE, 1)); //워드2: 프로로그 풋터(크기=8, 할당)
// 	PUT(heap_listp + (3*WSIZE), PACK(0, 1)); //워드3: 에필로그 헤더(크기=0, 할당)
// 	heap_listp += (2*WSIZE); //heap_listp 를 프로로그 풋터(실제 첫 가용 블록 payload 시작)로 옮김

// 	if(extend_heap(CHUNKSIZE/WSIZE) == NULL) {return 1;} //첫 가용 블록으로 4096바이트 extend
// 	//1024워드 = 4096바이트
//     return 0;
// }

// static void *extend_heap(size_t words)
// {
// 	char *bp;

// 	size_t size = (words %2) ? (words+1) * WSIZE : words *WSIZE; //짝수 워드로 맞춰 바이트 계산
// 	if((long)(bp = mem_sbrk(size)) == - 1) return NULL;

// 	// 새로 확장된 영역을 free 블록으로 초기화
// 	PUT(HDRP(bp), PACK(size, 0));			//free 헤더
// 	PUT(FTRP(bp), PACK(size, 0));			//free 풋터
// 	PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1));	//새 에필로그 헤더(크기=0, alloc=1) 추가

// 	return coalesce(bp); //이전 블록이 free 면 합쳐 주고, 합친 블록의 포인터 리턴
// }
// /*
//  * mm_malloc - Allocate a block by incrementing the brk pointer.
//  *     Always allocate a block whose size is a multiple of the alignment.
//  */
// void *mm_malloc(size_t size)
// {
// 	if (size == 0) return NULL;
//   // 1) 요청 크기 조정: 헤더+풋터(8) + 8 정렬 최소 단위
// 	size_t asize = (size <= DSIZE ? 2*DSIZE  			 //데이터 + 헤더·풋터 오버헤드(8B) 포함, 8바이트 배수로 올림, 
// 		: DSIZE * ((size + (DSIZE-1) + DSIZE) / DSIZE)); //최소 16B
		
//   // 2) 가용 리스트(first-fit) 탐색
// 	char *bp;
// 	if ((bp = find_fit(asize)) != NULL) { //first‐fit 으로 가용 리스트 탐색 → 
// 	place(bp, asize);					  //블록 발견 시 place 후 반환
// 	return bp;
// 	}

//   // 3) 없으면 힙 확장 후 place
// 	size_t extendsize = MAX(asize, CHUNKSIZE);
// 	if ((bp = extend_heap(extendsize/WSIZE)) == NULL) return NULL;
//   	place(bp, asize);
// 	return bp;  
// }

// /*
//  * mm_free - Freeing a block does nothing.
//  */
// void mm_free(void *bp)
// {
// 	size_t size = GET_SIZE(HDRP(bp));
// 	//헤더·풋터에 alloc=0 로 표시 → free
// 	PUT(HDRP(bp), PACK(size, 0));
// 	PUT(FTRP(bp), PACK(size, 0));
// 	//coalesce 호출해 인접 free 블록들과 합침
// 	coalesce(bp);
// }

// static void *coalesce(void *bp)
// {
// 	//앞/뒤 블록의 alloc 상태 확인
// 	size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
// 	size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
// 	size_t size = GET_SIZE(HDRP(bp)); // 현재 블록 크기 읽기

// 	if (prev_alloc && next_alloc)       return bp;               	// Case 1: 앞뒤 모두 할당 → 변화 없음

// 	if (prev_alloc && !next_alloc) 									// Case 2: 뒤쪽 free → 뒤 블록만 흡수
// 	{                              
// 	size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
//     PUT(HDRP(bp), PACK(size,0));  PUT(FTRP(bp), PACK(size,0));
//     return bp;
//   	}

//   	if (!prev_alloc && next_alloc) 									// Case 3: 앞쪽 free → 앞 블록만 흡수
// 	{                              
//     size += GET_SIZE(HDRP(PREV_BLKP(bp)));
//     bp = PREV_BLKP(bp);
//     PUT(HDRP(bp), PACK(size,0));  PUT(FTRP(bp), PACK(size,0));
//     return bp;
//   	}
  
//   	size += GET_SIZE(HDRP(PREV_BLKP(bp)))							// Case 4: 앞뒤 모두 free → 세 블록 합쳐 하나로
//     	  + GET_SIZE(FTRP(NEXT_BLKP(bp)));
//   	bp = PREV_BLKP(bp);
//   	PUT(HDRP(bp), PACK(size,0));  PUT(FTRP(bp), PACK(size,0));
//   	return bp;
// }

// static void *find_fit(size_t asize) //frist_fit							//힙 시작에서 에필로그 전까지 선형 탐색
// {
// 	void *bp;

// 	for(bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)){ //힙 시작(heap_listp)부터 에필로그 전까지 순차 탐색
// 		if(!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp)))) {	  //free 이면서 크기 충분한 첫 블록 리턴. 없으면 NULL
// 			return bp;
// 		}
// 	}
// 	return NULL;
// }



// static void place(void *bp, size_t asize) //블록 분할, 할당
// {
// 	size_t csize = GET_SIZE(HDRP(bp));

// 	if((csize - asize) >= (2*DSIZE)) { //여유 공간이 최소 16B 이상이면 “할당·남은 free” 두 블록으로 분할
// 		// 분할 가능
// 		PUT(HDRP(bp), PACK(asize , 1));
// 		PUT(FTRP(bp), PACK(asize, 1));
// 		bp = NEXT_BLKP(bp);
// 		PUT(HDRP(bp), PACK(csize-asize, 0));
// 		PUT(FTRP(bp), PACK(csize-asize, 0));
// 	}
// 	else {
// 		// 분할 여유 없으면 전체 할당
// 		PUT(HDRP(bp), PACK(csize, 1));
// 		PUT(FTRP(bp), PACK(csize, 1));
// 	}
// }
// /*
//  * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
//  */
// void *mm_realloc(void *ptr, size_t size) {		//메모리 재할당 improve raalloc
//     if (ptr == NULL) return mm_malloc(size);	//ptr이 NULL이면 malloc와 같음
//     if (size == 0) {							//size가 0이면 메모리 헤재하고 아무것도 안돌려줌
//         mm_free(ptr);
//         return NULL;
//     }

//     void *oldptr = ptr;							//기존 포인터 oldptr로 백업
//     size_t oldsize = GET_SIZE(HDRP(oldptr));	//현재 블록의 전체 크기(=헤더에 기록된 값)
//     size_t newsize = ALIGN(size + DSIZE);  // header + footer(8바이트) 포함 정렬

//     // Case 1: 요청 크기가 기존보다 작거나 같으면 그대로 사용
//     if (newsize <= oldsize) { 
//         return ptr;
//     }

//     // Case 2: 뒤 블록이 free이고, 현재 크기 + 다음 블록 크기 ≥ 새 요청 크기
//     void *next = NEXT_BLKP(oldptr);
//     if (!GET_ALLOC(HDRP(next)) && (oldsize + GET_SIZE(HDRP(next))) >= newsize) {
//         size_t total = oldsize + GET_SIZE(HDRP(next));
//         PUT(HDRP(oldptr), PACK(total, 1)); //헤더에 병합된 블록 크기를 할당 상태로 기록
//         PUT(FTRP(oldptr), PACK(total, 1)); //풋터에 병합된 블록 크기를 할당 상태로 기록
//         return oldptr;					   //블록 이동 없이 확장 성공 : 기존 포인터 그대로 반환
//     }

//     // Case 3: 새로 malloc하고 복사 후 old block free
//     void *newptr = mm_malloc(size);
//     if (newptr == NULL) return NULL; //메모리 부족이면 그냥 NULL 리턴

//     size_t copySize = oldsize - DSIZE;  // 실제 payload만 복사
//     if (size < copySize) copySize = size; //요청한 size가 더 작다면, size만큼만 복사

//     memmove(newptr, oldptr, copySize); //내용 복사
//     mm_free(oldptr);				   //원래 메모리 필요 없으니 해제
//     return newptr;
// }