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
#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>
#include <string.h>

#include "mm.h"
#include "memlib.h"

int mm_init(void);
static void *extend_heap(size_t words);
void *mm_malloc(size_t size);
void mm_free(void *bp);
static void *coalesce(void *bp);
static void *find_fit(size_t asize);
static void place(void *bp, size_t asize);
void *mm_realloc(void *ptr, size_t size);


static char *heap_listp = 0; //힙 블록 탐색 시작 포인터

/* Basic constants and macros */

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8 //8바이트 배수 정렬

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT - 1)) & ~0x7) //어떤 size라도 8의 배수로 올려줌

#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

#define WSIZE       4       // 워드 크기: 헤더/풋터 4바이트
#define DSIZE       8       // 더블 워드 크기: 8바이트
#define CHUNKSIZE  (1<<12)  // 힙 확장 단위(4096바이트)

#define MAX(x, y)  ((x) > (y) ? (x) : (y)) // 둘 중 큰 값 리턴

/* Pack a size and allocated bit into a word */
#define PACK(size, alloc)  ((size) | (alloc)) // 헤더/풋터 워드에 (블록 크기)|(할당 비트) 를 합쳐 저장
											  // alloc 은 0 or 1
/* Read and write a word at address p */
// 워드 단위로 읽고 쓰기
#define GET(p)       (*(unsigned int *)(p))
#define PUT(p, val)  (*(unsigned int *)(p) = (val))

/* Read the size and allocated fields from address p */
// 워드에서 크기(상위 비트)와 할당 여부(하위 비트) 추출
#define GET_SIZE(p)  (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)

/* Given block ptr bp, compute address of its header and footer */
#define HDRP(bp)  ((char *)(bp) - WSIZE) // payload 포인터 bp 에서 4바이트 앞에 있는 헤더 주소 계산
#define FTRP(bp)  ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE) // payload 끝(bp + size)에서 8바이트 앞에 있는 풋터 주소 계산

/* Given block ptr bp, compute address of next and previous blocks */
#define NEXT_BLKP(bp)  ((char *)(bp) + GET_SIZE((char *)(bp) - WSIZE)) // 현재 블록 크기만큼 payload 포인터를 앞으로 이동 → 다음 블록의 payload 시작
#define PREV_BLKP(bp)  ((char *)(bp) - GET_SIZE((char *)(bp) - DSIZE)) // (풋터-헤더)를 통해 이전 블록으로 이동



/*********************************************************
 * NOTE TO STUDENTS: Before you do anything else, please
 * provide your team information in the following struct.
 ********************************************************/
team_t team = {
    /* Team name */
    "6",
    /* First member's full name */
    "Harry Bovik",
    /* First member's email address */
    "bovik@cs.cmu.edu",
    /* Second member's full name (leave blank if none) */
    "",
    /* Second member's email address (leave blank if none) */
    ""};

/*
 * mm_init - initialize the malloc package.
 */
int mm_init(void)
{
	
	heap_listp = mem_sbrk(4 * WSIZE); // mem_sbrk(16) 호출해 힙 시작 부분에 16바이트(4 워드) 확보
	if(heap_listp == (void *)-1) return -1; 

	PUT(heap_listp, 0); //워드0: 패딩(0)
	PUT(heap_listp + (1*WSIZE), PACK(DSIZE, 1)); //워드1: 프로로그 헤더(크기=8, 할당)
	PUT(heap_listp + (2*WSIZE), PACK(DSIZE, 1)); //워드2: 프로로그 풋터(크기=8, 할당)
	PUT(heap_listp + (3*WSIZE), PACK(0, 1)); //워드3: 에필로그 헤더(크기=0, 할당)
	heap_listp += (2*WSIZE); //heap_listp 를 프로로그 풋터(실제 첫 가용 블록 payload 시작)로 옮김

	if(extend_heap(CHUNKSIZE/WSIZE) == NULL) {return 1;} //첫 가용 블록으로 4096바이트 extend
	//1024워드 = 4096바이트
    return 0;
}

static void *extend_heap(size_t words)
{
	char *bp;

	size_t size = (words %2) ? (words+1) * WSIZE : words *WSIZE; //짝수 워드로 맞춰 바이트 계산
	if((long)(bp = mem_sbrk(size)) == - 1) return NULL;

	// 새로 확장된 영역을 free 블록으로 초기화
	PUT(HDRP(bp), PACK(size, 0));			//free 헤더
	PUT(FTRP(bp), PACK(size, 0));			//free 풋터
	PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1));	//새 에필로그 헤더(크기=0, alloc=1) 추가

	return coalesce(bp); //이전 블록이 free 면 합쳐 주고, 합친 블록의 포인터 리턴
}
/*
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size)
{
	if (size == 0) return NULL;
  // 1) 요청 크기 조정: 헤더+풋터(8) + 8 정렬 최소 단위
	size_t asize = (size <= DSIZE ? 2*DSIZE  			 //데이터 + 헤더·풋터 오버헤드(8B) 포함, 8바이트 배수로 올림, 
		: DSIZE * ((size + (DSIZE-1) + DSIZE) / DSIZE)); //최소 16B

  // 2) 가용 리스트(first-fit) 탐색
	char *bp;
	if ((bp = find_fit(asize)) != NULL) { //first‐fit 으로 가용 리스트 탐색 → 
	place(bp, asize);					  //블록 발견 시 place 후 반환
	return bp;
	}

  // 3) 없으면 힙 확장 후 place
	size_t extendsize = MAX(asize, CHUNKSIZE);
	if ((bp = extend_heap(extendsize/WSIZE)) == NULL) return NULL;
  	place(bp, asize);
	return bp;  
}

/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *bp)
{
	size_t size = GET_SIZE(HDRP(bp));
	//헤더·풋터에 alloc=0 로 표시 → free
	PUT(HDRP(bp), PACK(size, 0));
	PUT(FTRP(bp), PACK(size, 0));
	//coalesce 호출해 인접 free 블록들과 합침
	coalesce(bp);
}

static void *coalesce(void *bp)
{
	//앞/뒤 블록의 alloc 상태 확인
	size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
	size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
	size_t size = GET_SIZE(HDRP(bp)); // 현재 블록 크기 읽기

	if (prev_alloc && next_alloc)       return bp;               	// Case 1: 앞뒤 모두 할당 → 변화 없음

	if (prev_alloc && !next_alloc) 									// Case 2: 뒤쪽 free → 뒤 블록만 흡수
	{                              
	size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
    PUT(HDRP(bp), PACK(size,0));  PUT(FTRP(bp), PACK(size,0));
    return bp;
  	}

  	if (!prev_alloc && next_alloc) 									// Case 3: 앞쪽 free → 앞 블록만 흡수
	{                              
    size += GET_SIZE(HDRP(PREV_BLKP(bp)));
    bp = PREV_BLKP(bp);
    PUT(HDRP(bp), PACK(size,0));  PUT(FTRP(bp), PACK(size,0));
    return bp;
  	}
  
  	size += GET_SIZE(HDRP(PREV_BLKP(bp)))							// Case 4: 앞뒤 모두 free → 세 블록 합쳐 하나로
    	  + GET_SIZE(FTRP(NEXT_BLKP(bp)));
  	bp = PREV_BLKP(bp);
  	PUT(HDRP(bp), PACK(size,0));  PUT(FTRP(bp), PACK(size,0));
  	return bp;
}

static void *find_fit(size_t asize) //frist_fit							//힙 시작에서 에필로그 전까지 선형 탐색
{
	void *bp;

	for(bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)){ //힙 시작(heap_listp)부터 에필로그 전까지 순차 탐색
		if(!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp)))) {	  //free 이면서 크기 충분한 첫 블록 리턴. 없으면 NULL
			return bp;
		}
	}
	return NULL;
}



static void place(void *bp, size_t asize) //블록 분할, 할당
{
	size_t csize = GET_SIZE(HDRP(bp));

	if((csize - asize) >= (2*DSIZE)) { //여유 공간이 최소 16B 이상이면 “할당·남은 free” 두 블록으로 분할
		// 분할 가능
		PUT(HDRP(bp), PACK(asize , 1));
		PUT(FTRP(bp), PACK(asize, 1));
		bp = NEXT_BLKP(bp);
		PUT(HDRP(bp), PACK(csize-asize, 0));
		PUT(FTRP(bp), PACK(csize-asize, 0));
	}
	else {
		// 분할 여유 없으면 전체 할당
		PUT(HDRP(bp), PACK(csize, 1));
		PUT(FTRP(bp), PACK(csize, 1));
	}
}
/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *ptr, size_t size) {		//메모리 재할당 improve raalloc
    if (ptr == NULL) return mm_malloc(size);	//ptr이 NULL이면 malloc와 같음
    if (size == 0) {							//size가 0이면 메모리 헤재하고 아무것도 안돌려줌
        mm_free(ptr);
        return NULL;
    }

    void *oldptr = ptr;							//기존 포인터 oldptr로 백업
    size_t oldsize = GET_SIZE(HDRP(oldptr));	//현재 블록의 전체 크기(=헤더에 기록된 값)
    size_t newsize = ALIGN(size + DSIZE);  // header + footer(8바이트) 포함 정렬

    // Case 1: 요청 크기가 기존보다 작거나 같으면 그대로 사용
    if (newsize <= oldsize) { 
        return ptr;
    }

    // Case 2: 뒤 블록이 free이고, 현재 크기 + 다음 블록 크기 ≥ 새 요청 크기
    void *next = NEXT_BLKP(oldptr);
    if (!GET_ALLOC(HDRP(next)) && (oldsize + GET_SIZE(HDRP(next))) >= newsize) {
        size_t total = oldsize + GET_SIZE(HDRP(next));
        PUT(HDRP(oldptr), PACK(total, 1)); //헤더에 병합된 블록 크기를 할당 상태로 기록
        PUT(FTRP(oldptr), PACK(total, 1)); //풋터에 병합된 블록 크기를 할당 상태로 기록
        return oldptr;					   //블록 이동 없이 확장 성공 : 기존 포인터 그대로 반환
    }

    // Case 3: 새로 malloc하고 복사 후 old block free
    void *newptr = mm_malloc(size);
    if (newptr == NULL) return NULL; //메모리 부족이면 그냥 NULL 리턴

    size_t copySize = oldsize - DSIZE;  // 실제 payload만 복사
    if (size < copySize) copySize = size; //요청한 size가 더 작다면, size만큼만 복사

    memmove(newptr, oldptr, copySize); //내용 복사
    mm_free(oldptr);				   //원래 메모리 필요 없으니 해제
    return newptr;
}