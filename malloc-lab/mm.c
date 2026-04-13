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
#include <errno.h>

#include "mm.h"
#include "memlib.h"

/*********************************************************
 * NOTE TO STUDENTS: Before you do anything else, please
 * provide your team information in the following struct.
 ********************************************************/
team_t team = {
    /* Team name */
    "ateam",
    /* First member's full name */
    "Harry Bovik",
    /* First member's email address */
    "bovik@cs.cmu.edu",
    /* Second member's full name (leave blank if none) */
    "",
    /* Second member's email address (leave blank if none) */
    ""};

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT - 1)) & ~0x7)

#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

// 워드 크기
#define WSIZE 4
// 더블 워드 크기
#define DSIZE 8

// 초기 가용 블록과 힙 확정을 위한 기본 크기
#define CHUNKSIZE (1 << 12)
#define MAX(x, y) ((x) > (y) ? (x) : (y))

// 크기와 할당 비트를 통합해서 헤더와 풋터에 저장 할 수 있는 값
#define PACK(size, alloc) ((size) | (alloc))

/*
인자 p가 참조하는 워드를 일어서 리턴한다. 여기서 캐스팅이 매우 중요하다..
인자 p는 보통 보이드 포인터이며 이것은 직접적으로 역참조할 수 는 없다.
*/
#define GET(p) (*(unsigned int *)(p))
// 인자 p가 가리키는 워드에 val을 저장한다.
#define PUT(p, val) (*(unsigned int *)(p) = (val))

// 주소 p에 있는 size를 리턴, p는 헤더 또는 풋터의 주소여야 한다
#define GET_SIZE(p) (GET(p) & ~0x7)
// 주소 p에 있는 할당 비트를 리턴, p는 헤더 또는 풋터의 주소여야 한다
#define GET_ALLOC(p) (GET(p) & 0x1)

// bp(블록 포인터)가 주어지면, 블록 헤더 포인터를 리턴한다.
#define HDRP(bp) ((char *)(bp) - WSIZE)
/*
block_start + block_size = 다음 블럭 주소
다음 블럭 주소 - WSIZE = 이전 블록 푸터
block start = bp - WSIZE
푸터 = bp + block_size - WSIZE - WSIZE
*/
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

// 다음 블록 포인터를 반환
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)))
// 이전 블록 풋터 포인터를 반환
#define PREV_FTRP(bp) ((char *)(bp) - DSIZE)
// 이전 블록 포인터를 반환
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE(PREV_FTRP(bp)))

static char *heap_listp = NULL;

static void *extend_heap(size_t words);
static void *coalesce(void *bp);
static void *find_first(size_t size);
static void place(void *bp, size_t asize);

/*
 * mm_init - initialize the malloc package.
 */
int mm_init(void)
{
    errno = 0;
    heap_listp = mem_sbrk(4 * WSIZE);
    if (errno != 0)
    {
        printf("에러 발생은 %d 때문입니다.", errno);
        return -1;
    }

    PUT(heap_listp, 0);
    PUT(heap_listp + WSIZE, PACK(DSIZE, 1));       // 프롤로그 헤더
    PUT(heap_listp + (2 * WSIZE), PACK(DSIZE, 1)); // 프롤로그 푸터
    PUT(heap_listp + (3 * WSIZE), PACK(0, 1));     // 에필로그 헤더
    heap_listp += (2 * WSIZE);                     // 프롤로그 푸터를 가르킴 (원래는 payload를 가르켜야하지만 프롤로그에는 payload가 없기 때문)

    if (extend_heap(CHUNKSIZE / WSIZE) == NULL)
        return -1;

    return 0;
}

/*
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size)
{
    size_t extendsize;
    size_t newsize;
    char *bp;
    if (size == 0)
    {
        return NULL;
    }

    newsize = ALIGN(size + SIZE_T_SIZE);
    if ((bp = find_first(newsize)) != NULL)
    {
        place(bp, newsize);
        return bp;
    }

    extendsize = MAX(newsize, CHUNKSIZE);
    if ((bp = extend_heap(extendsize / WSIZE)) == NULL)
    {
        return NULL;
    }
    else
    {
        place(bp, newsize);
        return bp;
    }
}

/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *ptr)
{
    size_t size = GET_SIZE(HDRP(ptr));

    PUT(HDRP(ptr), PACK(size, 0));
    PUT(FTRP(ptr), PACK(size, 0));
    coalesce(ptr);
}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *ptr, size_t size)
{
    void *oldptr = ptr;
    void *newptr;
    size_t copySize;

    newptr = mm_malloc(size);
    if (newptr == NULL)
        return NULL;
    copySize = *(size_t *)((char *)oldptr - SIZE_T_SIZE);
    if (size < copySize)
        copySize = size;
    memcpy(newptr, oldptr, copySize);
    mm_free(oldptr);
    return newptr;
}

static void *extend_heap(size_t words)
{
    char *bp;
    size_t size;

    // 더블 워드의 배수를 반환하기 위해 홀수인 경우 +1을 해서 WSIZE를 곱해준다.
    size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;
    if ((long)(bp = mem_sbrk(size)) == -1)
        return NULL;

    PUT(HDRP(bp), PACK(size, 0));         // 새로운 free block header
    PUT(FTRP(bp), PACK(size, 0));         // 새로운 free block footer
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); // 새로운 에필로그 헤더

    return coalesce(bp); // 만약 이전 블럭이 free block이었다면 합체
}

static void *coalesce(void *bp)
{
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));

    if (prev_alloc && next_alloc)
        return bp;

    if (prev_alloc && !next_alloc)
    {
        // 다음 블록만 가용 상태인 경우 = 기존 블록 헤더와 다음 블록 푸터를 수정, bp를 이전 블록 bp로 수정
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));   // size를 다음 블록 사이즈만큼 늘림
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0)); // 다음 블록 푸터 수정
        PUT(HDRP(bp), PACK(size, 0));            // 기존 블록 헤더 수정
    }
    else if (!prev_alloc && next_alloc)
    {
        // 이전 블록만 가용 상태인 경우 = 이전 블록 헤더와 기존 블록 푸터를 수정
        size += GET_SIZE(FTRP(PREV_BLKP(bp))); // size를 이전 블록 사이즈만큼 늘림
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
        bp = PREV_BLKP(bp); // 중요! bp를 이전 블록 bp로 수정해줘야함
    }
    else
    {
        // 이전 블록과 다음 블록이 가용 상태인 경우 = 이전 블럭 헤더와 다음 블럭 푸터 수정, bp를 이전 블록 bp로 수정
        size += GET_SIZE(FTRP(PREV_BLKP(bp))) + GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }

    return bp;
}

static void *find_first(size_t size)
{
    void *bp = NEXT_BLKP(heap_listp);

    while (1)
    {
        size_t block_size = GET_SIZE(HDRP(bp));

        if (block_size == 0)
        { // 에필로그 도착
            return NULL;
        }

        if (!GET_ALLOC(HDRP(bp)) && size <= block_size)
            return bp;

        bp = NEXT_BLKP(bp);
    }
}

static void place(void *bp, size_t asize)
{
    size_t size = GET_SIZE(HDRP(bp));
    void *next_bp = NULL;
    // 남는 공간이 최소 블록 크기(16byte) 이상이면 split
    if ((size - asize) >= (2 * DSIZE))
    {
        // 앞부분
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));

        next_bp = NEXT_BLKP(bp);
        PUT(HDRP(next_bp), PACK(size - asize, 0));
        PUT(FTRP(next_bp), PACK(size - asize, 0));
    }
    // 남는 공간이 최소 공간 보다 적다면 아예 통째로 할당
    else
    {
        PUT(HDRP(bp), PACK(size, 1));
        PUT(FTRP(bp), PACK(size, 1));
    }
}
