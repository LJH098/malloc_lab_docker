/*
 * LIFO 삽입 방식을 사용하는 명시적 free list allocator.
 *
 * 모든 블록은 4바이트 헤더와 푸터를 가진다. free block은 payload 앞의
 * 두 포인터 칸을 predecessor/successor 링크 저장 공간으로 사용하고,
 * free list 자체는 LIFO 순서로 관리한다.
 */
#include <assert.h>
#include <errno.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

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

#define ALIGNMENT 8
#define ALIGN(size) (((size) + (ALIGNMENT - 1)) & ~0x7)

// 워드 크기
#define WSIZE 4
// 더블 워드 크기
#define DSIZE 8
#define OVERHEAD (2 * WSIZE)

// 초기 가용 블록과 힙 확정을 위한 기본 크기
#define CHUNKSIZE ((1 << 12) + OVERHEAD)

#define PTRSIZE ((size_t)sizeof(char *))
#define MINBLOCKSIZE ALIGN(OVERHEAD + (2 * PTRSIZE))

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

// free block payload의 첫 번째 포인터 칸
#define PRED_PTR(bp) ((char *)(bp))
// free block payload의 두 번째 포인터 칸
#define SUCC_PTR(bp) ((char *)(bp) + PTRSIZE)

#define GET_PTR(p) (*(char **)(p))
#define PUT_PTR(p, val) (*(char **)(p) = (char *)(val))

// 이전 free block의 주소를 읽는다
#define PRED(bp) (GET_PTR(PRED_PTR(bp)))
// 다음 free block의 주소를 읽는다
#define SUCC(bp) (GET_PTR(SUCC_PTR(bp)))

static char *heap_listp = NULL;
static char *free_listp = NULL;

static void *extend_heap(size_t words);
static void *coalesce(void *bp);
static void *find_fit(size_t asize);
static void place(void *bp, size_t asize);
static void insert_free_block(void *bp);
static void remove_free_block(void *bp);

/*
 * mm_init - malloc 패키지를 초기화한다.
 */
int mm_init(void)
{
    if ((heap_listp = mem_sbrk(4 * WSIZE)) == (void *)-1)
        return -1;

    PUT(heap_listp, 0);
    PUT(heap_listp + (1 * WSIZE), PACK(DSIZE, 1)); // 프롤로그 헤더
    PUT(heap_listp + (2 * WSIZE), PACK(DSIZE, 1)); // 프롤로그 푸터
    PUT(heap_listp + (3 * WSIZE), PACK(0, 1));     // 에필로그 헤더

    heap_listp += (2 * WSIZE); // 프롤로그 푸터를 가르킴 (원래는 payload를 가르켜야하지만 프롤로그에는 payload가 없기 때문)
    free_listp = NULL;

    if (extend_heap(CHUNKSIZE / WSIZE) == NULL)
        return -1;

    return 0;
}

/*
 * mm_malloc - 정렬 조건에 맞는 블록을 할당한다.
 */
void *mm_malloc(size_t size)
{
    size_t asize;
    size_t extendsize;
    char *bp;

    if (size == 0)
        return NULL;

    // 헤더/푸터와 free list 포인터 영역까지 고려한 최소 블록 크기를 맞춘다.
    asize = MAX(ALIGN(size + OVERHEAD), MINBLOCKSIZE);

    if ((bp = find_fit(asize)) != NULL)
    {
        place(bp, asize);
        return bp;
    }

    extendsize = MAX(asize, CHUNKSIZE);
    if ((bp = extend_heap(extendsize / WSIZE)) == NULL)
        return NULL;

    place(bp, asize);
    return bp;
}

/*
 * mm_free - 블록을 해제하고 바로 병합한다.
 */
void mm_free(void *ptr)
{
    size_t size;

    if (ptr == NULL)
        return;

    size = GET_SIZE(HDRP(ptr));
    PUT(HDRP(ptr), PACK(size, 0));
    PUT(FTRP(ptr), PACK(size, 0));
    coalesce(ptr);
}

/*
 * mm_realloc - 가능하면 현재 블록을 재사용하는 realloc.
 */
void *mm_realloc(void *ptr, size_t size)
{
    size_t asize;
    size_t oldsize;
    size_t prev_alloc;
    size_t prev_size;
    size_t next_alloc;
    size_t next_size;
    size_t total_size;
    size_t remainder;
    size_t copy_size;
    char *prev_bp;
    char *next_bp;
    char *split_bp;
    void *newptr;

    // ptr이 NULL이면 realloc은 malloc과 같다.
    if (ptr == NULL)
        return mm_malloc(size);

    // size가 0이면 기존 블록을 해제한다.
    if (size == 0)
    {
        mm_free(ptr);
        return NULL;
    }

    // 새 요청 크기를 블록 단위 크기로 맞추고, 기존 payload 크기도 같이 계산한다.
    asize = MAX(ALIGN(size + OVERHEAD), MINBLOCKSIZE);
    oldsize = GET_SIZE(HDRP(ptr));
    copy_size = oldsize - OVERHEAD;

    // 이미 현재 블록이 충분히 크다면 가능하면 쪼개서 그대로 사용한다.
    if (asize <= oldsize)
    {
        remainder = oldsize - asize;

        if (remainder >= MINBLOCKSIZE)
        {
            PUT(HDRP(ptr), PACK(asize, 1));
            PUT(FTRP(ptr), PACK(asize, 1));

            // 남는 뒷부분을 새로운 free block으로 만들고 병합한다.
            next_bp = NEXT_BLKP(ptr);
            PUT(HDRP(next_bp), PACK(remainder, 0));
            PUT(FTRP(next_bp), PACK(remainder, 0));
            PUT_PTR(PRED_PTR(next_bp), NULL);
            PUT_PTR(SUCC_PTR(next_bp), NULL);
            coalesce(next_bp);
        }

        return ptr;
    }

    prev_bp = PREV_BLKP(ptr);
    next_bp = NEXT_BLKP(ptr);
    prev_alloc = GET_ALLOC(FTRP(prev_bp));
    prev_size = GET_SIZE(HDRP(prev_bp));
    next_alloc = GET_ALLOC(HDRP(next_bp));
    next_size = GET_SIZE(HDRP(next_bp));

    // 다음 블록이 free block이고 크기가 충분하면 뒤로 확장해서 해결한다.
    if (!next_alloc && (oldsize + next_size) >= asize)
    {
        remove_free_block(next_bp);
        oldsize += next_size;
        remainder = oldsize - asize;

        if (remainder >= MINBLOCKSIZE)
        {
            PUT(HDRP(ptr), PACK(asize, 1));
            PUT(FTRP(ptr), PACK(asize, 1));

            // 뒤쪽에 남는 공간은 다시 free block으로 돌려준다.
            next_bp = NEXT_BLKP(ptr);
            PUT(HDRP(next_bp), PACK(remainder, 0));
            PUT(FTRP(next_bp), PACK(remainder, 0));
            PUT_PTR(PRED_PTR(next_bp), NULL);
            PUT_PTR(SUCC_PTR(next_bp), NULL);
            coalesce(next_bp);
        }
        else
        {
            PUT(HDRP(ptr), PACK(oldsize, 1));
            PUT(FTRP(ptr), PACK(oldsize, 1));
        }

        return ptr;
    }

    // 이전 블록이 free block이고 둘을 합치면 충분한 경우 = 앞으로 당겨서 재배치한다.
    if (!prev_alloc && (prev_size + oldsize) >= asize)
    {
        remove_free_block(prev_bp);
        total_size = prev_size + oldsize;
        remainder = total_size - asize;

        // source와 destination이 겹칠 수 있으므로 memcpy 대신 memmove를 쓴다.
        memmove(prev_bp, ptr, copy_size);

        if (remainder >= MINBLOCKSIZE)
        {
            PUT(HDRP(prev_bp), PACK(asize, 1));
            PUT(FTRP(prev_bp), PACK(asize, 1));

            // 앞쪽으로 옮기고 남은 뒷부분은 free block으로 만든다.
            split_bp = NEXT_BLKP(prev_bp);
            PUT(HDRP(split_bp), PACK(remainder, 0));
            PUT(FTRP(split_bp), PACK(remainder, 0));
            PUT_PTR(PRED_PTR(split_bp), NULL);
            PUT_PTR(SUCC_PTR(split_bp), NULL);
            coalesce(split_bp);
        }
        else
        {
            PUT(HDRP(prev_bp), PACK(total_size, 1));
            PUT(FTRP(prev_bp), PACK(total_size, 1));
        }

        return prev_bp;
    }

    // 앞/뒤가 모두 free block이면 세 블록을 합쳐서 최대한 제자리 근처에서 해결한다.
    if (!prev_alloc && !next_alloc && (prev_size + oldsize + next_size) >= asize)
    {
        remove_free_block(prev_bp);
        remove_free_block(next_bp);
        total_size = prev_size + oldsize + next_size;
        remainder = total_size - asize;

        // 최종 payload 시작 위치가 앞당겨지므로 memmove로 복사한다.
        memmove(prev_bp, ptr, copy_size);

        if (remainder >= MINBLOCKSIZE)
        {
            PUT(HDRP(prev_bp), PACK(asize, 1));
            PUT(FTRP(prev_bp), PACK(asize, 1));

            // 세 블록을 합친 뒤 남는 공간은 다시 free block으로 분할한다.
            split_bp = NEXT_BLKP(prev_bp);
            PUT(HDRP(split_bp), PACK(remainder, 0));
            PUT(FTRP(split_bp), PACK(remainder, 0));
            PUT_PTR(PRED_PTR(split_bp), NULL);
            PUT_PTR(SUCC_PTR(split_bp), NULL);
            coalesce(split_bp);
        }
        else
        {
            PUT(HDRP(prev_bp), PACK(total_size, 1));
            PUT(FTRP(prev_bp), PACK(total_size, 1));
        }

        return prev_bp;
    }

    // 다음 블록이 에필로그면 힙을 더 늘려서 현재 위치를 유지한다.
    if (next_size == 0)
    {
        if (mem_sbrk(asize - oldsize) == (void *)-1)
            return NULL;

        PUT(HDRP(ptr), PACK(asize, 1));
        PUT(FTRP(ptr), PACK(asize, 1));
        PUT(HDRP(NEXT_BLKP(ptr)), PACK(0, 1));
        return ptr;
    }

    // 위 조건들로 해결이 안 되면 새 블록을 할당해서 내용을 옮긴다.
    newptr = mm_malloc(size);
    if (newptr == NULL)
        return NULL;

    if (size < copy_size)
        copy_size = size;

    memcpy(newptr, ptr, copy_size);
    mm_free(ptr);
    return newptr;
}

/*
 * extend_heap - 새 free block을 만들면서 힙을 확장한다.
 */
static void *extend_heap(size_t words)
{
    char *bp;
    size_t size;

    // 더블 워드의 배수를 반환하기 위해 홀수인 경우 +1을 해서 WSIZE를 곱해준다.
    size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;
    if (size < MINBLOCKSIZE)
        size = MINBLOCKSIZE;

    if ((bp = mem_sbrk(size)) == (void *)-1)
        return NULL;

    PUT(HDRP(bp), PACK(size, 0));         // 새로운 free block header
    PUT(FTRP(bp), PACK(size, 0));         // 새로운 free block footer
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); // 새로운 에필로그 헤더

    PUT_PTR(PRED_PTR(bp), NULL);
    PUT_PTR(SUCC_PTR(bp), NULL);

    return coalesce(bp); // 만약 이전 블럭이 free block이었다면 합체
}

/*
 * coalesce - boundary tag를 이용해 인접 free block을 병합한다.
 */
static void *coalesce(void *bp)
{
    char *prev_bp = PREV_BLKP(bp);
    char *next_bp = NEXT_BLKP(bp);
    size_t prev_alloc = GET_ALLOC(FTRP(prev_bp));
    size_t next_alloc = GET_ALLOC(HDRP(next_bp));
    size_t size = GET_SIZE(HDRP(bp));

    if (prev_alloc && next_alloc)
    {
        PUT_PTR(PRED_PTR(bp), NULL);
        PUT_PTR(SUCC_PTR(bp), NULL);
        insert_free_block(bp);
        return bp;
    }

    if (prev_alloc && !next_alloc)
    {
        // 다음 블록만 가용 상태인 경우 = 기존 블록 헤더와 다음 블록 푸터를 수정
        remove_free_block(next_bp);
        size += GET_SIZE(HDRP(next_bp));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    }
    else if (!prev_alloc && next_alloc)
    {
        // 이전 블록만 가용 상태인 경우 = 이전 블록 헤더와 기존 블록 푸터를 수정
        remove_free_block(prev_bp);
        size += GET_SIZE(HDRP(prev_bp));
        PUT(HDRP(prev_bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
        bp = prev_bp; // 중요! bp를 이전 블록 bp로 수정해줘야함
    }
    else
    {
        // 이전 블록과 다음 블록이 가용 상태인 경우 = 이전 블럭 헤더와 다음 블럭 푸터 수정
        remove_free_block(prev_bp);
        remove_free_block(next_bp);
        size += GET_SIZE(HDRP(prev_bp)) + GET_SIZE(HDRP(next_bp));
        PUT(HDRP(prev_bp), PACK(size, 0));
        PUT(FTRP(next_bp), PACK(size, 0));
        bp = prev_bp;
    }

    PUT_PTR(PRED_PTR(bp), NULL);
    PUT_PTR(SUCC_PTR(bp), NULL);
    insert_free_block(bp);

    return bp;
}

/*
 * find_fit - explicit free list에서 first fit을 찾는다.
 */
static void *find_fit(size_t asize)
{
    char *bp;

    // explicit free list를 순회하면서 first fit을 찾는다.
    for (bp = free_listp; bp != NULL; bp = SUCC(bp))
    {
        if (GET_SIZE(HDRP(bp)) >= asize)
            return bp;
    }

    return NULL;
}

/*
 * place - free list에서 블록을 제거하고 할당한다.
 */
static void place(void *bp, size_t asize)
{
    size_t csize = GET_SIZE(HDRP(bp));
    size_t remainder = csize - asize;
    char *next_bp;

    // 명시적 free list에서 먼저 제거하고 배치한다.
    remove_free_block(bp);

    if (remainder >= MINBLOCKSIZE)
    {
        // 앞부분
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));

        next_bp = NEXT_BLKP(bp);
        PUT(HDRP(next_bp), PACK(remainder, 0));
        PUT(FTRP(next_bp), PACK(remainder, 0));
        PUT_PTR(PRED_PTR(next_bp), NULL);
        PUT_PTR(SUCC_PTR(next_bp), NULL);
        insert_free_block(next_bp);
    }
    else
    {
        // 남는 공간이 최소 공간 보다 적다면 아예 통째로 할당
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
    }
}

/*
 * insert_free_block - free block을 free list 맨 앞에 넣는다.
 */
static void insert_free_block(void *bp)
{
    // free block을 free list 맨 앞에 넣는다.
    PUT_PTR(PRED_PTR(bp), NULL);
    PUT_PTR(SUCC_PTR(bp), free_listp);

    if (free_listp != NULL)
        PUT_PTR(PRED_PTR(free_listp), bp);

    free_listp = bp;
}

/*
 * remove_free_block - explicit free list에서 블록을 제거한다.
 */
static void remove_free_block(void *bp)
{
    char *prev = PRED(bp);
    char *next = SUCC(bp);

    if (prev != NULL)
        PUT_PTR(SUCC_PTR(prev), next);
    else
        free_listp = next;

    if (next != NULL)
        PUT_PTR(PRED_PTR(next), prev);

    PUT_PTR(PRED_PTR(bp), NULL);
    PUT_PTR(SUCC_PTR(bp), NULL);
}
