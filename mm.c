/*
 * mm.c
 * SWJungle 4기 이혜진
 * Week06 : Malloc-lab
 * Explicit Free List & LIFO
 * Score : 85/100
 *
 * Reference 
 * 1. Computer System : A Programmer's Perspective
 * 2. Carnegie Mellon 15-213 Introduction to Computer Systems
 * 3. github: https://github.com/HarshTrivedi/malloc/blob/master/mm.c
 */
#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>
#include <string.h>

#include "mm.h"
#include "memlib.h"

team_t team = {
    /* Team name */
    "swjungle_week06_6",
    /* First member's full name */
    "Lee Hye Jin",
    /* First member's email address */
    "annie_1229@naver.com",
    /* Second member's full name (leave blank if none) */
    "Mijungle",
    /* Third member's full name (leave blank if none) */
    "ZTeams"
};

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8
/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)

/* Basic constants and macros */
#define WSIZE 4 // Word and header/footer size(bytes)
#define DSIZE 8 // Double word size(bytes)
#define CHUNKSIZE (1<<12)   // Extend heap by this amount(bytes), 4096

#define MAX(x, y) ((x) > (y) ? (x) : (y))

/* size(상위 29bit)랑 alloc bit(하위 1bit) 합친다. */
#define PACK(size, alloc) ((size) | (alloc))

/* p에 담긴 값을 읽고(GET), 쓴다(PUT) */
#define GET(p) (*(unsigned int *)(p))
#define PUT(p, val) (GET(p) = (val))

/* p의 블록 사이즈(GET_SIZE), 블록 할당 여부(GET_ALLOC)를 계산한다. */
#define GET_SIZE(p) (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)

/* bp의 header주소, footer주소를 계산한다. */
#define HDRP(bp) ((char *)(bp) - WSIZE)
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

/* bp의 이전 블록, 다음 블록의 주소를 계산한다. */
#define NEXT_BLKP(bp) ((char *)bp + GET_SIZE(((char *)(bp) - WSIZE)))
#define PREV_BLKP(bp) ((char *)bp - GET_SIZE(((char *)(bp) - DSIZE)))

/* bp의 이전 가용 블록, 다음 가용 블록의 주소를 계산한다. */
#define GET_NEXT_PTR(bp)  (*(char **)(bp))
#define GET_PREV_PTR(bp)  (*(char **)(bp + WSIZE))

/* bp의 이전 가용 블록, 다음 가용 블록의 주소 자리에 qp를 넣는다. */
#define SET_NEXT_PTR(bp, qp) (GET_NEXT_PTR(bp) = (qp))
#define SET_PREV_PTR(bp, qp) (GET_PREV_PTR(bp) = (qp))

/* Global declarations */
static char *heap_listp; 
static char *free_list_start;

/* Function prototypes */
static void *coalesce(void *bp);
static void *extend_heap(size_t words);
static void *find_fit(size_t asize);
static void *place(void *bp, size_t asize);
static void insert_in_free_list(void *bp); 
static void remove_from_free_list(void *bp); 

/* 
 * mm_init - 초기화한다.
 */
int mm_init(void) {
    if ((heap_listp = mem_sbrk(6*WSIZE)) == (void *) - 1) 
        return -1;

    PUT(heap_listp, 0);                                 // Alignment paddine
    PUT(heap_listp + (1*WSIZE), PACK(2*DSIZE, 1));      // Prologue header
    PUT(heap_listp + (2*WSIZE), NULL);                  // Root_next
    PUT(heap_listp + (3*WSIZE), NULL);                  // Root_prev
    PUT(heap_listp + (4*WSIZE), PACK(2*DSIZE, 1));      // Prologue footer
    PUT(heap_listp + (5*WSIZE), PACK(0, 1));            // Epilogue header
    free_list_start = heap_listp + 2*WSIZE; 

    if (extend_heap(4) == NULL)
        return -1;
    return 0;
}

/* 
 * mm_malloc - payload의 size를 입력 받고, 블록을 할당하고 payload의 시작 주소를 반환한다.
 */
void *mm_malloc(size_t payload_size) {
    size_t blocksize;
    size_t extendsize;  
    void *bp;   /* block pointer = payload 시작 주소 담을 포인터 */

    if (payload_size == 0)
        return NULL;

    blocksize = ALIGN(payload_size+DSIZE);

    if ((bp = find_fit(blocksize)) != NULL) {
        bp = place(bp, blocksize);
        return (bp);
    }

    extendsize = MAX(blocksize, CHUNKSIZE);
    if ((bp = extend_heap(extendsize/WSIZE)) == NULL)
        return NULL;
    bp = place(bp, blocksize);
    return bp;
} 

/*
 * mm_free - block pointer를 입력받고 해당 블록을 할당 해제한다.
 */
void mm_free(void *bp) {
    size_t size = GET_SIZE(HDRP(bp));
    
    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    coalesce(bp);
}

/*
 * mm_realloc - 입력받은 size만큼 새로 할당하고 기존 ptr에 있던 정보를 옮기고 새로 할당된 block pointer를 반환한다.
 */
void *mm_realloc(void *ptr, size_t size) {
    size_t oldsize;
    void *newptr;

    if (size == 0) {
        mm_free(ptr);
        return 0;
    }

    if (ptr == NULL) {
        return mm_malloc(size);
    }
    newptr = mm_malloc(size);

    if (!newptr) {
        return 0;
    }

    /* Copy the old data. */
    oldsize = GET_SIZE(HDRP(ptr));
    if (size < oldsize)
        oldsize = size;
    memcpy(newptr, ptr, oldsize);

    /* Free the old block. */
    mm_free(ptr);
    return newptr;
}

/* 
 * coalesce - free된 block pointer를 입력받고, 이웃한 free 블록들을 합쳐서 free_list에 추가한다. 
 */
static void *coalesce(void *bp) {
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));
    
    if (prev_alloc && next_alloc) { // Case 1 : 앞, 뒷 블록 모두 alloc 상태
        insert_in_free_list(bp);
        return bp;
    } 
    else if (prev_alloc && !next_alloc) {   // Case 2: 앞 블록 alloc, 뒷 블록 free 상태            
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        remove_from_free_list(NEXT_BLKP(bp));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    }
    else if (!prev_alloc && next_alloc) {   // Case 3: 앞 블록 free, 뒷 블록 alloc 상태            
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        remove_from_free_list(PREV_BLKP(bp));
        bp = PREV_BLKP(bp);
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    }
    else {  // Case 4: 앞, 뒷 블록 모두 free 상태
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(HDRP(NEXT_BLKP(bp)));
        remove_from_free_list(PREV_BLKP(bp));
        remove_from_free_list(NEXT_BLKP(bp));
        bp = PREV_BLKP(bp);
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    }
    insert_in_free_list(bp);
    return bp;
}

/* 
 * extend_heap - 힙을 확장할 크기를 word 수로 입력받고, 힙을 확장한 후 새로 확장된 블록의 시작주소를 반환한다.
 */
static void *extend_heap(size_t words) {
    char *bp;
    size_t size;

    size = ALIGN(words*WSIZE);

    if ((bp = mem_sbrk(size)) == (void *) - 1)
        return NULL;
        
    PUT(HDRP(bp), PACK(size, 0));         /* free block header */
    PUT(FTRP(bp), PACK(size, 0));         /* free block footer */
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); /* new epilogue header */

    return coalesce(bp);
}

/* 
 * find_fit - blocksize를 입력받고 할당할 수 있는 블록을 찾아서 block pointer 반환한다.
 */
static void *find_fit(size_t blocksize) {
    void *bp;
    
    for (bp = free_list_start; GET_ALLOC(HDRP(bp)) == 0; bp = GET_NEXT_PTR(bp)) {
        if (blocksize <= GET_SIZE(HDRP(bp))) {
            return bp;
        }
    }
    return NULL;
}

/* 
 * place - blocksize(할당 받고싶은 블록의 크기)와 할당할 수 있는 블록(free 블록)의 block pointer를 입력받고 필요한 부분만큼 상태를 변경한 후 할당된 block pointer 반환한다.
 */
static void* place(void *bp, size_t blocksize) {
    size_t free_blocksize = GET_SIZE(HDRP(bp));
    size_t remain_size = free_blocksize - blocksize;

    remove_from_free_list(bp);
    if (remain_size < 2*DSIZE) {
        PUT(HDRP(bp), PACK(free_blocksize, 1)); 
        PUT(FTRP(bp), PACK(free_blocksize, 1)); 
    }
    else {
        PUT(HDRP(bp), PACK(blocksize, 1)); 
        PUT(FTRP(bp), PACK(blocksize, 1)); 
        PUT(HDRP(NEXT_BLKP(bp)), PACK(remain_size, 0)); 
        PUT(FTRP(NEXT_BLKP(bp)), PACK(remain_size, 0)); 
        insert_in_free_list(NEXT_BLKP(bp));
    }
    return bp;
}

/* 
 * insert_in_free_list - 입력받은 block pointer를 free_list에 앞에 추가한다.
 */
static void insert_in_free_list(void *bp) {
    SET_NEXT_PTR(bp, free_list_start); 
    SET_PREV_PTR(free_list_start, bp); 
    SET_PREV_PTR(bp, NULL); 
    free_list_start = bp; 
}

/* 
 * remove_from_free_list - 입력받은 block pointer를 free_list에서 삭제한다.
 */
static void remove_from_free_list(void *bp) {
    if (GET_PREV_PTR(bp))
        SET_NEXT_PTR(GET_PREV_PTR(bp), GET_NEXT_PTR(bp));
    else
        free_list_start = GET_NEXT_PTR(bp);
    SET_PREV_PTR(GET_NEXT_PTR(bp), GET_PREV_PTR(bp));
}
