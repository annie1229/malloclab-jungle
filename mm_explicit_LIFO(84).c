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
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>
#include <string.h>

#include "mm.h"
#include "memlib.h"

/*********************************************************
 * NOTE TO STUDENTS: Before you do anything else, please
 * provide your team information in the following struct.
 ********************************************************/
team_t team = {
    /* Team name */
    "swjungle",
    /* First member's full name */
    "Lee Hye Jin",
    /* First member's email address */
    "annie_1229@naver.com",
    /* Second member's full name (leave blank if none) */
    "",
    /* Second member's email address (leave blank if none) */
    ""
};

/* Basic constants and macros */
#define WSIZE 4 // Word and header/footer size(bytes)
#define DSIZE 8 // Double word size(bytes)
#define CHUNKSIZE (1<<12)   // Extend heap by this amount(bytes) // 4096

#define MAX(x, y) ((x) > (y) ? (x) : (y))

/* Pack a size and allocated bit into a word */
#define PACK(size, alloc) ((size) | (alloc))

/* Read and write a word at address p*/
#define GET(p) (*(unsigned int *)(p))
#define PUT(p, val) (GET(p) = (val))

/* Read the size and allocated fields from address p */
#define GET_SIZE(p) (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)

/* Given block ptr bp, compute address of its header and footer */
#define HDRP(bp) ((char *)(bp) - WSIZE)
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

/* Given block ptr bp, compute address of next and previous blocks */
// #define NEXT_BLKP(bp) ((char *)bp + GET_SIZE(HDRP(bp)))
#define NEXT_BLKP(bp) ((char *)bp + GET_SIZE(((char *)(bp) - WSIZE)))
#define PREV_BLKP(bp) ((char *)bp - GET_SIZE(((char *)(bp) - DSIZE)))

/* Given ptr in free list, get next and previous ptr in the list */
/* bp is address of the free block. Since minimum Block size is 16 bytes, 
   we utilize to store the address of previous block pointer and next block pointer.
*/
#define GET_NEXT_PTR(bp)  (*(char **)(bp + WSIZE))
#define GET_PREV_PTR(bp)  (*(char **)(bp))

/* Puts pointers in the next and previous elements of free list */
#define SET_NEXT_PTR(bp, qp) (GET_NEXT_PTR(bp) = (qp))
#define SET_PREV_PTR(bp, qp) (GET_PREV_PTR(bp) = (qp))

/* Global declarations */
static char *heap_listp; 
static char *free_list_start;

/* Function prototypes for internal helper routines */
static void *coalesce(void *bp);
static void *extend_heap(size_t words);
static void *find_fit(size_t asize);
static void place(void *bp, size_t asize);

/* Function prototypes for maintaining free list*/
static void insert_in_free_list(void *bp); 
static void remove_from_free_list(void *bp); 

/* 
 * mm_init - initialize the malloc package.
 */
int mm_init(void) {
    /* Create the initial empty heap. */
    if ((heap_listp = mem_sbrk(8*WSIZE)) == (void *) - 1) 
      return -1;

    PUT(heap_listp, 0);                             // Alignment paddine
    PUT(heap_listp + (1*WSIZE), PACK(DSIZE, 1));    // Prologue header
    PUT(heap_listp + (2*WSIZE), PACK(DSIZE, 1));    // Prologue footer
    PUT(heap_listp + (3*WSIZE), PACK(0, 1));        // Epilogue header
    free_list_start = heap_listp + 2*WSIZE; 

    /* Extend the empty heap with a free block of minimum possible block size */
    if (extend_heap(4) == NULL)
        return -1;
    return 0;
}

/* 
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size) {
    size_t asize;      /* Adjusted block size */
    size_t extendsize; /* Amount to extend heap if no fit */
    void *bp;

    /* Ignore spurious requests. */
    if (size == 0)
        return NULL;

    /* Adjust block size to include overhead and alignment reqs. */
    if (size <= DSIZE)
        asize = 2 * DSIZE;
    else
        asize = DSIZE * ((size + DSIZE + (DSIZE - 1)) / DSIZE);

    /* Search the free list for a fit. */
    if ((bp = find_fit(asize)) != NULL) {
        place(bp, asize);
        return (bp);
    }

    /* No fit found. Get more memory and place the block */
    extendsize = MAX(asize, CHUNKSIZE);
    if ((bp = extend_heap(extendsize/WSIZE)) == NULL)
        return NULL;
    place(bp, asize);
    return bp;
} 

/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *bp) {
    size_t size = GET_SIZE(HDRP(bp));
    
    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    coalesce(bp);
}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *ptr, size_t size) {
    size_t oldsize;
    void *newptr;

    /* If size == 0 the this is just free, and we return NULL. */
    if (size == 0) {
        mm_free(ptr);
        return 0;
    }

    /* If oldptr is NULL, then this is just malloc. */
    if (ptr == NULL) {
        return mm_malloc(size);
    }
    newptr = mm_malloc(size);

    /* If realloc() fails the original block is left untouched. */
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

/* Boundary tag coalescing. Return ptr ro coalesced block */
static void *coalesce(void *bp) {
    //if previous block is allocated or its size is zero then PREV_ALLOC will be set.
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp))) || PREV_BLKP(bp) == bp;
    size_t size = GET_SIZE(HDRP(bp));
    
    if (prev_alloc && next_alloc) {
        insert_in_free_list(bp);
        return bp;
    } 
    else if (prev_alloc && !next_alloc) {                  
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        remove_from_free_list(NEXT_BLKP(bp));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    }
    else if (!prev_alloc && next_alloc) {               
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        bp = PREV_BLKP(bp);
        remove_from_free_list(bp);
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    }
    else {                
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
 * extend_heap - Extends the heap with a free block and return its block pointer
*/
static void *extend_heap(size_t words) {
    char *bp;
    size_t size;

    /* Allocate an even number of words to maintain alignment */
    size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;

    if ((bp = mem_sbrk(size)) == (void *) - 1)
        return NULL;
        
    /* Initialize free block header/footer and the epilogue header */
    PUT(HDRP(bp), PACK(size, 0));         /* free block header */
    PUT(FTRP(bp), PACK(size, 0));         /* free block footer */
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); /* new epilogue header */

    /* coalesce bp with next and previous blocks */
    return coalesce(bp);
}

static void *find_fit(size_t asize) {
    void *bp;
    
    for (bp = free_list_start; GET_ALLOC(HDRP(bp)) == 0; bp = GET_NEXT_PTR(bp)) {
        if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp)))) {
            return bp;
        }
    }
    return NULL;
}

static void place(void *bp, size_t asize) {
    size_t csize = GET_SIZE(HDRP(bp));

    if ((csize - asize) >= (2*DSIZE)) {
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));
        remove_from_free_list(bp);
        bp = NEXT_BLKP(bp);
        PUT(HDRP(bp), PACK(csize-asize, 0));
        PUT(FTRP(bp), PACK(csize-asize, 0));
        coalesce(bp);
    }
    else {
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
        remove_from_free_list(bp);
    }
}

/*Inserts the free block pointer int the free_list*/
static void insert_in_free_list(void *bp) {
    SET_NEXT_PTR(bp, free_list_start); 
    SET_PREV_PTR(free_list_start, bp); 
    SET_PREV_PTR(bp, NULL); 
    free_list_start = bp; 
}

/*Removes the free block pointer int the free_list*/
static void remove_from_free_list(void *bp) {
    if (GET_PREV_PTR(bp))
        SET_NEXT_PTR(GET_PREV_PTR(bp), GET_NEXT_PTR(bp));
    else
        free_list_start = GET_NEXT_PTR(bp);
    SET_PREV_PTR(GET_NEXT_PTR(bp), GET_PREV_PTR(bp));
}
