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


/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8
/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)
// My additional Macros
#define WSIZE     4          // word and header/footer size (bytes)
#define DSIZE     8          // double word size (bytes)
#define INITCHUNKSIZE (1<<6)
#define CHUNKSIZE (1<<12)//+(1<<7) 

#define LISTLIMIT     20      
#define REALLOC_BUFFER  (1<<7)    

#define MAX(x, y) ((x) > (y) ? (x) : (y)) 
#define MIN(x, y) ((x) < (y) ? (x) : (y)) 

// Pack a size and allocated bit into a word
#define PACK(size, alloc) ((size) | (alloc))

// Read and write a word at address p 
#define GET(p)            (*(unsigned int *)(p))
#define PUT(p, val)       (*(unsigned int *)(p) = (val) | GET_TAG(p))
#define PUT_NOTAG(p, val) (*(unsigned int *)(p) = (val))

// Store predecessor or successor pointer for free blocks 
#define SET_PTR(p, ptr) (*(unsigned int *)(p) = (unsigned int)(ptr))

// Read the size and allocation bit from address p 
#define GET_SIZE(p)  (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)
#define GET_TAG(p)   (GET(p) & 0x2)
#define SET_RATAG(p)   (GET(p) |= 0x2)
#define REMOVE_RATAG(p) (GET(p) &= ~0x2)

// Address of block's header and footer 
#define HDRP(ptr) ((char *)(ptr) - WSIZE)
#define FTRP(ptr) ((char *)(ptr) + GET_SIZE(HDRP(ptr)) - DSIZE)

// Address of (physically) next and previous blocks 
#define NEXT_BLKP(ptr) ((char *)(ptr) + GET_SIZE((char *)(ptr) - WSIZE))
#define PREV_BLKP(ptr) ((char *)(ptr) - GET_SIZE((char *)(ptr) - DSIZE))

// Address of free block's predecessor and successor entries 
#define NEXT_PTR(ptr) ((char *)(ptr))
#define PREV_PTR(ptr) ((char *)(ptr) + WSIZE)

// Address of free block's predecessor and successor on the segregated list 
#define GET_NEXT_PTR(ptr) (*(char **)(ptr))
#define GET_PREV_PTR(ptr) (*(char **)(PREV_PTR(ptr)))

/* Global declarations */
void *segregated_free_lists[LISTLIMIT]; 

/* Function prototypes for internal helper routines */
static void *coalesce(void *bp);
static void *extend_heap(size_t words);
static void *place(void *bp, size_t asize);

/* Function prototypes for maintaining free list*/
static void insert_in_free_list(void *bp, size_t size);
static void remove_from_free_list(void *bp);


///////////////////////////////// Block information /////////////////////////////////////////////////////////
/*
 
A   : Allocated? (1: true, 0:false)
RA  : Reallocation tag (1: true, 0:false)
 
 < Allocated Block >
 
 
             31 30 29 28 27 26 25 24 23 22 21 20 19 18 17 16 15 14 13 12 11 10  9  8  7  6  5  4  3  2  1  0
            +--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+
 Header :   |                              size of the block                                       |  |  | A|
    bp ---> +--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+
            |                                                                                               |
            |                                                                                               |
            .                              Payload and padding                                              .
            .                                                                                               .
            .                                                                                               .
            +--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+
 Footer :   |                              size of the block                                       |     | A|
            +--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+
 
 
 < Free block >
 
             31 30 29 28 27 26 25 24 23 22 21 20 19 18 17 16 15 14 13 12 11 10  9  8  7  6  5  4  3  2  1  0
            +--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+
 Header :   |                              size of the block                                       |  |RA| A|
    bp ---> +--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+
            |                        pointer to its predecessor in Segregated list                          |
bp+WSIZE--> +--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+
            |                        pointer to its successor in Segregated list                            |
            +--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+
            .                                                                                               .
            .                                                                                               .
            .                                                                                               .
            +--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+
 Footer :   |                              size of the block                                       |     | A|
            +--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+
 
 
*/
///////////////////////////////// End of Block information /////////////////////////////////////////////////////////

/* 
 * mm_init - initialize the malloc package.
 */
int mm_init(void) {      
    char *heap_listp; // Pointer to beginning of heap
    
    // Initialize segregated free lists
    for (int list = 0; list < LISTLIMIT; list++) {
        segregated_free_lists[list] = NULL;
    }
    
    // Allocate memory for the initial empty heap 
    if ((heap_listp = mem_sbrk(4*WSIZE)) == (void *) - 1) 
        return -1;
    
    PUT_NOTAG(heap_listp, 0);                            /* Alignment padding */
    PUT_NOTAG(heap_listp + (1 * WSIZE), PACK(DSIZE, 1)); /* Prologue header */
    PUT_NOTAG(heap_listp + (2 * WSIZE), PACK(DSIZE, 1)); /* Prologue footer */
    PUT_NOTAG(heap_listp + (3 * WSIZE), PACK(0, 1));     /* Epilogue header */
    
    if (extend_heap(INITCHUNKSIZE) == NULL)
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
    void *bp;  /* Pointer */
    
    /* Ignore spurious requests. */
    if (size == 0)
        return NULL;

    /* Adjust block size to include overhead and alignment reqs. */
    if (size <= DSIZE)
        asize = 2 * DSIZE;
    else
        asize = DSIZE * ((size + DSIZE + (DSIZE - 1)) / DSIZE);
    
    int list = 0; 
    size_t searchsize = asize;
    // Search for free block in segregated list
    while (list < LISTLIMIT) {
        if ((list == LISTLIMIT - 1) || ((searchsize <= 1) && (segregated_free_lists[list] != NULL))) {
            bp = segregated_free_lists[list];
            // Ignore blocks that are too small or marked with the reallocation bit
            while ((bp != NULL) && ((asize > GET_SIZE(HDRP(bp))) || (GET_TAG(HDRP(bp)))))
            {
                bp = GET_NEXT_PTR(bp);
            }
            if (bp != NULL)
                break;
        }
        
        searchsize >>= 1;
        list++;
    }
    
    // if free block is not found, extend the heap
    if (bp == NULL) {
        extendsize = MAX(asize, CHUNKSIZE);
        
        if ((bp = extend_heap(extendsize)) == NULL)
            return NULL;
    }
    
    // Place and divide block
    bp = place(bp, asize);
    
    // Return pointer to newly allocated block 
    return bp;
}

/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *bp) {
    size_t size = GET_SIZE(HDRP(bp));
 
    REMOVE_RATAG(HDRP(NEXT_BLKP(bp)));
    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    
    insert_in_free_list(bp, size);
    coalesce(bp);
}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
// 여기 바꾸면 8점 떨어짐..
void *mm_realloc(void *ptr, size_t size) {
    void *new_ptr = ptr;    /* Pointer to be returned */
    size_t new_size = size; /* Size of new block */
    int remainder;          /* Adequacy of block sizes */
    int extendsize;         /* Size of heap extension */
    int block_buffer;       /* Size of block buffer */
    
    // Ignore size 0 cases
    if (size == 0)
        return NULL;
    
    // Align block size
    if (new_size <= DSIZE) {
        new_size = 2 * DSIZE;
    } else {
        new_size = ALIGN(size+DSIZE);
    }
    
    /* Add overhead requirements to block size */
    new_size += REALLOC_BUFFER;
    
    /* Calculate block buffer */
    block_buffer = GET_SIZE(HDRP(ptr)) - new_size;
    
    /* Allocate more space if overhead falls below the minimum */
    if (block_buffer < 0) {
        /* Check if next block is a free block or the epilogue block */
        if (!GET_ALLOC(HDRP(NEXT_BLKP(ptr))) || !GET_SIZE(HDRP(NEXT_BLKP(ptr)))) {
            remainder = GET_SIZE(HDRP(ptr)) + GET_SIZE(HDRP(NEXT_BLKP(ptr))) - new_size;
            if (remainder < 0) {
                extendsize = MAX(-remainder, CHUNKSIZE);
                if (extend_heap(extendsize) == NULL)
                    return NULL;
                remainder += extendsize;
            }
            
            remove_from_free_list(NEXT_BLKP(ptr));
            
            // Do not split block
            PUT_NOTAG(HDRP(ptr), PACK(new_size + remainder, 1)); 
            PUT_NOTAG(FTRP(ptr), PACK(new_size + remainder, 1)); 
        } else {
            new_ptr = mm_malloc(new_size - DSIZE);
            memcpy(new_ptr, ptr, MIN(size, new_size));
            mm_free(ptr);
        }
        block_buffer = GET_SIZE(HDRP(new_ptr)) - new_size;
    }
    
    // Tag the next block if block overhead drops below twice the overhead 
    if (block_buffer < 2 * REALLOC_BUFFER)
        SET_RATAG(HDRP(NEXT_BLKP(new_ptr)));
    
    // Return the reallocated block 
    return new_ptr;
}
// void *mm_realloc(void *ptr, size_t size) {
//     size_t oldsize;
//     void *newptr;

//     /* If size == 0 the this is just free, and we return NULL. */
//     if (size == 0) {
//         mm_free(ptr);
//         return 0;
//     }

//     /* If oldptr is NULL, then this is just malloc. */
//     if (ptr == NULL) {
//         return mm_malloc(size);
//     }
//     newptr = mm_malloc(size);

//     /* If realloc() fails the original block is left untouched. */
//     if (!newptr) {
//         return 0;
//     }

//     /* Copy the old data. */
//     oldsize = GET_SIZE(HDRP(ptr));
//     if (size < oldsize)
//         oldsize = size;
//     memcpy(newptr, ptr, oldsize);

//     /* Free the old block. */
//     mm_free(ptr);
//     return newptr;
// }

static void *extend_heap(size_t words) {
    void *bp;                   
    size_t asize;                // Adjusted size 
    
    asize = ALIGN(words);
    
    if ((bp = mem_sbrk(asize)) == (void *)-1)
        return NULL;
    
    // Set headers and footer 
    PUT_NOTAG(HDRP(bp), PACK(asize, 0));  
    PUT_NOTAG(FTRP(bp), PACK(asize, 0));   
    PUT_NOTAG(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); 
    insert_in_free_list(bp, asize);

    return coalesce(bp);
}

static void *coalesce(void *bp) {
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t prev_alloc = GET_ALLOC(HDRP(PREV_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));
    
    // Do not coalesce with previous block if the previous block is tagged with Reallocation tag
    if (GET_TAG(HDRP(PREV_BLKP(bp))))
        prev_alloc = 1;

    if (prev_alloc && next_alloc) {                         // Case 1
        return bp;
    }
    else if (prev_alloc && !next_alloc) {                   // Case 2
        remove_from_free_list(bp);
        remove_from_free_list(NEXT_BLKP(bp));
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    } else if (!prev_alloc && next_alloc) {                 // Case 3 
        remove_from_free_list(bp);
        remove_from_free_list(PREV_BLKP(bp));
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        bp = PREV_BLKP(bp);
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    } else {                                                // Case 4
        remove_from_free_list(bp);
        remove_from_free_list(PREV_BLKP(bp));
        remove_from_free_list(NEXT_BLKP(bp));
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(HDRP(NEXT_BLKP(bp)));
        bp = PREV_BLKP(bp);
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    }
    insert_in_free_list(bp, size);
    return bp;
}

static void *place(void *bp, size_t asize) {
    size_t csize = GET_SIZE(HDRP(bp));
    size_t remain_size = csize - asize;

    remove_from_free_list(bp);
    if (remain_size <= 2*DSIZE) {
        // Do not split block 
        PUT(HDRP(bp), PACK(csize, 1)); 
        PUT(FTRP(bp), PACK(csize, 1)); 
    }
    else if (asize >= 100) { // 할당할 사이즈가 너무 크면, 이 else if문 주석해도 돌아가긴 하는데 6점 낮아져서 92점 나옴 why?
        // Split block
        PUT(HDRP(bp), PACK(remain_size, 0)); // 앞쪽을 free블록으로
        PUT(FTRP(bp), PACK(remain_size, 0));
        insert_in_free_list(bp, remain_size);
        bp = NEXT_BLKP(bp);
        PUT_NOTAG(HDRP(bp), PACK(asize, 1));
        PUT_NOTAG(FTRP(bp), PACK(asize, 1));
    }
    else {
        // Split block
        PUT(HDRP(bp), PACK(asize, 1)); 
        PUT(FTRP(bp), PACK(asize, 1)); 
        PUT_NOTAG(HDRP(NEXT_BLKP(bp)), PACK(remain_size, 0)); 
        PUT_NOTAG(FTRP(NEXT_BLKP(bp)), PACK(remain_size, 0)); 
        insert_in_free_list(NEXT_BLKP(bp), remain_size);
    }
    return bp;
}

static void insert_in_free_list(void *bp, size_t size) {
    int list = 0;
    void *search_ptr = bp;
    void *insert_ptr = NULL;
    
    // Select segregated list, 들어갈 수 있는 가장 작은 블록(가장 적당하게 맞는 크기의 list찾기)
    while ((list < LISTLIMIT - 1) && (size > 1)) {
        size >>= 1; // size 2로 나누기하는거랑 똑같
        list++; // 다음 리스트로
    }
    
    // Keep size ascending order and search
    search_ptr = segregated_free_lists[list];
    while ((search_ptr != NULL) && (size > GET_SIZE(HDRP(search_ptr)))) {
        insert_ptr = search_ptr;
        search_ptr = GET_NEXT_PTR(search_ptr);
    }
    
    // Set predecessor and successor 
    if (search_ptr != NULL) {
        if (insert_ptr != NULL) {
            SET_PTR(NEXT_PTR(bp), search_ptr);
            SET_PTR(PREV_PTR(search_ptr), bp);
            SET_PTR(PREV_PTR(bp), insert_ptr);
            SET_PTR(NEXT_PTR(insert_ptr), bp);
        } else {
            SET_PTR(NEXT_PTR(bp), search_ptr);
            SET_PTR(PREV_PTR(search_ptr), bp);
            SET_PTR(PREV_PTR(bp), NULL);
            segregated_free_lists[list] = bp;
        }
    } else {
        if (insert_ptr != NULL) {
            SET_PTR(NEXT_PTR(bp), NULL);
            SET_PTR(PREV_PTR(bp), insert_ptr);
            SET_PTR(NEXT_PTR(insert_ptr), bp);
        } else {
            SET_PTR(NEXT_PTR(bp), NULL);
            SET_PTR(PREV_PTR(bp), NULL);
            segregated_free_lists[list] = bp;
        }
    }
}

static void remove_from_free_list(void *bp) {
    int list = 0;
    size_t size = GET_SIZE(HDRP(bp));
    
    // Select segregated list 
    while ((list < LISTLIMIT - 1) && (size > 1)) {
        size >>= 1;
        list++;
    }
    
    if (GET_NEXT_PTR(bp) != NULL) {
        if (GET_PREV_PTR(bp) != NULL) {
            SET_PTR(PREV_PTR(GET_NEXT_PTR(bp)), GET_PREV_PTR(bp));
            SET_PTR(NEXT_PTR(GET_PREV_PTR(bp)), GET_NEXT_PTR(bp));
        } else {
            SET_PTR(PREV_PTR(GET_NEXT_PTR(bp)), NULL);
            segregated_free_lists[list] = GET_NEXT_PTR(bp);
        }
    } else {
        if (GET_PREV_PTR(bp) != NULL) {
            SET_PTR(NEXT_PTR(GET_PREV_PTR(bp)), NULL);
        } else {
            segregated_free_lists[list] = NULL;
        }
    }
}

