/*
 * mm.c
 *
 * NOTE TO STUDENTS: Replace this header comment with your own header
 * comment that gives a high level description of your solution.
 */
#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#include "memlib.h"
#include "mm.h"

/* If you want debugging output, use the following macro.  When you hand
 * in, remove the #define DEBUG line. */
#define DEBUG
#ifdef DEBUG
#define dbg_printf(...) printf(__VA_ARGS__)
#else
#define dbg_printf(...)
#endif

/* do not change the following! */
#ifdef DRIVER
/* create aliases for driver tests */
#define malloc mm_malloc
#define free mm_free
#define realloc mm_realloc
#define calloc mm_calloc
#endif /* def DRIVER */

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(p) (((size_t)(p) + (ALIGNMENT - 1)) & ~0x7)

/* Basic constants and macros */
#define WSIZE 4             /* Word and header/footer size (bytes) */
#define DSIZE 8             /* Double word size (bytes) */
#define CHUNKSIZE (1 << 12) /* Extend heap by this amount (bytes) */

#define MAX(x, y) ((x) > (y) ? (x) : (y))

/* Pack a size and allocated bit into a word */
#define PACK(size, alloc) ((size) | (alloc))

/* Read and write a word at address p */
#define GET(p) (*(unsigned int *)(p))
#define PUT(p, val) (*(unsigned int *)(p) = (val))
#define ADDR_SUB(p, q) (int)((size_t)(p) - (size_t)(q))
/* Read the size and allocated fields from address p */
#define GET_SIZE(p) (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)

/* Given block ptr bp, compute address of its header and footer */
#define HDRP(bp) ((char *)(bp)-WSIZE)
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

#define NEXT_FRBP(bp) (bp)
#define PREV_FRBP(bp) ((char *)(bp) + WSIZE)

/* Given block ptr bp, compute address of next and previous blocks */
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp)-WSIZE)))
#define PREV_BLKP(bp) ((char *)(bp)-GET_SIZE(((char *)(bp)-DSIZE)))

/* Global variables */
static char *heap_listp = 0; /* Pointer to first block */
static char *fr_listp = 0;   /* Free_list */
/* Function prototypes for internal helper routines */
static void *extend_heap(size_t words);
static void place(void *bp, size_t asize);
static void *find_fit(size_t asize);
static void *coalesce(void *bp);

/* ansistant function */
static void add_free_block(void *bp);
static void delete_free_block(void *bp);

/*
 * Initialize: return -1 on error, 0 on success.
 */
int mm_init(void) {
  /* Create the initial empty heap */
  if ((heap_listp = mem_sbrk(4 * WSIZE)) == (void *)-1)
    return -1;
  PUT(heap_listp, 0);                            /* Alignment padding */
  PUT(heap_listp + (1 * WSIZE), PACK(DSIZE, 1)); /* Prologue header */
  PUT(heap_listp + (2 * WSIZE), PACK(DSIZE, 1)); /* Prologue footer */
  PUT(heap_listp + (3 * WSIZE), PACK(0, 1));     /* Epilogue header */
  heap_listp += (2 * WSIZE);
  fr_listp = 0;
  /* Extend the empty heap with a free block of CHUNKSIZE bytes */
  if (extend_heap(CHUNKSIZE / WSIZE) == NULL)
    return -1;
  return 0;
}

/*
 * malloc - Allocate a block with at least size bytes of payload
 */
void *mm_malloc(size_t size) {
  // printf("call malloc %lx\n", size);
  size_t asize;      /* Adjusted block size */
  size_t extendsize; /* Amount to extend heap if no fit */
  char *bp;
  if (heap_listp == 0) {
    mm_init();
  }
  /* Ignore spurious requests */
  if (size == 0)
    return NULL;

  /* Adjust block size to include overhead and alignment reqs. */
  if (size <= DSIZE)
    asize = 2 * DSIZE;
  else
    asize = DSIZE * ((size + (DSIZE) + (DSIZE - 1)) / DSIZE);

  /* Search the free list for a fit */
  if ((bp = find_fit(asize)) != NULL) {
    place(bp, asize);
    return bp;
  }

  /* No fit found. Get more memory and place the block */
  extendsize = MAX(asize, CHUNKSIZE);
  if ((bp = extend_heap(extendsize / WSIZE)) == NULL)
    return NULL;
  place(bp, asize);
  return bp;
}

/*
 * free - Free a block
 */
void mm_free(void *bp) {
  // printf("free %p\n", bp);
  if (bp == 0)
    return;
  size_t size = GET_SIZE(HDRP(bp));
  if (heap_listp == 0) {
    mm_init();
  }

  PUT(HDRP(bp), PACK(size, 0));
  PUT(FTRP(bp), PACK(size, 0));
  coalesce(bp);
}

/*
 * realloc - Naive implementation of realloc
 */
inline void *realloc(void *ptr, size_t size) {
  size_t oldsize;
  void *newptr;

  /* If size == 0 then this is just free, and we return NULL. */
  if (size == 0) {
    mm_free(ptr);
    return 0;
  }

  /* If oldptr is NULL, then this is just malloc. */
  if (ptr == NULL) {
    return mm_malloc(size);
  }

  newptr = mm_malloc(size);

  /* If realloc() fails the original block is left untouched  */
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
 * The remaining routines are internal helper routines
 */

/*
 * extend_heap - Extend heap with free block and return its block pointer
 */
inline static void *extend_heap(size_t words) {
  char *bp;
  size_t size;

  /* Allocate an even number of words to maintain alignment */
  size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;
  if ((long)(bp = mem_sbrk(size)) == -1)
    return NULL;
  /* Initialize free block header/footer and the epilogue header */
  PUT(HDRP(bp), PACK(size, 0));         /* Free block header */
  PUT(FTRP(bp), PACK(size, 0));         /* Free block footer */
  PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); /* New epilogue header */
  /* Coalesce if the previous block was free */
  return coalesce(bp);
}

/*
 * coalesce - Boundary tag coalescing. Return ptr to coalesced block
 */
inline static void *coalesce(void *bp) {
  size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
  size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
  size_t size = GET_SIZE(HDRP(bp));

  if (prev_alloc && next_alloc) { /* Case 1 */
    add_free_block(bp);
  }

  else if (prev_alloc && !next_alloc) { /* Case 2 */
    size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
    delete_free_block(NEXT_BLKP(bp));
    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    add_free_block(bp);
  }

  else if (!prev_alloc && next_alloc) { /* Case 3 */
    size += GET_SIZE(HDRP(PREV_BLKP(bp)));
    PUT(FTRP(bp), PACK(size, 0));
    PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
    bp = PREV_BLKP(bp);
  }

  else { /* Case 4 */
    size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp)));
    PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
    PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
    delete_free_block(NEXT_BLKP(bp));
    bp = PREV_BLKP(bp);
  }
  return bp;
}

/*
 * place - Place block of asize bytes at start of free block bp
 *         and split if remainder would be at least minimum block size
 */
inline static void place(void *bp, size_t asize) {
  size_t csize = GET_SIZE(HDRP(bp));
  if ((csize - asize) >= (2 * DSIZE)) {
    PUT(HDRP(bp), PACK(asize, 1));
    PUT(FTRP(bp), PACK(asize, 1));
    delete_free_block(bp);
    bp = NEXT_BLKP(bp);
    PUT(HDRP(bp), PACK(csize - asize, 0));
    PUT(FTRP(bp), PACK(csize - asize, 0));
    add_free_block(bp);
  } else {
    PUT(HDRP(bp), PACK(csize, 1));
    PUT(FTRP(bp), PACK(csize, 1));
    delete_free_block(bp);
  }
}

/*
 * find_fit - Find a fit for a block with asize bytes
 */
inline static void *find_fit(size_t asize) {
  void *bp = NULL;
  size_t tmp = 1 << 31;
  void *record = NULL;
  for (bp = fr_listp; bp != NULL && GET(NEXT_FRBP(bp)) != 0;
       bp = bp + (int)GET(NEXT_FRBP(bp))) {
    if (GET_SIZE(HDRP(bp)) >= asize && GET_SIZE(HDRP(bp)) < tmp) {
      record = bp;
      tmp = GET_SIZE(HDRP(bp));
    }
    if (tmp - asize < 256)
      return record;
  }
  if (bp != NULL && GET_SIZE(HDRP(bp)) >= asize && GET_SIZE(HDRP(bp)) < tmp) {
    return bp;
  }
  return record;
}
inline static void add_free_block(void *bp) {
  if (fr_listp == NULL) {
    fr_listp = bp;
    PUT(NEXT_FRBP(bp), 0);
    PUT(PREV_FRBP(bp), 0);
  } else {
    PUT(PREV_FRBP(bp), 0);
    PUT(NEXT_FRBP(bp), ADDR_SUB(fr_listp, bp));
    PUT(PREV_FRBP(fr_listp), ADDR_SUB(bp, fr_listp));
    fr_listp = bp;
  }
}
inline static void delete_free_block(void *bp) {
  if (bp == fr_listp) {
    if (GET(NEXT_FRBP(bp))) {
      fr_listp = bp + (int)(GET(NEXT_FRBP(bp)));
      PUT(PREV_FRBP(fr_listp), 0);
    } else {
      fr_listp = 0;
    }
  } else {
    if (GET(NEXT_FRBP(bp))) {
      char *tmp1 = (int)GET(PREV_FRBP(bp)) + bp;
      char *tmp2 = (int)GET(NEXT_FRBP(bp)) + bp;
      PUT(NEXT_FRBP(tmp1), ADDR_SUB(tmp2, tmp1));
      PUT(PREV_FRBP(tmp2), ADDR_SUB(tmp1, tmp2));
    } else {
      char *tmp = (int)GET(PREV_FRBP(bp)) + bp;
      PUT(NEXT_FRBP(tmp), 0);
    }
  }
}

/*
 * mm_checkheap - Check the heap for correctness. Helpful hint: You
 *                can call this function using mm_checkheap(__LINE__);
 *                to identify the line number of the call site.
 */
void mm_checkheap(int lineno) {
  switch (lineno) {
  case 0: {
    if (fr_listp == 0) {
      return;
    } else {
      char *tmp = fr_listp;
      while (GET(NEXT_FRBP(tmp))) {
        printf("this block %p size is %X, the next block is placed %X, the "
               "previous bolck is  %X\n",
               tmp, GET_SIZE(HDRP(tmp)), (int)GET(tmp),
               (int)GET(PREV_FRBP(tmp)));
        if (GET_ALLOC(tmp))
          printf("size is %x illegal!\n", GET_SIZE(HDRP(tmp)));
        tmp = tmp + (int)(GET(tmp));
      }
      printf("this block %p size is %X, the next block is placed %X, the "
             "previous bolck is  %X\n",
             tmp, GET_SIZE(HDRP(tmp)), (int)GET(tmp), (int)GET(PREV_FRBP(tmp)));
      if (GET_ALLOC(tmp))
        printf("size is %x illegal!\n", GET_SIZE(HDRP(tmp)));
    }
  }
  }
}
