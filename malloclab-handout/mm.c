/*
 * mm-naive.c - The fastest, least memory-efficient malloc package.
 *
 * In this naive approach, a block is allocated by simply incrementing
 * the brk pointer.  Blocks are never coalesced or reused.  The size of
 * a block is found at the first aligned word before the block (we need
 * it for realloc).
 *
 * This code is correct and blazingly fast, but very bad usage-wise since
 * it never frees anything.
 */
#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#include "mm.h"
#include "memlib.h"

/* If you want debugging output, use the following macro.  When you hand
 * in, remove the #define DEBUG line. */
#define DEBUG
#ifdef DEBUG
# define dbg_printf(...) printf(__VA_ARGS__)
#else
# define dbg_printf(...)
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
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)


#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

#define SIZE_PTR(p)  ((size_t*)(((char*)(p)) - SIZE_T_SIZE))

#define NEXT_FITx

#define WSIZE   4
#define DSIZE   8
#define CHUNKSIZE (1<<12)

#define MAX(x, y) ((x) > (y)? (x) : (y))

/*Pack a size and allocated bit into word*/
#define PACK(size, alloc) ((size) | (alloc))

/*Read and wirte a word at addres p */
#define GET(p)  (*(unsigned int *)(p))
#define PUT(p, val) (*(unsigned int *)(p) = (val))

/*Read the size and allocated fields from address p */
#define GET_SIZE(p) (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)

/*Given block ptr bp, compute address of its header and footer */
#define HDRP(bp)    ((char *)(bp) - WSIZE)
#define FTRP(bp)    ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

/*Given block ptr bp, compute address of next and previous blocks */
#define NEXT_BLKP(bp)   ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
#define PREV_BLKP(bp)   ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))

/*Given empty block ptr bp, compute address of empty predecessor and successor */
#define PRED(bp) ((char *)(bp))
#define SUCC(bp) ((char *)(bp) + WSIZE)

static char *heap_listp = 0;
static char *empty_listp = 0;
static char *start_list = 0;
#ifdef NEXT_FIT
static char *rover;
#endif

static void *extend_heap(size_t words);
static void place(void *bp, size_t asize);
static void *find_fit(size_t asize);
static void *coalesce(void *bp);
static void printblock(void *bp);
//static void mm_checkheap(int verbose);
static void checkblock(void *bp);
static void *r_coalesce(void *bp, size_t newsize, int *is_a_free);
static void r_place(void *bp, size_t asize);
inline void insert_freeblock(char *bp);
inline char *get_freeroot(size_t size);
/*
 * mm_init - Called when a new trace starts.
 */
int mm_init(void)
{
  if ((heap_listp = mem_sbrk(12*WSIZE)) == (void *)-1)
      return -1;
  PUT(heap_listp, 0);
  PUT(heap_listp + (1*WSIZE), 0);
  PUT(heap_listp + (2*WSIZE), 0);
  PUT(heap_listp + (3*WSIZE), 0);
  PUT(heap_listp + (4*WSIZE), 0);
  PUT(heap_listp + (5*WSIZE), 0);
  PUT(heap_listp + (6*WSIZE), 0);
  PUT(heap_listp + (7*WSIZE), 0);
  PUT(heap_listp + (8*WSIZE), 0);
  PUT(heap_listp + (9*WSIZE), PACK(DSIZE, 1));
  PUT(heap_listp + (10*WSIZE), PACK(DSIZE, 1));
  PUT(heap_listp + (11*WSIZE), PACK(0,1));
  start_list = heap_listp;
  heap_listp += (10*WSIZE);
  empty_listp = heap_listp;
#ifdef NEXTFIT
  rover = heap_listp;
#endif

  if (extend_heap(CHUNKSIZE/WSIZE) == NULL)
      return -1;
  return 0;
}

/*
 * malloc - Allocate a block by incrementing the brk pointer.
 *      Always allocate a block whose size is a multiple of the alignment.
 */
void *malloc(size_t size)
{
  size_t asize;
  size_t extendsize;
  char *bp;

  if (heap_listp == 0) {
    mm_init();
  }

  if (size == 0)
      return NULL;

  if (size <= DSIZE)
      asize = 2*DSIZE;
  else
      asize = DSIZE * ((size + (DSIZE) + (DSIZE-1)) / DSIZE);

  if ((bp = find_fit(asize)) != NULL) {
    place(bp, asize);
    return bp;
  }

  extendsize = MAX(asize,CHUNKSIZE);
  if ((bp = extend_heap(extendsize/WSIZE)) == NULL)
      return NULL;
  place(bp, asize);
  return bp;
  //int newsize = ALIGN(size + SIZE_T_SIZE);
  //unsigned char *p = mem_sbrk(newsize);
  ////dbg_printf("malloc %u => %p\n", size, p);

  //if ((long)p < 0)
  //  return NULL;
  //else {
  //  p += SIZE_T_SIZE;
  //  *SIZE_PTR(p) = size;
  //  return p;
  //}
}

/*
 * free - We don't know how to free a block.  So we ignore this call.
 *      Computers have big memories; surely it won't be a problem.
 */
void free(void *bp)
{
	/*Get gcc to be quiet */
  if (bp == 0)
      return;
  size_t size = GET_SIZE(HDRP(bp));
  if (heap_listp == 0) {
    mm_init();
  }
  PUT(HDRP(bp), PACK(size, 0));
  PUT(FTRP(bp), PACK(size, 0));
  PUT(PRED(bp), NULL);
  PUT(SUCC(bp), NULL);
  coalesce(bp);
}


static void *coalesce(void *bp)
{
  size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
  size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
  size_t size = GET_SIZE(HDRP(bp));

  if (prev_alloc && next_alloc) {
    return bp;
  }
  else if (prev_alloc && !next_alloc) {
    size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
    remove_freeblock(NEXT_BLKP(bp));
    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
  }
  else if (!prev_alloc && next_alloc) {
    size += GET_SIZE(HDRP(PREV_BLKP(bp)));
    remove_freeblock(PREV_BLKP(bp));
    PUT(FTRP(bp), PACK(size, 0));
    PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
    bp = PREV_BLKP(bp);
  }
  else {
    size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp)));
    remove_freeblock(PREV_BLKP(bp));
    remove_freeblock(NEXT_BLKP(bp));
    PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
    PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
    bp = PREV_BLKP(bp);
  }
  insert_freeblock(bp);

#ifdef NEXT_FIT
  if ((rover > (char*)bp) && (rover < NEXT_BLKP(bp)))
      rover bp;
#endif
  return bp;
}

inline void insert_freeblock(char *bp)
{
  char *root = get_freeroot(GET_SIZE(HDRP(bp)));
  char *prevp = root;
  char *nextp = GET(root);

  while (nextp != NULL) {
    if (GET_SIZE(HDRP(nextp)) >= GET_SIZE(HDRP(bp))) break;
    prevp = nextp;
    nextp = GET(SUCC(nextp));
  }

  if (prevp == root) {
    PUT(root, bp);
    PUT(PRED(bp), NULL);
  } else {
    PUT(SUCC(prevp), bp);
    PUT(PRED(bp), prevp);
  }
  PUT(SUCC(bp), nextp);
  if (nextp != NULL) PUT(PRED(nextp), bp);
}

inline void remove_freeblock(char *bp)
{
  char *root = get_freeroot(GET_SIZE(HDRP(bp)));
  char *prevp = GET(PRED(bp));
  char *nextp = GET(SUCC(bp));
  if (prevp == NULL) {
    if (nextp != NULL) PUT(PRED(nextp), 0);
    PUT(root, nextp);
  } else {
    if (nextp != NULL) PUT(PRED(nextp), prevp);
    PUT(SUCC(prevp), nextp);
  }
  PUT(SUCC(bp), NULL);
  PUT(PRED(bp), NULL);
}
/*
 * realloc - Change the size of the block by mallocing a new block,
 *      copying its data, and freeing the old block.  I'm too lazy
 *      to do better.
 */
void *realloc(void *oldptr, size_t size)
{
  size_t oldsize;
  void *newptr;
  size_t asize;

  /* If size == 0 then this is just free, and we return NULL. */
  if(size == 0) {
    free(oldptr);
    return 0;
  }

  /* If oldptr is NULL, then this is just malloc. */
  if(oldptr == NULL) {
    return malloc(size);
  }

  if(size <= DSIZE){
    asize = 2*(DSIZE);
  } else {
    asize = (DSIZE)*((size+(DSIZE)+(DSIZE-1))/(DSIZE));
  }

  oldsize = *SIZE_PTR(oldptr);
  if(oldsize == asize) return oldptr;
  if(oldsize < asize){
    int is_a_free;
    char *bp = r_coalesce(oldptr, asize, &is_a_free);
    if(is_a_free == 1){
        r_place(bp, asize);
        return bp;
    } else if(is_a_free == 0 && bp != oldptr){
        memcpy(bp, oldptr, oldsize);
        r_place(bp, asize);
        return bp;
    } else {
        newptr = malloc(size);
        memcpy(newptr, oldptr, oldsize);
        free(oldptr);
        return newptr;
    }
  }
  else  
  {
      r_place(oldptr, asize);
      return oldptr;
  }

}

static void *r_coalesce(void *bp, size_t newsize, int *is_a_free)
{
  size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
  size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
  size_t size = GET_SIZE(HDRP(bp));
  *is_a_free = 0;

  if(prev_alloc && next_alloc){
  
  } else if(prev_alloc && !next_alloc) {
    size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
    if(size >= newsize){
        remove_freeblock(NEXT_BLKP(bp));
        PUT(HDRP(bp), PACK(size,1));
        PUT(FTRP(bp), PACK(size,1));
        *is_a_free = 1;
        return bp;
    }
  } else if (!prev_alloc && next_alloc) {
    size += GET_SIZE(HDRP(PREV_BLKP(bp)));
    if (size >= newsize) {
        remove_freeblock(PREV_BLKP(bp));
        PUT(FTRP(bp), PACK(size, 1));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 1));
        bp = PREV_BLKP(bp);
        return bp;
    }
  } else {
    size += GET_SIZE(FTRP(NEXT_BLKP(bp))) + GET_SIZE(HDRP(PREV_BLKP(bp)));
    if (size >= newsize) {
        remove_freeblock(PREV_BLKP(bp));
        remove_freeblock(NEXT_BLKP(bp));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 1));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 1));
        bp = PREV_BLKP(bp);
    }
  }
  return bp;
}

static void r_place(void *bp, size_t asize)
{
   size_t csize = GET_SIZE(HDRP(bp));
   if ((csize - asize) >= (2*DSIZE)) {
     PUT(HDRP(bp), PACK(asize,1));
     PUT(FTRP(bp), PACK(asize,1));
     bp = NEXT_BLKP(bp);

     PUT(HDRP(bp),PACK(csize-asize,0));
     PUT(FTRP(bp),PACK(csize-asize,0));
     PUT(SUCC(bp),0);
     PUT(PRED(bp),0);
     coalesce(bp);
   } else {
     PUT(HDRP(bp),PACK(csize,1));
     PUT(FTRP(bp),PACK(csize,1));
   }
}
/*
 * calloc - Allocate the block and set it to zero.
 */
void *calloc (size_t nmemb, size_t size)
{
  size_t bytes = nmemb * size;
  void *newptr;

  newptr = malloc(bytes);
  memset(newptr, 0, bytes);

  return newptr;
}

/*
 * mm_checkheap - There are no bugs in my code, so I don't need to check,
 *      so nah!
 */
void mm_checkheap(int verbose){
	/*Get gcc to be quiet. */
  char *bp = heap_listp;

  if (verbose)
      printf("Heap (%p):\n",heap_listp);

  if ((GET_SIZE(HDRP(heap_listp)) != DSIZE) || !GET_ALLOC(HDRP(heap_listp)))
      printf("Bad prologue header\n");
  checkblock(heap_listp);

  for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) {
    if (verbose)
        printblock(bp);
    checkblock(bp);
  }

  if (verbose)
      printblock(bp);
  if ((GET_SIZE(HDRP(bp)) != 0) || !(GET_ALLOC(HDRP(bp))))
      printf("Bad eilogue headre\n");
}

static void *extend_heap(size_t words)
{
  char *bp;
  size_t size;

  size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;
  if ((long)(bp = mem_sbrk(size)) == -1)
      return NULL;

  PUT(HDRP(bp), PACK(size, 0));
  PUT(FTRP(bp), PACK(size, 0));
  PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1));
  PUT(PRED(bp), 0); 
  PUT(SUCC(bp), 0);

  return coalesce(bp);
}

static void place(void *bp, size_t asize)
{
  size_t csize = GET_SIZE(HDRP(bp));
  remove_freeblock(bp);

  if ((csize - asize) >= (2*DSIZE)) {
    PUT(HDRP(bp), PACK(asize, 1));
    PUT(FTRP(bp), PACK(asize, 1));
    bp = NEXT_BLKP(bp);
    PUT(HDRP(bp), PACK(csize - asize, 0));
    PUT(FTRP(bp), PACK(csize - asize, 0));
    coalesce(bp);
  }
  else {
    PUT(HDRP(bp), PACK(csize, 1));
    PUT(FTRP(bp), PACK(csize, 1));
  }
}


static void *find_fit(size_t asize)
{
  char *root = get_freeroot(asize);
  char *p = GET(root);
  for (; root != heap_listp - (2*WSIZE); root += WSIZE) {
    char *p = GET(root);
    while (p != NULL) {
      if (GET_SIZE(HDRP(p)) >= asize) return p;
      p = GET(SUCC(p));
    }
  }
  return NULL;
/*
#ifdef NEXT_FIT
    char *oldrover = rover;

    for (; GET_SIZE(HDRP(rover)) > 0; rover = NEXT_BLKP(rover))
        if (!GET_ALLOC(HDRP(rover)) && (asize <= GET_SIZE(HDRP(rover))))
            return rover;
    return NULL;
#else

    void *bp;

    for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) {
        if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp))))
            return bp;
    }
    return NULL;
#endif
*/
}

inline char *get_freeroot(size_t size)
{
  int i = 0;
  if (size <= 8) i = 0;
  else if (size <= 16) i = 0;
  else if (size <= 32) i = 0;
  else if (size <= 64) i = 1;
  else if (size <= 128) i = 2;
  else if (size <= 256) i = 3;
  else if (size <= 512) i = 4;
  else if (size <= 1024) i = 5;
  else if (size <= 2048) i = 6;
  else i = 7;

  return start_list + (i*WSIZE);
}

static void printblock(void *bp)
{
  size_t hsize, halloc, fsize, falloc;

  mm_checkheap(0);
  hsize = GET_SIZE(HDRP(bp));
  halloc = GET_ALLOC(HDRP(bp));
  fsize = GET_SIZE(FTRP(bp));
  falloc = GET_ALLOC(FTRP(bp));

  if (hsize == 0) {
    printf("%p: header: [%ld:%c] footer: [%ld:%c]\n", bp,
            hsize, (halloc ? 'a' : 'f'),
            fsize, (falloc ? 'a' : 'f'));
  }
}

static void checkblock(void *bp)
{
  if ((size_t)bp % 8)
      printf("Error: %p is not doubleword aligned\n", bp);
  if (GET(HDRP(bp)) != GET(FTRP(bp)))
      printf("Error: header does not match footer\n");
}

