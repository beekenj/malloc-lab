/*
 * mm-implicit.c -  Simple allocator based on implicit free lists,
 *                  first fit placement, and boundary tag coalescing.
 *
 * Each block has header and footer of the form:
 *
 *      31                     3  2  1  0
 *      -----------------------------------
 *     | s  s  s  s  ... s  s  s  0  0  a/f
 *      -----------------------------------
 *
 * where s are the meaningful size bits and a/f is set
 * iff the block is allocated. The list has the following form:
 *
 * begin                                                          end
 * heap                                                           heap
 *  -----------------------------------------------------------------
 * |  pad   | hdr(8:a) | ftr(8:a) | zero or more usr blks | hdr(8:a) |
 *  -----------------------------------------------------------------
 *          |       prologue      |                       | epilogue |
 *          |         block       |                       | block    |
 *
 * The allocated prologue and epilogue blocks are overhead that
 * eliminate edge conditions during coalescing.
 */
#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>
#include <memory.h>
#include "mm.h"
#include "memlib.h"

/*********************************************************
 * NOTE TO STUDENTS: Before you do anything else, please
 * provide your team information in the following struct.
 ********************************************************/
team_t team = {
  /* Team name */
  "Beeken",
  /* First member's full name */
  "Jack Beeken",
  /* First member's email address */
  "beekenj@colorado.edu",
  /* Second member's full name (leave blank if none) */
  "",
  /* Second member's email address (leave blank if none) */
  ""
};

/////////////////////////////////////////////////////////////////////////////
// Constants and macros
//
// These correspond to the material in Figure 9.43 of the text
// The macros have been turned into C++ inline functions to
// make debugging code easier.
//
/////////////////////////////////////////////////////////////////////////////
#define WSIZE       4       /* word size (bytes) */
#define DSIZE       8       /* doubleword size (bytes) */
#define CHUNKSIZE  (1<<12)  /* initial heap size (bytes) */
#define OVERHEAD    8       /* overhead of header and footer (bytes) */

//  single word (4) or double word (8) alignment
#define ALIGNMENT 8

// Rounds up to the nearest multiple of ALIGNMENT
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)

#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

#define BLK_HDR_SIZE ALIGN(sizeof(blockHdr))

typedef struct header blockHdr;

// Free list header structure
struct header {
  // blockHdr *bp = mem_sbrk(BLK_HDR_SIZE);
  blockHdr *next;
  blockHdr *prev;
};

// void FL_init(blockHdr *bp)
// {
//   bp->next = bp;
//   bp->prev = bp;
// }

// bp should be the root of the free list to add newbp to front of list
static void push(blockHdr *bp, blockHdr *newbp)
{
  newbp->next = bp->next;
  newbp->prev = bp;
  bp->next = newbp;
  newbp->next->prev = newbp;
}

static void pop(blockHdr *bp)
{
  bp->prev->next = bp->next;
  bp->next->prev = bp->prev;
  bp->next = NULL;
  bp->prev = NULL;
}

static inline int MAX(int x, int y) {
  return x > y ? x : y;
}

//
// Pack a size and allocated bit into a word
// We mask of the "alloc" field to insure only
// the lower bit is used
//
static inline uint32_t PACK(uint32_t size, int alloc) {
  return ((size) | (alloc & 0x1));
}

//
// Read and write a word at address p
//
static inline uint32_t GET(void *p) { return  *(uint32_t *)p; }
static inline void PUT( void *p, uint32_t val)
{
  *((uint32_t *)p) = val;
}

//
// Read the size and allocated fields from address p
//
static inline uint32_t GET_SIZE( void *p )  {
  return GET(p) & ~0x7;
}

static inline int GET_ALLOC( void *p  ) {
  return GET(p) & 0x1;
}

//
// Given block ptr bp, compute address of its header and footer
//
static inline void *HDRP(void *bp) {

  return ( (char *)bp) - WSIZE;
}
static inline void *FTRP(void *bp) {
  return ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE);
}

//
// Given block ptr bp, compute address of next and previous blocks
//
static inline void *NEXT_BLKP(void *bp) {
  return  ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)));
}

static inline void* PREV_BLKP(void *bp){
  return  ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)));
}

/////////////////////////////////////////////////////////////////////////////
//
// Global Variables
//

static char *heap_listp;  /* pointer to first block */

// Start my vars
blockHdr *free_list;
// End

//
// function prototypes for internal helper routines
//
static void *extend_heap(uint32_t words);
static void place(void *bp, uint32_t asize);
static void *find_fit(uint32_t asize);
static void *coalesce(void *bp);
static void printblock(void *bp);
static void checkblock(void *bp);

//
// mm_init - Initialize the memory manager
//
int mm_init(void)
{

  // Initialize empty free list
  free_list = mem_sbrk(BLK_HDR_SIZE);
  free_list->next = free_list;
  free_list->prev = free_list;

  // Create the initial empty heap
  if ((heap_listp = mem_sbrk(4*WSIZE)) == (void *)-1) return 1;
  PUT(heap_listp, 0);                                           // Alignment Padding
  PUT(heap_listp + (1*WSIZE), PACK(DSIZE, 1));                  // Prologue header
  PUT(heap_listp + (2*WSIZE), PACK(DSIZE, 1));                  // Prologue footer
  PUT(heap_listp + (3*WSIZE), PACK(0, 1));                  // Epilogue header
  heap_listp += (2*WSIZE);

  // Extend the empty heap with a free block of CHUNKSIZE bytes
  if (extend_heap(CHUNKSIZE/WSIZE) == NULL) return -1;

  return 0;
}


//
// extend_heap - Extend heap with free block and return its block pointer
//
static void *extend_heap(uint32_t words)
{
  char *bp;
  size_t size;
  /* Allocate an even number of words to maintain alignment */
  size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;
  if ((long)(bp = mem_sbrk(size)) == -1)
      return NULL;
  /* Initialize free block header/footer and the epilouge header*/
  PUT(HDRP(bp), PACK(size,0)); /* Free block header */
  PUT(FTRP(bp), PACK(size,0)); /* Free block footer */
  PUT(HDRP(NEXT_BLKP(bp)), PACK(0,1)); /* New Epilouge header */
  /* Coalesce if the previous block was free */
  return coalesce(bp);
}


//
// Practice problem 9.8
//
// find_fit - Find a fit for a block with asize bytes
//
static void *find_fit(uint32_t asize)
{
  // First-fit search
  blockHdr *bp;
  // Iterate through free list until loop back to root, or find block of requested size
  for (bp = free_list->next; bp != free_list; bp = bp->next) {
    if ((bp != free_list) && (asize <= GET_SIZE(HDRP(bp))))
      // Loop has found an appropriate block on the free list
      return bp;
  }
  // There is no appropriate block on the free list
  // calling function must initialize new block
  return NULL;
}

//
// mm_free - Free a block
//
void mm_free(void *ptr)
{
  blockHdr *bp = ptr;

  size_t size = GET_SIZE(HDRP(ptr));

  PUT(HDRP(ptr), PACK(size, 0));
  PUT(FTRP(ptr), PACK(size, 0));

  push(free_list, bp);

  // coalesce(bp);

}

//
// coalesce - boundary tag coalescing. Return ptr to coalesced block
//
static void *coalesce(void *bp)
{
  blockHdr *ptr = bp;
  blockHdr *nextb = NEXT_BLKP(bp);
  // blockHdr *prevb = PREV_BLKP(bp);

  size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
  size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
  size_t size = GET_SIZE(HDRP(bp));

  // Case 1: Previous block and next block both allocated
  if (prev_alloc && next_alloc) {
      push(free_list, ptr);
      return bp;
  }

  // Case 2: Previous block allocated, next block free
  else if (prev_alloc && !next_alloc) {

      pop(nextb);
      push(free_list, ptr);

      size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
      PUT(HDRP(bp), PACK(size, 0));
      PUT(FTRP(bp), PACK(size, 0));
  }

  // Case 3: Previous block free, next block allocated
  else if (!prev_alloc && next_alloc) {
      size += GET_SIZE(HDRP(PREV_BLKP(bp)));
      PUT(FTRP(bp), PACK(size, 0));
      PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
      bp = PREV_BLKP(bp);
  }

  // Case 4: Previous block and next block both free
  else {
      size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp)));

      pop(nextb);
      PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
      PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
      bp = PREV_BLKP(bp);
  }
  return bp;
}

//
// mm_malloc - Allocate a block with at least size bytes of payload
//
void *mm_malloc(uint32_t size)
{
  //
  // You need to provide this
  //
  size_t asize;         // Adjusted block size
  size_t extendsize;    // Amount to extend the heap if no fit
  char *bp;

  // Ignore squrious requests
  if (size == 0)
      return NULL;

  // Adjust block size to include overhead and alignment reqs.
  if (size <= DSIZE)
      asize = 2*DSIZE;
  else
      asize = DSIZE * ((size + (DSIZE) + (DSIZE-1)) / DSIZE);

  // Search the free list for a fit
  if ((bp = find_fit(asize)) != NULL) {
      place(bp, asize);
      return bp;
  }

  // No fit found. Get more memory and place the block
  extendsize = MAX(asize, CHUNKSIZE);
  if ((bp = extend_heap(extendsize/WSIZE)) == NULL)
      return NULL;
  place(bp, asize);
  return bp;
}

//
//
// Practice problem 9.9
//
// place - Place block of asize bytes at start of free block bp
//         and split if remainder would be at least minimum block size
//
static void place(void *bp, uint32_t asize)
{
  size_t csize = GET_SIZE(HDRP(bp));

  if ((csize - asize) >= (2*DSIZE)) {
    PUT(HDRP(bp), PACK(asize, 1));
    PUT(FTRP(bp), PACK(asize, 1));
    bp = NEXT_BLKP(bp);
    PUT(HDRP(bp), PACK(csize-asize, 0));
    PUT(FTRP(bp), PACK(csize-asize, 0));
  }

  else {
    PUT(HDRP(bp), PACK(csize, 1));
    PUT(FTRP(bp), PACK(csize, 1));
  }
}


//
// mm_realloc -- implemented for you
//
void *mm_realloc(void *ptr, uint32_t size)
{
  void *newp;
  uint32_t copySize;

  newp = mm_malloc(size);
  if (newp == NULL) {
    printf("ERROR: mm_malloc failed in mm_realloc\n");
    exit(1);
  }
  copySize = GET_SIZE(HDRP(ptr));
  if (size < copySize) {
    copySize = size;
  }
  memcpy(newp, ptr, copySize);
  mm_free(ptr);
  return newp;
}

//
// mm_checkheap - Check the heap for consistency
//
void mm_checkheap(int verbose)
{
  //
  // This provided implementation assumes you're using the structure
  // of the sample solution in the text. If not, omit this code
  // and provide your own mm_checkheap
  //
  void *bp = heap_listp;

  if (verbose) {
    printf("Heap (%p):\n", heap_listp);
  }

  if ((GET_SIZE(HDRP(heap_listp)) != DSIZE) || !GET_ALLOC(HDRP(heap_listp))) {
	printf("Bad prologue header\n");
  }
  checkblock(heap_listp);

  for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) {
    if (verbose)  {
      printblock(bp);
    }
    checkblock(bp);
  }

  if (verbose) {
    printblock(bp);
  }

  if ((GET_SIZE(HDRP(bp)) != 0) || !(GET_ALLOC(HDRP(bp)))) {
    printf("Bad epilogue header\n");
  }
}

static void printblock(void *bp)
{
  uint32_t hsize, halloc, fsize, falloc;

  hsize = GET_SIZE(HDRP(bp));
  halloc = GET_ALLOC(HDRP(bp));
  fsize = GET_SIZE(FTRP(bp));
  falloc = GET_ALLOC(FTRP(bp));

  if (hsize == 0) {
    printf("%p: EOL\n", bp);
    return;
  }

  printf("%p: header: [%d:%c] footer: [%d:%c]\n",
	 bp,
	 (int) hsize, (halloc ? 'a' : 'f'),
	 (int) fsize, (falloc ? 'a' : 'f'));
}

static void checkblock(void *bp)
{
  if ((uintptr_t)bp % 8) {
    printf("Error: %p is not doubleword aligned\n", bp);
  }
  if (GET(HDRP(bp)) != GET(FTRP(bp))) {
    printf("Error: header does not match footer\n");
  }
}

