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

// static char *heap_listp;  /* pointer to first block */

//
// function prototypes for internal helper routines
//
// static void *extend_heap(uint32_t words);
// static void place(void *bp, uint32_t asize);
// static void *coalesce(void *bp);
// static void printblock(void *bp);
// static void checkblock(void *bp);

static void *find_fit(uint32_t asize);
void print_heap();

//  single word (4) or double word (8) alignment
#define ALIGNMENT 8

// Rounds up to the nearest multiple of ALIGNMENT
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)

#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

#define BLK_HDR_SIZE ALIGN(sizeof(blockHdr))

typedef struct header blockHdr;

// Free list header structure
struct header {
  // Contains size of block and allocated bit
  size_t size;
  blockHdr *next_p;
  blockHdr *prior_p;
};

static inline void set_ftr(blockHdr *bp, int alloc) {
  PUT(((char *)(bp) + bp->size), PACK(bp->size, alloc));
}

static inline int ftr_alloc(blockHdr *bp) {
  return 0; 
}

// #define BLK_FTR_SIZE ALIGN(sizeof(blockFtr))

// typedef struct footer blockFtr;

// struct footer {
//   size_t size;
// };

// static inline void *blockFtr(blockHdr *bp) {
//   return ((char *)(bp) /*+ BLK_HDR_SIZE*/ + bp->size);
// }

//
// mm_init - Initialize the memory manager
//
int mm_init(void)
{
  // Create root node for empty free list
  blockHdr *bp = mem_sbrk(BLK_HDR_SIZE);
  bp->size = BLK_HDR_SIZE;
  bp->next_p = bp;
  bp->prior_p = bp;
  set_ftr(bp, 0);
  // .......
  // blockFtr *fp = mem_sbrk(BLK_FTR_SIZE);
  // fp->size = BLK_HDR_SIZE;
  return 0;
}

//
// print_heap - a test routine
//
void print_heap()
{
  blockHdr *bp = mem_heap_lo();
  while (bp < (blockHdr *)mem_heap_hi()) {
    printf("%s block at %p, size %d\n",
      (bp->size&1)?"allocated":"free", bp, (int)(bp->size & ~1));
    bp = (blockHdr *)((char *)bp +(bp->size & ~1));
  }
}

//
// mm_malloc - Allocate a block with at least size bytes of payload
//
void *mm_malloc(uint32_t size)
{
  // new block size is header + requested size
  int newsize = ALIGN(BLK_HDR_SIZE + size);
  // Call find_fit to request existing block of newsize
  blockHdr *bp = find_fit(newsize);

  // Did not find block of appropriate size in free list
  if (bp == NULL) {
    // Initialize a new block
    bp = mem_sbrk(newsize);
    // Space unavailable
    if ((long)bp == -1) {
      return NULL;
    }
    // Assign block size and set to allocated
    else
      bp->size = newsize | 1;
  }
  // Found a fit on the free list
  else {
    // Mark as allocated
    bp->size |= 1;
    // Remove from free list
    bp->prior_p->next_p = bp->next_p;
    bp->next_p->prior_p = bp->prior_p;
  }
  // Return pointer to the payload
  return (char *)bp + BLK_HDR_SIZE;
}

//
// find_fit - Find a fit for a block with asize bytes
//
static void *find_fit(uint32_t asize)
{
  blockHdr *bp;
  // Iterate through free list until end or find block of requested size
  for (bp = ((blockHdr *)mem_heap_lo())->next_p;
       bp != mem_heap_lo() && bp->size < asize;
       bp = bp->next_p);
  // Loop terminates either at a block of requested size, or at begining of free list, if there is no block of requested size

  // Loop has found an appropriate block on the free list <<?>>
  if (bp != mem_heap_lo())
    return bp;
  // There is no appropriate block on the free list
  // calling function must initialize new block <<?>>
  else
    return NULL;
}


//
// mm_free - Free a block
//
// ptr is a pointer to the payload of the block we want to free
void mm_free(void *ptr)
{
  blockHdr *bp = ptr-BLK_HDR_SIZE,
           *head = mem_heap_lo();   // Head of free list
  // Mark as unallocated
  bp->size &= ~1;
  // Add block to the front of the free list
  bp->next_p          = head->next_p;
  bp->prior_p         = head;
  head->next_p        = bp;
  bp->next_p->prior_p = bp;
}

//
// mm_realloc -- llist implementation
//
void *mm_realloc(void *ptr, uint32_t size)
{
  blockHdr *bp = ptr-BLK_HDR_SIZE;
  void *newptr = mm_malloc(size);
  // Ignore spurious input
  if (newptr == NULL)
    return NULL;
  int copySize = bp->size-BLK_HDR_SIZE;
  if (size < copySize)
    copySize = size;
  memcpy(newptr, ptr, copySize);
  mm_free(ptr);
  return newptr;
}

//
// extend_heap - Extend heap with free block and return its block pointer
//
// static void *extend_heap(uint32_t words)
// {
//   char *bp;
//   size_t size;
//   /* Allocate an even number of words to maintain alignment */
//   size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;
//   if ((long)(bp = mem_sbrk(size)) == -1)
//       return NULL;
//    //Initialize free block header/footer and the epilouge header
//   PUT(HDRP(bp), PACK(size,0));  /* Free block header */
//   PUT(FTRP(bp), PACK(size,0)); /* Free block footer */
//   PUT(HDRP(NEXT_BLKP(bp)), PACK(0,1)); /* New Epilouge header */
//   /* Coalesce if the previous block was free */
//   return coalesce(bp);
// }

//
// coalesce - boundary tag coalescing. Return ptr to coalesced block
//
// static void *coalesce(void *bp)
// {
//   size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
//   size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
//   size_t size = GET_SIZE(HDRP(bp));

//   if (prev_alloc && next_alloc) {         // Case 1
//       return bp;
//   }

//   else if (prev_alloc && !next_alloc) {   // Case 2
//       size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
//       PUT(HDRP(bp), PACK(size, 0));
//       PUT(FTRP(bp), PACK(size, 0));
//   }

//   else if (!prev_alloc && next_alloc) {   // Case 3
//       size += GET_SIZE(HDRP(PREV_BLKP(bp)));
//       PUT(FTRP(bp), PACK(size, 0));
//       PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
//       bp = PREV_BLKP(bp);
//   }

//   else {                                  // Case 4
//       size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp)));
//       PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
//       PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
//       bp = PREV_BLKP(bp);
//   }
//   return bp;
// }



//
//
// Practice problem 9.9
//
// place - Place block of asize bytes at start of free block bp
//         and split if remainder would be at least minimum block size
//
// static void place(void *bp, uint32_t asize)
// {
//   size_t csize = GET_SIZE(HDRP(bp));

//   if ((csize - asize) >= (2*DSIZE)) {
//     PUT(HDRP(bp), PACK(asize, 1));
//     PUT(FTRP(bp), PACK(asize, 1));
//     bp = NEXT_BLKP(bp);
//     PUT(HDRP(bp), PACK(csize-asize, 0));
//     PUT(FTRP(bp), PACK(csize-asize, 0));
//   }

//   else {
//     PUT(HDRP(bp), PACK(csize, 1));
//     PUT(FTRP(bp), PACK(csize, 1));
//   }
// }




// //
// // mm_checkheap - Check the heap for consistency
// //
// void mm_checkheap(int verbose)
// {
//   //
//   // This provided implementation assumes you're using the structure
//   // of the sample solution in the text. If not, omit this code
//   // and provide your own mm_checkheap
//   //
//   void *bp = heap_listp;

//   if (verbose) {
//     printf("Heap (%p):\n", heap_listp);
//   }

//   if ((GET_SIZE(HDRP(heap_listp)) != DSIZE) || !GET_ALLOC(HDRP(heap_listp))) {
// 	printf("Bad prologue header\n");
//   }
//   checkblock(heap_listp);

//   for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) {
//     if (verbose)  {
//       printblock(bp);
//     }
//     checkblock(bp);
//   }

//   if (verbose) {
//     printblock(bp);
//   }

//   if ((GET_SIZE(HDRP(bp)) != 0) || !(GET_ALLOC(HDRP(bp)))) {
//     printf("Bad epilogue header\n");
//   }
// }

// static void printblock(void *bp)
// {
//   uint32_t hsize, halloc, fsize, falloc;

//   hsize = GET_SIZE(HDRP(bp));
//   halloc = GET_ALLOC(HDRP(bp));
//   fsize = GET_SIZE(FTRP(bp));
//   falloc = GET_ALLOC(FTRP(bp));

//   if (hsize == 0) {
//     printf("%p: EOL\n", bp);
//     return;
//   }

//   printf("%p: header: [%d:%c] footer: [%d:%c]\n",
// 	 bp,
// 	 (int) hsize, (halloc ? 'a' : 'f'),
// 	 (int) fsize, (falloc ? 'a' : 'f'));
// }

// static void checkblock(void *bp)
// {
//   if ((uintptr_t)bp % 8) {
//     printf("Error: %p is not doubleword aligned\n", bp);
//   }
//   if (GET(HDRP(bp)) != GET(FTRP(bp))) {
//     printf("Error: header does not match footer\n");
//   }
// }

