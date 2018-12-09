  int newsize = ALIGN(BLK_HDR_SIZE + size);
  void *p = mem_sbreak(newsize);
  if ((long)p == -1)
    return NULL;
  else {
    *(size_t *)p = size;
    return (void *)((char *)p + SIZE_T_SIZE);
  }

#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))


// bp should be the root of the free list to add newbp to front of list
static void push(blockHdr *bp, void *nbp)
{
  blockHdr *newbp = *nbp + sizeof(HDRP);
  newbp->next = bp->next;
  newbp->prev = bp;
  bp->next = newbp;
  newbp->next->prev = newbp;
}
