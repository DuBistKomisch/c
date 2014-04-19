/*
 * mm.c
 * author: Jake Barnes (s3334445)
 *
 * This solution uses a segregated fit explicit free list strategy, with
 * header and footer records to support coalescing.
 *
 * The structure of a block is like so:
 * bytes: 0 1 2 3 4 5 6 7 8 9 10 11 . . . . . . . . . . 12 13 14 15
 *        [head ] [prev ] [next   ] [payload + padding] [foot     ]
 *
 * The payload is aligned to 8 bytes, so the header of one block and the
 * footer of the next share an 8 byte area of memory. The heap is initialised
 * with a fake allocated block at the start, and a fake allocated header at the
 * end, in order to avoid special cases while coalescing.
 *
 * The header and footer are identical, containing the size of the block,
 * however the last three bits don't count for the size and instead indicate
 * the state (free = 000 or allocated = 001).
 * The previous and next pointers maintain the structure of the explicit free
 * linked lists. In an allocated block, they are ignored.
 *
 * There are a series of linked list, segregated by block size by powers of 2.
 * Blocks larger than the largest segregation are put in a special list.
 * A first and last pointer are also maintained for each list.
 *
 * Coalescing is performed after freeing a block, getting a new block from the
 * heap, and when splitting a block.
 *
 * Splitting is always performed when allocating a block (assuming there is
 * enough to split off to fit the block overhead), and also when a realloc
 * request is submitted to shrink a block.
 *
 * Blocks are found by "first fit" searching each linked list successively,
 * starting with the smallest the desired block size would be in. The special
 * "oversized" list is also searched as a last resort.
 *
 * The heap is only extended when no suitable block can be found, and by the
 * size of the block desired.
 *
 * Realloc will handle special cases efficiently:
 *  - If the requested size is smaller than the original,
 *    it is simply shrunk in place via splitting.
 *  - If there is a big enough free block before the current block,
 *    it will be expanded by moving the data backwards and splitting.
 *  - If there is a big enough free block after the current block,
 *    it will be expanded into it and split.
 *  - Otherwise, a new block is simply allocated and the data copied over.
 */

#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>
#include <string.h>

#include "mm.h"
#include "memlib.h"

/* state flags */
#define FREE 0
#define ALLOCATED 1

/* rounds up to the nearest multiple of 8 bytes */
#define WORD 4
#define OVERHEAD 16
#define ALIGN(size) (((size) + 0x7) & ~0x7)

/* read/write a word pointed to */
#define VALUE(p) (*(unsigned int *)(p))

/* pack the block size and allocation state into one word */
#define PACK(size, state) ((size)|(state))
#define UNPACK_SIZE(p) (VALUE(p) & ~0x7)
#define UNPACK_STATE(p) (VALUE(p) & 0x1)
#define REPACK_SIZE(p, size) (VALUE(p) = PACK(size, UNPACK_STATE(p)))
#define REPACK_STATE(p, state) (VALUE(p) = PACK(UNPACK_SIZE(p), state))

/* pointer magic for block pointers */
#define HEADER(bp) ((char *)(bp) - OVERHEAD + WORD)
#define FOOTER(bp) ((char *)(bp) - OVERHEAD + UNPACK_SIZE(HEADER(bp)))
#define NEXT_HEADER(bp) ((char *)(bp) \
    - OVERHEAD + WORD + UNPACK_SIZE(HEADER(bp)))
#define PREV_FOOTER(bp) ((char *)(bp) - OVERHEAD)
#define NEXT_BLOCK(bp) ((char *)(bp) + UNPACK_SIZE(HEADER(bp)))
#define PREV_BLOCK(bp) ((char *)(bp) - UNPACK_SIZE(PREV_FOOTER(bp)))

/* pointer magic for explicit free list */
#define NEXT_FREE(bp) (*(void **)((char *)(bp) - WORD))
#define PREV_FREE(bp) (*(void **)((char *)(bp) - 2 * WORD))

/* pointers to the first and last free blocks
 * each element is a segregated list with blocks of size 2^(n-1)+1..2^n
 * 0th element is special and is a list of oversized blocks*/
#define MAX_SEG 13
static char *first[MAX_SEG];
static char *last[MAX_SEG];

/*
 * list_find
 * O(MAX_SEG)
 * finds which free list a block should belong to
 * returns the index of the appropriate free list
 */
int list_find(size_t size)
{
  int seg;
  size_t limit;

  /* find which list it fits into */
  for (seg = 1, limit = 2; seg < MAX_SEG; seg++, limit *= 2)
    if (size <= limit)
      return seg;

  /* too big, put in special list */
  return 0;
}

/*
 * list_add
 * O(list_find())
 * adds a free block to the free list
 * only call with a free block!
 */
void list_add(void *bp)
{
  int seg;

  seg = list_find(UNPACK_SIZE(HEADER(bp)));

  if (last[seg] == NULL)
  {
    /* empty list, initialise */
    first[seg] = last[seg] = bp;
    PREV_FREE(bp) = NEXT_FREE(bp) = NULL;
  }
  else
  {
    /* append to existing list */
    NEXT_FREE(last[seg]) = bp;
    PREV_FREE(bp) = last[seg];
    NEXT_FREE(bp) = NULL;
    last[seg] = bp;
  }
}

/*
 * list_remove
 * O(list_find())
 * removes a free block from the free list
 * only call with a free block!
 */
void list_remove(void *bp)
{
  void *prev, *next;
  int seg;

  prev = PREV_FREE(bp);
  next = NEXT_FREE(bp);
  seg = list_find(UNPACK_SIZE(HEADER(bp)));

  /* adjust previous block or first */
  if (prev != NULL)
    NEXT_FREE(prev) = next;
  else
    first[seg] = next;

  /* adjust next block or last */
  if (next != NULL)
    PREV_FREE(next) = prev;
  else
    last[seg] = prev;
}

/*
 * coalesce
 * O(list_find())
 * merges free blocks adjacent to a block
 * only call with a free block which isn't in a free list!
 * returns the possibly different address of the coalesced block
 */
void *coalesce(void *bp)
{
  size_t newsize;

  /* coalesce left */
  if (UNPACK_STATE(PREV_FOOTER(bp)) == FREE)
  {
    bp = PREV_BLOCK(bp);
    list_remove(bp);
    newsize = UNPACK_SIZE(HEADER(bp)) + UNPACK_SIZE(NEXT_HEADER(bp));
    REPACK_SIZE(HEADER(bp), newsize);
    REPACK_SIZE(FOOTER(bp), newsize);
  }

  /* coalesce right */
  if (UNPACK_STATE(NEXT_HEADER(bp)) == FREE)
  {
    list_remove(NEXT_BLOCK(bp));
    newsize = UNPACK_SIZE(HEADER(bp)) + UNPACK_SIZE(NEXT_HEADER(bp));
    REPACK_SIZE(HEADER(bp), newsize);
    REPACK_SIZE(FOOTER(bp), newsize);
  }

  list_add(bp);
  return bp;
}

/*
 * split
 * O(list_find())
 * splits an existing block so that the first is of the specified size
 * only call with an allocated block!
 */
void split(void *bp, size_t size)
{
  size_t oldsize;
  
  oldsize = UNPACK_SIZE(HEADER(bp));

  /* not enough to split off */
  if (oldsize < size + OVERHEAD)
    return;

  /* resize blocks */
  VALUE(HEADER(bp)) = PACK(size, ALLOCATED);
  VALUE(FOOTER(bp)) = PACK(size, ALLOCATED);
  VALUE(NEXT_HEADER(bp)) = PACK(oldsize - size, FREE);
  VALUE(FOOTER(NEXT_BLOCK(bp))) = PACK(oldsize - size, FREE);

  /* coalesce leftover */
  coalesce(NEXT_BLOCK(bp));
}

/*
 * find_block
 * O(n(free)/MAX_SEG)
 * progressive "first fit" search which approximates "best fit"
 * returns a pointer to the first free block found with sufficient size
 */
void *find_block(size_t size)
{
  char *bp;
  int seg;

  seg = list_find(size);

  /* search through lists */
  if (seg > 0)
    for (; seg < MAX_SEG; seg++)
      for (bp = first[seg]; bp != NULL; bp = NEXT_FREE(bp))
        if (UNPACK_SIZE(HEADER(bp)) >= size)
          return bp;

  /* couldn't find, try special list for large blocks */
  for (bp = first[0]; bp != NULL; bp = NEXT_FREE(bp))
    if (UNPACK_SIZE(HEADER(bp)) >= size)
      return bp;

  /* none found */
  return NULL;
}

/*
 * new_block
 * O(list_find())
 * extends the heap to create a new free block
 * returns a pointer to the newly created free block
 */
void *new_block(size_t size)
{
  char *bp;

  /* extend heap to accomodate new block */
  bp = mem_sbrk(size);
  if (bp == (char *)-1)
    return NULL;

  /* take over space of old terminal block */
  bp += OVERHEAD - 2 * WORD;
  VALUE(HEADER(bp)) = PACK(size, FREE);
  VALUE(FOOTER(bp)) = PACK(size, FREE);

  /* recreate terminal block */
  VALUE(NEXT_HEADER(bp)) = PACK(0, ALLOCATED);

  /* merge with trailing free block if possible */
  bp = coalesce(bp);

  /* new block is ready */
  return bp;
}

/* 
 * mm_init
 * O(list_find())
 * sets up free lists and terminal blocks
 * always returns 0
 */
int mm_init(void)
{
  char *p;
  int seg;

  /* allocate initial fake edge blocks */
  p = mem_sbrk(OVERHEAD + 2 * WORD);
  p += OVERHEAD;
  VALUE(HEADER(p)) = PACK(OVERHEAD, ALLOCATED);
  VALUE(FOOTER(p)) = PACK(OVERHEAD, ALLOCATED);
  p = NEXT_BLOCK(p);
  VALUE(HEADER(p)) = PACK(0, ALLOCATED);

  /* set up explicit lists */
  for (seg = 0; seg < MAX_SEG; seg++)
  {
    first[seg] = NULL;
    last[seg] = NULL;
  }

  return 0;
}

/* 
 * mm_malloc
 * O(n(free))
 * allocates a block of space to hold the given size
 * returns a pointer to the allocated block, or NULL
 */
void *mm_malloc(size_t size)
{
  void *bp;

  /* ignore empty case */
  if (size == 0)
    return NULL;

  /* adjust to actual block size, including header/footer and padding */
  size = ALIGN(size + OVERHEAD);

  /* find a block big enough to use */
  bp = find_block(size);
  if (bp == NULL)
  {
    bp = new_block(size);
    if (bp == NULL)
      return NULL;
  }

  /* mark as allocated */
  list_remove(bp);
  REPACK_STATE(HEADER(bp), ALLOCATED);
  REPACK_STATE(FOOTER(bp), ALLOCATED);
  split(bp, size);

  /* block is ready for user */
  return bp;
}

/*
 * mm_free
 * O(list_find())
 * signals a block is no longer needed and can be reused
 */
void mm_free(void *bp)
{
  /* set block as free */
  REPACK_STATE(HEADER(bp), FREE);
  REPACK_STATE(FOOTER(bp), FREE);

  /* merge with adjacent free blocks */
  coalesce(bp);
}

/*
 * mm_realloc
 * O(find_block())
 * resize an existing block, moving if necessary
 * returns a pointer to the resized block, possibly different
 */
void *mm_realloc(void *bp, size_t size)
{
  void *bp2;
  size_t newsize, cosize, oldsize;

  /* special cases */
  if (bp == NULL)
    return mm_malloc(size);
  if (size == 0)
  {
    mm_free(bp);
    return NULL;
  }

  /* adjust to actual block size, including header/footer and padding */
  newsize = ALIGN(size + OVERHEAD);
  oldsize = UNPACK_SIZE(HEADER(bp));

  if (newsize + OVERHEAD < oldsize)
  {
    /* shrink by splitting if possible */
    split(bp, size);
    return bp;
  }
  if (newsize < oldsize)
    /* only slightly smaller, can't shrink, so do nothing */
    return bp;

  cosize = oldsize + UNPACK_SIZE(NEXT_HEADER(bp));
  if (UNPACK_STATE(NEXT_HEADER(bp)) == FREE && cosize >= newsize)
  {
    /* grow in place by absorbing next free block and then splitting */
    list_remove(NEXT_BLOCK(bp));
    VALUE(HEADER(bp)) = PACK(cosize, ALLOCATED);
    VALUE(FOOTER(bp)) = PACK(cosize, ALLOCATED);
    split(bp, newsize);
    return bp;
  }
  cosize = oldsize + UNPACK_SIZE(PREV_FOOTER(bp));
  if (UNPACK_STATE(PREV_FOOTER(bp)) == FREE && cosize >= newsize)
  {
    /* absorb previous block */
    bp2 = PREV_BLOCK(bp);
    list_remove(bp2);
    VALUE(HEADER(bp2)) = PACK(cosize, ALLOCATED);
    VALUE(FOOTER(bp2)) = PACK(cosize, ALLOCATED);
    /* move data backwards */
    memmove(bp2, bp, oldsize - OVERHEAD);
    /* split */
    split(bp2, newsize);
    return bp2;
  }

  /* no easy way out, allocate another block, copy data over */
  bp2 = mm_malloc(size);
  if (bp2 != NULL)
  {
    memcpy(bp2, bp, oldsize - OVERHEAD);
    mm_free(bp);
  }
  return bp2;
}

