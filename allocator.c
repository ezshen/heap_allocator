/*
 * File: allocator.c
 * Author: Taresh Sethi, Ethan Shen
 * ----------------------
 * Implementation: 
 * Explicit Free List
 * Double Linked List
 * Headers + Footers w/ Coalescing
 */

#include <stdlib.h>
#include <string.h>
#include "allocator.h"
#include <stdio.h>
#include "segment.h"

#define ALLOC 1
#define FREE 0
#define ALIGNMENT 8 // Heap blocks are required to be aligned to 8-byte boundary
#define INIT_PAGE_NUM 3 // Initial optimal number of pages 
#define INIT_PAGE_PADDING 4
#define HEADER_SIZE 4 // Size of the header without the two pointers.
#define NUM_OF_BUCKETS 1
#define MIN_BLOCKSZ 24

#pragma pack(1)

// Struct for headers, compatible for both
// allocated blocks and free blocks
typedef struct {     
    unsigned int packed_blocksz; 
    void *nextptr;
    void *prevptr;
} headerT;

// Struct for footers
typedef struct {
    unsigned int packed_blocksz;
} footerT;

/* Private global variables */ 

// Tracks the end of memory in the current
// segment
headerT *curr_seg_ptr;
headerT *free_list;

/* Very efficient bitwise round of sz up to nearest multiple of mult
 * does this by adding mult-1 to sz, then masking off the
 * the bottom bits to compute least multiple of mult that is
 * greater/equal than sz, this value is returned
 * NOTE: mult has to be power of 2 for the bitwise trick to work!
 */
static inline size_t roundup(size_t sz, size_t mult)
{
    return (sz + mult-1) & ~(mult-1);
}

/* Given a size and allocated/free value, return header */
static inline unsigned int calc_packed_blocksz(unsigned int size, unsigned int alloc)
{
    return (size) | (alloc);
}

/* Given a pointer to start of header, return size of payload */
static inline unsigned int get_blocksz(void *header) 
{
    return (((headerT*)header)->packed_blocksz) & ~0x7; 
}

/* Given a pointer to start of header, return if it is allocated */
static inline unsigned int get_alloc(void *header) 
{
    return (((headerT*)header)->packed_blocksz) & 0x1; 
}


/* Given a pointer to start of payload, simply back up to access its block header */
static inline headerT *hdr_for_payload(void *payload)
{
    return (headerT *)((char *)payload - HEADER_SIZE);
}

/* Given a pointer to block header, advance past header to access start of payload */
static inline void *payload_for_hdr(headerT *header)
{
    return (char *)header + HEADER_SIZE;
}

/* Given a pointer to block header, return a pointer to its footer */
static inline footerT *ftr_for_hdr(headerT *header) 
{
    return (footerT*)((char*)header + get_blocksz(header) - sizeof(footerT));
}

/* Given a pointer to current block header, return a pointer to its next pointer */
static inline headerT *next_blockptr(headerT *header) {
    return (headerT*)((char*)(header) + get_blocksz(header));
}
/* Given a pointer to current block header, return a pointer to its previous pointer */
static inline headerT *prev_blockptr(headerT *header)
{
    footerT *prev_footer = (footerT*)((char*)header - HEADER_SIZE);
    return (headerT*)((char*)header - get_blocksz(prev_footer));
}


 /*
 * Configures a new empty heap, initializing the heap segment
 * to INIT_PAGE_NUM. It then adds appropriate housekeeiping,
 * including prologue and epilogue structures that will allow
 * for coalescing in the future. Initializes free list, or 
 * resets anytime the function is called again.
 */
bool myinit() 
{
    // reset heap segment to initial pages allocated, return false
    // if failed
    if (init_heap_segment(INIT_PAGE_NUM) == NULL) return false;

    // add prologue for coalescing
    footerT *prologueh = (footerT*)((char*)heap_segment_start() + INIT_PAGE_PADDING);
    prologueh->packed_blocksz = calc_packed_blocksz(ALIGNMENT, ALLOC);
    footerT *prologuef = (footerT*)((char*)prologueh + HEADER_SIZE);
    prologuef->packed_blocksz = prologueh->packed_blocksz;

    // initialize ptr to segment, accomodating for alignment padding
    curr_seg_ptr = (headerT*)((char*)(prologuef) + INIT_PAGE_PADDING);

    // initialize epilogue for coalescing
    footerT *epilogue = (footerT*)curr_seg_ptr;
    epilogue->packed_blocksz = calc_packed_blocksz(HEADER_SIZE, ALLOC);
    
    // initialize/reset the free list
    free_list = NULL;
    return true;
}

 /*
 * Extends the heap if necessary and then returns the global
 * pointer to the end of the current segment or NULL if the
 * extension of the heap fails
 */
static headerT *extend_memory(unsigned int blocksz) {
    // calculate the end of the current segment, 
    // taking into account the epilogue
    char* heap_segment_end = (char*)heap_segment_start() + heap_segment_size() - HEADER_SIZE;
    // extend heap if there is not enough space to fit
    // the block at the end of the current memory
    if (blocksz > (heap_segment_end - (char*)curr_seg_ptr)) {
        if (extend_heap_segment(blocksz/PAGE_SIZE + 1) == NULL) return NULL;
    }
    // return the pointer to the end
    // of memory of the current segment
    return (headerT*)curr_seg_ptr;
}

 /*
 * Adds the newly freed block to the beginning of the
 * free list, linking the appropriate pointers to promote
 * a LIFO structure
 */
static void link_freed_block(headerT *header){
    if (free_list == NULL) { // free list is empty
        free_list = header;
        header->nextptr = NULL;
        header->prevptr = NULL;
    } else { // free list is not empty 
        header->prevptr = NULL;
        header->nextptr = free_list;
        ((headerT*)(header->nextptr))->prevptr = header;
        free_list = header;
    }
}

 /*
 * Splits the free block if there is enough memory after
 * the requested size to make atleast a minimum sized free block.
 * It takes in the header of the block, its requested size, and a 
 * pointer to the difference amongst the requested block size and
 * the actual block size, updating the difference. If it split, it 
 * inserts the newly freed block into the free list
 */
static void split_block(headerT* header, unsigned int req_blocksz, 
        unsigned int *difference) {
    unsigned int blocksz = get_blocksz(header);
    // sets value of the pointer to the difference between
    // the actual current block size and the requested block
    // size
    *difference = blocksz - req_blocksz;

    // split
    if (*difference >= MIN_BLOCKSZ) {
        // create new header and footer for newly split block
        headerT *split_header = (headerT*)((char*)header + req_blocksz);
        split_header->packed_blocksz = calc_packed_blocksz(blocksz - req_blocksz, FREE); 
        ftr_for_hdr(split_header)->packed_blocksz = split_header->packed_blocksz;

        // insert newly freed block into free list
        link_freed_block(split_header);
    }
}

 /*
 * Removes a block from the free list, relinks associated pointers
 */
static void remove_from_list(headerT *header){
    if (header->prevptr == NULL && header->nextptr == NULL) { // block is only one in free list
        free_list = NULL;
    } else if (header->prevptr == NULL) { // block is at the beginning of free list
        free_list = header->nextptr;
        ((headerT*)(header->nextptr))->prevptr = NULL;
        header->nextptr = NULL;
    } else if (header->nextptr == NULL) { // block is at end of free list
        ((headerT*)(header->prevptr))->nextptr = NULL;
        header->prevptr = NULL; 
    } else { // block is at middle of free list
        ((headerT*)(header->prevptr))->nextptr = header->nextptr; 
        ((headerT*)(header->nextptr))->prevptr = header->prevptr;
        header->nextptr = NULL;
        header->prevptr = NULL;
    }
}

 /*
 * Iterates through the free list, finding the first fit given a block
 * size. Once it finds a fit, it checks to see if it can be splitted
 * and calls split_block if so. Then, it updates the value of the pointer
 * to the difference amongst the actual block and the requested size to
 * relay how much difference was left, and then returns the header of
 * the final found block. If a fit is not found in the free list, returns
 * the pointer to the end of memory of the current segment.
 */
static headerT *find_fit(unsigned int req_blocksz, unsigned int *difference) {
    if (free_list != NULL) {
        // loop through free list until land at correct size
        headerT *header = free_list;
        while (req_blocksz > get_blocksz(header) && header->nextptr != NULL) {
            header = header->nextptr;
        }      
        // return the end of the heap if there are no fitting free blocks
        if (req_blocksz > get_blocksz(header)) return extend_memory(req_blocksz);        
        // split header, link newly freed block into free list
        split_block(header, req_blocksz, difference);
        // remove original header from list
        remove_from_list(header);
        return header;
    }
    // no fit in free list
    return extend_memory(req_blocksz);
}
 
 /*
 * Given a size, allocates a block of memory of that size into heap
 * by first checking the free list to see if any freed blocks could
 * accomodate that size, and then adding the memory to the end of
 * the heap if a fit was not found in the free list. If added to
 * the end of memory, shifts global pointer to the end of the heap
 * along with the epilogue structure for coalescing. If necessary, a
 * helper extends the heap segment. Returns a pointer to the payload 
 * of the final allocated block
 */
void *mymalloc(size_t size) 
{
    unsigned int req_blocksz;
    unsigned int full_blocksz; 
    // calculates extra memory to ensure footers 
    // are correctly placed, size of header and footers
    // are correct
    unsigned int difference = 0;
    
    // unacceptable request
    if (size == 0) return NULL; 
    
    // Calculate the necessary blocksz
    if (size <= sizeof(void*) * 2) req_blocksz = MIN_BLOCKSZ;
    else req_blocksz = roundup(size + 2 * HEADER_SIZE, ALIGNMENT);

    // Search the free list for a fit, 
    headerT *header = find_fit(req_blocksz, &difference); 
    if (header == NULL) return NULL;
    
    // increase global pointer and set new epilogue if returned 
    // header is at end of heap
    if (header == (headerT*)curr_seg_ptr) {
        curr_seg_ptr = (headerT*)((char*)curr_seg_ptr + req_blocksz);
        footerT *epilogue = (footerT*)curr_seg_ptr;
        epilogue->packed_blocksz = calc_packed_blocksz(HEADER_SIZE, ALLOC);
    } 
    
    // set the header, footer size to the full block size
    // of the free block found if block was not split, requested
    // block size if block was split
    full_blocksz = req_blocksz + difference;
    if (difference < MIN_BLOCKSZ) {
        header->packed_blocksz = calc_packed_blocksz(full_blocksz, ALLOC);
    } else {
        header->packed_blocksz = calc_packed_blocksz(req_blocksz, ALLOC);
    }
    // set correct footer
    ftr_for_hdr(header)->packed_blocksz = header->packed_blocksz;
    return payload_for_hdr(header);
}
 
 /*
 * Create a larger free block if the immediate previous and/or next
 * pointers are free. Checks 4 specific conditions and relinks free
 * list in each, then calls remove_from_list to remove anything in the
 * coalesced block that is in the free list. Returns the header to the 
 * coalesced block.
 */
static headerT *coalesce(headerT *header)
{
    // get size and alloc of next block
    headerT *next_block = next_blockptr(header);
    unsigned int next_alloc = get_alloc(next_block);
    
    // get size and alloc of previous block
    headerT *prev_block = prev_blockptr(header);
    unsigned int prev_alloc = get_alloc(prev_block);

    unsigned int blocksz = get_blocksz(header);
    footerT *footer = ftr_for_hdr(header);
    
    // Both prev and next are allocated 
    if (prev_alloc && next_alloc) {
        header->packed_blocksz = blocksz;
        footer->packed_blocksz = blocksz;
        return header;
    }
    // Prev is allocated, next is free
    else if (prev_alloc && !next_alloc) {
        blocksz += get_blocksz(next_block);
        footer = (footerT*)((char*)header + blocksz - HEADER_SIZE);
        remove_from_list(next_block);
    }
    // Prev is free, next is alloc
    else if (!prev_alloc && next_alloc) {
        header = prev_block;
        blocksz += get_blocksz(prev_block);
        footer = (footerT*)((char*)header + blocksz - HEADER_SIZE);
        remove_from_list(prev_block);
    }
    // Both prev and next are free
    else {
        header = prev_block;
        blocksz = blocksz + get_blocksz(prev_block) + get_blocksz(next_block);
        footer = (footerT*)((char*)header + blocksz - HEADER_SIZE);
        remove_from_list(next_block);
        remove_from_list(prev_block);
    }
    // blocksz is free due to bit operations
    header->packed_blocksz = blocksz;
    footer->packed_blocksz = blocksz;
    return header;
}

 /*
 * check to see if the block can be coalesced, theninsert the block 
 * corresponding to the pointer provided into the free list
 */
void myfree(void *ptr)
{
    if (ptr == NULL) return;
    headerT *header = coalesce(hdr_for_payload(ptr));
    // relink new_header to free list
    link_freed_block(header);
}

 /*
 * changes size of memory block associated with given pointer to new
 * size if the old size is less than the new size. Does so by mallocing
 * double the new size since realloc is likely to be called again, and then
 * memcopying all of the data from the previous block into new block.
 * Returns the pointer to the new place where the memory block is stored,
 * corresponding to the payload
 */
void *myrealloc(void *oldptr, size_t newsz)
{
    // special cases
    if (oldptr == NULL) return malloc(newsz);
    if (newsz == 0) {
        myfree(oldptr);
        return NULL;
    }
    
    // find associated header and payload size
    headerT *header = hdr_for_payload(oldptr); 
    unsigned int payloadsz_old = get_blocksz(header) - 2 * HEADER_SIZE;
    
    // return the old pointer if there is enough
    // memory in the current place
    if (payloadsz_old >= newsz) return oldptr;

    // realloc is likely to be called again, so
    // malloc twice the new size
    void *newptr = mymalloc(2*newsz);
    memcpy(newptr, oldptr, payloadsz_old);
    myfree(oldptr);
    return newptr;
}

bool validate_heap()
{   
    // start from beginning of heap and loop through block by block
    headerT *curr_blockptr = (headerT*)((char*)heap_segment_start() + INIT_PAGE_PADDING); 
    int heap_free_blocks = 0;
    
    while (curr_blockptr < (headerT*)curr_seg_ptr) {
        // if there is an unusually sized pointer
        if ((int)get_blocksz(curr_blockptr) < 0) {
            printf("Block in heap is weird!\n");
            printf("Block Pointer: %p, Allocated? %d, Size: %d\n", curr_blockptr, get_alloc(curr_blockptr), get_blocksz(curr_blockptr));
            return false;
        }
        
        // count number of free blocks in heap
        if (get_alloc(curr_blockptr) == FREE) heap_free_blocks++;
        curr_blockptr = next_blockptr(curr_blockptr);
    }

    // Loop through free list
    int list_free_blocks = 0;
    headerT* curr_freeptr = free_list;
    while (curr_freeptr != NULL) {
        // count number of free blocks
        list_free_blocks++;
        
        // check if there is an allocated block in the free list
        if (get_alloc(curr_freeptr) == ALLOC) {
            printf("Allocated block in free list!");
            printf("Freed List: %p, Allocated? %d, Size: %d\n", curr_freeptr, get_alloc(curr_freeptr), get_blocksz(curr_freeptr));
            printf("Nextptr: %p, Prevptr: %p\n", curr_freeptr->nextptr, curr_freeptr->prevptr);
            return false;
        }
        curr_freeptr = curr_freeptr->nextptr;
    }

    // check if there are the same amount of freed blocks in heap and free list
    if (heap_free_blocks != list_free_blocks) {
        printf("There are %d free blocks in heap and %d free blocks in the list.\n", heap_free_blocks, list_free_blocks);
        return false;
    }

    return true;
}

