#include <errno.h>
#include <pthread.h>
#include <stddef.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#include "myMalloc.h"
#include "printing.h"

#define MIN_INDEX_SIZE (3)
#define MIN_SIZE (32)

static inline size_t max(size_t a, size_t b) {
  return a > b ? a : b;
}

static inline size_t min(size_t a, size_t b) {
  return a > b ? b : a;
}

/* Due to the way assert() prints error messges we use out own assert function
 * for deteminism when testing assertions
 */
#ifdef TEST_ASSERT
  inline static void assert(int e) {
    if (!e) {
      const char * msg = "Assertion Failed!\n";
      write(2, msg, strlen(msg));
      exit(1);
    }
  }
#else
  #include <assert.h>
#endif

/*
 * Mutex to ensure thread safety for the freelist
 */
static pthread_mutex_t mutex;

/*
 * Array of sentinel nodes for the freelists
 */
header freelistSentinels[N_LISTS];

/*
 * Pointer to the second fencepost in the most recently allocated chunk from
 * the OS. Used for coalescing chunks
 */
header * lastFencePost;

/*
 * Pointer to maintian the base of the heap to allow printing based on the
 * distance from the base of the heap
 */ 
void * base;

/*
 * List of chunks allocated by  the OS for printing boundary tags
 */
header * osChunkList [MAX_OS_CHUNKS];
size_t numOsChunks = 0;

/*
 * direct the compiler to run the init function before running main
 * this allows initialization of required globals
 */
static void init (void) __attribute__ ((constructor));

// Helper functions for manipulating pointers to headers
static inline header * get_header_from_offset(void * ptr, ptrdiff_t off);
static inline header * get_left_header(header * h);
static inline header * ptr_to_header(void * p);

// Helper functions for allocating more memory from the OS
static inline void initialize_fencepost(header * fp, size_t object_left_size);
static inline void insert_os_chunk(header * hdr);
static inline void insert_fenceposts(void * raw_mem, size_t size);
static header * allocate_chunk(size_t size);

// Helper functions for freeing a block
static inline void deallocate_object(void * p);

// Helper functions for allocating a block
static inline header * allocate_object(size_t raw_size);

// Helper functions for verifying that the data structures are structurally 
// valid
static inline header * detect_cycles();
static inline header * verify_pointers();
static inline bool verify_freelist();
static inline header * verify_chunk(header * chunk);
static inline bool verify_tags();


// Helper function to get index in freelist

static inline int get_freelist_index(size_t size) {
  return min(size / sizeof(size_t) - MIN_INDEX_SIZE, N_LISTS - 1);
}

// Helper function to remove a block from its freelist

static inline void remove_from_freelist(header* block) {
  block->next->prev = block->prev;
  block->prev->next = block->next;
}

// Helper function to add block to free list

static inline void add_to_freelist(header * block) {
  int idx = min(get_object_size(block) / sizeof(size_t) - MIN_INDEX_SIZE, N_LISTS - 1);
  block->next = freelistSentinels[idx].next;
  block->prev = &freelistSentinels[idx];
  freelistSentinels[idx].next->prev = block;
  freelistSentinels[idx].next = block;

  // if the free list was empty
  if (freelistSentinels[idx].prev == &freelistSentinels[idx]) {
    freelistSentinels[idx].prev = block;
  }
} 

// Helper function to coalesce two blocks

static inline void coalesce_blocks(header* left, header* right) {
  header* right_block = get_header_from_offset(right, get_object_size(right));
  right_block->object_left_size = get_object_size(left) + get_object_size(right);
  set_object_size(left, get_object_size(left) + get_object_size(right));
  set_object_state(left, UNALLOCATED);
}

static void init();

static bool isMallocInitialized;

/**
 * @brief Helper function to retrieve a header pointer from a pointer and an 
 *        offset
 *
 * @param ptr base pointer
 * @param off number of bytes from base pointer where header is located
 *
 * @return a pointer to a header offset bytes from pointer
 */
static inline header * get_header_from_offset(void * ptr, ptrdiff_t off) {
	return (header *)((char *) ptr + off);
}

/**
 * @brief Helper function to get the header to the right of a given header
 *
 * @param h original header
 *
 * @return header to the right of h
 */
header * get_right_header(header * h) {
	return get_header_from_offset(h, get_object_size(h));
}

/**
 * @brief Helper function to get the header to the left of a given header
 *
 * @param h original header
 *
 * @return header to the right of h
 */
inline static header * get_left_header(header * h) {
  return get_header_from_offset(h, -h->object_left_size);
}

/**
 * @brief Fenceposts are marked as always allocated and may need to have
 * a left object size to ensure coalescing happens properly
 *
 * @param fp a pointer to the header being used as a fencepost
 * @param object_left_size the size of the object to the left of the fencepost
 */
inline static void initialize_fencepost(header * fp, size_t object_left_size) {
	set_object_state(fp,FENCEPOST);
	set_object_size(fp, ALLOC_HEADER_SIZE);
	fp->object_left_size = object_left_size;
}

/**
 * @brief Helper function to maintain list of chunks from the OS for debugging
 *
 * @param hdr the first fencepost in the chunk allocated by the OS
 */
inline static void insert_os_chunk(header * hdr) {
  if (numOsChunks < MAX_OS_CHUNKS) {
    osChunkList[numOsChunks++] = hdr;
  }
}

/**
 * @brief given a chunk of memory insert fenceposts at the left and 
 * right boundaries of the block to prevent coalescing outside of the
 * block
 *
 * @param raw_mem a void pointer to the memory chunk to initialize
 * @param size the size of the allocated chunk
 */
inline static void insert_fenceposts(void * raw_mem, size_t size) {
  // Convert to char * before performing operations
  char * mem = (char *) raw_mem;

  // Insert a fencepost at the left edge of the block
  header * leftFencePost = (header *) mem;
  initialize_fencepost(leftFencePost, ALLOC_HEADER_SIZE);

  // Insert a fencepost at the right edge of the block
  header * rightFencePost = get_header_from_offset(mem, size - ALLOC_HEADER_SIZE);
  initialize_fencepost(rightFencePost, size - 2 * ALLOC_HEADER_SIZE);
}

/**
 * @brief Allocate another chunk from the OS and prepare to insert it
 * into the free list
 *
 * @param size The size to allocate from the OS
 *
 * @return A pointer to the allocable block in the chunk (just after the 
 * first fencpost)
 */
static header * allocate_chunk(size_t size) {
  void * mem = sbrk(size);
  insert_fenceposts(mem, size);
  header * hdr = (header *) ((char *)mem + ALLOC_HEADER_SIZE);
  set_object_state(hdr, UNALLOCATED);
  set_object_size(hdr, size - 2 * ALLOC_HEADER_SIZE);
  hdr->object_left_size = ALLOC_HEADER_SIZE;
  return hdr;
}

/**
 * @brief Helper allocate an object given a raw request size from the user
 *
 * @param raw_size number of bytes the user needs
 *
 * @return A block satisfying the user's request
 */
static inline header * allocate_object(size_t raw_size) {
  // Calculate req size
  if (raw_size == 0) return NULL;
  size_t required_size = ((raw_size + 7) & ~0x7) + ALLOC_HEADER_SIZE;
  if (required_size < MIN_SIZE) required_size = MIN_SIZE;


  header * mem = NULL;

  // Searching for a free block
  int idx = min(required_size / sizeof(size_t) - MIN_INDEX_SIZE, N_LISTS - 1);
  int found = 1;
  if (idx == N_LISTS - 1) {
    header* temp = freelistSentinels[idx].next;
    while (get_object_size(temp) < required_size && temp != &freelistSentinels[idx]) temp = temp->next;
    if (get_object_size(temp) < required_size) found = 0;
  } else {
    while (idx < N_LISTS && freelistSentinels[idx].next == &freelistSentinels[idx]) {
      idx++;
    }
    if (idx == N_LISTS) found = 0;
  }
  


  header* my_block;
  if (!found) {
    // Allocating new chunks
    mem = allocate_chunk(ARENA_SIZE);
    if (numOsChunks >= 1 && get_right_header(lastFencePost) == get_left_header(mem)) {
      header* left_block = get_header_from_offset(lastFencePost, -lastFencePost->object_left_size);
      if (get_object_state(left_block) == UNALLOCATED) {
        // combine the two fenceposts and left_block
        remove_from_freelist(left_block);
        set_object_size(left_block, get_object_size(left_block) + 2 * ALLOC_HEADER_SIZE + get_object_size(mem));
        lastFencePost = get_right_header(mem);
        mem = left_block;
      } else {
        // combine the fenceposts
        set_object_state(lastFencePost, UNALLOCATED);
        set_object_size(lastFencePost, get_object_size(lastFencePost) + ALLOC_HEADER_SIZE + get_object_size(mem));
        mem = lastFencePost;
        lastFencePost = get_right_header(mem);
      }
    } else {
      insert_os_chunk(get_left_header(mem));
      lastFencePost = get_right_header(mem);
    }

    set_object_size(mem, get_object_size(mem) - required_size);
    set_object_state(mem, UNALLOCATED);
    my_block = get_header_from_offset(mem, get_object_size(mem));
    my_block->object_left_size = get_object_size(mem);
    set_object_size(my_block, required_size);
    add_to_freelist(mem);
  } else {
    // Found a free block
    if (idx == N_LISTS - 1) {
      header* temp = freelistSentinels[idx].next;
      while (get_object_size(temp) < required_size) temp = temp->next;
      mem = temp;
    } else {
      mem = freelistSentinels[idx].next;
    }
    size_t left = get_object_size(mem) - required_size;
    if (left >= 32) {
      set_object_size(mem, get_object_size(mem) - required_size);
      int idx_to_change = min(get_object_size(mem) / sizeof(size_t) - MIN_INDEX_SIZE, N_LISTS - 1);
      if (idx_to_change != idx) {
        mem->next->prev = mem->prev;
        mem->prev->next = mem->next;
        add_to_freelist(mem);
      }
      my_block = get_header_from_offset(mem, get_object_size(mem));
      my_block->object_left_size = get_object_size(mem);
      set_object_size(my_block, required_size);
    } else {
      my_block = mem;
      remove_from_freelist(mem);
    }
  }

  set_object_state(my_block, ALLOCATED);
  ((header *)((char *)my_block + get_object_size(my_block)))->object_left_size = get_object_size(my_block);
  return my_block;
}

/**
 * @brief Helper to get the header from a pointer allocated with malloc
 *
 * @param p pointer to the data region of the block
 *
 * @return A pointer to the header of the block
 */
static inline header * ptr_to_header(void * p) {
  return (header *)((char *) p - ALLOC_HEADER_SIZE); //sizeof(header));
}

/**
 * @brief Helper to manage deallocation of a pointer returned by the user
 *
 * @param p The pointer returned to the user by a call to malloc
 */
static inline void deallocate_object(void * p) {
  // TODO implement deallocation
  // p points to data
  // p's header is p - ALLOC_HEADER_SIZE

  header * block_to_free = ptr_to_header(p);
  if (get_object_state(block_to_free) == UNALLOCATED) {
    fprintf(stderr, "Double Free Detected\n");
    assert(false);
    exit(1);
  }
  set_object_state(block_to_free, UNALLOCATED);
  header* left_block = get_header_from_offset(block_to_free, -(block_to_free->object_left_size));
  header* right_block = get_header_from_offset(block_to_free, get_object_size(block_to_free));

  size_t left_size = get_object_size(left_block);
  size_t right_size = get_object_size(right_block);

  if (get_object_state(left_block) != UNALLOCATED && get_object_state(right_block) != UNALLOCATED) {
      add_to_freelist(block_to_free);
  } else {
    // need to coalesce
    if (get_object_state(right_block) == UNALLOCATED) {
      // Coalescing with right
      coalesce_blocks(block_to_free, right_block);
    }
    if (get_object_state(left_block) == UNALLOCATED) {
      // Coalesce with left
      coalesce_blocks(left_block, block_to_free);
    }

    if (get_object_state(left_block) == UNALLOCATED && get_object_state(right_block) == UNALLOCATED) {
      if (get_freelist_index(left_size) == N_LISTS - 1) {
        remove_from_freelist(right_block);
      } else if (get_freelist_index(right_size) == N_LISTS - 1) {
        remove_from_freelist(left_block);
        left_block->next = right_block->next;
        left_block->prev = right_block->prev;
        right_block->next->prev = left_block;
        right_block->prev->next = left_block;
      } else {
        remove_from_freelist(left_block);
        remove_from_freelist(right_block);
        add_to_freelist(left_block);
      }
    } else if (get_object_state(left_block) == UNALLOCATED) {
      if (get_freelist_index(left_size) != N_LISTS - 1) {
        remove_from_freelist(left_block);
        add_to_freelist(left_block);
      }
    } else {
      if (get_freelist_index(right_size) == N_LISTS - 1) {
        remove_from_freelist(right_block);
        right_block->next->prev = block_to_free;
        right_block->prev->next = block_to_free;
        block_to_free->next = right_block->next;
        block_to_free->prev = right_block->prev;
      } else {
        remove_from_freelist(right_block);
        add_to_freelist(block_to_free);
      }
    }

  }
}

/**
 * @brief Helper to detect cycles in the free list
 * https://en.wikipedia.org/wiki/Cycle_detection#Floyd's_Tortoise_and_Hare
 *
 * @return One of the nodes in the cycle or NULL if no cycle is present
 */
static inline header * detect_cycles() {
  for (int i = 0; i < N_LISTS; i++) {
    header * freelist = &freelistSentinels[i];
    for (header * slow = freelist->next, * fast = freelist->next->next; 
         fast != freelist; 
         slow = slow->next, fast = fast->next->next) {
      if (slow == fast) {
        return slow;
      }
    }
  }
  return NULL;
}

/**
 * @brief Helper to verify that there are no unlinked previous or next pointers
 *        in the free list
 *
 * @return A node whose previous and next pointers are incorrect or NULL if no
 *         such node exists
 */
static inline header * verify_pointers() {
  for (int i = 0; i < N_LISTS; i++) {
    header * freelist = &freelistSentinels[i];
    for (header * cur = freelist->next; cur != freelist; cur = cur->next) {
      if (cur->next->prev != cur || cur->prev->next != cur) {
        return cur;
      }
    }
  }
  return NULL;
}

/**
 * @brief Verify the structure of the free list is correct by checkin for 
 *        cycles and misdirected pointers
 *
 * @return true if the list is valid
 */
static inline bool verify_freelist() {
  header * cycle = detect_cycles();
  if (cycle != NULL) {
    fprintf(stderr, "Cycle Detected\n");
    return false;
  }

  header * invalid = verify_pointers();
  if (invalid != NULL) {
    fprintf(stderr, "Invalid pointers\n");
    print_object(invalid);
    return false;
  }

  return true;
}

/**
 * @brief Helper to verify that the sizes in a chunk from the OS are correct
 *        and that allocated node's canary values are correct
 *
 * @param chunk AREA_SIZE chunk allocated from the OS
 *
 * @return a pointer to an invalid header or NULL if all header's are valid
 */
static inline header * verify_chunk(header * chunk) {
	if (get_object_state(chunk) != FENCEPOST) {
		fprintf(stderr, "Invalid fencepost\n");
		print_object(chunk);
		return chunk;
	}
	
	for (; get_object_state(chunk) != FENCEPOST; chunk = get_right_header(chunk)) {
		if (get_object_size(chunk)  != get_right_header(chunk)->object_left_size) {
			fprintf(stderr, "Invalid sizes\n");
			print_object(chunk);
			return chunk;
		}
	}
	
	return NULL;
}

/**
 * @brief For each chunk allocated by the OS verify that the boundary tags
 *        are consistent
 *
 * @return true if the boundary tags are valid
 */
static inline bool verify_tags() {
  for (size_t i = 0; i < numOsChunks; i++) {
    header * invalid = verify_chunk(osChunkList[i]);
    if (invalid != NULL) {
      return invalid;
    }
  }

  return NULL;
}

/**
 * @brief Initialize mutex lock and prepare an initial chunk of memory for allocation
 */
static void init() {
  // Initialize mutex for thread safety
  pthread_mutex_init(&mutex, NULL);

#ifdef DEBUG
  // Manually set printf buffer so it won't call malloc when debugging the allocator
  setvbuf(stdout, NULL, _IONBF, 0);
#endif // DEBUG

  // Allocate the first chunk from the OS
  header * block = allocate_chunk(ARENA_SIZE);

  header * prevFencePost = get_header_from_offset(block, -ALLOC_HEADER_SIZE);
  insert_os_chunk(prevFencePost);

  lastFencePost = get_header_from_offset(block, get_object_size(block));

  // Set the base pointer to the beginning of the first fencepost in the first
  // chunk from the OS
  base = ((char *) block) - ALLOC_HEADER_SIZE; //sizeof(header);

  // Initialize freelist sentinels
  for (int i = 0; i < N_LISTS; i++) {
    header * freelist = &freelistSentinels[i];
    freelist->next = freelist;
    freelist->prev = freelist;
  }

  // Insert first chunk into the free list
  header * freelist = &freelistSentinels[N_LISTS - 1];
  freelist->next = block;
  freelist->prev = block;
  block->next = freelist;
  block->prev = freelist;
}

/* 
 * External interface
 */
void * my_malloc(size_t size) {
  pthread_mutex_lock(&mutex);
  header * hdr = NULL;
  void *to_return;
  if (size != 0) {
    hdr  = allocate_object(size);
    to_return = hdr->data;
  } else {
    to_return = NULL;
  }
  pthread_mutex_unlock(&mutex);
  return to_return;
}

void * my_calloc(size_t nmemb, size_t size) {
  return memset(my_malloc(size * nmemb), 0, size * nmemb);
}

void * my_realloc(void * ptr, size_t size) {
  void * mem = my_malloc(size);
  memcpy(mem, ptr, size);
  my_free(ptr);
  return mem; 
}

void my_free(void * p) {
  pthread_mutex_lock(&mutex);
  if (p) deallocate_object(p);
  pthread_mutex_unlock(&mutex);
}

bool verify() {
  return verify_freelist() && verify_tags();
}
