//=== softboundcets.h - headers for functions introduced by SoftBound+CETS--*- C
//-*===//
// Copyright (c) 2014 Santosh Nagarakatte, Milo M. K. Martin. All rights
// reserved.

// Developed by: Santosh Nagarakatte, Milo M.K. Martin,
//               Jianzhou Zhao, Steve Zdancewic
//               Department of Computer and Information Sciences,
//               University of Pennsylvania
//               http://www.cis.upenn.edu/acg/softbound/

// Permission is hereby granted, free of charge, to any person obtaining a copy
// of this software and associated documentation files (the "Software"), to
// deal with the Software without restriction, including without limitation the
// rights to use, copy, modify, merge, publish, distribute, sublicense, and/or
// sell copies of the Software, and to permit persons to whom the Software is
// furnished to do so, subject to the following conditions:

//   1. Redistributions of source code must retain the above copyright notice,
//      this list of conditions and the following disclaimers.

//   2. Redistributions in binary form must reproduce the above copyright
//      notice, this list of conditions and the following disclaimers in the
//      documentation and/or other materials provided with the distribution.

//   3. Neither the names of Santosh Nagarakatte, Milo M. K. Martin,
//      Jianzhou Zhao, Steve Zdancewic, University of Pennsylvania, nor
//      the names of its contributors may be used to endorse or promote
//      products derived from this Software without specific prior
//      written permission.

// THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
// IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
// FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT.  IN NO EVENT SHALL THE
// CONTRIBUTORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
// LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
// FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS
// WITH THE SOFTWARE.
//===---------------------------------------------------------------------===//

#ifndef __SOFTBOUNDCETS_H__
#define __SOFTBOUNDCETS_H__

#include <assert.h>
#include <fcntl.h>
#include <limits.h>
#include <stddef.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/mman.h>
#include <sys/stat.h>
#include <unistd.h>

#if __SOFTBOUNDCETS_SPATIAL + __SOFTBOUNDCETS_TEMPORAL +                       \
        __SOFTBOUNDCETS_SPATIAL_TEMPORAL !=                                    \
    1
#error Require one and only one of: __SOFTBOUNDCETS_SPATIAL + __SOFTBOUNDCETS_TEMPORAL + __SOFTBOUNDCETS_SPATIAL_TEMPORAL
#endif

/* Trie represented by the following by a structure with four fields
 * if both __SOFTBOUNDCETS_SPATIAL and __SOFTBOUNDCETS_TEMPORAL are
 * specified. It has key and lock with size_t
 */

typedef void *sbcets_base_t;
typedef void *sbcets_bound_t;
typedef size_t sbcets_key_t;
typedef size_t *sbcets_lock_t;

typedef struct {

#if __SOFTBOUNDCETS_SPATIAL
  void *base;
  void *bound;

#define __SOFTBOUNDCETS_METADATA_NUM_FIELDS 2
#define __BASE_INDEX 0
#define __BOUND_INDEX 1
#define __KEY_INDEX 10000000
#define __LOCK_INDEX 10000000

#elif __SOFTBOUNDCETS_TEMPORAL
  size_t key;
  size_t *lock;
#define __SOFTBOUNDCETS_METADATA_NUM_FIELDS 2
#define __KEY_INDEX 0
#define __LOCK_INDEX 1
#define __BASE_INDEX 10000000
#define __BOUND_INDEX 10000000

#elif __SOFTBOUNDCETS_SPATIAL_TEMPORAL

  void *base;
  void *bound;
  size_t key;
  size_t *lock;
#define __SOFTBOUNDCETS_METADATA_NUM_FIELDS 4

#define __BASE_INDEX 0
#define __BOUND_INDEX 1
#define __KEY_INDEX 2
#define __LOCK_INDEX 3

#endif

} __softboundcets_metadata_t;

#if defined(__APPLE__)
#define SOFTBOUNDCETS_MMAP_FLAGS (MAP_ANON | MAP_NORESERVE | MAP_PRIVATE)
#else
#define SOFTBOUNDCETS_MMAP_FLAGS (MAP_PRIVATE | MAP_ANONYMOUS | MAP_NORESERVE)
#endif

// Logging levels
#define LOG_LEVEL_DEBUG 1
#define LOG_LEVEL_INFO 2
#define LOG_LEVEL_WARN 3
#define LOG_LEVEL_ERROR 4
#define LOG_LEVEL_NOTHING 5

#if __SOFTBOUNDCETS_BENCHMARKING

#ifndef LOG_LEVEL
#define LOG_LEVEL LOG_LEVEL_NOTHING
#endif

#define __SOFTBOUNDCETS_CONTINUE_ON_ABORT 1

#elif __SOFTBOUNDCETS_TEST_BENCHMARKING

#ifndef LOG_LEVEL
#define LOG_LEVEL LOG_LEVEL_ERROR
#endif

#define __SOFTBOUNDCETS_CONTINUE_ON_ABORT 1

#endif

#ifndef LOG_LEVEL
#define LOG_LEVEL LOG_LEVEL_ERROR
#endif

#ifndef __SOFTBOUNDCETS_PREALLOCATE_TRIE
#define __SOFTBOUNDCETS_PREALLOCATE_TRIE 1
#endif

#ifndef __SOFTBOUNDCETS_CHECK_LOADS
#define __SOFTBOUNDCETS_CHECK_LOADS 1
#endif

#define UNLIKELY(x) __builtin_expect(!!(x), 0)

#if __SOFTBOUNDCETS_PREVENT_SEGFAULTS_ON_INVALID_LOCKS
#define IS_INVALID_LOCK(x) UNLIKELY((x) < 0x10000 || (x) > 0x8fff00000000)
#else
#define IS_INVALID_LOCK(x) (0)
#endif

#define __SOFTBOUNDCETS_FREE_MAP 0

// check if __WORDSIZE works with clang on both Linux and MacOSX
/* Allocating one million entries for the temporal key */
#if __WORDSIZE == 32
static const size_t __SOFTBOUNDCETS_N_TEMPORAL_ENTRIES =
    ((size_t)4 * (size_t)1024 * (size_t)1024);
static const size_t __SOFTBOUNDCETS_LOWER_ZERO_POINTER_BITS = 2;
static const size_t __SOFTBOUNDCETS_N_STACK_TEMPORAL_ENTRIES =
    ((size_t)1024 * (size_t)64);
static const size_t __SOFTBOUNDCETS_N_GLOBAL_LOCK_SIZE =
    ((size_t)1024 * (size_t)32);
// 2^23 entries each will be 8 bytes each
static const size_t __SOFTBOUNDCETS_TRIE_PRIMARY_TABLE_ENTRIES =
    ((size_t)8 * (size_t)1024 * (size_t)1024);
static const size_t __SOFTBOUNDCETS_SHADOW_STACK_ENTRIES =
    ((size_t)128 * (size_t)32);
/* 256 Million simultaneous objects */
static const size_t __SOFTBOUNDCETS_N_FREE_MAP_ENTRIES =
    ((size_t)32 * (size_t)1024 * (size_t)1024);
// each secondary entry has 2^ 22 entries
static const size_t __SOFTBOUNDCETS_TRIE_SECONDARY_TABLE_ENTRIES =
    ((size_t)4 * (size_t)1024 * (size_t)1024);

#else

static const size_t __SOFTBOUNDCETS_N_TEMPORAL_ENTRIES =
    ((size_t)64 * (size_t)1024 * (size_t)1024);
static const size_t __SOFTBOUNDCETS_LOWER_ZERO_POINTER_BITS = 3;

static const size_t __SOFTBOUNDCETS_N_STACK_TEMPORAL_ENTRIES =
    ((size_t)1024 * (size_t)64);
static const size_t __SOFTBOUNDCETS_N_GLOBAL_LOCK_SIZE =
    ((size_t)1024 * (size_t)32);

// 2^23 entries each will be 8 bytes each
static const size_t __SOFTBOUNDCETS_TRIE_PRIMARY_TABLE_ENTRIES =
    ((size_t)8 * (size_t)1024 * (size_t)1024);

static const size_t __SOFTBOUNDCETS_SHADOW_STACK_ENTRIES =
    ((size_t)128 * (size_t)32);

/* 256 Million simultaneous objects */
static const size_t __SOFTBOUNDCETS_N_FREE_MAP_ENTRIES =
    ((size_t)32 * (size_t)1024 * (size_t)1024);
// each secondary entry has 2^ 22 entries
static const size_t __SOFTBOUNDCETS_TRIE_SECONDARY_TABLE_ENTRIES =
    ((size_t)4 * (size_t)1024 * (size_t)1024);

#endif

#define __WEAK__ __attribute__((__weak__))

#if __SOFTBOUNDCETS_DYNAMIC_RT
#define __RT_VISIBILITY extern "C" __attribute__((__visibility__("default")))
#else
#define __RT_VISIBILITY                                                        \
  extern "C" __attribute__((__weak__, always_inline,                           \
                            __visibility__("default"), retain, used))
#endif

__WEAK__ extern __softboundcets_metadata_t **__softboundcets_trie_primary_table;

__WEAK__ extern size_t *__softboundcets_shadow_stack_ptr;
__WEAK__ extern size_t *__softboundcets_temporal_space_begin;

__WEAK__ extern size_t *__softboundcets_stack_temporal_space_begin;
__WEAK__ extern size_t *__softboundcets_free_map_table;

__attribute__((__weak__))
#if !__SOFTBOUNDCETS_CONTINUE_ON_ABORT
__attribute__((__noreturn__))
#endif
extern void
__softboundcets_abort(void);

__WEAK__ extern void __softboundcets_printf(const char *str, ...);
__WEAK__ extern void __softboundcets_debug_printf(const char *str, ...);
__WEAK__ extern void __softboundcets_error_printf(const char *str, ...);

__attribute__((always_inline,__weak__)) void
__softboundcets_log_message(int level, const char *str, ...);

extern size_t *__softboundcets_global_lock;

__RT_VISIBILITY void
__softboundcets_allocation_secondary_trie_allocate(void *addr_of_ptr);
__RT_VISIBILITY void __softboundcets_add_to_free_map(size_t ptr_key, void *ptr);

static __softboundcets_metadata_t dummy_invalid_metadata = {0, 0, 0, 0};

static int softboundcets_initialized = 0;

__RT_VISIBILITY void __softboundcets_init(void);

__RT_VISIBILITY void softboundcets_init_ctype(void);

__RT_VISIBILITY int __softboundcets_wrap_main(int argc, char *argv[],
                                              char *envp[]);

/******************************************************************************/

/* Layout of the shadow stack

  1) size of the previous stack frame
  2) size of the current stack frame
  3) base/bound/key/lock of each argument

  Allocation: read the current stack frames size, increment the
  shadow_stack_ptr by current_size + 2, store the previous size into
  the new prev value, calcuate the allocation size and store in the
  new current stack size field; Deallocation: read the previous size,
  and decrement the shadow_stack_ptr */

__RT_VISIBILITY void
__softboundcets_allocate_shadow_stack_space(size_t num_pointer_args);

__RT_VISIBILITY __softboundcets_metadata_t *
__softboundcets_shadow_stack_metadata_ptr(size_t arg_no);

__RT_VISIBILITY void *__softboundcets_load_base_shadow_stack(size_t arg_no);

__RT_VISIBILITY void *__softboundcets_load_bound_shadow_stack(size_t arg_no);

__RT_VISIBILITY size_t __softboundcets_load_key_shadow_stack(size_t arg_no);

__RT_VISIBILITY size_t *__softboundcets_load_lock_shadow_stack(size_t arg_no);

__RT_VISIBILITY void __softboundcets_store_base_shadow_stack(void *base,
                                                             size_t arg_no);

__RT_VISIBILITY void __softboundcets_store_bound_shadow_stack(void *bound,
                                                              size_t arg_no);

__RT_VISIBILITY void __softboundcets_store_key_shadow_stack(size_t key,
                                                            size_t arg_no);

__RT_VISIBILITY void __softboundcets_store_lock_shadow_stack(size_t *lock,
                                                             size_t arg_no);

__RT_VISIBILITY void __softboundcets_store_metadata_shadow_stack(
#if __SOFTBOUNDCETS_SPATIAL || __SOFTBOUNDCETS_SPATIAL_TEMPORAL
    void *base, void *bound,
#endif
#if __SOFTBOUNDCETS_TEMPORAL || __SOFTBOUNDCETS_SPATIAL_TEMPORAL
    size_t key, size_t *lock,
#endif
    size_t arg_no);

__RT_VISIBILITY void __softboundcets_deallocate_shadow_stack_space(void);

__RT_VISIBILITY __softboundcets_metadata_t *__softboundcets_trie_allocate(void);

#if 0

//These are primary used to test and introspect  metadata during testing

__RT_VISIBILITY void __softboundcets_print_metadata(void* base, void* bound, void* ptr, size_t key, size_t* lock){
  
  printf("[print metadata] ptr = %p, base=%p, bound=%p, key = %zd, lock = %p, *lock = %zd\n", ptr, base, bound, key, lock, *lock);

}

__RT_VISIBILITY void __softboundcets_intermediate(char cmp1, char cmp2, char cmp3, size_t loaded_lock){

  printf("cmp = %d, cmp2 =%d cmp=%d, loaded_lock=%zd\n", cmp1, cmp2, cmp3, loaded_lock);

}

#endif

__RT_VISIBILITY void __softboundcets_dummy(void);
__RT_VISIBILITY void __softboundcets_introspect_metadata(void *ptr, void *base,
                                                         void *bound,
                                                         int arg_no);

__RT_VISIBILITY
void __softboundcets_copy_metadata(void *dest, void *from, size_t size);

__RT_VISIBILITY void
__softboundcets_shrink_bounds(void *new_base, void *new_bound, void *old_base,
                              void *old_bound, void **base_alloca,
                              void **bound_alloca);

__RT_VISIBILITY void __softboundcets_spatial_call_dereference_check(void *base,
                                                                    void *bound,
                                                                    void *ptr);

extern void *malloc_address;
__RT_VISIBILITY void
__softboundcets_spatial_load_dereference_check(void *base, void *bound,
                                               void *ptr, size_t size_of_type);

__RT_VISIBILITY void
__softboundcets_spatial_store_dereference_check(void *base, void *bound,
                                                void *ptr, size_t size_of_type);

/* Memcopy check, different variants based on spatial, temporal and
   spatial+temporal modes
*/

__RT_VISIBILITY void __softboundcets_memcopy_check(
    void *dest, void *src, size_t size

#if __SOFTBOUNDCETS_SPATIAL || __SOFTBOUNDCETS_SPATIAL_TEMPORAL
    ,
    void *dest_base, void *dest_bound, void *src_base, void *src_bound
#endif

#if __SOFTBOUNDCETS_TEMPORAL || __SOFTBOUNDCETS_SPATIAL_TEMPORAL
    ,
    size_t dest_key, void *dest_lock, size_t src_key, void *src_lock
#endif
);
/* Memset check, different variants based on spatial, temporal and
   spatial+temporal modes */

__RT_VISIBILITY void __softboundcets_memset_check(void *dest, size_t size
#if __SOFTBOUNDCETS_SPATIAL || __SOFTBOUNDCETS_SPATIAL_TEMPORAL
                                                  ,
                                                  sbcets_base_t dest_base,
                                                  sbcets_bound_t dest_bound
#endif
#if __SOFTBOUNDCETS_TEMPORAL || __SOFTBOUNDCETS_SPATIAL_TEMPORAL
                                                  ,
                                                  sbcets_key_t dest_key,
                                                  sbcets_lock_t dest_lock
#endif
);

/* Metadata store parameterized by the mode of checking */

#if __SOFTBOUNDCETS_SPATIAL

__RT_VISIBILITY void __softboundcets_metadata_store(void *addr_of_ptr,
                                                    void *base, void *bound);

#elif __SOFTBOUNDCETS_TEMPORAL

__RT_VISIBILITY void __softboundcets_metadata_store(void *addr_of_ptr,
                                                    size_t key, size_t *lock);

#elif __SOFTBOUNDCETS_SPATIAL_TEMPORAL

__RT_VISIBILITY void __softboundcets_metadata_store(void *addr_of_ptr,
                                                    void *base, void *bound,
                                                    size_t key, size_t *lock);

#endif

__RT_VISIBILITY __softboundcets_metadata_t *
__softboundcets_shadowspace_metadata_ptr(void *addr_of_ptr);

__RT_VISIBILITY __softboundcets_metadata_t *
__softboundcets_shadowspace_metadata_ptr_create_secondary_tries(
    void *addr_of_ptr);

__RT_VISIBILITY __softboundcets_metadata_t *
__softboundcets_shadowspace_vector_metadata_ptr(void *addr_of_ptr, int index);

__RT_VISIBILITY __softboundcets_metadata_t *
__softboundcets_shadowspace_masked_vector_metadata_ptr(void *addr_of_ptr,
                                                       int index, bool mask);

#if __SOFTBOUNDCETS_SPATIAL_TEMPORAL || __SOFTBOUNDCETS_SPATIAL
__RT_VISIBILITY sbcets_base_t __softboundcets_metadata_load_base(void *address);

__RT_VISIBILITY sbcets_bound_t
__softboundcets_metadata_load_bound(void *address);

__RT_VISIBILITY sbcets_base_t
__softboundcets_metadata_load_vector_base(void *ptr, int index);
__RT_VISIBILITY sbcets_bound_t
__softboundcets_metadata_load_vector_bound(void *ptr, int index);

__RT_VISIBILITY sbcets_base_t __softboundcets_metadata_masked_load_vector_base(
    void *ptr, int index, bool mask);
__RT_VISIBILITY sbcets_bound_t
__softboundcets_metadata_masked_load_vector_bound(void *ptr, int index,
                                                  bool mask);

#endif

#if __SOFTBOUNDCETS_SPATIAL_TEMPORAL || __SOFTBOUNDCETS_TEMPORAL
__RT_VISIBILITY sbcets_key_t __softboundcets_metadata_load_key(void *address);

__RT_VISIBILITY sbcets_lock_t __softboundcets_metadata_load_lock(void *address);

__RT_VISIBILITY sbcets_lock_t
__softboundcets_metadata_load_vector_lock(void *ptr, int index);
__RT_VISIBILITY sbcets_key_t
__softboundcets_metadata_load_vector_key(void *ptr, int index);

__RT_VISIBILITY sbcets_lock_t __softboundcets_metadata_masked_load_vector_lock(
    void *ptr, int index, bool mask);
__RT_VISIBILITY sbcets_key_t __softboundcets_metadata_masked_load_vector_key(
    void *ptr, int index, bool mask);

#endif

/******************************************************************************/

extern __WEAK__ size_t __softboundcets_key_id_counter;
extern __WEAK__ size_t *__softboundcets_lock_next_location;
extern __WEAK__ size_t *__softboundcets_lock_new_location;

__RT_VISIBILITY void
__softboundcets_temporal_load_dereference_check(size_t *pointer_lock,
                                                size_t key);

__RT_VISIBILITY void
__softboundcets_temporal_store_dereference_check(size_t *pointer_lock,
                                                 size_t key);

__RT_VISIBILITY void __softboundcets_stack_memory_deallocation(size_t ptr_key);

__RT_VISIBILITY void __softboundcets_memory_deallocation(size_t *ptr_lock,
                                                         size_t ptr_key);

__RT_VISIBILITY void *__softboundcets_allocate_lock_location(void);

__RT_VISIBILITY void
__softboundcets_allocation_secondary_trie_allocate_range(void *initial_ptr,
                                                         size_t size);

__RT_VISIBILITY void
__softboundcets_allocation_secondary_trie_allocate(void *addr_of_ptr);

__RT_VISIBILITY void __softboundcets_stack_memory_allocation(size_t **ptr_lock,
                                                             size_t *ptr_key);

__RT_VISIBILITY void __softboundcets_memory_allocation(void *ptr,
                                                       size_t **ptr_lock,
                                                       size_t *ptr_key);

__RT_VISIBILITY sbcets_lock_t __softboundcets_get_global_lock(void);

__RT_VISIBILITY void __softboundcets_add_to_free_map(size_t ptr_key, void *ptr);

__RT_VISIBILITY void __softboundcets_check_remove_from_free_map(size_t ptr_key,
                                                                void *ptr);

__RT_VISIBILITY void __softboundcets_metadata_store_vector(void *addr_of_ptr,
#if __SOFTBOUNDCETS_SPATIAL
                                                           void *base,
                                                           void *bound,
#elif __SOFTBOUNDCETS_TEMPORAL
                                                           size_t key,
                                                           size_t *lock,
#elif __SOFTBOUNDCETS_SPATIAL_TEMPORAL
                                                           void *base,
                                                           void *bound,
                                                           size_t key,
                                                           size_t *lock,
#endif
                                                           int index);

#endif
