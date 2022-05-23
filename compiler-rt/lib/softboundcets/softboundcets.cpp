//=== softboundcets.c - Creates the main function for SoftBound+CETS Runtime
//--*- C -*===//
// Copyright (c) 2014 Santosh Nagarakatte, Milo M. K. Martin. All rights
// reserved.

// Developed by: Santosh Nagarakatte,
//               Department of Computer Science, Rutgers University
//               https://github.com/santoshn/softboundcets-34/
//               http://www.cs.rutgers.edu/~santosh.nagarakatte/
//
//               in collaboration with
//
//               Milo M.K. Martin, Jianzhou Zhao, Steve Zdancewic
//               Department of Computer and Information Sciences,
//               University of Pennsylvania

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

#include <assert.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#if defined(__linux__)
#include <malloc.h>
#endif
#include <ctype.h>
#include <stdarg.h>
#include <string.h>
#include <sys/mman.h>
#if !defined(__FreeBSD__)
#include <execinfo.h>
#endif
#include "softboundcets.h"

__softboundcets_metadata_t **__softboundcets_trie_primary_table;

size_t *__softboundcets_free_map_table = NULL;

size_t *__softboundcets_shadow_stack_ptr = NULL;

size_t *__softboundcets_lock_next_location = NULL;
size_t *__softboundcets_lock_new_location = NULL;
size_t __softboundcets_key_id_counter = 2;

/* key 0 means not used, 1 is for  globals*/
size_t __softboundcets_deref_check_count = 0;
size_t *__softboundcets_global_lock = 0;

size_t *__softboundcets_temporal_space_begin = 0;
size_t *__softboundcets_stack_temporal_space_begin = NULL;

void *malloc_address = NULL;

void softboundcets_init_ctype(void) {
#if defined(__linux__)

  unsigned short const **ct_b_loc = __ctype_b_loc();
  unsigned short *ct_b_loc_base = *(unsigned short **)ct_b_loc;

  int const **ct_toupper_loc = __ctype_toupper_loc();
  int *ct_toupper_loc_base = *(int **)ct_toupper_loc;

  int const **ct_tolower_loc = __ctype_tolower_loc();
  int *ct_tolower_loc_base = *(int **)ct_tolower_loc;

  // __softboundcets_allocation_secondary_trie_allocate(ct_b_loc_base);
  // __softboundcets_allocation_secondary_trie_allocate(ct_toupper_loc);

#if __SOFTBOUNDCETS_SPATIAL
  __softboundcets_metadata_store(ct_b_loc, (ct_b_loc_base - 128),
                                 (ct_b_loc_base + 256));
  __softboundcets_metadata_store(ct_toupper_loc, (ct_toupper_loc_base - 128),
                                 (ct_toupper_loc_base + 256));
  __softboundcets_metadata_store(ct_tolower_loc, (ct_tolower_loc_base - 128),
                                 (ct_tolower_loc_base + 256));
#elif __SOFTBOUNDCETS_TEMPORAL
  __softboundcets_metadata_store(ct_b_loc, 1, __softboundcets_global_lock);
  __softboundcets_metadata_store(ct_toupper_loc, 1,
                                 __softboundcets_global_lock);
  __softboundcets_metadata_store(ct_tolower_loc, 1,
                                 __softboundcets_global_lock);
#elif __SOFTBOUNDCETS_SPATIAL_TEMPORAL
  __softboundcets_metadata_store(ct_b_loc, (ct_b_loc_base - 128),
                                 (ct_b_loc_base + 256), 1,
                                 __softboundcets_global_lock);
  __softboundcets_metadata_store(ct_toupper_loc, (ct_toupper_loc_base - 128),
                                 (ct_toupper_loc_base + 256), 1,
                                 __softboundcets_global_lock);
  __softboundcets_metadata_store(ct_tolower_loc, (ct_tolower_loc_base - 128),
                                 (ct_tolower_loc_base + 256), 1,
                                 __softboundcets_global_lock);
#endif

#endif // End of __linux__
}

void __softboundcets_init(void) {
  if (softboundcets_initialized != 0) {
    return; // already initialized, do nothing
  }

  softboundcets_initialized = 1;

#if __WORDSIZE == 32
  exit(1);
#endif

  __softboundcets_log_message(LOG_LEVEL_INFO,
                              "Initializing softboundcets metadata space\n");

  static_assert(sizeof(__softboundcets_metadata_t) >= 16, "");

  /* Allocating the temporal shadow space */

  size_t temporal_table_length =
      (__SOFTBOUNDCETS_N_TEMPORAL_ENTRIES) * sizeof(void *);

  __softboundcets_lock_new_location =
      (size_t *)mmap(0, temporal_table_length, PROT_READ | PROT_WRITE,
                     SOFTBOUNDCETS_MMAP_FLAGS, -1, 0);

  assert(__softboundcets_lock_new_location != (void *)-1);
  __softboundcets_temporal_space_begin =
      (size_t *)__softboundcets_lock_new_location;

  size_t stack_temporal_table_length =
      (__SOFTBOUNDCETS_N_STACK_TEMPORAL_ENTRIES) * sizeof(void *);
  __softboundcets_stack_temporal_space_begin =
      (size_t *)mmap(0, stack_temporal_table_length, PROT_READ | PROT_WRITE,
                     SOFTBOUNDCETS_MMAP_FLAGS, -1, 0);
  assert(__softboundcets_stack_temporal_space_begin != (void *)-1);

  size_t global_lock_size =
      (__SOFTBOUNDCETS_N_GLOBAL_LOCK_SIZE) * sizeof(void *);
  __softboundcets_global_lock =
      (size_t *)mmap(0, global_lock_size, PROT_READ | PROT_WRITE,
                     SOFTBOUNDCETS_MMAP_FLAGS, -1, 0);
  assert(__softboundcets_global_lock != (void *)-1);
  //  __softboundcets_global_lock =  __softboundcets_lock_new_location++;
  *__softboundcets_global_lock = 1;

  size_t shadow_stack_size =
      __SOFTBOUNDCETS_SHADOW_STACK_ENTRIES * sizeof(size_t);
  __softboundcets_shadow_stack_ptr =
      (size_t *)mmap(0, shadow_stack_size, PROT_READ | PROT_WRITE,
                     SOFTBOUNDCETS_MMAP_FLAGS, -1, 0);
  assert(__softboundcets_shadow_stack_ptr != (void *)-1);

  *((size_t *)__softboundcets_shadow_stack_ptr) = 0; /* prev stack size */
  size_t *current_size_shadow_stack_ptr = __softboundcets_shadow_stack_ptr + 1;
  *(current_size_shadow_stack_ptr) = 0;

  if (__SOFTBOUNDCETS_FREE_MAP) {
    size_t length_free_map =
        (__SOFTBOUNDCETS_N_FREE_MAP_ENTRIES) * sizeof(size_t);
    __softboundcets_free_map_table =
        (size_t *)mmap(0, length_free_map, PROT_READ | PROT_WRITE,
                       SOFTBOUNDCETS_MMAP_FLAGS, -1, 0);
    assert(__softboundcets_free_map_table != (void *)-1);
  }

  size_t length_trie = (__SOFTBOUNDCETS_TRIE_PRIMARY_TABLE_ENTRIES) *
                       sizeof(__softboundcets_metadata_t *);

  __softboundcets_trie_primary_table = (__softboundcets_metadata_t **)mmap(
      0, length_trie, PROT_READ | PROT_WRITE, SOFTBOUNDCETS_MMAP_FLAGS, -1, 0);
  assert(__softboundcets_trie_primary_table != (void *)-1);

  int *temp = (int *)malloc(1);
  __softboundcets_allocation_secondary_trie_allocate_range(0, (size_t)temp);

  //  printf("before init_ctype\n");
  softboundcets_init_ctype();
}

void __softboundcets_printf(const char *str, ...) {
  va_list args;

  va_start(args, str);
  vfprintf(stderr, str, args);
  va_end(args);
}

void __softboundcets_log_message(int level, const char *str, ...) {
  va_list args;
  if (level >= LOG_LEVEL) {
    va_start(args, str);
    vfprintf(stderr, str, args);
    va_end(args);
  }
}

void __softboundcets_debug_printf(const char *str, ...) {
#if (LOG_LEVEL_DEBUG >= LOG_LEVEL)
  va_list args;

  va_start(args, str);
  vfprintf(stderr, str, args);
  va_end(args);
#endif
}

void __softboundcets_error_printf(const char *str, ...) {
#if (LOG_LEVEL_ERROR >= LOG_LEVEL)
  va_list args;

  va_start(args, str);
  vfprintf(stderr, str, args);
  va_end(args);
#endif
}

__attribute__((always_inline))
#if __SOFTBOUNDCETS_CONTINUE_ON_ABORT
void __softboundcets_abort(void) {
  volatile int dummy;
  dummy = 1;
}
#else
__attribute__((__noreturn__)) void
__softboundcets_abort(void) {
  fprintf(stderr,
          "\nSoftboundcets: Memory safety violation detected\n\nBacktrace:\n");

  // Based on code from the backtrace man page
  size_t size;
  void *array[100];

#if !defined(__FreeBSD__)
  size = backtrace(array, 100);
  backtrace_symbols_fd(array, size, fileno(stderr));
#endif

  fprintf(stderr, "\n\n");

  abort();
}
#endif

__attribute__((__weak__)) extern "C" int
__softboundcets_real_main(int argc, char *argv[], char *envp[]);

int __softboundcets_wrap_main(int argc, char *argv[], char *envp[]) {

  int *temp = (int *)malloc(1);
  malloc_address = temp;
  __softboundcets_allocation_secondary_trie_allocate_range(0, (size_t)temp);
  __softboundcets_allocation_secondary_trie_allocate_range(argv,
                                                           (size_t)argc * 8);

  // Create lock and key for argv.
  size_t argv_key;
  size_t *argv_lock;
  __softboundcets_stack_memory_allocation(&argv_lock, &argv_key);

#if defined(__linux__)
  mallopt(M_MMAP_MAX, 0);
#endif

  // ===========================================================================================
  // Create metadata for the environ pointer

  size_t environ_key;
  size_t *environ_lock;
  __softboundcets_stack_memory_allocation(&environ_lock, &environ_key);

  size_t environ_size = 0;

  // Create metadata for the environment environiables stored in environ.
  char **env1;
  for (env1 = environ; *env1; ++env1) {
    environ_size++;
#if __SOFTBOUNDCETS_SPATIAL
    __softboundcets_metadata_store(env1, *env1, *env1 + strlen(*env1) + 1);
#elif __SOFTBOUNDCETS_TEMPORAL
    __softboundcets_metadata_store(env1, environ_key, environ_lock);
#elif __SOFTBOUNDCETS_SPATIAL_TEMPORAL
    __softboundcets_metadata_store(env1, *env1, *env1 + strlen(*env1) + 1,
                                   environ_key, environ_lock);
#endif
  }
#if __SOFTBOUNDCETS_SPATIAL
  __softboundcets_metadata_store(&environ, environ, environ + environ_size + 1);
#elif __SOFTBOUNDCETS_TEMPORAL
  __softboundcets_metadata_store(&environ, environ_key, environ_lock);
#elif __SOFTBOUNDCETS_SPATIAL_TEMPORAL
  __softboundcets_metadata_store(&environ, environ, environ + environ_size + 1,
                                 environ_key, environ_lock);
#endif

  // ===========================================================================================
  // Create metadata for the arguments stored in argv.
  for (int i = 0; i < argc; ++i) {
#if __SOFTBOUNDCETS_SPATIAL
    __softboundcets_metadata_store(&argv[i], argv[i],
                                   argv[i] + strlen(argv[i]) + 1);
#elif __SOFTBOUNDCETS_TEMPORAL
    __softboundcets_metadata_store(&argv[i], argv_key, argv_lock);
#elif __SOFTBOUNDCETS_SPATIAL_TEMPORAL
    __softboundcets_metadata_store(
        &argv[i], argv[i], argv[i] + strlen(argv[i]) + 1, argv_key, argv_lock);
#endif
  }

  // ===========================================================================================
  // Create metadata for the environment variables stored in envp.
  size_t envp_key;
  size_t *envp_lock;
  __softboundcets_stack_memory_allocation(&envp_lock, &envp_key);

  char **env2;
  for (env2 = envp; *env2; ++env2) {
#if __SOFTBOUNDCETS_SPATIAL
    __softboundcets_metadata_store(env2, *env2, *env2 + strlen(*env2) + 1);
#elif __SOFTBOUNDCETS_TEMPORAL
    __softboundcets_metadata_store(env2, envp_key, envp_lock);
#elif __SOFTBOUNDCETS_SPATIAL_TEMPORAL
    __softboundcets_metadata_store(env2, *env2, *env2 + strlen(*env2) + 1,
                                   envp_key, envp_lock);
#endif
  }

  // =============================================================================================

  // Allocate shadow stack space for argv's and envp's metadata.
  __softboundcets_allocate_shadow_stack_space(2);

  // NULL pointer stored as argv's last element.
#if __SOFTBOUNDCETS_SPATIAL || __SOFTBOUNDCETS_SPATIAL_TEMPORAL
  char *argv_bound = (char *)(&argv[argc] + 1);
  __softboundcets_store_base_shadow_stack(&argv[0], 0);
  __softboundcets_store_bound_shadow_stack(argv_bound, 0);
#endif
#if __SOFTBOUNDCETS_TEMPORAL || __SOFTBOUNDCETS_SPATIAL_TEMPORAL
  __softboundcets_store_key_shadow_stack(argv_key, 0);
  __softboundcets_store_lock_shadow_stack(argv_lock, 0);
#endif

  // Store envp's metadata onto the shadow stack. We have to account for the
  // NULL pointer stored as envp's last element.
#if __SOFTBOUNDCETS_SPATIAL || __SOFTBOUNDCETS_SPATIAL_TEMPORAL
  char *envp_bound = (char *)(env2 + 1);
  __softboundcets_store_base_shadow_stack(envp, 1);
  __softboundcets_store_bound_shadow_stack(envp_bound, 1);
#endif
#if __SOFTBOUNDCETS_TEMPORAL || __SOFTBOUNDCETS_SPATIAL_TEMPORAL
  __softboundcets_store_key_shadow_stack(envp_key, 1);
  __softboundcets_store_lock_shadow_stack(envp_lock, 1);
#endif

  // ===========================================================================================
  // call main of instrumented program

  int return_value = __softboundcets_real_main(argc, argv, envp);

  // Deallocate shadow stack space.
  __softboundcets_deallocate_shadow_stack_space();

  // Delete argv's lock and key.
  __softboundcets_stack_memory_deallocation(argv_key);

  return return_value;
}

void __softboundcets_allocate_shadow_stack_space(size_t num_pointer_args) {

  size_t *prev_stack_size_ptr = __softboundcets_shadow_stack_ptr + 1;
  size_t prev_stack_size = *((size_t *)prev_stack_size_ptr);

  __softboundcets_shadow_stack_ptr =
      __softboundcets_shadow_stack_ptr + prev_stack_size + 2;

  *((size_t *)__softboundcets_shadow_stack_ptr) = prev_stack_size;
  size_t *current_stack_size_ptr = __softboundcets_shadow_stack_ptr + 1;

  ssize_t size = num_pointer_args * __SOFTBOUNDCETS_METADATA_NUM_FIELDS;
  *((size_t *)current_stack_size_ptr) = size;
}

__RT_VISIBILITY __softboundcets_metadata_t *
__softboundcets_shadow_stack_metadata_ptr(size_t arg_no) {
  assert(arg_no >= 0);
  size_t count = 2 + arg_no * __SOFTBOUNDCETS_METADATA_NUM_FIELDS;
  size_t *metadata_ptr = (__softboundcets_shadow_stack_ptr + count);
  return (__softboundcets_metadata_t *)metadata_ptr;
}

__RT_VISIBILITY void *__softboundcets_load_base_shadow_stack(size_t arg_no) {
  assert(arg_no >= 0);
  size_t count =
      2 + arg_no * __SOFTBOUNDCETS_METADATA_NUM_FIELDS + __BASE_INDEX;
  size_t *base_ptr = (__softboundcets_shadow_stack_ptr + count);
  void *base = *((void **)base_ptr);
  return base;
}

__RT_VISIBILITY void *__softboundcets_load_bound_shadow_stack(size_t arg_no) {

  assert(arg_no >= 0);
  size_t count =
      2 + arg_no * __SOFTBOUNDCETS_METADATA_NUM_FIELDS + __BOUND_INDEX;
  size_t *bound_ptr = (__softboundcets_shadow_stack_ptr + count);

  void *bound = *((void **)bound_ptr);
  return bound;
}

__RT_VISIBILITY size_t __softboundcets_load_key_shadow_stack(size_t arg_no) {

  assert(arg_no >= 0);
  size_t count = 2 + arg_no * __SOFTBOUNDCETS_METADATA_NUM_FIELDS + __KEY_INDEX;
  size_t *key_ptr = (__softboundcets_shadow_stack_ptr + count);
  size_t key = *key_ptr;
  return key;
}

__RT_VISIBILITY size_t *__softboundcets_load_lock_shadow_stack(size_t arg_no) {

  assert(arg_no >= 0);
  size_t count =
      2 + arg_no * __SOFTBOUNDCETS_METADATA_NUM_FIELDS + __LOCK_INDEX;
  size_t **lock_ptr = (size_t **)(__softboundcets_shadow_stack_ptr + count);
  return *lock_ptr;
}

__RT_VISIBILITY void __softboundcets_store_base_shadow_stack(void *base,
                                                             size_t arg_no) {

  assert(arg_no >= 0);
  size_t count =
      2 + arg_no * __SOFTBOUNDCETS_METADATA_NUM_FIELDS + __BASE_INDEX;
  void **base_ptr = (void **)(__softboundcets_shadow_stack_ptr + count);

  *(base_ptr) = base;
}

__RT_VISIBILITY void __softboundcets_store_bound_shadow_stack(void *bound,
                                                              size_t arg_no) {

  assert(arg_no >= 0);
  size_t count =
      2 + arg_no * __SOFTBOUNDCETS_METADATA_NUM_FIELDS + __BOUND_INDEX;
  void **bound_ptr = (void **)(__softboundcets_shadow_stack_ptr + count);

  *(bound_ptr) = bound;
}

__RT_VISIBILITY void __softboundcets_store_key_shadow_stack(size_t key,
                                                            size_t arg_no) {
  assert(arg_no >= 0);
  size_t count = 2 + arg_no * __SOFTBOUNDCETS_METADATA_NUM_FIELDS + __KEY_INDEX;
  size_t *key_ptr = (__softboundcets_shadow_stack_ptr + count);

  *(key_ptr) = key;
}

__RT_VISIBILITY void __softboundcets_store_lock_shadow_stack(size_t *lock,
                                                             size_t arg_no) {
  assert(arg_no >= 0);
  size_t count =
      2 + arg_no * __SOFTBOUNDCETS_METADATA_NUM_FIELDS + __LOCK_INDEX;
  size_t **lock_ptr = (size_t **)(__softboundcets_shadow_stack_ptr + count);

  *(lock_ptr) = lock;
}

__RT_VISIBILITY void __softboundcets_store_metadata_shadow_stack(
#if __SOFTBOUNDCETS_SPATIAL || __SOFTBOUNDCETS_SPATIAL_TEMPORAL
    void *base, void *bound,
#endif
#if __SOFTBOUNDCETS_TEMPORAL || __SOFTBOUNDCETS_SPATIAL_TEMPORAL
    size_t key, size_t *lock,
#endif
    size_t arg_no) {

  __softboundcets_metadata_t *metadata =
      __softboundcets_shadow_stack_metadata_ptr(arg_no);

#if __SOFTBOUNDCETS_SPATIAL || __SOFTBOUNDCETS_SPATIAL_TEMPORAL
  metadata->base = base;
  metadata->bound = bound;
#endif
#if __SOFTBOUNDCETS_TEMPORAL || __SOFTBOUNDCETS_SPATIAL_TEMPORAL
  metadata->key = key;
  metadata->lock = lock;
#endif
}

__RT_VISIBILITY void __softboundcets_deallocate_shadow_stack_space(void) {

  size_t *reserved_space_ptr = __softboundcets_shadow_stack_ptr;

  size_t read_value = *((size_t *)reserved_space_ptr);

  assert(
      (read_value >= 0 && read_value <= __SOFTBOUNDCETS_SHADOW_STACK_ENTRIES));

  __softboundcets_shadow_stack_ptr =
      __softboundcets_shadow_stack_ptr - read_value - 2;
}

__RT_VISIBILITY __softboundcets_metadata_t *
__softboundcets_trie_allocate(void) {

  __softboundcets_metadata_t *secondary_entry;
  size_t length = (__SOFTBOUNDCETS_TRIE_SECONDARY_TABLE_ENTRIES) *
                  sizeof(__softboundcets_metadata_t);
  secondary_entry = (__softboundcets_metadata_t *)mmap(
      0, length, PROT_READ | PROT_WRITE, SOFTBOUNDCETS_MMAP_FLAGS, -1, 0);
  // assert(secondary_entry != (void*)-1);
  // printf("snd trie table %p %lx\n", secondary_entry, length);
  return secondary_entry;
}

__RT_VISIBILITY void __softboundcets_dummy(void) { printf("calling abort"); }
__RT_VISIBILITY void __softboundcets_introspect_metadata(void *ptr, void *base,
                                                         void *bound,
                                                         int arg_no) {

  printf("[introspect_metadata]ptr=%p, base=%p, bound=%p, arg_no=%d\n", ptr,
         base, bound, arg_no);
}

__RT_VISIBILITY
void __softboundcets_copy_metadata(void *dest, void *from, size_t size) {

  //  printf("dest=%p, from=%p, size=%zx\n", dest, from, size);

  size_t dest_ptr = (size_t)dest;
  size_t dest_ptr_end = dest_ptr + size;

  size_t from_ptr = (size_t)from;
  size_t from_ptr_end = from_ptr + size;

  if (from_ptr % 8 != 0) {
    // printf("dest=%p, from=%p, size=%zx\n", dest, from, size);
    return;
    //    from_ptr = from_ptr %8;
    //    dest_ptr = dest_ptr %8;
  }

  //  printf("dest=%p, from=%p, size=%zx\n", dest, from, size);
  __softboundcets_metadata_t *trie_secondary_table_dest_begin;
  __softboundcets_metadata_t *trie_secondary_table_from_begin;

  size_t dest_primary_index_begin = (dest_ptr >> 25);
  size_t dest_primary_index_end = (dest_ptr_end >> 25);

  size_t from_primary_index_begin = (from_ptr >> 25);
  size_t from_primary_index_end = (from_ptr_end >> 25);

  if ((from_primary_index_begin != from_primary_index_end) ||
      (dest_primary_index_begin != dest_primary_index_end)) {

    size_t from_sizet = from_ptr;
    size_t dest_sizet = dest_ptr;

    size_t trie_size = size;
    size_t index = 0;

    for (index = 0; index < trie_size; index = index + 8) {

      size_t temp_from_pindex = (from_sizet + index) >> 25;
      size_t temp_to_pindex = (dest_sizet + index) >> 25;

      size_t dest_secondary_index = (((dest_sizet + index) >> 3) & 0x3fffff);
      size_t from_secondary_index = (((from_sizet + index) >> 3) & 0x3fffff);

      __softboundcets_metadata_t *temp_from_strie =
          __softboundcets_trie_primary_table[temp_from_pindex];

      if (temp_from_strie == NULL) {
        temp_from_strie = __softboundcets_trie_allocate();
        __softboundcets_trie_primary_table[temp_from_pindex] = temp_from_strie;
      }
      __softboundcets_metadata_t *temp_to_strie =
          __softboundcets_trie_primary_table[temp_to_pindex];

      if (temp_to_strie == NULL) {
        temp_to_strie = __softboundcets_trie_allocate();
        __softboundcets_trie_primary_table[temp_to_pindex] = temp_to_strie;
      }

      void *dest_entry_ptr = &temp_to_strie[dest_secondary_index];
      void *from_entry_ptr = &temp_from_strie[from_secondary_index];

#if __SOFTBOUNDCETS_SPATIAL
      memcpy(dest_entry_ptr, from_entry_ptr, 16);
#elif __SOFTBOUNDCETS_TEMPORAL
      memcpy(dest_entry_ptr, from_entry_ptr, 16);
#elif __SOFTBOUNDCETS_SPATIAL_TEMPORAL
      memcpy(dest_entry_ptr, from_entry_ptr, 32);
#endif
    }
    return;
  }

  trie_secondary_table_dest_begin =
      __softboundcets_trie_primary_table[dest_primary_index_begin];
  trie_secondary_table_from_begin =
      __softboundcets_trie_primary_table[from_primary_index_begin];

  if (trie_secondary_table_from_begin == NULL)
    return;

  if (trie_secondary_table_dest_begin == NULL) {
    trie_secondary_table_dest_begin = __softboundcets_trie_allocate();
    __softboundcets_trie_primary_table[dest_primary_index_begin] =
        trie_secondary_table_dest_begin;
  }

  size_t dest_secondary_index = ((dest_ptr >> 3) & 0x3fffff);
  size_t from_secondary_index = ((from_ptr >> 3) & 0x3fffff);

  assert(dest_secondary_index < __SOFTBOUNDCETS_TRIE_SECONDARY_TABLE_ENTRIES);
  assert(from_secondary_index < __SOFTBOUNDCETS_TRIE_SECONDARY_TABLE_ENTRIES);

  void *dest_entry_ptr = &trie_secondary_table_dest_begin[dest_secondary_index];
  void *from_entry_ptr = &trie_secondary_table_from_begin[from_secondary_index];

#if __SOFTBOUNDCETS_SPATIAL

  memcpy(dest_entry_ptr, from_entry_ptr, 16 * (size >> 3));
#elif __SOFTBOUNDCETS_TEMPORAL

  memcpy(dest_entry_ptr, from_entry_ptr, 16 * (size >> 3));
#elif __SOFTBOUNDCETS_SPATIAL_TEMPORAL

  memcpy(dest_entry_ptr, from_entry_ptr, 32 * (size >> 3));
#endif
  return;
}

__RT_VISIBILITY void
__softboundcets_shrink_bounds(void *new_base, void *new_bound, void *old_base,
                              void *old_bound, void **base_alloca,
                              void **bound_alloca) {

  *(base_alloca) = new_base < old_base ? old_base : new_base;
  *(bound_alloca) = new_bound > old_bound ? old_bound : new_bound;
}

__RT_VISIBILITY void __softboundcets_spatial_call_dereference_check(void *base,
                                                                    void *bound,
                                                                    void *ptr) {

#ifndef __NOSIM_CHECKS
  if ((base != bound) && (ptr != base)) {
    __softboundcets_error_printf(
        "In Call Dereference Check, base=%p, bound=%p, ptr=%p\n", base, bound,
        ptr);
    __softboundcets_abort();
  }
#endif
}

__RT_VISIBILITY void
__softboundcets_spatial_load_dereference_check(void *base, void *bound,
                                               void *ptr, size_t size_of_type) {

  __softboundcets_log_message(LOG_LEVEL_INFO,
                              "[spatial_load_deref_check] base=%p, "
                              "bound=%p, ptr=%p, size_of_type=%zx\n",
                              base, bound, ptr, size_of_type);
  if ((ptr < base) || ((void *)((char *)ptr + size_of_type) > bound)) {

    __softboundcets_error_printf(
        "[spatial_load_deref_check] base=%zx, bound=%zx, ptr=%zx\n", base,
        bound, ptr);
    __softboundcets_abort();
  }
}

__RT_VISIBILITY void __softboundcets_spatial_store_dereference_check(
    void *base, void *bound, void *ptr, size_t size_of_type) {

  __softboundcets_log_message(LOG_LEVEL_INFO,
                              "[spatial_store_deref_check] base=%p, bound=%p, "
                              "ptr=%p, size_of_type=%zx\n",
                              base, bound, ptr, size_of_type);
  if ((ptr < base) || ((void *)((char *)ptr + size_of_type) > bound)) {
    __softboundcets_error_printf(
        "[spatial_store_deref_check] base=%p, bound=%p, "
        "ptr=%p, size_of_type=%zx, ptr+size=%p\n",
        base, bound, ptr, size_of_type, (char *)ptr + size_of_type);

    __softboundcets_abort();
  }
}

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
) {

  if (size >= LONG_MAX)
    __softboundcets_abort();

#if __SOFTBOUNDCETS_SPATIAL || __SOFTBOUNDCETS_SPATIAL_TEMPORAL
  if (dest < dest_base || (char *)dest > ((char *)dest_bound - size) ||
      (size > (size_t)dest_bound))
    __softboundcets_abort();

  if (src < src_base || (char *)src > ((char *)src_bound - size) ||
      (size > (size_t)dest_bound))
    __softboundcets_abort();
#endif

#if __SOFTBOUNDCETS_TEMPORAL || __SOFTBOUNDCETS_SPATIAL_TEMPORAL
  if (IS_INVALID_LOCK((size_t)dest_lock)) {
    __softboundcets_error_printf("[memcpy] Invalid dest temporal lock: %p\n",
                                 dest_lock);
    __softboundcets_abort();
    return;
  }

  if (IS_INVALID_LOCK((size_t)src_lock)) {
    __softboundcets_error_printf("[memcpy] Invalid src temporal lock: %p\n",
                                 src_lock);
    __softboundcets_abort();
    return;
  }

  if (dest_key != *((size_t *)(dest_lock))) {
    __softboundcets_abort();
  }

  if (src_key != *((size_t *)(src_lock))) {
    __softboundcets_abort();
  }
#endif
}
/* #elif __SOFTBOUNDCETS_TEMPORAL */

/* __RT_VISIBILITY void __softboundcets_memcopy_check(void *dest, void *src, */
/*                                                  size_t size, size_t
 * dest_key, */
/*                                                  void *dest_lock, */
/*                                                  size_t src_key, */
/*                                                  void *src_lock) { */

/*   if (size >= LONG_MAX) */
/*     __softboundcets_abort(); */

/*   if (dest_key != *((size_t *)(dest_lock))) { */
/*     __softboundcets_abort(); */
/*   } */

/*   if (src_key != *((size_t *)(src_lock))) { */
/*     __softboundcets_abort(); */
/*   } */
/* } */

/* #elif __SOFTBOUNDCETS_SPATIAL_TEMPORAL */

/* __RT_VISIBILITY void */
/* __softboundcets_memcopy_check(void *dest, void *src, size_t size, */
/*                               void *dest_base, void *dest_bound, void
 * *src_base, */
/*                               void *src_bound, size_t dest_key, void
 * *dest_lock, */
/*                               size_t src_key, void *src_lock) { */

/* #ifndef __NOSIM_CHECKS */

/*   /\* printf("dest=%zx, src=%zx, size=%zx, ulong_max=%zx\n",  *\/ */
/*   /\*        dest, src, size, ULONG_MAX); *\/ */
/*   if (size >= LONG_MAX) */
/*     __softboundcets_abort(); */

/*   if (dest < dest_base || (char *)dest > ((char *)dest_bound - size) || */
/*       (size > (size_t)dest_bound)) */
/*     __softboundcets_abort(); */

/*   if (src < src_base || (char *)src > ((char *)src_bound - size) || */
/*       (size > (size_t)dest_bound)) */
/*     __softboundcets_abort(); */

/*   if (dest_key != *((size_t *)(dest_lock))) { */
/*     __softboundcets_abort(); */
/*   } */

/*   if (src_key != *((size_t *)(src_lock))) { */
/*     __softboundcets_abort(); */
/*   } */

/* #endif */
/* } */
/* #else */

/* __RT_VISIBILITY void */
/* __softboundcets_memcopy_check(void *dest, void *src, size_t size, */
/*                               void *dest_base, void *dest_bound, void
 * *src_base, */
/*                               void *src_bound, size_t dest_key, void
 * *dest_lock, */
/*                               size_t src_key, void *src_lock) { */

/*   printf("not handled\n"); */
/*   __softboundcets_abort(); */
/* } */
/* #endif */

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
) {

  if (size >= LONG_MAX)
    __softboundcets_abort();

#if __SOFTBOUNDCETS_SPATIAL || __SOFTBOUNDCETS_SPATIAL_TEMPORAL
  if (dest < dest_base || (char *)dest > ((char *)dest_bound - size) ||
      (size > (size_t)dest_bound))
    __softboundcets_abort();

#endif
#if __SOFTBOUNDCETS_TEMPORAL || __SOFTBOUNDCETS_SPATIAL_TEMPORAL
  if (IS_INVALID_LOCK((size_t)dest_lock)) {
    __softboundcets_error_printf("[memset] Invalid dest temporal lock: %p\n",
                                 dest_lock);
    __softboundcets_abort();
    return;
  }

  if (dest_key != *((size_t *)(dest_lock))) {
    __softboundcets_abort();
  }
#endif
}
/* #elif __SOFTBOUNDCETS_TEMPORAL */

/* __RT_VISIBILITY void __softboundcets_memset_check(void *dest, size_t size, */
/*                                                 size_t dest_key, */
/*                                                 void *dest_lock) { */

/*   if (size >= LONG_MAX) */
/*     __softboundcets_abort(); */

/*   if (dest_key != *((size_t *)(dest_lock))) { */
/*     __softboundcets_abort(); */
/*   } */
/* } */

/* #elif __SOFTBOUNDCETS_SPATIAL_TEMPORAL */

/* __RT_VISIBILITY void __softboundcets_memset_check(void *dest, size_t size, */
/*                                                 void *dest_base, */
/*                                                 void *dest_bound, */
/*                                                 size_t dest_key, */
/*                                                 void *dest_lock) { */

/* #ifndef __NOSIM_CHECKS */

/*   if (size >= LONG_MAX) */
/*     __softboundcets_abort(); */

/*   if (dest < dest_base || (char *)dest > ((char *)dest_bound - size) || */
/*       (size > (size_t)dest_bound)) */
/*     __softboundcets_abort(); */

/*   if (dest_key != *((size_t *)(dest_lock))) { */
/*     __softboundcets_abort(); */
/*   } */

/* #endif */
/* } */
/* #else */

/* __RT_VISIBILITY void __softboundcets_memset_check(void *dest, size_t size, */
/*                                                 void *dest_base, */
/*                                                 void *dest_bound, */
/*                                                 size_t dest_key, */
/*                                                 void *dest_lock) { */

/*   printf("not handled\n"); */
/*   __softboundcets_abort(); */
/* } */
/* #endif */

/* Metadata store parameterized by the mode of checking */

#if __SOFTBOUNDCETS_SPATIAL

__RT_VISIBILITY void __softboundcets_metadata_store(void *addr_of_ptr,
                                                    void *base, void *bound) {

#elif __SOFTBOUNDCETS_TEMPORAL

__RT_VISIBILITY void __softboundcets_metadata_store(void *addr_of_ptr,
                                                    size_t key, size_t *lock) {

#elif __SOFTBOUNDCETS_SPATIAL_TEMPORAL

__RT_VISIBILITY void __softboundcets_metadata_store(void *addr_of_ptr,
                                                    void *base, void *bound,
                                                    size_t key, size_t *lock) {
#endif

#if __SOFTBOUNDCETS_SPATIAL || __SOFTBOUNDCETS_SPATIAL_TEMPORAL
  __softboundcets_log_message(
      LOG_LEVEL_DEBUG,
      "[metadata_store] addr_of_ptr = %p, ptr = %p, base=%p, bound = %p\n",
      addr_of_ptr, *(void **)addr_of_ptr, base, bound);
#endif
#if __SOFTBOUNDCETS_TEMPORAL || __SOFTBOUNDCETS_SPATIAL_TEMPORAL
  __softboundcets_log_message(
      LOG_LEVEL_DEBUG,
      "[metadata_store] addr_of_ptr = %p, ptr = %p, key=%zx, lock = %p\n",
      addr_of_ptr, *(void **)addr_of_ptr, key, lock);
#endif

  size_t ptr = (size_t)addr_of_ptr;
  size_t primary_index;
  __softboundcets_metadata_t *trie_secondary_table;

  primary_index = (ptr >> 25);
  trie_secondary_table = __softboundcets_trie_primary_table[primary_index];

  if (UNLIKELY(trie_secondary_table == NULL)) {
    trie_secondary_table = __softboundcets_trie_allocate();
    __softboundcets_trie_primary_table[primary_index] = trie_secondary_table;
  }
  assert(trie_secondary_table != NULL);

  size_t secondary_index = ((ptr >> 3) & 0x3fffff);
  __softboundcets_metadata_t *entry_ptr =
      &trie_secondary_table[secondary_index];

#if __SOFTBOUNDCETS_SPATIAL || __SOFTBOUNDCETS_SPATIAL_TEMPORAL

  entry_ptr->base = base;
  entry_ptr->bound = bound;

#endif
#if __SOFTBOUNDCETS_TEMPORAL || __SOFTBOUNDCETS_SPATIAL_TEMPORAL

  entry_ptr->key = key;
  entry_ptr->lock = lock;

#endif

  return;
}

__RT_VISIBILITY
void __softboundcets_log_pointer_metadata(
    void *address, __softboundcets_metadata_t *metadata) {
#if __SOFTBOUNDCETS_SPATIAL_TEMPORAL || __SOFTBOUNDCETS_SPATIAL
  __softboundcets_log_message(
      LOG_LEVEL_DEBUG,
      "[metadata_load_base/bound]  addr_of_ptr = %p, base = %p, bound = %p\n",
      address, metadata->base, metadata->bound);
#endif
#if __SOFTBOUNDCETS_TEMPORAL || __SOFTBOUNDCETS_SPATIAL_TEMPORAL
  __softboundcets_log_message(
      LOG_LEVEL_DEBUG,
      "[metadata_load_key/lock]  addr_of_ptr = %p, key = %p, lock = %p\n",
      address, metadata->key, metadata->lock);
#endif
}

__RT_VISIBILITY __softboundcets_metadata_t *
__softboundcets_shadowspace_metadata_ptr(void *address) {

  size_t ptr = (size_t)address;
  __softboundcets_metadata_t *trie_secondary_table;
  size_t primary_index = (ptr >> 25);
  trie_secondary_table = __softboundcets_trie_primary_table[primary_index];

  size_t secondary_index = ((ptr >> 3) & 0x3fffff);
  __softboundcets_metadata_t *entry_ptr =
      &trie_secondary_table[secondary_index];

  __softboundcets_log_pointer_metadata(address, entry_ptr);

  return entry_ptr;
}

__RT_VISIBILITY __softboundcets_metadata_t *
__softboundcets_shadowspace_metadata_ptr_create_secondary_tries(void *address) {

  size_t ptr = (size_t)address;
  __softboundcets_metadata_t *trie_secondary_table;
  size_t primary_index = (ptr >> 25);
  trie_secondary_table = __softboundcets_trie_primary_table[primary_index];

  /* unnecessary control flow causes performance overhead */
  /* this can cause segfaults with uninitialized pointer reads from memory */
  if (UNLIKELY(trie_secondary_table == NULL)) {
    trie_secondary_table = __softboundcets_trie_allocate();
    __softboundcets_trie_primary_table[primary_index] = trie_secondary_table;
  }

  size_t secondary_index = ((ptr >> 3) & 0x3fffff);
  __softboundcets_metadata_t *entry_ptr =
      &trie_secondary_table[secondary_index];

  __softboundcets_log_pointer_metadata(address, entry_ptr);

  return entry_ptr;
}

__RT_VISIBILITY __softboundcets_metadata_t *
__softboundcets_shadowspace_vector_metadata_ptr(void *addr_of_ptr, int index) {
  size_t val = index * 8;
  size_t addr = (size_t)addr_of_ptr;
  addr = addr + val;
  sbcets_base_t addr_cast = (sbcets_base_t)addr;

  return __softboundcets_shadowspace_metadata_ptr(addr_cast);
}

__RT_VISIBILITY __softboundcets_metadata_t *
__softboundcets_shadowspace_masked_vector_metadata_ptr(void *addr_of_ptr,
                                                       int index, bool mask) {
  if (mask)
    return __softboundcets_shadowspace_vector_metadata_ptr(addr_of_ptr, index);
  return &dummy_invalid_metadata;
}

#if __SOFTBOUNDCETS_SPATIAL_TEMPORAL || __SOFTBOUNDCETS_SPATIAL
__RT_VISIBILITY sbcets_base_t
__softboundcets_metadata_load_base(void *address) {
  __softboundcets_metadata_t *entry_ptr =
      __softboundcets_shadowspace_metadata_ptr(address);
  sbcets_base_t base = entry_ptr->base;
  __softboundcets_log_message(
      LOG_LEVEL_DEBUG, "[metadata_load_base]  addr_of_ptr = %p, base = %p\n",
      address, base);
  return base;
}

__RT_VISIBILITY sbcets_bound_t
__softboundcets_metadata_load_bound(void *address) {
  __softboundcets_metadata_t *entry_ptr =
      __softboundcets_shadowspace_metadata_ptr(address);
  sbcets_bound_t bound = entry_ptr->bound;
  __softboundcets_log_message(
      LOG_LEVEL_DEBUG, "[metadata_load_bound] addr_of_ptr = %p, bound = %p\n",
      address, bound);
  return bound;
}
__RT_VISIBILITY sbcets_base_t
__softboundcets_metadata_load_vector_base(void *ptr, int index) {
  size_t val = index * 8;
  size_t addr = (size_t)ptr;
  addr = addr + val;
  sbcets_base_t addr_cast = (sbcets_base_t)addr;

  return __softboundcets_metadata_load_base(addr_cast);
}

__RT_VISIBILITY sbcets_bound_t
__softboundcets_metadata_load_vector_bound(void *ptr, int index) {
  size_t val = index * 8;
  size_t addr = (size_t)ptr;
  addr = addr + val;
  sbcets_base_t addr_cast = (sbcets_base_t)addr;

  return __softboundcets_metadata_load_bound(addr_cast);
}

__RT_VISIBILITY sbcets_base_t __softboundcets_metadata_masked_load_vector_base(
    void *ptr, int index, bool mask) {
  if (mask)
    return __softboundcets_metadata_load_vector_base(ptr, index);
  return 0;
}
__RT_VISIBILITY sbcets_bound_t
__softboundcets_metadata_masked_load_vector_bound(void *ptr, int index,
                                                  bool mask) {
  if (mask)
    return __softboundcets_metadata_load_vector_bound(ptr, index);
  return 0;
}

#endif

#if __SOFTBOUNDCETS_SPATIAL_TEMPORAL || __SOFTBOUNDCETS_TEMPORAL
__RT_VISIBILITY size_t __softboundcets_metadata_load_key(void *address) {
  __softboundcets_metadata_t *entry_ptr =
      __softboundcets_shadowspace_metadata_ptr(address);
  sbcets_key_t key = entry_ptr->key;
  __softboundcets_log_message(
      LOG_LEVEL_DEBUG, "[metadata_load_key]   addr_of_ptr = %p, key = %p\n",
      address, key);
  return key;
}

__RT_VISIBILITY size_t *__softboundcets_metadata_load_lock(void *address) {

  __softboundcets_metadata_t *entry_ptr =
      __softboundcets_shadowspace_metadata_ptr(address);
  sbcets_lock_t lock = entry_ptr->lock;
  __softboundcets_log_message(
      LOG_LEVEL_DEBUG, "[metadata_load_lock]  addr_of_ptr = %p, lock = %p\n",
      address, lock);
  return lock;
}

__RT_VISIBILITY sbcets_lock_t
__softboundcets_metadata_load_vector_lock(void *ptr, int index) {
  size_t val = index * 8;
  size_t addr = (size_t)ptr;
  addr = addr + val;
  sbcets_base_t addr_cast = (sbcets_base_t)addr;

  return __softboundcets_metadata_load_lock(addr_cast);
}
__RT_VISIBILITY sbcets_key_t
__softboundcets_metadata_load_vector_key(void *ptr, int index) {
  size_t val = index * 8;
  size_t addr = (size_t)ptr;
  addr = addr + val;
  sbcets_base_t addr_cast = (sbcets_base_t)addr;

  return __softboundcets_metadata_load_key(addr_cast);
}

__RT_VISIBILITY sbcets_key_t __softboundcets_metadata_masked_load_vector_key(
    void *ptr, int index, bool mask) {
  if (mask)
    return __softboundcets_metadata_load_vector_key(ptr, index);
  return 0;
}

__RT_VISIBILITY sbcets_lock_t __softboundcets_metadata_masked_load_vector_lock(
    void *ptr, int index, bool mask) {
  if (mask)
    return __softboundcets_metadata_load_vector_lock(ptr, index);
  return 0;
}
#endif

__RT_VISIBILITY void
__softboundcets_temporal_load_dereference_check(size_t *pointer_lock,
                                                size_t key) {

  /* URGENT: I should think about removing this condition check */
  if (IS_INVALID_LOCK((size_t)pointer_lock)) {
    __softboundcets_error_printf(
        "[temporal_load_deref_check] Invalid temporal lock: %p\n",
        pointer_lock);
    __softboundcets_abort();
    return;
  }

  size_t temp = *pointer_lock;

  if (temp != key) {
    __softboundcets_error_printf(
        "[temporal_load_deref_check] Key mismatch key = %zx, *lock=%zx\n", key,
        temp);
    __softboundcets_abort();
  }
}

__RT_VISIBILITY void
__softboundcets_temporal_store_dereference_check(size_t *pointer_lock,
                                                 size_t key) {

  if (IS_INVALID_LOCK((size_t)pointer_lock)) {
    __softboundcets_error_printf(
        "[temporal_store_deref_check] Invalid temporal lock: %p\n",
        pointer_lock);
    __softboundcets_abort();
    return;
  }

  size_t temp = *pointer_lock;

  if (temp != key) {

    __softboundcets_error_printf(
        "[temporal_store_deref_check] Key mismatch, key = %zx, *lock=%zx\n",
        key, temp);
    __softboundcets_abort();
  }
}

__RT_VISIBILITY void __softboundcets_stack_memory_deallocation(size_t ptr_key) {

#ifndef __SOFTBOUNDCETS_CONSTANT_STACK_KEY_LOCK

  __softboundcets_stack_temporal_space_begin--;
  *(__softboundcets_stack_temporal_space_begin) = 0;

#endif

  return;
}

__RT_VISIBILITY void __softboundcets_memory_deallocation(size_t *ptr_lock,
                                                         size_t ptr_key) {

  if (IS_INVALID_LOCK((size_t)ptr_lock)) {
    __softboundcets_error_printf("[mem_dealloc] Invalid temporal lock: %p\n",
                                 ptr_lock);
    __softboundcets_abort();
    return;
  }
  size_t lock_content = *ptr_lock;

  if (lock_content != ptr_key || lock_content == 1) {
    __softboundcets_log_message(
        LOG_LEVEL_ERROR,
        "[mem_dealloc] invalid deallocation!\npointer_lock = %p, key = %zx, "
        "*pointer_lock=%zx\n",
        ptr_lock, ptr_key, *ptr_lock);
    __softboundcets_abort();
    return;
  }

  __softboundcets_log_message(
      LOG_LEVEL_INFO, "[mem_dealloc] pointer_lock = %p, *pointer_lock=%zx\n",
      ptr_lock, *ptr_lock);

  *ptr_lock = 0;
  *((void **)ptr_lock) = __softboundcets_lock_next_location;
  __softboundcets_lock_next_location = ptr_lock;
}

__RT_VISIBILITY void *__softboundcets_allocate_lock_location(void) {

  void *temp = NULL;
  if (__softboundcets_lock_next_location == NULL) {
    __softboundcets_debug_printf("[lock_allocate] new_lock_location=%p\n",
                                 __softboundcets_lock_new_location);

    if (__softboundcets_lock_new_location >
        __softboundcets_temporal_space_begin +
            __SOFTBOUNDCETS_N_TEMPORAL_ENTRIES) {
      __softboundcets_error_printf(
          "[lock_allocate] out of temporal free entries \n");
      __softboundcets_abort();
    }

    return __softboundcets_lock_new_location++;
  }

  temp = __softboundcets_lock_next_location;
  __softboundcets_lock_next_location =
      *((size_t **)__softboundcets_lock_next_location);
  __softboundcets_debug_printf(
      "[lock_allocate] allocated lock_location=%p (-> %p)\n", temp,
      __softboundcets_lock_next_location);

  return temp;
}

__RT_VISIBILITY void
__softboundcets_allocation_secondary_trie_allocate_range(void *initial_ptr,
                                                         size_t size) {

  if (!__SOFTBOUNDCETS_PREALLOCATE_TRIE)
    return;

  void *addr_of_ptr = initial_ptr;
  size_t start_addr_of_ptr = (size_t)addr_of_ptr;
  size_t start_primary_index = start_addr_of_ptr >> 25;

  size_t end_addr_of_ptr = (size_t)((char *)initial_ptr + size);
  size_t end_primary_index = end_addr_of_ptr >> 25;

  for (; start_primary_index <= end_primary_index; start_primary_index++) {

    __softboundcets_metadata_t *trie_secondary_table =
        __softboundcets_trie_primary_table[start_primary_index];
    if (trie_secondary_table == NULL) {
      trie_secondary_table = __softboundcets_trie_allocate();
      __softboundcets_trie_primary_table[start_primary_index] =
          trie_secondary_table;
    }
  }
}

__RT_VISIBILITY void
__softboundcets_allocation_secondary_trie_allocate(void *addr_of_ptr) {

  /* URGENT: THIS FUNCTION REQUIRES REWRITE */

  if (!__SOFTBOUNDCETS_PREALLOCATE_TRIE)
    return;

  size_t ptr = (size_t)addr_of_ptr;
  size_t primary_index = (ptr >> 25);
  //  size_t secondary_index = ((ptr >> 3) & 0x3fffff);

  __softboundcets_metadata_t *trie_secondary_table =
      __softboundcets_trie_primary_table[primary_index];

  if (trie_secondary_table == NULL) {
    trie_secondary_table = __softboundcets_trie_allocate();
    __softboundcets_trie_primary_table[primary_index] = trie_secondary_table;
  }

  __softboundcets_metadata_t *trie_secondary_table_second_entry =
      __softboundcets_trie_primary_table[primary_index + 1];

  if (trie_secondary_table_second_entry == NULL) {
    __softboundcets_trie_primary_table[primary_index + 1] =
        __softboundcets_trie_allocate();
  }

  if (primary_index != 0 &&
      (__softboundcets_trie_primary_table[primary_index - 1] == NULL)) {
    __softboundcets_trie_primary_table[primary_index - 1] =
        __softboundcets_trie_allocate();
  }

  return;
}

__RT_VISIBILITY void __softboundcets_stack_memory_allocation(size_t **ptr_lock,
                                                             size_t *ptr_key) {

#if __SOFTBOUNDCETS_CONSTANT_STACK_KEY_LOCK
  *ptr_key = 1;
  *ptr_lock = __softboundcets_global_lock;
#else
  size_t temp_id = __softboundcets_key_id_counter++;
  *ptr_lock = (size_t *)__softboundcets_stack_temporal_space_begin++;
  *ptr_key = temp_id;
  **ptr_lock = temp_id;
#endif
}

__RT_VISIBILITY void __softboundcets_memory_allocation(void *ptr,
                                                       size_t **ptr_lock,
                                                       size_t *ptr_key) {

  size_t temp_id = __softboundcets_key_id_counter++;

  *ptr_lock = (size_t *)__softboundcets_allocate_lock_location();
  *ptr_key = temp_id;
  **ptr_lock = temp_id;

  __softboundcets_add_to_free_map(temp_id, ptr);
  //  printf("memory allocation ptr=%zx, ptr_key=%zx\n", ptr, temp_id);
  __softboundcets_allocation_secondary_trie_allocate(ptr);

  __softboundcets_log_message(
      LOG_LEVEL_INFO, "[mem_alloc] lock = %p, ptr_key = %p, key = %zx\n",
      *ptr_lock, ptr_key, temp_id);
}

__RT_VISIBILITY size_t *__softboundcets_get_global_lock(void) {
  return __softboundcets_global_lock;
}

__RT_VISIBILITY void __softboundcets_add_to_free_map(size_t ptr_key,
                                                     void *ptr) {

  if (!__SOFTBOUNDCETS_FREE_MAP)
    return;

  assert(ptr != NULL);

  size_t counter = 0;
  while (1) {
    size_t index = (ptr_key + counter) % __SOFTBOUNDCETS_N_FREE_MAP_ENTRIES;
    size_t *entry_ptr = &__softboundcets_free_map_table[index];
    size_t tag = *entry_ptr;

    if (tag == 0 || tag == 2) {
      //      printf("entry_ptr=%zx, ptr=%zx, key=%zx\n", entry_ptr, ptr,
      //      ptr_key);
      *entry_ptr = (size_t)(ptr);
      return;
    }
    if (counter >= (__SOFTBOUNDCETS_N_FREE_MAP_ENTRIES)) {
#ifndef __NOSIM_CHECKS
      __softboundcets_abort();
#else
      break;
#endif
    }
    counter++;
  }
  return;
}

__RT_VISIBILITY void __softboundcets_check_remove_from_free_map(size_t ptr_key,
                                                                void *ptr) {

  if (!__SOFTBOUNDCETS_FREE_MAP) {
    return;
  }
  size_t counter = 0;
  while (1) {
    size_t index = (ptr_key + counter) % __SOFTBOUNDCETS_N_FREE_MAP_ENTRIES;
    size_t *entry_ptr = &__softboundcets_free_map_table[index];
    size_t tag = *entry_ptr;

    if (tag == 0) {
#ifndef __NOSIM_CHECKS
      __softboundcets_abort();
#else
      break;
#endif
    }

    if (tag == (size_t)ptr) {
      *entry_ptr = 2;
      return;
    }

    if (counter >= __SOFTBOUNDCETS_N_FREE_MAP_ENTRIES) {
      //      printf("free map out of entries\n");
#ifndef __NOSIM_CHECKS
      __softboundcets_abort();
#else
      break;
#endif
    }
    counter++;
  }
  return;
}

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
                                                           int index) {
  size_t val = index * 8;
  size_t addr = (size_t)addr_of_ptr;
  addr = addr + val;

#if __SOFTBOUNDCETS_SPATIAL
  __softboundcets_metadata_store((void *)addr, base, bound);
#elif __SOFTBOUNDCETS_TEMPORAL
  __softboundcets_metadata_store((void *)addr, key, lock);
#elif __SOFTBOUNDCETS_SPATIAL_TEMPORAL
  __softboundcets_metadata_store((void *)addr, base, bound, key, lock);
#endif
}
