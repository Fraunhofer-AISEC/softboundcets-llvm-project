//=== softboundcets-wrappers.c- SoftBound wrappers for libraries --*- C -*===//
// Copyright (c) 2011 Santosh Nagarakatte, Milo M. K. Martin. All rights
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

// #include "safecode/Config/config.h"

#define _GNU_SOURCE

#include <arpa/inet.h>

#if defined(__linux__)
#include <errno.h>
#include <libintl.h>
#include <obstack.h>
#include <sys/wait.h>
#include <wait.h>
#endif

#include <fnmatch.h>
#include <sys/mman.h>
#include <sys/resource.h>
#include <sys/socket.h>
#include <sys/stat.h>
#include <sys/time.h>
#include <sys/times.h>
#include <sys/types.h>
#include <wchar.h>

#include <netinet/in.h>

#include <assert.h>
#include <ctype.h>
#include <dirent.h>
#include <errno.h>
#include <getopt.h>
#include <glob.h>
#include <grp.h>
#include <limits.h>
#include <math.h>
#include <netdb.h>
#include <pwd.h>
#include <setjmp.h>
#include <signal.h>
#include <stdarg.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <syslog.h>
#include <malloc.h>

#include <langinfo.h>
#include <regex.h>
#include <time.h>
#include <ttyent.h>
#include <unistd.h>

#ifdef HAVE_ICONV_H
#include <iconv.h>
#endif

#include <locale.h>
#include <math.h>
#include <utime.h>

#include <fcntl.h>
#include <wctype.h>

#include "sanitizer_common/sanitizer_vector.h"

#include "softboundcets.h"

typedef void (*sighandler_t)(int);
typedef void (*void_func_ptr)(void);

extern size_t *__softboundcets_global_lock;

/* extern void __softboundcets_process_memory_total(); */

__RT_VISIBILITY void
__softboundcets_read_shadow_stack_metadata_store(char **endptr, int arg_num) {

#if __SOFTBOUNDCETS_SPATIAL
  void *nptr_base = __softboundcets_load_base_shadow_stack(arg_num);
  void *nptr_bound = __softboundcets_load_bound_shadow_stack(arg_num);

  __softboundcets_metadata_store(endptr, nptr_base, nptr_bound);

#elif __SOFTBOUNDCETS_TEMPORAL

  size_t nptr_key = __softboundcets_load_key_shadow_stack(arg_num);
  size_t *nptr_lock = __softboundcets_load_lock_shadow_stack(arg_num);

  __softboundcets_metadata_store(endptr, nptr_key, nptr_lock);

#elif __SOFTBOUNDCETS_SPATIAL_TEMPORAL
  void *nptr_base = __softboundcets_load_base_shadow_stack(arg_num);
  void *nptr_bound = __softboundcets_load_bound_shadow_stack(arg_num);
  size_t nptr_key = __softboundcets_load_key_shadow_stack(arg_num);
  size_t *nptr_lock = __softboundcets_load_lock_shadow_stack(arg_num);
  __softboundcets_metadata_store(endptr, nptr_base, nptr_bound, nptr_key,
                                 nptr_lock);

#endif
}

__RT_VISIBILITY void
__softboundcets_propagate_metadata_shadow_stack_from(int from_argnum,
                                                     int to_argnum) {

#if __SOFTBOUNDCETS_SPATIAL || __SOFTBOUNDCETS_SPATIAL_TEMPORAL

  void *base = __softboundcets_load_base_shadow_stack(from_argnum);
  void *bound = __softboundcets_load_bound_shadow_stack(from_argnum);
  __softboundcets_store_base_shadow_stack(base, to_argnum);
  __softboundcets_store_bound_shadow_stack(bound, to_argnum);

#endif
#if __SOFTBOUNDCETS_TEMPORAL || __SOFTBOUNDCETS_SPATIAL_TEMPORAL

  size_t key = __softboundcets_load_key_shadow_stack(from_argnum);
  size_t *lock = __softboundcets_load_lock_shadow_stack(from_argnum);
  __softboundcets_store_key_shadow_stack(key, to_argnum);
  __softboundcets_store_lock_shadow_stack(lock, to_argnum);

#endif
}

__RT_VISIBILITY void __softboundcets_store_null_return_metadata(void) {

#if __SOFTBOUNDCETS_SPATIAL || __SOFTBOUNDCETS_SPATIAL_TEMPORAL

  __softboundcets_store_base_shadow_stack(NULL, 0);
  __softboundcets_store_bound_shadow_stack(NULL, 0);

#endif
#if __SOFTBOUNDCETS_TEMPORAL || __SOFTBOUNDCETS_SPATIAL_TEMPORAL

  __softboundcets_store_key_shadow_stack(0, 0);
  __softboundcets_store_lock_shadow_stack(NULL, 0);

#endif
}

__RT_VISIBILITY void __softboundcets_store_return_metadata(void *base,
                                                           void *bound,
                                                           sbcets_key_t key,
                                                           sbcets_lock_t lock) {

#if __SOFTBOUNDCETS_SPATIAL || __SOFTBOUNDCETS_SPATIAL_TEMPORAL

  __softboundcets_store_base_shadow_stack(base, 0);
  __softboundcets_store_bound_shadow_stack(bound, 0);

#endif
#if __SOFTBOUNDCETS_TEMPORAL || __SOFTBOUNDCETS_SPATIAL_TEMPORAL

  __softboundcets_store_key_shadow_stack(key, 0);
  __softboundcets_store_lock_shadow_stack(lock, 0);

#endif
}

/*
 * Helper macros for parameter checking (depending on what checks are enabled)
 */

#if __SOFTBOUNDCETS_SPATIAL || __SOFTBOUNDCETS_SPATIAL_TEMPORAL

// Loads the base and bound from the shadow stack for the argument at the given position and store
// them at <ptr>_base and <ptr>_bounds.
#define LOAD_PTR_BOUNDS(pos, ptr)                                                              \
  [[ maybe_unused ]] sbcets_base_t ptr##_base = __softboundcets_load_base_shadow_stack(pos);   \
  [[ maybe_unused ]] sbcets_bound_t ptr##_bound = __softboundcets_load_bound_shadow_stack(pos);

// Since bounds checking every pointer may lead to a significant loss in performance, those checks
// need to be enabled using a macro.
#if __SOFTBOUNDCETS_CHECK_LOADS

// Check if a pointer dereference of a given size is in bounds and generate an appropriate error
// message if not.
// This requires both base and bounds to be defined (see LOAD_PTR_BOUNDS).
#define CHECK_PTR_BOUNDS_LOAD_ONLY(ptr, size)                                         \
  __softboundcets_spatial_load_dereference_check(ptr##_base, ptr##_bound, (void*)ptr, size);

// Check if a string function can properly dereference the pointer when it is interpreted as a
// string.
// This requires the base and bound pointers to be defined (See LOAD_PTR_BOUNDS).
#define CHECK_STRING_BOUNDS_LOAD_ONLY(ptr)                                                          \
  if (!memchr(ptr, '\0', (char*)ptr##_bound - (char*)ptr)) {                                        \
    __softboundcets_error_printf("In string load dereference check: base=%zx, bound=%zx, ptr=%zx",  \
      ptr##_base, ptr##_bound, ptr);                                                                \
    __softboundcets_abort();                                                                        \
  }

#else // __SOFTBOUNDCETS_CHECK_LOADS

// NOOP since loads are not checked.
// Define __SOFTBOUNDCETS_CHECK_LOADS to enable bounds checks on reads.
#define CHECK_PTR_BOUNDS_LOAD_ONLY(ptr, size)

// NOOP since loads are not checked.
// Define __SOFTBOUNDCETS_CHECK_LOADS to enable bounds checks on reads.
#define CHECK_STRING_BOUNDS_LOAD_ONLY(ptr)

#endif // __SOFTBOUNDCETS_CHECK_LOADS

// Check if a pointer dereference is in bounds and raise an appropriate error if not.
// This macro requires base and bound for the pointer to be in scope (see LOAD_PTR_BOUNDS)
#define CHECK_PTR_BOUNDS_STORE_ONLY(ptr, size)                                        \
  __softboundcets_spatial_store_dereference_check(ptr##_base, ptr##_bound, ptr, size);

// Check if a string function can access this pointer correctly, that is that it contains a null
// terminator within bounds.
// This macro requires the appropriate base and bound to be in scope (See LOAD_PTR_BOUNDS)
#define CHECK_STRING_BOUNDS_STORE_ONLY(ptr)                                                         \
  if (!memchr(ptr, '\0', (char*)ptr##_bound - (char*)ptr)) {                                        \
    __softboundcets_error_printf("In string store dereference check: base=%zx, bound=%zx, ptr=%zx", \
      ptr##_base, ptr##_bound, ptr);                                                                \
    __softboundcets_abort();                                                                        \
  }

#else // __SOFTBOUNDCETS_SPATIAL || __SOFTBOUNDCETS_SPATIAL_TEMPORAL

// Since bounds checking is disabled, this macro introduces dummy variables for a parameter's base
// and bounds pointers.

// To enable bounds checking, define __SOFTBOUND_SPATIAL=1 of __SOFTBOUND_SPATIAL_TEMPORAL=1.
#define LOAD_PTR_BOUNDS(pos, ptr)                    \
  [[ maybe_unused ]] void *ptr##_base = nullptr;     \
  [[ maybe_unused ]] void *ptr##_bound = nullptr;

// NOOP since bounds checking and load checking are both disabled.
// To enable bounds checking, define __SOFTBOUND_SPATIAL=1 or __SOFTBOUND_SPATIAL_TEMPORAL=1.
// Define __SOFTBOUNDCETS_CHECK_LOADS to enable load checking.
#define CHECK_PTR_BOUNDS_LOAD_ONLY(ptr, size)

// NOOP since bounds checking and load checking are both disabled.
// To enable bounds checking, define __SOFTBOUND_SPATIAL=1 or __SOFTBOUND_SPATIAL_TEMPORAL=1.
// Define __SOFTBOUNDCETS_CHECK_LOADS to enable load checking.
#define CHECK_STRING_BOUNDS_LOAD_ONLY(ptr)

// NOOP since bounds checking is disabled.
// To enable bounds checking, define __SOFTBOUND_SPATIAL=1 or __SOFTBOUND_SPATIAL_TEMPORAL=1.
#define CHECK_PTR_BOUNDS_STORE_ONLY(ptr, size)

// NOOP since bounds checking is disabled.
// To enable bounds checking, define __SOFTBOUND_SPATIAL=1 or __SOFTBOUND_SPATIAL_TEMPORAL=1.
#define CHECK_STRING_BOUNDS_STORE_ONLY(ptr)

#endif // __SOFTBOUNDCETS_SPATIAL || __SOFTBOUNDCETS_SPATIAL_TEMPORAL

// Introduce base and bounds for the given argument and check for a read access.
// This combines the LOAD_PTR_BOUNDS and CHECK_PTR_BOUNDS_LOAD_ONLY.
#define CHECK_PTR_BOUNDS_LOAD(pos, ptr, size) \
  LOAD_PTR_BOUNDS(pos, ptr);	                \
  CHECK_PTR_BOUNDS_LOAD_ONLY(ptr, size);

// Introduce base and bound for the given argument.
// If the pointer is not null, also check if it can be dereferenced.
// This combines the LOAD_PTR_BOUNDS and CHECK_PTR_BOUNDS_LOAD_ONLY.
#define CHECK_PTR_BOUNDS_LOAD_NULLABLE(pos, ptr, size) \
  LOAD_PTR_BOUNDS(pos, ptr);                           \
  if (ptr != nullptr) {                                \
    CHECK_PTR_BOUNDS_LOAD_ONLY(ptr, size);             \
  }

// Introduce base and bound for the given string argument and check if it can be safely passed to
// a string function.
// This combines the LOAD_PTR_BOUNDS and CHECK_STRING_BOUNDS_LOAD_ONLY.
#define CHECK_STRING_BOUNDS_LOAD(pos, ptr)  \
  LOAD_PTR_BOUNDS(pos, ptr);                \
  CHECK_STRING_BOUNDS_LOAD_ONLY(ptr);

// Introduce base and bound for the given string argument and check if it can be safely passed to
// a string function, if it is not null.
// This combines the LOAD_PTR_BOUNDS and CHECK_STRING_BOUNDS_LOAD_ONLY.
#define CHECK_STRING_BOUNDS_LOAD_NULLABLE(pos, ptr) \
  LOAD_PTR_BOUNDS(pos, ptr);                        \
  if (ptr != nullptr) {                             \
    CHECK_STRING_BOUNDS_LOAD_ONLY(ptr);             \
  }

// Introduce the base and bound for a given argument and check if it can be dereferenced.
// This combines the LOAD_PTR_BOUNDS and CHECK_PTR_BOUNDS_STORE_ONLY macros.
#define CHECK_PTR_BOUNDS_STORE(pos, ptr, size) \
  LOAD_PTR_BOUNDS(pos, ptr);                   \
  CHECK_PTR_BOUNDS_STORE_ONLY(ptr, size);

// Introduce the base and bound for a given argument.
// It the argument is not null, also check if it can be dereferenced.
// This combines the LOAD_PTR_BOUNDS and CHECK_PTR_BOUNDS_STORE_ONLY macros.
#define CHECK_PTR_BOUNDS_STORE_NULLABLE(pos, ptr, size) \
  LOAD_PTR_BOUNDS(pos, ptr);                            \
  if (ptr != nullptr) {                                 \
    CHECK_PTR_BOUNDS_STORE_ONLY(ptr, size);             \
  }

// Introduce the base and bound for a given argument and check if it can be dereferenced.
// This combines the LOAD_PTR_BOUNDS and CHECK_PTR_BOUNDS_STORE_ONLY macros.
#define CHECK_STRING_BOUNDS_STORE(pos, ptr) \
  LOAD_PTR_BOUNDS(pos, ptr);                \
  CHECK_STRING_BOUNDS_STORE_ONLY(ptr);

// Introduce the base and bound for a given argument.
// It the argument is not null, also check if it can be dereferenced.
// This combines the LOAD_PTR_BOUNDS and CHECK_PTR_BOUNDS_STORE_ONLY macros.
#define CHECK_STRING_BOUNDS_STORE_NULLABLE(pos, ptr, size)  \
  LOAD_PTR_BOUNDS(pos, ptr);                                \
  if (ptr != nullptr) {                                     \
    CHECK_STRING_BOUNDS_STORE_ONLY(ptr, size);              \
  }

#if __SOFTBOUNDCETS_TEMPORAL || __SOFTBOUNDCETS_SPATIAL_TEMPORAL

// Loads the lock and key for the given parameter from the shadow stack into <ptr>_lock and
// <ptr>_key.
#define LOAD_PTR_LOCK(pos, ptr)                                                              \
  [[ maybe_unused ]] sbcets_lock_t ptr##_lock = __softboundcets_load_lock_shadow_stack(pos); \
  [[ maybe_unused ]] sbcets_key_t ptr##_key = __softboundcets_load_key_shadow_stack(pos);

#if __SOFTBOUNDCETS_CHECK_LOADS

// Check if a pointer is still alive when it is dereferenced.
// The lock and key for the pointer must be defined (see LOAD_PTR_LOCK).
#define CHECK_PTR_ALIVE_LOAD_ONLY(ptr)                                    \
  __softboundcets_temporal_load_dereference_check(ptr##_lock, ptr##_key);

#else // __SOFTBOUNDCETS_CHECK_LOADS

// NOOP, since load checking is disabled.
// define __SOFTBOUNDCETS_CHECK_LOADS=1 to enable.
#define CHECK_PTR_ALIVE_LOAD_ONLY(ptr)

#endif // __SOFTBOUNDCETS_CHECK_LOADS

// Check if a pointer is still alive when dereferenced for writing.
// This macro requires that the lock and key values for the pointer are in scope
// (see LOAD_PTR_LOCK).
#define CHECK_PTR_ALIVE_STORE_ONLY(ptr)                                   \
  __softboundcets_temporal_store_dereference_check(ptr##_lock, ptr##_key);

#else // __SOFTBOUNDCETS_TEMPORAL || __SOFTBOUNDCETS_SPATIAL_TEMPORAL

// Define dummy values for the pointers lock and key as temporal checking is disabled.
// To enable, define __SOFTBOUNDCETS_TEMPORAL=1 or __SOFTBOUNDCETS_SPATIAL_TEMPORAL=1
#define LOAD_PTR_LOCK(pos, ptr)                          \
  [[ maybe_unused ]] sbcets_lock_t ptr##_lock = nullptr; \
  [[ maybe_unused ]] sbcets_key_t ptr##_key = 0;

// NOOP as temporal checking is disabled.
// To enable, define __SOFTBOUNDCETS_CHECK_LOADS=1 and __SOFTBOUNDCETS_TEMPORAL=1 or
// __SOFTBOUNDCETS_SPATIAL_TEMPORAL=1
#define CHECK_PTR_ALIVE_LOAD_ONLY(ptr)

// NOOP as temporal checking is disabled.
// To enable, define __SOFTBOUNDCETS_TEMPORAL=1 or __SOFTBOUNDCETS_SPATIAL_TEMPORAL=1
#define CHECK_PTR_ALIVE_STORE_ONLY(ptr)

#endif // __SOFTBOUNDCETS_TEMPORAL || __SOFTBOUNDCETS_SPATIAL_TEMPORAL

// Introduce the lock and key for an argument and check that it is alive.
// This macro combines the LOAD_PTR_LOCK and CHECK_PTR_ACTIVE_LOAD_ONLY macros.
#define CHECK_PTR_ALIVE_LOAD(pos, ptr)  \
  LOAD_PTR_LOCK(pos, ptr);              \
  CHECK_PTR_ALIVE_LOAD_ONLY(ptr);

// Introduce the lock and key for an argument and check that it is alive if it is not null.
// This macro combines the LOAD_PTR_LOCK and CHECK_PTR_ACTIVE_LOAD_ONLY macros.
#define CHECK_PTR_ALIVE_LOAD_NULLABLE(pos, ptr) \
  LOAD_PTR_LOCK(pos, ptr);                      \
  if (ptr != nullptr) {                         \
    CHECK_PTR_ALIVE_LOAD_ONLY(ptr);             \
  }

// Introduce the lock and key for an argument and check that it is alive.
// This macro combines the LOAD_PTR_LOCK and CHECK_PTR_ACTIVE_STORe_ONLY macros.
#define CHECK_PTR_ALIVE_STORE(pos, ptr) \
  LOAD_PTR_LOCK(pos, ptr);              \
  CHECK_PTR_ALIVE_STORE_ONLY(ptr);

// Introduce the lock and key for an argument and check that it is alive if it is not null.
// This macro combines the LOAD_PTR_LOCK and CHECK_PTR_ACTIVE_STORE_ONLY macros.
#define CHECK_PTR_ALIVE_STORE_NULLABLE(pos, ptr) \
  LOAD_PTR_LOCK(pos, ptr);                      \
  if (ptr != nullptr) {                         \
    CHECK_PTR_ALIVE_STORE_ONLY(ptr);             \
  }

// Check that a pointer read is both alive and in bounds.
// It will also introduce variables for its base, bound, key and lock in the local scope.
// This combines the CHECK_PTR_BOUNDS_LOAD and CHECK_PTR_ALIVE_LOAD macros.
#define CHECK_PTR_LOAD(pos, ptr, size)    \
  CHECK_PTR_BOUNDS_LOAD(pos, ptr, size);  \
  CHECK_PTR_ALIVE_LOAD(pos, ptr);

// Check that a pointer read is both alive and in bounds if it is not null.
// It will also introduce variables for its base, bound, key and lock in the local scope.
// This combines the CHECK_PTR_BOUNDS_LOAD_NULLABLE and CHECK_PTR_ALIVE_LOAD_NULLABLE macros.
#define CHECK_PTR_LOAD_NULLABLE(pos, ptr, size)    \
  CHECK_PTR_BOUNDS_LOAD_NULLABLE(pos, ptr, size);  \
  CHECK_PTR_ALIVE_LOAD_NULLABLE(pos, ptr);

// Check that a pointer write is both alive and in bounds.
// It will also introduce variables for its base, bound, key and lock in the local scope.
// This combines the CHECK_PTR_BOUNDS_STORE and CHECK_PTR_ALIVE_STORE macros.
#define CHECK_PTR_STORE(pos, ptr, size)   \
  CHECK_PTR_BOUNDS_STORE(pos, ptr, size); \
  CHECK_PTR_ALIVE_STORE(pos, ptr);

// Check that a pointer read is both alive and in bounds if it is not null.
// It will also introduce variables for its base, bound, key and lock in the local scope.
// This combines the CHECK_PTR_BOUNDS_STORE_NULLABLE and CHECK_PTR_ALIVE_STORE_NULLABLE macros.
#define CHECK_PTR_STORE_NULLABLE(pos, ptr, size)    \
  CHECK_PTR_BOUNDS_STORE_NULLABLE(pos, ptr, size);  \
  CHECK_PTR_ALIVE_STORE_NULLABLE(pos, ptr);

// Check that passing an argument to a function expecting a null terminated string is safe.
// It will also introduce variables for its base, bound, key and lock in the local scope.
// This combines the CHECK_STRING_BOUNDS_LOAD and CHECK_PTR_ALIVE_LOAD macros.
#define CHECK_STRING_LOAD(pos, ptr)   \
  CHECK_STRING_BOUNDS_LOAD(pos, ptr); \
  CHECK_PTR_ALIVE_LOAD(pos, ptr);

// Check that passing an argument to a function expecting a null terminated string is safe, if it
// is not null.
// It will still introduce variables for its base, bound, key and lock in the local scope.
// This combines the CHECK_STRING_BOUNDS_LOAD_NULLABLE and CHECK_PTR_ALIVE_LOAD_NULLABLE macros.
#define CHECK_STRING_LOAD_NULLABLE(pos, ptr)    \
  CHECK_STRING_BOUNDS_LOAD_NULLABLE(pos, ptr);  \
  CHECK_PTR_ALIVE_LOAD_NULLABLE(pos, ptr);

// Check that passing an argument to a function expecting a null terminated string is safe.
// It will also introduce variables for its base, bound, key and lock in the local scope.
// This combines the CHECK_STRING_BOUNDS_STORE and CHECK_PTR_ALIVE_STORE macros.
#define CHECK_STRING_STORE(pos, ptr)    \
  CHECK_STRING_BOUNDS_STORE(pos, ptr);  \
  CHECK_PTR_ALIVE_STORE(pos, ptr);

// Check that passing an argument to a function expecting a null terminated string is safe, if it
// is not null.
// It will still introduce variables for its base, bound, key and lock in the local scope.
// This combines the CHECK_STRING_BOUNDS_STORE_NULLABLE and CHECK_PTR_ALIVE_STORE_NULLABLE macros.
#define CHECK_STRING_STORE_NULLABLE(pos, ptr)    \
  CHECK_STRING_BOUNDS_STORE_NULLABLE(pos, ptr);  \
  CHECK_PTR_ALIVE_STORE_NULLABLE(pos, ptr);

/* wrappers for library calls (incomplete) */
//////////////////////system wrappers //////////////////////

__RT_VISIBILITY int softboundcets_setenv(const char *name, const char *value,
                                         int overwrite) {

  return setenv(name, value, overwrite);
}

__RT_VISIBILITY
int softboundcets_unsetenv(const char *name) { return unsetenv(name); }

__RT_VISIBILITY int softboundcets_system(char *ptr) { return system(ptr); }

__RT_VISIBILITY int softboundcets_setreuid(uid_t ruid, uid_t euid) {

  /* tested */
  return setreuid(ruid, euid);
}

__RT_VISIBILITY int softboundcets_mkstemp(char *templ) {

  /* tested */
  return mkstemp(templ);
}

__RT_VISIBILITY int softboundcets_getrlimit(int resource, struct rlimit *rlim) {

  /* tested */
  return getrlimit(resource, rlim);
}

__RT_VISIBILITY int softboundcets_setrlimit(int resource,
                                            const struct rlimit *rlim) {

  /* tested */
  return setrlimit(resource, rlim);
}

__RT_VISIBILITY size_t softboundcets_fread_unlocked(void *ptr, size_t size,
                                                    size_t n, FILE *stream) {

  return fread_unlocked(ptr, size, n, stream);
}

#if 0
__RT_VISIBILITY int
softboundcets_fputs_unlocked(const char *s, FILE *stream){
  return fputs_unlocked(s, stream);
}
#endif

__RT_VISIBILITY size_t softboundcets_fread(void *ptr, size_t size, size_t nmemb,
                                           FILE *stream) {
  /* tested */
  return fread(ptr, size, nmemb, stream);
}

__RT_VISIBILITY int softboundcets_mkdir(const char *pathname, mode_t mode) {

  /* tested */
  return mkdir(pathname, mode);
}

__RT_VISIBILITY int softboundcets_chroot(const char *path) {
  /* tested */
  return chroot(path);
}

__RT_VISIBILITY int softboundcets_rmdir(const char *pathname) {

  /* tested */
  return rmdir(pathname);
}

__RT_VISIBILITY int softboundcets_stat(const char *path, struct stat *buf) {
  /* tested */
  return stat(path, buf);
}

__RT_VISIBILITY int softboundcets_fputc(int c, FILE *stream) {

  /* tested */
  return fputc(c, stream);
}

__RT_VISIBILITY int softboundcets_fileno(FILE *stream) {

  return fileno(stream);
}

__RT_VISIBILITY int softboundcets_fgetc(FILE *stream) { return fgetc(stream); }

__RT_VISIBILITY int softboundcets_ungetc(int c, FILE *stream) {

  return ungetc(c, stream);
}

__RT_VISIBILITY int softboundcets_strncmp(const char *s1, const char *s2,
                                          size_t n) {
  return strncmp(s1, s2, n);
}

__RT_VISIBILITY long long softboundcets_fwrite(char *ptr, size_t size,
                                               size_t nmemb, FILE *stream) {
  return fwrite(ptr, size, nmemb, stream);
}

__RT_VISIBILITY double softboundcets_atof(char *ptr) { return atof(ptr); }

__RT_VISIBILITY int softboundcets_feof(FILE *stream) { return feof(stream); }

__RT_VISIBILITY int softboundcets_remove(const char *pathname) {

  return remove(pathname);
}

////////////////File Library Wrappers here //////////////////////

__RT_VISIBILITY FILE *softboundcets_tmpfile(void) {

  FILE *ret_ptr = tmpfile();
  void *ret_ptr_bound = (char *)ret_ptr + sizeof(FILE);
  __softboundcets_store_return_metadata(ret_ptr, ret_ptr_bound, 1,
                                        __softboundcets_global_lock);
  return ret_ptr;
}

__RT_VISIBILITY int softboundcets_ferror(FILE *stream) {

  return ferror(stream);
}

__RT_VISIBILITY long softboundcets_ftell(FILE *stream) { return ftell(stream); }

__RT_VISIBILITY int softboundcets_fstat(int filedes, struct stat *buff) {

  return fstat(filedes, buff);
}

// __RT_VISIBILITY int softboundcets___lxstat(int __ver, const char *__filename,
//                                            struct stat *__stat_buf) {

//   return __lxstat(__ver, __filename, __stat_buf);
// }

__RT_VISIBILITY size_t softboundcets_mbrtowc(wchar_t *pwc, const char *s,
                                             size_t n, mbstate_t *ps) {
  return mbrtowc(pwc, s, n, ps);
}

__RT_VISIBILITY int softboundcets_mbsinit(const mbstate_t *ps) {
  return mbsinit(ps);
}

// __RT_VISIBILITY int softboundcets___fxstat(int ver, int file_des,
//                                            struct stat *stat_struct) {
//   return __fxstat(ver, file_des, stat_struct);
// }

// __RT_VISIBILITY int softboundcets___fxstatat(int ver, int file_des,
//                                              const char *filename,
//                                              struct stat *stat_struct,
//                                              int flag) {
//   return __fxstatat(ver, file_des, filename, stat_struct, flag);
// }

__RT_VISIBILITY int softboundcets_fflush(FILE *stream) {

  return fflush(stream);
}

__RT_VISIBILITY int softboundcets_fputs(const char *s, FILE *stream) {

  return fputs(s, stream);
}

__RT_VISIBILITY DIR *softboundcets_fdopendir(int fd) {

  void *ret_ptr = (void *)fdopendir(fd);
  void *ret_ptr_bound = (char *)ret_ptr + 1024 * 1024;
  __softboundcets_store_return_metadata(ret_ptr, ret_ptr_bound, 1,
                                        __softboundcets_global_lock);
  return (DIR *)ret_ptr;
}

__RT_VISIBILITY int softboundcets_fseeko(FILE *stream, off_t offset,
                                         int whence) {

  return fseeko(stream, offset, whence);
}

__RT_VISIBILITY char *softboundcets_mkdtemp(char *templ) {

  char *ret_ptr = mkdtemp(templ);
  __softboundcets_propagate_metadata_shadow_stack_from(1, 0);
  return ret_ptr;
}

__RT_VISIBILITY int softboundcets_linkat(int olddirfd, const char *oldpath,
                                         int newdirfd, const char *newpath,
                                         int flags) {

  return linkat(olddirfd, oldpath, newdirfd, newpath, flags);
}

__RT_VISIBILITY int softboundcets_utimes(const char *filename,
                                         const struct timeval times[2]) {

  return utimes(filename, times);
}

#if 0
__RT_VISIBILITY int softboundcets_futimesat(int dirfd, const char *pathname,
                                          const struct timeval times[2]){
  
  return futimesat(dirfd, pathname, times);
}
#endif

__RT_VISIBILITY int softboundcets_futimens(int fd,
                                           const struct timespec times[2]) {

  return futimens(fd, times);
}

__RT_VISIBILITY int softboundcets_utimensat(int dirfd, const char *pathname,
                                            const struct timespec times[2],
                                            int flags) {

  return utimensat(dirfd, pathname, times, flags);
}

__RT_VISIBILITY int softboundcets_iswprint(wint_t wc) { return iswprint(wc); }

__RT_VISIBILITY int softboundcets_getpagesize(void) { return getpagesize(); }

__RT_VISIBILITY int softboundcets_dirfd(DIR *dirp) { return dirfd(dirp); }

__RT_VISIBILITY struct lconv *softboundcets_localeconv(void) {
  struct lconv *temp = localeconv();

  __softboundcets_store_return_metadata(temp, temp + 1024, 1,
                                        __softboundcets_global_lock);

  return temp;
}

__RT_VISIBILITY struct tm *softboundcets_gmtime(const time_t *timep) {

  struct tm *temp = gmtime(timep);

  __softboundcets_store_return_metadata(temp, temp + 1024, 1,
                                        __softboundcets_global_lock);

  return temp;
}

__RT_VISIBILITY void *
softboundcets_bsearch(const void *key, const void *base, size_t nmemb,
                      size_t size, int (*compar)(const void *, const void *)) {

  void *ret_ptr = bsearch(key, base, nmemb, size, compar);

  __softboundcets_propagate_metadata_shadow_stack_from(2, 0);
  return ret_ptr;
}

__RT_VISIBILITY
struct group *softboundcets_getgrnam(const char *name) {
  struct group *ret_ptr = getgrnam(name);
  __softboundcets_store_return_metadata(ret_ptr, (char *)ret_ptr + 1024 * 1024,
                                        1, __softboundcets_global_lock);

  return ret_ptr;
}

__RT_VISIBILITY
int softboundcets_rpmatch(const char *response) { return rpmatch(response); }

__RT_VISIBILITY
int softboundcets_regcomp(regex_t *preg, const char *regex, int cflags) {
  return regcomp(preg, regex, cflags);
}

__RT_VISIBILITY
size_t softboundcets_regerror(int errcode, const regex_t *preg, char *errbuf,
                              size_t errbuf_size) {

  return regerror(errcode, preg, errbuf, errbuf_size);
}

__RT_VISIBILITY
int softboundcets_regexec(const regex_t *preg, const char *string,
                          size_t nmatch, regmatch_t pmatch[], int eflags) {
  return regexec(preg, string, nmatch, pmatch, eflags);
}

#ifdef HAVE_ICONV_H
__RT_VISIBILITY
size_t softboundcets_iconv(iconv_t cd, char **inbuf, size_t *inbytesleft,
                           char **outbuf, size_t *outbytesleft) {

  return iconv(cd, inbuf, inbytesleft, outbuf, outbytesleft);
}

__RT_VISIBILITY
iconv_t softboundcets_iconv_open(const char *tocode, const char *fromcode) {

  return iconv_open(tocode, fromcode);
}
#endif

__RT_VISIBILITY
struct passwd *softboundcets_getpwnam(const char *name) {
  struct passwd *ret_ptr = getpwnam(name);
  __softboundcets_store_return_metadata(ret_ptr, (char *)ret_ptr + 1024 * 1024,
                                        1, __softboundcets_global_lock);

  return ret_ptr;
}

__RT_VISIBILITY struct passwd *softboundcets_getpwuid(uid_t uid) {
  struct passwd *ret_ptr = getpwuid(uid);

  __softboundcets_store_return_metadata(ret_ptr, (char *)ret_ptr + 1024 * 1024,
                                        1, __softboundcets_global_lock);

  return ret_ptr;
}

__RT_VISIBILITY struct group *softboundcets_getgrgid(gid_t gid) {

  struct group *ret_ptr = getgrgid(gid);
  __softboundcets_store_return_metadata(ret_ptr, (char *)ret_ptr + 1024 * 1024,
                                        1, __softboundcets_global_lock);

  return ret_ptr;
}

__RT_VISIBILITY FILE *softboundcets_fopen(const char *path, const char *mode) {

  FILE *ret_ptr = fopen(path, mode);
  void *ret_ptr_bound = (char *)ret_ptr + sizeof(FILE);

  __softboundcets_store_return_metadata(ret_ptr, ret_ptr_bound, 1,
                                        __softboundcets_global_lock);
  return ret_ptr;
}

__RT_VISIBILITY FILE *softboundcets_fdopen(int fildes, const char *mode) {

  void *ret_ptr = (void *)fdopen(fildes, mode);
  void *ret_ptr_bound = (char *)ret_ptr + sizeof(FILE);

  __softboundcets_store_return_metadata(ret_ptr, ret_ptr_bound, 1,
                                        __softboundcets_global_lock);
  return (FILE *)ret_ptr;
}

__RT_VISIBILITY int softboundcets_fseek(FILE *stream, long offset, int whence) {

  return fseek(stream, offset, whence);
}

__RT_VISIBILITY int softboundcets_ftruncate(int fd, off_t length) {
  return ftruncate(fd, length);
}

__RT_VISIBILITY FILE *softboundcets_popen(const char *command,
                                          const char *type) {

  FILE *ret_ptr = popen(command, type);
  void *ret_ptr_bound = (char *)ret_ptr + sizeof(FILE);

  __softboundcets_store_return_metadata(ret_ptr, ret_ptr_bound, 1,
                                        __softboundcets_global_lock);
  return ret_ptr;
}

__RT_VISIBILITY int softboundcets_fclose(FILE *fp) { return fclose(fp); }

__RT_VISIBILITY int softboundcets_pclose(FILE *stream) {

  return pclose(stream);
}

__RT_VISIBILITY void softboundcets_rewind(FILE *stream) { rewind(stream); }

__RT_VISIBILITY struct dirent *softboundcets_readdir(DIR *dir) {

  struct dirent *ret_ptr = readdir(dir);
  void *ret_ptr_bound = (char *)ret_ptr + sizeof(struct dirent);

  __softboundcets_store_return_metadata(ret_ptr, ret_ptr_bound, 1,
                                        __softboundcets_global_lock);

  return ret_ptr;
}

__RT_VISIBILITY int softboundcets_creat(const char *pathname, mode_t mode) {

  return creat(pathname, mode);
}

__RT_VISIBILITY int softboundcets_fnmatch(const char *pattern,
                                          const char *string, int flags) {

  return fnmatch(pattern, string, flags);
}

__RT_VISIBILITY DIR *softboundcets_opendir(const char *name) {

  DIR *ret_ptr = opendir(name);

  /* FIX Required, don't know the sizeof(DIR) */
  void *ret_ptr_bound = (char *)ret_ptr + 1024 * 1024;

  __softboundcets_store_return_metadata(ret_ptr, ret_ptr_bound, 1,
                                        __softboundcets_global_lock);

  return ret_ptr;
}

__RT_VISIBILITY int softboundcets_closedir(DIR *dir) { return closedir(dir); }

__RT_VISIBILITY int softboundcets_rename(const char *old_path,
                                         const char *new_path) {

  return rename(old_path, new_path);
}

////////////////////unistd.h wrappers ////////////////////////////////

__RT_VISIBILITY char *softboundcets_getcwd(char *buf, size_t size) {

  if (buf == NULL) {
    printf("This case not handled, requesting memory from system\n");
    __softboundcets_abort();
  }

#if __SOFTBOUNDCETS_SPATIAL || __SOFTBOUNDCETS_SPATIAL_TEMPORAL

  char *base = (char *)__softboundcets_load_base_shadow_stack(1);
  char *bound = (char *)__softboundcets_load_bound_shadow_stack(1);

  if (buf < base || buf + size > bound) {
    __softboundcets_error_printf("[getcwd], overflow in buf in getcwd\n");
    __softboundcets_abort();
  }

#endif

  char *ret_ptr = getcwd(buf, size);

  __softboundcets_propagate_metadata_shadow_stack_from(1, 0);

  return ret_ptr;
}

__RT_VISIBILITY
int softboundcets_readlinkat(int dirfd, const char *pathname, char *buf,
                             size_t bufsiz) {
  return readlinkat(dirfd, pathname, buf, bufsiz);
}

__RT_VISIBILITY
int softboundcets_renameat(int olddirfd, const char *oldpath, int newdirfd,
                           const char *newpath) {
  return renameat(olddirfd, oldpath, newdirfd, newpath);
}

__RT_VISIBILITY
int softboundcets_unlinkat(int dirfd, const char *pathname, int flags) {
  return unlinkat(dirfd, pathname, flags);
}

__RT_VISIBILITY
int softboundcets_symlinkat(const char *oldpath, int newdirfd,
                            const char *newpath) {

  return symlinkat(oldpath, newdirfd, newpath);
}

__RT_VISIBILITY
int softboundcets_mkdirat(int dirfd, const char *pathname, mode_t mode) {

  return mkdirat(dirfd, pathname, mode);
}

__RT_VISIBILITY
int softboundcets_fchownat(int dirfd, const char *pathname, uid_t owner,
                           gid_t group, int flags) {

  return fchownat(dirfd, pathname, owner, group, flags);
}

__RT_VISIBILITY
int softboundcets_chmod(const char *path, mode_t mode) {
  return chmod(path, mode);
}

__RT_VISIBILITY
int softboundcets_openat(int dirfd, const char *pathname, int flags) {
  return openat(dirfd, pathname, flags);
}

__RT_VISIBILITY
int softboundcets_fchmodat(int dirfd, const char *pathname, mode_t mode,
                           int flags) {
  return fchmodat(dirfd, pathname, mode, flags);
}

#if defined(__linux__)

// __RT_VISIBILITY
// int softboundcets___xmknodat(int __ver, int __fd, const char *__path,
//                              __mode_t __mode, __dev_t *__dev) {
//   return __xmknodat(__ver, __fd, __path, __mode, __dev);
// }

__RT_VISIBILITY
int softboundcets_mkfifoat(int dirfd, const char *pathname, mode_t mode) {
  return mkfifoat(dirfd, pathname, mode);
}

#endif

#if 0
__RT_VISIBILITY 
int softboundcets_openat(int dirfd, const char *pathname, int flags, mode_t mode){
  return opennat(dirfd, pathname, flags, mode);
}
#endif

__RT_VISIBILITY int softboundcets_chown(const char *path, uid_t owner,
                                        gid_t group) {
  return chown(path, owner, group);
}

__RT_VISIBILITY int softboundcets_chdir(const char *path) {
  return chdir(path);
}

///////////////////String related wrappers ////////////////////////////

__RT_VISIBILITY int softboundcets_strcmp(const char *s1, const char *s2) {

  return strcmp(s1, s2);
}

__RT_VISIBILITY int softboundcets_strcasecmp(const char *s1, const char *s2) {

  return strcasecmp(s1, s2);
}

__RT_VISIBILITY int softboundcets_strncasecmp(const char *s1, const char *s2,
                                              size_t n) {
  return strncasecmp(s1, s2, n);
}

__RT_VISIBILITY size_t softboundcets_strlen(const char *s) { return strlen(s); }

__RT_VISIBILITY const char *softboundcets_strpbrk(const char *s,
                                                  const char *accept) {

  const char *ret_ptr = strpbrk(s, accept);
  if (ret_ptr != NULL) {

    __softboundcets_propagate_metadata_shadow_stack_from(1, 0);
  } else {

    __softboundcets_store_null_return_metadata();
  }

  return ret_ptr;
}

__RT_VISIBILITY char *softboundcets_gets(char *s) {

  printf("[SBCETS] gets used and should not be used\n");
  __softboundcets_abort();
#if 0
  printf("[Softboundcets][Warning] Should not use gets\n");
  char* ret_ptr = gets(s);
  __softboundcets_propagate_metadata_shadow_stack_from(1, 0);
  return ret_ptr;
#endif
  return NULL;
}

__RT_VISIBILITY char *softboundcets_fgets(char *s, int size, FILE *stream) {

  char *ret_ptr = fgets(s, size, stream);
  __softboundcets_propagate_metadata_shadow_stack_from(1, 0);

  return ret_ptr;
}

__RT_VISIBILITY void softboundcets_perror(const char *s) { perror(s); }

__RT_VISIBILITY size_t softboundcets_strspn(const char *s, const char *accept) {

  return strspn(s, accept);
}

__RT_VISIBILITY size_t softboundcets_strcspn(const char *s,
                                             const char *reject) {

  return strcspn(s, reject);
}

#ifdef _GNU_SOURCE

__RT_VISIBILITY void *softboundcets_mempcpy(void *dest, const void *src,
                                            size_t n) {

  // IMP: need to copy the metadata
  void *ret_ptr = mempcpy(dest, src, n);
  __softboundcets_propagate_metadata_shadow_stack_from(1, 0);
  return ret_ptr;
}

#endif

__RT_VISIBILITY int softboundcets_memcmp(const void *s1, const void *s2,
                                         size_t n) {
  return memcmp(s1, s2, n);
}

#ifdef _GNU_SOURCE

__RT_VISIBILITY const void *softboundcets_memrchr(const void *s, int c,
                                                  size_t n) {
  const void *ret_ptr = memrchr(s, c, n);
  if (ret_ptr != NULL) {
    __softboundcets_propagate_metadata_shadow_stack_from(1, 0);
  } else {
    __softboundcets_store_null_return_metadata();
  }
  return ret_ptr;
}
#endif

__RT_VISIBILITY void softboundcets_rewinddir(DIR *dirp) { rewinddir(dirp); }

__RT_VISIBILITY const void *softboundcets_memchr(const void *s, int c,
                                                 size_t n) {
  const void *ret_ptr = memchr(s, c, n);
  if (ret_ptr != NULL) {
    __softboundcets_propagate_metadata_shadow_stack_from(1, 0);
  } else {
    __softboundcets_store_null_return_metadata();
  }
  return ret_ptr;
}

__RT_VISIBILITY char *softboundcets_rindex(char *s, int c) {

  char *ret_ptr = rindex(s, c);
  __softboundcets_propagate_metadata_shadow_stack_from(1, 0);
  return ret_ptr;
}

__RT_VISIBILITY ssize_t softboundcets___getdelim(char **lineptr, size_t *n,
                                                 int delim, FILE *stream) {

  int metadata_prop = 1;
  if (*lineptr == NULL) {
    metadata_prop = 0;
  }

  ssize_t ret_val = getdelim(lineptr, n, delim, stream);

  /* TODO fix storing of metadata for lineptr*/
  if (metadata_prop) {
    __softboundcets_read_shadow_stack_metadata_store(lineptr, 0);
  } else {
    // no need to store return metadata as no pointer is returned
    __softboundcets_store_return_metadata(*lineptr,
                                          (*lineptr) + strlen(*lineptr), 1,
                                          __softboundcets_global_lock);
  }

  return ret_val;
}

__RT_VISIBILITY unsigned long int
softboundcets_strtoul(const char *nptr, char **endptr, int base) {

  unsigned long temp = strtoul(nptr, endptr, base);
  if (endptr != NULL) {
    __softboundcets_read_shadow_stack_metadata_store(endptr, 0);
  }

  return temp;
}

__RT_VISIBILITY double softboundcets_strtod(const char *nptr, char **endptr) {

  double temp = strtod(nptr, endptr);

  if (endptr != NULL) {
    __softboundcets_read_shadow_stack_metadata_store(endptr, 0);
  }
  return temp;
}

__RT_VISIBILITY long softboundcets_strtol(const char *nptr, char **endptr,
                                          int base) {

  long temp = strtol(nptr, endptr, base);
  if (endptr != NULL) {
    //    __softboundcets_printf("*endptr=%p\n", *endptr);
    __softboundcets_read_shadow_stack_metadata_store(endptr, 0);
  }
  return temp;
}

#ifdef _GNU_SOURCE

__RT_VISIBILITY const char *softboundcets_strchrnul(const char *s, int c) {

  const char *ret_ptr = strchrnul(s, c);
  __softboundcets_propagate_metadata_shadow_stack_from(1, 0);
  return ret_ptr;
}
#endif

__RT_VISIBILITY const char *softboundcets_strchr(const char *s, int c) {

  const char *ret_ptr = strchr(s, c);
  __softboundcets_propagate_metadata_shadow_stack_from(1, 0);
  return ret_ptr;
}

__RT_VISIBILITY const char *softboundcets_strrchr(const char *s, int c) {

  const char *ret_ptr = strrchr(s, c);
  __softboundcets_propagate_metadata_shadow_stack_from(1, 0);
  return ret_ptr;
}

__RT_VISIBILITY char *softboundcets_stpcpy(char *dest, char *src) {

  char *ret_ptr = stpcpy(dest, src);
  __softboundcets_propagate_metadata_shadow_stack_from(1, 0);
  return ret_ptr;
}

__RT_VISIBILITY char *softboundcets_strcpy(char *dest, char *src) {

#if __SOFTBOUNDCETS_SPATIAL || __SOFTBOUNDCETS_SPATIAL_TEMPORAL
  char *dest_base = (char *)__softboundcets_load_base_shadow_stack(1);
  char *dest_bound = (char *)__softboundcets_load_bound_shadow_stack(1);

  char *src_base = (char *)__softboundcets_load_base_shadow_stack(2);
  char *src_bound = (char *)__softboundcets_load_bound_shadow_stack(2);

  /* There will be an out-of-bound read before we trigger an error as
     we currently use strlen. Can either (dest + size) or (src + size)
     overflow?
  */
#ifndef __NOSIM_CHECKS
  size_t size = strlen(src);
  if (dest < dest_base || (dest > dest_bound - size - 1) ||
      (size > (size_t)dest_bound)) {
    printf("[strcpy] overflow in strcpy with dest\n");
    __softboundcets_abort();
  }
  if (src < src_base || (src > src_bound - size - 1) ||
      (size > (size_t)src_bound)) {
    printf("[strcpy] overflow in strcpy with src\n");
    __softboundcets_abort();
  }
#endif
#endif

  char *ret_ptr = strcpy(dest, src);
  __softboundcets_propagate_metadata_shadow_stack_from(1, 0);
  return ret_ptr;
}

/////////////////* TODO *///////////////////////////

__RT_VISIBILITY int softboundcets_atoi(const char *ptr) {

  if (ptr == NULL) {
    __softboundcets_abort();
  }
  return atoi(ptr);
}

__RT_VISIBILITY int softboundcets_puts(char *ptr) { return puts(ptr); }

__RT_VISIBILITY char *softboundcets_strtok(char *str, const char *delim) {

  char *ret_ptr = strtok(str, delim);
  __softboundcets_store_return_metadata((void *)0, (void *)(281474976710656), 1,
                                        __softboundcets_global_lock);
  return ret_ptr;
}

__RT_VISIBILITY void __softboundcets_strdup_handler(void *ret_ptr) {
  sbcets_key_t ptr_key;
  sbcets_lock_t ptr_lock;

  if (ret_ptr == NULL) {
    __softboundcets_store_null_return_metadata();
  } else {
    //    printf("strndup malloced pointer %p\n", ret_ptr);
    __softboundcets_memory_allocation(ret_ptr, &ptr_lock, &ptr_key);
    __softboundcets_store_return_metadata(
        ret_ptr, (void *)((char *)ret_ptr + strlen((char *)ret_ptr) + 1),
        ptr_key, ptr_lock);
  }
}

// strdup, allocates memory from the system using malloc, thus can be freed
__RT_VISIBILITY char *softboundcets_strndup(const char *s, size_t n) {

  /* IMP: strndup just copies the string s */
  char *ret_ptr = strndup(s, n);
  __softboundcets_strdup_handler(ret_ptr);
  return ret_ptr;
}

// strdup, allocates memory from the system using malloc, thus can be freed
__RT_VISIBILITY char *softboundcets_strdup(const char *s) {

  /* IMP: strdup just copies the string s */
  char *ret_ptr = strdup(s);

  __softboundcets_strdup_handler(ret_ptr);
  return ret_ptr;
}

__RT_VISIBILITY char *softboundcets___strdup(const char *s) {

  char *ret_ptr = strdup(s);
  __softboundcets_strdup_handler(ret_ptr);
  return ret_ptr;
}

__RT_VISIBILITY char *softboundcets_strcat(char *dest, char *src) {
  CHECK_STRING_STORE(1, dest);
  CHECK_STRING_LOAD(2, src);

  // + 1 for the null terminator
  // Note: strlen(src) may overrun if we don't define __SOFTBOUNDCETS_CHECK_LOADS
  if (dest + strlen(dest) + strlen(src) + 1 > dest_bound) {
    printf("overflow with strcat, dest = %p, strlen(dest)=%d, "
            "strlen(src)=%d, dest_bound=%p \n",
           dest, strlen(dest), strlen(src), dest_bound);
    __softboundcets_abort();
  }

  char *ret_ptr = strcat(dest, src);
  __softboundcets_propagate_metadata_shadow_stack_from(1, 0);
  return ret_ptr;
}

__RT_VISIBILITY char *softboundcets_strncat(char *dest, char *src,
                                            size_t n) {
  CHECK_STRING_STORE(1, dest);

  size_t src_len = strlen(src);
  size_t min_n_src_len = (n < src_len) ? n : src_len;

  CHECK_PTR_LOAD(2, src, min_n_src_len);


  if (dest + strlen(dest) + min_n_src_len + 1 > dest_bound) {
    printf("overflow with strncat, dest = %p, strlen(dest)=%d, "
            "n=%d, dest_bound=%p \n",
           dest, strlen(dest), n, dest_bound);
    __softboundcets_abort();
  }

  char *ret_ptr = strncat(dest, src, n);
  __softboundcets_propagate_metadata_shadow_stack_from(1, 0);
  
  return ret_ptr;
}

__RT_VISIBILITY char *softboundcets_strncpy(char *dest, char *src, size_t n) {

#if __SOFTBOUNDCETS_SPATIAL || __SOFTBOUNDCETS_SPATIAL_TEMPORAL
  char *dest_base = (char *)__softboundcets_load_base_shadow_stack(1);
  char *dest_bound = (char *)__softboundcets_load_bound_shadow_stack(1);

  char *src_base = (char *)__softboundcets_load_base_shadow_stack(2);
  char *src_bound = (char *)__softboundcets_load_bound_shadow_stack(2);

  /* Can either (dest + n) or (src + n) overflow? */
  if (dest < dest_base || (dest + n > dest_bound)) {
    printf("[strncpy] overflow in strncpy with dest\n");
    __softboundcets_abort();
  }
  if (src < src_base || (src > src_bound - n)) {
    __softboundcets_abort();
  }
#endif

  char *ret_ptr = strncpy(dest, src, n);
  __softboundcets_propagate_metadata_shadow_stack_from(1, 0);
  return ret_ptr;
}

__RT_VISIBILITY const char *softboundcets_strstr(const char *haystack,
                                                 const char *needle) {

  const char *ret_ptr = strstr(haystack, needle);
  if (ret_ptr != NULL) {
    __softboundcets_propagate_metadata_shadow_stack_from(1, 0);
  } else {
    __softboundcets_store_null_return_metadata();
  }
  return ret_ptr;
}

__RT_VISIBILITY sighandler_t softboundcets_signal(int signum,
                                                  sighandler_t handler) {

  sighandler_t ptr = signal(signum, handler);
  __softboundcets_store_return_metadata((void *)ptr, (void *)ptr, 1,
                                        __softboundcets_global_lock);
  return ptr;
}

__RT_VISIBILITY long softboundcets_atol(const char *nptr) { return atol(nptr); }

__RT_VISIBILITY void *softboundcets_realloc(void *ptr, size_t size) {

  __softboundcets_debug_printf("performing relloc, which can cause ptr=%p\n",
                               ptr);
  void *ret_ptr = realloc(ptr, size);
  __softboundcets_allocation_secondary_trie_allocate(ret_ptr);
  size_t ptr_key = 1;
  size_t *ptr_lock = __softboundcets_global_lock;

#if __SOFTBOUNDCETS_TEMPORAL || __SOFTBOUNDCETS_SPATIAL_TEMPORAL
  // if the original pointer is null, we must allocate a new lock
  if (ptr == NULL) {
    __softboundcets_memory_allocation(ret_ptr, &ptr_lock, &ptr_key);
  } else {
    ptr_key = __softboundcets_load_key_shadow_stack(1);
    ptr_lock = __softboundcets_load_lock_shadow_stack(1);
  }
#endif

  __softboundcets_store_return_metadata(ret_ptr, (char *)(ret_ptr) + size,
                                        ptr_key, ptr_lock);
  if (ret_ptr != ptr) {
    __softboundcets_check_remove_from_free_map(ptr_key, ptr);
    __softboundcets_add_to_free_map(ptr_key, ret_ptr);
    __softboundcets_copy_metadata(ret_ptr, ptr, size);
  }

  return ret_ptr;
}

__RT_VISIBILITY void *softboundcets_calloc(size_t nmemb, size_t size) {

  sbcets_key_t ptr_key = 1;
  sbcets_lock_t ptr_lock = NULL;

  void *ret_ptr = calloc(nmemb, size);
  if (ret_ptr != NULL) {

#if __SOFTBOUNDCETS_TEMPORAL || __SOFTBOUNDCETS_SPATIAL_TEMPORAL
    __softboundcets_memory_allocation(ret_ptr, &ptr_lock, &ptr_key);
#endif

    __softboundcets_store_return_metadata(
        ret_ptr, ((char *)(ret_ptr) + (nmemb * size)), ptr_key, ptr_lock);

    if (__SOFTBOUNDCETS_FREE_MAP) {
#if 0
       __softboundcets_debug_printf("calloc ptr=%p, ptr_key=%zx\n", 
                              ret_ptr, ptr_key);
#endif
      //       __softboundcets_add_to_free_map(ptr_key, ret_ptr);
    }
  } else {
    __softboundcets_store_null_return_metadata();
  }
  return ret_ptr;
}

__RT_VISIBILITY void *softboundcets_mmap(void *addr, size_t length, int prot,
                                         int flags, int fd, off_t offset) {

  sbcets_key_t ptr_key = 1;
  sbcets_lock_t ptr_lock = __softboundcets_global_lock;
  char *ret_ptr = (char *)mmap(addr, length, prot, flags, fd, offset);
  if (ret_ptr == (void *)-1) {
    __softboundcets_store_null_return_metadata();
  } else {

    char *ret_bound = ret_ptr + length;
    __softboundcets_store_return_metadata(ret_ptr, ret_bound, ptr_key,
                                          ptr_lock);
  }
  return ret_ptr;
}

__RT_VISIBILITY void *softboundcets_malloc(size_t size) {

  sbcets_key_t ptr_key = 1;
  sbcets_lock_t ptr_lock = NULL;

  char *ret_ptr = (char *)malloc(size);
  if (ret_ptr == NULL) {
    __softboundcets_store_null_return_metadata();
  } else {

#if __SOFTBOUNDCETS_TEMPORAL || __SOFTBOUNDCETS_SPATIAL_TEMPORAL
    __softboundcets_memory_allocation(ret_ptr, &ptr_lock, &ptr_key);
#endif

    char *ret_bound = ret_ptr + size;
    __softboundcets_store_return_metadata(ret_ptr, ret_bound, ptr_key,
                                          ptr_lock);

    if (__SOFTBOUNDCETS_FREE_MAP) {
#if 1
      __softboundcets_debug_printf("malloc ptr=%p, ptr_key=%zx\n", ret_ptr,
                                   ptr_key);
#endif
      /* __softboundcets_add_to_free_map(ptr_key, ret_ptr); */
    }
  }
  return ret_ptr;
}

__RT_VISIBILITY clock_t softboundcets_times(struct tms *buf) {
  return times(buf);
}

__RT_VISIBILITY size_t softboundcets_strftime(char *s, size_t max,
                                              const char *format,
                                              const struct tm *tm) {

  return strftime(s, max, format, tm);
}

__RT_VISIBILITY time_t softboundcets_mktime(struct tm *tm) {
  return mktime(tm);
}

__RT_VISIBILITY long softboundcets_pathconf(char *path, int name) {
  return pathconf(path, name);
}

__RT_VISIBILITY struct tm *softboundcets_localtime(const time_t *timep) {

  struct tm *ret_ptr = localtime(timep);
  __softboundcets_store_return_metadata(ret_ptr,
                                        (char *)ret_ptr + sizeof(struct tm), 1,
                                        __softboundcets_global_lock);
  return ret_ptr;
}

__RT_VISIBILITY time_t softboundcets_time(time_t *t) { return time(t); }

__RT_VISIBILITY void softboundcets_free(void *ptr) {
  /* more checks required to check if it is a malloced address */
  // freeing a null pointer is allowed by the libc
  if (ptr != NULL) {
#if __SOFTBOUNDCETS_SPATIAL || __SOFTBOUNDCETS_SPATIAL_TEMPORAL
    void *base = __softboundcets_load_base_shadow_stack(0);
    if (ptr != base) {
      __softboundcets_log_message(
          LOG_LEVEL_ERROR,
          "[mem_dealloc] invalid deallocation!\npointer = %p, base = %p\n,",
          ptr, base);
      __softboundcets_abort();
    }
#endif
#if __SOFTBOUNDCETS_TEMPORAL || __SOFTBOUNDCETS_SPATIAL_TEMPORAL
    size_t *ptr_lock = __softboundcets_load_lock_shadow_stack(0);
    size_t ptr_key = __softboundcets_load_key_shadow_stack(0);

    __softboundcets_log_message(LOG_LEVEL_INFO,
                                "[free] ptr = %p, lock = %p, key = %zx\n", ptr,
                                ptr_lock, ptr_key);
    __softboundcets_memory_deallocation(ptr_lock, ptr_key);

    if (__SOFTBOUNDCETS_FREE_MAP) {
      __softboundcets_check_remove_from_free_map(ptr_key, ptr);
    }
#endif
  }

  free(ptr);
}

/* ////////////////////Time Related Library Wrappers///////////////////////// */

__RT_VISIBILITY char *softboundcets_ctime(const time_t *timep) {

  char *ret_ptr = ctime(timep);

  if (ret_ptr == NULL) {
    __softboundcets_store_null_return_metadata();
  } else {
    __softboundcets_store_return_metadata(
        ret_ptr, ret_ptr + strlen(ret_ptr) + 1, 1, __softboundcets_global_lock);
  }
  return ret_ptr;
}

__RT_VISIBILITY void softboundcets_setbuf(FILE *stream, char *buf) {
  setbuf(stream, buf);
}

__RT_VISIBILITY char *softboundcets_getenv(const char *name) {

  char *ret_ptr = getenv(name);

  if (ret_ptr != NULL) {
    __softboundcets_store_return_metadata(
        ret_ptr, ret_ptr + strlen(ret_ptr) + 1, 1, __softboundcets_global_lock);
  } else {
    __softboundcets_store_null_return_metadata();
  }

  return ret_ptr;
}

__RT_VISIBILITY int softboundcets_atexit(void_func_ptr function) {
  return atexit(function);
}

#ifdef _GNU_SOURCE
__RT_VISIBILITY char *softboundcets_strerror_r(int errnum, char *buf,
                                               size_t buf_len) {

  char *ret_ptr = strerror_r(errnum, buf, buf_len);
  __softboundcets_store_return_metadata(
      ret_ptr, (void *)((char *)ret_ptr + strlen(ret_ptr) + 1), 1,
      __softboundcets_global_lock);
  return ret_ptr;
}
#endif

__RT_VISIBILITY char *softboundcets_strerror(int errnum) {

  char *ret_ptr = strerror(errnum);
  __softboundcets_store_return_metadata(
      ret_ptr, (void *)((char *)ret_ptr + strlen(ret_ptr) + 1), 1,
      __softboundcets_global_lock);
  return ret_ptr;
}

__RT_VISIBILITY int softboundcets_unlink(const char *pathname) {
  return unlink(pathname);
}

__RT_VISIBILITY int softboundcets_open(const char *pathname, int flags) {
  return open(pathname, flags);
}

__RT_VISIBILITY ssize_t softboundcets_read(int fd, void *buf, size_t count) {

  return read(fd, buf, count);
}

__RT_VISIBILITY ssize_t softboundcets_write(int fd, void *buf, size_t count) {
  return write(fd, buf, count);
}

__RT_VISIBILITY int softboundcets_gettimeofday(struct timeval *tv, void *tz) {
  return gettimeofday(tv, tz);
}

__RT_VISIBILITY int softboundcets_select(int nfds, fd_set *readfds,
                                         fd_set *writefds, fd_set *exceptfds,
                                         struct timeval *timeout) {
  return select(nfds, readfds, writefds, exceptfds, timeout);
}

#if defined(__linux__)

__RT_VISIBILITY char *softboundcets_setlocale(int category,
                                              const char *locale) {

  char *ret_ptr = setlocale(category, locale);
  // when setlocale is called, the ctype array is potentially rewritten and we
  // need to renew the stored metadata
  softboundcets_init_ctype();
  __softboundcets_store_return_metadata(
      ret_ptr, (void *)((char *)ret_ptr + strlen(ret_ptr)), 1,
      __softboundcets_global_lock);
  return ret_ptr;
}

__RT_VISIBILITY char *softboundcets_textdomain(const char *domainname) {

  char *ret_ptr = textdomain(domainname);
  __softboundcets_store_return_metadata(
      ret_ptr, (void *)((char *)ret_ptr + strlen(ret_ptr)), 1,
      __softboundcets_global_lock);

  return ret_ptr;
}

__RT_VISIBILITY char *softboundcets_bindtextdomain(const char *domainname,
                                                   const char *dirname) {

  char *ret_ptr = bindtextdomain(domainname, dirname);
  __softboundcets_store_return_metadata(
      ret_ptr, (void *)((char *)ret_ptr + strlen(ret_ptr)), 1,
      __softboundcets_global_lock);

  return ret_ptr;
}

__RT_VISIBILITY char *softboundcets_gettext(const char *msgid) {

  char *ret_ptr = gettext(msgid);
  __softboundcets_store_return_metadata(
      ret_ptr, (void *)((char *)ret_ptr + strlen(ret_ptr)), 1,
      __softboundcets_global_lock);

  return ret_ptr;
}

__RT_VISIBILITY char *softboundcets_dcngettext(const char *domainname,
                                               const char *msgid,
                                               const char *msgid_plural,
                                               unsigned long int n,
                                               int category) {

  char *ret_ptr = dcngettext(domainname, msgid, msgid_plural, n, category);
  __softboundcets_store_return_metadata(
      ret_ptr, (void *)((char *)ret_ptr + strlen(ret_ptr)), 1,
      __softboundcets_global_lock);

  return ret_ptr;
}

/* IMP: struct hostent may have pointers in the structure being returned,
   we need to store the metadata for all those pointers */
__RT_VISIBILITY
struct hostent *softboundcets_gethostbyname(const char *name) {

  struct hostent *ret_ptr = gethostbyname(name);

  void *ret_bound = ret_ptr + sizeof(struct hostent);
  __softboundcets_store_return_metadata(ret_ptr, ret_bound, 1,
                                        __softboundcets_global_lock);

  return ret_ptr;
}

__RT_VISIBILITY char *softboundcets_dcgettext(const char *domainname,
                                              const char *msgid, int category) {

  char *ret_ptr = dcgettext(domainname, msgid, category);
  __softboundcets_store_return_metadata(
      ret_ptr, (void *)((char *)ret_ptr + strlen(ret_ptr)), 1,
      __softboundcets_global_lock);

  return ret_ptr;
}

#endif

#if defined(__linux__)
__RT_VISIBILITY int *softboundcets___errno_location(void) {
  int *ret_ptr = __errno_location();
  //  printf("ERRNO: ptr is %lx", ptrs->ptr);
  __softboundcets_store_return_metadata(
      ret_ptr, (void *)((char *)ret_ptr + sizeof(int *)), 1,
      __softboundcets_global_lock);

  return ret_ptr;
}

__RT_VISIBILITY unsigned short const **softboundcets___ctype_b_loc(void) {

  unsigned short const **ret_ptr = __ctype_b_loc();

  __softboundcets_store_return_metadata((void *)ret_ptr,
                                        (void *)((char *)ret_ptr + 8), 1,
                                        __softboundcets_global_lock);
  return ret_ptr;
}

__RT_VISIBILITY int const **softboundcets___ctype_toupper_loc(void) {

  int const **ret_ptr = __ctype_toupper_loc();

  __softboundcets_store_return_metadata((void *)ret_ptr,
                                        (void *)((char *)ret_ptr + 8), 1,
                                        __softboundcets_global_lock);
  return ret_ptr;
}

__RT_VISIBILITY int const **softboundcets___ctype_tolower_loc(void) {

  int const **ret_ptr = __ctype_tolower_loc();
  __softboundcets_store_return_metadata((void *)ret_ptr,
                                        (void *)((char *)ret_ptr + 8), 1,
                                        __softboundcets_global_lock);
  return ret_ptr;
}
#endif

/* This is a custom implementation of qsort */

static int
compare_elements_helper(void *base, size_t element_size, int idx1, int idx2,
                        int (*comparer)(const void *, const void *)) {

  char *base_bytes = (char *)base;
  return comparer(&base_bytes[idx1 * element_size],
                  &base_bytes[idx2 * element_size]);
}

#define element_less_than(i, j)                                                \
  (compare_elements_helper(base, element_size, (i), (j), comparer) < 0)

static void exchange_elements_helper(void *base, size_t element_size, int idx1,
                                     int idx2) {

  char *base_bytes = (char *)base;
  size_t i;

  for (i = 0; i < element_size; i++) {
    char temp = base_bytes[idx1 * element_size + i];
    base_bytes[idx1 * element_size + i] = base_bytes[idx2 * element_size + i];
    base_bytes[idx2 * element_size + i] = temp;
  }

  for (i = 0; i < element_size; i += 8) {
    void *base_idx1;
    void *bound_idx1;

    void *base_idx2;
    void *bound_idx2;

    size_t key_idx1 = 1;
    size_t key_idx2 = 1;

    sbcets_lock_t lock_idx1 = NULL;
    sbcets_lock_t lock_idx2 = NULL;

    char *addr_idx1 = &base_bytes[idx1 * element_size + i];
    char *addr_idx2 = &base_bytes[idx2 * element_size + i];

    //    printf("addr_idx1= %p, addr_idx2=%p\n", addr_idx1, addr_idx2);
    __softboundcets_metadata_t *metadata1 = __softboundcets_shadowspace_metadata_ptr(addr_idx1);
    __softboundcets_metadata_t *metadata2 = __softboundcets_shadowspace_metadata_ptr(addr_idx2);

#if __SOFTBOUNDCETS_SPATIAL || __SOFTBOUNDCETS_SPATIAL_TEMPORAL

    base_idx1 = metadata1->base;
    bound_idx1 = metadata1->bound;
    base_idx2 = metadata2->base;
    bound_idx2 = metadata2->bound;

#endif
#if __SOFTBOUNDCETS_TEMPORAL || __SOFTBOUNDCETS_SPATIAL_TEMPORAL

    lock_idx1 = metadata1->lock;
    key_idx1 = metadata1->key;
    lock_idx2 = metadata2->lock;
    key_idx2 = metadata2->key;
    
#endif
    __softboundcets_metadata_store(addr_idx1, base_idx2, bound_idx2, key_idx2,
                                   lock_idx2);
    __softboundcets_metadata_store(addr_idx2, base_idx1, bound_idx1, key_idx1,
                                   lock_idx1);

  }
}

#define exchange_elements(i, j)                                                \
  (exchange_elements_helper(base, element_size, (i), (j)))

#define MIN_QSORT_LIST_SIZE 32

__WEAK__
void my_qsort(void *base, size_t num_elements, size_t element_size,
              int (*comparer)(const void *, const void *)) {

  size_t i;

  for (i = 0; i < num_elements; i++) {
    int j;
    for (j = i - 1; j >= 0; j--) {
      if (element_less_than(j, j + 1))
        break;
      exchange_elements(j, j + 1);
    }
  }
  /* may be implement qsort here */
}

__RT_VISIBILITY void softboundcets_qsort(void *base, size_t nmemb, size_t size,
                                         int (*compar)(const void *,
                                                       const void *)) {

  my_qsort(base, nmemb, size, compar);
}

#if defined(__linux__)

__RT_VISIBILITY
void softboundcets__obstack_newchunk(struct obstack *obj, int b) {

  _obstack_newchunk(obj, b);
}

__RT_VISIBILITY
int softboundcets__obstack_begin(struct obstack *obj, int a, int b,
                                 void *(foo)(long), void(bar)(void *)) {
  return _obstack_begin(obj, a, b, foo, bar);
}

__RT_VISIBILITY
void softboundcets_obstack_free(struct obstack *obj, void *object) {
  obstack_free(obj, object);
}

__RT_VISIBILITY
char *softboundcets_nl_langinfo(nl_item item) {

  char *ret_ptr = nl_langinfo(item);

  __softboundcets_store_return_metadata(ret_ptr, ret_ptr + 1024 * 1024, 1,
                                        __softboundcets_global_lock);

  return ret_ptr;
}

__RT_VISIBILITY
int softboundcets_clock_gettime(clockid_t clk_id, struct timespec *tp) {
  return clock_gettime(clk_id, tp);
}

#endif

#if 0

int softboundcets__obstack_memory_used(struct obstack *h){
  return _obstack_memory_used(h);
}

#endif

// TODO: Move to the correct file section (wchar.h)

__RT_VISIBILITY
int softboundcets_wprintf(wchar_t *fmt, ...) {
  CHECK_PTR_ALIVE_LOAD(0, fmt);
  LOAD_PTR_BOUNDS(0, fmt);

#if __SOFTBOUNDCETS_CHECK_LOADS
  if (!wmemchr(fmt, L'\0', (char*)fmt_bound - (char*)fmt)) {
    __softboundcets_error_printf("In wstring load dereference check: base=%zx, bound=%zx, ptr=%zx",
      fmt_base, fmt_bound, fmt);
    __softboundcets_abort();
  }
#endif
  
  va_list va;
  va_start(va, fmt);
  int result= vwprintf(fmt, va);
  va_end(va);

  return result;
}

// Functions from string.h

__RT_VISIBILITY
void *softboundcets___mempcpy(void *dest, void *src, size_t n) {
  CHECK_PTR_STORE(1, dest, n);
  CHECK_PTR_LOAD(2, src, n);
  __softboundcets_propagate_metadata_shadow_stack_from(1, 0);
  __softboundcets_copy_metadata(dest, src, n & ~7);

  return __mempcpy(dest, src, n);
}

__RT_VISIBILITY
char *softboundcets___stpcpy(char *dest, char *src) {
  CHECK_STRING_STORE(1, dest);
  CHECK_STRING_LOAD(2, src);
  __softboundcets_propagate_metadata_shadow_stack_from(1, 0);

  return __stpcpy(dest, src);
}

__RT_VISIBILITY
char *softboundcets___stpncpy(char *dest, char *src, size_t n) {
  CHECK_PTR_STORE(1, dest, n);
  CHECK_PTR_LOAD(2, src, n);
  __softboundcets_propagate_metadata_shadow_stack_from(1, 0);

  return __stpncpy(dest, src, n);
}

__RT_VISIBILITY
char *softboundcets_basename(char *filename) {
  CHECK_STRING_LOAD_NULLABLE(1, filename);

  char *result = basename(filename);

  if (filename != nullptr) {
    // The return value is part of the (modified) filename parameter => copy the metadata over.
    // We need to check this since the null pointer may not have all the metadata we want.
    __softboundcets_propagate_metadata_shadow_stack_from(1, 0);
  } else {
    // strlen here is safe as the static result strings are always null terminated
    __softboundcets_store_return_metadata(result, result + strlen(result) + 1, 1, __softboundcets_global_lock);
  }

  return result;
}

__RT_VISIBILITY
void softboundcets_explicit_bzero(void *buf, size_t n) {
  CHECK_PTR_STORE(0, buf, n);

  explicit_bzero(buf, n);
}

// NOTE: We are treating this function as a string copy function, so we are not copying metadata
__RT_VISIBILITY
void *softboundcets_memccpy(void *dest, void *src, int c, size_t n) {
  CHECK_PTR_STORE(1, dest, n);
  CHECK_PTR_LOAD(2, src, n);

  void *result = memccpy(dest, src, c, n);

  if (result != nullptr) {
    __softboundcets_propagate_metadata_shadow_stack_from(1, 0);
  } else {
    __softboundcets_store_null_return_metadata();
  }

  return result;
}

__RT_VISIBILITY
void *softboundcets_memfrob(void *buf, size_t n) {
  CHECK_PTR_LOAD(1, buf, n);
  __softboundcets_propagate_metadata_shadow_stack_from(1, 0);
  return memfrob(buf, n);
}

__RT_VISIBILITY
void *softboundcets_memmem(void *haystack, size_t haystack_len, void *needle, size_t needle_len) {
  CHECK_PTR_LOAD(1, haystack, haystack_len);
  CHECK_PTR_LOAD(2, needle, needle_len);

  void *result = memmem(haystack, haystack_len, needle, needle_len);

  if (result != nullptr) {
    __softboundcets_propagate_metadata_shadow_stack_from(1, 0);
  } else {
    __softboundcets_store_null_return_metadata();
  }

  return result;
}

__RT_VISIBILITY
void *softboundcets_memmove(void *dest, void *src, size_t n) {
  CHECK_PTR_STORE(1, dest, n);
  CHECK_PTR_LOAD(2, src, n);
  __softboundcets_propagate_metadata_shadow_stack_from(1, 0);
  __softboundcets_copy_metadata(dest, src, n & ~7);
  return memmove(dest, src, n);
}

__RT_VISIBILITY
void *softboundcets_memset(void *buf, int c, size_t n) {
  CHECK_PTR_STORE(1, buf, n);
  __softboundcets_propagate_metadata_shadow_stack_from(1, 0);
  return memset(buf, c, n);
}

__RT_VISIBILITY
void *softboundcets_rawmemchr(void *buf, int c) {
  // Note that the point of this function is that it is memchr without the bounds check.
  // This wrapper essentially makes the function useless, so we just use regular memchr.
  LOAD_PTR_BOUNDS(1, buf);
  CHECK_PTR_ALIVE_LOAD(1, buf);

  void *result = memchr(buf, c, (char*)buf_bound - (char*)buf);
  if (result != nullptr) {
    __softboundcets_propagate_metadata_shadow_stack_from(1, 0);
  } else {
    __softboundcets_error_printf("Out of bounds read in rawmemchr, base=%zx, bound=%zx, ptr=%zx, c=%u",
      buf_base, buf_bound, buf, c);
    __softboundcets_abort();
  }
  return result;
}

/*
The following functions should exist, but are not defined in the header file.

__RT_VISIBILITY
char *softboundcets_sigabbrev_np(int sig) {
  char *result = sigabbrev_np(sig);
  if (result) {
    __softboundcets_store_return_metadata(result, result + strlen(result) + 1, 1, __softboundcets_global_lock);
  } else {
    __softboundcets_store_null_return_metadata();
  }
  return result;
}

__RT_VISIBILITY
char *softboundcets_sigdescr_np(int sig) {
  char *result = sigdescr_np(sig);
  if (result) {
    __softboundcets_store_return_metadata(result, result + strlen(result) + 1, 1, __softboundcets_global_lock);
  } else {
    __softboundcets_store_null_return_metadata();
  }
  return result;
}
*/

__RT_VISIBILITY
char *softboundcets_stpncpy(char *dest, char *src, size_t n) {
  CHECK_PTR_STORE(1, dest, n);
  CHECK_PTR_LOAD(2, src, n);
  __softboundcets_propagate_metadata_shadow_stack_from(1, 0);
  return stpncpy(dest, src, n);
}

__RT_VISIBILITY
char *softboundcets_strcasestr(char *haystack, char *needle) {
  CHECK_STRING_LOAD(1, haystack);
  CHECK_STRING_LOAD(2, needle);

  char *result = strcasestr(haystack, needle);

  if (result != nullptr) {
    __softboundcets_propagate_metadata_shadow_stack_from(1, 0);
  } else {
    __softboundcets_store_null_return_metadata();
  }
  return result;
}

__RT_VISIBILITY
int softboundcets_strcoll(char *s1, char *s2) {
  CHECK_STRING_BOUNDS_LOAD(0, s1);
  CHECK_STRING_BOUNDS_LOAD(1, s2);
  return strcoll(s1, s2);
}

__RT_VISIBILITY
int softboundcets_strcoll_l(char *s1, char *s2, locale_t locale) {
  CHECK_STRING_BOUNDS_LOAD(0, s1);
  CHECK_STRING_BOUNDS_LOAD(1, s2);
  return strcoll_l(s1, s2, locale);
}

__RT_VISIBILITY
char *softboundcets_strerror_l(int errnum, locale_t locale) {
  char *result = strerror_l(errnum, locale);
  // This is save as strerror_l returns a valid string
  __softboundcets_store_return_metadata(result, result + strlen(result) + 1, 1, __softboundcets_global_lock);
  return result;
}

/*
__RT_VISIBILITY
char *softboundcets_strerrordesc_np(int errnum) {
  char *result = strerrordesc_np(errnum);
  if (result) {
    __softboundcets_store_return_metadata(result, result + strlen(result) + 1, 1, __softboundcets_global_lock);
  } else {
    __softboundcets_store_null_return_metadata();
  }
  return result;
}

__RT_VISIBILITY
char *softboundcets_strerrorname_np(int errnum) {
  char *result = strerrorname_np(errnum);
  if (result) {
    __softboundcets_store_return_metadata(result, result + strlen(result) + 1, 1, __softboundcets_global_lock);
  } else {
    __softboundcets_store_null_return_metadata();
  }
  return result;
}
*/

__RT_VISIBILITY
char *softboundcets_strfry(char *str) {
  CHECK_STRING_LOAD(1, str);
  char *result = strfry(str);
  __softboundcets_propagate_metadata_shadow_stack_from(1, 0);
  return result;
}

/*
__RT_VISIBILITY
size_t softboundcets_strlcat(char *dest, char *src, size_t n) {
  CHECK_PTR_STORE(1, dest, n);
  CHECK_PTR_LOAD(2, src, n);
  return strlcat(dest, src, n);
}
*/

__RT_VISIBILITY
size_t softboundcets_strnlen(char *str, size_t n) {
  CHECK_PTR_LOAD(0, str, n);
  return strnlen(str, n);
}

__RT_VISIBILITY
char *softboundcets_strsep(char **segment, char *delim) {
  CHECK_PTR_STORE(1, segment, sizeof(char*));
  CHECK_STRING_LOAD(2, delim);

  if(*segment != nullptr) {
    // Also check if the string pointed to by segment is valid
    sbcets_base_t str_base = __softboundcets_metadata_load_base(*segment);
    sbcets_bound_t str_bound = __softboundcets_metadata_load_bound(*segment);
    sbcets_key_t str_key = __softboundcets_metadata_load_key(*segment);
    sbcets_lock_t str_lock = __softboundcets_metadata_load_lock(*segment);
    __softboundcets_temporal_store_dereference_check(str_lock, str_key);
    // We need *segment to be a valid string -> It must contain a null terminator
    if (!memchr(*segment, '\n', (char*)str_bound - *segment)) {
      __softboundcets_error_printf("In string store dereference check: base=%zx, bound=%zx, ptr=%zx",
        str_base, str_bound, *segment);
      __softboundcets_abort();
    }

    __softboundcets_store_return_metadata(str_base, str_bound, str_key, str_lock);
    return strsep(segment, delim);
  } else {
    __softboundcets_store_null_return_metadata();
    return nullptr;
  }
}

__RT_VISIBILITY
char *softboundcets_strsignal(int sig) {
  char *result = strsignal(sig);
  __softboundcets_store_return_metadata(result, result + strlen(result) + 1, 1, __softboundcets_global_lock);
  return result;
}

__RT_VISIBILITY
char *softboundcets_strtok_r(char *s, char *delim, char **save_ptr) {
  // This function has two "modes"
  // If s is not null, it reads from s and modifies *save_ptr with the return pointing into s
  // else it reads from and modifies *save_ptr with the retur pointing there as well
  // Note that this behaviour may change with future releases of glibc
  CHECK_STRING_LOAD_NULLABLE(1, s);
  CHECK_STRING_LOAD(2, delim);
  CHECK_PTR_LOAD(3, save_ptr, sizeof(char*));

  if(s != nullptr) {
    // We already checked all pointers
    char *result = strtok_r(s, delim, save_ptr);

    // Store the metadata for *save_ptr
    __softboundcets_metadata_store(*save_ptr, s_base, s_bound, s_key, s_lock);
    if (result) {
      __softboundcets_propagate_metadata_shadow_stack_from(1, 0);
    } else {
      __softboundcets_store_null_return_metadata();
    }
    return result;
  } else {
    // We need to check the metadata of *save_ptr manually
    sbcets_base_t saved_ptr_base = __softboundcets_metadata_load_base(*save_ptr);
    sbcets_bound_t saved_ptr_bound = __softboundcets_metadata_load_bound(*save_ptr);
    sbcets_lock_t saved_ptr_lock = __softboundcets_metadata_load_lock(*save_ptr);
    sbcets_key_t saved_ptr_key = __softboundcets_metadata_load_key(*save_ptr);

    __softboundcets_temporal_store_dereference_check(saved_ptr_lock, saved_ptr_key);
    if (!memchr(*save_ptr, '\n', (char*)saved_ptr_bound - *save_ptr)) {
      __softboundcets_error_printf("In string store dereference check: base=%zx, bound=%zx, ptr=%zx",
        saved_ptr_base, saved_ptr_bound, *save_ptr);
      __softboundcets_abort();
    }

    char *result = strtok_r(s, delim, save_ptr);
    if (result) {
      // The returned pointer is in *save_ptr's bounds
      __softboundcets_store_return_metadata(saved_ptr_base, saved_ptr_bound, saved_ptr_key, saved_ptr_lock);
    } else {
      __softboundcets_store_null_return_metadata();
    }
    return result;
  }
}

__RT_VISIBILITY
int softboundcets_strverscmp(char *s1, char *s2) {
  CHECK_STRING_LOAD(0, s1);
  CHECK_STRING_LOAD(1, s2);
  return strverscmp(s1, s2);
}

__RT_VISIBILITY
size_t softboundcets_strxfrm(char *dest, char *src, size_t n) {
  CHECK_PTR_STORE(0, dest, n);
  CHECK_PTR_LOAD(1, src, n);
  return strxfrm(dest, src, n);
}

__RT_VISIBILITY
size_t softboundcets_strxfrm_l(char *dest, const char *src, size_t n, locale_t locale) {
  CHECK_PTR_STORE(0, dest, n);
  CHECK_PTR_LOAD(1, src, n);
  return strxfrm_l(dest, src, n, locale);
}

// Wrappers for strings.h

__RT_VISIBILITY
int softboundcets_bcmp(void *s1, void *s2, size_t n) {
  CHECK_PTR_LOAD(0, s1, n);
  CHECK_PTR_LOAD(1, s2, n);
  return bcmp(s1, s2, n);
}

__RT_VISIBILITY
void softboundcets_bcopy(void *src, void *dest, size_t n) {
  CHECK_PTR_LOAD(0, src, n);
  CHECK_PTR_STORE(1, dest, n);
  __softboundcets_copy_metadata(dest, src, n & ~7);
  bcopy(src, dest, n);
}

__RT_VISIBILITY
void softboundcets_bzero(void *s, size_t n) {
  CHECK_PTR_STORE(1, s, n);
  bzero(s, n);
}

__RT_VISIBILITY
char *softboundcets_index(char *s, int c) {
  CHECK_STRING_LOAD(1, s);
  char *result = index(s, c);
  if (result) {
    __softboundcets_propagate_metadata_shadow_stack_from(1, 0);
  } else {
    __softboundcets_store_null_return_metadata();
  }
  return result;
}

__RT_VISIBILITY
int softboundcets_strcasecmp_l(char *s1, char *s2, locale_t l) {
  CHECK_STRING_LOAD(0, s1);
  CHECK_STRING_LOAD(1, s2);
  return strcasecmp_l(s1, s2, l);
}

__RT_VISIBILITY
int softboundcets_strncasecmp_l(char *s1, char *s2, size_t n, locale_t l) {
  CHECK_PTR_LOAD(0, s1, n);
  CHECK_PTR_LOAD(1, s2, n);
  return strncasecmp_l(s1, s2, n, l);
}

// Wrappers for stdio.h

__RT_VISIBILITY
int softboundcets___asprintf(char **ptr, char *fmt, ...) {
  CHECK_PTR_STORE(0, ptr, sizeof(char*));
  CHECK_STRING_LOAD(1, fmt);
  // Cannot use varargs directly, so use vasprintf
  // Since __asprintf and asprintf point to the same implementation, this should be fine
  va_list varargs;
  va_start(varargs, fmt);
  int result = vasprintf(ptr, fmt, varargs);
  va_end(varargs);

  if (result != -1) {
    sbcets_key_t key = 0;
    sbcets_lock_t lock = nullptr;
    __softboundcets_memory_allocation(*ptr, &lock, &key);
    // We have sucessfully allocated, result contains the size of the buffer - 1 for \0
    __softboundcets_metadata_store(*ptr, *ptr, *ptr + result + 1, key, lock);
  }

  return result;
}

__RT_VISIBILITY
int softboundcets___overflow(FILE *file, int i) {
  // Note: While we should probably never dereference FILE* directly, some libc macros may, so set
  // the bounds accordingly.
  CHECK_PTR_LOAD(0, file, sizeof(FILE));
  return __overflow(file, i);
}

__RT_VISIBILITY
int softboundcets___uflow(FILE *file) {
  CHECK_PTR_LOAD(0, file, sizeof(FILE));
  return __uflow(file);
}

__RT_VISIBILITY
int softboundcets_asprintf(char **ptr, char *fmt, ...) {
  CHECK_PTR_STORE(0, ptr, sizeof(char*));
  CHECK_STRING_LOAD(1, fmt);
  
  va_list varargs;
  va_start(varargs, fmt);
  int result = vasprintf(ptr, fmt, varargs);
  va_end(varargs);

  if (result != -1) {
    sbcets_key_t key = 0;
    sbcets_lock_t lock = nullptr;
    __softboundcets_memory_allocation(*ptr, &lock, &key);
    // We have sucessfully allocated, result contains the size of the buffer - 1 for \0
    __softboundcets_metadata_store(*ptr, *ptr, *ptr + result + 1, key, lock);
  }

  return result;
}

__RT_VISIBILITY
void softboundcets_clearerr(FILE *file) {
  CHECK_PTR_LOAD(0, file, sizeof(FILE));
  clearerr(file);
}

__RT_VISIBILITY
void softboundcets_clearerr_unlocked(FILE *file) {
  CHECK_PTR_LOAD(0, file, sizeof(FILE));
  clearerr(file);
}

__RT_VISIBILITY
char *softboundcets_ctermid(char *s) {
  // L_ctermid is the maximum size retuned by the function.
  CHECK_PTR_LOAD_NULLABLE(1, s, L_ctermid);

  char *result = ctermid(s);
  
  if (s != nullptr) {
    __softboundcets_propagate_metadata_shadow_stack_from(1, 0);
  } else {
    __softboundcets_store_return_metadata(result, result + L_ctermid, 1, __softboundcets_global_lock);
  }
  return result;
}

__RT_VISIBILITY
char *softboundcets_cuserid(char *s) {
  CHECK_PTR_STORE_NULLABLE(1, s, L_cuserid);

  char *result = cuserid(s);

  if (s != nullptr) {
    __softboundcets_propagate_metadata_shadow_stack_from(1, 0);
  } else {
    __softboundcets_store_return_metadata(result, result + L_cuserid, 1, __softboundcets_global_lock);
  }
  return result;
}

__RT_VISIBILITY
int softboundcets_dprintf(int fd, char *fmt, ...) {
  CHECK_STRING_LOAD(0, fmt);

  va_list varargs;
  va_start(varargs, fmt);
  int result = vdprintf(fd, fmt, varargs);
  va_end(varargs);

  return result;
}

__RT_VISIBILITY
int softboundcets_feof_unlocked(FILE *file) {
  CHECK_PTR_LOAD(0, file, sizeof(FILE));
  return feof_unlocked(file);
}

__RT_VISIBILITY
int softboundcets_ferror_unlocked(FILE *file) {
  CHECK_PTR_LOAD(0, file, sizeof(FILE));
  return ferror_unlocked(file);
}

__RT_VISIBILITY
int softboundcets_fflush_unlocked(FILE *file) {
  CHECK_PTR_LOAD(0, file, sizeof(FILE));
  return fflush_unlocked(file);
}

__RT_VISIBILITY
int softboundcets_fgetc_unlocked(FILE *file) {
  CHECK_PTR_LOAD(0, file, sizeof(FILE))
  return fgetc_unlocked(file);
}

__RT_VISIBILITY
int softboundcets_fgetpos(FILE *file, fpos_t *pos) {
  CHECK_PTR_LOAD(0, file, sizeof(FILE));
  CHECK_PTR_STORE(1, pos, sizeof(fpos_t));
  return fgetpos(file, pos);
}

__RT_VISIBILITY
int softboundcets_fgetpos64(FILE *file, fpos64_t *pos) {
  CHECK_PTR_LOAD(0, file, sizeof(FILE));
  CHECK_PTR_STORE(1, pos, sizeof(fpos64_t));
  return fgetpos64(file, pos);
}

__RT_VISIBILITY
char *softboundcets_fgets_unlockd(char *s, int n, FILE *file) {
  CHECK_PTR_STORE(1, s, n);
  CHECK_PTR_LOAD(2, file, sizeof(FILE));
  char *result = fgets_unlocked(s, n, file);
  if (result) {
    __softboundcets_propagate_metadata_shadow_stack_from(1, 0);
  } else {
    __softboundcets_store_null_return_metadata();
  }
  return result;
}

__RT_VISIBILITY
int softboundcets_fileno_unlocked(FILE *file) {
  CHECK_PTR_LOAD(0, file, sizeof(FILE));
  return fileno_unlocked(file);
}

__RT_VISIBILITY
void softboundcets_flockfile(FILE *file) {
  CHECK_PTR_LOAD(0, file, sizeof(FILE));
  flockfile(file);
}

__RT_VISIBILITY
FILE *softboundcets_fmemopen(void *buf, size_t n, char *mode) {
  CHECK_PTR_STORE_NULLABLE(1, buf, n);
  CHECK_STRING_LOAD(2, mode);

  FILE *result = fmemopen(buf, n, mode);
  if (result) {
    sbcets_lock_t lock;
    sbcets_key_t key;
    __softboundcets_memory_allocation(result, &lock, &key);
    __softboundcets_store_return_metadata(result, result + sizeof(FILE), key, lock);
  } else {
    __softboundcets_store_null_return_metadata();
  }
  return result;
}

__RT_VISIBILITY
FILE *softboundcets_fopen64(char *filename, char *mode) {
  CHECK_STRING_LOAD(1, filename);
  CHECK_STRING_LOAD(2, mode);

  FILE *result = fopen64(filename, mode);
  if (result) {
    sbcets_lock_t lock;
    sbcets_key_t key;
    __softboundcets_memory_allocation(result, &lock, &key);
    __softboundcets_store_return_metadata(result, result + sizeof(FILE), key, lock);
  } else {
    __softboundcets_store_null_return_metadata();
  }
  return result;
}

// TODO: The inner pointers of cookie_io_functions_t are probably not checked, so add macros for
// situations like this as well?
__RT_VISIBILITY
FILE *softboundcets_fopencookie(void *magic_cookie, char *modes, cookie_io_functions_t io_functions) {
  // TODO: What to do with dynamically sized data types? I suppose they are checked in the callback
  // functions that this value is eventually passed to since the io_functions are user-defined.
  CHECK_PTR_LOAD(1, magic_cookie, 0);
  CHECK_STRING_LOAD(2, modes);
  
  FILE *result = fopencookie(magic_cookie, modes, io_functions);
  if (result) {
    sbcets_lock_t lock;
    sbcets_key_t key;
    __softboundcets_memory_allocation(result, &lock, &key);
    __softboundcets_store_return_metadata(result, result + sizeof(FILE), key, lock);
  } else {
    __softboundcets_store_null_return_metadata();
  }
  return result;
}

__RT_VISIBILITY
int softboundcets_fprintf(FILE *file, char *fmt, ...) {
  CHECK_PTR_LOAD(0, file, sizeof(FILE));
  CHECK_STRING_LOAD(1, fmt);

  va_list va;
  va_start(va, fmt);
  int result = vfprintf(file, fmt, va);
  va_end(va);

  return result;
}

__RT_VISIBILITY
int softboundcets_fputc_unlocked(int c, FILE *file) {
  CHECK_PTR_LOAD(0, file, sizeof(FILE));

  return fputc_unlocked(c, file);
}

__RT_VISIBILITY
int softboundcets_fputs_unlocked(char *s, FILE *file) {
  CHECK_STRING_LOAD(0, s);
  CHECK_PTR_LOAD(1, file, sizeof(FILE));

  return fputs_unlocked(s, file);
}

__RT_VISIBILITY
FILE *softboundcets_freopen(char *filename, char *mode, FILE *file) {
  CHECK_STRING_LOAD_NULLABLE(1, filename);
  CHECK_STRING_LOAD(2, mode);
  // TODO: The freopen function accepts null, but returns an error if it does.
  // Is that something we want to avoid?
  CHECK_PTR_LOAD_NULLABLE(3, file, sizeof(FILE));
  
  // TODO: I'm somewhat confused as to how this function works.
  // It seems like the old file is always closed in the glibc implementation, but the man page
  // seems to disagree
  // Just treat this as a deallocation and new allocation for now, if the function succeeds
  FILE *result = freopen(filename, mode, file);
  if (result) {
    sbcets_lock_t lock;
    sbcets_key_t key;
    __softboundcets_memory_allocation(result, &lock, &key);
    __softboundcets_store_return_metadata(result, result + sizeof(FILE), key, lock);
    __softboundcets_memory_deallocation(file_lock, file_key);
  } else {
    __softboundcets_store_null_return_metadata();
  }
  return result;
}

__RT_VISIBILITY
FILE *softboundcets_freopen64(char *filename, char *mode, FILE *file) {
  CHECK_STRING_LOAD_NULLABLE(1, filename);
  CHECK_STRING_LOAD(2, mode);
  CHECK_PTR_LOAD_NULLABLE(3, file, sizeof(FILE));

  FILE *result = freopen64(filename, mode, file);
  if (result) {
    sbcets_lock_t lock;
    sbcets_key_t key;
    __softboundcets_memory_allocation(result, &lock, &key);
    __softboundcets_store_return_metadata(result, result + sizeof(FILE), key, lock);
    __softboundcets_memory_deallocation(file_lock, file_key);
  } else {
    __softboundcets_store_null_return_metadata();
  }
  return result;
}

__RT_VISIBILITY
int softboundcets_fscanf(FILE *file, char *format, ...) {
  CHECK_PTR_LOAD(0, file, sizeof(FILE));
  CHECK_STRING_LOAD(1, format);

  va_list va;
  va_start(va, format);
  int result = vfscanf(file, format, va);
  va_end(va);

  return result;
}

__RT_VISIBILITY
int softboundcets_fseeko64(FILE *file, off64_t off, int whence) {
  CHECK_PTR_LOAD(0, file, sizeof(FILE));
  return fseeko64(file, off, whence);
}

__RT_VISIBILITY
int softboundcets_fsetpos(FILE *file, fpos_t *pos) {
  CHECK_PTR_LOAD(0, file, sizeof(FILE));
  CHECK_PTR_LOAD(1, pos, sizeof(fpos_t));
  return fsetpos(file, pos);
}

__RT_VISIBILITY
int softboundcets_fsetpos64(FILE *file, fpos64_t *pos) {
  CHECK_PTR_LOAD(0, file, sizeof(FILE));
  CHECK_PTR_LOAD(1, pos, sizeof(fpos_t));
  return fsetpos64(file, pos);
}

__RT_VISIBILITY
off_t softboundcets_ftello(FILE *file) {
  CHECK_PTR_LOAD(0, file, sizeof(FILE));
  return ftello(file);
}

__RT_VISIBILITY
off64_t softboundcets_ftello64(FILE *file) {
  CHECK_PTR_LOAD(0, file, sizeof(FILE));
  return ftello64(file);
}

__RT_VISIBILITY
int softboundcets_ftrylockfile(FILE *file) {
  CHECK_PTR_LOAD(0, file, sizeof(FILE));
  return ftrylockfile(file);
}

__RT_VISIBILITY
void softboundcets_funlockfile(FILE *file) {
  CHECK_PTR_LOAD(0, file, sizeof(FILE));
  funlockfile(file);
}

__RT_VISIBILITY
size_t softboundcets_fwrite_unlocked(void *ptr, size_t size, size_t n, FILE *file) {
  // Note: This could technically overflow
  CHECK_PTR_LOAD(0, ptr, size * n);
  CHECK_PTR_LOAD(1, file, sizeof(FILE));
  return fwrite_unlocked(ptr, size, n, file);
}

__RT_VISIBILITY
int softboundcets_getc(FILE *file) {
  CHECK_PTR_LOAD(0, file, sizeof(FILE));
  return getc(file);
}

__RT_VISIBILITY
int softboundcets_getc_unlocked(FILE *file) {
  CHECK_PTR_LOAD(0, file, sizeof(FILE));
  return getc_unlocked(file);
}


__RT_VISIBILITY
ssize_t softboundcets_getdelim(char **lineptr, size_t *n, int delim, FILE *file) {
  CHECK_PTR_STORE(0, lineptr, sizeof(char*));
  CHECK_PTR_STORE(1, n, sizeof(size_t));
  CHECK_PTR_LOAD(2, file, sizeof(FILE));

  // Note: *lineptr can be null or malloc'd, but should not be static of from some other allocator
  // that does not work with metadata.
  // Since I don't think that softboundcets can express this, this is not checked.
  if (*lineptr) {
    sbcets_bound_t line_bound = __softboundcets_metadata_load_bound(*lineptr);
    size_t buffer_size = (char*)line_bound - *lineptr;
    if (buffer_size < *n) {
      __softboundcets_error_printf("in getdelim, the buffer size is assumed to be too large: "\
        "actual size: %d, stated size: %d", buffer_size, *n);
    }
  }
  char *prev_line = *lineptr;

  ssize_t result = getdelim(lineptr, n, delim, file);

  // Check if we (re-)allocated and reset metadata if so
  // TODO: Is this correct? Is there any other way to detect reallocation at the same location?
  if (prev_line != *lineptr) {

    sbcets_lock_t line_lock = __softboundcets_metadata_load_lock(prev_line);
    sbcets_key_t line_key = __softboundcets_metadata_load_key(prev_line);
    __softboundcets_memory_deallocation(line_lock, line_key);

    sbcets_lock_t new_line_lock = nullptr;
    sbcets_key_t new_line_key = 0;
    __softboundcets_memory_allocation(*lineptr, &new_line_lock, &new_line_key);
    __softboundcets_metadata_store(*lineptr, *lineptr, *lineptr + *n, new_line_key, new_line_lock);
  }

  return result;
}

__RT_VISIBILITY
ssize_t softboundcets_getline(char **lineptr, size_t *n, FILE *file) {
  CHECK_PTR_STORE(0, lineptr, sizeof(char*));
  CHECK_PTR_STORE(1, n, sizeof(size_t));
  CHECK_PTR_LOAD(2, file, sizeof(FILE));

  // Note: *lineptr can be null or malloc'd, but should not be static of from some other allocator
  // that does not work with metadata.
  // Since I don't think that softboundcets can express this, this is not checked.
  if (*lineptr) {
    sbcets_bound_t line_bound = __softboundcets_metadata_load_bound(*lineptr);
    size_t buffer_size = (char*)line_bound - *lineptr;
    if (buffer_size < *n) {
      __softboundcets_error_printf("in getdelim, the buffer size is assumed to be too large: "\
        "actual size: %d, stated size: %d", buffer_size, *n);
      __softboundcets_abort();
    }
  }
  char *prev_line = *lineptr;

  ssize_t result = getline(lineptr, n, file);

  // Check if we (re-)allocated and reset metadata if so
  if (prev_line != *lineptr) {

    sbcets_lock_t line_lock = __softboundcets_metadata_load_lock(prev_line);
    sbcets_key_t line_key = __softboundcets_metadata_load_key(prev_line);
    __softboundcets_memory_deallocation(line_lock, line_key);

    sbcets_lock_t new_line_lock = nullptr;
    sbcets_key_t new_line_key = 0;
    __softboundcets_memory_allocation(*lineptr, &new_line_lock, &new_line_key);
    __softboundcets_metadata_store(*lineptr, *lineptr, *lineptr + *n, new_line_key, new_line_lock);
  }

  return result;
}

__RT_VISIBILITY
int softboundcets_getw(FILE *file) {
  CHECK_PTR_LOAD(0, file, sizeof(FILE));
  return getw(file);
}

__RT_VISIBILITY
int softboundcets_obstack_printf(struct obstack *obstack, char *fmt, ...) {
  CHECK_PTR_LOAD(0, obstack, sizeof(struct obstack));
  CHECK_STRING_LOAD(1, fmt);

  va_list va;
  va_start(va, fmt);
  int result = obstack_vprintf(obstack, fmt, va);
  va_end(va);
  return result;
}

__RT_VISIBILITY
int softboundcets_obstack_vprintf(struct obstack *obstack, char *fmt, va_list va) {
  CHECK_PTR_LOAD(0, obstack, sizeof(struct obstack));
  CHECK_STRING_LOAD(1, fmt);

  return obstack_vprintf(obstack, fmt, va);
}

__RT_VISIBILITY
FILE *softboundcets_open_memstream(char **buf, size_t *size) {
  CHECK_PTR_STORE(1, buf, sizeof(char*));
  CHECK_PTR_STORE(2, size, sizeof(size_t));

  // Note: The pointer pointed to by *buf grows dynamically and is this reallocated when writing.
  FILE *result = open_memstream(buf, size);

  if (result) {
    sbcets_lock_t result_lock = nullptr;
    sbcets_key_t result_key = 0;
    __softboundcets_memory_allocation(result, &result_lock, &result_key);
    __softboundcets_store_return_metadata(result, result + sizeof(FILE), result_key, result_lock);
  } else {
    __softboundcets_store_null_return_metadata();
  }

  // *buf can be assigned regardless of the functions success
  if (*buf) {
    sbcets_lock_t lock = nullptr;
    sbcets_key_t key = 0;
    __softboundcets_memory_allocation(*buf, &lock, &key);
    // WORKAROUND: Since the pointer can be reallocated by the libc without us knowing, just make
    // this pointer valid erverywhere.
    // I don't think this function is used often enough to merit runtime patching the relevant
    // realloc function.
    __softboundcets_metadata_store(*buf, 0, (void*)281474976710656, key, lock);
  }

  return result;
}

__RT_VISIBILITY
int softboundcets_printf(char *fmt, ...) {
  CHECK_STRING_LOAD(0, fmt);

  va_list args;
  va_start(args,
           fmt); // Initialize va_list with the start of the variable arguments
  size_t ptr_arg_pos = 1;

  int i = 0;
  while (fmt[i] != '\0') {
    if (fmt[i] == '%' && fmt[i + 1] != '%' && fmt[i + 1] != '\0') {
      i++;
      // ignore all flags/width/precision/modifiers
      while(isdigit(fmt[i]) || fmt[i] == '.' || fmt[i] == '#' || fmt[i] == '+' || 
            fmt[i] == '-' || fmt[i] == ' ' || fmt[i] == 'h' || fmt[i] == 'l' || 
            fmt[i] == 'j' || fmt[i] == 'z' || fmt[i] == 't' || fmt[i] == 'L')
        i++;
      switch (fmt[i]) {
        // Integer specifiers
      case 'd':
      case 'i':
      case 'o':
      case 'u':
      case 'x':
      case 'X': {
        int intValue = va_arg(args, int);
        break;
      }
        // Floating-point specifiers
      case 'f':
      case 'F':
      case 'e':
      case 'E':
      case 'g':
      case 'G':
      case 'a':
      case 'A': {
        double floatValue =
            va_arg(args, double); // Note: 'float' is promoted to 'double' when
                                  // passed through '...'
        break;
      }
      case 's': {
        char *stringValue = va_arg(args, char *);
        CHECK_STRING_LOAD(ptr_arg_pos, stringValue);
        ptr_arg_pos++;
        break;
      }
      case 'c': {
        // Note: 'char' is promoted to 'int' when passed through '...'
        int charValue = va_arg(args, int);
        break;
      }
      case 'p': {
        void *val = va_arg(args, void *);
        break;
      }
      // Add more cases as needed
      default:
        printf("Unknown fmt specifier: %%%c\n", fmt[i]);
        break;
      }
    } else if (fmt[i] == '%' && fmt[i + 1] == '%') {
      // Skip "%%" since it's used to print a literal '%'
      i++;
    }
    i++;
  }

  va_end(args);
  va_list va;
  va_start(va, fmt);
  int result = vprintf(fmt, va);
  va_end(va);
  return result;
}

__RT_VISIBILITY
int softboundcets_putc(int c, FILE *file) {
  CHECK_PTR_LOAD(0, file, sizeof(FILE));
  return putc(c, file);
}

__RT_VISIBILITY
int softboundcets_putc_unlocked(int c, FILE *file) {
  CHECK_PTR_LOAD(0, file, sizeof(FILE));
  return putc_unlocked(c, file);
}

__RT_VISIBILITY
int softboundcets_putw(int w, FILE *file) {
  CHECK_PTR_LOAD(0, file, sizeof(FILE));
  return putw(w, file);
}

__RT_VISIBILITY
int softboundcets_renameat2(int oldfd, char *oldpath, int newfd, char *newpath, unsigned int flags) {
  CHECK_STRING_LOAD(0, oldpath);
  CHECK_STRING_LOAD(1, newpath);

  return renameat2(oldfd, oldpath, newfd, newpath, flags);
}

__RT_VISIBILITY
int softboundcets_scanf(char *fmt, ...) {
  CHECK_STRING_LOAD(0, fmt);

  va_list va;
  va_start(va, fmt);
  int result = vscanf(fmt, va);
  va_end(va);
  return result;
}

__RT_VISIBILITY
void softboundcets_setbuffer(FILE *file, char *buf, size_t size) {
  CHECK_PTR_LOAD(0, file, sizeof(FILE));
  CHECK_PTR_STORE_NULLABLE(1, buf, size);

  // Note: the buffer needs to be alive as long as it is bound to file, but we cannot express this
  setbuffer(file, buf, size);
}

__RT_VISIBILITY
void softboundcets_setlinebuf(FILE *file) {
  CHECK_PTR_LOAD(0, file, sizeof(FILE));
  setlinebuf(file);
}

__RT_VISIBILITY
int softboundcets_setvbuf(FILE *file, char *buf, int mode, size_t size) {
  CHECK_PTR_LOAD(0, file, sizeof(FILE));
  CHECK_PTR_STORE_NULLABLE(1, buf, size);

  // Note: the buffer needs to be alive as long as it is bound to file, but we cannot express this
  return setvbuf(file, buf, mode, size);
}

__RT_VISIBILITY
int softboundcets_snprintf(char *buf, size_t n, char *fmt, ...) {
  CHECK_PTR_STORE(0, buf, n);
  CHECK_STRING_LOAD(1, fmt);

  va_list va;
  va_start(va, fmt);
  int result = vsnprintf(buf, n, fmt, va);
  va_end(va);

  return result;
}

__RT_VISIBILITY
int softboundcets_sprintf(char *buf, char *fmt, ...) {
  CHECK_PTR_STORE_NULLABLE(0, buf, 0);
  CHECK_STRING_LOAD(1, fmt);

  // Note: Since we cannot check for the buffer size before calling sprintf, we check after to
  // limit the potential damage
  va_list va;
  va_start(va, fmt);
  int result = vsprintf(buf, fmt, va);
  va_end(va);

  if (buf) {
    size_t bufsize = (size_t)buf_bound - (size_t)buf_base;
    // The trailing null character is not included, so if the result is the same as the buffer size,
    // we have overshot by one.
    if ((size_t)result >= bufsize) {
      __softboundcets_error_printf("sprintf result did not fit in the provided buffer: "\
        "buffer size = %llu, required size = %d", bufsize, result + 1);
      __softboundcets_abort();
    }
  }
  return result;
}

__RT_VISIBILITY
int softboundcets_sscanf(char *buf, char *fmt, ...) {
  CHECK_STRING_LOAD(0, buf);
  CHECK_STRING_LOAD(1, fmt);

  va_list va;
  va_start(va, fmt);
  int result = vsscanf(buf, fmt, va);
  va_end(va);

  return result;
}

__RT_VISIBILITY
char *softboundcets_tempnam(char *dir, char *pfx) {
  CHECK_STRING_LOAD_NULLABLE(1, dir);
  CHECK_STRING_LOAD_NULLABLE(2, pfx);

  char *result = tempnam(dir, pfx);

  if (result) {
    sbcets_lock_t result_lock = nullptr;
    sbcets_key_t result_key = 0;
    __softboundcets_memory_allocation(result, &result_lock, &result_key);
    __softboundcets_store_return_metadata(result, result + strlen(result) + 1, result_key, result_lock);
  } else {
    __softboundcets_store_null_return_metadata();
  }
  return result;
}

__RT_VISIBILITY
FILE *softboundcets_tmpfile64() {
  FILE *result = tmpfile64();
  
  if (result) {
    sbcets_lock_t result_lock = nullptr;
    sbcets_key_t result_key = 0;
    __softboundcets_memory_allocation(result, &result_lock, &result_key);
    __softboundcets_store_return_metadata(result, result + sizeof(FILE), result_key, result_lock);
  } else {
    __softboundcets_store_null_return_metadata();
  }
  return result;
}

__RT_VISIBILITY
char *softboundcets_tmpnam(char *s) {
  CHECK_PTR_STORE_NULLABLE(1, s, L_tmpnam);

  char *result = tmpnam(s);

  if (result) {
    if (s) {
      __softboundcets_propagate_metadata_shadow_stack_from(1, 0);
    } else {
      // Per the man page, this returns a static buffer
      __softboundcets_store_return_metadata(result, result + L_tmpnam, 1, __softboundcets_global_lock);
    }
  } else {
    __softboundcets_store_null_return_metadata();
  }
  return result;
}

__RT_VISIBILITY
char *softboundcets_tmpnam_r(char *s) {
  CHECK_PTR_STORE_NULLABLE(1, s, L_tmpnam);

  char *result = tmpnam_r(s);

  if (result) {
    // This just returns s
    __softboundcets_propagate_metadata_shadow_stack_from(1, 0);
  } else {
    __softboundcets_store_null_return_metadata();
  }
  return result;
}

__RT_VISIBILITY
int softboundcets_vasprintf(char **ptr, char *fmt, va_list va) {
  CHECK_PTR_STORE(0, ptr, sizeof(char*));
  CHECK_STRING_LOAD(1, fmt);
  
  int result = vasprintf(ptr, fmt, va);

  if (result != -1) {
    sbcets_key_t key = 0;
    sbcets_lock_t lock = nullptr;
    __softboundcets_memory_allocation(*ptr, &lock, &key);
    // We have sucessfully allocated, result contains the size of the buffer - 1 for \0
    __softboundcets_metadata_store(*ptr, *ptr, *ptr + result + 1, key, lock);
  }

  return result;
}

__RT_VISIBILITY
int softboundcets_vdprintf(int fd, char *fmt, va_list va) {
  CHECK_STRING_LOAD(0, fmt);

  return vdprintf(fd, fmt, va);
}

__RT_VISIBILITY
int softboundcets_vfprintf(FILE *file, char *fmt, va_list va) {
  CHECK_PTR_LOAD(0, file, sizeof(FILE));
  CHECK_STRING_LOAD(1, fmt);

  return vfprintf(file, fmt, va);
}

__RT_VISIBILITY
int softboundcets_vfscanf(FILE *file, char *format, va_list va) {
  CHECK_PTR_LOAD(0, file, sizeof(FILE));
  CHECK_STRING_LOAD(1, format);

  return vfscanf(file, format, va);
}

__RT_VISIBILITY
int softboundcets_vprintf(char *fmt, va_list va) {
  CHECK_STRING_LOAD(0, fmt);

  return vprintf(fmt, va);
}

__RT_VISIBILITY
int softboundcets_vscanf(char *fmt, va_list va) {
  CHECK_STRING_LOAD(0, fmt);

  return vscanf(fmt, va);
}


__RT_VISIBILITY
int softboundcets_vsnprintf(char *buf, size_t n, char *fmt, va_list va) {
  CHECK_PTR_STORE(0, buf, n);
  CHECK_STRING_LOAD(1, fmt);

  return vsnprintf(buf, n, fmt, va);
}

__RT_VISIBILITY
int softboundcets_vsprintf(char *buf, char *fmt, va_list va) {
  CHECK_PTR_STORE_NULLABLE(0, buf, 0);
  CHECK_STRING_LOAD(1, fmt);

  // Note: Since we cannot check for the buffer size before calling sprintf, we check after to
  // limit the potential damage
  int result = vsprintf(buf, fmt, va);

  if (buf) {
    size_t bufsize = (size_t)buf_bound - (size_t)buf_base;
    // The trailing null character is not included, so if the result is the same as the buffer size,
    // we have overshot by one.
    if ((size_t)result >= bufsize) {
      __softboundcets_error_printf("vsprintf result did not fit in the provided buffer: "\
        "buffer size = %llu, required size = %d", bufsize, result + 1);
      __softboundcets_abort();
    }
  }
  return result;
}

__RT_VISIBILITY
int softboundcets_vsscanf(char *buf, char *fmt, va_list va) {
  CHECK_STRING_LOAD(0, buf);
  CHECK_STRING_LOAD(1, fmt);

  return vsscanf(buf, fmt, va);
}

__RT_VISIBILITY
wchar_t *softboundcets_wcscpy(wchar_t *dest, const wchar_t *src) {
  CHECK_STRING_STORE(1, dest);
  CHECK_STRING_LOAD(2, src);

  size_t size = wcslen(src)*sizeof(wchar_t);
  if (dest < dest_base || ((char*)dest > (char*)dest_bound - size - 1) ||
      (size > (size_t)dest_bound)) {
    printf("[wcscpy] overflow in wcscpy with dest\n");
    __softboundcets_abort();
  }
  if (src < src_base || ((char*)src > (char*)src_bound - size - 1) ||
      (size > (size_t)src_bound)) {
    printf("[wcscpy] overflow in wcscpy with src\n");
    __softboundcets_abort();
  }

  __softboundcets_propagate_metadata_shadow_stack_from(1, 0);

  return wcscpy(dest, src);
}

// Wrappers for unistd.h

__RT_VISIBILITY
int softboundcets_access(char *name, int type) {
  CHECK_STRING_LOAD(0, name);
  return access(name, type);
}

__RT_VISIBILITY
int softboundcets_brk(void *addr) {
  // Note: brk only uses the address of the pointer, this is not expected to be valid
  return brk(addr);
}

__RT_VISIBILITY
size_t softboundcets_confstr(int name, char *buf, size_t len) {
  CHECK_PTR_STORE_NULLABLE(0, buf, len);
  return confstr(name, buf, len);
}

__RT_VISIBILITY
ssize_t softboundcets_copy_file_range(int infd, loff_t *inoff, int outfd, loff_t *outoff, size_t length, unsigned int flags) {
  CHECK_PTR_LOAD_NULLABLE(0, inoff, sizeof(loff_t));
  CHECK_PTR_STORE_NULLABLE(1, outoff, sizeof(loff_t));
  return copy_file_range(infd, inoff, outfd, outoff, length, flags);
}

/*__RT_VISIBILITY
char *softboundcets_crypt(char *key, char *salt) {
  CHECK_STRING_LOAD(1, key);
  CHECK_STRING_LOAD(2, salt);

  char *result = crypt(key, salt);
  // crypt should always return a buffer, but an invalid value on error
  __softboundcets_store_return_metadata(result, result + CRYPT_OUTPUT_SIZE, 1, __softboundcets_global_lock);
  return result;
}*/

__RT_VISIBILITY
int softboundcets_eaccess(char *name, int type) {
  CHECK_STRING_LOAD(0, name);
  return eaccess(name, type);
}

__RT_VISIBILITY
int softboundcets_euidaccess(char *name, int type) {
  CHECK_STRING_LOAD(0, name);
  return euidaccess(name, type);
}

__RT_VISIBILITY
int softboundcets_execl(char *path, char *arg0, ...) {
  CHECK_STRING_LOAD(0, path);
  CHECK_STRING_LOAD(1, arg0);

  __sanitizer::Vector<char *> args;
  args.PushBack(arg0);
  char *arg;
  va_list va;
  va_start(va, arg0);

  // Note: This loop may overrun if the va_list is not terminated
  arg = va_arg(va, char *);
  while (arg != nullptr) {
    sbcets_base_t arg_base = __softboundcets_metadata_load_base(arg);
    sbcets_bound_t arg_bound = __softboundcets_metadata_load_bound(arg);
    sbcets_lock_t arg_lock = __softboundcets_metadata_load_lock(arg);
    sbcets_key_t arg_key = __softboundcets_metadata_load_key(arg);

    __softboundcets_temporal_load_dereference_check(arg_lock, arg_key); 
    if (!memchr(arg, '\0', (char*)arg_bound - arg)) {
      __softboundcets_error_printf("In string load dereference check: base=%zx, bound=%zx, ptr=%zx",
        arg_base, arg_bound, arg);
      __softboundcets_abort();
    }

    args.PushBack(arg);
    arg = va_arg(va, char *);
  }
  args.PushBack(nullptr);

  int result = execv(path, &args[0]);

  va_end(va);
  return result;
}

// Check a null terminated string array
static void check_string_array(char **array, sbcets_bound_t array_bound) {
  bool null_found = false;
  for (char **element = array; element < array_bound; element++) {
    if (element == nullptr) {
      null_found = true;
      break;
    }

    sbcets_base_t element_base = __softboundcets_metadata_load_base(element);
    sbcets_bound_t element_bound = __softboundcets_metadata_load_bound(element);
    sbcets_lock_t element_lock = __softboundcets_metadata_load_lock(element);
    sbcets_key_t element_key = __softboundcets_metadata_load_key(element);

    __softboundcets_temporal_load_dereference_check(element_lock, element_key);
    if (!memchr(*element, '\0', (char*)element_bound - *element)) {
      __softboundcets_error_printf("In string load dereference check: base=%zx, bound=%zx, ptr=%zx",
        element_base, element_bound, *element);
      __softboundcets_abort();
    }
  }
  
  if (!null_found) {
    __softboundcets_error_printf("Array was not NULL-terminated");
    __softboundcets_abort();
  }
}

__RT_VISIBILITY
int softboundcets_execle(char *path, char *arg0, .../*, nullptr, char *envp[]*/) {
  CHECK_STRING_LOAD(0, path);
  CHECK_STRING_LOAD(1, arg0);

  __sanitizer::Vector<char *> args;
  args.PushBack(arg0);
  char *arg;
  va_list va;
  va_start(va, arg0);

  // Note: This loop may overrun if the va_list is not terminated
  arg = va_arg(va, char *);
  while (arg != nullptr) {
    sbcets_base_t arg_base = __softboundcets_metadata_load_base(arg);
    sbcets_bound_t arg_bound = __softboundcets_metadata_load_bound(arg);
    sbcets_lock_t arg_lock = __softboundcets_metadata_load_lock(arg);
    sbcets_key_t arg_key = __softboundcets_metadata_load_key(arg);

    __softboundcets_temporal_load_dereference_check(arg_lock, arg_key); 
    if (!memchr(arg, '\0', (char*)arg_bound - arg)) {
      __softboundcets_error_printf("In string load dereference check: base=%zx, bound=%zx, ptr=%zx",
        arg_base, arg_bound, arg);
      __softboundcets_abort();
    }

    args.PushBack(arg);
    arg = va_arg(va, char *);
  }
  args.PushBack(nullptr);

  char **envp = va_arg(va, char **);
#if __SOFTBOUNDCETS_CHECK_LOADS
  sbcets_base_t envp_base = __softboundcets_metadata_load_base(envp);
  sbcets_bound_t envp_bound = __softboundcets_metadata_load_bound(envp);
  sbcets_lock_t envp_lock = __softboundcets_metadata_load_lock(envp);
  sbcets_key_t envp_key = __softboundcets_metadata_load_key(envp);
  
  __softboundcets_temporal_load_dereference_check(envp_lock, envp_key);
  check_string_array(envp, envp_bound);
#endif

  int result = execve(path, &args[0], envp);

  va_end(va);
  return result;
}

__RT_VISIBILITY
int softboundcets_execlp(char *file, char *arg0, ...) {
  CHECK_STRING_LOAD(0, file);
  CHECK_STRING_LOAD(1, arg0);

  __sanitizer::Vector<char *> args;
  args.PushBack(arg0);
  char *arg;
  va_list va;
  va_start(va, arg0);

  // Note: This loop may overrun if the va_list is not terminated
  arg = va_arg(va, char *);
  while (arg != nullptr) {
    sbcets_base_t arg_base = __softboundcets_metadata_load_base(arg);
    sbcets_bound_t arg_bound = __softboundcets_metadata_load_bound(arg);
    sbcets_lock_t arg_lock = __softboundcets_metadata_load_lock(arg);
    sbcets_key_t arg_key = __softboundcets_metadata_load_key(arg);

    __softboundcets_temporal_load_dereference_check(arg_lock, arg_key); 
    if (!memchr(arg, '\0', (char*)arg_bound - arg)) {
      __softboundcets_error_printf("In string load dereference check: base=%zx, bound=%zx, ptr=%zx",
        arg_base, arg_bound, arg);
      __softboundcets_abort();
    }

    args.PushBack(arg);
    arg = va_arg(va, char *);
  }
  args.PushBack(nullptr);

  int result = execvp(file, &args[0]);

  va_end(va);
  return result;
}

__RT_VISIBILITY
int softboundcets_execv(char *path, char **argv) {
  CHECK_STRING_LOAD(0, path);
  CHECK_PTR_LOAD(1, argv, sizeof(char*));
#if __SOFTBOUNDCETS_CHECK_LOADS
  check_string_array(argv, argv_bound);
#endif

  return execv(path, argv);
}

__RT_VISIBILITY
int softboundcets_execve(char *path, char **argv, char **envp) {
  CHECK_STRING_LOAD(0, path);
  CHECK_PTR_LOAD(1, argv, sizeof(char*));
  CHECK_PTR_LOAD(2, envp, sizeof(char*));

#if __SOFTBOUNDCETS_CHECK_LOADS
  check_string_array(argv, argv_bound);
  check_string_array(envp, envp_bound);
#endif

  return execve(path, argv, envp);
}

/* TODO: This is undefined on debian?
__RT_VISIBILITY
int softboundcets_execveat(int dirfd, char *path, char **argv, char **envp, int flags) {
  CHECK_STRING_LOAD(2, path);
  CHECK_PTR_LOAD(3, argv, sizeof(char*));
  CHECK_PTR_LOAD(4, envp, sizeof(char*));

#if __SOFTBOUNDCETS_CHECK_LOADS
  check_string_array(argv, argv_bound);
  check_string_array(envp, envp_bound);
#endif

  return execveat(dirfd, path, argv, envp, flags);
}
*/

__RT_VISIBILITY
int softboundcets_execvp(char *file, char **args) {
  CHECK_STRING_LOAD(0, file);
  CHECK_PTR_LOAD(1, args, sizeof(char*));

#if __SOFTBOUNDCETS_CHECK_LOADS
  check_string_array(args, args_bound);
#endif

  return execvp(file, args);
}

__RT_VISIBILITY
int softboundcets_execvpe(char *file, char **args, char **envp) {
  CHECK_STRING_LOAD(0, file);
  CHECK_PTR_LOAD(1, args, sizeof(char*));
  CHECK_PTR_LOAD(2, envp, sizeof(char*));

#if __SOFTBOUNDCETS_CHECK_LOADS
  check_string_array(args, args_bound);
  check_string_array(envp, envp_bound);
#endif

  return execvpe(file, args, envp);
}

__RT_VISIBILITY
int softboundcets_faccessat(int fd, char *file, int type, int flags) {
  CHECK_STRING_LOAD(0, file);
  return faccessat(fd, file, type, flags);
}

__RT_VISIBILITY
int softboundcets_fexecve(int fd, char **argv, char **envp) {
  CHECK_PTR_LOAD(0, argv, sizeof(char*));
  CHECK_PTR_LOAD(1, envp, sizeof(char*));

#if __SOFTBOUNDCETS_CHECK_LOADS
  check_string_array(argv, argv_bound);
  check_string_array(envp, envp_bound);
#endif

  return fexecve(fd, argv, envp);
}

__RT_VISIBILITY
char *softboundcets_get_current_dir_name(void) {
  char *result = get_current_dir_name();

  if (result) {
    sbcets_lock_t result_lock = nullptr;
    sbcets_key_t result_key = 0;

    __softboundcets_memory_allocation(result, &result_lock, &result_key);
    __softboundcets_store_return_metadata(result, result + strlen(result) + 1, result_key, result_lock);
  } else {
    __softboundcets_store_null_return_metadata();
  }

  return result;
}

__RT_VISIBILITY
int softboundcets_getdomainname(char *name, size_t len) {
  CHECK_PTR_STORE(0, name, len);
  return getdomainname(name, len);
}

__RT_VISIBILITY
int softboundcets_getgroups(int size, gid_t *list) {
  if (size > 0) {
    CHECK_PTR_STORE(0, list, size * sizeof(gid_t));
  }

  return getgroups(size, list);
}

__RT_VISIBILITY
int softboundcets_gethostname(char *name, size_t len) {
  CHECK_PTR_STORE(0, name, len);
  return gethostname(name, len);
}

__RT_VISIBILITY
char *softboundcets_getlogin(void) {
  char *result = getlogin();

  if (result) {
    __softboundcets_store_return_metadata(result, result + strlen(result) + 1, 1,
                                          __softboundcets_global_lock);
  } else {
    __softboundcets_store_null_return_metadata();
  }

  return result;
}

__RT_VISIBILITY
int softboundcets_getlogin_r(char *name, size_t len) {
  CHECK_PTR_STORE(0, name, len);
  return getlogin_r(name, len);
}

__RT_VISIBILITY
char *softboundcets_getpass(char *prompt) {
  CHECK_STRING_LOAD(1, prompt);
  char *result = getpass(prompt);

  if (result) {
    // Note: The bound should be PASS_MAX, but in glibc, it allocates BUFSIZ instead
    __softboundcets_store_return_metadata(result, result + BUFSIZ, 1, __softboundcets_global_lock);
  } else {
    __softboundcets_store_null_return_metadata();
  }

  return result;
}

__RT_VISIBILITY
int softboundcets_getresgid(gid_t *rgid, gid_t *egid, gid_t *sgid) {
  CHECK_PTR_STORE(0, rgid, sizeof(gid_t));
  CHECK_PTR_STORE(1, egid, sizeof(gid_t));
  CHECK_PTR_STORE(2, sgid, sizeof(gid_t));
  return getresgid(rgid, egid, sgid);
}

__RT_VISIBILITY
int softboundcets_getresuid(uid_t *ruid, uid_t *euid, uid_t *suid) {
  CHECK_PTR_STORE(0, ruid, sizeof(uid_t));
  CHECK_PTR_STORE(1, euid, sizeof(uid_t));
  CHECK_PTR_STORE(2, suid, sizeof(uid_t));
  return getresuid(ruid, euid, suid);
}

__RT_VISIBILITY
char *softboundcets_getusershell(void) {
  char *result = getusershell();

  if (result) {
    // The man page does not have a lot to say about this function, so I assume that the buffer is
    // not malloc'd
    __softboundcets_store_return_metadata(result, result + strlen(result) + 1, 1,
                                          __softboundcets_global_lock);
  } else {
    __softboundcets_store_null_return_metadata();
  }

  return result;
}

__RT_VISIBILITY
char *softboundcets_getwd(char *buf) {
  CHECK_PTR_STORE(1, buf, PATH_MAX);
  __softboundcets_propagate_metadata_shadow_stack_from(1, 0);
  return getwd(buf);
}

__RT_VISIBILITY
int softboundcets_lchown(char *file, uid_t owner, gid_t group) {
  CHECK_STRING_LOAD(0, file);
  return lchown(file, owner, group);
}

__RT_VISIBILITY
int softboundcets_link(char *from, char *to) {
  CHECK_STRING_LOAD(0, from);
  CHECK_STRING_LOAD(1, to);

  return link(from, to);
}

__RT_VISIBILITY
int softboundcets_pipe(int *pipes) {
  CHECK_PTR_LOAD(0, pipes, 2 * sizeof(int));
  return pipe(pipes);
}

__RT_VISIBILITY
int softboundcets_pipe2(int *pipes, int flags) {
  CHECK_PTR_LOAD(0, pipes, 2 * sizeof(int));
  return pipe2(pipes, flags);
}

__RT_VISIBILITY
ssize_t softboundcets_pread(int fd, void *buf, size_t nbytes, off_t offset) {
  CHECK_PTR_STORE(0, buf, nbytes);
  return pread(fd, buf, nbytes, offset);
}

__RT_VISIBILITY
ssize_t softboundcets_pread64(int fd, void *buf, size_t nbytes, off64_t offset) {
  CHECK_PTR_STORE(0, buf, nbytes);
  return pread64(fd, buf, nbytes, offset);
}

__RT_VISIBILITY
int softboundcets_profil(unsigned short *buf, size_t bufsize, size_t offset, unsigned int scale) {
  // Note: buf is stored in libc and must be valid until the function is called again, I think
  CHECK_PTR_STORE(0, buf, bufsize);
  return profil(buf, bufsize, offset, scale);
}

__RT_VISIBILITY
ssize_t softboundcets_pwrite(int fd, void *buf, size_t n, off_t offset) {
  CHECK_PTR_LOAD(0, buf, n);
  return pwrite(fd, buf, n, offset);
}

__RT_VISIBILITY
ssize_t softboundcets_pwrite64(int fd, void *buf, size_t n, off64_t offset) {
  CHECK_PTR_LOAD(0, buf, n);
  return pwrite64(fd, buf, n, offset);
}

__RT_VISIBILITY
ssize_t softboundcets_readlink(char *path, char *buf, size_t len) {
  CHECK_STRING_LOAD(0, path);
  CHECK_PTR_STORE(1, buf, len);
  return readlink(path, buf, len);
}

__RT_VISIBILITY
int softboundcets_revoke(char *file) {
  CHECK_STRING_LOAD(0, file);
  return revoke(file);
}

__RT_VISIBILITY
void *softboundcets_sbrk(intptr_t delta) {
  void *result = sbrk(delta);
  if ((intptr_t)result == (intptr_t)-1) {
    // Note: Since NULL is actually a valid pointer here, -1 is the null pointer essentially
    __softboundcets_store_null_return_metadata();
  } else {
    sbcets_lock_t result_lock = nullptr;
    sbcets_key_t result_key = 0;
    __softboundcets_memory_allocation(result, &result_lock, &result_key);
    __softboundcets_store_return_metadata(result, (void*)((intptr_t)result + delta), result_key, result_lock);
  }
  return result;
}

__RT_VISIBILITY
int softboundcets_setdomainname(char *name, size_t len) {
  CHECK_PTR_LOAD(0, name, len);
  return setdomainname(name, len);
}

__RT_VISIBILITY
int softboundcets_sethostname(char *name, size_t len) {
  CHECK_PTR_LOAD(0, name, len);
  return sethostname(name, len);
}

__RT_VISIBILITY
int softboundcets_setlogin(char *name) {
  CHECK_STRING_LOAD(0, name);
}

__RT_VISIBILITY
void softboundcets_swab(void *from, void *to, ssize_t n) {
  if (n < 0) {
    // Negative n is allowed, but the function does nothing in that case
    // We can thus return early and not have to deal with passing a negative number to the checkers
    return;
  }

  CHECK_PTR_LOAD(0, from, n);
  CHECK_PTR_STORE(1, to, n);

  // Note: I'll not copy over any metadata since the buffer is scrambled and any pointer will be
  // invalid after.

  swab(from, to, n);
}

__RT_VISIBILITY
int softboundcets_symlink(char *from, char *to) {
  CHECK_STRING_LOAD(0, from);
  CHECK_STRING_LOAD(1, to);

  return symlink(from, to);
}

__RT_VISIBILITY
int softboundcets_truncate(char *file, off_t length) {
  CHECK_STRING_LOAD(0, file);

  return truncate(file, length);
}

__RT_VISIBILITY
int softboundcets_truncate64(char *file, off64_t length) {
  CHECK_STRING_LOAD(0, file);

  return truncate64(file, length);
}

__RT_VISIBILITY
char *softboundcets_ttyname(int fd) {
  char *result = ttyname(fd);

  if (result) {
    // From the man page: "The return pointer *may* point to static data", so I'll not do an
    // allocation here.
    __softboundcets_store_return_metadata(result, result + strlen(result) + 1, 1,
                                          __softboundcets_global_lock);
  } else {
    __softboundcets_store_null_return_metadata();
  }

  return result;
}

__RT_VISIBILITY
int softboundcets_ttyname_r(int fd, char *buf, size_t len) {
  CHECK_PTR_STORE(0, buf, len);

  return ttyname_r(fd, buf, len);
}

__RT_VISIBILITY
int softboundcets_acct(char *filename) {
  CHECK_STRING_LOAD_NULLABLE(0, filename);

  return acct(filename);
}

__RT_VISIBILITY
int softboundcets_getentropy(void *buffer, size_t len) {
  CHECK_PTR_STORE(0, buffer, len);

  return getentropy(buffer, len);
}

// Wrappers for stdlib.h

__RT_VISIBILITY
long softboundcets_a64l(char *s) {
  CHECK_STRING_LOAD(0, s);

  return a64l(s);
}

__RT_VISIBILITY
void *softboundcets_aligned_alloc(size_t alignment, size_t size) {
  void *result = aligned_alloc(alignment, size);

  if (result) {
    sbcets_lock_t result_lock = nullptr;
    sbcets_key_t result_key = 0;

    __softboundcets_memory_allocation(result, &result_lock, &result_key);
    __softboundcets_store_return_metadata(result, (char*)result + size, result_key, result_lock);
  } else {
    __softboundcets_store_null_return_metadata();
  }
  return result;
}

/**
__RT_VISIBILITY
void softboundcets_arc4random_buf(void *buf, size_t size) {
  CHECK_PTR_STORE(0, buf, size);

  arc4random_buf(buf, size);
}
*/

__RT_VISIBILITY
int softboundcets_at_quick_exit(void (*func)(void)) {
  CHECK_PTR_LOAD(0, func, 0);

  at_quick_exit(func);
}

__RT_VISIBILITY
long long softboundcets_atoll(char *nptr) {
  CHECK_STRING_LOAD(0, nptr);

  return atoll(nptr);
}

__RT_VISIBILITY
char *softboundcets_canonicalize_file_name(char *name) {
  CHECK_STRING_LOAD(1, name);

  char *result = canonicalize_file_name(name);
  if (result) {
    sbcets_lock_t result_lock = nullptr;
    sbcets_key_t result_key = 0;

    __softboundcets_memory_allocation(result, &result_lock, &result_key);
    __softboundcets_store_return_metadata(result, result + strlen(result) + 1, result_key, result_lock);
  } else {
    __softboundcets_store_null_return_metadata();
  }
  return result;
}

__RT_VISIBILITY
int softboundcets_drand48_r(struct drand48_data *buffer, double *result) {
  CHECK_PTR_STORE(0, buffer, sizeof(struct drand48_data));
  CHECK_PTR_STORE(1, result, sizeof(double));

  return drand48_r(buffer, result);
}

__RT_VISIBILITY
char *softboundcets_ecvt(double value, int ndigits, int *decpt, int *sign) {
  CHECK_PTR_STORE(1, decpt, sizeof(int));
  CHECK_PTR_STORE(1, sign, sizeof(int));

  char *result = ecvt(value, ndigits, decpt, sign);
  // I'm not sure this ever returns null, but just in case
  if (result) {
    // The result is allocated in a static buffer
    __softboundcets_store_return_metadata(result, result + strlen(result) + 1, 1, __softboundcets_global_lock);
  } else {
    __softboundcets_store_null_return_metadata();
  }

  return result;
}

__RT_VISIBILITY
int softboundcets_ecvt_r(double value, int ndigits, int *decpt, int *sign, char *buf, size_t len) {
  CHECK_PTR_STORE(0, decpt, sizeof(int));
  CHECK_PTR_STORE(1, sign, sizeof(int));
  CHECK_PTR_STORE(2, buf, len);

  return ecvt_r(value, ndigits, decpt, sign, buf, len);
}

__RT_VISIBILITY
double softboundcets_erand48(unsigned short xsubi[3]) {
  CHECK_PTR_STORE(0, xsubi, 3 * sizeof(unsigned short));

  return erand48(xsubi);
}

__RT_VISIBILITY
int softboundcets_erand48_r(unsigned short xsubi[3], struct drand48_data *buffer, double *result) {
  CHECK_PTR_STORE(0, xsubi, sizeof(unsigned short) * 3);
  CHECK_PTR_STORE(1, buffer, sizeof(struct drand48_data));
  CHECK_PTR_STORE(2, result, sizeof(double));

  return erand48_r(xsubi, buffer, result);
}

__RT_VISIBILITY
char *softboundcets_fcvt(double value, int ndigits, int *decpt, int *sign) {
  CHECK_PTR_STORE(1, decpt, sizeof(int));
  CHECK_PTR_STORE(2, sign, sizeof(int));

  char *result = fcvt(value, ndigits, decpt, sign);
  if (result) {
    __softboundcets_store_return_metadata(result, result + strlen(result) + 1, 1, __softboundcets_global_lock);
  } else {
    __softboundcets_store_null_return_metadata();
  }

  return result;
}

__RT_VISIBILITY
int softboundcets_fcvt_r(double value, int ndigits, int *decpt, int *sign, char *buf, size_t len) {
  CHECK_PTR_STORE(0, decpt, sizeof(int));
  CHECK_PTR_STORE(1, sign, sizeof(int));
  CHECK_PTR_STORE(2, buf, len);

  return fcvt_r(value, ndigits, decpt, sign, buf, len);
}


__RT_VISIBILITY
char *softboundcets_gcvt(double value, int ndigit, char *buf) {
  CHECK_PTR_LOAD(1, buf, ndigit);
  __softboundcets_propagate_metadata_shadow_stack_from(1, 0);

  return gcvt(value, ndigit, buf);
}

__RT_VISIBILITY
int softboundcets_getloadavg(double *loadavg, int nelem) {
  CHECK_PTR_STORE(0, loadavg, nelem * sizeof(double));

  return getloadavg(loadavg, nelem);
}

__RT_VISIBILITY
int softboundcets_getsubopt(char **optionp, char **tokens, char **valuep) {
  CHECK_PTR_STORE(0, optionp, sizeof(char*));
  CHECK_PTR_LOAD(1, tokens, sizeof(char*));
  CHECK_PTR_STORE(2, valuep, sizeof(char*));

  // The optionp should point into a continous string -> make sure the string has a null terminator
  char *option = *optionp;
  sbcets_base_t option_base = __softboundcets_metadata_load_base(option);
  sbcets_bound_t option_bound = __softboundcets_metadata_load_bound(option);
  sbcets_lock_t option_lock = __softboundcets_metadata_load_lock(option);
  sbcets_key_t option_key = __softboundcets_metadata_load_key(option);

  CHECK_PTR_ALIVE_LOAD_ONLY(option);
  CHECK_STRING_BOUNDS_LOAD_ONLY(option);

  check_string_array(tokens, tokens_bound);

  int result = getsubopt(optionp, tokens, valuep);

  if (*valuep) {
    // Since *valuep points into *optionp, we just copy over the metadata
    __softboundcets_metadata_store(*valuep, option_base, option_bound, option_key, option_lock);
  }
}

// Since the initstate function returns the previous value, we have to keep track of its metadata
// Note: This is set up to return universally valid metadata for the first call since
// we do not know the location of the initial state's internal buffer in glibc
static size_t _initstate_size = 32;
static sbcets_base_t _initstate_base = 0;
static sbcets_bound_t _initstate_bound = (void*)281474976710656;
static sbcets_lock_t _initstate_lock = __softboundcets_global_lock;
static sbcets_key_t _initstate_key = 1;

__RT_VISIBILITY
char *softboundcets_initstate(unsigned int seed, char *state, size_t n) {
  CHECK_PTR_LOAD(1, state, n);

  char *result = initstate(seed, state, n);

  if (result) {
    __softboundcets_store_return_metadata(_initstate_base, _initstate_bound, _initstate_key,
                                          _initstate_lock);

    _initstate_size = n;
    _initstate_base = state_base;
    _initstate_bound = state_bound;
    _initstate_lock = state_lock;
    _initstate_key = state_key;
  } else {
    __softboundcets_store_null_return_metadata();
  }

  return result;
}

__RT_VISIBILITY
int softboundcets_initstate_r(unsigned int seed, char *state, size_t n, struct random_data *buf) {
  CHECK_PTR_LOAD(0, state, n);
  CHECK_PTR_STORE(1, buf, sizeof(struct random_data));

  return initstate_r(seed, state, n, buf);
}

__RT_VISIBILITY
long softboundcets_jrand48(unsigned short xsubi[3]) {
  CHECK_PTR_STORE(0, xsubi, sizeof(unsigned short) * 3);

  return jrand48(xsubi);
}

__RT_VISIBILITY
int softboundcets_jrand48_r(unsigned short xsubi[3], struct drand48_data *buf, long *result) {
  CHECK_PTR_STORE(0, xsubi, sizeof(unsigned short) * 3);
  CHECK_PTR_STORE(1, buf, sizeof(struct drand48_data));
  CHECK_PTR_STORE(2, result, sizeof(long));

  return jrand48_r(xsubi, buf, result);
}

__RT_VISIBILITY
char *softboundcets_l64a(long n) {
  char *result = l64a(n);

  // I'm not sure if this ever returns null, but better to be sure
  if (result) {
    __softboundcets_store_return_metadata(result, result + strlen(result) + 1, 1,
                                          __softboundcets_global_lock);
  } else {
    __softboundcets_store_null_return_metadata();
  }

  return result;
}

__RT_VISIBILITY
void softboundcets_lcong48(unsigned short param[7]) {
  CHECK_PTR_LOAD(0, param, sizeof(unsigned short) * 7);

  lcong48(param);
}

__RT_VISIBILITY
int softboundcets_lcong48_r(unsigned short param[7], struct drand48_data *buf) {
  CHECK_PTR_LOAD(0, param, sizeof(unsigned short) * 7);
  CHECK_PTR_STORE(1, buf, sizeof(struct drand48_data));

  return lcong48_r(param, buf);
}

__RT_VISIBILITY
int softboundcets_lrand48_r(struct drand48_data *buf, long *result) {
  CHECK_PTR_STORE(0, buf, sizeof(struct drand48_data));
  CHECK_PTR_STORE(1, result, sizeof(long));

  return lrand48_r(buf, result);
}

__RT_VISIBILITY
int softboundcets_mblen(char *s, size_t n) {
  CHECK_PTR_LOAD_NULLABLE(0, s, n);

  return mblen(s, n);
}

__RT_VISIBILITY
size_t softboundcets_mbstowcs(wchar_t *dest, char *src, size_t dest_size) {
  CHECK_PTR_BOUNDS_STORE_NULLABLE(0, dest, dest_size);
  // While src is a multibyte-encoded string, it still is terminated by NULL
  CHECK_STRING_BOUNDS_LOAD(1, src);

  return mbstowcs(dest, src, dest_size);
}

__RT_VISIBILITY
int softboundcets_mbtowc(wchar_t *dest, char *src, size_t n) {
  CHECK_PTR_STORE_NULLABLE(0, dest, sizeof(wchar_t));
  CHECK_PTR_LOAD_NULLABLE(1, src, n);

  return mbtowc(dest, src, n);
}

__RT_VISIBILITY
int softboundcets_mkostemp(char *path_template, int flags) {
  CHECK_STRING_LOAD(0, path_template);

  return mkostemp(path_template, flags);
}

__RT_VISIBILITY
int softboundcets_mkostemp64(char *path_template, int flags) {
  CHECK_STRING_LOAD(0, path_template);

  return mkostemp64(path_template, flags);
}

__RT_VISIBILITY
int softboundcets_mkostemps(char *path_template, int suffixlen, int flags) {
  CHECK_STRING_LOAD(0, path_template);

  return mkostemps(path_template, suffixlen, flags);
}

__RT_VISIBILITY
int softboundcets_mkostemps64(char *path_template, int suffixlen, int flags) {
  CHECK_STRING_LOAD(0, path_template);

  return mkostemps64(path_template, suffixlen, flags);
}

__RT_VISIBILITY
int softboundcets_mkstemp64(char *path_template) {
  CHECK_STRING_LOAD(0, path_template);

  return mkstemp64(path_template);
}

__RT_VISIBILITY
int softboundcets_mkstemps(char *path_template, int suffixlen) {
  CHECK_STRING_LOAD(0, path_template);

  return mkstemps(path_template, suffixlen);
}

__RT_VISIBILITY
int softboundcets_mkstemps64(char *path_template, int suffixlen) {
  CHECK_STRING_LOAD(0, path_template);

  return mkstemps64(path_template, suffixlen);
}


__RT_VISIBILITY
char *softboundcets_mktemp(char *path_template) {
  CHECK_STRING_STORE(1, path_template);
  __softboundcets_propagate_metadata_shadow_stack_from(1, 0);
  
  return mktemp(path_template);
}

__RT_VISIBILITY
int softboundcets_mrand48_r(struct drand48_data *buf, long *result) {
  CHECK_PTR_STORE(0, buf, sizeof(struct drand48_data));
  CHECK_PTR_STORE(1, result, sizeof(long));

  return mrand48_r(buf, result);
}

__RT_VISIBILITY
long softboundcets_nrand48(unsigned short xsubi[3]) {
  CHECK_PTR_STORE(0, xsubi, sizeof(unsigned short) * 3);

  return nrand48(xsubi);
}

__RT_VISIBILITY
int softboundcets_nrand48_r(unsigned short xsubi[3], struct drand48_data *buf, long *result) {
  CHECK_PTR_STORE(0, xsubi, sizeof(unsigned short) * 3);
  CHECK_PTR_STORE(1, buf, sizeof(struct drand48_data));
  CHECK_PTR_STORE(2, result, sizeof(long));

  return nrand48_r(xsubi, buf, result);
}

__RT_VISIBILITY
int softboundcets_on_exit(void (*func)(int status, void *arg), void *arg) {
  CHECK_PTR_LOAD(0, func, 0);
  // Note: Arg should be valid when the on_exit function is called.
  // TODO: We could wrap the callback as well, but that would probably require us to leak memory
  CHECK_PTR_LOAD(1, arg, 0);

  return on_exit(func, arg);
}

__RT_VISIBILITY
int softboundcets_posix_memalign(void **ptr, size_t alignment, size_t size) {
  CHECK_PTR_STORE(0, ptr, sizeof(void*));

  int result = posix_memalign(ptr, alignment, size);
  if (result == 0) {
    sbcets_lock_t result_lock = nullptr;
    sbcets_key_t result_key = 0;

    __softboundcets_memory_allocation(*ptr, &result_lock, &result_key);
    __softboundcets_metadata_store(*ptr, *ptr, (char*)*ptr + size, result_key, result_lock);
  }

  return result;
}

__RT_VISIBILITY
char *softboundcets_ptsname(int fd) {
  char *result = ptsname(fd);

  if (result) {
    __softboundcets_store_return_metadata(result, result + strlen(result) + 1, 1,
                                          __softboundcets_global_lock);
  } else {
    __softboundcets_store_null_return_metadata();
  }

  return result;
}

__RT_VISIBILITY
int softboundcets_ptsname_r(int fd, char *buf, size_t n) {
  CHECK_PTR_STORE(0, buf, n);

  return ptsname_r(fd, buf, n);
}

__RT_VISIBILITY
int softboundcets_putenv(char *string) {
  CHECK_STRING_LOAD(0, string);

  return putenv(string);
}

__RT_VISIBILITY
char *softboundcets_qecvt(long double value, int ndigit, int *decpt, int *sign) {
  CHECK_PTR_STORE(1, decpt, sizeof(int));
  CHECK_PTR_STORE(2, sign, sizeof(int));

  char *result = qecvt(value, ndigit, decpt, sign);

  if (result) {
    __softboundcets_store_return_metadata(result, result + strlen(result) + 1, 1,
                                          __softboundcets_global_lock);
  } else {
    __softboundcets_store_null_return_metadata();
  }

  return result;
}

__RT_VISIBILITY
int softboundcets_qecvt_r(long double value, int ndigit, int *decpt, int *sign, char *buf, size_t n) {
  CHECK_PTR_STORE(0, decpt, sizeof(int));
  CHECK_PTR_STORE(1, sign, sizeof(int));
  CHECK_PTR_STORE(2, buf, n);

  return qecvt_r(value, ndigit, decpt, sign, buf, n);
}

__RT_VISIBILITY
char *softboundcets_qfcvt(long double value, int ndigit, int *decpt, int *sign) {
  CHECK_PTR_STORE(1, decpt, sizeof(int));
  CHECK_PTR_STORE(2, sign, sizeof(int));

  char *result = qfcvt(value, ndigit, decpt, sign);

  if (result) {
    __softboundcets_store_return_metadata(result, result + strlen(result) + 1, 1,
                                          __softboundcets_global_lock);
  } else {
    __softboundcets_store_null_return_metadata();
  }

  return result;
}

__RT_VISIBILITY
int softboundcets_qfcvt_r(long double value, int ndigit, int *decpt, int *sign, char *buf, size_t n) {
  CHECK_PTR_STORE(0, decpt, sizeof(int));
  CHECK_PTR_STORE(1, sign, sizeof(int));
  CHECK_PTR_STORE(2, buf, n);

  return qfcvt_r(value, ndigit, decpt, sign, buf, n);
}

__RT_VISIBILITY
char *softboundcets_qgcvt(long double value, int ndigit, char *buf) {
  CHECK_PTR_STORE(1, buf, ndigit);
  __softboundcets_propagate_metadata_shadow_stack_from(1, 0);
  return qgcvt(value, ndigit, buf);
}

/*
 * We use heapsort for qsort_r, since it provides nlogn runtime complexity while not requiring
 * memory allocations on the heap or the stack.
 * Glibc uses mergesort and falls back to heapsort in case the allocator fails, which would be
 * better for performance but I do not want to implement two sorting algorithms.
 * 
 * We build a max heap in-place in the array we have to sort.
 * After that, we put the largest (root) element at the back and end up with an array sorted in
 * ascending order.
 * The heap is a binary tree where for index i, its children are at 2 * i + 1 and 2 * i + 2.
 */

typedef struct {
  sbcets_base_t array_base;
  sbcets_bound_t array_bound;
  sbcets_lock_t array_lock;
  sbcets_key_t array_key;

  sbcets_base_t arg_base;
  sbcets_bound_t arg_bound;
  sbcets_lock_t arg_lock;
  sbcets_key_t arg_key;
} _qsort_r_meta;


typedef int (*_qsort_r_cmp_fn)(void *left, void *right, void *arg);

__attribute__((always_inline))
int _qsort_r_call_cmp(_qsort_r_cmp_fn cmp, void *left, void *right, void *arg,
                             _qsort_r_meta meta) {
  __softboundcets_allocate_shadow_stack_space(3);

  // Since both left and right point into the same array, we pass the arrays metadata here
  __softboundcets_store_base_shadow_stack(meta.array_base, 0);
  __softboundcets_store_bound_shadow_stack(meta.array_bound, 0);
  __softboundcets_store_lock_shadow_stack(meta.array_lock, 0);
  __softboundcets_store_key_shadow_stack(meta.array_key, 0);

  __softboundcets_store_base_shadow_stack(meta.array_base, 1);
  __softboundcets_store_bound_shadow_stack(meta.array_bound, 1);
  __softboundcets_store_lock_shadow_stack(meta.array_lock, 1);
  __softboundcets_store_key_shadow_stack(meta.array_key, 1);

  __softboundcets_store_base_shadow_stack(meta.arg_base, 2);
  __softboundcets_store_bound_shadow_stack(meta.arg_bound, 2);
  __softboundcets_store_lock_shadow_stack(meta.arg_lock, 2);
  __softboundcets_store_key_shadow_stack(meta.arg_key, 2);

  int result = cmp(left, right, arg);

  __softboundcets_deallocate_shadow_stack_space();

  return result;
}

__attribute__((always_inline))
void _qsort_r_swap_element(char *ptr1, char *ptr2, size_t size, bool is_ptr) {
  // We could probably make this more efficient by copying in word-size steps but oh well
  for (size_t i = 0; i < size; i++) {
    char swap = ptr1[i];
    ptr1[i] = ptr2[i];
    ptr2[i] = swap;
  }

  if (is_ptr) {
    for (size_t i = 0; i < size; i += sizeof(void*)) {
      __softboundcets_metadata_t *ptr1_meta = __softboundcets_shadowspace_metadata_ptr_create_secondary_tries(&ptr1[i]);
      __softboundcets_metadata_t *ptr2_meta = __softboundcets_shadowspace_metadata_ptr_create_secondary_tries(&ptr2[i]);

      sbcets_base_t ptr1_base = nullptr;
      sbcets_bound_t ptr1_bound = nullptr;
      sbcets_lock_t ptr1_lock = nullptr;
      sbcets_key_t ptr1_key = 0;
      
      sbcets_base_t ptr2_base = nullptr;
      sbcets_bound_t ptr2_bound = nullptr;
      sbcets_lock_t ptr2_lock = nullptr;
      sbcets_key_t ptr2_key = 0;

      // We have to feature gate these assignments since the __softboundcets_metadata_t struct is
      // defined differently based on the flags
#if __SOFTBOUNDCETS_SPATIAL || __SOFTBOUNDCETS_SPATIAL_TEMPORAL
      ptr1_base = ptr1_meta->base;
      ptr1_bound = ptr1_meta->bound;

      ptr2_base = ptr2_meta->base;
      ptr2_bound = ptr2_meta->bound;
#endif

#if __SOFTBOUNDCETS_TEMPORAL || __SOFTBOUNDCETS_SPATIAL_TEMPORAL
      ptr1_lock = ptr1_meta->lock;
      ptr1_key = ptr1_meta->key;

      ptr2_lock = ptr2_meta->lock;
      ptr2_key = ptr2_meta->key;
#endif

      __softboundcets_metadata_store(&ptr1[i], ptr1_base, ptr1_bound, ptr1_key, ptr1_lock);
      __softboundcets_metadata_store(&ptr2[i], ptr2_base, ptr2_bound, ptr2_key, ptr2_lock);
    }
  }
}

__attribute__((always_inline))
void _qsort_r_sift_down(char *array, size_t nmemb, size_t size, _qsort_r_cmp_fn cmp,
                               void *arg, bool is_ptr, size_t parent, _qsort_r_meta meta) {
  while (2 * parent + 1 < nmemb) {
    // We select the left child first, since it has to exist
    size_t child = 2 * parent + 1;

    // If the right child exists and is larger, consieder it instead
    if (child + 1 < nmemb && _qsort_r_call_cmp(cmp, &array[child * size],
        &array[(child + 1) * size], arg, meta) < 0) {
      child++;
    }

    // Now we compare the larger child with the parent and swap them if larger
    // Since we swapped with the larger child, the heap property is valid at the current element
    if (_qsort_r_call_cmp(cmp, &array[parent * size], &array[child * size], arg, meta) < 0) {
      _qsort_r_swap_element(&array[parent * size], &array[child * size], size, is_ptr);
      // Since we swapped the child element with a smaller value, we may have broken the heap
      // property.
      // To fix this, we attempt a swap at the child index again.
      parent = child;
    } else {
      // Since we did nothing, we can stop
      break;
    }
  }
}

__attribute__((always_inline))
void _qsort_r_heapify(char *array, size_t nmemb, size_t size, _qsort_r_cmp_fn cmp,
                             void *arg, bool is_ptr, _qsort_r_meta meta) {
  // The start of the heap is the parent of the last element
  for (size_t start = nmemb / 2; start > 0; start--) {
    _qsort_r_sift_down(array, nmemb, size, cmp, arg, is_ptr, start - 1, meta);
  }
}

__RT_VISIBILITY
void softboundcets_qsort_r(void *base, size_t nmemb, size_t size, _qsort_r_cmp_fn cmp, void *arg) {
  CHECK_PTR_STORE(0, base, nmemb * size);
  CHECK_PTR_LOAD(1, cmp, 0);
  CHECK_PTR_LOAD_NULLABLE(2, arg, 0);

  bool is_ptr = false;
  char *array = (char*)base;

  _qsort_r_meta meta = {
    .array_base = base_base,
    .array_bound = base_bound,
    .array_lock = base_lock,
    .array_key = base_key,

    .arg_base = arg_base,
    .arg_bound = arg_bound,
    .arg_lock = arg_lock,
    .arg_key = arg_key
  };

  // NOTE:
  // We first check if the data to sort contains pointers. If so, we have to swap metadata as well.
  // We assume that data is homogeneous and check the first element for pointers by looking for
  // secondary tries.
  // Note that this can lead to false positives/negatives when our assumption is incorrect and/or
  // a non-pointer value would also be a valid pointer.
  // We could also check for trie entries in every swap for correctness at the cost of performance
  for (size_t i = 0; i < size; i += sizeof(void*)) {
    // Reinterpret the array as a pointer-sized array and get the potential trie index
    size_t primary_index = ((size_t*)array)[i] >> 25;
    // Check if the primary trie contains a secondary tree for this element
    // If it does, assume this is a pointer
    // TODO: Is this reasonable?
    __softboundcets_metadata_t *secondary_index = __softboundcets_trie_primary_table[primary_index];
    if (secondary_index != nullptr) {
      is_ptr = true;
      break;
    }
  }

  // We start by constructing a heap in the array
  _qsort_r_heapify(array, nmemb, size, cmp, arg, is_ptr, meta);

  while (nmemb > 0) {
    // Since we have a max-heap, the first (root) element is always the maximum
    nmemb--;
    _qsort_r_swap_element(&array[0], &array[nmemb * size], size, is_ptr);

    // Restore the heap property
    _qsort_r_sift_down(array, nmemb, size, cmp, arg, is_ptr, 0, meta);
  }
}

__RT_VISIBILITY
int softboundcets_rand_r(unsigned int *seed) {
  CHECK_PTR_STORE(0, seed, sizeof(int));

  return rand_r(seed);
}

__RT_VISIBILITY
int softboundcets_random_r(struct random_data *buf, int32_t *result) {
  CHECK_PTR_STORE(0, buf, sizeof(struct random_data));
  CHECK_PTR_STORE(1, result, sizeof(int32_t));

  return random_r(buf, result);
}

__RT_VISIBILITY
char *softboundcets_realpath(char *name, char *resolved) {
  CHECK_STRING_LOAD(1, name);
  CHECK_PTR_STORE_NULLABLE(2, resolved, PATH_MAX);

  char *result = realpath(name, resolved);
  if (result) {
    // This function can optionally allocate if the resolved parameter is null
    if (resolved) {
      __softboundcets_propagate_metadata_shadow_stack_from(2, 0);
    } else {
      sbcets_lock_t result_lock = nullptr;
      sbcets_key_t result_key = 0;
      __softboundcets_memory_allocation(result, &result_lock, &result_key);
      // TODO: Check the allocation again
      __softboundcets_store_return_metadata(result, result + PATH_MAX, result_key, result_lock);
    }
  } else {
    __softboundcets_store_null_return_metadata();
  }

  return result;
}

__RT_VISIBILITY
char *softboundcets_secure_getenv(char *name) {
  CHECK_STRING_LOAD(1, name);

  char *result = secure_getenv(name);
  if (result) {
    __softboundcets_store_return_metadata(result, result + strlen(result) + 1, 1,
                                          __softboundcets_global_lock);
  } else {
    __softboundcets_store_null_return_metadata();
  }
  return result;
}

__RT_VISIBILITY
unsigned short *softboundcets_seed48(unsigned short seed[3]) {
  CHECK_PTR_LOAD(1, seed, sizeof(unsigned short) * 3);

  unsigned short *result = seed48(seed);
  // seed48 stores the previous buffer in a static buffer that is returned
  __softboundcets_store_return_metadata(result, result + sizeof(unsigned short) * 3, 1,
                                        __softboundcets_global_lock);

  return result;
}

__RT_VISIBILITY
int softboundcets_seed48_r(unsigned short seed[3], struct drand48_data *buf) {
  CHECK_PTR_LOAD(0, seed, sizeof(unsigned short) * 3);
  CHECK_PTR_STORE(1, buf, sizeof(struct drand48_data));

  return seed48_r(seed, buf);
}

__RT_VISIBILITY
char *softboundcets_setstate(char *state) {
  // Note: This is linked to initstate, where the bound value can be changed
  CHECK_PTR_LOAD(1, state, _initstate_size);

  char *result = setstate(state);

  __softboundcets_store_return_metadata(_initstate_base, _initstate_bound, _initstate_key,
                                        _initstate_lock);

  _initstate_base = state_base;
  _initstate_bound = state_bound;
  _initstate_lock = state_lock;
  _initstate_key = state_key;

  return result;
}

__RT_VISIBILITY
int softboundcets_setstate_r(char *state, struct random_data *buf) {
  // TODO: What size?
  CHECK_PTR_LOAD(0, state, 0);
  CHECK_PTR_STORE(1, buf, sizeof(struct random_data));

  return setstate_r(state, buf);
}

__RT_VISIBILITY
int softboundcets_srand48_r(long seed, struct drand48_data *buffer) {
  CHECK_PTR_STORE(0, buffer, sizeof(drand48_data));

  return srand48_r(seed, buffer);
}

__RT_VISIBILITY
int softboundcets_srandom_r(unsigned int seed, struct random_data *buf) {
  CHECK_PTR_STORE(0, buf, sizeof(struct random_data));

  return srandom_r(seed, buf);
}

__RT_VISIBILITY
int softboundcets_strfromd(char *dest, size_t size, char *format, double f) {
  CHECK_PTR_STORE(0, dest, size);
  CHECK_STRING_LOAD(1, format);

  return strfromd(dest, size, format, f);
}

__RT_VISIBILITY
int softboundcets_strfromf(char *dest, size_t size, char *format, float f) {
  CHECK_PTR_STORE(0, dest, size);
  CHECK_STRING_LOAD(1, format);

  return strfromf(dest, size, format, f);
}

/*
__RT_VISIBILITY
int softboundcets_strfromf128(char *dest, size_t size, char *format, _Float128 f) {
  CHECK_PTR_STORE(0, dest, size);
  CHECK_STRING_LOAD(1, format);

  return strfromf128(dest, size, format, f);
}
*/

__RT_VISIBILITY
int softboundcets_strfromf32(char *dest, size_t size, char *format, _Float32 f) {
  CHECK_PTR_STORE(0, dest, size);
  CHECK_STRING_LOAD(1, format);

  return strfromf32(dest, size, format, f);
}

__RT_VISIBILITY
int softboundcets_strfromf32x(char *dest, size_t size, char *format, _Float32x f) {
  CHECK_PTR_STORE(0, dest, size);
  CHECK_STRING_LOAD(1, format);

  return strfromf32x(dest, size, format, f);
}

__RT_VISIBILITY
int softboundcets_strfromf64(char *dest, size_t size, char *format, _Float64 f) {
  CHECK_PTR_STORE(0, dest, size);
  CHECK_STRING_LOAD(1, format);

  return strfromf64(dest, size, format, f);
}

__RT_VISIBILITY
int softboundcets_strfromf64x(char *dest, size_t size, char *format, _Float64x f) {
  CHECK_PTR_STORE(0, dest, size);
  CHECK_STRING_LOAD(1, format);

  return strfromf64x(dest, size, format, f);
}

__RT_VISIBILITY
int softboundcets_strfroml(char *dest, size_t size, char *format, long double f) {
  CHECK_PTR_STORE(0, dest, size);
  CHECK_STRING_LOAD(1, format);

  return strfroml(dest, size, format, f);
}

__RT_VISIBILITY
double softboundcets_strtod_l(char *nptr, char **endptr, locale_t locale) {
  CHECK_STRING_LOAD(0, nptr);
  CHECK_PTR_STORE_NULLABLE(1, endptr, sizeof(char*));

  if (endptr != nullptr) {
    // If not null, endptr will point into the same buffer as nptr, even on error
    __softboundcets_metadata_store(*endptr, nptr_base, nptr_bound, nptr_key, nptr_lock);
  }

  return strtod_l(nptr, endptr, locale);
}

__RT_VISIBILITY
float softboundcets_strtof(char *nptr, char **endptr) {
  CHECK_STRING_LOAD(0, nptr);
  CHECK_PTR_STORE_NULLABLE(1, endptr, sizeof(char*));

  if (endptr != nullptr) {
    // If not null, endptr will point into the same buffer as nptr, even on error
    __softboundcets_metadata_store(*endptr, nptr_base, nptr_bound, nptr_key, nptr_lock);
  }

  return strtof(nptr, endptr);
}

/*
__RT_VISIBILITY
_Float128 softboundcets_strtof128(char *nptr, char **endptr) {
  CHECK_STRING_LOAD(0, nptr);
  CHECK_PTR_STORE_NULLABLE(1, endptr, sizeof(char*));

  if (endptr != nullptr) {
    // If not null, endptr will point into the same buffer as nptr, even on error
    __softboundcets_metadata_store(*endptr, nptr_base, nptr_bound, nptr_key, nptr_lock);
  }

  return strtof128(nptr, endptr);
}

__RT_VISIBILITY
_Float128 softboundcets_strtof128_l(char *nptr, char **endptr, locale_t locale) {
  CHECK_STRING_LOAD(0, nptr);
  CHECK_PTR_STORE_NULLABLE(1, endptr, sizeof(char*));

  if (endptr != nullptr) {
    // If not null, endptr will point into the same buffer as nptr, even on error
    __softboundcets_metadata_store(*endptr, nptr_base, nptr_bound, nptr_key, nptr_lock);
  }

  return strtof128_l(nptr, endptr, locale);
}
*/

__RT_VISIBILITY
_Float32 softboundcets_strtof32(char *nptr, char **endptr) {
  CHECK_STRING_LOAD(0, nptr);
  CHECK_PTR_STORE_NULLABLE(1, endptr, sizeof(char*));

  if (endptr != nullptr) {
    // If not null, endptr will point into the same buffer as nptr, even on error
    __softboundcets_metadata_store(*endptr, nptr_base, nptr_bound, nptr_key, nptr_lock);
  }

  return strtof32(nptr, endptr);
}

__RT_VISIBILITY
_Float32 softboundcets_strtof32_l(char *nptr, char **endptr, locale_t locale) {
  CHECK_STRING_LOAD(0, nptr);
  CHECK_PTR_STORE_NULLABLE(1, endptr, sizeof(char*));

  if (endptr != nullptr) {
    // If not null, endptr will point into the same buffer as nptr, even on error
    __softboundcets_metadata_store(*endptr, nptr_base, nptr_bound, nptr_key, nptr_lock);
  }

  return strtof32_l(nptr, endptr, locale);
}

__RT_VISIBILITY
_Float32x softboundcets_strtof32x(char *nptr, char **endptr) {
  CHECK_STRING_LOAD(0, nptr);
  CHECK_PTR_STORE_NULLABLE(1, endptr, sizeof(char*));

  if (endptr != nullptr) {
    // If not null, endptr will point into the same buffer as nptr, even on error
    __softboundcets_metadata_store(*endptr, nptr_base, nptr_bound, nptr_key, nptr_lock);
  }

  return strtof32x(nptr, endptr);
}

__RT_VISIBILITY
_Float32x softboundcets_strtof32x_l(char *nptr, char **endptr, locale_t locale) {
  CHECK_STRING_LOAD(0, nptr);
  CHECK_PTR_STORE_NULLABLE(1, endptr, sizeof(char*));

  if (endptr != nullptr) {
    // If not null, endptr will point into the same buffer as nptr, even on error
    __softboundcets_metadata_store(*endptr, nptr_base, nptr_bound, nptr_key, nptr_lock);
  }

  return strtof32x_l(nptr, endptr, locale);
}

__RT_VISIBILITY
_Float64 softboundcets_strtof64(char *nptr, char **endptr) {
  CHECK_STRING_LOAD(0, nptr);
  CHECK_PTR_STORE_NULLABLE(1, endptr, sizeof(char*));

  if (endptr != nullptr) {
    // If not null, endptr will point into the same buffer as nptr, even on error
    __softboundcets_metadata_store(*endptr, nptr_base, nptr_bound, nptr_key, nptr_lock);
  }

  return strtof64(nptr, endptr);
}

__RT_VISIBILITY
_Float64 softboundcets_strtof64_l(char *nptr, char **endptr, locale_t locale) {
  CHECK_STRING_LOAD(0, nptr);
  CHECK_PTR_STORE_NULLABLE(1, endptr, sizeof(char*));

  if (endptr != nullptr) {
    // If not null, endptr will point into the same buffer as nptr, even on error
    __softboundcets_metadata_store(*endptr, nptr_base, nptr_bound, nptr_key, nptr_lock);
  }

  return strtof64_l(nptr, endptr, locale);
}

__RT_VISIBILITY
_Float64x softboundcets_strtof64x(char *nptr, char **endptr) {
  CHECK_STRING_LOAD(0, nptr);
  CHECK_PTR_STORE_NULLABLE(1, endptr, sizeof(char*));

  if (endptr != nullptr) {
    // If not null, endptr will point into the same buffer as nptr, even on error
    __softboundcets_metadata_store(*endptr, nptr_base, nptr_bound, nptr_key, nptr_lock);
  }

  return strtof64x(nptr, endptr);
}

__RT_VISIBILITY
_Float64x softboundcets_strtof64x_l(char *nptr, char **endptr, locale_t locale) {
  CHECK_STRING_LOAD(0, nptr);
  CHECK_PTR_STORE_NULLABLE(1, endptr, sizeof(char*));

  if (endptr != nullptr) {
    // If not null, endptr will point into the same buffer as nptr, even on error
    __softboundcets_metadata_store(*endptr, nptr_base, nptr_bound, nptr_key, nptr_lock);
  }

  return strtof64x_l(nptr, endptr, locale);
}

__RT_VISIBILITY
float softboundcets_strtof_l(char *nptr, char **endptr, locale_t locale) {
  CHECK_STRING_LOAD(0, nptr);
  CHECK_PTR_STORE_NULLABLE(1, endptr, sizeof(char*));

  if (endptr != nullptr) {
    // If not null, endptr will point into the same buffer as nptr, even on error
    __softboundcets_metadata_store(*endptr, nptr_base, nptr_bound, nptr_key, nptr_lock);
  }

  return strtof_l(nptr, endptr, locale);
}

__RT_VISIBILITY
long softboundcets_strtol_l(char *nptr, char **endptr, int base, locale_t locale) {
  CHECK_STRING_LOAD(0, nptr);
  CHECK_PTR_STORE_NULLABLE(1, endptr, sizeof(char*));

  if (endptr != nullptr) {
    // If not null, endptr will point into the same buffer as nptr, even on error
    __softboundcets_metadata_store(*endptr, nptr_base, nptr_bound, nptr_key, nptr_lock);
  }

  return strtol_l(nptr, endptr, base, locale);
}

__RT_VISIBILITY
long double softboundcets_strtold(char *nptr, char **endptr) {
  CHECK_STRING_LOAD(0, nptr);
  CHECK_PTR_STORE_NULLABLE(1, endptr, sizeof(char*));

  if (endptr != nullptr) {
    // If not null, endptr will point into the same buffer as nptr, even on error
    __softboundcets_metadata_store(*endptr, nptr_base, nptr_bound, nptr_key, nptr_lock);
  }

  return strtold(nptr, endptr);
}

__RT_VISIBILITY
long double softboundcets_strtold_l(char *nptr, char **endptr, locale_t locale) {
  CHECK_STRING_LOAD(0, nptr);
  CHECK_PTR_STORE_NULLABLE(1, endptr, sizeof(char*));

  if (endptr != nullptr) {
    // If not null, endptr will point into the same buffer as nptr, even on error
    __softboundcets_metadata_store(*endptr, nptr_base, nptr_bound, nptr_key, nptr_lock);
  }

  return strtold_l(nptr, endptr, locale);
}

__RT_VISIBILITY
long long softboundcets_strtoll(char *nptr, char **endptr, int base) {
  CHECK_STRING_LOAD(0, nptr);
  CHECK_PTR_STORE_NULLABLE(1, endptr, sizeof(char*));

  if (endptr != nullptr) {
    // If not null, endptr will point into the same buffer as nptr, even on error
    __softboundcets_metadata_store(*endptr, nptr_base, nptr_bound, nptr_key, nptr_lock);
  }

  return strtoll(nptr, endptr, base);
}

__RT_VISIBILITY
long long softboundcets_strtoll_l(char *nptr, char **endptr, int base, locale_t locale) {
  CHECK_STRING_LOAD(0, nptr);
  CHECK_PTR_STORE_NULLABLE(1, endptr, sizeof(char*));

  if (endptr != nullptr) {
    // If not null, endptr will point into the same buffer as nptr, even on error
    __softboundcets_metadata_store(*endptr, nptr_base, nptr_bound, nptr_key, nptr_lock);
  }

  return strtoll_l(nptr, endptr, base, locale);
}

__RT_VISIBILITY
long long softboundcets_strtoq(char *nptr, char **endptr, int base) {
  CHECK_STRING_LOAD(0, nptr);
  CHECK_PTR_STORE_NULLABLE(1, endptr, sizeof(char*));

  if (endptr != nullptr) {
    // If not null, endptr will point into the same buffer as nptr, even on error
    __softboundcets_metadata_store(*endptr, nptr_base, nptr_bound, nptr_key, nptr_lock);
  }

  return strtoq(nptr, endptr, base);
}

__RT_VISIBILITY
unsigned long softboundcets_strtoul_l(char *nptr, char **endptr, int base, locale_t locale) {
  CHECK_STRING_LOAD(0, nptr);
  CHECK_PTR_STORE_NULLABLE(1, endptr, sizeof(char*));

  if (endptr != nullptr) {
    // If not null, endptr will point into the same buffer as nptr, even on error
    __softboundcets_metadata_store(*endptr, nptr_base, nptr_bound, nptr_key, nptr_lock);
  }

  return strtoul_l(nptr, endptr, base, locale);
}

__RT_VISIBILITY
unsigned long long softboundcets_strtoull(char *nptr, char **endptr, int base) {
  CHECK_STRING_LOAD(0, nptr);
  CHECK_PTR_STORE_NULLABLE(1, endptr, sizeof(char*));

  if (endptr != nullptr) {
    // If not null, endptr will point into the same buffer as nptr, even on error
    __softboundcets_metadata_store(*endptr, nptr_base, nptr_bound, nptr_key, nptr_lock);
  }

  return strtoull(nptr, endptr, base);
}

__RT_VISIBILITY
unsigned long long softboundcets_strtoull_l(char *nptr, char **endptr, int base, locale_t locale) {
  CHECK_STRING_LOAD(0, nptr);
  CHECK_PTR_STORE_NULLABLE(1, endptr, sizeof(char*));

  if (endptr != nullptr) {
    // If not null, endptr will point into the same buffer as nptr, even on error
    __softboundcets_metadata_store(*endptr, nptr_base, nptr_bound, nptr_key, nptr_lock);
  }

  return strtoull_l(nptr, endptr, base, locale);
}

__RT_VISIBILITY
unsigned long long softboundcets_strtouq(char *nptr, char **endptr, int base) {
  CHECK_STRING_LOAD(0, nptr);
  CHECK_PTR_STORE_NULLABLE(1, endptr, sizeof(char*));

  if (endptr != nullptr) {
    // If not null, endptr will point into the same buffer as nptr, even on error
    __softboundcets_metadata_store(*endptr, nptr_base, nptr_bound, nptr_key, nptr_lock);
  }

  return strtouq(nptr, endptr, base);
}

__RT_VISIBILITY
size_t softboundcets_wcstombs(char *s, wchar_t *wstr, size_t n) {
  CHECK_PTR_STORE_NULLABLE(0, s, n);
  LOAD_PTR_BOUNDS(1, wstr);

#if __SOFTBOUNDCETS_CHECK_LOADS
  if (!wmemchr(wstr, L'\0', (wchar_t*)wstr_bound - (wchar_t*)wstr)) {
    __softboundcets_error_printf("In string load dereference check: base=%zx, bound=%zx, ptr=%zx",
      wstr_base, wstr_bound, wstr);
    __softboundcets_abort();
  }
#endif
  CHECK_PTR_ALIVE_LOAD(1, wstr);

  return wcstombs(s, wstr, n);
}

__RT_VISIBILITY
int softboundcets_wctomb(char *s, wchar_t wchar) {
  CHECK_PTR_LOAD_NULLABLE(0, s, MB_CUR_MAX);

  return wctomb(s, wchar);
}

__RT_VISIBILITY
void *softboundcets_reallocarray(void *ptr, size_t nmemb, size_t size) {
  LOAD_PTR_BOUNDS(1, ptr);
  LOAD_PTR_LOCK(1, ptr);
  // We do not check the pointer here since the allocator has its own metadata for that

  void *result = reallocarray(ptr, nmemb, size);

  if (result) {
    sbcets_base_t result_base = result;
    // This cannot overflow since reallocarray succeeded
    sbcets_bound_t result_bound = (char*)result + nmemb * size;
    sbcets_lock_t result_lock = nullptr;
    sbcets_key_t result_key = 0;
    if (ptr != result) {
      // We have reallocated
      if (ptr) {
        // Since ptr was not null, we must deallocate it
        __softboundcets_memory_deallocation(ptr_lock, ptr_key);
      }
      __softboundcets_memory_allocation(result, &result_lock, &result_key);
    } else {
      result_lock = ptr_lock;
      result_key = ptr_key;

      // Since the pointer was not moved, we need to update the bounds
      // TODO: Updating this on the shadow stack is correct, right?
      __softboundcets_store_bound_shadow_stack(result_bound, 1);
    }

    __softboundcets_store_return_metadata(result_base, result_bound, result_key, result_lock);
  } else {
    // If the reallocarray function returned NULL, the pointer may have been free'd if size was 0.
    // We also check if the pointer has a key value > 1 (0: not allocated, 1: global lock) in case
    // someone tried to deallocate a static variable.
    // TODO: Is this sufficient to check for errors?
    if (size == 0 && ptr_key > 1) {
      __softboundcets_memory_deallocation(ptr_lock, ptr_key);
    }

    __softboundcets_store_null_return_metadata();
  }

  return result;
}

// malloc.h

__RT_VISIBILITY
int softboundcets_malloc_info(int options, FILE *fp) {
  CHECK_PTR_LOAD(0, fp, sizeof(FILE));

  return malloc_info(options, fp);
}

__RT_VISIBILITY
size_t softboundcets_malloc_usable_size(void *ptr) {
  CHECK_PTR_ALIVE_LOAD_NULLABLE(0, ptr);

  return malloc_usable_size(ptr);
}

__RT_VISIBILITY
void *softboundcets_memalign(size_t alignment, size_t size) {
  void *result = memalign(alignment, size);

  if (result) {
    sbcets_lock_t result_lock = nullptr;
    sbcets_key_t result_key = 0;
    __softboundcets_memory_allocation(result, &result_lock, &result_key);

    __softboundcets_store_return_metadata(result, (char*)result + size, result_key, result_lock);
  } else {
    __softboundcets_store_null_return_metadata();
  }

  return result;
}

__RT_VISIBILITY
void *softboundcets_pvalloc(size_t size) {
  void *result = pvalloc(size);

  size_t page_size = sysconf(_SC_PAGESIZE);
  size_t real_size = size;

  // I'm not sure if this can ever be zero, but just in case...
  if (page_size) {
    // Round up to next multiple of page size
    real_size = ((size + page_size - 1) / page_size) * page_size;
  }

  if (result) {
    sbcets_lock_t result_lock = nullptr;
    sbcets_key_t result_key = 0;
    __softboundcets_memory_allocation(result, &result_lock, &result_key);

    __softboundcets_store_return_metadata(result, (char*)result + real_size, result_key,
                                          result_lock);
  } else {
    __softboundcets_store_null_return_metadata();
  }

  return result;
}

__RT_VISIBILITY
void *softboundcets_valloc(size_t size) {
  void *result = valloc(size);

  if (result) {
    sbcets_lock_t result_lock = nullptr;
    sbcets_key_t result_key = 0;
    __softboundcets_memory_allocation(result, &result_lock, &result_key);

    __softboundcets_store_return_metadata(result, (char*)result + size, result_key, result_lock);
  } else {
    __softboundcets_store_null_return_metadata();
  }

  return result;
}
