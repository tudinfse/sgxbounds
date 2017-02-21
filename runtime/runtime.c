#ifdef __cplusplus
extern "C" {
#endif

#include <stdio.h>
#include <string.h>
#include <stdlib.h>
#include <stdint.h>
#include <assert.h>
#include <pthread.h>
#include <sys/mman.h>
#include "../include/common.h"

/* ------------------------------------------------------------------------- */
/* ------------------ Run-time macros to change behaviour ------------------ */
/* ------------------------------------------------------------------------- */
//#define SGXBOUNDS_BOUNDLESS 1  // comment out if only print error msg on out-of-bounds
#define SGXBOUNDS_STOPONERROR 1  // comment out if stop immediately on error

/* ------------------------------------------------------------------------- */
/* -------------------------- Local vars and types ------------------------- */
/* ------------------------------------------------------------------------- */
static PTRTYPE highest_bound = 0;

struct __sgxbounds_global_meta {
   void* lbnd;
   void* ubnd;
};

/* ------------------------------------------------------------------------- */
/* ---------------------- libc real funcs declarations --------------------- */
/* ------------------------------------------------------------------------- */
void *malloc_real(size_t size);
void free_real(void* ptr);
int memcmp_real(const void *vl, const void *vr, size_t n);
void *memset_real(void *dest, int c, size_t n);
int printf_real(const char *format, ...);
size_t strlen_real(const char *s);
extern char **environ;

// mem* func declarations required for our compiler pass
void *__sgxbound_memcpy(void *__restrict__ dest, const void *__restrict__ src, size_t n);
void *__sgxbound_memmove(void *dest, const void *src, size_t n);
void *__sgxbound_memset(void *dest, int c, size_t n);
size_t __sgxbound_strlen(const char *s);

/* ------------------------------------------------------------------------- */
/* ------------------------ Vector-of-pointers types ----------------------- */
/* ------------------------------------------------------------------------- */
// NOTE: vectors cannot be of pointer type, so we use uintptr_t
typedef uintptr_t vector2ptr __attribute__((__vector_size__(sizeof(uintptr_t) * 2))); // 128-bit SSE
typedef uintptr_t vector4ptr __attribute__((__vector_size__(sizeof(uintptr_t) * 4))); // 256-bit AVX

/* ------------------------------------------------------------------------- */
/* -------------------- LRU Cache for boundless memory --------------------- */
/* ------------------------------------------------------------------------- */
/* Works as follows:
 *   - we maintain a bounded LRU cache that redirects out-of-bounds accesses
 *     to a separate "overlay" memory area to prevent object corruption
 *   - "overlay" memory is allocated on demand and can be max 1MB in size
 *   - LRU cache is a hash table that maps [ ptrval & mask -> overlay chunk]
 *     - each overlay chunk is 1KB in size and is malloced on demand
 *     - we mask low bits of ptrval to get the key for hash table
 *     - we also memorize offset of ptrval from the mask-address and add it
 *       it later to the overlayed address to get real address
 *   - the cache is *not* performant and uses global pthread_mutex
 *   - in cases when we cannot read/write LRU cache, resort to failure-oblivious
 //    (write to dummy place, read dummy place with all zeros)
 */
// NOTE: adopted from http://jehiah.cz/a/uthash
#include "uthash.h"

#undef uthash_fatal
#undef uthash_malloc
#undef uthash_free
#undef uthash_strlen
#undef uthash_memcmp
#undef uthash_memset

#define uthash_fatal(msg)
#define uthash_malloc(sz)    malloc_real(sz)
#define uthash_free(ptr,sz)  free_real(ptr)
#define uthash_strlen(s)     strlen_real(s)
#define uthash_memcmp(a,b,n) memcmp_real(a,b,n)
#define uthash_memset(s,c,n) memset_real(s,c,n)

#define CACHE_ADDR_ALIGN (1ULL << 10)                    // 1KB alignment of chunks
#define MAX_CACHE_SIZE ((1024*1024)/CACHE_ADDR_ALIGN)    // X entries to store 1MB of data
#define CACHE_OFFSET_MASK (CACHE_ADDR_ALIGN - 1ULL)
#define CACHE_ADDR_MASK   (~CACHE_OFFSET_MASK)

struct CacheEntry {
  const void* key;    // out-of-bounds ptr value
  const void* value;  // real allocated 64B chunk (ptr to which mem access is redirected)
  UT_hash_handle hh;
};

static struct CacheEntry *cache = NULL;

static pthread_mutex_t cache_lock = PTHREAD_MUTEX_INITIALIZER;

static __attribute__((noinline)) const void* __sgxbounds_find_in_cache(const void *ptrval, size_t size) {
  const void* key  = (const void*) ((uintptr_t)ptrval & CACHE_ADDR_MASK);
  uintptr_t offset = (uintptr_t)ptrval & CACHE_OFFSET_MASK;

  const void* keyend = (const void*) ((uintptr_t)(ptrval + size) & CACHE_ADDR_MASK);
  if (key != keyend) {
    // mem access spans more than one CACHE_ADDR_ALIGN chunk, panic
    // TODO: support such mem accesses?
    return NULL;
  }

  struct CacheEntry *entry;
  const void* ret = NULL;

  pthread_mutex_lock(&cache_lock);
  HASH_FIND_PTR(cache, &key, entry);
  if (entry) {
    // remove it (so the subsequent add will throw it on the front of the list)
    HASH_DEL(cache, entry);
    HASH_ADD_PTR(cache, key, entry);
    ret = entry->value + offset;
  }
  pthread_mutex_unlock(&cache_lock);
  return ret;
}

static __attribute__((noinline)) const void* __sgxbounds_add_to_cache(const void *ptrval, size_t size) {
  const void* key  = (const void*) ((uintptr_t)ptrval & CACHE_ADDR_MASK);
  uintptr_t offset = (uintptr_t)ptrval & CACHE_OFFSET_MASK;

  const void* keyend = (const void*) ((uintptr_t)(ptrval + size) & CACHE_ADDR_MASK);
  if (key != keyend) {
    // mem access spans more than one CACHE_ADDR_ALIGN chunk, panic
    // TODO: support such mem accesses?
    return NULL;
  }

  struct CacheEntry *entry, *tmp_entry;
  entry = uthash_malloc(sizeof(struct CacheEntry));
  entry->key   = key;
  entry->value = uthash_malloc(CACHE_ADDR_ALIGN);
  // will return ptr into newly allocated 64B chunk
  const void* ret = entry->value + offset;

  pthread_mutex_lock(&cache_lock);
  HASH_ADD_PTR(cache, key, entry);
  // prune the cache to MAX_CACHE_SIZE
  if (HASH_COUNT(cache) > MAX_CACHE_SIZE) {
    HASH_ITER(hh, cache, entry, tmp_entry) {
      // prune the first entry (loop is based on insertion order so this
      // deletes the oldest item)
      HASH_DEL(cache, entry);
      free((void*)entry->value);
      free(entry);
      break;
    }
  }
  pthread_mutex_unlock(&cache_lock);
  return ret;
}

/* ------------------------------------------------------------------------- */
/* ------------------------ Out-of-bounds reaction ------------------------- */
/* ------------------------------------------------------------------------- */
static __attribute__((noinline))
void __sgxbounds_outofbounds_fail(const void* ptrval, size_t size, PTRTYPE lbnd, PTRTYPE ubnd) {
  printf_real("[SGXBOUNDS-ERROR] OUT-OF-BOUNDS ACCESS AT %p DETECTED (size=%lu, lbnd=%p, ubnd=%p)!\n", ptrval, size, lbnd, ubnd);
#ifdef SGXBOUNDS_STOPONERROR
  exit(254);
#endif
}

static __attribute__((noinline))
const int __sgxbounds_isfalsepositive(const void* ptrval) {
  // check for false positives due to `environ`
  uintptr_t ptrvalint = (uintptr_t) ptrval;
  size_t checklbnd, checkubnd;
  size_t i;
  for (i = 0; environ[i]; i++) {
    checklbnd = (uintptr_t)environ[i];
    checkubnd = checklbnd + strlen_real(environ[i]);
    if (ptrvalint >= checklbnd && ptrvalint < checkubnd)
      return 1;
  }
  checklbnd = (uintptr_t)&environ[0];
  checkubnd = checklbnd + (i+1)*sizeof(char*);
  if (ptrvalint >= checklbnd && ptrvalint < checkubnd)
    return 1;
  return 0;
}

static __attribute__((noinline))
const void* __sgxbounds_outofbounds(const void* ptrval, size_t size, PTRTYPE lbnd, PTRTYPE ubnd, int accesstype) {
  if (__sgxbounds_isfalsepositive(ptrval))
    return ptrval;

#ifndef SGXBOUNDS_BOUNDLESS
  __sgxbounds_outofbounds_fail(ptrval, size, lbnd, ubnd);
#else
  // boundless approach to tolerance: try to read from/write to separate LRU cache
  printf_real("[sgxbounds-info] TOLERATING OUT-OF-BOUNDS ACCESS AT %p\n", ptrval);
  switch (accesstype) {
    case SGXBOUNDS_RDACCESS:
    {
      // if this out-of-bounds ptrval is in LRU cache, use its "real" address
      const void* realptr = __sgxbounds_find_in_cache(ptrval, size);
      if (realptr)  return realptr;
      // not found in LRU cache, resort to failure-oblivious (dummy read)
      return (const void*)(uintptr_t)(highest_bound + 1024);
    }

    case SGXBOUNDS_WRACCESS:
    case SGXBOUNDS_RDWRACCESS:
    {
      // if this out-of-bounds ptrval is in LRU cache, use its "real" address
      const void* realptr = __sgxbounds_find_in_cache(ptrval, size);
      if (realptr)  return realptr;
      // not found in LRU cache, try to allocate more memory for a write
      const void* newptr = __sgxbounds_add_to_cache(ptrval, size);
      if (newptr)   return newptr;
      // cannot even add to cache, resort to failure-oblivious (dummy write)
      return (const void*)(uintptr_t)(highest_bound + 2048);
    }

    case SGXBOUNDS_DEFACCESS:
      return ptrval; // allow to continue; TODO: need to react on bad inline asm
  }
#endif
  return ptrval;
}

/* ------------------------------------------------------------------------- */
/* --------------------------- LLVM pass helpers --------------------------- */
/* ------------------------------------------------------------------------- */
#define INLINEATTR __attribute__((always_inline))

void* __sgxbounds_dummy_uses(void* dest, void* src, size_t n, int c) {
  // keeps declared __sgxbound_* funcs from being optimized out
  n = __sgxbound_strlen(dest);
  dest = __sgxbound_memcpy(dest, src, n);
  dest = __sgxbound_memmove(dest, src, n);
  dest = __sgxbound_memset(dest, c, n);
  return dest;
}

INLINEATTR void* __sgxbounds_extract_ptrval(const void* ptr) {
  void* ptrval = (void*) ((uintptr_t)ptr & PTRVALMASK);
  return ptrval;
}

INLINEATTR vector2ptr __sgxbounds_extract_ptrval_vector2(vector2ptr ptr) {
  vector2ptr mask   = {PTRVALMASK, PTRVALMASK};
  vector2ptr ptrval = ptr & mask;
  return ptrval;
}

INLINEATTR vector4ptr __sgxbounds_extract_ptrval_vector4(vector4ptr ptr) {
  vector4ptr mask   = {PTRVALMASK, PTRVALMASK, PTRVALMASK, PTRVALMASK};
  vector4ptr ptrval = ptr & mask;
  return ptrval;
}

INLINEATTR PTRTYPE __sgxbounds_extract_ubnd(const void* ptr) {
  PTRTYPE ubnd = ((uintptr_t)ptr & UPBNDMASK) >> PTRSIZEBITS;
  return ubnd;
}

INLINEATTR vector2ptr __sgxbounds_extract_ubnd_vector2(vector2ptr ptr) {
  vector2ptr mask = {UPBNDMASK, UPBNDMASK};
  vector2ptr bits = {PTRSIZEBITS, PTRSIZEBITS};
  vector2ptr ubnd = (ptr & mask) >> bits;
  return ubnd;
}

INLINEATTR vector4ptr __sgxbounds_extract_ubnd_vector4(vector4ptr ptr) {
  vector4ptr mask = {UPBNDMASK, UPBNDMASK, UPBNDMASK, UPBNDMASK};
  vector4ptr bits = {PTRSIZEBITS, PTRSIZEBITS, PTRSIZEBITS, PTRSIZEBITS};
  vector4ptr ubnd = (ptr & mask) >> bits;
  return ubnd;
}

INLINEATTR PTRTYPE __sgxbounds_extract_lbnd(PTRTYPE ubnd) {
  PTRTYPE lbnd = *((PTRTYPE*) (uintptr_t) ubnd);
  return lbnd;
}

INLINEATTR void* __sgxbounds_combine_ptr(const void* ptrval, PTRTYPE ubnd) {
  uintptr_t ptr = ((uintptr_t) ubnd << PTRSIZEBITS);
  ptr |= (uintptr_t) __sgxbounds_extract_ptrval(ptrval);
  return (void*) ptr;
}

INLINEATTR vector2ptr __sgxbounds_combine_ptr_vector2(vector2ptr ptrval, vector2ptr ubnd) {
  vector2ptr bits = {PTRSIZEBITS, PTRSIZEBITS};
  vector2ptr ptr  = ubnd << bits;
  ptr |= __sgxbounds_extract_ptrval_vector2(ptrval);
  return ptr;
}

INLINEATTR vector4ptr __sgxbounds_combine_ptr_vector4(vector4ptr ptrval, vector4ptr ubnd) {
  vector4ptr bits = {PTRSIZEBITS, PTRSIZEBITS, PTRSIZEBITS, PTRSIZEBITS};
  vector4ptr ptr  = ubnd << bits;
  ptr |= __sgxbounds_extract_ptrval_vector4(ptrval);
  return ptr;
}

INLINEATTR const void* __sgxbounds_check_allbnd(const void* ptrval, size_t size, PTRTYPE lbnd, PTRTYPE ubnd, int accesstype) {
  uintptr_t ptrvalint = (uintptr_t) ptrval;
  if (ptrvalint < lbnd || (ptrvalint + size) > ubnd)
    return __sgxbounds_outofbounds(ptrval, size, lbnd, ubnd, accesstype);
  return ptrval;
}

INLINEATTR const void* __sgxbounds_check_ubnd(const void* ptrval, size_t size, PTRTYPE ubnd, int accesstype) {
  uintptr_t ptrvalint = (uintptr_t) ptrval;
  if (size > MAXPTRVAL || (ptrvalint + size) > ubnd)
    return __sgxbounds_outofbounds(ptrval, size, 0xDEAD, ubnd, accesstype);
  return ptrval;
}

INLINEATTR const void* __sgxbounds_check_lbnd(const void* ptrval, PTRTYPE lbnd, int accesstype) {
  uintptr_t ptrvalint = (uintptr_t) ptrval;
  if (ptrvalint < lbnd)
    return __sgxbounds_outofbounds(ptrval, 0, lbnd, 0xDEAD, accesstype);
  return ptrval;
}

INLINEATTR void* __sgxbounds_alloca(const void* ptrval, PTRTYPE ubnd) {
  PTRTYPE* lbndaddr = (PTRTYPE*) (uintptr_t) ubnd;
  *lbndaddr = (PTRTYPE) (uintptr_t) ptrval;
  uintptr_t ptr = ((uintptr_t) ubnd << PTRSIZEBITS);
  ptr |= (uintptr_t) ptrval;
  return (void*) ptr;
}

INLINEATTR void* __sgxbounds_uninstrument(const void* ptr) {
    return __sgxbounds_extract_ptrval(ptr);
}

INLINEATTR void* __sgxbounds_uninstrument_check(const void* ptr, size_t* size) {
  PTRTYPE ubnd = __sgxbounds_extract_ubnd(ptr);
  PTRTYPE lbnd = __sgxbounds_extract_lbnd(ubnd);
  void* ptrval = __sgxbounds_extract_ptrval(ptr);

  uintptr_t ptrvalint = (uintptr_t) ptrval;
  if (*size > MAXPTRVAL || ptrvalint < lbnd || (ptrvalint + *size) > ubnd) {
    if (__sgxbounds_isfalsepositive(ptrval))
      return ptrval;

    __sgxbounds_outofbounds_fail(ptrval, *size, lbnd, ubnd);
    if (ptrvalint >= lbnd && ptrvalint < ubnd) {
      // ptr itself is inside of bounds, problem is size -> decrease to good
      *size = (size_t)(ubnd - ptrvalint);
    }
    else {
      // ptr is out of bounds, we're screwed, signal caller about it
      *size = 0;
    }
  }
  return ptrval;
}

INLINEATTR void __sgxbounds_check_funcptr(const void* ptrval) {
#if 0
  if (((uintptr_t)ptrval & PTRVALMASK) == 0)
    printf_real("[SGXBOUNDS] SUSPISIOUS FUNCTION POINTER CALL TO %p DETECTED!\n", ptrval);
#endif
}

/* ------------------------------------------------------------------------- */
/* ----------------------------- special funcs ----------------------------- */
/* ------------------------------------------------------------------------- */
void *memcpy_real(void *__restrict__ s1, const void *__restrict__ s2, size_t n);

/* these funcs rely on libc wrappers */
char** __sgxbounds_instrument_argv(int argc, char** argv) {
    int i;

    // NOTE: C standard requires that argv[argc] = NULL
    char** fat_argv = (char**) malloc(sizeof(char*) * (argc+1));
    char** fat_argv_val = (char**) __sgxbounds_extract_ptrval(fat_argv);
    for (i = 0; i < argc; i++) {
        size_t l = strlen(argv[i]) + 1;  // one for trailing null

        fat_argv_val[i] = (char*) malloc(l);
        void* fat_argv_val_i = __sgxbounds_extract_ptrval(fat_argv_val[i]);
        memcpy_real(fat_argv_val_i, argv[i], l);
    }
    fat_argv_val[argc] = NULL;
    return fat_argv;
}

// all stores to `environ` are replaced by call to this func (see compiler pass)
void __sgxbounds_assign_environ(void* inenv) {
  char** newenv = (char**) inenv;
  int i;
  newenv = __sgxbounds_uninstrument(newenv);
  for (i = 0; newenv[i]; i++)
    newenv[i] = __sgxbounds_uninstrument(newenv[i]);
  environ = newenv;
}

/* ------------------------------------------------------------------------- */
/* ------------------------------- init funcs ------------------------------ */
/* ------------------------------------------------------------------------- */
void *mmap_real(void *start, size_t len, int prot, int flags, int fd, off_t off);
void* get_heap_end();

INLINEATTR PTRTYPE __sgxbounds_highest_bound() {
  return highest_bound;
}

INLINEATTR vector2ptr __sgxbounds_highest_bound_vector2() {
  vector2ptr ptr = {highest_bound, highest_bound};
  return ptr;
}

INLINEATTR vector4ptr __sgxbounds_highest_bound_vector4() {
  vector4ptr ptr = {highest_bound, highest_bound, highest_bound, highest_bound};
  return ptr;
}

// __sgxbounds_globals array is created and filled up by compiler pass
void __sgxbounds_globals_init(void* p, size_t n) {
    struct __sgxbounds_global_meta* __sgxbounds_globals = (struct __sgxbounds_global_meta*)p;

    size_t i;
    for (i = 0; i < n; i++) {
        PTRTYPE* lbndaddr = (PTRTYPE*) __sgxbounds_globals[i].ubnd;
        *lbndaddr = (PTRTYPE) (uintptr_t) __sgxbounds_globals[i].lbnd;
    }
}

__attribute__ ((constructor (0))) void __sgxbounds_init(void) {
    // LLVM compiler pass will insert call to __sgxbounds_globals_init

    // init highest_bound as the last available page
    uintptr_t heapend = (uintptr_t)get_heap_end();
    assert(heapend <= (MAXPTRVAL+1));
    heapend -= 4*1024; // one page
    void* ret = mmap_real((void*)heapend, 4*1024, PROT_READ | PROT_WRITE, MAP_PRIVATE | MAP_FIXED | MAP_ANONYMOUS, 0, 0);
    if (ret == MAP_FAILED) {
      printf_real("[SGXBOUNDS-ERROR] COULD NOT ALLOCATE HIGHEST BOUND AT %p!!!\n", (void*)heapend);
    } else {
      highest_bound = (PTRTYPE)(uintptr_t)ret;
//      printf_real("[sgxbounds-info] allocated highest bounds at %p (highest_bound = 0x%x, lowest_bound = 0x%x).\n", (void*)heapend, highest_bound, *((PTRTYPE*)(uintptr_t)highest_bound));
    }
}

#ifdef __cplusplus
}
#endif
