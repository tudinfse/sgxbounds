#ifdef __cplusplus
extern "C" {
#endif

#include <stdio.h>
#include <string.h>
#include <strings.h>
#include <stdlib.h>
#include <stdint.h>
#include <assert.h>
#include <stdarg.h>
#include <errno.h>
#include <fcntl.h>
#include <unistd.h>
#include <limits.h>
#include <time.h>
#include <utime.h>
#include <dirent.h>
#include <setjmp.h>
#include <mntent.h>
#include <libgen.h>
#include <getopt.h>
#include <ftw.h>
#include <poll.h>
#include <pthread.h>
#include <libintl.h>
#include <nl_types.h>
#include <iconv.h>
#include <locale.h>
#include <langinfo.h>
#include <monetary.h>
#include <wchar.h>
#include <semaphore.h>
#include <netdb.h>
#include <ifaddrs.h>
#include <grp.h>
#include <pwd.h>
#include <shadow.h>
#include <signal.h>
#include <sys/uio.h>
#include <sys/time.h>
#include <sys/times.h>
#include <sys/timeb.h>
#include <sys/types.h>
#include <sys/stat.h>
#include <sys/vfs.h>
#include <sys/statvfs.h>
#include <sys/resource.h>
#include <sys/utsname.h>
#include <sys/select.h>
#include <sys/socket.h>
#include <sys/epoll.h>
#include <sys/sem.h>
#include <netinet/in.h>
#include <net/if.h>
#include <arpa/inet.h>

#define weak_alias(old, new) extern __typeof(old) new __attribute__((weak, alias(#old)))

#define PAGE_SIZE 4096
#define PTRSIZE 4
#define PTRTYPE uint32_t
#define PTRSIZEBITS PTRSIZE*8
#define PTRVALMASK ((1ULL << PTRSIZEBITS) - 1ULL)
#define UPBNDMASK  (~((1ULL << PTRSIZEBITS) - 1ULL))
#define MAXPTRVAL PTRVALMASK

#define INLINEATTR __attribute__((always_inline))

/* ------------------------------------------------------------------------- */
/* ------------------ Run-time macros to change behaviour ------------------ */
/* ------------------------------------------------------------------------- */
//#define SGXBOUNDS_ZERO_ON_ERROR 1  // comment out if want at least partial results

/* ------------------------------------------------------------------------- */
/* --------------------------- SGXBounds helpers --------------------------- */
/* ------------------------------------------------------------------------- */
INLINEATTR void* __sgxbounds_uninstrument(const void* ptr);
INLINEATTR void* __sgxbounds_uninstrument_check(const void* ptr, size_t* size);
INLINEATTR PTRTYPE __sgxbounds_extract_ubnd(const void* ptr);
INLINEATTR void* __sgxbounds_combine_ptr(const void* ptrval, PTRTYPE ubnd);
INLINEATTR PTRTYPE __sgxbounds_highest_bound();

int printf_real(const char *__restrict format, ...);
__attribute__((noinline)) void __sgxbounds_printptr(const char* str, const void* ptr) {
    str = __sgxbounds_uninstrument(str);
    long long unsigned ptrint = (long long unsigned) ptr;
    printf_real("[sgxbounds info] %s = %llx\n", str, ptrint);
}


// TODOs:
//   - currently we only uninstrument, must also sgxbounds-check
//       - done for most important (mem*) funcs via __sgxbounds_uninstrument_check
//   - environ variable is uninstrumented: must deal with accesses to it
//       - done in a hacky way (environ is always uninstrumented)
//   - currently ignore widechar versions of functions (e.g., wcstod, wprintf)
//
//   - high priority: linux,
//                    search, regex,
//   - low  priority: complex (?), conf, crypt, ctype (?), math,
//                    sched,
//   - zero priority: fenv (?), ldso, legacy, mq, multibyte, process,
//                    termios, tsxqueue
//
// DONE: fcntl, malloc, mman, stdlib, string, unistd, stdio, time, env, errno,
//       stat, exit, prng, dirent, setjmp, misc, select, thread, locale, network,
//       temp, passwd, signal, ipc

// NOTE: we use `0` in high bits to indicate NULL (always-failing) bounds;
//       this should work fine -- we do not have legacy uninstrumented funcs

/* ------------------------------------------------------------------------- */
/* --------------------------- memory allocation --------------------------- */
/* ------------------------------------------------------------------------- */
void *malloc_real(size_t size);
void* calloc_real(size_t n_elements, size_t element_size);
void* realloc_real(void* p, size_t n);
void* memalign_real(size_t alignment, size_t n);
int posix_memalign_real(void** pp, size_t alignment, size_t n);
void* valloc_real(size_t size);
void* pvalloc_real(size_t size);
void free_real(void* ptr);

void *mmap_real(void *start, size_t len, int prot, int flags, int fd, off_t off);
int mprotect_real(void *addr, size_t len, int prot);
int madvise_real(void *addr, size_t len, int advice);
int mincore_real(void *addr, size_t len, unsigned char *vec);
int munmap_real(void *start, size_t len);

static inline uintptr_t specifyupbound(uintptr_t ptrint, size_t size) {
    // calculate upper bound
    uintptr_t upbnd = ptrint + size;
    assert(upbnd <= MAXPTRVAL);
    // save lower bound right after allocated object
    PTRTYPE* lobndaddr = (PTRTYPE*) upbnd;
    *lobndaddr = ptrint;
    return upbnd;
}

static inline void* makefatptr(uintptr_t ptrint, uintptr_t upbnd) {
    // add upper bound in upper bits of ptr
    ptrint |= upbnd << PTRSIZEBITS;
    return (void*) ptrint;
}

static inline void* specifybounds(void* ptr, size_t size) {
    uintptr_t ptrint = (uintptr_t) ptr;
    uintptr_t upbnd = specifyupbound(ptrint, size);
    return makefatptr(ptrint, upbnd);
}

void* malloc(size_t size) {
    if (size == 0) {
        // comply with musl which returns some (unaccessible) address
        return malloc_real(size);
    }
    void* ptr = malloc_real(size + PTRSIZE);
    if (ptr)
        ptr = specifybounds(ptr, size);
    return ptr;
}

void* calloc(size_t n_elements, size_t element_size) {
    if (n_elements == 0 || element_size == 0) {
        // comply with musl which returns some (unaccessible) address
        return calloc_real(n_elements, element_size);
    }
    size_t add = (element_size >= PTRSIZE) ? 1 : (PTRSIZE/element_size + 1);
    void* ptr = calloc_real(n_elements + add, element_size);
    if (ptr)
        ptr = specifybounds(ptr, n_elements * element_size);
    return ptr;
}

void* realloc(void* p, size_t n) {
    if (n == 0) {
        // comply with musl which returns some (unaccessible) address
        return realloc_real(p, n);
    }
    if (p)  p = __sgxbounds_uninstrument(p);
    void* ptr = realloc_real(p, n + PTRSIZE);
    if (ptr)
        ptr = specifybounds(ptr, n);
    return ptr;
}

void* memalign(size_t alignment, size_t n) {
    if (n == 0) {
        // comply with musl which returns some (unaccessible) address
        return memalign_real(alignment, n);
    }
    void* ptr = memalign_real(alignment, n + PTRSIZE);
    if (ptr)
        ptr = specifybounds(ptr, n);
    return ptr;
}

int posix_memalign(void** pp, size_t alignment, size_t n) {
    if (n == 0) {
        // comply with musl which returns some (unaccessible) address
        return posix_memalign_real(pp, alignment, n);
    }
    if (pp)  pp = __sgxbounds_uninstrument(pp);
    int ret = posix_memalign_real(pp, alignment, n + PTRSIZE);
    *pp = specifybounds(*pp, n);
    return ret;
}

void* valloc(size_t size) {
    if (size == 0) {
        // comply with musl which returns some (unaccessible) address
        return valloc_real(size);
    }
    void* ptr = valloc_real(size + PTRSIZE);
    if (ptr)
        ptr = specifybounds(ptr, size);
    return ptr;
}

void* pvalloc(size_t size) {
    if (size == 0) {
        // comply with musl which returns some (unaccessible) address
        return pvalloc_real(size);
    }
    void* ptr = pvalloc_real(size + PTRSIZE);
    if (ptr)
        ptr = specifybounds(ptr, size);
    return ptr;
}

void free(void* ptr) {
    if (ptr)  ptr = __sgxbounds_uninstrument(ptr);
    free_real(ptr);
}

void *mmap(void *start, size_t len, int prot, int flags, int fd, off_t off) {
    void* startval = NULL;
    if (start)  startval = __sgxbounds_uninstrument(start);
    void* ptr = mmap_real(startval, len + PTRSIZE, prot, flags, fd, off);
    if (ptr)
        ptr = specifybounds(ptr, len);
    return ptr;
}

void *mmap64(void *start, size_t len, int prot, int flags, int fd, off_t off) {
    return mmap(start, len, prot, flags, fd, off);
}

void *mremap(void *old_addr, size_t old_len, size_t new_len, int flags, ...) {
    assert(0 && "mremap is not implemented in SGXBounds!");
    exit(42);
    return NULL;
}

int mprotect(void *addr, size_t len, int prot) {
    if (addr)  addr = __sgxbounds_uninstrument(addr);
    return mprotect_real(addr, len + PTRSIZE, prot);
}

int madvise(void *addr, size_t len, int advice) {
    if (addr)  addr = __sgxbounds_uninstrument(addr);
    return madvise_real(addr, len + PTRSIZE, advice);
}

int mincore(void *addr, size_t len, unsigned char *vec) {
    if (addr)  addr = __sgxbounds_uninstrument(addr);
    if (vec)   vec  = __sgxbounds_uninstrument(vec);
    return mincore_real(addr, len + PTRSIZE, vec);
}

int munmap(void *start, size_t len) {
    if (start)  start = __sgxbounds_uninstrument(start);
    return munmap_real(start, len + PTRSIZE);
}

int munmap64(void *start, size_t len) {
    return munmap(start, len);
}

/* ------------------------------------------------------------------------- */
/* ---------------------------- memory movements --------------------------- */
/* ------------------------------------------------------------------------- */
void *memcpy_real(void *__restrict__ dest, const void *__restrict__ src, size_t n);
void *memmove_real(void *dest, const void *src, size_t n);
void *memset_real(void *dest, int c, size_t n);
void bzero_real(void *s, size_t n);
int bcmp_real(const void *s1, const void *s2, size_t n);
void bcopy_real(const void *s1, void *s2, size_t n);
void *memccpy_real(void *__restrict__ dest, const void *__restrict__ src, int c, size_t n);
void *memchr_real(const void *src, int c, size_t n);
int memcmp_real(const void *vl, const void *vr, size_t n);
void *memmem_real(const void *h0, size_t k, const void *n0, size_t l);
void *mempcpy_real(void *dest, const void *src, size_t n);
void *memrchr_real(const void *m, int c, size_t n);

void *memcpy(void *__restrict__ dest, const void *__restrict__ src, size_t n) {
    void* ret = dest;
    size_t oldn = n;
    if (dest) dest = __sgxbounds_uninstrument_check(dest, &n);
    if (src)  src  = __sgxbounds_uninstrument_check(src, &n);
    memcpy_real(dest, src, n);
#ifdef SGXBOUNDS_ZERO_ON_ERROR
    if (oldn > n) {
        PTRTYPE ubnd = __sgxbounds_extract_ubnd(ret);
        PTRTYPE rest = (ubnd - (uintptr_t)dest) - n;
        bzero_real(dest+n, rest);
    }
#endif
    return ret;
}

void *memmove(void *dest, const void *src, size_t n) {
    void* ret = dest;
    size_t oldn = n;
    if (dest) dest = __sgxbounds_uninstrument_check(dest, &n);
    if (src)  src  = __sgxbounds_uninstrument_check(src, &n);
    memmove_real(dest, src, n);
#ifdef SGXBOUNDS_ZERO_ON_ERROR
    if (oldn > n) {
        PTRTYPE ubnd = __sgxbounds_extract_ubnd(ret);
        PTRTYPE rest = (ubnd - (uintptr_t)dest) - n;
        bzero_real(dest+n, rest);
    }
#endif
    return ret;
}

void *memset(void *dest, int c, size_t n) {
    void* ret = dest;
    size_t oldn = n;
    if (dest) dest = __sgxbounds_uninstrument_check(dest, &n);
    memset_real(dest, c, n);
    return ret;
}

void bzero(void *s, size_t n) {
    size_t oldn = n;
    if (s)  s = __sgxbounds_uninstrument_check(s, &n);
    bzero_real(s, n);
}

int bcmp(const void *s1, const void *s2, size_t n) {
    if (s1)  s1 = __sgxbounds_uninstrument_check(s1, &n);
    if (s2)  s2 = __sgxbounds_uninstrument_check(s2, &n);
    return bcmp_real(s1, s2, n);
}

void bcopy(const void *s1, void *s2, size_t n) {
    void* olds2 = s2;
    size_t oldn = n;
    if (s1)  s1 = __sgxbounds_uninstrument_check(s1, &n);
    if (s2)  s2 = __sgxbounds_uninstrument_check(s2, &n);
    bcopy_real(s1, s2, n);
#ifdef SGXBOUNDS_ZERO_ON_ERROR
    if (oldn > n)  bzero_real(s2, __sgxbounds_extract_ubnd(olds2));
#endif
}

void *memccpy(void *__restrict__ dest, const void *__restrict__ src, int c, size_t n) {
    PTRTYPE ubnd = __sgxbounds_extract_ubnd(dest);
    size_t oldn = n;
    if (dest)  dest = __sgxbounds_uninstrument_check(dest, &n);
    if (src)   src  = __sgxbounds_uninstrument_check(src, &n);
    void* ptr = memccpy_real(dest, src, c, n);
    if (ptr) {
        // ptr points into dest, so it has the same bounds as dest
        ptr = __sgxbounds_combine_ptr(ptr, ubnd);
    }
#ifdef SGXBOUNDS_ZERO_ON_ERROR
    if (oldn > n)  bzero_real(dest, ubnd);
#endif
    return ptr;
}

void *memchr(const void *src, int c, size_t n) {
    PTRTYPE ubnd = __sgxbounds_extract_ubnd(src);
    size_t oldn = n;
    if (src)  src  = __sgxbounds_uninstrument_check(src, &n);
    char* ptr = memchr_real(src, c, n);
    if (ptr) {
        // ptr points into src, so it has the same bounds as src
        ptr = __sgxbounds_combine_ptr(ptr, ubnd);
    }
    return ptr;
}

int memcmp(const void *vl, const void *vr, size_t n) {
    if (vl)  vl  = __sgxbounds_uninstrument_check(vl, &n);
    if (vr)  vr  = __sgxbounds_uninstrument_check(vr, &n);
    return memcmp_real(vl, vr, n);
}

void *memmem(const void *h0, size_t k, const void *n0, size_t l) {
    PTRTYPE ubnd = __sgxbounds_extract_ubnd(h0);
    if (h0)  h0  = __sgxbounds_uninstrument_check(h0, &k);
    if (n0)  n0  = __sgxbounds_uninstrument_check(n0, &l);
    void* ptr = memmem_real(h0, k, n0, l);
    if (ptr) {
        // ptr points into h0, so it has the same bounds as h0
        ptr = __sgxbounds_combine_ptr(ptr, ubnd);
    }
    return ptr;
}

void *mempcpy(void *dest, const void *src, size_t n) {
    PTRTYPE ubnd = __sgxbounds_extract_ubnd(dest);
    size_t oldn = n;
    if (dest)  dest = __sgxbounds_uninstrument_check(dest, &n);
    if (src)   src  = __sgxbounds_uninstrument_check(src, &n);
    void* ptr = mempcpy_real(dest, src, n);
#ifdef SGXBOUNDS_ZERO_ON_ERROR
    if (oldn > n)  bzero_real(dest, ubnd);
#endif
    // ptr points into dest, so it has the same bounds as dest
    return __sgxbounds_combine_ptr(ptr, ubnd);
}

void *memrchr(const void *m, int c, size_t n) {
    PTRTYPE ubnd = __sgxbounds_extract_ubnd(m);
    if (m)  m  = __sgxbounds_uninstrument_check(m, &n);
    char* ptr = memrchr_real(m, c, n);
    if (ptr) {
        // ptr points into m, so it has the same bounds as m
        ptr = __sgxbounds_combine_ptr(ptr, ubnd);
    }
    return ptr;
}

weak_alias(memcpy, __sgxbound_memcpy);
weak_alias(memmove, __sgxbound_memmove);
weak_alias(memset, __sgxbound_memset);

/* ------------------------------------------------------------------------- */
/* ---------------------------- string functions --------------------------- */
/* ------------------------------------------------------------------------- */
struct charbuf {
    char buf[1020]; // hopefully enough for all kinds of strings
    PTRTYPE lbnd;
};

char *index_real(const char *s, int c);
char *rindex_real(const char *s, int c);
char *stpcpy_real(char *__restrict__ d, const char *__restrict__ s);
char *stpncpy_real(char *__restrict__ d, const char *__restrict__ s, size_t n);
int strcasecmp_real(const char *_l, const char *_r);
char *strcasestr_real(const char *h, const char *n);
char *strcat_real(char *__restrict__ dest, const char *__restrict__ src);
char *strchr_real(const char *s, int c);
char *strchrnul_real(const char *s, int c);
int strcmp_real(const char *l, const char *r);
char *strcpy_real(char *__restrict__ dest, const char *__restrict__ src);
size_t strcspn_real(const char *s, const char *c);
char *strdup_real(const char *s);
char *strerror_real(int errnum);
int strerror_r_real(int err, char *buf, size_t buflen);
int __xpg_strerror_r_real(int err, char *buf, size_t buflen);
size_t strlcat_real(char *d, const char *s, size_t n);
size_t strlcpy_real(char *d, const char *s, size_t n);
size_t strlen_real(const char *s);
int strncasecmp_real(const char *l, const char *r, size_t n);
char *strncat_real(char *__restrict__ d, const char *__restrict__ s, size_t n);
int strncmp_real(const char *l, const char *r, size_t n);
char *strncpy_real(char *__restrict__ d, const char *__restrict__ s, size_t n);
char *strndup_real(const char *s, size_t n);
size_t strnlen_real(const char *s, size_t n);
char *strpbrk_real(const char *s, const char *b);
char *strrchr_real(const char *s, int c);
char *strsep_real(char **str, const char *sep);
char *strsignal_real(int signum);
size_t strspn_real(const char *s, const char *c);
char *strstr_real(const char *h, const char *n);
char *strtok_real(char *__restrict__ s, const char *__restrict__ sep);
char *strtok_r_real(char *__restrict__ s, const char *__restrict__ sep, char **__restrict__ p);
int strverscmp_real(const char *l, const char *r);
void swab_real(const void *__restrict__ src, void *__restrict__ dest, ssize_t n);

char *index(const char *s, int c) {
    char* sval = __sgxbounds_uninstrument(s);
    char* ptr = index_real(sval, c);
    if (ptr) {
        // ptr points into s, so it has the same bounds as s
        PTRTYPE ubnd = __sgxbounds_extract_ubnd(s);
        ptr = __sgxbounds_combine_ptr(ptr, ubnd);
    }
    return ptr;
}

char *rindex(const char *s, int c) {
    char* sval = __sgxbounds_uninstrument(s);
    char* ptr = rindex_real(sval, c);
    if (ptr) {
        // ptr points into s, so it has the same bounds as s
        PTRTYPE ubnd = __sgxbounds_extract_ubnd(s);
        ptr = __sgxbounds_combine_ptr(ptr, ubnd);
    }
    return ptr;
}

char *stpcpy(char *__restrict__ d, const char *__restrict__ s) {
    char* dval = __sgxbounds_uninstrument(d);
    char* sval  = __sgxbounds_uninstrument(s);
    char* ptr = stpcpy_real(dval, sval);
    // ptr points into d, so it has the same bounds as d
    PTRTYPE ubnd = __sgxbounds_extract_ubnd(d);
    return __sgxbounds_combine_ptr(ptr, ubnd);
}

char *stpncpy(char *__restrict__ d, const char *__restrict__ s, size_t n) {
    char* dval = __sgxbounds_uninstrument(d);
    char* sval  = __sgxbounds_uninstrument(s);
    char* ptr = stpncpy_real(dval, sval, n);
    // ptr points into d, so it has the same bounds as d
    PTRTYPE ubnd = __sgxbounds_extract_ubnd(d);
    return __sgxbounds_combine_ptr(ptr, ubnd);
}

int strcasecmp(const char *l, const char *r) {
    l = __sgxbounds_uninstrument(l);
    r = __sgxbounds_uninstrument(r);
    return strcasecmp_real(l, r);
}

char *strcasestr(const char *h, const char *n) {
    char* hval = __sgxbounds_uninstrument(h);
    char* nval = __sgxbounds_uninstrument(n);
    char* ptr = strcasestr_real(hval, nval);
    if (ptr) {
        // ptr points into h, so it has the same bounds as h
        PTRTYPE ubnd = __sgxbounds_extract_ubnd(h);
        ptr = __sgxbounds_combine_ptr(ptr, ubnd);
    }
    return ptr;
}

char *strcat(char *__restrict__ dest, const char *__restrict__ src) {
    char* destval = __sgxbounds_uninstrument(dest);
    char* srcval  = __sgxbounds_uninstrument(src);
    strcat_real(destval, srcval);
    return dest;
}

char *strchr(const char *s, int c) {
    char* sval = __sgxbounds_uninstrument(s);
    char* ptr = strchr_real(sval, c);
    if (ptr) {
        // ptr points into s, so it has the same bounds as s
        PTRTYPE ubnd = __sgxbounds_extract_ubnd(s);
        ptr = __sgxbounds_combine_ptr(ptr, ubnd);
    }
    return ptr;
}

char *strchrnul(const char *s, int c) {
    char* sval = __sgxbounds_uninstrument(s);
    char* ptr = strchrnul_real(sval, c);
    // ptr points into s, so it has the same bounds as s
    PTRTYPE ubnd = __sgxbounds_extract_ubnd(s);
    return __sgxbounds_combine_ptr(ptr, ubnd);
}

int strcmp(const char *l, const char *r) {
    l = __sgxbounds_uninstrument(l);
    r = __sgxbounds_uninstrument(r);
    return strcmp_real(l, r);
}

char *strcpy(char *__restrict__ dest, const char *__restrict__ src) {
    char* destval = __sgxbounds_uninstrument(dest);
    char* srcval  = __sgxbounds_uninstrument(src);
    strcpy_real(destval, srcval);
    return dest;
}

size_t strcspn(const char *s, const char *c) {
    s = __sgxbounds_uninstrument(s);
    c = __sgxbounds_uninstrument(c);
    return strcspn_real(s, c);
}

void* __sgxbounds_memdup(const void *s, size_t size) {
    void* ptr = malloc_real(size + PTRSIZE);
    if (!ptr) return NULL;
    memcpy_real(ptr, s, size);
    ptr = specifybounds(ptr, size);
    return ptr;
}

char* __sgxbounds_strdup(const char *s) {
    size_t size = strlen_real(s) + 1;           // +1 for null terminator
    return __sgxbounds_memdup(s, size);
}

char *strdup(const char *s) {
    s = __sgxbounds_uninstrument(s);
    return __sgxbounds_strdup(s);
}

char *strerror(int errnum) {
    static struct charbuf buf = {.lbnd = 0};
    if (buf.lbnd == 0)  buf.lbnd = (PTRTYPE)&buf;
    char* ret = strerror_real(errnum);
    if (!ret) return NULL;
    strcpy_real(buf.buf, ret);
    return __sgxbounds_combine_ptr(&buf, (PTRTYPE)&(buf.lbnd));
}

int strerror_r(int err, char *buf, size_t buflen) {
    buf = __sgxbounds_uninstrument(buf);
    return strerror_r_real(err, buf, buflen);
}

int __xpg_strerror_r(int err, char *buf, size_t buflen) {
    buf = __sgxbounds_uninstrument(buf);
    return __xpg_strerror_r_real(err, buf, buflen);
}

size_t strlcat(char *d, const char *s, size_t n) {
    d = __sgxbounds_uninstrument(d);
    s = __sgxbounds_uninstrument(s);
    return strlcat_real(d, s, n);
}

size_t strlcpy(char *d, const char *s, size_t n) {
    d = __sgxbounds_uninstrument(d);
    s = __sgxbounds_uninstrument(s);
    return strlcpy_real(d, s, n);
}

size_t strlen(const char *s) {
    s = __sgxbounds_uninstrument(s);
    return strlen_real(s);
}

weak_alias(strlen, __sgxbound_strlen);

int strncasecmp(const char *l, const char *r, size_t n) {
    l = __sgxbounds_uninstrument(l);
    r = __sgxbounds_uninstrument(r);
    return strncasecmp_real(l, r, n);
}

char *strncat(char *__restrict__ d, const char *__restrict__ s, size_t n) {
    char* dval = __sgxbounds_uninstrument(d);
    char* sval  = __sgxbounds_uninstrument(s);
    strncat_real(dval, sval, n);
    return d;
}

int strncmp(const char *l, const char *r, size_t n) {
    l = __sgxbounds_uninstrument(l);
    r = __sgxbounds_uninstrument(r);
    return strncmp_real(l, r, n);
}

char *strncpy(char *__restrict__ d, const char *__restrict__ s, size_t n) {
    char* dval = __sgxbounds_uninstrument(d);
    char* sval  = __sgxbounds_uninstrument(s);
    strncpy_real(dval, sval, n);
    return d;
}

char *strndup(const char *s, size_t n) {
    s = __sgxbounds_uninstrument(s);
    size_t l = strnlen_real(s, n);
    char *d = malloc_real(l + 1 + PTRSIZE); // +1 for null terminator
    if (!d) return NULL;
    memcpy_real(d, s, l);
    d[l] = 0;
    d = specifybounds(d, l + 1);
    return d;
}

size_t strnlen(const char *s, size_t n) {
    s = __sgxbounds_uninstrument(s);
    return strnlen_real(s, n);
}

char *strpbrk(const char *s, const char *b) {
    char* sval = __sgxbounds_uninstrument(s);
    char* bval = __sgxbounds_uninstrument(b);
    char* ptr = strpbrk_real(sval, bval);
    if (ptr) {
        // ptr points into s, so it has the same bounds as s
        PTRTYPE ubnd = __sgxbounds_extract_ubnd(s);
        ptr = __sgxbounds_combine_ptr(ptr, ubnd);
    }
    return ptr;
}

char *strrchr(const char *s, int c) {
    char* sval = __sgxbounds_uninstrument(s);
    char* ptr = strrchr_real(sval, c);
    if (ptr) {
        // ptr points into s, so it has the same bounds as s
        PTRTYPE ubnd = __sgxbounds_extract_ubnd(s);
        ptr = __sgxbounds_combine_ptr(ptr, ubnd);
    }
    return ptr;
}

char *strsep(char **str, const char *sep) {
    str = (char **) __sgxbounds_uninstrument((void*) str);
    sep = (const char *) __sgxbounds_uninstrument((void*) sep);
    char *s = *str;
    if (!s) return NULL;
    *str = __sgxbounds_uninstrument(s);
    strsep_real(str, sep);
    if (*str) {
        // *str points into s, so it has the same bounds as s
        PTRTYPE ubnd = __sgxbounds_extract_ubnd(s);
        *str = __sgxbounds_combine_ptr(*str, ubnd);
    }
    return s;
}

char *strsignal(int signum) {
    static struct charbuf buf = {.lbnd = 0};
    if (buf.lbnd == 0)  buf.lbnd = (PTRTYPE)&buf;
    char* ret = strsignal_real(signum);
    if (!ret) return NULL;
    strcpy_real(buf.buf, ret);
    return __sgxbounds_combine_ptr(&buf, (PTRTYPE)&(buf.lbnd));
}

size_t strspn(const char *s, const char *c) {
    s = __sgxbounds_uninstrument(s);
    c = __sgxbounds_uninstrument(c);
    return strspn_real(s, c);
}

char *strstr(const char *h, const char *n) {
    char* hval = __sgxbounds_uninstrument(h);
    char* nval = __sgxbounds_uninstrument(n);
    char* ptr = strstr_real(hval, nval);
    if (ptr) {
        // ptr points into h, so it has the same bounds as h
        PTRTYPE ubnd = __sgxbounds_extract_ubnd(h);
        ptr = __sgxbounds_combine_ptr(ptr, ubnd);
    }
    return ptr;
}

char *strtok(char *__restrict__ s, const char *__restrict__ sep) {
    static PTRTYPE curr_ubnd = 0;
    char* sval = NULL;
    if (s) {
        // first invocation, memorize ubnd of s
        sval      = __sgxbounds_uninstrument(s);
        curr_ubnd = __sgxbounds_extract_ubnd(s);
    }
    sep = __sgxbounds_uninstrument(sep);
    char* ptr = strtok_real(sval, sep);
    if (ptr) {
        // ptr points into s from first invocation
        assert(curr_ubnd != 0);
        ptr = __sgxbounds_combine_ptr(ptr, curr_ubnd);
    }
    return ptr;
}

char *strtok_r(char *__restrict__ s, const char *__restrict__ sep, char **__restrict__ p) {
    PTRTYPE curr_ubnd = 0;
    char* sval = NULL;
    sep = __sgxbounds_uninstrument(sep);
    p   = __sgxbounds_uninstrument(p);
    if (s) {
        // first invocation
        curr_ubnd = __sgxbounds_extract_ubnd(s);
        sval = __sgxbounds_uninstrument(s);
    } else {
        // following invocations
        curr_ubnd = __sgxbounds_extract_ubnd(*p);
        *p = __sgxbounds_uninstrument(*p);
    }
    char* ptr = strtok_r_real(sval, sep, p);
    *p = __sgxbounds_combine_ptr(*p, curr_ubnd);
    if (ptr) {
        // ptr points into s, so it has the same bounds as s
        // (which value is memorized in curr_ubnd)
        assert(curr_ubnd != 0);
        ptr = __sgxbounds_combine_ptr(ptr, curr_ubnd);
    }
    return ptr;
}

int strverscmp(const char *l, const char *r) {
    l = __sgxbounds_uninstrument(l);
    r = __sgxbounds_uninstrument(r);
    return strverscmp_real(l, r);
}

void swab(const void *__restrict__ src, void *__restrict__ dest, ssize_t n) {
    if (n <= 0) return;
    src  = __sgxbounds_uninstrument(src);
    dest = __sgxbounds_uninstrument(dest);
    swab_real(src, dest, n);
}

/* ------------------------------------------------------------------------- */
/* ------------------------- file descriptor funcs ------------------------- */
/* ------------------------------------------------------------------------- */
int open_real(const char *filename, int flags, ...);
int open64_real(const char *filename, int flags, ...);
int openat_real(int fd, const char *filename, int flags, ...);
int openat64_real(int fd, const char *filename, int flags, ...);
int creat_real(const char *filename, mode_t mode);
int creat64_real(const char *filename, mode_t mode);
int access_real(const char *filename, int amode);
int acct_real(const char *filename);
int chdir_real(const char *path);
int chown_real(const char *path, uid_t uid, gid_t gid);
int lchown_real(const char *path, uid_t uid, gid_t gid);
char *ctermid_real(char *s);
int faccessat_real(int fd, const char *filename, int amode, int flag);
int fchownat_real(int fd, const char *path, uid_t uid, gid_t gid, int flag);
char *getcwd_real(char *buf, size_t size);
int getgroups_real(int count, gid_t list[]);
int gethostname_real(char *name, size_t len);
char *getlogin_real(void);
int getlogin_r_real(char *name, size_t size);
int link_real(const char *existing, const char *new);
int linkat_real(int fd1, const char *existing, int fd2, const char *new, int flag);
int pipe_real(int fd[2]);
int pipe2_real(int fd[2], int flag);
ssize_t pread_real(int fd, void *buf, size_t size, off_t ofs);
ssize_t pread64_real(int fd, void *buf, size_t size, off_t ofs);
ssize_t preadv_real(int fd, const struct iovec *iov, int count, off_t ofs);
ssize_t preadv64_real(int fd, const struct iovec *iov, int count, off_t ofs);
ssize_t pwrite_real(int fd, const void *buf, size_t size, off_t ofs);
ssize_t pwrite64_real(int fd, const void *buf, size_t size, off_t ofs);
ssize_t pwritev_real(int fd, const struct iovec *iov, int count, off_t ofs);
ssize_t pwritev64_real(int fd, const struct iovec *iov, int count, off_t ofs);
ssize_t read_real(int fd, void *buf, size_t count);
ssize_t readlink_real(const char *__restrict__ path, char *__restrict__ buf, size_t bufsize);
ssize_t readlinkat_real(int fd, const char *__restrict__ path, char *__restrict__ buf, size_t bufsize);
ssize_t readv_real(int fd, const struct iovec *iov, int count);
int renameat_real(int oldfd, const char *old, int newfd, const char *new);
int rmdir_real(const char *path);
int symlink_real(const char *existing, const char *new);
int symlinkat_real(const char *existing, int fd, const char *new);
int truncate_real(const char *path, off_t length);
int truncate64_real(const char *path, off_t length);
char *ttyname_real(int fd);
int ttyname_r_real(int fd, char *name, size_t size);
int unlink_real(const char *path);
int unlinkat_real(int fd, const char *path, int flag);
ssize_t write_real(int fd, const void *buf, size_t count);
ssize_t writev_real(int fd, const struct iovec *iov, int count);

// TODO: fcntl() from fcntl.c uses varargs; instrument similar to printf?

int open(const char *filename, int flags, ...) {
    filename = __sgxbounds_uninstrument(filename);
    mode_t mode = 0;
    if ((flags & O_CREAT) || (flags & O_TMPFILE) == O_TMPFILE) {
        va_list ap;
        va_start(ap, flags);
        mode = va_arg(ap, mode_t);
        va_end(ap);
        return open_real(filename, flags, mode);
    }
    return open_real(filename, flags);
}

int open64(const char *filename, int flags, ...) {
    filename = __sgxbounds_uninstrument(filename);
    mode_t mode = 0;
    if ((flags & O_CREAT) || (flags & O_TMPFILE) == O_TMPFILE) {
        va_list ap;
        va_start(ap, flags);
        mode = va_arg(ap, mode_t);
        va_end(ap);
        return open64_real(filename, flags, mode);
    }
    return open64_real(filename, flags);
}

int openat(int fd, const char *filename, int flags, ...) {
    filename = __sgxbounds_uninstrument(filename);
    mode_t mode = 0;
    if ((flags & O_CREAT) || (flags & O_TMPFILE) == O_TMPFILE) {
        va_list ap;
        va_start(ap, flags);
        mode = va_arg(ap, mode_t);
        va_end(ap);
        return openat_real(fd, filename, flags, mode);
    }
    return openat_real(fd, filename, flags);
}

int openat64(int fd, const char *filename, int flags, ...) {
    filename = __sgxbounds_uninstrument(filename);
    mode_t mode = 0;
    if ((flags & O_CREAT) || (flags & O_TMPFILE) == O_TMPFILE) {
        va_list ap;
        va_start(ap, flags);
        mode = va_arg(ap, mode_t);
        va_end(ap);
        return openat64_real(fd, filename, flags, mode);
    }
    return openat64_real(fd, filename, flags);
}

int creat(const char *filename, mode_t mode) {
    filename = __sgxbounds_uninstrument(filename);
    return creat_real(filename, mode);
}

int creat64(const char *filename, mode_t mode) {
    return creat(filename, mode);
}

int access(const char *filename, int amode) {
    filename = __sgxbounds_uninstrument(filename);
    return access_real(filename, amode);
}

int acct(const char *filename) {
    filename = __sgxbounds_uninstrument(filename);
    return acct_real(filename);
}

int chdir(const char *path) {
    path = __sgxbounds_uninstrument(path);
    return chdir_real(path);
}

int chown(const char *path, uid_t uid, gid_t gid) {
    path = __sgxbounds_uninstrument(path);
    return chown_real(path, uid, gid);
}

int lchown(const char *path, uid_t uid, gid_t gid) {
    path = __sgxbounds_uninstrument(path);
    return lchown_real(path, uid, gid);
}

char *ctermid(char *s) {
    // TODO: now it's suboptimal due to mem allocation on each call via strdup
    s = __sgxbounds_uninstrument(s);
    char* tmp = ctermid_real(s);
    if (!tmp) return NULL;
    return __sgxbounds_strdup(tmp);
}

int faccessat(int fd, const char *filename, int amode, int flag) {
    filename = __sgxbounds_uninstrument(filename);
    return faccessat_real(fd, filename, amode, flag);
}

int fchownat(int fd, const char *path, uid_t uid, gid_t gid, int flag) {
    path = __sgxbounds_uninstrument(path);
    return fchownat_real(fd, path, uid, gid, flag);
}

char *getcwd(char *buf, size_t size)
{
    if (buf) {
        // user supplied `buf` which is already instrumented:
        // uninstrument for real getcwd, but return `buf`
        char* bufval = __sgxbounds_uninstrument(buf);
        char* ret = getcwd_real(bufval, size);
        if (!ret) return 0;
        return buf;
    }
    // else no `buf` is supplied, use tmp for real getcwd
    // and copy it using our instrumented version of strdup
    char tmp[PATH_MAX];
    char* ret = getcwd_real(tmp, sizeof(tmp));
    if (!ret) return 0;
    return __sgxbounds_strdup(tmp);
}

int getgroups(int count, gid_t list[]) {
    // TODO: implement it?
    return -1;
}

int gethostname(char *name, size_t len) {
    name = __sgxbounds_uninstrument(name);
    return gethostname_real(name, len);
}

char *getlogin(void) {
    static struct charbuf buf = {.lbnd = 0};
    if (buf.lbnd == 0)  buf.lbnd = (PTRTYPE)&buf;
    char* ret = getlogin_real();
    if (!ret) return NULL;
    strcpy_real(buf.buf, ret);
    return __sgxbounds_combine_ptr(&buf, (PTRTYPE)&(buf.lbnd));
}

int getlogin_r(char *name, size_t size) {
    name = __sgxbounds_uninstrument(name);
    return getlogin_r_real(name, size);
}

int link(const char *existing, const char *new) {
    existing = __sgxbounds_uninstrument(existing);
    new = __sgxbounds_uninstrument(new);
    return link_real(existing, new);
}

int linkat(int fd1, const char *existing, int fd2, const char *new, int flag) {
    existing = __sgxbounds_uninstrument(existing);
    new = __sgxbounds_uninstrument(new);
    return linkat_real(fd1, existing, fd2, new, flag);
}

int pipe(int fd[2]) {
    int* fdval = (int*)__sgxbounds_uninstrument((void*) fd);
    return pipe_real(fdval);
}

int pipe2(int fd[2], int flag) {
    int* fdval = (int*)__sgxbounds_uninstrument((void*) fd);
    return pipe2_real(fdval, flag);
}

ssize_t pread(int fd, void *buf, size_t size, off_t ofs) {
    buf = __sgxbounds_uninstrument(buf);
    return pread_real(fd, buf, size, ofs);
}

ssize_t pread64(int fd, void *buf, size_t size, off_t ofs) {
    return pread(fd, buf, size, ofs);
}

ssize_t preadv(int fd, const struct iovec *iov, int count, off_t ofs) {
    int i;
    // uninstrument iov into iovval including its iov_base members
    struct iovec* iovval = malloc_real(count * sizeof(struct iovec));
    iov = __sgxbounds_uninstrument(iov);
    for (i = 0; i < count; i++) {
        iovval[i].iov_base = __sgxbounds_uninstrument(iov[i].iov_base);
        iovval[i].iov_len = iov[i].iov_len;
    }
    ssize_t ret = preadv_real(fd, iovval, count, ofs);
    free_real(iovval);
    return ret;
}

ssize_t preadv64(int fd, const struct iovec *iov, int count, off_t ofs) {
    return preadv(fd, iov, count, ofs);
}

ssize_t pwrite(int fd, const void *buf, size_t size, off_t ofs) {
    buf = __sgxbounds_uninstrument(buf);
    return pwrite_real(fd, buf, size, ofs);
}

ssize_t pwrite64(int fd, const void *buf, size_t size, off_t ofs) {
    return pwrite(fd, buf, size, ofs);
}

ssize_t write(int fd, const void *buf, size_t count) {
    buf = __sgxbounds_uninstrument(buf);
    return write_real(fd, buf, count);
}

ssize_t pwritev(int fd, const struct iovec *iov, int count, off_t ofs) {
    int i;
    // uninstrument iov into iovval including its iov_base members
    struct iovec* iovval = malloc_real(count * sizeof(struct iovec));
    iov = __sgxbounds_uninstrument(iov);
    for (i = 0; i < count; i++) {
        iovval[i].iov_base = __sgxbounds_uninstrument(iov[i].iov_base);
        iovval[i].iov_len = iov[i].iov_len;
    }
    ssize_t ret = pwritev_real(fd, iovval, count, ofs);
    free_real(iovval);
    return ret;
}

ssize_t pwritev64(int fd, const struct iovec *iov, int count, off_t ofs) {
    return pwritev(fd, iov, count, ofs);
}

ssize_t writev(int fd, const struct iovec *iov, int count) {
    int i;
    // uninstrument iov into iovval including its iov_base members
    struct iovec* iovval = malloc_real(count * sizeof(struct iovec));
    iov = __sgxbounds_uninstrument(iov);
    for (i = 0; i < count; i++) {
        iovval[i].iov_base = __sgxbounds_uninstrument(iov[i].iov_base);
        iovval[i].iov_len = iov[i].iov_len;
    }
    ssize_t ret = writev_real(fd, iovval, count);
    free_real(iovval);
    return ret;
}

ssize_t read(int fd, void *buf, size_t count) {
    buf = __sgxbounds_uninstrument(buf);
    return read_real(fd, buf, count);
}

ssize_t readlink(const char *__restrict__ path, char *__restrict__ buf, size_t bufsize) {
    path = __sgxbounds_uninstrument(path);
    buf = __sgxbounds_uninstrument(buf);
    return readlink_real(path, buf, bufsize);
}

ssize_t readlinkat(int fd, const char *__restrict__ path, char *__restrict__ buf, size_t bufsize) {
    path = __sgxbounds_uninstrument(path);
    buf = __sgxbounds_uninstrument(buf);
    return readlinkat_real(fd, path, buf, bufsize);
}

ssize_t readv(int fd, const struct iovec *iov, int count) {
    int i;
    // uninstrument iov into iovval including its iov_base members
    struct iovec* iovval = malloc_real(count * sizeof(struct iovec));
    iov = __sgxbounds_uninstrument(iov);
    for (i = 0; i < count; i++) {
        iovval[i].iov_base = __sgxbounds_uninstrument(iov[i].iov_base);
        iovval[i].iov_len = iov[i].iov_len;
    }
    ssize_t ret = readv_real(fd, iovval, count);
    free_real(iovval);
    return ret;
}

int renameat(int oldfd, const char *old, int newfd, const char *new) {
    old = __sgxbounds_uninstrument(old);
    new = __sgxbounds_uninstrument(new);
    return renameat_real(oldfd, old, newfd, new);
}

int rmdir(const char *path) {
    path = __sgxbounds_uninstrument(path);
    return rmdir_real(path);
}

int symlink(const char *existing, const char *new) {
    existing = __sgxbounds_uninstrument(existing);
    new = __sgxbounds_uninstrument(new);
    return symlink_real(existing, new);
}

int symlinkat(const char *existing, int fd, const char *new) {
    existing = __sgxbounds_uninstrument(existing);
    new = __sgxbounds_uninstrument(new);
    return symlinkat_real(existing, fd, new);
}

int truncate(const char *path, off_t length) {
    path = __sgxbounds_uninstrument(path);
    return truncate_real(path, length);
}

int truncate64(const char *path, off_t length) {
    return truncate(path, length);
}

char *ttyname(int fd) {
    static struct charbuf buf = {.lbnd = 0};
    if (buf.lbnd == 0)  buf.lbnd = (PTRTYPE)&buf;
    char* ret = ttyname_real(fd);
    if (!ret) return NULL;
    strcpy_real(buf.buf, ret);
    return __sgxbounds_combine_ptr(&buf, (PTRTYPE)&(buf.lbnd));
}

int ttyname_r(int fd, char *name, size_t size) {
    name = __sgxbounds_uninstrument(name);
    return ttyname_r_real(fd, name, size);
}

int unlink(const char *path) {
    path = __sgxbounds_uninstrument(path);
    return unlink_real(path);
}

int unlinkat(int fd, const char *path, int flag) {
    path = __sgxbounds_uninstrument(path);
    return unlinkat_real(fd, path, flag);
}

/* ------------------------------------------------------------------------- */
/* ------------------------------ FILE* family ----------------------------- */
/* ------------------------------------------------------------------------- */
// NOTE: struct FILE* is opaque and must never be dereferenced; we use this
//       feature and do not instrument FILE* pointers -- leaving them with
//       NULL (always-failing) bounds, such that any attempt to deref them
//       leads to segfault on address `0`.
//       E.g., fopen() returns FILE* ptr -- we must not instrument this ptr.
//
// NOTE: same reasoning applies to auxiliary structs: fpos_t

FILE *fdopen_real(int fd, const char *mode);
char *fgetln_real(FILE *f, size_t *plen);
FILE *fmemopen_real(void *__restrict__ buf, size_t size, const char *__restrict__ mode);
FILE *fopen_real(const char *__restrict__ filename, const char *__restrict__ mode);
FILE *fopen64_real(const char *__restrict__ filename, const char *__restrict__ mode);
size_t fread_real(void *__restrict__ destv, size_t size, size_t nmemb, FILE *__restrict__ f);
size_t fread_unlocked_real(void *__restrict__ destv, size_t size, size_t nmemb, FILE *__restrict__ f);
FILE *freopen_real(const char *__restrict__ filename, const char *__restrict__ mode, FILE *__restrict__ f);
FILE *freopen64_real(const char *__restrict__ filename, const char *__restrict__ mode, FILE *__restrict__ f);
size_t fwrite_real(const void *__restrict__ src, size_t size, size_t nmemb, FILE *__restrict__ f);
size_t fwrite_unlocked_real(const void *__restrict__ src, size_t size, size_t nmemb, FILE *__restrict__ f);
ssize_t getdelim_real(char **__restrict__ s, size_t *__restrict__ n, int delim, FILE *__restrict__ f);
FILE *open_memstream_real(char **bufp, size_t *sizep);
void perror_real(const char *msg);
FILE *popen_real(const char *cmd, const char *mode);
int remove_real(const char *path);
int rename_real(const char *old, const char *new);
void setbuf_real(FILE *__restrict__ f, char *__restrict__ buf);
void setbuffer_real(FILE *f, char *buf, size_t size);
int setvbuf_real(FILE *__restrict__ f, char *__restrict__ buf, int type, size_t size);
char *tempnam_real(const char *dir, const char *pfx);
char *tmpnam_real(char *buf);


FILE *fdopen(int fd, const char *mode) {
    mode = __sgxbounds_uninstrument(mode);
    return fdopen_real(fd, mode);
}

char *fgetln(FILE *f, size_t *plen) {
    plen = __sgxbounds_uninstrument(plen);
    char* ret = fgetln_real(f, plen);
    if (ret) {
        // TODO: suboptimal due to mem allocation on each call to fgetln
        ret = __sgxbounds_memdup(ret, *plen);
    }
    return ret;
}

FILE *fmemopen(void *__restrict__ buf, size_t size, const char *__restrict__ mode) {
    buf  = __sgxbounds_uninstrument(buf);
    mode = __sgxbounds_uninstrument(mode);
    return fmemopen_real(buf, size, mode);
}

FILE *fopen(const char *__restrict__ filename, const char *__restrict__ mode) {
    filename  = __sgxbounds_uninstrument(filename);
    mode      = __sgxbounds_uninstrument(mode);
    return fopen_real(filename, mode);
}

FILE *fopen64(const char *__restrict__ filename, const char *__restrict__ mode) {
    return fopen(filename, mode);
}

size_t fread(void *__restrict__ destv, size_t size, size_t nmemb, FILE *__restrict__ f) {
    destv = __sgxbounds_uninstrument(destv);
    return fread_real(destv, size, nmemb, f);
}

size_t fread_unlocked(void *__restrict__ destv, size_t size, size_t nmemb, FILE *__restrict__ f) {
    return fread(destv, size, nmemb, f);
}

FILE *freopen(const char *__restrict__ filename, const char *__restrict__ mode, FILE *__restrict__ f) {
    filename  = __sgxbounds_uninstrument(filename);
    mode      = __sgxbounds_uninstrument(mode);
    return freopen_real(filename, mode, f);
}

FILE *freopen64(const char *__restrict__ filename, const char *__restrict__ mode, FILE *__restrict__ f) {
    return freopen(filename, mode, f);
}

size_t fwrite(const void *__restrict__ src, size_t size, size_t nmemb, FILE *__restrict__ f) {
    src = __sgxbounds_uninstrument(src);
    return fwrite_real(src, size, nmemb, f);
}

size_t fwrite_unlocked(const void *__restrict__ src, size_t size, size_t nmemb, FILE *__restrict__ f) {
    return fwrite(src, size, nmemb, f);
}

ssize_t getdelim(char **__restrict__ s, size_t *__restrict__ n, int delim, FILE *__restrict__ f) {
    s = __sgxbounds_uninstrument(s);
    n = __sgxbounds_uninstrument(n);
    char* instoldss   = NULL;
    char* uninstoldss = NULL;
    if (*s) {
        instoldss = *s;
        uninstoldss =  __sgxbounds_uninstrument(*s);
        *s = uninstoldss;
    }
    ssize_t ret = getdelim_real(s, n, delim, f);
    if (ret != -1 && *s != uninstoldss) {
        // *s is internally realloced, always use our memdup()
        char* oldbuf = *s;
        *s = __sgxbounds_memdup(oldbuf, *n);
        free_real(oldbuf);
    } else {
        // *s is a user-supplied buffer, no need to malloc but instrument back
        *s = instoldss;
    }
    return ret;
}

ssize_t __getdelim(char **__restrict__ s, size_t *__restrict__ n, int delim, FILE *__restrict__ f) {
    return getdelim(s, n, delim, f);
}

ssize_t getline(char **__restrict__ s, size_t *__restrict__ n, FILE *__restrict__ f) {
    return getdelim(s, n, '\n', f);
}

FILE *open_memstream(char **bufp, size_t *sizep) {
    // TODO: this func is tricky because it resizes *bufp on its own;
    //       implementing its wrapper will be a huge pain
    return NULL;
}

void perror(const char *msg) {
    msg = __sgxbounds_uninstrument(msg);
    perror_real(msg);
}

FILE *popen(const char *cmd, const char *mode) {
    cmd  = __sgxbounds_uninstrument(cmd);
    mode = __sgxbounds_uninstrument(mode);
    return popen_real(cmd, mode);
}

int remove(const char *path) {
    path = __sgxbounds_uninstrument(path);
    return remove_real(path);
}

int rename(const char *old, const char *new) {
    old = __sgxbounds_uninstrument(old);
    new = __sgxbounds_uninstrument(new);
    return rename_real(old, new);
}

void setbuf(FILE *__restrict__ f, char *__restrict__ buf) {
    buf = __sgxbounds_uninstrument(buf);
    setbuf_real(f, buf);
}

void setbuffer(FILE *f, char *buf, size_t size) {
    buf = __sgxbounds_uninstrument(buf);
    setbuffer_real(f, buf, size);
}

int setvbuf(FILE *__restrict__ f, char *__restrict__ buf, int type, size_t size) {
    buf = __sgxbounds_uninstrument(buf);
    return setvbuf_real(f, buf, type, size);
}

char *tempnam(const char *dir, const char *pfx) {
    // TODO: now it's suboptimal due to mem allocation on each call via strdup
    dir = __sgxbounds_uninstrument(dir);
    pfx = __sgxbounds_uninstrument(pfx);
    char* ret = tempnam_real(dir, pfx);
    if (!ret) return ret;
    return __sgxbounds_strdup(ret);
}

char *tmpnam(char *buf) {
    if (!buf) {
        static struct charbuf buf = {.lbnd = 0};
        if (buf.lbnd == 0)  buf.lbnd = (PTRTYPE)&buf;
        char* ret = tmpnam_real(NULL);
        if (!ret) return NULL;
        strcpy_real(buf.buf, ret);
        return __sgxbounds_combine_ptr(&buf, (PTRTYPE)&(buf.lbnd));
    }
    // result will be stored in user-supplied buf, no need to strdup
    char* bufval = __sgxbounds_uninstrument(buf);
    char* ret = tmpnam_real(bufval);
    if (!ret) return ret;
    return buf;
}


/* ------------------------------------------------------------------------- */
/* ------------------------------ scanf family ----------------------------- */
/* ------------------------------------------------------------------------- */
// NOTE: we uninstrument only `format`, va_list will be uninstrumented
//       in vfscanf (we modified vfscanf in musl library)
int scanf_real(const char *__restrict__ fmt, ...);
int fscanf_real(FILE *__restrict__ f, const char *__restrict__ fmt, ...);
int vscanf_real(const char *__restrict__ fmt, va_list ap);
int vfscanf_real(FILE *__restrict__ f, const char *__restrict__ fmt, va_list ap);
int sscanf_real(const char *__restrict__ s, const char *__restrict__ fmt, ...);
int vsscanf_real(const char *__restrict__ s, const char *__restrict__ fmt, va_list ap);

int scanf(const char *__restrict__ fmt, ...) {
    char* fmtval = __sgxbounds_uninstrument((void*)fmt);
    int ret;
    va_list ap;
    va_start(ap, fmt);
    ret = vscanf_real(fmtval, ap);
    va_end(ap);
    return ret;
}

int fscanf(FILE *__restrict__ f, const char *__restrict__ fmt, ...) {
    char* fmtval = __sgxbounds_uninstrument((void*)fmt);
    int ret;
    va_list ap;
    va_start(ap, fmt);
    ret = vfscanf_real(f, fmtval, ap);
    va_end(ap);
    return ret;
}

int vfscanf(FILE *__restrict__ f, const char *__restrict__ fmt, va_list ap) {
    ap = __sgxbounds_uninstrument((void*)ap);
    fmt = __sgxbounds_uninstrument((void*)fmt);
    return vfscanf_real(f, fmt, ap);
}

int vscanf(const char *__restrict__ fmt, va_list ap) {
    ap = __sgxbounds_uninstrument((void*)ap);
    fmt = __sgxbounds_uninstrument((void*)fmt);
    return vscanf_real(fmt, ap);
}

int vsscanf(const char *__restrict__ s, const char *__restrict__ fmt, va_list ap) {
    ap = __sgxbounds_uninstrument((void*)ap);
    s   = __sgxbounds_uninstrument((void*)s);
    fmt = __sgxbounds_uninstrument((void*)fmt);
    return vsscanf_real(s, fmt, ap);
}

int sscanf(const char *__restrict__ s, const char *__restrict__ fmt, ...) {
    char* sval   = __sgxbounds_uninstrument((void*)s);
    char* fmtval = __sgxbounds_uninstrument((void*)fmt);
    int ret;
    va_list ap;
    va_start(ap, fmt);
    ret = vsscanf_real(sval, fmtval, ap);
    va_end(ap);
    return ret;
}

/* ------------------------------------------------------------------------- */
/* ----------------------------- printf family ----------------------------- */
/* ------------------------------------------------------------------------- */
// NOTE: we uninstrument only `format`, va_list will be uninstrumented
//       in vfprintf (we modified printf_core in musl library)

int asprintf_real(char **s, const char *fmt, ...);
int vasprintf_real(char **s, const char *fmt, va_list ap);
int dprintf_real(int fd, const char *__restrict__ fmt, ...);
int vdprintf_real(int fd, const char *__restrict__ fmt, va_list ap);
int fprintf_real(FILE *__restrict__ f, const char *__restrict__ fmt, ...);
int snprintf_real(char *__restrict__ s, size_t n, const char *__restrict__ fmt, ...);
int vsnprintf_real(char *__restrict__ s, size_t n, const char *__restrict__ fmt, va_list ap);
int sprintf_real(char *__restrict__ s, const char *__restrict__ fmt, ...);
int vsprintf_real(char *__restrict__ s, const char *__restrict__ fmt, va_list ap);
int vprintf_real(const char *__restrict__ fmt, va_list ap);
int printf_real(const char *__restrict format, ...);
int vfprintf_real(FILE *__restrict f, const char *__restrict fmt, va_list ap);

#ifndef SGXBOUNDS_NO_ASPRINTF
int asprintf(char **s, const char *fmt, ...) {
    // TODO: now it's suboptimal because vasprintf_real() does internal malloc,
    //       and we need to perform our own malloc via strdup()
    char** sval  = __sgxbounds_uninstrument(s);
    char* fmtval = __sgxbounds_uninstrument((void*)fmt);
    int ret;
    va_list ap;
    va_start(ap, fmt);
    ret = vasprintf_real(sval, fmtval, ap);
    va_end(ap);
    if (ret != -1) {
        char* oldbuf = *sval;
        *sval = __sgxbounds_strdup(oldbuf);
        free_real(oldbuf);
    }
    return ret;
}
#endif

#ifndef SGXBOUNDS_NO_VASPRINTF
int vasprintf(char **s, const char *fmt, va_list ap) {
    // TODO: now it's suboptimal because vasprintf_real() does internal malloc,
    //       and we need to perform our own malloc via strdup()
    ap = __sgxbounds_uninstrument((void*)ap);
    char** sval  = __sgxbounds_uninstrument(s);
    char* fmtval = __sgxbounds_uninstrument((void*)fmt);
    int ret = vasprintf_real(sval, fmtval, ap);
    if (ret != -1) {
        char* oldbuf = *sval;
        *sval = __sgxbounds_strdup(oldbuf);
        free_real(oldbuf);
    }
    return ret;
}
#endif

int dprintf(int fd, const char *__restrict__ fmt, ...) {
    char* fmtval = __sgxbounds_uninstrument((void*)fmt);
    int ret;
    va_list ap;
    va_start(ap, fmt);
    ret = vdprintf_real(fd, fmtval, ap);
    va_end(ap);
    return ret;
}

int vdprintf(int fd, const char *__restrict__ fmt, va_list ap) {
    ap = __sgxbounds_uninstrument((void*)ap);
    fmt = __sgxbounds_uninstrument((void*)fmt);
    return vdprintf_real(fd, fmt, ap);
}

int fprintf(FILE *__restrict__ f, const char *__restrict__ fmt, ...) {
    char* fmtval = __sgxbounds_uninstrument((void*)fmt);
    int ret;
    va_list ap;
    va_start(ap, fmt);
    ret = vfprintf_real(f, fmtval, ap);
    va_end(ap);
    return ret;
}

int vfprintf(FILE *__restrict__ f, const char *__restrict__ fmt, va_list ap) {
    ap = __sgxbounds_uninstrument((void*)ap);
    fmt = __sgxbounds_uninstrument((void*)fmt);
    return vfprintf_real(f, fmt, ap);
}

int snprintf(char *__restrict__ s, size_t n, const char *__restrict__ fmt, ...) {
    char* sval   = __sgxbounds_uninstrument((void*)s);
    char* fmtval = __sgxbounds_uninstrument((void*)fmt);
    int ret;
    va_list ap;
    va_start(ap, fmt);
    ret = vsnprintf_real(sval, n, fmtval, ap);
    va_end(ap);
    return ret;
}

int sprintf(char *__restrict__ s, const char *__restrict__ fmt, ...) {
    char* sval   = __sgxbounds_uninstrument((void*)s);
    char* fmtval = __sgxbounds_uninstrument((void*)fmt);
    int ret;
    va_list ap;
    va_start(ap, fmt);
    ret = vsprintf_real(sval, fmtval, ap);
    va_end(ap);
    return ret;
}

int vprintf(const char *__restrict__ fmt, va_list ap) {
    ap = __sgxbounds_uninstrument((void*)ap);
    fmt = __sgxbounds_uninstrument((void*)fmt);
    return vprintf_real(fmt, ap);
}

int vsnprintf(char *__restrict__ s, size_t n, const char *__restrict__ fmt, va_list ap) {
    ap = __sgxbounds_uninstrument((void*)ap);
    s   = __sgxbounds_uninstrument((void*)s);
    fmt = __sgxbounds_uninstrument((void*)fmt);
    return vsnprintf_real(s, n, fmt, ap);
}

int vsprintf(char *__restrict__ s, const char *__restrict__ fmt, va_list ap) {
    ap = __sgxbounds_uninstrument((void*)ap);
    s   = __sgxbounds_uninstrument((void*)s);
    fmt = __sgxbounds_uninstrument((void*)fmt);
    return vsprintf_real(s, fmt, ap);
}


int printf(const char *__restrict format, ...) {
    char* formatval = __sgxbounds_uninstrument((void*)format);
    int ret;
    va_list ap;
    va_start(ap, format);
    ret = vfprintf_real(stdout, formatval, ap);
    va_end(ap);
    return ret;
}

/* ------------------------------------------------------------------------- */
/* ------------------------------- puts/gets ------------------------------- */
/* ------------------------------------------------------------------------- */
int puts_real(const char *s);
int fputs_real(const char *__restrict__ s, FILE *__restrict__ f);
int fputs_unlocked_real(const char *__restrict__ s, FILE *__restrict__ f);
char *gets_real(char *s);
char *fgets_real(char *__restrict__ s, int n, FILE *__restrict__ f);
char *fgets_unlocked_real(char *__restrict__ s, int n, FILE *__restrict__ f);


int puts(const char *s) {
    s = __sgxbounds_uninstrument((void*) s);
    return puts_real(s);
}

int fputs(const char *__restrict__ s, FILE *__restrict__ f) {
    s = __sgxbounds_uninstrument((void*) s);
    return fputs_real(s, f);
}

int fputs_unlocked(const char *__restrict__ s, FILE *__restrict__ f) {
    return fputs(s, f);
}

char *gets(char *s) {
    char* sval = __sgxbounds_uninstrument(s);
    char* ret = gets_real(sval);
    if (!ret) return ret;
    return s;
}

char *fgets(char *__restrict__ s, int n, FILE *__restrict__ f) {
    char* sval = __sgxbounds_uninstrument(s);
    char* ret = fgets_real(sval, n, f);
    if (!ret) return ret;
    return s;
}

char *fgets_unlocked(char *__restrict__ s, int n, FILE *__restrict__ f) {
    return fgets(s, n, f);
}


/* ------------------------------------------------------------------------- */
/* ------------------------------- stdlib.h -------------------------------- */
/* ------------------------------------------------------------------------- */
typedef int (*cmpfun)(const void *, const void *);

int atoi_real(const char *s);
double atof_real(const char *s);
long atol_real(const char *s);
long long atoll_real(const char *s);

// TODO: bsearch ecvt fcvt gcvt ???
void qsort_real(void *base, size_t nel, size_t width, cmpfun cmp);

float strtof_real(const char *__restrict__ s, char **__restrict__ p);
double strtod_real(const char *__restrict__ s, char **__restrict__ p);
long double strtold_real(const char *__restrict__ s, char **__restrict__ p);
long strtol_real(const char *__restrict__ s, char **__restrict__ p, int base);
long long strtoll_real(const char *__restrict__ s, char **__restrict__ p, int base);
unsigned long strtoul_real(const char *restrict s, char **restrict p, int base);
unsigned long long strtoull_real(const char *restrict s, char **restrict p, int base);
intmax_t strtoimax_real(const char *__restrict__ s, char **__restrict__ p, int base);
uintmax_t strtoumax_real(const char *__restrict__ s, char **__restrict__ p, int base);

char *gcvt_real(double x, int n, char *b);
char *ecvt_real(double x, int n, int *dp, int *sign);
char *fcvt_real(double x, int n, int *dp, int *sign);

int atoi(const char *s) {
    s = __sgxbounds_uninstrument((void*) s);
    return atoi_real(s);
}

double atof(const char *s) {
    s = __sgxbounds_uninstrument((void*) s);
    return atof_real(s);
}

long atol(const char *s) {
    s = __sgxbounds_uninstrument((void*) s);
    return atol_real(s);
}

long long atoll(const char *s)
{
    s = __sgxbounds_uninstrument((void*) s);
    return atoll_real(s);
}

// TODO: bsearch ecvt fcvt gcvt ???

static __thread PTRTYPE qsort_ubnd;
static __thread cmpfun  qsort_real_cmp;

static int qsort_cmp(const void *v1, const void *v2) {
   v1 = __sgxbounds_combine_ptr(v1, qsort_ubnd);
   v2 = __sgxbounds_combine_ptr(v2, qsort_ubnd);
   return qsort_real_cmp(v1, v2);
}

void qsort(void *base, size_t nel, size_t width, cmpfun cmp) {
    // memorize ubnd of base and the real cmp function supplied by user
    qsort_ubnd = __sgxbounds_extract_ubnd(base);
    qsort_real_cmp = cmp;
    // continue with real uninstrumented qsort(); it will call qsort_cmp
    // which instruments v1 and v2 with qsort_ubnd and forward to real cmp
    base = __sgxbounds_uninstrument(base);
    qsort_real(base, nel, width, qsort_cmp);
}

float strtof(const char *__restrict__ s, char **__restrict__ p) {
    char* sval = __sgxbounds_uninstrument((void*) s);
    if (p)
        p = (char **) __sgxbounds_uninstrument((void*) p);
    float ret = strtof_real(sval, p);
    if (p) {
        // *p points into s, so it has the same bounds as s
        PTRTYPE ubnd = __sgxbounds_extract_ubnd(s);
        *p = __sgxbounds_combine_ptr(*p, ubnd);
    }
    return ret;
}

double strtod(const char *__restrict__ s, char **__restrict__ p) {
    char* sval = __sgxbounds_uninstrument((void*) s);
    if (p)
        p = (char **) __sgxbounds_uninstrument((void*) p);
    double ret = strtod_real(sval, p);
    if (p) {
        // *p points into s, so it has the same bounds as s
        PTRTYPE ubnd = __sgxbounds_extract_ubnd(s);
        *p = __sgxbounds_combine_ptr(*p, ubnd);
    }
    return ret;
}

long double strtold(const char *__restrict__ s, char **__restrict__ p) {
    char* sval = __sgxbounds_uninstrument((void*) s);
    if (p)
        p = (char **) __sgxbounds_uninstrument((void*) p);
    long double ret = strtold_real(sval, p);
    if (p) {
        // *p points into s, so it has the same bounds as s
        PTRTYPE ubnd = __sgxbounds_extract_ubnd(s);
        *p = __sgxbounds_combine_ptr(*p, ubnd);
    }
    return ret;
}

float strtof_l(const char *__restrict__ s, char **__restrict__ p) {
    return strtof(s, p);
}

double strtod_l(const char *__restrict__ s, char **__restrict__ p) {
    return strtod(s, p);
}

long double strtold_l(const char *__restrict__ s, char **__restrict__ p) {
    return strtold(s, p);
}

long strtol(const char *__restrict__ s, char **__restrict__ p, int base)
{
    char* sval = __sgxbounds_uninstrument((void*) s);
    if (p)
        p = (char **) __sgxbounds_uninstrument((void*) p);
    long ret = strtol_real(sval, p, base);
    if (p) {
        // *p points into s, so it has the same bounds as s
        PTRTYPE ubnd = __sgxbounds_extract_ubnd(s);
        *p = __sgxbounds_combine_ptr(*p, ubnd);
    }
    return ret;
}

long long strtoll(const char *__restrict__ s, char **__restrict__ p, int base)
{
    char* sval = __sgxbounds_uninstrument((void*) s);
    if (p)
        p = (char **) __sgxbounds_uninstrument((void*) p);
    long long ret = strtoll_real(sval, p, base);
    if (p) {
        // *p points into s, so it has the same bounds as s
        PTRTYPE ubnd = __sgxbounds_extract_ubnd(s);
        *p = __sgxbounds_combine_ptr(*p, ubnd);
    }
    return ret;
}

unsigned long strtoul(const char *restrict s, char **restrict p, int base) {
    char* sval = __sgxbounds_uninstrument((void*) s);
    if (p)
        p = (char **) __sgxbounds_uninstrument((void*) p);
    unsigned long ret = strtoul_real(sval, p, base);
    if (p) {
        // *p points into s, so it has the same bounds as s
        PTRTYPE ubnd = __sgxbounds_extract_ubnd(s);
        *p = __sgxbounds_combine_ptr(*p, ubnd);
    }
    return ret;
}

unsigned long long strtoull(const char *restrict s, char **restrict p, int base) {
    char* sval = __sgxbounds_uninstrument((void*) s);
    if (p)
        p = (char **) __sgxbounds_uninstrument((void*) p);
    unsigned long long ret = strtoull_real(sval, p, base);
    if (p) {
        // *p points into s, so it has the same bounds as s
        PTRTYPE ubnd = __sgxbounds_extract_ubnd(s);
        *p = __sgxbounds_combine_ptr(*p, ubnd);
    }
    return ret;
}


intmax_t strtoimax(const char *__restrict__ s, char **__restrict__ p, int base)
{
    char* sval = __sgxbounds_uninstrument((void*) s);
    if (p)
        p = (char **) __sgxbounds_uninstrument((void*) p);
    intmax_t ret = strtoimax_real(sval, p, base);
    if (p) {
        // *p points into s, so it has the same bounds as s
        PTRTYPE ubnd = __sgxbounds_extract_ubnd(s);
        *p = __sgxbounds_combine_ptr(*p, ubnd);
    }
    return ret;
}

uintmax_t strtoumax(const char *__restrict__ s, char **__restrict__ p, int base)
{
    char* sval = __sgxbounds_uninstrument((void*) s);
    if (p)
        p = (char **) __sgxbounds_uninstrument((void*) p);
    uintmax_t ret = strtoumax_real(sval, p, base);
    if (p) {
        // *p points into s, so it has the same bounds as s
        PTRTYPE ubnd = __sgxbounds_extract_ubnd(s);
        *p = __sgxbounds_combine_ptr(*p, ubnd);
    }
    return ret;
}

char *gcvt(double x, int n, char *b) {
    char* bval = __sgxbounds_uninstrument((void*) b);
    gcvt_real(x, n, bval);
    return b;
}

char *ecvt(double x, int n, int *dp, int *sign) {
    dp   = __sgxbounds_uninstrument((void*) dp);
    sign = __sgxbounds_uninstrument((void*) sign);
    PTRTYPE ubnd = __sgxbounds_highest_bound();  // NOTE: not the best solution
    char* ret = ecvt_real(x, n, dp, sign);
    ret = __sgxbounds_combine_ptr(ret, ubnd);
    return ret;
}

char *fcvt(double x, int n, int *dp, int *sign) {
    dp   = __sgxbounds_uninstrument((void*) dp);
    sign = __sgxbounds_uninstrument((void*) sign);
    PTRTYPE ubnd = __sgxbounds_highest_bound();  // NOTE: not the best solution
    char* ret = fcvt_real(x, n, dp, sign);
    ret = __sgxbounds_combine_ptr(ret, ubnd);
    return ret;
}


/* ------------------------------------------------------------------------- */
/* ----------------------------- time funcs -------------------------------- */
/* ------------------------------------------------------------------------- */
struct timecharbuf {
    char buf[26];
    PTRTYPE lbnd;
};

struct timetmbuf {
    struct tm buf;
    PTRTYPE lbnd;
};

char *asctime_real(const struct tm *tm);
char *asctime_r_real(const struct tm *__restrict__ tm, char *__restrict__ buf);
int clock_getcpuclockid_real(pid_t pid, clockid_t *clk);
int clock_getres_real(clockid_t clk, struct timespec *ts);
int clock_gettime_real(clockid_t clk, struct timespec *ts);
int clock_nanosleep_real(clockid_t clk, int flags, const struct timespec *req, struct timespec *rem);
int clock_settime_real(clockid_t clk, const struct timespec *ts);
char *ctime_real(const time_t *t);
char *ctime_r_real(const time_t *t, char *buf);
int ftime_real(struct timeb *tp);
struct tm *getdate_real(const char *s);
int gettimeofday_real(struct timeval *__restrict__ tv, void *__restrict__ tz);
struct tm *gmtime_real(const time_t *t);
struct tm *gmtime_r_real(const time_t *__restrict__ t, struct tm *__restrict__ tm);
struct tm *localtime_real(const time_t *t);
struct tm *localtime_r_real(const time_t *__restrict__ t, struct tm *__restrict__ tm);
time_t mktime_real(struct tm *tm);
int nanosleep_real(const struct timespec *req, struct timespec *rem);
size_t strftime_real(char *__restrict__ s, size_t n, const char *__restrict__ f, const struct tm *__restrict__ tm);
size_t strftime_l_real(char *__restrict__ s, size_t n, const char *__restrict__ f, const struct tm *__restrict__ tm, locale_t loc);
char *strptime_real(const char *__restrict__ s, const char *__restrict__ f, struct tm *__restrict__ tm);
time_t time_real(time_t *t);
time_t timegm_real(struct tm *tm);
int timer_create_real(clockid_t clk, struct sigevent *__restrict__ evp, timer_t *__restrict__ res);
int timer_gettime_real(timer_t t, struct itimerspec *val);
int timer_settime_real(timer_t t, int flags, const struct itimerspec *__restrict__ val, struct itimerspec *__restrict__ old);
clock_t times_real(struct tms *tms);
int timespec_get_real(struct timespec * ts, int base);
int utime_real(const char *path, const struct utimbuf *times);


char *asctime(const struct tm *tm) {
    static struct timecharbuf buf = {.lbnd = 0};
    if (buf.lbnd == 0)  buf.lbnd = (PTRTYPE)&buf;

    tm = __sgxbounds_uninstrument((void*) tm);
    char* ret = asctime_real(tm);
    if (!ret) return ret;
    strncpy_real(buf.buf, ret, 26);
    return __sgxbounds_combine_ptr(&buf, (PTRTYPE)&(buf.lbnd));
}

char *asctime_r(const struct tm *__restrict__ tm, char *__restrict__ buf) {
    tm = __sgxbounds_uninstrument((void*) tm);
    char* bufval = __sgxbounds_uninstrument((void*) buf);
    char* ret = asctime_r_real(tm, bufval);
    if (!ret) return ret;
    return buf;
}

int clock_getcpuclockid(pid_t pid, clockid_t *clk) {
    clk = __sgxbounds_uninstrument(clk);
    return clock_getcpuclockid_real(pid, clk);
}

int clock_getres(clockid_t clk, struct timespec *ts) {
    if (ts) {
        ts = __sgxbounds_uninstrument(ts);
    }
    return clock_getres_real(clk, ts);
}

int clock_gettime(clockid_t clk, struct timespec *ts) {
    ts = __sgxbounds_uninstrument(ts);
    return clock_gettime_real(clk, ts);
}

int clock_nanosleep(clockid_t clk, int flags, const struct timespec *req, struct timespec *rem) {
    if (req) {
        req = __sgxbounds_uninstrument(req);
    }
    if (rem) {
        rem = __sgxbounds_uninstrument(rem);
    }
    return clock_nanosleep_real(clk, flags, req, rem);
}

int clock_settime(clockid_t clk, const struct timespec *ts) {
    ts = __sgxbounds_uninstrument(ts);
    return clock_settime_real(clk, ts);
}

char *ctime(const time_t *t) {
    static struct timecharbuf buf = {.lbnd = 0};
    if (buf.lbnd == 0)  buf.lbnd = (PTRTYPE)&buf;

    t = __sgxbounds_uninstrument((void*) t);
    char* ret = ctime_real(t);
    if (!ret) return ret;
    strncpy_real(buf.buf, ret, 26);
    return __sgxbounds_combine_ptr(&buf, (PTRTYPE)&(buf.lbnd));
}

char *ctime_r(const time_t *t, char *buf) {
    t = __sgxbounds_uninstrument((void*) t);
    char* bufval = __sgxbounds_uninstrument(buf);
    char* ret = ctime_r_real(t, bufval);
    if (!ret) return ret;
    return buf;
}

int ftime(struct timeb *tp) {
    tp = __sgxbounds_uninstrument((void*) tp);
    return ftime_real(tp);
}

struct tm *getdate(const char *s) {
    static struct timetmbuf buf = {.lbnd = 0};
    if (buf.lbnd == 0)  buf.lbnd = (PTRTYPE)&buf;

    s = __sgxbounds_uninstrument((void*) s);
    struct tm* ret = getdate_real(s);
    if (!ret) return ret;
    memcpy_real(&buf.buf, ret, sizeof(struct tm));
    return __sgxbounds_combine_ptr(&buf, (PTRTYPE)&(buf.lbnd));
}

int gettimeofday(struct timeval *__restrict__ tv, void *__restrict__ tz) {
    if (tv) {
        tv = __sgxbounds_uninstrument(tv);
    }
    if (tz) {
        tz = __sgxbounds_uninstrument(tz);
    }
    return gettimeofday_real(tv, tz);
}

struct tm *gmtime(const time_t *t) {
    static struct timetmbuf buf = {.lbnd = 0};
    if (buf.lbnd == 0)  buf.lbnd = (PTRTYPE)&buf;

    t = __sgxbounds_uninstrument((void*) t);
    struct tm* ret = gmtime_real(t);
    if (!ret) return ret;
    memcpy_real(&buf.buf, ret, sizeof(struct tm));
    return __sgxbounds_combine_ptr(&buf, (PTRTYPE)&(buf.lbnd));
}

struct tm *gmtime_r(const time_t *__restrict__ t, struct tm *__restrict__ tm) {
    t  = __sgxbounds_uninstrument((void*) t);
    struct tm *tmval = __sgxbounds_uninstrument((void*) tm);
    struct tm *ret = gmtime_r_real(t, tmval);
    if (!ret) return ret;
    return tm;
}

struct tm *localtime(const time_t *t) {
    static struct timetmbuf buf = {.lbnd = 0};
    if (buf.lbnd == 0)  buf.lbnd = (PTRTYPE)&buf;

    t = __sgxbounds_uninstrument((void*) t);
    struct tm* ret = localtime_real(t);
    if (!ret) return ret;
    memcpy_real(&buf.buf, ret, sizeof(struct tm));
    return __sgxbounds_combine_ptr(&buf, (PTRTYPE)&(buf.lbnd));
}

struct tm *localtime_r(const time_t *__restrict__ t, struct tm *__restrict__ tm) {
    t  = __sgxbounds_uninstrument((void*) t);
    struct tm *tmval = __sgxbounds_uninstrument((void*) tm);
    struct tm *ret = localtime_r_real(t, tmval);
    if (!ret) return ret;
    return tm;
}

time_t mktime(struct tm *tm) {
    tm = __sgxbounds_uninstrument((void*) tm);
    return mktime_real(tm);
}

int nanosleep(const struct timespec *req, struct timespec *rem) {
    if (req) {
        req = __sgxbounds_uninstrument(req);
    }
    if (rem) {
        rem = __sgxbounds_uninstrument(rem);
    }
    return nanosleep_real(req, rem);
}

size_t strftime(char *__restrict__ s, size_t n, const char *__restrict__ f, const struct tm *__restrict__ tm) {
    s  = __sgxbounds_uninstrument(s);
    f  = __sgxbounds_uninstrument(f);
    tm = __sgxbounds_uninstrument(tm);
    return strftime_real(s, n, f, tm);
}

size_t strftime_l(char *__restrict__ s, size_t n, const char *__restrict__ f, const struct tm *__restrict__ tm, locale_t loc) {
    s  = __sgxbounds_uninstrument(s);
    f  = __sgxbounds_uninstrument(f);
    tm = __sgxbounds_uninstrument(tm);
    return strftime_l_real(s, n, f, tm, loc);
}

char *strptime(const char *__restrict__ s, const char *__restrict__ f, struct tm *__restrict__ tm) {
    char* sval  = __sgxbounds_uninstrument(s);
    f  = __sgxbounds_uninstrument(f);
    tm = __sgxbounds_uninstrument(tm);
    char* ptr = strptime_real(sval, f, tm);
    if (ptr) {
        // ptr points into s, so it has the same bounds as s
        PTRTYPE ubnd = __sgxbounds_extract_ubnd(s);
        ptr = __sgxbounds_combine_ptr(ptr, ubnd);
    }
    return ptr;
}

time_t time(time_t *t) {
    if (t) {
        t = __sgxbounds_uninstrument(t);
    }
    return time_real(t);
}

time_t timegm(struct tm *tm) {
    if (tm) {
        tm = __sgxbounds_uninstrument(tm);
    }
    return timegm_real(tm);
}

int timer_create(clockid_t clk, struct sigevent *__restrict__ evp, timer_t *__restrict__ res) {
    // TODO: we do not support signals...
    return -1;
}

int timer_gettime(timer_t t, struct itimerspec *val) {
    if (val) {
        val = __sgxbounds_uninstrument(val);
    }
    return timer_gettime_real(t, val);
}

int timer_settime(timer_t t, int flags, const struct itimerspec *__restrict__ val, struct itimerspec *__restrict__ old) {
    if (val) {
        val = __sgxbounds_uninstrument(val);
    }
    if (old) {
        old = __sgxbounds_uninstrument(old);
    }
    return timer_settime_real(t, flags, val, old);
}

clock_t times(struct tms *tms) {
    tms = __sgxbounds_uninstrument(tms);
    return times_real(tms);
}

int timespec_get(struct timespec * ts, int base) {
    ts = __sgxbounds_uninstrument(ts);
    return timespec_get_real(ts, base);
}

int utime(const char *path, const struct utimbuf *times) {
    path = __sgxbounds_uninstrument(path);
    if (times) {
        times = __sgxbounds_uninstrument(times);
    }
    return utime_real(path, times);
}

/* ------------------------------------------------------------------------- */
/* ------------------------------ env funcs -------------------------------- */
/* ------------------------------------------------------------------------- */
char *getenv_real(const char *name);
int putenv_real(char *s);
int setenv_real(const char *var, const char *value, int overwrite);
int unsetenv_real(const char *name);

char *getenv(const char *name) {
    // TODO: now it's suboptimal due to mem allocation on each call via strdup
    name = __sgxbounds_uninstrument(name);
    char* tmp = getenv_real(name);
    if (!tmp) return NULL;
    return __sgxbounds_strdup(tmp);
}

int putenv(char *s) {
    s = __sgxbounds_uninstrument(s);
    return putenv_real(s);
}

int setenv(const char *var, const char *value, int overwrite) {
    var = __sgxbounds_uninstrument(var);
    value = __sgxbounds_uninstrument(value);
    return setenv_real(var, value, overwrite);
}

int unsetenv(const char *name) {
    name = __sgxbounds_uninstrument(name);
    return unsetenv_real(name);
}

/* ------------------------------------------------------------------------- */
/* ----------------------------- stat funcs -------------------------------- */
/* ------------------------------------------------------------------------- */
int chmod_real(const char *path, mode_t mode);
int fchmodat_real(int fd, const char *path, mode_t mode, int flag);
int fstat_real(int fd, struct stat *st);
int fstat64_real(int fd, struct stat *st);
int fstatat_real(int fd, const char *__restrict__ path, struct stat *__restrict__ buf, int flag);
int fstatat64_real(int fd, const char *__restrict__ path, struct stat *__restrict__ buf, int flag);
int futimens_real(int fd, const struct timespec times[2]);
int futimesat_real(int dirfd, const char *pathname, const struct timeval times[2]);
int lchmod_real(const char *path, mode_t mode);
int lstat_real(const char *__restrict__ path, struct stat *__restrict__ buf);
int lstat64_real(const char *__restrict__ path, struct stat *__restrict__ buf);
int mkdir_real(const char *path, mode_t mode);
int mkdirat_real(int fd, const char *path, mode_t mode);
int mkfifo_real(const char *path, mode_t mode);
int mkfifoat_real(int fd, const char *path, mode_t mode);
int mknod_real(const char *path, mode_t mode, dev_t dev);
int mknodat_real(int fd, const char *path, mode_t mode, dev_t dev);
int stat_real(const char *__restrict__ path, struct stat *__restrict__ buf);
int stat64_real(const char *__restrict__ path, struct stat *__restrict__ buf);
int statfs_real(const char *path, struct statfs *buf);
int statfs64_real(const char *path, struct statfs *buf);
int fstatfs_real(int fd, struct statfs *buf);
int fstatfs64_real(int fd, struct statfs *buf);
int statvfs_real(const char *__restrict__ path, struct statvfs *__restrict__ buf);
int statvfs64_real(const char *__restrict__ path, struct statvfs *__restrict__ buf);
int fstatvfs_real(int fd, struct statvfs *buf);
int fstatvfs64_real(int fd, struct statvfs *buf);
int utimensat_real(int fd, const char *path, const struct timespec times[2], int flags);

int chmod(const char *path, mode_t mode) {
    path = __sgxbounds_uninstrument(path);
    return chmod_real(path, mode);
}

int fchmodat(int fd, const char *path, mode_t mode, int flag) {
    path = __sgxbounds_uninstrument(path);
    return fchmodat_real(fd, path, mode, flag);
}

int fstat(int fd, struct stat *st) {
    st = __sgxbounds_uninstrument(st);
    return fstat_real(fd, st);
}

int fstat64(int fd, struct stat *st) {
    return fstat(fd, st);
}

int fstatat(int fd, const char *__restrict__ path, struct stat *__restrict__ buf, int flag) {
    path = __sgxbounds_uninstrument(path);
    buf = __sgxbounds_uninstrument(buf);
    return fstatat_real(fd, path, buf, flag);
}

int fstatat64(int fd, const char *__restrict__ path, struct stat *__restrict__ buf, int flag) {
    return fstatat(fd, path, buf, flag);
}

int futimens(int fd, const struct timespec times[2]) {
    struct timespec* timesval = (struct timespec*)__sgxbounds_uninstrument((void*) times);
    return futimens_real(fd, timesval);
}

int futimesat(int dirfd, const char *pathname, const struct timeval times[2]) {
    pathname = __sgxbounds_uninstrument(pathname);
    struct timeval* timesval = (struct timeval*)__sgxbounds_uninstrument((void*) times);
    return futimesat_real(dirfd, pathname, timesval);
}

int lchmod(const char *path, mode_t mode) {
    path = __sgxbounds_uninstrument(path);
    return lchmod_real(path, mode);
}

int lstat(const char *__restrict__ path, struct stat *__restrict__ buf) {
    path = __sgxbounds_uninstrument(path);
    buf = __sgxbounds_uninstrument(buf);
    return lstat_real(path, buf);
}

int lstat64(const char *__restrict__ path, struct stat *__restrict__ buf) {
    return lstat(path, buf);
}

int mkdir(const char *path, mode_t mode) {
    path = __sgxbounds_uninstrument(path);
    return mkdir_real(path, mode);
}

int mkdirat(int fd, const char *path, mode_t mode) {
    path = __sgxbounds_uninstrument(path);
    return mkdirat_real(fd, path, mode);
}

int mkfifo(const char *path, mode_t mode) {
    path = __sgxbounds_uninstrument(path);
    return mkfifo_real(path, mode);
}

int mkfifoat(int fd, const char *path, mode_t mode) {
    path = __sgxbounds_uninstrument(path);
    return mkfifoat_real(fd, path, mode);
}

int mknod(const char *path, mode_t mode, dev_t dev) {
    path = __sgxbounds_uninstrument(path);
    return mknod_real(path, mode, dev);
}

int mknodat(int fd, const char *path, mode_t mode, dev_t dev) {
    path = __sgxbounds_uninstrument(path);
    return mknodat_real(fd, path, mode, dev);
}

int stat(const char *__restrict__ path, struct stat *__restrict__ buf) {
    path = __sgxbounds_uninstrument(path);
    buf = __sgxbounds_uninstrument(buf);
    return stat_real(path, buf);
}

int stat64(const char *__restrict__ path, struct stat *__restrict__ buf) {
    return stat(path, buf);
}

int statfs(const char *path, struct statfs *buf) {
    path = __sgxbounds_uninstrument(path);
    buf = __sgxbounds_uninstrument(buf);
    return statfs_real(path, buf);
}

int statfs64(const char *path, struct statfs *buf) {
    return statfs(path, buf);
}

int fstatfs(int fd, struct statfs *buf) {
    buf = __sgxbounds_uninstrument(buf);
    return fstatfs_real(fd, buf);
}

int fstatfs64(int fd, struct statfs *buf) {
    return fstatfs(fd, buf);
}

int statvfs(const char *__restrict__ path, struct statvfs *__restrict__ buf) {
    path = __sgxbounds_uninstrument(path);
    buf = __sgxbounds_uninstrument(buf);
    return statvfs_real(path, buf);
}

int statvfs64(const char *__restrict__ path, struct statvfs *__restrict__ buf) {
    return statvfs(path, buf);
}

int fstatvfs(int fd, struct statvfs *buf) {
    buf = __sgxbounds_uninstrument(buf);
    return fstatvfs_real(fd, buf);
}

int fstatvfs64(int fd, struct statvfs *buf) {
    return fstatvfs(fd, buf);
}

int utimensat(int fd, const char *path, const struct timespec times[2], int flags) {
    path = __sgxbounds_uninstrument(path);
    struct timespec* timesval = (struct timespec*)__sgxbounds_uninstrument((void*) times);
    return utimensat_real(fd, path, timesval, flags);
}

/* ------------------------------------------------------------------------- */
/* ------------------------------- exit funcs  ----------------------------- */
/* ------------------------------------------------------------------------- */
// NOTE: we do not instrument function ptrs, thus we do not uninstrument
//       arguments such as void (*func)(void *)

int __cxa_atexit_real(void (*func)(void *), void *arg, void *dso);
void __assert_fail_real(const char *expr, const char *file, int line, const char *func);

int __cxa_atexit(void (*func)(void *), void *arg, void *dso) {
#if 0
    // TODO: args and dso can contain ptrs within, must uninstrument them?
    arg = __sgxbounds_uninstrument(arg);
    dso = __sgxbounds_uninstrument(dso);
#endif
    return __cxa_atexit_real(func, arg, dso);
}

void __assert_fail(const char *expr, const char *file, int line, const char *func) {
    expr = __sgxbounds_uninstrument(expr);
    file = __sgxbounds_uninstrument(file);
    if (func)
        func = __sgxbounds_uninstrument(func);
    return __assert_fail_real(expr, file, line, func);
}

/* ------------------------------------------------------------------------- */
/* ------------------------------- prng funcs  ----------------------------- */
/* ------------------------------------------------------------------------- */
struct seed48buf {
    unsigned short buf[7];
    PTRTYPE lbnd;
};

double erand48_real(unsigned short s[3]);
void lcong48_real(unsigned short p[7]);
long nrand48_real(unsigned short s[3]);
long jrand48_real(unsigned short s[3]);
int rand_r_real(unsigned *seed);
unsigned short *seed48_real(unsigned short *s);

double erand48(unsigned short s[3]) {
    unsigned short* sval = (unsigned short*)__sgxbounds_uninstrument((void*) s);
    return erand48_real(sval);
}

void lcong48(unsigned short p[7]) {
    unsigned short* pval = (unsigned short*)__sgxbounds_uninstrument((void*) p);
    lcong48_real(pval);
}

long nrand48(unsigned short s[3]) {
    unsigned short* sval = (unsigned short*)__sgxbounds_uninstrument((void*) s);
    return nrand48_real(sval);
}

long jrand48(unsigned short s[3]) {
    unsigned short* sval = (unsigned short*)__sgxbounds_uninstrument((void*) s);
    return jrand48_real(sval);
}

// TODO: initstate() and setstate() from random.c operate on internal char*, ignoring them for now

int rand_r(unsigned *seed) {
    seed = __sgxbounds_uninstrument(seed);
    return rand_r_real(seed);
}

extern unsigned short __seed48[7];

unsigned short *seed48(unsigned short *s) {
    static struct seed48buf buf = {.lbnd = 0};
    if (buf.lbnd == 0) {
        memcpy_real(&buf.buf, __seed48, sizeof(buf.buf));
        buf.lbnd = (PTRTYPE)&buf;
    }
    s = __sgxbounds_uninstrument((void*) s);
    if ((void*)s == (void*)&buf) {
        // corner-case when user calls something like `seed = seed48(seed)` ->
        //   this means that the underlying __seed48 is supposed to be used
        memcpy_real(&buf.buf, __seed48, sizeof(buf.buf));
    }
    unsigned short * ret = seed48_real(s);
    if (!ret) return ret;
    memcpy_real(&buf.buf, ret, sizeof(unsigned short)*3);
    return __sgxbounds_combine_ptr(&buf, (PTRTYPE)&(buf.lbnd));
}

/* ------------------------------------------------------------------------- */
/* ----------------------------- dirent funcs  ----------------------------- */
/* ------------------------------------------------------------------------- */
// NOTE: struct DIR* is opaque and must never be dereferenced; we use this
//       feature and do not instrument DIR* pointers -- leaving them with
//       NULL (always-failing) bounds, such that any attempt to deref them
//       leads to segfault on address `0`.
//       E.g., opendir() returns DIR* ptr -- we must not instrument this ptr.

struct direntbuf {
    struct dirent buf;
    PTRTYPE lbnd;
};

int getdents_real(int fd, struct dirent *buf, size_t len);
int getdents64_real(int fd, struct dirent *buf, size_t len);
DIR *opendir_real(const char *name);
struct dirent *readdir_real(DIR *dir);
struct dirent *readdir64_real(DIR *dir);
int readdir_r_real(DIR *__restrict__ dir, struct dirent *__restrict__ buf, struct dirent **__restrict__ result);
int readdir64_r_real(DIR *__restrict__ dir, struct dirent *__restrict__ buf, struct dirent **__restrict__ result);

int getdents(int fd, struct dirent *buf, size_t len) {
    buf = __sgxbounds_uninstrument((void*) buf);
    return getdents_real(fd, buf, len);
}

int getdents64(int fd, struct dirent *buf, size_t len) {
    return getdents(fd, buf, len);
}

DIR *opendir(const char *name) {
    name = __sgxbounds_uninstrument(name);
    return opendir_real(name);
}

struct dirent *readdir(DIR *dir) {
    static struct direntbuf buf = {.lbnd = 0};
    if (buf.lbnd == 0)  buf.lbnd = (PTRTYPE)&buf;
    struct dirent *ret = readdir_real(dir);
    if (!ret) return ret;
    memcpy_real(&buf.buf, ret, sizeof(struct dirent));
    return __sgxbounds_combine_ptr(&buf, (PTRTYPE)&(buf.lbnd));
}

struct dirent *readdir64(DIR *dir) {
    return readdir(dir);
}

int readdir_r(DIR *__restrict__ dir, struct dirent *__restrict__ buf, struct dirent **__restrict__ result) {
    struct dirent *bufval = __sgxbounds_uninstrument(buf);
    result = __sgxbounds_uninstrument(result);
    int ret = readdir_r_real(dir, bufval, result);
    if (*result) {
        *result = buf;
    }
    return ret;
}

int readdir64_r(DIR *__restrict__ dir, struct dirent *__restrict__ buf, struct dirent **__restrict__ result) {
    return readdir_r(dir, buf, result);
}

// NOTE: we do not instrument alphasort() and versionsort() because they are
//       supposed to be used *only* via scandir()
int versionsort(const struct dirent **a, const struct dirent **b);
int alphasort(const struct dirent **a, const struct dirent **b);

// need this wrapper around `struct dirent` because we need to memorize
// length for future sgxbounds-instrumentation and survive swapping via qsort()
struct direntlen {
    struct dirent *d;
    PTRTYPE l;
};

int *__errno_location_real(void);

int scandir(const char *path, struct dirent ***res,
    int (*sel)(const struct dirent *),
    int (*cmp)(const struct dirent **, const struct dirent **))
{
    // we completely re-implement scandir because it allocates `res` internally
    // in general, we use _real versions of funcs, but malloc PTRSIZE more bytes
    // we also take care that sel() func receives instrumented argument
    path = __sgxbounds_uninstrument(path);
    res  = __sgxbounds_uninstrument(res);

    DIR *d = opendir_real(path);
    struct dirent *de;
    struct direntlen *names=0, *tmp;
    size_t cnt=0, len=0, i;
    int* errno_addr = __errno_location_real();
    int old_errno = *errno_addr;

    if (!d) return -1;

    while ((*errno_addr=0), (de = readdir(d))) {
        if (sel && !sel(de)) continue;
        if (cnt >= len) {
            len = 2*len+1;
            if (len > SIZE_MAX/sizeof *names) break;
            tmp = realloc_real(names, len * sizeof *names);
            if (!tmp) break;
            names = tmp;
        }
        struct dirent *deval = __sgxbounds_uninstrument(de);
        names[cnt].d = malloc_real(deval->d_reclen + PTRSIZE);
        names[cnt].l = deval->d_reclen;
        if (!names[cnt].d) break;
        memcpy_real(names[cnt++].d, deval, deval->d_reclen);
    }

    closedir(d);

    if (*errno_addr) {
        if (names) while (cnt-->0) free_real(names[cnt].d);
        free_real(names);
        return -1;
    }
    *errno_addr = old_errno;

    if (cmp) {
        assert(cmp == alphasort || cmp == versionsort); // we support only these two for now
        qsort_real(names, cnt, sizeof *names, (int (*)(const void *, const void *))cmp);
    }

    // instrument final *res and all its items (of type struct dirent*) with sgxbounds
    *res = 0;
    if (names) {
        *res = malloc_real(cnt * sizeof(struct dirent *) + PTRSIZE);
        if (!*res) return -1;
        for (i = 0; i < cnt; i++) {
            (*res)[i] = specifybounds(names[i].d, names[i].l);
        }
        *res = specifybounds(*res, cnt * sizeof(struct dirent *));
        free_real(names);
    }

    return cnt;
}

int scandir64(const char *path, struct dirent ***res,
    int (*sel)(const struct dirent *),
    int (*cmp)(const struct dirent **, const struct dirent **))
{
    return scandir(path, res, sel, cmp);
}

/* ------------------------------------------------------------------------- */
/* ----------------------------- setjmp/longjmp ---------------------------- */
/* ------------------------------------------------------------------------- */
int setjmp_real(jmp_buf);
_Noreturn void longjmp_real(jmp_buf, int);

int setjmp(jmp_buf b) {
    b = __sgxbounds_uninstrument(b);
    return setjmp_real(b);
}

_Noreturn void longjmp(jmp_buf b, int i) {
    b = __sgxbounds_uninstrument(b);
    longjmp_real(b, i);
}

/* ------------------------------------------------------------------------- */
/* ------------------------------- misc funcs  ----------------------------- */
/* ------------------------------------------------------------------------- */
// NOTE: ignoring openpty, login_tty, forkpty, ptsname, ptsname_r, wordexp

long a64l_real(const char *s);
char *l64a_real(long x0);
char *basename_real(char *s);
char *dirname_real(char *s);
int fmtmsg_real(long classification, const char *label, int severity, const char *text, const char *action, const char *tag);
char *get_current_dir_name_real(void);
int getdomainname_real(char *name, size_t len);
int getopt_real(int argc, char * const argv[], const char *optstring);
int getopt_long_real(int argc, char *const *argv, const char *optstring, const struct option *longopts, int *idx);
int getopt_long_only_real(int argc, char *const *argv, const char *optstring, const struct option *longopts, int *idx);
int getresgid_real(gid_t *rgid, gid_t *egid, gid_t *sgid);
int getresuid_real(uid_t *ruid, uid_t *euid, uid_t *suid);
int getrlimit_real(int resource, struct rlimit *rlim);
int getrlimit64_real(int resource, struct rlimit *rlim);
int getrusage_real(int who, struct rusage *ru);
int getsubopt_real(char **opt, char *const *keys, char **val);
int initgroups_real(const char *user, gid_t gid);
FILE *setmntent_real(const char *name, const char *mode);
struct mntent *getmntent_r_real(FILE *f, struct mntent *mnt, char *linebuf, int buflen);
struct mntent *getmntent_real(FILE *f);
int addmntent_real(FILE *f, const struct mntent *mnt);
char *hasmntopt_real(const struct mntent *mnt, const char *opt);
int nftw_real(const char *path, int (*fn)(const char *, const struct stat *, int, struct FTW *), int fd_limit, int flags);
int nftw64_real(const char *path, int (*fn)(const char *, const struct stat *, int, struct FTW *), int fd_limit, int flags);
char *realpath_real(const char *restrict filename, char *restrict resolved);
int setdomainname_real(const char *name, size_t len);
int setrlimit_real(int resource, const struct rlimit *rlim);
int setrlimit64_real(int resource, const struct rlimit *rlim);
void openlog_real(const char *ident, int opt, int facility);
void syslog_real(int priority, const char *message, ...);
void vsyslog_real(int priority, const char *message, va_list ap);
int uname_real(struct utsname *uts);
int ioctl_real(int fd, int req, ...);

long a64l(const char *s) {
    s = __sgxbounds_uninstrument(s);
    return a64l_real(s);
}

struct smallcharbuf {
    char buf[7];
    PTRTYPE lbnd;
};

char *l64a(long x0) {
    static struct smallcharbuf buf = {.lbnd = 0};
    if (buf.lbnd == 0)  buf.lbnd = (PTRTYPE)&buf;
    char* ret = l64a_real(x0);
    strcpy_real(buf.buf, ret);
    return __sgxbounds_combine_ptr(&buf, (PTRTYPE)&(buf.lbnd));
}

char *basename(char *s) {
    char* sval = NULL;
    if (s)  sval = __sgxbounds_uninstrument(s);
    char* ret = basename_real(sval);
    if (strlen_real(ret) == 1 && ret[0] == '.') {
        // returned constant string "."
        static struct smallcharbuf buf = {.lbnd = 0};
        if (buf.lbnd == 0) {
            buf.lbnd = (PTRTYPE)&buf;
            strcpy(buf.buf, ".");
        }
        ret = __sgxbounds_combine_ptr(&buf, (PTRTYPE)&(buf.lbnd));
    } else {
        // ret points into s, so uses its bounds
        PTRTYPE ubnd = __sgxbounds_extract_ubnd(s);
        ret = __sgxbounds_combine_ptr(ret, ubnd);
    }
    return ret;
}

char *dirname(char *s) {
    char* sval = NULL;
    if (s)  sval = __sgxbounds_uninstrument(s);
    char* ret = dirname_real(sval);
    if (strlen_real(ret) == 1 && ret[0] == '.') {
        // returned constant string "."
        static struct smallcharbuf buf = {.lbnd = 0};
        if (buf.lbnd == 0) {
            buf.lbnd = (PTRTYPE)&buf;
            strcpy(buf.buf, ".");
        }
        ret = __sgxbounds_combine_ptr(&buf, (PTRTYPE)&(buf.lbnd));
    } else if (strlen_real(ret) == 1 && ret[0] == '/') {
        // returned constant string "/"
        static struct smallcharbuf buf = {.lbnd = 0};
        if (buf.lbnd == 0) {
            buf.lbnd = (PTRTYPE)&buf;
            strcpy(buf.buf, "/");
        }
        ret = __sgxbounds_combine_ptr(&buf, (PTRTYPE)&(buf.lbnd));
    } else {
        // ret points into s, so uses its bounds
        PTRTYPE ubnd = __sgxbounds_extract_ubnd(s);
        ret = __sgxbounds_combine_ptr(ret, ubnd);
    }
    return ret;
}

int fmtmsg(long classification, const char *label, int severity,
           const char *text, const char *action, const char *tag) {
    label  = __sgxbounds_uninstrument(label);
    text   = __sgxbounds_uninstrument(text);
    action = __sgxbounds_uninstrument(action);
    tag    = __sgxbounds_uninstrument(tag);
    return fmtmsg_real(classification, label, severity, text, action, tag);
}

char *get_current_dir_name(void) {
    // use tmp for real func and copy it using our instrumented version of strdup
    char* tmp = get_current_dir_name_real();
    char* ret =__sgxbounds_strdup(tmp);
    free_real(tmp);
    return ret;
}

int getdomainname(char *name, size_t len) {
    name = __sgxbounds_uninstrument(name);
    return getdomainname_real(name, len);
}

extern char* optarg;
int getopt(int argc, char * const argv[], const char *optstring) {
    char** inargv = malloc_real(sizeof(char*) * argc);
    optstring = __sgxbounds_uninstrument(optstring);
    argv = __sgxbounds_uninstrument(argv);
    for (int i=0; i<argc; i++)
        inargv[i] = __sgxbounds_uninstrument(argv[i]);
    int ret = getopt_real(argc, inargv, optstring);
    if (ret != -1 && optarg) {
        PTRTYPE ubnd = __sgxbounds_highest_bound();
        optarg = __sgxbounds_combine_ptr(optarg, ubnd);
    }
    free_real(inargv);
    return ret;
}

int getopt_long(int argc, char *const *argv, const char *optstring, const struct option *longopts, int *idx) {
    static struct option inlongopts[128];
    struct option *inlongoptsptr = NULL;

    char** inargv = malloc_real(sizeof(char*) * argc);
    optstring = __sgxbounds_uninstrument(optstring);
    if (longopts) {
        longopts = __sgxbounds_uninstrument(longopts);
        inlongoptsptr = &inlongopts[0];

        int i = 0;
        while (longopts[i].name) {
            inlongopts[i].name    = __sgxbounds_uninstrument(longopts[i].name);
            inlongopts[i].flag    = __sgxbounds_uninstrument(longopts[i].flag);
            inlongopts[i].has_arg = longopts[i].has_arg;
            inlongopts[i].val     = longopts[i].val;
            i++;
        }
        inlongopts[i].name = NULL;
        inlongopts[i].flag = NULL;
        inlongopts[i].has_arg = inlongopts[i].val = 0;
    }
    if (idx)
        idx = __sgxbounds_uninstrument(idx);

    argv = __sgxbounds_uninstrument(argv);
    for (int i=0; i<argc; i++)
        inargv[i] = __sgxbounds_uninstrument(argv[i]);
    int ret = getopt_long_real(argc, inargv, optstring, inlongoptsptr, idx);
    if (ret != -1 && optarg) {
        PTRTYPE ubnd = __sgxbounds_highest_bound();
        optarg = __sgxbounds_combine_ptr(optarg, ubnd);
    }
    free_real(inargv);
    return ret;
}

#ifndef SGXBOUNDS_NO_GETOPTLONGONLY
int getopt_long_only(int argc, char *const *argv, const char *optstring, const struct option *longopts, int *idx) {
    // NOTE: must be identical to getopt_long but calling another real func
    static struct option inlongopts[128];
    struct option *inlongoptsptr = NULL;

    char** inargv = malloc_real(sizeof(char*) * argc);
    optstring = __sgxbounds_uninstrument(optstring);
    if (longopts) {
        longopts = __sgxbounds_uninstrument(longopts);
        inlongoptsptr = &inlongopts[0];

        int i = 0;
        while (longopts[i].name) {
            inlongopts[i].name    = __sgxbounds_uninstrument(longopts[i].name);
            inlongopts[i].flag    = __sgxbounds_uninstrument(longopts[i].flag);
            inlongopts[i].has_arg = longopts[i].has_arg;
            inlongopts[i].val     = longopts[i].val;
            i++;
        }
        inlongopts[i].name = NULL;
        inlongopts[i].flag = NULL;
        inlongopts[i].has_arg = inlongopts[i].val = 0;
    }
    if (idx)
        idx = __sgxbounds_uninstrument(idx);

    argv = __sgxbounds_uninstrument(argv);
    for (int i=0; i<argc; i++)
        inargv[i] = __sgxbounds_uninstrument(argv[i]);
    int ret = getopt_long_only_real(argc, inargv, optstring, inlongoptsptr, idx);
    if (ret != -1 && optarg) {
        PTRTYPE ubnd = __sgxbounds_highest_bound();
        optarg = __sgxbounds_combine_ptr(optarg, ubnd);
    }
    free_real(inargv);
    return ret;
}
#endif

int getresgid(gid_t *rgid, gid_t *egid, gid_t *sgid) {
    rgid = __sgxbounds_uninstrument(rgid);
    egid = __sgxbounds_uninstrument(egid);
    sgid = __sgxbounds_uninstrument(sgid);
    return getresgid_real(rgid, egid, sgid);
}

int getresuid(uid_t *ruid, uid_t *euid, uid_t *suid) {
    ruid = __sgxbounds_uninstrument(ruid);
    euid = __sgxbounds_uninstrument(euid);
    suid = __sgxbounds_uninstrument(suid);
    return getresuid_real(ruid, euid, suid);
}

int getrlimit(int resource, struct rlimit *rlim) {
    rlim = __sgxbounds_uninstrument(rlim);
    return getrlimit_real(resource, rlim);
}

int getrlimit64(int resource, struct rlimit *rlim) {
    return getrlimit(resource, rlim);
}

int getrusage(int who, struct rusage *ru) {
    ru = __sgxbounds_uninstrument(ru);
    return getrusage_real(who, ru);
}

int getsubopt(char **opt, char *const *keys, char **val) {
    // NOTE: array size is chosen arbitrarily but must suffice
    char** inkeys = calloc_real(64, sizeof(char*));

    val = __sgxbounds_uninstrument(val);
    opt = __sgxbounds_uninstrument(opt);
    char* prevopt = *opt;
    *opt = __sgxbounds_uninstrument(*opt);
    keys = __sgxbounds_uninstrument(keys);
    for (int i=0; i<64; i++) {
        if (!keys[i])  break;
        inkeys[i] = __sgxbounds_uninstrument(keys[i]);
    }
    inkeys[63] = NULL;  // for sanity

    int ret = getsubopt_real(opt, inkeys, val);
    if (*val) {
        // val points into *opt, so uses its bounds
        PTRTYPE ubnd = __sgxbounds_extract_ubnd(prevopt);
        *val = __sgxbounds_combine_ptr(*val, ubnd);
    }
    if (*opt) {
        // *opt can be changed, but uses its own bounds
        PTRTYPE ubnd = __sgxbounds_extract_ubnd(prevopt);
        *opt = __sgxbounds_combine_ptr(*opt, ubnd);
    }
    free_real(inkeys);
    return ret;
}

int initgroups(const char *user, gid_t gid) {
    user = __sgxbounds_uninstrument(user);
    return initgroups_real(user, gid);
}

FILE *setmntent(const char *name, const char *mode) {
    name = __sgxbounds_uninstrument(name);
    mode = __sgxbounds_uninstrument(mode);
    return setmntent_real(name, mode);
}

struct mntent *getmntent_r(FILE *f, struct mntent *mnt, char *linebuf, int buflen) {
    struct mntent *mntval = __sgxbounds_uninstrument(mnt);
    char * linebufval = __sgxbounds_uninstrument(linebuf);
    struct mntent *ret = getmntent_r_real(f, mntval, linebufval, buflen);
    if (ret) {
        // all subfields of ret are ptrs inside linebuf, so use its bounds
        PTRTYPE ubnd = __sgxbounds_extract_ubnd(linebuf);
        ret->mnt_fsname = __sgxbounds_combine_ptr(ret->mnt_fsname, ubnd);
        ret->mnt_dir    = __sgxbounds_combine_ptr(ret->mnt_dir, ubnd);
        ret->mnt_type   = __sgxbounds_combine_ptr(ret->mnt_type, ubnd);
        ret->mnt_opts   = __sgxbounds_combine_ptr(ret->mnt_opts, ubnd);
        ret = mnt;  // func returns ptr to initial mnt
    }
    return ret;
}

struct mtentbuf {
    struct mntent buf;
    PTRTYPE lbnd;
};

struct mntent *getmntent(FILE *f) {
    static struct charbuf buf = {.lbnd = 0};
    if (buf.lbnd == 0)  buf.lbnd = (PTRTYPE)&buf;
    static struct mtentbuf mnt = {.lbnd = 0};
    if (mnt.lbnd == 0)  mnt.lbnd = (PTRTYPE)&mnt;
    struct mntent *inmnt = __sgxbounds_combine_ptr(&mnt, (PTRTYPE)&mnt.lbnd);
    char *inbuf = __sgxbounds_combine_ptr(&buf, (PTRTYPE)&buf.lbnd);
    return getmntent_r(f, inmnt, inbuf, sizeof(buf.buf));
}

int addmntent(FILE *f, const struct mntent *mnt) {
    struct mntent inmnt;
    mnt = __sgxbounds_uninstrument(mnt);
    inmnt.mnt_fsname = __sgxbounds_uninstrument(mnt->mnt_fsname);
    inmnt.mnt_dir    = __sgxbounds_uninstrument(mnt->mnt_dir);
    inmnt.mnt_type   = __sgxbounds_uninstrument(mnt->mnt_type);
    inmnt.mnt_opts   = __sgxbounds_uninstrument(mnt->mnt_opts);
    inmnt.mnt_freq   = mnt->mnt_freq;
    inmnt.mnt_passno = mnt->mnt_passno;
    return addmntent_real(f, &inmnt);
}

char *hasmntopt(const struct mntent *mnt, const char *opt) {
    struct mntent inmnt;
    mnt = __sgxbounds_uninstrument(mnt);
    inmnt.mnt_opts = __sgxbounds_uninstrument(mnt->mnt_opts);
    opt = __sgxbounds_uninstrument(opt);
    char* ret = hasmntopt_real(&inmnt, opt);
    if (ret) {
        // ret points inside mnt->mnt_opts, so use its bounds
        PTRTYPE ubnd = __sgxbounds_extract_ubnd(mnt->mnt_opts);
        ret = __sgxbounds_combine_ptr(ret, ubnd);
    }
    return ret;
}

typedef int (*nftw_fn_fun)(const char *, const struct stat *, int, struct FTW *);

struct statbuf {
    struct stat buf;
    PTRTYPE lbnd;
};

struct ftwbuf {
    struct FTW buf;
    PTRTYPE lbnd;
};

static __thread nftw_fn_fun  nftw_fn_fun_real;

static int nftw_fn(const char *fpath, const struct stat *sb, int typeflag, struct FTW *ftw) {
    static __thread struct charbuf fpathbuf;
    static __thread struct statbuf sbbuf;
    static __thread struct ftwbuf  ftwbuf;

    if (fpathbuf.lbnd == 0)  fpathbuf.lbnd = (PTRTYPE)&fpathbuf;
    if (sbbuf.lbnd == 0)     sbbuf.lbnd    = (PTRTYPE)&sbbuf;
    if (ftwbuf.lbnd == 0)    ftwbuf.lbnd   = (PTRTYPE)&ftwbuf;

    strcpy_real(fpathbuf.buf, fpath);
    memcpy_real(&sbbuf.buf, sb, sizeof(struct stat));
    memcpy_real(&ftwbuf.buf, ftw, sizeof(struct FTW));

    char *fpathbufptr     = __sgxbounds_combine_ptr(&fpathbuf, (PTRTYPE)&fpathbuf.lbnd);
    struct stat *sbbufptr = __sgxbounds_combine_ptr(&sbbuf, (PTRTYPE)&sbbuf.lbnd);
    struct FTW *ftwbufptr = __sgxbounds_combine_ptr(&ftwbuf, (PTRTYPE)&ftwbuf.lbnd);

    return nftw_fn_fun_real(fpathbufptr, sbbufptr, typeflag, ftwbufptr);
}

int nftw(const char *path, int (*fn)(const char *, const struct stat *, int, struct FTW *), int fd_limit, int flags) {
    // memorize the real fn function supplied by user
    nftw_fn_fun_real = fn;
    // continue with real uninstrumented nftw(); it will call fn
    // which copies & instruments all args and forwards to real fn
    path = __sgxbounds_uninstrument(path);
    return nftw_real(path, nftw_fn, fd_limit, flags);
}

int nftw64(const char *path, int (*fn)(const char *, const struct stat *, int, struct FTW *), int fd_limit, int flags) {
    return nftw(path, fn, fd_limit, flags);
}

char *realpath(const char *restrict filename, char *restrict resolved) {
    filename = __sgxbounds_uninstrument(filename);
    char* resolvedval = __sgxbounds_uninstrument(resolved);
    char* ret = realpath_real(filename, resolvedval);
    if (ret)
        ret = resolved;
    return ret;
}

int setdomainname(const char *name, size_t len) {
    name = __sgxbounds_uninstrument(name);
    return setdomainname_real(name, len);
}

int setrlimit(int resource, const struct rlimit *rlim) {
    rlim = __sgxbounds_uninstrument(rlim);
    return setrlimit_real(resource, rlim);
}

int setrlimit64(int resource, const struct rlimit *rlim) {
    return setrlimit(resource, rlim);
}

void openlog(const char *ident, int opt, int facility) {
    ident = __sgxbounds_uninstrument(ident);
    openlog_real(ident, opt, facility);
}

void syslog(int priority, const char *message, ...) {
    message = __sgxbounds_uninstrument(message);
    va_list ap;
    va_start(ap, message);
    vsyslog_real(priority, message, ap);
    va_end(ap);
}

void vsyslog(int priority, const char *message, va_list ap) {
    ap = __sgxbounds_uninstrument((void*)ap);
    message = __sgxbounds_uninstrument(message);
    vsyslog_real(priority, message, ap);
}

int uname(struct utsname *uts) {
    uts = __sgxbounds_uninstrument(uts);
    return uname_real(uts);
}

int ioctl(int fd, int req, ...) {
    void *arg;
    va_list ap;
    va_start(ap, req);
    arg = va_arg(ap, void *);
    va_end(ap);

    if (arg)  arg = __sgxbounds_uninstrument(arg);
    return ioctl_real(fd, req, arg);
}


/* ------------------------------------------------------------------------- */
/* ----------------------------- select funcs  ----------------------------- */
/* ------------------------------------------------------------------------- */
int poll_real(struct pollfd *fds, nfds_t n, int timeout);
int pselect_real(int n, fd_set *restrict rfds, fd_set *restrict wfds, fd_set *restrict efds, const struct timespec *restrict ts, const sigset_t *restrict mask);
int select_real(int n, fd_set *restrict rfds, fd_set *restrict wfds, fd_set *restrict efds, struct timeval *restrict tv);

int poll(struct pollfd *fds, nfds_t n, int timeout) {
    fds = __sgxbounds_uninstrument(fds);
    return poll_real(fds, n, timeout);
}

int pselect(int n, fd_set *restrict rfds, fd_set *restrict wfds, fd_set *restrict efds, const struct timespec *restrict ts, const sigset_t *restrict mask) {
    if (rfds)
        rfds = __sgxbounds_uninstrument(rfds);
    if (wfds)
        wfds = __sgxbounds_uninstrument(wfds);
    if (efds)
        efds = __sgxbounds_uninstrument(efds);
    if (ts)
        ts = __sgxbounds_uninstrument(ts);
    if (mask)
        mask = __sgxbounds_uninstrument(mask);
    return pselect_real(n, rfds, wfds, efds, ts, mask);
}

int select(int n, fd_set *restrict rfds, fd_set *restrict wfds, fd_set *restrict efds, struct timeval *restrict tv) {
    if (rfds)
        rfds = __sgxbounds_uninstrument(rfds);
    if (wfds)
        wfds = __sgxbounds_uninstrument(wfds);
    if (efds)
        efds = __sgxbounds_uninstrument(efds);
    if (tv)
        tv = __sgxbounds_uninstrument(tv);
    return select_real(n, rfds, wfds, efds, tv);
}

/* ------------------------------------------------------------------------- */
/* ----------------------------- thread funcs  ----------------------------- */
/* ------------------------------------------------------------------------- */
// NOTE: ignore all funcs to do with clone, fork, and raw syscalls
// NOTE: pthread_t is treated as opaque and thus not instrumented, but others
//       (e.g., pthread_attr_t) are allocated by app and thus instrumented
int pthread_attr_getdetachstate_real(const pthread_attr_t *a, int *state);
int pthread_attr_getguardsize_real(const pthread_attr_t *restrict a, size_t *restrict size);
int pthread_attr_getinheritsched_real(const pthread_attr_t *restrict a, int *restrict inherit);
int pthread_attr_getschedparam_real(const pthread_attr_t *restrict a, struct sched_param *restrict param);
int pthread_attr_getschedpolicy_real(const pthread_attr_t *restrict a, int *restrict policy);
int pthread_attr_getscope_real(const pthread_attr_t *restrict a, int *restrict scope);
int pthread_attr_getstack_real(const pthread_attr_t *restrict a, void **restrict addr, size_t *restrict size);
int pthread_attr_getstacksize_real(const pthread_attr_t *restrict a, size_t *restrict size);
int pthread_barrierattr_getpshared_real(const pthread_barrierattr_t *restrict a, int *restrict pshared);
int pthread_condattr_getclock_real(const pthread_condattr_t *restrict a, clockid_t *restrict clk);
int pthread_condattr_getpshared_real(const pthread_condattr_t *restrict a, int *restrict pshared);
int pthread_mutexattr_getprotocol_real(const pthread_mutexattr_t *restrict a, int *restrict protocol);
int pthread_mutexattr_getpshared_real(const pthread_mutexattr_t *restrict a, int *restrict pshared);
int pthread_mutexattr_getrobust_real(const pthread_mutexattr_t *restrict a, int *restrict robust);
int pthread_mutexattr_gettype_real(const pthread_mutexattr_t *restrict a, int *restrict type);
int pthread_rwlockattr_getpshared_real(const pthread_rwlockattr_t *restrict a, int *restrict pshared);
int pthread_attr_setstack_real(pthread_attr_t *a, void *addr, size_t size);
int pthread_cond_timedwait_real(pthread_cond_t *restrict c, pthread_mutex_t *restrict m, const struct timespec *restrict ts);
int pthread_create_real(pthread_t *restrict res, const pthread_attr_t *restrict attrp, void *(*entry)(void *), void *restrict arg);
int pthread_getcpuclockid_real(pthread_t t, clockid_t *clockid);
int pthread_getschedparam_real(pthread_t t, int *restrict policy, struct sched_param *restrict param);
int pthread_join_real(pthread_t t, void **res);
int pthread_mutex_getprioceiling_real(const pthread_mutex_t *restrict m, int *restrict ceiling);
int pthread_mutex_setprioceiling_real(pthread_mutex_t *restrict m, int ceiling, int *restrict old);
int pthread_mutex_timedlock_real(pthread_mutex_t *restrict m, const struct timespec *restrict at);
int pthread_rwlock_timedrdlock_real(pthread_rwlock_t *restrict rw, const struct timespec *restrict at);
int pthread_rwlock_timedwrlock_real(pthread_rwlock_t *restrict rw, const struct timespec *restrict at);
int pthread_setcancelstate_real(int new, int *old);
int pthread_setcanceltype_real(int new, int *old);
int pthread_setschedparam_real(pthread_t t, int policy, const struct sched_param *param);
int pthread_setspecific_real(pthread_key_t k, const void *x);
void *pthread_getspecific_real(pthread_key_t k);
int sem_getvalue_real(sem_t *restrict sem, int *restrict valp);
sem_t *sem_open_real(const char *name, int flags, ...);
int sem_timedwait_real(sem_t *restrict sem, const struct timespec *restrict at);
int sem_unlink_real(const char *name);
int pthread_attr_destroy_real(pthread_attr_t *a);
int pthread_attr_init_real(pthread_attr_t *a);
int pthread_attr_setdetachstate_real(pthread_attr_t *a, int state);
int pthread_attr_setguardsize_real(pthread_attr_t *a, size_t size);
int pthread_attr_setinheritsched_real(pthread_attr_t *a, int inherit);
int pthread_attr_setschedparam_real(pthread_attr_t *restrict a, const struct sched_param *restrict param);
int pthread_attr_setschedpolicy_real(pthread_attr_t *a, int policy);
int pthread_attr_setscope_real(pthread_attr_t *a, int scope);
int pthread_attr_setstacksize_real(pthread_attr_t *a, size_t size);
int pthread_barrierattr_destroy_real(pthread_barrierattr_t *a);
int pthread_barrierattr_init_real(pthread_barrierattr_t *a);
int pthread_barrierattr_setpshared_real(pthread_barrierattr_t *a, int pshared);
int pthread_barrier_destroy_real(pthread_barrier_t *b);
int pthread_barrier_init_real(pthread_barrier_t *restrict b, const pthread_barrierattr_t *restrict a, unsigned count);
int pthread_barrier_wait_real(pthread_barrier_t *b);
int pthread_condattr_destroy_real(pthread_condattr_t *a);
int pthread_condattr_init_real(pthread_condattr_t *a);
int pthread_condattr_setclock_real(pthread_condattr_t *a, clockid_t clk);
int pthread_condattr_setpshared_real(pthread_condattr_t *a, int pshared);
int pthread_cond_broadcast_real(pthread_cond_t *c);
int pthread_cond_destroy_real(pthread_cond_t *c);
int pthread_cond_init_real(pthread_cond_t *restrict c, const pthread_condattr_t *restrict a);
int pthread_cond_signal_real(pthread_cond_t *c);
int pthread_cond_wait_real(pthread_cond_t *restrict c, pthread_mutex_t *restrict m);
int pthread_getattr_np_real(pthread_t t, pthread_attr_t *a);
int pthread_key_create_real(pthread_key_t *k, void (*dtor)(void *));
int pthread_mutexattr_destroy_real(pthread_mutexattr_t *a);
int pthread_mutexattr_init_real(pthread_mutexattr_t *a);
int pthread_mutexattr_setprotocol_real(pthread_mutexattr_t *a, int protocol);
int pthread_mutexattr_setpshared_real(pthread_mutexattr_t *a, int pshared);
int pthread_mutexattr_setrobust_real(pthread_mutexattr_t *a, int robust);
int pthread_mutexattr_settype_real(pthread_mutexattr_t *a, int type);
int pthread_mutex_consistent_real(pthread_mutex_t *m);
int pthread_mutex_destroy_real(pthread_mutex_t *mutex);
int pthread_mutex_init_real(pthread_mutex_t *restrict m, const pthread_mutexattr_t *restrict a);
int pthread_mutex_lock_real(pthread_mutex_t *m);
int pthread_mutex_trylock_real(pthread_mutex_t *m);
int pthread_mutex_unlock_real(pthread_mutex_t *m);
int pthread_once_real(pthread_once_t *control, void (*init)(void));
int pthread_rwlockattr_destroy_real(pthread_rwlockattr_t *a);
int pthread_rwlockattr_init_real(pthread_rwlockattr_t *a);
int pthread_rwlockattr_setpshared_real(pthread_rwlockattr_t *a, int pshared);
int pthread_rwlock_destroy_real(pthread_rwlock_t *rw);
int pthread_rwlock_init_real(pthread_rwlock_t *restrict rw, const pthread_rwlockattr_t *restrict a);
int pthread_rwlock_rdlock_real(pthread_rwlock_t *rw);
int pthread_rwlock_tryrdlock_real(pthread_rwlock_t *rw);
int pthread_rwlock_trywrlock_real(pthread_rwlock_t *rw);
int pthread_rwlock_unlock_real(pthread_rwlock_t *rw);
int pthread_rwlock_wrlock_real(pthread_rwlock_t *rw);
int pthread_sigmask_real(int how, const sigset_t *restrict set, sigset_t *restrict old);
int sem_destroy_real(sem_t *sem);
int sem_init_real(sem_t *sem, int pshared, unsigned value);
int sem_post_real(sem_t *sem);
int sem_trywait_real(sem_t *sem);
int sem_wait_real(sem_t *sem);

int pthread_attr_getdetachstate(const pthread_attr_t *a, int *state) {
    a = __sgxbounds_uninstrument(a);
    state = __sgxbounds_uninstrument(state);
    return pthread_attr_getdetachstate_real(a, state);
}

int pthread_attr_getguardsize(const pthread_attr_t *restrict a, size_t *restrict size) {
    a = __sgxbounds_uninstrument(a);
    size = __sgxbounds_uninstrument(size);
    return pthread_attr_getguardsize_real(a, size);
}

int pthread_attr_getinheritsched(const pthread_attr_t *restrict a, int *restrict inherit) {
    a = __sgxbounds_uninstrument(a);
    inherit = __sgxbounds_uninstrument(inherit);
    return pthread_attr_getinheritsched_real(a, inherit);
}

int pthread_attr_getschedparam(const pthread_attr_t *restrict a, struct sched_param *restrict param) {
    a = __sgxbounds_uninstrument(a);
    param = __sgxbounds_uninstrument(param);
    return pthread_attr_getschedparam_real(a, param);
}

int pthread_attr_getschedpolicy(const pthread_attr_t *restrict a, int *restrict policy) {
    a = __sgxbounds_uninstrument(a);
    policy = __sgxbounds_uninstrument(policy);
    return pthread_attr_getschedpolicy_real(a, policy);
}

int pthread_attr_getscope(const pthread_attr_t *restrict a, int *restrict scope) {
    a = __sgxbounds_uninstrument(a);
    scope = __sgxbounds_uninstrument(scope);
    return pthread_attr_getscope_real(a, scope);
}

int pthread_attr_getstack(const pthread_attr_t *restrict a, void **restrict addr, size_t *restrict size) {
    // NOTE: this func messes with stack, we disallow it
    return 1;
}

int pthread_attr_getstacksize(const pthread_attr_t *restrict a, size_t *restrict size) {
    a = __sgxbounds_uninstrument(a);
    size = __sgxbounds_uninstrument(size);
    return pthread_attr_getstacksize_real(a, size);
}

int pthread_barrierattr_getpshared(const pthread_barrierattr_t *restrict a, int *restrict pshared) {
    a = __sgxbounds_uninstrument(a);
    pshared = __sgxbounds_uninstrument(pshared);
    return pthread_barrierattr_getpshared_real(a, pshared);
}

int pthread_condattr_getclock(const pthread_condattr_t *restrict a, clockid_t *restrict clk) {
    a = __sgxbounds_uninstrument(a);
    clk = __sgxbounds_uninstrument(clk);
    return pthread_condattr_getclock_real(a, clk);
}

int pthread_condattr_getpshared(const pthread_condattr_t *restrict a, int *restrict pshared) {
    a = __sgxbounds_uninstrument(a);
    pshared = __sgxbounds_uninstrument(pshared);
    return pthread_condattr_getpshared_real(a, pshared);
}

int pthread_mutexattr_getprotocol(const pthread_mutexattr_t *restrict a, int *restrict protocol) {
    a = __sgxbounds_uninstrument(a);
    protocol = __sgxbounds_uninstrument(protocol);
    return pthread_mutexattr_getprotocol_real(a, protocol);
}

int pthread_mutexattr_getpshared(const pthread_mutexattr_t *restrict a, int *restrict pshared) {
    a = __sgxbounds_uninstrument(a);
    pshared = __sgxbounds_uninstrument(pshared);
    return pthread_mutexattr_getpshared_real(a, pshared);
}

int pthread_mutexattr_getrobust(const pthread_mutexattr_t *restrict a, int *restrict robust) {
    a = __sgxbounds_uninstrument(a);
    robust = __sgxbounds_uninstrument(robust);
    return pthread_mutexattr_getrobust_real(a, robust);
}

int pthread_mutexattr_gettype(const pthread_mutexattr_t *restrict a, int *restrict type) {
    a = __sgxbounds_uninstrument(a);
    type = __sgxbounds_uninstrument(type);
    return pthread_mutexattr_gettype_real(a, type);
}

int pthread_rwlockattr_getpshared(const pthread_rwlockattr_t *restrict a, int *restrict pshared) {
    a = __sgxbounds_uninstrument(a);
    pshared = __sgxbounds_uninstrument(pshared);
    return pthread_rwlockattr_getpshared_real(a, pshared);
}

int pthread_attr_setstack(pthread_attr_t *a, void *addr, size_t size) {
    // NOTE: this func messes with stack, we disallow it
    return 1;
}

int pthread_cond_timedwait(pthread_cond_t *restrict c, pthread_mutex_t *restrict m, const struct timespec *restrict ts) {
    c = __sgxbounds_uninstrument(c);
    m = __sgxbounds_uninstrument(m);
    ts = __sgxbounds_uninstrument(ts);
    return pthread_cond_timedwait_real(c, m, ts);
}

int pthread_create(pthread_t *restrict res, const pthread_attr_t *restrict attrp, void *(*entry)(void *), void *restrict arg) {
    // NOTE: no need to uninstrument:
    //         - entry is function ptr which we do not instrument
    //         - arg will be forwarded to entry() as-is, instrumented
    res = __sgxbounds_uninstrument(res);
    if (attrp)  attrp = __sgxbounds_uninstrument(attrp);

    return pthread_create_real(res, attrp, entry, arg);
}

int pthread_getcpuclockid(pthread_t t, clockid_t *clockid) {
    clockid = __sgxbounds_uninstrument(clockid);
    return pthread_getcpuclockid_real(t, clockid);
}

int pthread_getschedparam(pthread_t t, int *restrict policy, struct sched_param *restrict param) {
    policy = __sgxbounds_uninstrument(policy);
    param  = __sgxbounds_uninstrument(param);
    return pthread_getschedparam_real(t, policy, param);
}

int pthread_join(pthread_t t, void **res) {
    // NOTE: no need to care about *res since it is passed between instrumented funcs
    if (res)
        res  = __sgxbounds_uninstrument(res);
    return pthread_join_real(t, res);
}

int pthread_mutex_getprioceiling(const pthread_mutex_t *restrict m, int *restrict ceiling) {
    m       = __sgxbounds_uninstrument(m);
    ceiling = __sgxbounds_uninstrument(ceiling);
    return pthread_mutex_getprioceiling_real(m, ceiling);
}

int pthread_mutex_setprioceiling(pthread_mutex_t *restrict m, int ceiling, int *restrict old) {
    m   = __sgxbounds_uninstrument(m);
    old = __sgxbounds_uninstrument(old);
    return pthread_mutex_setprioceiling_real(m, ceiling, old);
}

int pthread_mutex_timedlock(pthread_mutex_t *restrict m, const struct timespec *restrict at) {
    m  = __sgxbounds_uninstrument(m);
    at = __sgxbounds_uninstrument(at);
    return pthread_mutex_timedlock_real(m, at);
}

int pthread_rwlock_timedrdlock(pthread_rwlock_t *restrict rw, const struct timespec *restrict at) {
    rw = __sgxbounds_uninstrument(rw);
    at = __sgxbounds_uninstrument(at);
    return pthread_rwlock_timedrdlock_real(rw, at);
}

int pthread_rwlock_timedwrlock(pthread_rwlock_t *restrict rw, const struct timespec *restrict at) {
    rw = __sgxbounds_uninstrument(rw);
    at = __sgxbounds_uninstrument(at);
    return pthread_rwlock_timedwrlock_real(rw, at);
}

int pthread_setcancelstate(int new, int *old) {
    old = __sgxbounds_uninstrument(old);
    return pthread_setcancelstate_real(new, old);
}

int pthread_setcanceltype(int new, int *old) {
    old = __sgxbounds_uninstrument(old);
    return pthread_setcanceltype_real(new, old);
}

int pthread_setschedparam(pthread_t t, int policy, const struct sched_param *param) {
    param = __sgxbounds_uninstrument(param);
    return pthread_setschedparam_real(t, policy, param);
}

int pthread_setspecific(pthread_key_t k, const void *x) {
    // NOTE: set value is not manipulated by libc so can keep instrumented
    return pthread_setspecific_real(k, x);
}

void *pthread_getspecific(pthread_key_t k) {
    // NOTE: ret value is not manipulated by libc so can keep instrumented
    return pthread_getspecific_real(k);
}

int sem_getvalue(sem_t *restrict sem, int *restrict valp) {
    sem  = __sgxbounds_uninstrument(sem);
    valp = __sgxbounds_uninstrument(valp);
    return sem_getvalue_real(sem, valp);
}

sem_t *sem_open(const char *name, int flags, ...) {
    //TODO: returned semaphor is not instrumented, and if passed to
    //      some other funcs will error since they expect instrumented
    va_list ap;
    name = __sgxbounds_uninstrument(name);
    if (flags & O_CREAT) {
        va_start(ap, flags);
        mode_t mode = va_arg(ap, mode_t);
        unsigned value = va_arg(ap, unsigned);
        va_end(ap);
        return sem_open_real(name, flags, mode, value);
    }
    // no O_CREAT in flags, call 2-arg version of sem_open()
    return sem_open_real(name, flags);
}

int sem_timedwait(sem_t *restrict sem, const struct timespec *restrict at) {
    sem = __sgxbounds_uninstrument(sem);
    at = __sgxbounds_uninstrument(at);
    return sem_timedwait_real(sem, at);
}

int sem_unlink(const char *name) {
    name = __sgxbounds_uninstrument(name);
    return sem_unlink_real(name);
}

int pthread_attr_destroy(pthread_attr_t *a) {
    a = __sgxbounds_uninstrument(a);
    return pthread_attr_destroy_real(a);
}

int pthread_attr_init(pthread_attr_t *a) {
    a = __sgxbounds_uninstrument(a);
    return pthread_attr_init_real(a);
}

int pthread_attr_setdetachstate(pthread_attr_t *a, int state) {
    a = __sgxbounds_uninstrument(a);
    return pthread_attr_setdetachstate_real(a, state);
}

int pthread_attr_setguardsize(pthread_attr_t *a, size_t size) {
    a = __sgxbounds_uninstrument(a);
    return pthread_attr_setguardsize_real(a, size);
}

int pthread_attr_setinheritsched(pthread_attr_t *a, int inherit) {
    a = __sgxbounds_uninstrument(a);
    return pthread_attr_setinheritsched_real(a, inherit);
}

int pthread_attr_setschedparam(pthread_attr_t *restrict a, const struct sched_param *restrict param) {
    a = __sgxbounds_uninstrument(a);
    param = __sgxbounds_uninstrument(param);
    return pthread_attr_setschedparam_real(a, param);
}

int pthread_attr_setschedpolicy(pthread_attr_t *a, int policy) {
    a = __sgxbounds_uninstrument(a);
    return pthread_attr_setschedpolicy_real(a, policy);
}

int pthread_attr_setscope(pthread_attr_t *a, int scope) {
    a = __sgxbounds_uninstrument(a);
    return pthread_attr_setscope_real(a, scope);
}

int pthread_attr_setstacksize(pthread_attr_t *a, size_t size) {
    a = __sgxbounds_uninstrument(a);
    return pthread_attr_setstacksize_real(a, size);
}

int pthread_barrierattr_destroy(pthread_barrierattr_t *a) {
    a = __sgxbounds_uninstrument(a);
    return pthread_barrierattr_destroy_real(a);
}

int pthread_barrierattr_init(pthread_barrierattr_t *a) {
    a = __sgxbounds_uninstrument(a);
    return pthread_barrierattr_init_real(a);
}

int pthread_barrierattr_setpshared(pthread_barrierattr_t *a, int pshared) {
    a = __sgxbounds_uninstrument(a);
    return pthread_barrierattr_setpshared_real(a, pshared);
}

int pthread_barrier_destroy(pthread_barrier_t *b) {
    b = __sgxbounds_uninstrument(b);
    return pthread_barrier_destroy_real(b);
}

int pthread_barrier_init(pthread_barrier_t *restrict b, const pthread_barrierattr_t *restrict a, unsigned count) {
    b = __sgxbounds_uninstrument(b);
    if (a)  a = __sgxbounds_uninstrument(a);
    return pthread_barrier_init_real(b, a, count);
}

int pthread_barrier_wait(pthread_barrier_t *b) {
    b = __sgxbounds_uninstrument(b);
    return pthread_barrier_wait_real(b);
}

int pthread_condattr_destroy(pthread_condattr_t *a) {
    a = __sgxbounds_uninstrument(a);
    return pthread_condattr_destroy_real(a);
}

int pthread_condattr_init(pthread_condattr_t *a) {
    a = __sgxbounds_uninstrument(a);
    return pthread_condattr_init_real(a);
}

int pthread_condattr_setclock(pthread_condattr_t *a, clockid_t clk) {
    a = __sgxbounds_uninstrument(a);
    return pthread_condattr_setclock_real(a, clk);
}

int pthread_condattr_setpshared(pthread_condattr_t *a, int pshared) {
    a = __sgxbounds_uninstrument(a);
    return pthread_condattr_setpshared_real(a, pshared);
}

int pthread_cond_broadcast(pthread_cond_t *c) {
    c = __sgxbounds_uninstrument(c);
    return pthread_cond_broadcast_real(c);
}

int pthread_cond_destroy(pthread_cond_t *c) {
    c = __sgxbounds_uninstrument(c);
    return pthread_cond_destroy_real(c);
}

int pthread_cond_init(pthread_cond_t *restrict c, const pthread_condattr_t *restrict a) {
    c = __sgxbounds_uninstrument(c);
    if (a)  a = __sgxbounds_uninstrument(a);
    return pthread_cond_init_real(c, a);
}

int pthread_cond_signal(pthread_cond_t *c) {
    c = __sgxbounds_uninstrument(c);
    return pthread_cond_signal_real(c);
}

int pthread_cond_wait(pthread_cond_t *restrict c, pthread_mutex_t *restrict m) {
    c = __sgxbounds_uninstrument(c);
    m = __sgxbounds_uninstrument(m);
    return pthread_cond_wait_real(c, m);
}

int pthread_getattr_np(pthread_t t, pthread_attr_t *a) {
    a = __sgxbounds_uninstrument(a);
    return pthread_getattr_np_real(t, a);
}

int pthread_key_create(pthread_key_t *k, void (*dtor)(void *)) {
    k = __sgxbounds_uninstrument(k);
    return pthread_key_create_real(k, dtor);
}

int pthread_mutexattr_destroy(pthread_mutexattr_t *a) {
    a = __sgxbounds_uninstrument(a);
    return pthread_mutexattr_destroy_real(a);
}

int pthread_mutexattr_init(pthread_mutexattr_t *a) {
    a = __sgxbounds_uninstrument(a);
    return pthread_mutexattr_init_real(a);
}

int pthread_mutexattr_setprotocol(pthread_mutexattr_t *a, int protocol) {
    a = __sgxbounds_uninstrument(a);
    return pthread_mutexattr_setprotocol_real(a, protocol);
}

int pthread_mutexattr_setpshared(pthread_mutexattr_t *a, int pshared) {
    a = __sgxbounds_uninstrument(a);
    return pthread_mutexattr_setpshared_real(a, pshared);
}

int pthread_mutexattr_setrobust(pthread_mutexattr_t *a, int robust) {
    a = __sgxbounds_uninstrument(a);
    return pthread_mutexattr_setrobust_real(a, robust);
}

int pthread_mutexattr_settype(pthread_mutexattr_t *a, int type) {
    a = __sgxbounds_uninstrument(a);
    return pthread_mutexattr_settype_real(a, type);
}

int pthread_mutex_consistent(pthread_mutex_t *m) {
    m = __sgxbounds_uninstrument(m);
    return pthread_mutex_consistent_real(m);
}

int pthread_mutex_destroy(pthread_mutex_t *mutex) {
    mutex = __sgxbounds_uninstrument(mutex);
    return pthread_mutex_destroy_real(mutex);
}

int pthread_mutex_init(pthread_mutex_t *restrict m, const pthread_mutexattr_t *restrict a) {
    m = __sgxbounds_uninstrument(m);
    if (a)  a = __sgxbounds_uninstrument(a);
    return pthread_mutex_init_real(m, a);
}

//__attribute__((noinline))
int pthread_mutex_lock(pthread_mutex_t *m) {
    m = __sgxbounds_uninstrument(m);
    return pthread_mutex_lock_real(m);
}

int pthread_mutex_trylock(pthread_mutex_t *m) {
    m = __sgxbounds_uninstrument(m);
    return pthread_mutex_trylock_real(m);
}

int pthread_mutex_unlock(pthread_mutex_t *m) {
    m = __sgxbounds_uninstrument(m);
    return pthread_mutex_unlock_real(m);
}

int pthread_once(pthread_once_t *control, void (*init)(void)) {
    control = __sgxbounds_uninstrument(control);
    return pthread_once_real(control, init);
}

int pthread_rwlockattr_destroy(pthread_rwlockattr_t *a) {
    a = __sgxbounds_uninstrument(a);
    return pthread_rwlockattr_destroy_real(a);
}

int pthread_rwlockattr_init(pthread_rwlockattr_t *a) {
    a = __sgxbounds_uninstrument(a);
    return pthread_rwlockattr_init_real(a);
}

int pthread_rwlockattr_setpshared(pthread_rwlockattr_t *a, int pshared) {
    a = __sgxbounds_uninstrument(a);
    return pthread_rwlockattr_setpshared_real(a, pshared);
}

int pthread_rwlock_destroy(pthread_rwlock_t *rw) {
    rw = __sgxbounds_uninstrument(rw);
    return pthread_rwlock_destroy_real(rw);
}

int pthread_rwlock_init(pthread_rwlock_t *restrict rw, const pthread_rwlockattr_t *restrict a) {
    rw = __sgxbounds_uninstrument(rw);
    if (a)  a = __sgxbounds_uninstrument(a);
    return pthread_rwlock_init_real(rw, a);
}

int pthread_rwlock_rdlock(pthread_rwlock_t *rw) {
    rw = __sgxbounds_uninstrument(rw);
    return pthread_rwlock_rdlock_real(rw);
}

int pthread_rwlock_tryrdlock(pthread_rwlock_t *rw) {
    rw = __sgxbounds_uninstrument(rw);
    return pthread_rwlock_tryrdlock_real(rw);
}

int pthread_rwlock_trywrlock(pthread_rwlock_t *rw) {
    rw = __sgxbounds_uninstrument(rw);
    return pthread_rwlock_trywrlock_real(rw);
}

int pthread_rwlock_unlock(pthread_rwlock_t *rw) {
    rw = __sgxbounds_uninstrument(rw);
    return pthread_rwlock_unlock_real(rw);
}

int pthread_rwlock_wrlock(pthread_rwlock_t *rw) {
    rw = __sgxbounds_uninstrument(rw);
    return pthread_rwlock_wrlock_real(rw);
}

int pthread_sigmask(int how, const sigset_t *restrict set, sigset_t *restrict old) {
    set = __sgxbounds_uninstrument(set);
    if (old)  old = __sgxbounds_uninstrument(old);
    return pthread_sigmask_real(how, set, old);
}

int sem_destroy(sem_t *sem) {
    sem = __sgxbounds_uninstrument(sem);
    return sem_destroy_real(sem);
}

int sem_init(sem_t *sem, int pshared, unsigned value) {
    sem = __sgxbounds_uninstrument(sem);
    return sem_init_real(sem, pshared, value);
}

int sem_post(sem_t *sem) {
    sem = __sgxbounds_uninstrument(sem);
    return sem_post_real(sem);
}

int sem_trywait(sem_t *sem) {
    sem = __sgxbounds_uninstrument(sem);
    return sem_trywait_real(sem);
}

int sem_wait(sem_t *sem) {
    sem = __sgxbounds_uninstrument(sem);
    return sem_wait_real(sem);
}

/* ------------------------------------------------------------------------- */
/* ----------------------------- locale funcs  ----------------------------- */
/* ------------------------------------------------------------------------- */
// NOTE: locale_t & iconv_t are opaque and thus not instrumented
char *bind_textdomain_codeset_real(const char *domainname, const char *codeset);
char *catgets_real(nl_catd catd, int set_id, int msg_id, const char *s);
nl_catd catopen_real(const char *name, int oflag);
char *bindtextdomain_real(const char *domainname, const char *dirname);
char *dcngettext_real(const char *domainname, const char *msgid1, const char *msgid2, unsigned long int n, int category);
char *dcgettext_real(const char *domainname, const char *msgid, int category);
char *dngettext_real(const char *domainname, const char *msgid1, const char *msgid2, unsigned long int n);
char *dgettext_real(const char *domainname, const char *msgid);
char *gettext_real(const char *msgid);
char *ngettext_real(const char *msgid1, const char *msgid2, unsigned long int n);
iconv_t iconv_open_real(const char *to, const char *from);
size_t iconv_real(iconv_t cd0, char **restrict in, size_t *restrict inb, char **restrict out, size_t *restrict outb);
char *nl_langinfo_real(nl_item item);
char *nl_langinfo_l_real(nl_item item, locale_t loc);
struct lconv *localeconv_real(void);
locale_t newlocale_real(int mask, const char *name, locale_t loc);
char *setlocale_real(int cat, const char *name);
int strcoll_l_real(const char *l, const char *r, locale_t loc);
int strcoll_real(const char *l, const char *r);
ssize_t strfmon_l_real(char *restrict s, size_t n, locale_t loc, const char *restrict fmt, ...);
ssize_t strfmon_real(char *restrict s, size_t n, const char *restrict fmt, ...);
size_t strxfrm_l_real(char *restrict dest, const char *restrict src, size_t n, locale_t loc);
size_t strxfrm_real(char *restrict dest, const char *restrict src, size_t n);
char *textdomain_real(const char *domainname);


char *bind_textdomain_codeset(const char *domainname, const char *codeset) {
    static struct charbuf sbuf;
    if (sbuf.lbnd == 0)  sbuf.lbnd = (PTRTYPE)&sbuf;
    if (domainname)  domainname = __sgxbounds_uninstrument(domainname);
    if (codeset)  codeset = __sgxbounds_uninstrument(codeset);
    char* ret = bind_textdomain_codeset_real(domainname, codeset);
    if (ret) {
        strcpy_real(sbuf.buf, ret);
        ret = __sgxbounds_combine_ptr(&sbuf, (PTRTYPE)&sbuf.lbnd);
    }
    return ret;
}

char *catgets(nl_catd catd, int set_id, int msg_id, const char *s) {
    static struct charbuf sbuf;
    if (sbuf.lbnd == 0)  sbuf.lbnd = (PTRTYPE)&sbuf;
    char* sval = __sgxbounds_uninstrument(s);
    char* ret = catgets_real(catd, set_id, msg_id, sval);
    if (ret == sval) {
        // on failure, returns s
        return (char*)s;
    }
    strcpy_real(sbuf.buf, ret);
    return __sgxbounds_combine_ptr(&sbuf, (PTRTYPE)&sbuf.lbnd);
}

nl_catd catopen(const char *name, int oflag) {
    name = __sgxbounds_uninstrument(name);
    return catopen_real(name, oflag);
}

char *bindtextdomain(const char *domainname, const char *dirname) {
    static struct charbuf sbuf;
    if (sbuf.lbnd == 0)  sbuf.lbnd = (PTRTYPE)&sbuf;
    if (domainname)  domainname = __sgxbounds_uninstrument(domainname);
    if (dirname)  dirname = __sgxbounds_uninstrument(dirname);
    char* ret = bindtextdomain_real(domainname, dirname);
    if (ret) {
        strcpy_real(sbuf.buf, ret);
        ret = __sgxbounds_combine_ptr(&sbuf, (PTRTYPE)&sbuf.lbnd);
    }
    return ret;
}

char *dcngettext(const char *domainname, const char *msgid1, const char *msgid2, unsigned long int n, int category) {
    static struct charbuf sbuf;
    if (sbuf.lbnd == 0)  sbuf.lbnd = (PTRTYPE)&sbuf;
    char *msgid1val = NULL, *msgid2val = NULL;
    if (domainname)  domainname = __sgxbounds_uninstrument(domainname);
    if (msgid1)  msgid1val = __sgxbounds_uninstrument(msgid1);
    if (msgid2)  msgid2val = __sgxbounds_uninstrument(msgid2);
    char* ret = dcngettext_real(domainname, msgid1val, msgid2val, n, category);
    if (ret == msgid1val)  return (char*) msgid1;
    if (ret == msgid2val)  return (char*) msgid2;
    strcpy_real(sbuf.buf, ret);
    return __sgxbounds_combine_ptr(&sbuf, (PTRTYPE)&sbuf.lbnd);

}

// NOTE: for next 5 funcs, it is easier to call wrappers
char *dcgettext(const char *domainname, const char *msgid, int category) {
    return dcngettext(domainname, msgid, 0, 1, category);
}

char *dngettext(const char *domainname, const char *msgid1, const char *msgid2, unsigned long int n) {
    return dcngettext(domainname, msgid1, msgid2, n, LC_MESSAGES);
}

char *dgettext(const char *domainname, const char *msgid) {
    return dcngettext(domainname, msgid, 0, 1, LC_MESSAGES);
}

char *gettext(const char *msgid) {
    return dgettext(0, msgid);
}

char *ngettext(const char *msgid1, const char *msgid2, unsigned long int n) {
    return dngettext(0, msgid1, msgid2, n);
}


iconv_t iconv_open(const char *to, const char *from) {
    to   = __sgxbounds_uninstrument(to);
    from = __sgxbounds_uninstrument(from);
    return iconv_open_real(to, from);
}

size_t iconv(iconv_t cd0, char **restrict in, size_t *restrict inb, char **restrict out, size_t *restrict outb) {
    char *inoldval = NULL, *outoldval = NULL;
    if (in) {
        in  = __sgxbounds_uninstrument(in);
        if (*in) {
            inoldval = *in;
            *in = __sgxbounds_uninstrument(*in);
        }
    }
    if (out) {
        out  = __sgxbounds_uninstrument(out);
        if (*out) {
            outoldval = *out;
            *out = __sgxbounds_uninstrument(*out);
        }
    }
    if (inb)   inb   = __sgxbounds_uninstrument(inb);
    if (outb)  outb  = __sgxbounds_uninstrument(outb);
    size_t ret = iconv_real(cd0, in, inb, out, outb);
    if (in && *in) {
        // *in points into inoldval, so it has the same bounds
        PTRTYPE ubnd = __sgxbounds_extract_ubnd(inoldval);
        *in = __sgxbounds_combine_ptr(*in, ubnd);
    }
    if (out && *out) {
        // *out points into outoldval, so it has the same bounds
        PTRTYPE ubnd = __sgxbounds_extract_ubnd(outoldval);
        *out = __sgxbounds_combine_ptr(*out, ubnd);
    }
    return ret;
}

char *nl_langinfo_l(nl_item item, locale_t loc) {
    static struct charbuf sbuf;
    if (sbuf.lbnd == 0)  sbuf.lbnd = (PTRTYPE)&sbuf;
    char* ret = nl_langinfo_l_real(item, loc);
    if (ret) {
        strcpy_real(sbuf.buf, ret);
        ret = __sgxbounds_combine_ptr(&sbuf, (PTRTYPE)&sbuf.lbnd);
    }
    return ret;
}

char *nl_langinfo(nl_item item) {
    static struct charbuf sbuf;
    if (sbuf.lbnd == 0)  sbuf.lbnd = (PTRTYPE)&sbuf;
    char* ret = nl_langinfo_real(item);
    if (ret) {
        strcpy_real(sbuf.buf, ret);
        ret = __sgxbounds_combine_ptr(&sbuf, (PTRTYPE)&sbuf.lbnd);
    }
    return ret;
}

struct lconvbuf {
    struct lconv buf;
    PTRTYPE lbnd;
};

struct lconvcharsbuf {
    char decimal_point[5];
    char thousands_sep[5];
    char grouping[5];
    char int_curr_symbol[5];
    char currency_symbol[5];
    char mon_decimal_point[5];
    char mon_thousands_sep[5];
    char mon_grouping[5];
    char positive_sign[5];
    char negative_sign[5];
    PTRTYPE lbnd;
};

struct lconv *localeconv(void) {
    static struct lconvbuf buf;
    static struct lconvcharsbuf charsbuf;
    if (buf.lbnd == 0)  buf.lbnd = (PTRTYPE)&buf;
    if (charsbuf.lbnd == 0)  charsbuf.lbnd = (PTRTYPE)&charsbuf;
    struct lconv *ret = localeconv_real();
    memcpy_real(&buf.buf, ret, sizeof(struct lconv));

    strncpy_real(charsbuf.decimal_point, buf.buf.decimal_point, 5);
    buf.buf.decimal_point = __sgxbounds_combine_ptr(&charsbuf.decimal_point, (PTRTYPE)&charsbuf.lbnd);
    strncpy_real(charsbuf.thousands_sep, buf.buf.thousands_sep, 5);
    buf.buf.thousands_sep = __sgxbounds_combine_ptr(&charsbuf.thousands_sep, (PTRTYPE)&charsbuf.lbnd);
    strncpy_real(charsbuf.grouping, buf.buf.grouping, 5);
    buf.buf.grouping = __sgxbounds_combine_ptr(&charsbuf.grouping, (PTRTYPE)&charsbuf.lbnd);
    strncpy_real(charsbuf.int_curr_symbol, buf.buf.int_curr_symbol, 5);
    buf.buf.int_curr_symbol = __sgxbounds_combine_ptr(&charsbuf.int_curr_symbol, (PTRTYPE)&charsbuf.lbnd);
    strncpy_real(charsbuf.currency_symbol, buf.buf.currency_symbol, 5);
    buf.buf.currency_symbol = __sgxbounds_combine_ptr(&charsbuf.currency_symbol, (PTRTYPE)&charsbuf.lbnd);
    strncpy_real(charsbuf.mon_decimal_point, buf.buf.mon_decimal_point, 5);
    buf.buf.mon_decimal_point = __sgxbounds_combine_ptr(&charsbuf.mon_decimal_point, (PTRTYPE)&charsbuf.lbnd);
    strncpy_real(charsbuf.mon_thousands_sep, buf.buf.mon_thousands_sep, 5);
    buf.buf.mon_thousands_sep = __sgxbounds_combine_ptr(&charsbuf.mon_thousands_sep, (PTRTYPE)&charsbuf.lbnd);
    strncpy_real(charsbuf.mon_grouping, buf.buf.mon_grouping, 5);
    buf.buf.mon_grouping = __sgxbounds_combine_ptr(&charsbuf.mon_grouping, (PTRTYPE)&charsbuf.lbnd);
    strncpy_real(charsbuf.positive_sign, buf.buf.positive_sign, 5);
    buf.buf.positive_sign = __sgxbounds_combine_ptr(&charsbuf.positive_sign, (PTRTYPE)&charsbuf.lbnd);
    strncpy_real(charsbuf.negative_sign, buf.buf.negative_sign, 5);
    buf.buf.negative_sign = __sgxbounds_combine_ptr(&charsbuf.negative_sign, (PTRTYPE)&charsbuf.lbnd);

    return __sgxbounds_combine_ptr(&buf, (PTRTYPE)&buf.lbnd);
}

locale_t newlocale(int mask, const char *name, locale_t loc) {
    if (name)  name = __sgxbounds_uninstrument(name);
    return newlocale_real(mask, name, loc);
}

char *setlocale(int cat, const char *name) {
    // NOTE: setlocale returns an opaque string, no need to instrument it
    if (name)  name = __sgxbounds_uninstrument(name);
    return setlocale_real(cat, name);
}

int strcoll_l(const char *l, const char *r, locale_t loc) {
    l = __sgxbounds_uninstrument(l);
    r = __sgxbounds_uninstrument(r);
    return strcoll_l_real(l, r, loc);
}

int strcoll(const char *l, const char *r) {
    l = __sgxbounds_uninstrument(l);
    r = __sgxbounds_uninstrument(r);
    return strcoll_real(l, r);
}

ssize_t strfmon_l(char *restrict s, size_t n, locale_t loc, const char *restrict fmt, ...) {
    // NOTE: too specific to implement
    return -1;
}

ssize_t strfmon(char *restrict s, size_t n, const char *restrict fmt, ...) {
    // NOTE: too specific to implement
    return -1;
}

size_t strxfrm_l(char *restrict dest, const char *restrict src, size_t n, locale_t loc) {
    dest = __sgxbounds_uninstrument(dest);
    src  = __sgxbounds_uninstrument(src);
    return strxfrm_l_real(dest, src, n, loc);
}

size_t strxfrm(char *restrict dest, const char *restrict src, size_t n) {
    dest = __sgxbounds_uninstrument(dest);
    src  = __sgxbounds_uninstrument(src);
    return strxfrm_real(dest, src, n);
}

char *textdomain(const char *domainname) {
    static struct charbuf sbuf;
    if (sbuf.lbnd == 0)  sbuf.lbnd = (PTRTYPE)&sbuf;
    if (domainname)  domainname = __sgxbounds_uninstrument(domainname);
    char* ret = textdomain_real(domainname);
    if (ret) {
        strcpy_real(sbuf.buf, ret);
        ret = __sgxbounds_combine_ptr(&sbuf, (PTRTYPE)&sbuf.lbnd);
    }
    return ret;
}

/* ------------------------------------------------------------------------- */
/* ------------------------------ wide chars ------------------------------- */
/* ------------------------------------------------------------------------- */
// NOTE: minimal set of wchar-related funcs to make C++ init/fini happy
size_t wcrtomb_real(char *restrict s, wchar_t wc, mbstate_t *restrict st);

size_t wcrtomb(char *restrict s, wchar_t wc, mbstate_t *restrict st) {
    if (s)  s  = __sgxbounds_uninstrument(s);
    if (st) st = __sgxbounds_uninstrument(st);
    return wcrtomb_real(s, wc, st);
}


/* ------------------------------------------------------------------------- */
/* --------------------------------- errno --------------------------------- */
/* ------------------------------------------------------------------------- */
int *__errno_location_real(void);

int *__errno_location(void) {
    PTRTYPE ubnd = __sgxbounds_highest_bound();
    int* ret = __errno_location_real();
    ret = __sgxbounds_combine_ptr(ret, ubnd);
    return ret;
}

/* ------------------------------------------------------------------------- */
/* -------------------------------- network -------------------------------- */
/* ------------------------------------------------------------------------- */
// NOTE:  ignore all DNS funcs: res_ninit, res_nquery, res_nsearch, res_nquerydomain,
//         res_nmkquery, res_nsend, res_init, res_query, res_search, res_querydomain,
//         res_mkquery, res_send, dn_comp, dn_expand
// NOTE2: ignore all ether funcs: ether_aton, ether_ntoa, ether_ntohost,
//          ether_hostton, ether_line, ether_ntoa_r, ether_aton_r
// NOTE3: ignore all resolver funcs (from ns_parse.c)
int accept_real(int fd, struct sockaddr *restrict addr, socklen_t *restrict len);
int accept4_real(int fd, struct sockaddr *restrict addr, socklen_t *restrict len, int flg);
int bind_real(int fd, const struct sockaddr *addr, socklen_t len);
int connect_real(int fd, const struct sockaddr *addr, socklen_t len);
struct hostent *gethostent_real(void);
int getaddrinfo_real(const char *restrict host, const char *restrict serv, const struct addrinfo *restrict hint, struct addrinfo **restrict res);
void freeaddrinfo_real(struct addrinfo *p);
const char *gai_strerror_real(int ecode);
struct hostent *gethostbyaddr_real(const void *a, socklen_t l, int af);
int gethostbyaddr_r_real(const void *a, socklen_t l, int af, struct hostent *h, char *buf, size_t buflen, struct hostent **res, int *err);
struct hostent *gethostbyname_real(const char *name);
struct hostent *gethostbyname2_real(const char *name, int af);
int gethostbyname2_r_real(const char *name, int af, struct hostent *h, char *buf, size_t buflen, struct hostent **res, int *err);
int gethostbyname_r_real(const char *name, struct hostent *h, char *buf, size_t buflen, struct hostent **res, int *err);
void freeifaddrs_real(struct ifaddrs *ifp);
int getifaddrs_real(struct ifaddrs **ifap);
int getnameinfo_real(const struct sockaddr *restrict sa, socklen_t sl, char *restrict node, socklen_t nodelen, char *restrict serv, socklen_t servlen, int flags);
int getpeername_real(int fd, struct sockaddr *restrict addr, socklen_t *restrict len);
struct servent *getservbyname_real(const char *name, const char *prots);
int getservbyname_r_real(const char *name, const char *prots, struct servent *se, char *buf, size_t buflen, struct servent **res);
struct servent *getservbyport_real(int port, const char *prots);
int getservbyport_r_real(int port, const char *prots, struct servent *se, char *buf, size_t buflen, struct servent **res);
int getsockname_real(int fd, struct sockaddr *restrict addr, socklen_t *restrict len);
int getsockopt_real(int fd, int level, int optname, void *restrict optval, socklen_t *restrict optlen);
int *__h_errno_location_real(void);
void herror_real(const char *msg);
const char *hstrerror_real(int ecode);
void if_freenameindex_real(struct if_nameindex *idx);
struct if_nameindex *if_nameindex_real();
char *if_indextoname_real(unsigned index, char *name);
unsigned if_nametoindex_real(const char *name);
in_addr_t inet_addr_real(const char *p);
int inet_aton_real(const char *s0, struct in_addr *dest);
in_addr_t inet_network_real(const char *p);
char *inet_ntoa_real(struct in_addr in);
const char *inet_ntop_real(int af, const void *restrict a0, char *restrict s, socklen_t l);
int inet_pton_real(int af, const char *restrict s, void *restrict a0);
struct netent *getnetbyaddr_real(uint32_t net, int type);
struct netent *getnetbyname_real(const char *name);
struct protoent *getprotoent_real(void);
struct protoent *getprotobyname_real(const char *name);
struct protoent *getprotobynumber_real(int num);
ssize_t recv_real(int fd, void *buf, size_t len, int flags);
ssize_t recvfrom_real(int fd, void *restrict buf, size_t len, int flags, struct sockaddr *restrict addr, socklen_t *restrict alen);
ssize_t recvmsg_real(int fd, struct msghdr *msg, int flags);
ssize_t send_real(int fd, const void *buf, size_t len, int flags);
ssize_t sendmsg_real(int fd, const struct msghdr *msg, int flags);
ssize_t sendto_real(int fd, const void *buf, size_t len, int flags, const struct sockaddr *addr, socklen_t alen);
struct servent *getservent_real(void);
int setsockopt_real(int fd, int level, int optname, const void *optval, socklen_t optlen);
int socketpair_real(int domain, int type, int protocol, int fd[2]);

int accept(int fd, struct sockaddr *restrict addr, socklen_t *restrict len) {
    if (addr)  addr = __sgxbounds_uninstrument(addr);
    if (len)   len  = __sgxbounds_uninstrument(len);
    return accept_real(fd, addr, len);
}

int accept4(int fd, struct sockaddr *restrict addr, socklen_t *restrict len, int flg) {
    if (addr)  addr = __sgxbounds_uninstrument(addr);
    if (len)   len  = __sgxbounds_uninstrument(len);
    return accept4_real(fd, addr, len, flg);
}

int bind(int fd, const struct sockaddr *addr, socklen_t len) {
    addr = __sgxbounds_uninstrument(addr);
    return bind_real(fd, addr, len);
}

int connect(int fd, const struct sockaddr *addr, socklen_t len) {
    addr = __sgxbounds_uninstrument(addr);
    return connect_real(fd, addr, len);
}

struct hostent *gethostent(void) {
    static struct charbuf buf = {.lbnd = 0};
    if (buf.lbnd == 0)  buf.lbnd = (PTRTYPE)&buf;
    void* ret = gethostent_real();
    if (!ret) return NULL;
    strcpy_real(buf.buf, ret);
    return __sgxbounds_combine_ptr(&buf, (PTRTYPE)&(buf.lbnd));
}

int getaddrinfo(const char *restrict host, const char *restrict serv, const struct addrinfo *restrict hint, struct addrinfo **restrict res) {
    // TODO: uses dummy (highest) bounds, no security here!
    PTRTYPE ubnd = __sgxbounds_highest_bound();

    if (host)  host = __sgxbounds_uninstrument(host);
    if (serv)  serv = __sgxbounds_uninstrument(serv);
    if (res)   res  = __sgxbounds_uninstrument(res);
    if (hint)  hint = __sgxbounds_uninstrument(hint);

    int ret = getaddrinfo_real(host, serv, hint, res);
    if (!ret) {
        struct addrinfo *rp;
        for (rp = *res; rp != NULL; ) {
            struct addrinfo *ainext = rp->ai_next;
            rp->ai_addr      = __sgxbounds_combine_ptr(rp->ai_addr, ubnd);
            rp->ai_canonname = __sgxbounds_combine_ptr(rp->ai_canonname, ubnd);
            if (rp->ai_next)
                rp->ai_next  = __sgxbounds_combine_ptr(rp->ai_next, ubnd);
            rp = ainext;
        }
    }
    *res = __sgxbounds_combine_ptr(*res, ubnd);
    return ret;
}

void freeaddrinfo(struct addrinfo *p) {
    if (p)  p = __sgxbounds_uninstrument(p);
    freeaddrinfo_real(p);
}

const char *gai_strerror(int ecode) {
    static __thread struct charbuf buf;
    if (buf.lbnd == 0)  buf.lbnd = (PTRTYPE)&buf;
    void* ret = (void*) gai_strerror_real(ecode);
    if (!ret) return NULL;
    strcpy_real(buf.buf, ret);
    return __sgxbounds_combine_ptr(&buf, (PTRTYPE)&(buf.lbnd));
}

struct hostent *gethostbyaddr(const void *a, socklen_t l, int af) {
    // TODO: uses dummy (highest) bounds, no security here!
    PTRTYPE ubnd = __sgxbounds_highest_bound();
    int i;
    a = __sgxbounds_uninstrument(a);
    struct hostent* ret = gethostbyaddr_real(a, l, af);
    if (ret) {
        ret->h_name = __sgxbounds_combine_ptr(ret->h_name, ubnd);
        for (i=0; ret->h_aliases[i] != NULL; i++)
            ret->h_aliases[i] = __sgxbounds_combine_ptr(ret->h_aliases[i], ubnd);
        ret->h_aliases = __sgxbounds_combine_ptr(ret->h_aliases, ubnd);
        for (i=0; ret->h_addr_list[i] != NULL; i++)
            ret->h_addr_list[i] = __sgxbounds_combine_ptr(ret->h_addr_list[i], ubnd);
        ret->h_addr_list = __sgxbounds_combine_ptr(ret->h_addr_list, ubnd);
        ret = __sgxbounds_combine_ptr(ret, ubnd);
    }
    return ret;
}

int gethostbyaddr_r(const void *a, socklen_t l, int af, struct hostent *h, char *buf, size_t buflen, struct hostent **res, int *err) {
    // TODO: uses dummy (highest) bounds, no security here!
    PTRTYPE ubnd = __sgxbounds_highest_bound();
    int i;
    a = __sgxbounds_uninstrument(a);
    h = __sgxbounds_uninstrument(h);
    buf = __sgxbounds_uninstrument(buf);
    res = __sgxbounds_uninstrument(res);
    if (err)  err = __sgxbounds_uninstrument(err);
    int ret = gethostbyaddr_r_real(a, l, af, h, buf, buflen, res, err);
    if (!ret) {
        h->h_name = __sgxbounds_combine_ptr(h->h_name, ubnd);
        for (i=0; h->h_aliases[i] != NULL; i++)
            h->h_aliases[i] = __sgxbounds_combine_ptr(h->h_aliases[i], ubnd);
        h->h_aliases = __sgxbounds_combine_ptr(h->h_aliases, ubnd);
        for (i=0; h->h_addr_list[i] != NULL; i++)
            h->h_addr_list[i] = __sgxbounds_combine_ptr(h->h_addr_list[i], ubnd);
        h->h_addr_list = __sgxbounds_combine_ptr(h->h_addr_list, ubnd);
        *res = __sgxbounds_combine_ptr(*res, ubnd);
    }
    return ret;
}

struct hostent *gethostbyname(const char *name) {
    // TODO: uses dummy (highest) bounds, no security here!
    PTRTYPE ubnd = __sgxbounds_highest_bound();
    int i;
    name = __sgxbounds_uninstrument(name);
    struct hostent* ret = gethostbyname_real(name);
    if (ret) {
        ret->h_name = __sgxbounds_combine_ptr(ret->h_name, ubnd);
        for (i=0; ret->h_aliases[i] != NULL; i++)
            ret->h_aliases[i] = __sgxbounds_combine_ptr(ret->h_aliases[i], ubnd);
        ret->h_aliases = __sgxbounds_combine_ptr(ret->h_aliases, ubnd);
        for (i=0; ret->h_addr_list[i] != NULL; i++)
            ret->h_addr_list[i] = __sgxbounds_combine_ptr(ret->h_addr_list[i], ubnd);
        ret->h_addr_list = __sgxbounds_combine_ptr(ret->h_addr_list, ubnd);
        ret = __sgxbounds_combine_ptr(ret, ubnd);
    }
    return ret;
}

struct hostent *gethostbyname2(const char *name, int af) {
    // TODO: uses dummy (highest) bounds, no security here!
    PTRTYPE ubnd = __sgxbounds_highest_bound();
    int i;
    name = __sgxbounds_uninstrument(name);
    struct hostent* ret = gethostbyname2_real(name, af);
    if (ret) {
        ret->h_name = __sgxbounds_combine_ptr(ret->h_name, ubnd);
        for (i=0; ret->h_aliases[i] != NULL; i++)
            ret->h_aliases[i] = __sgxbounds_combine_ptr(ret->h_aliases[i], ubnd);
        ret->h_aliases = __sgxbounds_combine_ptr(ret->h_aliases, ubnd);
        for (i=0; ret->h_addr_list[i] != NULL; i++)
            ret->h_addr_list[i] = __sgxbounds_combine_ptr(ret->h_addr_list[i], ubnd);
        ret->h_addr_list = __sgxbounds_combine_ptr(ret->h_addr_list, ubnd);
        ret = __sgxbounds_combine_ptr(ret, ubnd);
    }
    return ret;
}

int gethostbyname2_r(const char *name, int af, struct hostent *h, char *buf, size_t buflen, struct hostent **res, int *err) {
    // TODO: uses dummy (highest) bounds, no security here!
    PTRTYPE ubnd = __sgxbounds_highest_bound();
    int i;
    name = __sgxbounds_uninstrument(name);
    h    = __sgxbounds_uninstrument(h);
    buf  = __sgxbounds_uninstrument(buf);
    res  = __sgxbounds_uninstrument(res);
    if (err)  err = __sgxbounds_uninstrument(err);
    int ret = gethostbyname2_r_real(name, af, h, buf, buflen, res, err);
    if (!ret) {
        h->h_name = __sgxbounds_combine_ptr(h->h_name, ubnd);
        for (i=0; h->h_aliases[i] != NULL; i++)
            h->h_aliases[i] = __sgxbounds_combine_ptr(h->h_aliases[i], ubnd);
        h->h_aliases = __sgxbounds_combine_ptr(h->h_aliases, ubnd);
        for (i=0; h->h_addr_list[i] != NULL; i++)
            h->h_addr_list[i] = __sgxbounds_combine_ptr(h->h_addr_list[i], ubnd);
        h->h_addr_list = __sgxbounds_combine_ptr(h->h_addr_list, ubnd);
        *res = __sgxbounds_combine_ptr(*res, ubnd);
    }
    return ret;
}

int gethostbyname_r(const char *name, struct hostent *h, char *buf, size_t buflen, struct hostent **res, int *err) {
    return gethostbyname2_r(name, AF_INET, h, buf, buflen, res, err);
}

void freeifaddrs(struct ifaddrs *ifp) {
    // NOTE: we re-implement functionality of real freeifaddrs
    struct ifaddrs *n;
    while (ifp) {
        ifp = __sgxbounds_uninstrument(ifp);
        n = ifp->ifa_next;
        free_real(ifp);
        ifp = n;
    }
}

int getifaddrs(struct ifaddrs **ifap) {
    // TODO: uses dummy (highest) bounds, no security here!
    PTRTYPE ubnd = __sgxbounds_highest_bound();

    ifap = __sgxbounds_uninstrument(ifap);
    int ret = getifaddrs_real(ifap);
    if (!ret) {
        struct ifaddrs *ifp;
        for (ifp = *ifap; ifp != NULL; ) {
            struct ifaddrs *ifanext = ifp->ifa_next;
            ifp->ifa_name      = __sgxbounds_combine_ptr(ifp->ifa_name, ubnd);
            ifp->ifa_addr      = __sgxbounds_combine_ptr(ifp->ifa_addr, ubnd);
            ifp->ifa_netmask   = __sgxbounds_combine_ptr(ifp->ifa_netmask, ubnd);
            ifp->ifa_broadaddr = __sgxbounds_combine_ptr(ifp->ifa_broadaddr, ubnd);
            ifp->ifa_data      = __sgxbounds_combine_ptr(ifp->ifa_data, ubnd);
            if (ifp->ifa_next)
                ifp->ifa_next  = __sgxbounds_combine_ptr(ifp->ifa_next, ubnd);
            ifp = ifanext;
        }
        *ifap = __sgxbounds_combine_ptr(*ifap, ubnd);
    }
    return ret;
}

int getnameinfo(const struct sockaddr *restrict sa, socklen_t sl, char *restrict node, socklen_t nodelen, char *restrict serv, socklen_t servlen, int flags) {
    if (sa)    sa   = __sgxbounds_uninstrument(sa);
    if (node)  node = __sgxbounds_uninstrument(node);
    if (serv)  serv = __sgxbounds_uninstrument(serv);
    return getnameinfo_real(sa, sl, node, nodelen, serv, servlen, flags);
}

int getpeername(int fd, struct sockaddr *restrict addr, socklen_t *restrict len) {
    addr = __sgxbounds_uninstrument(addr);
    len  = __sgxbounds_uninstrument(len);
    return getpeername_real(fd, addr, len);
}

struct servent *getservbyname(const char *name, const char *prots) {
    // TODO: uses dummy (highest) bounds, no security here!
    PTRTYPE ubnd = __sgxbounds_highest_bound();
    int i;
    if (name)  name = __sgxbounds_uninstrument(name);
    if (prots) prots = __sgxbounds_uninstrument(prots);
    struct servent* ret = getservbyname_real(name, prots);
    if (ret) {
        ret->s_name  = __sgxbounds_combine_ptr(ret->s_name, ubnd);
        ret->s_proto = __sgxbounds_combine_ptr(ret->s_proto, ubnd);
        for (i=0; ret->s_aliases[i] != NULL; i++)
            ret->s_aliases[i] = __sgxbounds_combine_ptr(ret->s_aliases[i], ubnd);
        ret->s_aliases = __sgxbounds_combine_ptr(ret->s_aliases, ubnd);
        ret = __sgxbounds_combine_ptr(ret, ubnd);
    }
    return ret;
}

int getservbyname_r(const char *name, const char *prots, struct servent *se, char *buf, size_t buflen, struct servent **res) {
    int i;
    PTRTYPE se_ubnd  = __sgxbounds_extract_ubnd(se);
    PTRTYPE buf_ubnd = __sgxbounds_extract_ubnd(buf);
    if (name)  name = __sgxbounds_uninstrument(name);
    if (prots) prots = __sgxbounds_uninstrument(prots);
    se  = __sgxbounds_uninstrument(se);
    buf = __sgxbounds_uninstrument(buf);
    res = __sgxbounds_uninstrument(res);
    int ret = getservbyname_r_real(name, prots, se, buf, buflen, res);
    if (!ret) {
        se->s_name  = __sgxbounds_combine_ptr(se->s_name, buf_ubnd);
        se->s_proto = __sgxbounds_combine_ptr(se->s_proto, buf_ubnd);
        for (i=0; se->s_aliases[i] != NULL; i++)
            se->s_aliases[i] = __sgxbounds_combine_ptr(se->s_aliases[i], buf_ubnd);
        se->s_aliases = __sgxbounds_combine_ptr(se->s_aliases, buf_ubnd);
        if (*res)  *res = __sgxbounds_combine_ptr(*res, se_ubnd);
    }
    return ret;
}

struct servent *getservbyport(int port, const char *prots) {
    // TODO: uses dummy (highest) bounds, no security here!
    PTRTYPE ubnd = __sgxbounds_highest_bound();
    int i;
    if (prots) prots = __sgxbounds_uninstrument(prots);
    struct servent* ret = getservbyport_real(port, prots);
    if (ret) {
        ret->s_name  = __sgxbounds_combine_ptr(ret->s_name, ubnd);
        ret->s_proto = __sgxbounds_combine_ptr(ret->s_proto, ubnd);
        for (i=0; ret->s_aliases[i] != NULL; i++)
            ret->s_aliases[i] = __sgxbounds_combine_ptr(ret->s_aliases[i], ubnd);
        ret->s_aliases = __sgxbounds_combine_ptr(ret->s_aliases, ubnd);
        ret = __sgxbounds_combine_ptr(ret, ubnd);
    }
    return ret;
}

int getservbyport_r(int port, const char *prots, struct servent *se, char *buf, size_t buflen, struct servent **res) {
    int i;
    PTRTYPE se_ubnd  = __sgxbounds_extract_ubnd(se);
    PTRTYPE buf_ubnd = __sgxbounds_extract_ubnd(buf);
    if (prots) prots = __sgxbounds_uninstrument(prots);
    se  = __sgxbounds_uninstrument(se);
    buf = __sgxbounds_uninstrument(buf);
    res = __sgxbounds_uninstrument(res);
    int ret = getservbyport_r_real(port, prots, se, buf, buflen, res);
    if (!ret) {
        se->s_name  = __sgxbounds_combine_ptr(se->s_name, buf_ubnd);
        se->s_proto = __sgxbounds_combine_ptr(se->s_proto, buf_ubnd);
        for (i=0; se->s_aliases[i] != NULL; i++)
            se->s_aliases[i] = __sgxbounds_combine_ptr(se->s_aliases[i], buf_ubnd);
        se->s_aliases = __sgxbounds_combine_ptr(se->s_aliases, buf_ubnd);
        if (*res)  *res = __sgxbounds_combine_ptr(*res, se_ubnd);
    }
    return ret;
}

int getsockname(int fd, struct sockaddr *restrict addr, socklen_t *restrict len) {
    addr = __sgxbounds_uninstrument(addr);
    len  = __sgxbounds_uninstrument(len);
    return getsockname_real(fd, addr, len);
}

int getsockopt(int fd, int level, int optname, void *restrict optval, socklen_t *restrict optlen) {
    if (optval)  optval = __sgxbounds_uninstrument(optval);
    if (optlen)  optlen = __sgxbounds_uninstrument(optlen);
    return getsockopt_real(fd, level, optname, optval, optlen);
}

int *__h_errno_location(void) {
    PTRTYPE ubnd = __sgxbounds_highest_bound();
    int* ret = __h_errno_location_real();
    ret = __sgxbounds_combine_ptr(ret, ubnd);
    return ret;
}

void herror(const char *msg) {
    msg  = __sgxbounds_uninstrument(msg);
    herror_real(msg);
}

const char *hstrerror(int ecode) {
    static __thread struct charbuf buf = {.lbnd = 0};
    if (buf.lbnd == 0)  buf.lbnd = (PTRTYPE)&buf;
    char* ret = (char*) hstrerror_real(ecode);
    if (!ret) return NULL;
    strcpy_real(buf.buf, ret);
    return __sgxbounds_combine_ptr(&buf, (PTRTYPE)&(buf.lbnd));
}

void if_freenameindex(struct if_nameindex *idx) {
    idx  = __sgxbounds_uninstrument(idx);
    if_freenameindex_real(idx);
}

struct if_nameindex *if_nameindex() {
    // TODO: uses dummy (highest) bounds, no security here!
    PTRTYPE ubnd = __sgxbounds_highest_bound();
    int i;
    struct if_nameindex *ret = if_nameindex_real();
    if (ret) {
        for (i=0; ret[i].if_name != NULL; i++)
            ret[i].if_name = __sgxbounds_combine_ptr(ret[i].if_name, ubnd);
        ret = __sgxbounds_combine_ptr(ret, ubnd);
    }
    return ret;
}

char *if_indextoname(unsigned index, char *name) {
    PTRTYPE name_ubnd  = __sgxbounds_extract_ubnd(name);
    name  = __sgxbounds_uninstrument(name);
    char* ret = if_indextoname_real(index, name);
    if (ret)  ret = __sgxbounds_combine_ptr(ret, name_ubnd);
    return ret;
}

unsigned if_nametoindex(const char *name) {
    name  = __sgxbounds_uninstrument(name);
    return if_nametoindex_real(name);
}

in_addr_t inet_addr(const char *p) {
    p  = __sgxbounds_uninstrument(p);
    return inet_addr_real(p);
}

int inet_aton(const char *s0, struct in_addr *dest) {
    s0   = __sgxbounds_uninstrument(s0);
    dest = __sgxbounds_uninstrument(dest);
    return inet_aton_real(s0, dest);
}

in_addr_t inet_network(const char *p) {
    p = __sgxbounds_uninstrument(p);
    return inet_network_real(p);
}

char *inet_ntoa(struct in_addr in) {
    static struct charbuf buf = {.lbnd = 0};
    if (buf.lbnd == 0)  buf.lbnd = (PTRTYPE)&buf;
    char* ret = inet_ntoa_real(in);
    if (!ret) return NULL;
    strcpy_real(buf.buf, ret);
    return __sgxbounds_combine_ptr(&buf, (PTRTYPE)&(buf.lbnd));
}

const char *inet_ntop(int af, const void *restrict a0, char *restrict s, socklen_t l) {
    PTRTYPE s_ubnd  = __sgxbounds_extract_ubnd(s);
    a0 = __sgxbounds_uninstrument(a0);
    s  = __sgxbounds_uninstrument(s);
    char* ret = (char*) inet_ntop_real(af, a0, s, l);
    if (ret) {
        ret = __sgxbounds_combine_ptr(ret, s_ubnd);
    }
    return ret;
}

int inet_pton(int af, const char *restrict s, void *restrict a0) {
    a0 = __sgxbounds_uninstrument(a0);
    s  = __sgxbounds_uninstrument(s);
    return inet_pton_real(af, s, a0);
}

struct netent *getnetbyaddr(uint32_t net, int type) {
    // TODO: uses dummy (highest) bounds, no security here!
    PTRTYPE ubnd = __sgxbounds_highest_bound();
    int i;
    struct netent* ret = getnetbyaddr_real(net, type);
    if (ret) {
        ret->n_name = __sgxbounds_combine_ptr(ret->n_name, ubnd);
        for (i=0; ret->n_aliases[i] != NULL; i++)
            ret->n_aliases[i] = __sgxbounds_combine_ptr(ret->n_aliases[i], ubnd);
        ret->n_aliases = __sgxbounds_combine_ptr(ret->n_aliases, ubnd);
        ret = __sgxbounds_combine_ptr(ret, ubnd);
    }
    return ret;
}

struct netent *getnetbyname(const char *name) {
    // TODO: uses dummy (highest) bounds, no security here!
    PTRTYPE ubnd = __sgxbounds_highest_bound();
    int i;
    name = __sgxbounds_uninstrument(name);
    struct netent* ret = getnetbyname_real(name);
    if (ret) {
        ret->n_name = __sgxbounds_combine_ptr(ret->n_name, ubnd);
        for (i=0; ret->n_aliases[i] != NULL; i++)
            ret->n_aliases[i] = __sgxbounds_combine_ptr(ret->n_aliases[i], ubnd);
        ret->n_aliases = __sgxbounds_combine_ptr(ret->n_aliases, ubnd);
        ret = __sgxbounds_combine_ptr(ret, ubnd);
    }
    return ret;
}

struct protoent *getprotoent(void) {
    // TODO: uses dummy (highest) bounds, no security here!
    PTRTYPE ubnd = __sgxbounds_highest_bound();
    int i;
    struct protoent* ret = getprotoent_real();
    if (ret) {
        ret->p_name = __sgxbounds_combine_ptr(ret->p_name, ubnd);
        for (i=0; ret->p_aliases[i] != NULL; i++)
            ret->p_aliases[i] = __sgxbounds_combine_ptr(ret->p_aliases[i], ubnd);
        ret->p_aliases = __sgxbounds_combine_ptr(ret->p_aliases, ubnd);
        ret = __sgxbounds_combine_ptr(ret, ubnd);
    }
    return ret;
}

struct protoent *getprotobyname(const char *name) {
    // TODO: uses dummy (highest) bounds, no security here!
    PTRTYPE ubnd = __sgxbounds_highest_bound();
    int i;
    name = __sgxbounds_uninstrument(name);
    struct protoent* ret = getprotobyname_real(name);
    if (ret) {
        ret->p_name = __sgxbounds_combine_ptr(ret->p_name, ubnd);
        for (i=0; ret->p_aliases[i] != NULL; i++)
            ret->p_aliases[i] = __sgxbounds_combine_ptr(ret->p_aliases[i], ubnd);
        ret->p_aliases = __sgxbounds_combine_ptr(ret->p_aliases, ubnd);
        ret = __sgxbounds_combine_ptr(ret, ubnd);
    }
    return ret;
}

struct protoent *getprotobynumber(int num) {
    // TODO: uses dummy (highest) bounds, no security here!
    PTRTYPE ubnd = __sgxbounds_highest_bound();
    int i;
    struct protoent* ret = getprotobynumber_real(num);
    if (ret) {
        ret->p_name = __sgxbounds_combine_ptr(ret->p_name, ubnd);
        for (i=0; ret->p_aliases[i] != NULL; i++)
            ret->p_aliases[i] = __sgxbounds_combine_ptr(ret->p_aliases[i], ubnd);
        ret->p_aliases = __sgxbounds_combine_ptr(ret->p_aliases, ubnd);
        ret = __sgxbounds_combine_ptr(ret, ubnd);
    }
    return ret;
}

ssize_t recv(int fd, void *buf, size_t len, int flags) {
    if (buf)  buf = __sgxbounds_uninstrument_check(buf, &len);
    if (!len) {errno = EINVAL; return -1;} // detected out-of-bounds, silently return
    return recv_real(fd, buf, len, flags);
}

ssize_t recvfrom(int fd, void *restrict buf, size_t len, int flags, struct sockaddr *restrict addr, socklen_t *restrict alen) {
    if (buf)  buf = __sgxbounds_uninstrument_check(buf, &len);
    if (!len) {errno = EINVAL; return -1;} // detected out-of-bounds, silently return
    if (addr)  addr = __sgxbounds_uninstrument(addr);
    if (alen)  alen = __sgxbounds_uninstrument(alen);
    return recvfrom_real(fd, buf, len, flags, addr, alen);
}

ssize_t recvmsg(int fd, struct msghdr *msg, int flags) {
    int i;
    struct msghdr msgval = {.msg_name = NULL, .msg_namelen = 0, .msg_iov = NULL, .msg_iovlen = 0, .msg_control = NULL, .msg_controllen = 0, .msg_flags = 0};
    msg = __sgxbounds_uninstrument(msg);

    if (msg->msg_name)    msgval.msg_name    = __sgxbounds_uninstrument(msg->msg_name);
    if (msg->msg_control) msgval.msg_control = __sgxbounds_uninstrument(msg->msg_control);
    msgval.msg_namelen = msg->msg_namelen;
    msgval.msg_iovlen  = msg->msg_iovlen;
    msgval.msg_controllen  = msg->msg_controllen;
    msgval.msg_flags   = msg->msg_flags;

    struct iovec* iovval = malloc_real(msg->msg_iovlen * sizeof(struct iovec));
    for (i = 0; i < msg->msg_iovlen; i++) {
        struct iovec *msgiov = __sgxbounds_uninstrument(msg->msg_iov);
        iovval[i].iov_base = __sgxbounds_uninstrument(msgiov[i].iov_base);
        iovval[i].iov_len  = msgiov[i].iov_len;
    }
    msgval.msg_iov = iovval;

    ssize_t ret = recvmsg_real(fd, &msgval, flags);
    free_real(iovval);
    return ret;
}

ssize_t send(int fd, const void *buf, size_t len, int flags) {
    if (buf)  buf = __sgxbounds_uninstrument_check(buf, &len);
    if (!len) {errno = EINVAL; return -1;} // detected out-of-bounds, silently return
    return send_real(fd, buf, len, flags);
}

ssize_t sendmsg(int fd, const struct msghdr *msg, int flags) {
    int i;
    struct msghdr msgval = {.msg_name = NULL, .msg_namelen = 0, .msg_iov = NULL, .msg_iovlen = 0, .msg_control = NULL, .msg_controllen = 0, .msg_flags = 0};
    msg = __sgxbounds_uninstrument(msg);

    if (msg->msg_name)    msgval.msg_name    = __sgxbounds_uninstrument(msg->msg_name);
    if (msg->msg_control) msgval.msg_control = __sgxbounds_uninstrument(msg->msg_control);
    msgval.msg_namelen = msg->msg_namelen;
    msgval.msg_iovlen  = msg->msg_iovlen;
    msgval.msg_controllen  = msg->msg_controllen;
    msgval.msg_flags   = msg->msg_flags;

    struct iovec* iovval = malloc_real(msg->msg_iovlen * sizeof(struct iovec));
    for (i = 0; i < msg->msg_iovlen; i++) {
        struct iovec *msgiov = __sgxbounds_uninstrument(msg->msg_iov);
        iovval[i].iov_base = __sgxbounds_uninstrument(msgiov[i].iov_base);
        iovval[i].iov_len  = msgiov[i].iov_len;
    }
    msgval.msg_iov = iovval;

    ssize_t ret = sendmsg_real(fd, &msgval, flags);
    free_real(iovval);
    return ret;
}

ssize_t sendto(int fd, const void *buf, size_t len, int flags, const struct sockaddr *addr, socklen_t alen) {
    if (buf)  buf = __sgxbounds_uninstrument_check(buf, &len);
    if (!len) {errno = EINVAL; return -1;} // detected out-of-bounds, silently return
    if (addr)  addr = __sgxbounds_uninstrument(addr);
    return sendto_real(fd, buf, len, flags, addr, alen);
}

struct servent *getservent(void) {
    // TODO: uses dummy (highest) bounds, no security here!
    PTRTYPE ubnd = __sgxbounds_highest_bound();
    int i;
    struct servent* ret = getservent_real();
    if (ret) {
        ret->s_name  = __sgxbounds_combine_ptr(ret->s_name, ubnd);
        ret->s_proto = __sgxbounds_combine_ptr(ret->s_proto, ubnd);
        for (i=0; ret->s_aliases[i] != NULL; i++)
            ret->s_aliases[i] = __sgxbounds_combine_ptr(ret->s_aliases[i], ubnd);
        ret->s_aliases = __sgxbounds_combine_ptr(ret->s_aliases, ubnd);
        ret = __sgxbounds_combine_ptr(ret, ubnd);
    }
    return ret;
}

int setsockopt(int fd, int level, int optname, const void *optval, socklen_t optlen) {
    if (optval)  optval = __sgxbounds_uninstrument(optval);
    return setsockopt_real(fd, level, optname, optval, optlen);
}

int socketpair(int domain, int type, int protocol, int fd[2]) {
    int* fdval = (int*)__sgxbounds_uninstrument((void*) fd);
    return socketpair_real(domain, type, protocol, fdval);
}

/* ------------------------------------------------------------------------- */
/* -------------------------------- linux ---------------------------------- */
/* ------------------------------------------------------------------------- */
int epoll_ctl_real(int fd, int op, int fd2, struct epoll_event *ev);
int epoll_wait_real(int fd, struct epoll_event *ev, int cnt, int to);
int epoll_pwait_real(int fd, struct epoll_event *ev, int cnt, int to, const sigset_t *sigs);
ssize_t sendfile_real(int out_fd, int in_fd, off_t *ofs, size_t count);

int epoll_ctl(int fd, int op, int fd2, struct epoll_event *ev) {
    // NOTE: hope that noone uses ev->data.ptr (otherwise need to uninstrument union)
    if (ev)  ev = __sgxbounds_uninstrument(ev);
    return epoll_ctl_real(fd, op, fd2, ev);
}

int epoll_wait(int fd, struct epoll_event *ev, int cnt, int to) {
    // NOTE: hope that noone uses ev->data.ptr (otherwise need to uninstrument union)
    if (ev)  ev = __sgxbounds_uninstrument(ev);
    return epoll_wait_real(fd, ev, cnt, to);
}

int epoll_pwait(int fd, struct epoll_event *ev, int cnt, int to, const sigset_t *sigs) {
    // NOTE: hope that noone uses ev->data.ptr (otherwise need to uninstrument union)
    if (ev)    ev = __sgxbounds_uninstrument(ev);
    if (sigs)  sigs = __sgxbounds_uninstrument(sigs);
    return epoll_pwait_real(fd, ev, cnt, to, sigs);
}

ssize_t sendfile(int out_fd, int in_fd, off_t *ofs, size_t count) {
    if (ofs)  ofs = __sgxbounds_uninstrument(ofs);
    return sendfile_real(out_fd, in_fd, ofs, count);
}


/* ------------------------------------------------------------------------- */
/* --------------------------------- temp ---------------------------------- */
/* ------------------------------------------------------------------------- */
char *mkdtemp_real(char *template);
int mkostemp_real(char *template, int flags);
int mkostemp64_real(char *template, int flags);
int mkostemps_real(char *template, int len, int flags);
int mkostemps64_real(char *template, int len, int flags);
int mkstemp_real(char *template);
int mkstemp64_real(char *template);
int mkstemps_real(char *template, int len);
int mkstemps64_real(char *template, int len);
char *mktemp_real(char *template);

char *mkdtemp(char *template) {
    PTRTYPE ubnd  = __sgxbounds_extract_ubnd(template);
    template = __sgxbounds_uninstrument(template);
    char* ret = mkdtemp_real(template);
    return __sgxbounds_combine_ptr(ret, ubnd);
}

int mkostemp(char *template, int flags) {
    template = __sgxbounds_uninstrument(template);
    return mkostemp_real(template, flags);
}

int mkostemp64(char *template, int flags) {
    return mkostemp(template, flags);
}

int mkostemps(char *template, int len, int flags) {
    template = __sgxbounds_uninstrument(template);
    return mkostemps_real(template, len, flags);
}

int mkostemps64(char *template, int len, int flags) {
    return mkostemps(template, len, flags);
}

int mkstemp(char *template) {
    template = __sgxbounds_uninstrument(template);
    return mkstemp_real(template);
}

int mkstemp64(char *template) {
    return mkstemp(template);
}

int mkstemps(char *template, int len) {
    template = __sgxbounds_uninstrument(template);
    return mkstemps_real(template, len);
}

int mkstemps64(char *template, int len) {
    return mkstemps(template, len);
}

char *mktemp(char *template) {
    PTRTYPE ubnd  = __sgxbounds_extract_ubnd(template);
    template = __sgxbounds_uninstrument(template);
    char* ret = mktemp_real(template);
    return __sgxbounds_combine_ptr(ret, ubnd);
}

/* ------------------------------------------------------------------------- */
/* ------------------------------- passwd ---------------------------------- */
/* ------------------------------------------------------------------------- */
struct group *fgetgrent_real(FILE *f);
struct passwd *fgetpwent_real(FILE *f);
struct spwd *fgetspent_real(FILE *f);
struct group *getgrent_real();
struct group *getgrgid_real(gid_t gid);
struct group *getgrnam_real(const char *name);
int getgrouplist_real(const char *user, gid_t gid, gid_t *groups, int *ngroups);
int getgrnam_r_real(const char *name, struct group *gr, char *buf, size_t size, struct group **res);
int getgrgid_r_real(gid_t gid, struct group *gr, char *buf, size_t size, struct group **res);
struct passwd *getpwent_real();
struct passwd *getpwuid_real(uid_t uid);
struct passwd *getpwnam_real(const char *name);
int getpwnam_r_real(const char *name, struct passwd *pw, char *buf, size_t size, struct passwd **res);
int getpwuid_r_real(uid_t uid, struct passwd *pw, char *buf, size_t size, struct passwd **res);
struct spwd *getspnam_real(const char *name);
int getspnam_r_real(const char *name, struct spwd *sp, char *buf, size_t size, struct spwd **res);
int putgrent_real(const struct group *gr, FILE *f);
int putpwent_real(const struct passwd *pw, FILE *f);
int putspent_real(const struct spwd *sp, FILE *f);

struct group *fgetgrent(FILE *f) {
    // TODO: uses dummy (highest) bounds, no security here!
    PTRTYPE ubnd = __sgxbounds_highest_bound();
    int i;

    struct group* ret = fgetgrent_real(f);
    if (ret) {
        ret->gr_name   = __sgxbounds_combine_ptr(ret->gr_name, ubnd);
        ret->gr_passwd = __sgxbounds_combine_ptr(ret->gr_passwd, ubnd);
        for (i=0; ret->gr_mem[i] != NULL; i++)
            ret->gr_mem[i] = __sgxbounds_combine_ptr(ret->gr_mem[i], ubnd);
        ret->gr_mem = __sgxbounds_combine_ptr(ret->gr_mem, ubnd);
        ret = __sgxbounds_combine_ptr(ret, ubnd);
    }
    return ret;
}

struct passwd *fgetpwent(FILE *f) {
    // TODO: uses dummy (highest) bounds, no security here!
    PTRTYPE ubnd = __sgxbounds_highest_bound();
    struct passwd* ret = fgetpwent_real(f);
    if (ret) {
        ret->pw_name   = __sgxbounds_combine_ptr(ret->pw_name, ubnd);
        ret->pw_passwd = __sgxbounds_combine_ptr(ret->pw_passwd, ubnd);
        ret->pw_gecos  = __sgxbounds_combine_ptr(ret->pw_gecos, ubnd);
        ret->pw_dir    = __sgxbounds_combine_ptr(ret->pw_dir, ubnd);
        ret->pw_shell  = __sgxbounds_combine_ptr(ret->pw_shell, ubnd);
        ret = __sgxbounds_combine_ptr(ret, ubnd);
    }
    return ret;
}

struct spwd *fgetspent(FILE *f) {
    // TODO: uses dummy (highest) bounds, no security here!
    PTRTYPE ubnd = __sgxbounds_highest_bound();
    struct spwd* ret = fgetspent_real(f);
    if (ret) {
        ret->sp_namp = __sgxbounds_combine_ptr(ret->sp_namp, ubnd);
        ret->sp_pwdp = __sgxbounds_combine_ptr(ret->sp_pwdp, ubnd);
        ret = __sgxbounds_combine_ptr(ret, ubnd);
    }
    return ret;
}

struct group *getgrent() {
    // TODO: uses dummy (highest) bounds, no security here!
    PTRTYPE ubnd = __sgxbounds_highest_bound();
    int i;

    struct group* ret = getgrent_real();
    if (ret) {
        ret->gr_name   = __sgxbounds_combine_ptr(ret->gr_name, ubnd);
        ret->gr_passwd = __sgxbounds_combine_ptr(ret->gr_passwd, ubnd);
        for (i=0; ret->gr_mem[i] != NULL; i++)
            ret->gr_mem[i] = __sgxbounds_combine_ptr(ret->gr_mem[i], ubnd);
        ret->gr_mem = __sgxbounds_combine_ptr(ret->gr_mem, ubnd);
        ret = __sgxbounds_combine_ptr(ret, ubnd);
    }
    return ret;
}

struct group *getgrgid(gid_t gid) {
    // TODO: uses dummy (highest) bounds, no security here!
    PTRTYPE ubnd = __sgxbounds_highest_bound();
    int i;

    struct group* ret = getgrgid_real(gid);
    if (ret) {
        ret->gr_name   = __sgxbounds_combine_ptr(ret->gr_name, ubnd);
        ret->gr_passwd = __sgxbounds_combine_ptr(ret->gr_passwd, ubnd);
        for (i=0; ret->gr_mem[i] != NULL; i++)
            ret->gr_mem[i] = __sgxbounds_combine_ptr(ret->gr_mem[i], ubnd);
        ret->gr_mem = __sgxbounds_combine_ptr(ret->gr_mem, ubnd);
        ret = __sgxbounds_combine_ptr(ret, ubnd);
    }
    return ret;
}


struct group *getgrnam(const char *name) {
    // TODO: uses dummy (highest) bounds, no security here!
    PTRTYPE ubnd = __sgxbounds_highest_bound();
    int i;

    name = __sgxbounds_uninstrument(name);
    struct group* ret = getgrnam_real(name);
    if (ret) {
        ret->gr_name   = __sgxbounds_combine_ptr(ret->gr_name, ubnd);
        ret->gr_passwd = __sgxbounds_combine_ptr(ret->gr_passwd, ubnd);
        for (i=0; ret->gr_mem[i] != NULL; i++)
            ret->gr_mem[i] = __sgxbounds_combine_ptr(ret->gr_mem[i], ubnd);
        ret->gr_mem = __sgxbounds_combine_ptr(ret->gr_mem, ubnd);
        ret = __sgxbounds_combine_ptr(ret, ubnd);
    }
    return ret;
}

int getgrouplist(const char *user, gid_t gid, gid_t *groups, int *ngroups) {
    user = __sgxbounds_uninstrument(user);
    groups = __sgxbounds_uninstrument(groups);
    ngroups = __sgxbounds_uninstrument(ngroups);
    return getgrouplist_real(user, gid, groups, ngroups);
}

int getgrnam_r(const char *name, struct group *gr, char *buf, size_t size, struct group **res) {
    PTRTYPE grubnd  = __sgxbounds_extract_ubnd(gr);
    PTRTYPE bufubnd  = __sgxbounds_extract_ubnd(buf);

    name = __sgxbounds_uninstrument(name);
    gr   = __sgxbounds_uninstrument(gr);
    buf  = __sgxbounds_uninstrument(buf);
    res  = __sgxbounds_uninstrument(res);
    int ret = getgrnam_r_real(name, gr, buf, size, res);
    if (!ret) {
        gr->gr_name   = __sgxbounds_combine_ptr(gr->gr_name, bufubnd);
        gr->gr_passwd = __sgxbounds_combine_ptr(gr->gr_passwd, bufubnd);
        int i;
        for (i=0; gr->gr_mem[i] != NULL; i++)
            gr->gr_mem[i] = __sgxbounds_combine_ptr(gr->gr_mem[i], bufubnd);
        gr->gr_mem = __sgxbounds_combine_ptr(gr->gr_mem, bufubnd);
        if (*res)  *res = __sgxbounds_combine_ptr(*res, grubnd);
    }
    return ret;
}

int getgrgid_r(gid_t gid, struct group *gr, char *buf, size_t size, struct group **res) {
    PTRTYPE grubnd  = __sgxbounds_extract_ubnd(gr);
    PTRTYPE bufubnd  = __sgxbounds_extract_ubnd(buf);

    gr   = __sgxbounds_uninstrument(gr);
    buf  = __sgxbounds_uninstrument(buf);
    res  = __sgxbounds_uninstrument(res);
    int ret = getgrgid_r_real(gid, gr, buf, size, res);
    if (!ret) {
        gr->gr_name   = __sgxbounds_combine_ptr(gr->gr_name, bufubnd);
        gr->gr_passwd = __sgxbounds_combine_ptr(gr->gr_passwd, bufubnd);
        int i;
        for (i=0; gr->gr_mem[i] != NULL; i++)
            gr->gr_mem[i] = __sgxbounds_combine_ptr(gr->gr_mem[i], bufubnd);
        gr->gr_mem = __sgxbounds_combine_ptr(gr->gr_mem, bufubnd);
        if (*res)  *res = __sgxbounds_combine_ptr(*res, grubnd);
    }
    return ret;
}

struct passwd *getpwent() {
    // TODO: uses dummy (highest) bounds, no security here!
    PTRTYPE ubnd = __sgxbounds_highest_bound();
    struct passwd* ret = getpwent_real();
    if (ret) {
        ret->pw_name   = __sgxbounds_combine_ptr(ret->pw_name, ubnd);
        ret->pw_passwd = __sgxbounds_combine_ptr(ret->pw_passwd, ubnd);
        ret->pw_gecos  = __sgxbounds_combine_ptr(ret->pw_gecos, ubnd);
        ret->pw_dir    = __sgxbounds_combine_ptr(ret->pw_dir, ubnd);
        ret->pw_shell  = __sgxbounds_combine_ptr(ret->pw_shell, ubnd);
        ret = __sgxbounds_combine_ptr(ret, ubnd);
    }
    return ret;
}

struct passwd *getpwuid(uid_t uid) {
    // TODO: uses dummy (highest) bounds, no security here!
    PTRTYPE ubnd = __sgxbounds_highest_bound();
    struct passwd* ret = getpwuid_real(uid);
    if (ret) {
        ret->pw_name   = __sgxbounds_combine_ptr(ret->pw_name, ubnd);
        ret->pw_passwd = __sgxbounds_combine_ptr(ret->pw_passwd, ubnd);
        ret->pw_gecos  = __sgxbounds_combine_ptr(ret->pw_gecos, ubnd);
        ret->pw_dir    = __sgxbounds_combine_ptr(ret->pw_dir, ubnd);
        ret->pw_shell  = __sgxbounds_combine_ptr(ret->pw_shell, ubnd);
        ret = __sgxbounds_combine_ptr(ret, ubnd);
    }
    return ret;
}

struct passwd *getpwnam(const char *name) {
    // TODO: uses dummy (highest) bounds, no security here!
    PTRTYPE ubnd = __sgxbounds_highest_bound();
    name = __sgxbounds_uninstrument(name);
    struct passwd* ret = getpwnam_real(name);
    if (ret) {
        ret->pw_name   = __sgxbounds_combine_ptr(ret->pw_name, ubnd);
        ret->pw_passwd = __sgxbounds_combine_ptr(ret->pw_passwd, ubnd);
        ret->pw_gecos  = __sgxbounds_combine_ptr(ret->pw_gecos, ubnd);
        ret->pw_dir    = __sgxbounds_combine_ptr(ret->pw_dir, ubnd);
        ret->pw_shell  = __sgxbounds_combine_ptr(ret->pw_shell, ubnd);
        ret = __sgxbounds_combine_ptr(ret, ubnd);
    }
    return ret;
}

int getpwnam_r(const char *name, struct passwd *pw, char *buf, size_t size, struct passwd **res) {
    PTRTYPE pwubnd  = __sgxbounds_extract_ubnd(pw);
    PTRTYPE bufubnd  = __sgxbounds_extract_ubnd(buf);

    name = __sgxbounds_uninstrument(name);
    pw   = __sgxbounds_uninstrument(pw);
    buf  = __sgxbounds_uninstrument(buf);
    res  = __sgxbounds_uninstrument(res);
    int ret = getpwnam_r_real(name, pw, buf, size, res);
    if (!ret) {
        pw->pw_name   = __sgxbounds_combine_ptr(pw->pw_name, bufubnd);
        pw->pw_passwd = __sgxbounds_combine_ptr(pw->pw_passwd, bufubnd);
        pw->pw_gecos  = __sgxbounds_combine_ptr(pw->pw_gecos, bufubnd);
        pw->pw_dir    = __sgxbounds_combine_ptr(pw->pw_dir, bufubnd);
        pw->pw_shell  = __sgxbounds_combine_ptr(pw->pw_shell, bufubnd);
        if (*res)  *res = __sgxbounds_combine_ptr(*res, pwubnd);
    }
    return ret;
}

int getpwuid_r(uid_t uid, struct passwd *pw, char *buf, size_t size, struct passwd **res) {
    PTRTYPE pwubnd  = __sgxbounds_extract_ubnd(pw);
    PTRTYPE bufubnd  = __sgxbounds_extract_ubnd(buf);

    pw   = __sgxbounds_uninstrument(pw);
    buf  = __sgxbounds_uninstrument(buf);
    res  = __sgxbounds_uninstrument(res);
    int ret = getpwuid_r_real(uid, pw, buf, size, res);
    if (!ret) {
        pw->pw_name   = __sgxbounds_combine_ptr(pw->pw_name, bufubnd);
        pw->pw_passwd = __sgxbounds_combine_ptr(pw->pw_passwd, bufubnd);
        pw->pw_gecos  = __sgxbounds_combine_ptr(pw->pw_gecos, bufubnd);
        pw->pw_dir    = __sgxbounds_combine_ptr(pw->pw_dir, bufubnd);
        pw->pw_shell  = __sgxbounds_combine_ptr(pw->pw_shell, bufubnd);
        if (*res)  *res = __sgxbounds_combine_ptr(*res, pwubnd);
    }
    return ret;
}

struct spwd *getspnam(const char *name) {
    // TODO: uses dummy (highest) bounds, no security here!
    PTRTYPE ubnd = __sgxbounds_highest_bound();
    name = __sgxbounds_uninstrument(name);
    struct spwd* ret = getspnam_real(name);
    if (ret) {
        ret->sp_namp = __sgxbounds_combine_ptr(ret->sp_namp, ubnd);
        ret->sp_pwdp = __sgxbounds_combine_ptr(ret->sp_pwdp, ubnd);
        ret = __sgxbounds_combine_ptr(ret, ubnd);
    }
    return ret;
}

int getspnam_r(const char *name, struct spwd *sp, char *buf, size_t size, struct spwd **res) {
    PTRTYPE spubnd  = __sgxbounds_extract_ubnd(sp);
    PTRTYPE bufubnd  = __sgxbounds_extract_ubnd(buf);

    name = __sgxbounds_uninstrument(name);
    sp   = __sgxbounds_uninstrument(sp);
    buf  = __sgxbounds_uninstrument(buf);
    res  = __sgxbounds_uninstrument(res);
    int ret = getspnam_r_real(name, sp, buf, size, res);
    if (!ret) {
        sp->sp_namp = __sgxbounds_combine_ptr(sp->sp_namp, bufubnd);
        sp->sp_pwdp = __sgxbounds_combine_ptr(sp->sp_pwdp, bufubnd);
        if (*res)  *res = __sgxbounds_combine_ptr(*res, spubnd);
    }
    return ret;
}

int putgrent(const struct group *gr, FILE *f) {
    // TODO: need to thread-safely copy-and-uninstrument gr
    //       such that original gr is not modified
    return -1;
}

int putpwent(const struct passwd *pw, FILE *f) {
    struct passwd inpw;
    pw = __sgxbounds_uninstrument(pw);
    inpw.pw_name   = __sgxbounds_uninstrument(pw->pw_name);
    inpw.pw_passwd = __sgxbounds_uninstrument(pw->pw_passwd);
    inpw.pw_gecos  = __sgxbounds_uninstrument(pw->pw_gecos);
    inpw.pw_dir    = __sgxbounds_uninstrument(pw->pw_dir);
    inpw.pw_shell  = __sgxbounds_uninstrument(pw->pw_shell);
    inpw.pw_uid    = pw->pw_uid;
    inpw.pw_gid    = pw->pw_gid;
    return putpwent_real(&inpw, f);
}

int putspent(const struct spwd *sp, FILE *f) {
    struct spwd insp;
    sp = __sgxbounds_uninstrument(sp);
    insp.sp_namp   = __sgxbounds_uninstrument(sp->sp_namp);
    insp.sp_pwdp   = __sgxbounds_uninstrument(sp->sp_pwdp);
    insp.sp_lstchg = sp->sp_lstchg;
    insp.sp_min    = sp->sp_min;
    insp.sp_max    = sp->sp_max;
    insp.sp_warn   = sp->sp_warn;
    insp.sp_inact  = sp->sp_inact;
    insp.sp_expire = sp->sp_expire;
    insp.sp_flag   = sp->sp_flag;
    return putspent_real(&insp, f);
}

/* ------------------------------------------------------------------------- */
/* --------------------------------- math ---------------------------------- */
/* ------------------------------------------------------------------------- */
// NOTE: added only those needed by Apache and SPEC2006
double modf_real(double x, double *iptr);
double frexp_real(double x, int *e);

double modf(double x, double *iptr) {
    iptr = __sgxbounds_uninstrument(iptr);
    return modf_real(x, iptr);
}

double frexp(double x, int *e) {
    e = __sgxbounds_uninstrument(e);
    return frexp_real(x, e);
}


/* ------------------------------------------------------------------------- */
/* -------------------------------- signal --------------------------------- */
/* ------------------------------------------------------------------------- */
// NOTE: struct sigaction contains only func-ptrs -> no need to deep-uninstrument
int setitimer_real(int which, const struct itimerval *restrict new, struct itimerval *restrict old);
int sigaction_real(int sig, const struct sigaction *restrict sa, struct sigaction *restrict old);
int sigaddset_real(sigset_t *set, int sig);
int sigaltstack_real(const stack_t *restrict ss, stack_t *restrict old);
int sigandset_real(sigset_t *dest, const sigset_t *left, const sigset_t *right);
int sigdelset_real(sigset_t *set, int sig);
int sigemptyset_real(sigset_t *set);
int sigfillset_real(sigset_t *set);
int sigisemptyset_real(const sigset_t *set);
int sigismember_real(const sigset_t *set, int sig);
int sigsetjmp_real(sigjmp_buf buf, int ret);
_Noreturn void siglongjmp_real(sigjmp_buf buf, int ret);
int sigorset_real(sigset_t *dest, const sigset_t *left, const sigset_t *right);
int sigpending_real(sigset_t *set);
int sigprocmask_real(int how, const sigset_t *restrict set, sigset_t *restrict old);
int sigsuspend_real(const sigset_t *mask);
int sigwait_real(const sigset_t *restrict mask, int *restrict sig);
int sigtimedwait_real(const sigset_t *restrict mask, siginfo_t *restrict si, const struct timespec *restrict timeout);
int sigwaitinfo_real(const sigset_t *restrict mask, siginfo_t *restrict si);
void psignal_real(int sig, const char *msg);
void psiginfo_real(const siginfo_t *si, const char *msg);
int getitimer_real(int which, struct itimerval *old);

int getitimer(int which, struct itimerval *old) {
    if (old) old = __sgxbounds_uninstrument(old);
    return getitimer_real(which, old);
}

void psiginfo(const siginfo_t *si, const char *msg) {
    si  = __sgxbounds_uninstrument(si);
    msg = __sgxbounds_uninstrument(msg);
    psiginfo_real(si, msg);
}

void psignal(int sig, const char *msg) {
    msg = __sgxbounds_uninstrument(msg);
    psignal_real(sig, msg);
}

int setitimer(int which, const struct itimerval *restrict new, struct itimerval *restrict old) {
    if (new) new = __sgxbounds_uninstrument(new);
    if (old) old = __sgxbounds_uninstrument(old);
    return setitimer_real(which, new, old);
}

int sigaction(int sig, const struct sigaction *restrict sa, struct sigaction *restrict old) {
    if (sa)  sa = __sgxbounds_uninstrument(sa);
    if (old) old = __sgxbounds_uninstrument(old);
    return sigaction_real(sig, sa, old);
}

int sigaddset(sigset_t *set, int sig) {
    if (set)  set = __sgxbounds_uninstrument(set);
    return sigaddset_real(set, sig);
}

int sigaltstack(const stack_t *restrict ss, stack_t *restrict old) {
    // TODO: implement it?
    return -1;
}

int sigandset(sigset_t *dest, const sigset_t *left, const sigset_t *right) {
    if (dest)  dest = __sgxbounds_uninstrument(dest);
    if (left)  left = __sgxbounds_uninstrument(left);
    if (right) right = __sgxbounds_uninstrument(right);
    return sigandset_real(dest, left, right);
}

int sigdelset(sigset_t *set, int sig) {
    if (set)  set = __sgxbounds_uninstrument(set);
    return sigdelset_real(set, sig);
}

int sigemptyset(sigset_t *set) {
    if (set)  set = __sgxbounds_uninstrument(set);
    return sigemptyset_real(set);
}

int sigfillset(sigset_t *set) {
    if (set)  set = __sgxbounds_uninstrument(set);
    return sigfillset_real(set);
}

int sigisemptyset(const sigset_t *set) {
    set = __sgxbounds_uninstrument(set);
    return sigisemptyset_real(set);
}

int sigismember(const sigset_t *set, int sig) {
    set = __sgxbounds_uninstrument(set);
    return sigismember_real(set, sig);
}

int sigsetjmp(sigjmp_buf buf, int ret) {
    buf = __sgxbounds_uninstrument(buf);
    return sigsetjmp_real(buf, ret);
}

_Noreturn void siglongjmp(sigjmp_buf buf, int ret) {
    buf = __sgxbounds_uninstrument(buf);
    siglongjmp_real(buf, ret);
}

int sigorset(sigset_t *dest, const sigset_t *left, const sigset_t *right) {
    if (dest)  dest = __sgxbounds_uninstrument(dest);
    if (left)  left = __sgxbounds_uninstrument(left);
    if (right) right = __sgxbounds_uninstrument(right);
    return sigorset_real(dest, left, right);
}

int sigpending(sigset_t *set) {
    set = __sgxbounds_uninstrument(set);
    return sigpending_real(set);
}

int sigprocmask(int how, const sigset_t *restrict set, sigset_t *restrict old) {
    if (set) set = __sgxbounds_uninstrument(set);
    if (old) old = __sgxbounds_uninstrument(old);
    return sigprocmask_real(how, set, old);
}

int sigsuspend(const sigset_t *mask) {
    mask = __sgxbounds_uninstrument(mask);
    return sigsuspend_real(mask);
}

int sigwait(const sigset_t *restrict mask, int *restrict sig) {
    if (mask) mask = __sgxbounds_uninstrument(mask);
    if (sig)  sig = __sgxbounds_uninstrument(sig);
    return sigwait_real(mask, sig);
}

int sigtimedwait(const sigset_t *restrict mask, siginfo_t *restrict si, const struct timespec *restrict timeout) {
    if (mask) mask = __sgxbounds_uninstrument(mask);
    if (si)   si = __sgxbounds_uninstrument(si);
    if (timeout)   timeout = __sgxbounds_uninstrument(timeout);
    return sigtimedwait_real(mask, si, timeout);
}

int sigwaitinfo(const sigset_t *restrict mask, siginfo_t *restrict si) {
    if (mask) mask = __sgxbounds_uninstrument(mask);
    if (si)   si = __sgxbounds_uninstrument(si);
    return sigwaitinfo_real(mask, si);
}

/* ------------------------------------------------------------------------- */
/* --------------------------------- ipc ----------------------------------- */
/* ------------------------------------------------------------------------- */
// NOTE: added only those needed by Apache stack
int semop_real(int id, struct sembuf *buf, size_t n);
int semtimedop_real(int id, struct sembuf *buf, size_t n, const struct timespec *ts);

int semop(int id, struct sembuf *buf, size_t n) {
    buf = __sgxbounds_uninstrument(buf);
    return semop_real(id, buf, n);
}

int semtimedop(int id, struct sembuf *buf, size_t n, const struct timespec *ts) {
    buf = __sgxbounds_uninstrument(buf);
    ts  = __sgxbounds_uninstrument(ts);
    return semtimedop_real(id, buf, n, ts);
}


/* ------------------------------------------------------------------------- */
/* ------------------------------ multibyte -------------------------------- */
/* ------------------------------------------------------------------------- */
// NOTE: added only those needed by xalancbmk from SPEC2006

int mbtowc_real(wchar_t *restrict wc, const char *restrict src, size_t n);
int mblen_real(const char *s, size_t n);
size_t wcstombs_real(char *restrict s, const wchar_t *restrict ws, size_t n);
size_t mbstowcs_real(wchar_t *restrict ws, const char *restrict s, size_t wn);

int mbtowc(wchar_t *restrict wc, const char *restrict src, size_t n) {
    wc  = __sgxbounds_uninstrument(wc);
    src = __sgxbounds_uninstrument(src);
    return mbtowc_real(wc, src, n);
}

int mblen(const char *s, size_t n) {
    s  = __sgxbounds_uninstrument(s);
    return mblen_real(s, n);
}

size_t wcstombs(char *restrict s, const wchar_t *restrict ws, size_t n) {
    ws = __sgxbounds_uninstrument(ws);
    s  = __sgxbounds_uninstrument(s);
    return wcstombs_real(s, ws, n);
}

size_t mbstowcs(wchar_t *restrict ws, const char *restrict s, size_t wn) {
    ws = __sgxbounds_uninstrument(ws);
    s  = __sgxbounds_uninstrument(s);
    return mbstowcs_real(ws, s, wn);
}


#ifdef __cplusplus
}
#endif
