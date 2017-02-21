#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <limits.h>
#include <setjmp.h>
#include <stdio.h>
#include <time.h>
#include <dirent.h>
#include <fcntl.h>
#include <unistd.h>

void* get_heap_end() {
    return (void*)(1LL<<32);
}

void* pvalloc(size_t s) {
    // dummy
    return (void*)0;
}
