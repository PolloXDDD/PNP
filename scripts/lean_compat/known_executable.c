#define _GNU_SOURCE
#include <dlfcn.h>
#include <errno.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

/* Environment compatibility only. Supply the already-known executable path
   for Lean/Lake's application-directory discovery, without reading procfs. */
extern char *program_invocation_short_name;
ssize_t readlink(const char *path, char *buf, size_t n) {
    const char *bin = getenv("PNP_LEAN_BIN");
    char own[80];
    snprintf(own, sizeof own, "/proc/%ld/exe", (long)getpid());
    if (bin && (!strcmp(path, "/proc/self/exe") || !strcmp(path, own)) &&
        (!strcmp(program_invocation_short_name, "lean") ||
         !strcmp(program_invocation_short_name, "lake"))) {
        char known[4096];
        int len = snprintf(known, sizeof known, "%s/%s", bin,
                           program_invocation_short_name);
        if (len < 0 || (size_t)len >= sizeof known) { errno = ENAMETOOLONG; return -1; }
        size_t count = (size_t)len < n ? (size_t)len : n;
        memcpy(buf, known, count);
        return (ssize_t)count;
    }
    ssize_t (*real_readlink)(const char *, char *, size_t) = dlsym(RTLD_NEXT, "readlink");
    return real_readlink(path, buf, n);
}
