/* Valgrind client requests, wrapped as ordinary C functions so Rust can call them.
 *
 * These are macros that expand to a magic no-op instruction sequence. Outside of Valgrind they
 * cost a handful of cycles and do nothing; under Memcheck they retag the definedness ("V") bits
 * of the named memory range. That is the whole mechanism behind this harness: secret bytes are
 * tagged *undefined*, and Memcheck then reports any conditional branch or memory address that
 * depends on them. */

#include <stddef.h>
#include <valgrind/memcheck.h>

/* Tag `n` bytes at `p` as secret (undefined), so that branching on them is an error. */
void kopis_ct_make_undefined(void *p, size_t n) {
    (void)VALGRIND_MAKE_MEM_UNDEFINED(p, n);
}

/* Tag `n` bytes at `p` as public (defined) again. Used to declassify outputs before the harness
 * itself looks at them, and to whitelist values the design intentionally leaks. */
void kopis_ct_make_defined(void *p, size_t n) {
    (void)VALGRIND_MAKE_MEM_DEFINED(p, n);
}

/* Nonzero iff we are running under Valgrind. Lets the harness warn when it is a no-op. */
int kopis_ct_running_on_valgrind(void) {
    return RUNNING_ON_VALGRIND != 0;
}
