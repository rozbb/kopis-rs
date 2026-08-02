#!/bin/bash

set -eux

CHARON=/home/dev/aeneas/charon/bin/charon
AENEAS=/home/dev/aeneas/bin/aeneas

# Both backends are extracted, into separate files and separate Lean namespaces. The backend is
# forced here rather than left to `build.rs`'s autodetection so that each run sees exactly one
# set of `#[cfg(kopis_avx2)]` dispatch blocks — either all of them or none — and the extracted
# code is the code the corresponding proofs are written against.
#
# This goes through RUSTFLAGS rather than charon's --rustc-arg because build.rs has to see it
# too: build.rs is what turns the cfg into the backend selection.

# ---------------------------------------------------------------------------------------
# The serial backend: the portable code, with every dispatch block cfg'd out. `ExtractedRust.lean`
# is what `lean/Kopis/Properties/*` and `TopLevelTheorems.lean` are proved about.
# ---------------------------------------------------------------------------------------

export RUSTFLAGS='--cfg kopis_backend="serial"'
$CHARON cargo --preset=aeneas
$AENEAS kopis.llbc -backend lean -loops-to-rec -namespace RustKopisSerial
mv Kopis.lean ./lean/ExtractedRust.lean
rm kopis.llbc

# ---------------------------------------------------------------------------------------
# The AVX2 backend. Two modules are kept opaque, which aeneas emits as axioms:
#
#   * `backend::avx2::intrinsics` — the SIMD instruction set. `__m256i` is a rustc builtin with
#     no MIR and the intrinsics are bodyless `extern "unadjusted"` declarations, so there is
#     nothing for charon to lower; without this, aeneas aborts with `Unreachable` at the first
#     `_mm256_set1_epi16`. Their semantics are supplied by hand in
#     `lean/Kopis/Avx2/Intrinsics.lean` — that file is this backend's whole added trust base.
#   * `backend::avx2::cpu` — the CPUID/XGETBV feature probe. Nothing can be proved about it
#     here, so `available()` becomes an assumption rather than a definition.
#
# Everything else in `backend/avx2/` is ordinary Rust and is translated normally.
# ---------------------------------------------------------------------------------------

export RUSTFLAGS='--cfg kopis_backend="avx2"'
$CHARON cargo --preset=aeneas \
    --opaque 'kopis::backend::avx2::intrinsics' \
    --opaque 'kopis::backend::avx2::cpu'
$AENEAS kopis.llbc -backend lean -loops-to-rec -namespace RustKopisAvx2
mv Kopis.lean ./lean/ExtractedRustAvx2.lean
rm kopis.llbc
