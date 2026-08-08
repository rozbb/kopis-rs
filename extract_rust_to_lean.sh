#!/bin/bash

set -eux

AENEAS_VERSION="b59d5188c082f704a418c7cb4e52ad69328002d1"

CHARON="nix run github:AeneasVerif/aeneas/${AENEAS_VERSION}#charon \
    --extra-experimental-features nix-command \
    --extra-experimental-features flakes \
    --"
AENEAS="nix run github:AeneasVerif/aeneas/${AENEAS_VERSION} \
    --extra-experimental-features nix-command \
    --extra-experimental-features flakes \
    --"

# All three backends are extracted, into separate files and separate Lean namespaces. The backend
# is forced here rather than left to `build.rs`'s autodetection so that each run sees exactly one
# set of `#[cfg(kopis_avx2)]` / `#[cfg(kopis_neon)]` dispatch blocks — either all of them or none
# — and the extracted code is the code the corresponding proofs are written against.
#
# This goes through RUSTFLAGS rather than charon's --rustc-arg because build.rs has to see it
# too: build.rs is what turns the cfg into the backend selection.

# ---------------------------------------------------------------------------------------
# The serial backend: the portable code, with every dispatch block cfg'd out. `ExtractedRustSerial.lean`
# is what `lean/Kopis/Properties/*` and `TopLevelTheoremsSerial.lean` are proved about.
# ---------------------------------------------------------------------------------------

export RUSTFLAGS='--cfg kopis_backend="serial"'
$CHARON cargo --preset=aeneas
$AENEAS kopis.llbc -backend lean -loops-to-rec -namespace RustKopisSerial
mv Kopis.lean ./lean/ExtractedRustSerial.lean
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
#
# Like the NEON one below, this is a *cross* extraction, and for the same reason: the target is
# named explicitly rather than left as the host, so that the extraction is the same on every
# machine. Without `--target`, `build.rs` accepts the configuration only when the *host* is x86
# with AVX2 (see `avx2_is_available`), so the script would die here on an Apple silicon or other
# non-x86 machine — and, worse, would silently be extracting a host-dependent build on the ones
# where it succeeded.
#
# `-C target-feature=+avx2` is then required rather than merely tidy: it is what makes
# `avx2_is_available()` true for a cross build, since the host-CPU fallback it would otherwise
# rely on is disabled the moment host and target differ.
# ---------------------------------------------------------------------------------------

export RUSTFLAGS='--cfg kopis_backend="avx2" -C target-feature=+avx2'
$CHARON cargo --preset=aeneas \
    --opaque 'kopis::backend::avx2::intrinsics' \
    --opaque 'kopis::backend::avx2::cpu' \
    -- --target x86_64-unknown-linux-gnu
$AENEAS kopis.llbc -backend lean -loops-to-rec -namespace RustKopisAvx2
mv Kopis.lean ./lean/ExtractedRustAvx2.lean
rm kopis.llbc

# ---------------------------------------------------------------------------------------
# The NEON backend. This one is a *cross* extraction: the code only exists on AArch64, so
# charon has to run rustc for `aarch64-unknown-linux-gnu` rather than the host. Nothing else
# about the run differs — the sysroot charon builds carries full MIR for that target too.
#
# `-C target-feature=+sha3` is not optional. `build.rs` gates the two-way TurboSHAKE
# (`backend::neon::keccak`, and the batched samplers that drive it) on the ARMv8.2 SHA3
# extension, so without it the extraction would silently cover a *different*, smaller backend.
# `aarch64-apple-darwin` — every Apple silicon core — enables `sha3` by default, so this is the
# configuration that actually ships; a generic AArch64 target without the extension gets the
# scalar sponge, and that variant is NOT covered by this extraction or the proofs built on it.
#
# One module is kept opaque, which aeneas emits as axioms:
#
#   * `backend::neon::intrinsics` — the SIMD instruction set. The NEON vector types are rustc
#     builtins with no MIR and the intrinsics are bodyless `extern "unadjusted"` declarations,
#     so there is nothing for charon to lower. Their semantics are supplied by hand in
#     `lean/Kopis/Neon/Intrinsics.lean` — that file is this backend's whole added trust base.
#
# Note what is *not* here: `backend::neon::cpu`. AVX2 has to keep its CPUID/XGETBV probe opaque,
# but NEON is baseline on AArch64 and `available()` is a compile-time constant `true`, so it
# extracts as an ordinary definition and adds no assumption at all. This backend's trust base is
# therefore the intrinsics and nothing else.
# ---------------------------------------------------------------------------------------

export RUSTFLAGS='--cfg kopis_backend="neon" -C target-feature=+sha3'
$CHARON cargo --preset=aeneas \
    --opaque 'kopis::backend::neon::intrinsics' \
    -- --target aarch64-unknown-linux-gnu
$AENEAS kopis.llbc -backend lean -loops-to-rec -namespace RustKopisNeon
mv Kopis.lean ./lean/ExtractedRustNeon.lean
rm kopis.llbc
