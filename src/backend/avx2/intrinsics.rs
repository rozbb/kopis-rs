//! The AVX2 instruction set, as an opaque interface.
//!
//! Every `core::arch::x86_64` intrinsic this backend uses is reached through exactly one thin
//! wrapper here, over the newtypes [`Vec256`] and [`Vec128`] rather than `__m256i` / `__m128i`;
//! nothing outside this file names an intrinsic or a raw pointer. The rest of the backend is
//! then ordinary Rust over an abstract vector type.
//!
//! # Why
//!
//! This is what makes the backend extractable. `__m256i` is a rustc builtin with no MIR
//! definition and the intrinsics are `extern "unadjusted"` declarations with no body, so charon
//! has nothing to lower and aeneas's symbolic interpreter falls over the moment it reaches one.
//! Confining them here lets the extraction treat this one module as opaque
//! (`charon --opaque 'kopis::backend::avx2::intrinsics'`), which aeneas emits as an opaque type
//! plus one opaque function per wrapper — and the Lean side supplies their semantics by hand, in
//! `lean/Kopis/Avx2/Intrinsics.lean`. That file is the *entire* trusted base this backend adds:
//! one axiom per function below, each stating what the instruction does to a 256-bit word.
//!
//! Two consequences for anything written here:
//!
//! * **The bodies are unverified.** Nothing below is checked against the Lean model, and nothing
//!   in Lean is checked against silicon. Keep each wrapper a single instruction with no
//!   arithmetic of its own, so that "does the body match the axiom" stays a matter of reading
//!   one line against the Intel SDM.
//! * **The interface is the specification.** A wrapper's *type* is what the Lean model gets to
//!   assume, which is why the memory accessors below take array and slice references with an
//!   element index rather than raw pointers: a bound the type system states is a bound the model
//!   can state too. This is the same architecture libcrux uses for its AVX2 proofs
//!   (`libcrux/crates/utils/intrinsics/src/avx2_extract.rs`); the wrappers here are written
//!   fresh, but the shape is theirs.
//!
//! # Safety
//!
//! Every function is `#[target_feature(enable = "avx2")]`, so it is safe to call from any other
//! `avx2` function — which is all of this backend — and unsafe to call from outside one, exactly
//! as the intrinsics themselves are. The unaligned loads and stores are the only `unsafe` here;
//! each is preceded by a bounds check that makes the access in-range for *any* arguments, so
//! these are sound as safe functions and the checks are what the Lean preconditions mirror.

#[cfg(target_arch = "x86")]
use core::arch::x86::*;
#[cfg(target_arch = "x86_64")]
use core::arch::x86_64::*;

/// A 256-bit AVX2 vector (`ymm`).
///
/// Opaque on purpose: the extraction models it as an uninterpreted type with a 256-bit view,
/// so the only thing that can be done with one is to pass it back to a function below.
#[derive(Clone, Copy)]
#[repr(transparent)]
pub(crate) struct Vec256(__m256i);

/// A 128-bit SSE vector (`xmm`), needed for the few instructions that take or produce a half
#[derive(Clone, Copy)]
#[repr(transparent)]
pub(crate) struct Vec128(__m128i);

// ---------------------------------------------------------------------------------------
// Constants and bitwise
// ---------------------------------------------------------------------------------------

/// `vpbroadcastw`: every 16-bit lane set to `a`
#[inline]
#[target_feature(enable = "avx2")]
pub(crate) fn set1_epi16(a: i16) -> Vec256 {
    Vec256(_mm256_set1_epi16(a))
}

/// `vpbroadcastd`: every 32-bit lane set to `a`
#[inline]
#[target_feature(enable = "avx2")]
pub(crate) fn set1_epi32(a: i32) -> Vec256 {
    Vec256(_mm256_set1_epi32(a))
}

/// `vpxor`: all 256 bits zero
#[inline]
#[target_feature(enable = "avx2")]
pub(crate) fn setzero_si256() -> Vec256 {
    Vec256(_mm256_setzero_si256())
}

/// `vmovd`: the low 32 bits set to `a`, the rest zero
#[inline]
#[target_feature(enable = "avx2")]
pub(crate) fn cvtsi32_si128(a: i32) -> Vec128 {
    Vec128(_mm_cvtsi32_si128(a))
}

/// `vpand`: bitwise and of all 256 bits
#[inline]
#[target_feature(enable = "avx2")]
pub(crate) fn and_si256(a: Vec256, b: Vec256) -> Vec256 {
    Vec256(_mm256_and_si256(a.0, b.0))
}

// ---------------------------------------------------------------------------------------
// Lane arithmetic
// ---------------------------------------------------------------------------------------

/// `vpaddw`: 16 lanes of wrapping 16-bit addition
#[inline]
#[target_feature(enable = "avx2")]
pub(crate) fn add_epi16(a: Vec256, b: Vec256) -> Vec256 {
    Vec256(_mm256_add_epi16(a.0, b.0))
}

/// `vpsubw`: 16 lanes of wrapping 16-bit subtraction
#[inline]
#[target_feature(enable = "avx2")]
pub(crate) fn sub_epi16(a: Vec256, b: Vec256) -> Vec256 {
    Vec256(_mm256_sub_epi16(a.0, b.0))
}

/// `vpaddd`: 8 lanes of wrapping 32-bit addition
#[inline]
#[target_feature(enable = "avx2")]
pub(crate) fn add_epi32(a: Vec256, b: Vec256) -> Vec256 {
    Vec256(_mm256_add_epi32(a.0, b.0))
}

/// `vpsubd`: 8 lanes of wrapping 32-bit subtraction
#[inline]
#[target_feature(enable = "avx2")]
pub(crate) fn sub_epi32(a: Vec256, b: Vec256) -> Vec256 {
    Vec256(_mm256_sub_epi32(a.0, b.0))
}

/// `vpmullw`: 16 lanes of the low half of the 16×16→32 product
#[inline]
#[target_feature(enable = "avx2")]
pub(crate) fn mullo_epi16(a: Vec256, b: Vec256) -> Vec256 {
    Vec256(_mm256_mullo_epi16(a.0, b.0))
}

/// `vpmulhw`: 16 lanes of the high half of the *signed* 16×16→32 product
#[inline]
#[target_feature(enable = "avx2")]
pub(crate) fn mulhi_epi16(a: Vec256, b: Vec256) -> Vec256 {
    Vec256(_mm256_mulhi_epi16(a.0, b.0))
}

/// `vpmulld`: 8 lanes of the low half of the 32×32→64 product
#[inline]
#[target_feature(enable = "avx2")]
pub(crate) fn mullo_epi32(a: Vec256, b: Vec256) -> Vec256 {
    Vec256(_mm256_mullo_epi32(a.0, b.0))
}

/// `vpcmpgtd`: 8 lanes of signed 32-bit `>`, as an all-ones / all-zeros mask
#[inline]
#[target_feature(enable = "avx2")]
pub(crate) fn cmpgt_epi32(a: Vec256, b: Vec256) -> Vec256 {
    Vec256(_mm256_cmpgt_epi32(a.0, b.0))
}

// ---------------------------------------------------------------------------------------
// Shifts
// ---------------------------------------------------------------------------------------

/// `vpsraw`: 16 lanes of arithmetic right shift by the immediate `IMM`
#[inline]
#[target_feature(enable = "avx2")]
pub(crate) fn srai_epi16<const IMM: i32>(a: Vec256) -> Vec256 {
    Vec256(_mm256_srai_epi16::<IMM>(a.0))
}

/// `vpsrad`: 8 lanes of arithmetic right shift by the immediate `IMM`
#[inline]
#[target_feature(enable = "avx2")]
pub(crate) fn srai_epi32<const IMM: i32>(a: Vec256) -> Vec256 {
    Vec256(_mm256_srai_epi32::<IMM>(a.0))
}

/// `vpsrlw`: 16 lanes of logical right shift by the immediate `IMM`
#[inline]
#[target_feature(enable = "avx2")]
pub(crate) fn srli_epi16<const IMM: i32>(a: Vec256) -> Vec256 {
    Vec256(_mm256_srli_epi16::<IMM>(a.0))
}

/// `vpslld`: 8 lanes of left shift by the immediate `IMM`
#[inline]
#[target_feature(enable = "avx2")]
pub(crate) fn slli_epi32<const IMM: i32>(a: Vec256) -> Vec256 {
    Vec256(_mm256_slli_epi32::<IMM>(a.0))
}

/// `vpsrlw`: 16 lanes of logical right shift by a count taken from the low 64 bits of `count`
///
/// Counts of 16 or more shift the lane out entirely, giving zero.
#[inline]
#[target_feature(enable = "avx2")]
pub(crate) fn srl_epi16(a: Vec256, count: Vec128) -> Vec256 {
    Vec256(_mm256_srl_epi16(a.0, count.0))
}

/// `vpsrlvd`: 8 lanes of logical right shift, each by its own lane of `counts`
#[inline]
#[target_feature(enable = "avx2")]
pub(crate) fn srlv_epi32(a: Vec256, counts: Vec256) -> Vec256 {
    Vec256(_mm256_srlv_epi32(a.0, counts.0))
}

// ---------------------------------------------------------------------------------------
// Shuffles, packs and lane surgery
// ---------------------------------------------------------------------------------------

/// `vpshufb`: byte `i` of each 128-bit half becomes byte `b[i] & 0xF` of that same half of `a`,
/// or zero when bit 7 of `b[i]` is set
#[inline]
#[target_feature(enable = "avx2")]
pub(crate) fn shuffle_epi8(a: Vec256, b: Vec256) -> Vec256 {
    Vec256(_mm256_shuffle_epi8(a.0, b.0))
}

/// `vpunpcklwd`: interleaves the low four 16-bit lanes of each 128-bit half
#[inline]
#[target_feature(enable = "avx2")]
pub(crate) fn unpacklo_epi16(a: Vec256, b: Vec256) -> Vec256 {
    Vec256(_mm256_unpacklo_epi16(a.0, b.0))
}

/// `vpunpckhwd`: interleaves the high four 16-bit lanes of each 128-bit half
#[inline]
#[target_feature(enable = "avx2")]
pub(crate) fn unpackhi_epi16(a: Vec256, b: Vec256) -> Vec256 {
    Vec256(_mm256_unpackhi_epi16(a.0, b.0))
}

/// `vpunpckldq`: interleaves the low two 32-bit lanes of each 128-bit half
#[inline]
#[target_feature(enable = "avx2")]
pub(crate) fn unpacklo_epi32(a: Vec256, b: Vec256) -> Vec256 {
    Vec256(_mm256_unpacklo_epi32(a.0, b.0))
}

/// `vpunpckhdq`: interleaves the high two 32-bit lanes of each 128-bit half
#[inline]
#[target_feature(enable = "avx2")]
pub(crate) fn unpackhi_epi32(a: Vec256, b: Vec256) -> Vec256 {
    Vec256(_mm256_unpackhi_epi32(a.0, b.0))
}

/// `vpunpcklqdq`: the low 64-bit lane of each 128-bit half of `a`, then that of `b`
#[inline]
#[target_feature(enable = "avx2")]
pub(crate) fn unpacklo_epi64(a: Vec256, b: Vec256) -> Vec256 {
    Vec256(_mm256_unpacklo_epi64(a.0, b.0))
}

/// `vpunpckhqdq`: the high 64-bit lane of each 128-bit half of `a`, then that of `b`
#[inline]
#[target_feature(enable = "avx2")]
pub(crate) fn unpackhi_epi64(a: Vec256, b: Vec256) -> Vec256 {
    Vec256(_mm256_unpackhi_epi64(a.0, b.0))
}

/// `vperm2i128`: each 128-bit half of the result selected from the four halves of `a`, `b` by a
/// nibble of `IMM` (or zeroed when its bit 3 is set)
#[inline]
#[target_feature(enable = "avx2")]
pub(crate) fn permute2x128_si256<const IMM: i32>(a: Vec256, b: Vec256) -> Vec256 {
    Vec256(_mm256_permute2x128_si256::<IMM>(a.0, b.0))
}

/// `vpermq`: the four 64-bit lanes permuted by the four 2-bit fields of `IMM`
#[inline]
#[target_feature(enable = "avx2")]
pub(crate) fn permute4x64_epi64<const IMM: i32>(a: Vec256) -> Vec256 {
    Vec256(_mm256_permute4x64_epi64::<IMM>(a.0))
}

/// `vpackssdw`: the 32-bit lanes of `a` then `b`, *signed*-saturated to 16 bits, interleaved by
/// 128-bit half
#[inline]
#[target_feature(enable = "avx2")]
pub(crate) fn packs_epi32(a: Vec256, b: Vec256) -> Vec256 {
    Vec256(_mm256_packs_epi32(a.0, b.0))
}

/// `vpackusdw`: the 32-bit lanes of `a` then `b`, *unsigned*-saturated to 16 bits, interleaved
/// by 128-bit half
#[inline]
#[target_feature(enable = "avx2")]
pub(crate) fn packus_epi32(a: Vec256, b: Vec256) -> Vec256 {
    Vec256(_mm256_packus_epi32(a.0, b.0))
}

/// `vpmovzxwd`: the eight 16-bit lanes of a half, zero-extended to 32 bits
#[inline]
#[target_feature(enable = "avx2")]
pub(crate) fn cvtepu16_epi32(a: Vec128) -> Vec256 {
    Vec256(_mm256_cvtepu16_epi32(a.0))
}

/// The low 128 bits of `a`, a no-op at the instruction level
#[inline]
#[target_feature(enable = "avx2")]
pub(crate) fn castsi256_si128(a: Vec256) -> Vec128 {
    Vec128(_mm256_castsi256_si128(a.0))
}

/// `vextracti128`: half `IMM` of `a`
#[inline]
#[target_feature(enable = "avx2")]
pub(crate) fn extracti128_si256<const IMM: i32>(a: Vec256) -> Vec128 {
    Vec128(_mm256_extracti128_si256::<IMM>(a.0))
}

/// `vbroadcasti128`: `a` in both 128-bit halves
#[inline]
#[target_feature(enable = "avx2")]
pub(crate) fn broadcastsi128_si256(a: Vec128) -> Vec256 {
    Vec256(_mm256_broadcastsi128_si256(a.0))
}

// ---------------------------------------------------------------------------------------
// Memory
//
// One accessor per element type the backend needs, each indexed in whole vectors rather than
// elements, and each bounds-checked. `NttElem` and the pointwise accumulator are `[i16; 512]`
// and `[i32; 512]` outright — the two residue blocks are the two halves — so these are plain
// typed loads and stores, with no reinterpretation to state.
// ---------------------------------------------------------------------------------------

/// Loads the 16 `i16` at `src[16 * i ..]`
#[inline]
#[target_feature(enable = "avx2")]
pub(crate) fn load_i16<const N: usize>(src: &[i16; N], i: usize) -> Vec256 {
    assert!(16 * (i + 1) <= N);
    // SAFETY: the assert puts all 16 elements in bounds; the load is unaligned.
    Vec256(unsafe { _mm256_loadu_si256(src.as_ptr().add(16 * i).cast()) })
}

/// Stores 16 `i16` at `dst[16 * i ..]`
#[inline]
#[target_feature(enable = "avx2")]
pub(crate) fn store_i16<const N: usize>(dst: &mut [i16; N], i: usize, v: Vec256) {
    assert!(16 * (i + 1) <= N);
    // SAFETY: the assert puts all 16 elements in bounds; the store is unaligned.
    unsafe { _mm256_storeu_si256(dst.as_mut_ptr().add(16 * i).cast(), v.0) }
}

/// Loads the 16 `u16` at `src[16 * i ..]`
#[inline]
#[target_feature(enable = "avx2")]
pub(crate) fn load_u16<const N: usize>(src: &[u16; N], i: usize) -> Vec256 {
    assert!(16 * (i + 1) <= N);
    // SAFETY: the assert puts all 16 elements in bounds; the load is unaligned.
    Vec256(unsafe { _mm256_loadu_si256(src.as_ptr().add(16 * i).cast()) })
}

/// Stores 16 `u16` at `dst[16 * i ..]`
#[inline]
#[target_feature(enable = "avx2")]
pub(crate) fn store_u16<const N: usize>(dst: &mut [u16; N], i: usize, v: Vec256) {
    assert!(16 * (i + 1) <= N);
    // SAFETY: the assert puts all 16 elements in bounds; the store is unaligned.
    unsafe { _mm256_storeu_si256(dst.as_mut_ptr().add(16 * i).cast(), v.0) }
}

/// Loads the 8 `i32` at `src[8 * i ..]`
#[inline]
#[target_feature(enable = "avx2")]
pub(crate) fn load_i32<const N: usize>(src: &[i32; N], i: usize) -> Vec256 {
    assert!(8 * (i + 1) <= N);
    // SAFETY: the assert puts all 8 elements in bounds; the load is unaligned.
    Vec256(unsafe { _mm256_loadu_si256(src.as_ptr().add(8 * i).cast()) })
}

/// Stores 8 `i32` at `dst[8 * i ..]`
#[inline]
#[target_feature(enable = "avx2")]
pub(crate) fn store_i32<const N: usize>(dst: &mut [i32; N], i: usize, v: Vec256) {
    assert!(8 * (i + 1) <= N);
    // SAFETY: the assert puts all 8 elements in bounds; the store is unaligned.
    unsafe { _mm256_storeu_si256(dst.as_mut_ptr().add(8 * i).cast(), v.0) }
}

/// Loads the 32 `u8` at `src[32 * i ..]`
#[inline]
#[target_feature(enable = "avx2")]
pub(crate) fn load_u8<const N: usize>(src: &[u8; N], i: usize) -> Vec256 {
    assert!(32 * (i + 1) <= N);
    // SAFETY: the assert puts all 32 bytes in bounds; the load is unaligned.
    Vec256(unsafe { _mm256_loadu_si256(src.as_ptr().add(32 * i).cast()) })
}

/// Loads the 16 bytes at `src[offset ..]`, as a half-vector
///
/// Byte-indexed rather than vector-indexed: `crate::backend::avx2::ser` reads groups at
/// multiples of the coefficient width, which is not a multiple of 16.
#[inline]
#[target_feature(enable = "avx2")]
pub(crate) fn load_u8x16(src: &[u8], offset: usize) -> Vec128 {
    assert!(offset + 16 <= src.len());
    // SAFETY: the assert puts all 16 bytes in bounds; the load is unaligned.
    Vec128(unsafe { _mm_loadu_si128(src.as_ptr().add(offset).cast()) })
}
