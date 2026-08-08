//! The AArch64 NEON instruction set, as an opaque interface.
//!
//! Every `core::arch::aarch64` intrinsic this backend uses is reached through exactly one thin
//! wrapper here, over the newtype [`Vec128`] rather than `int16x8_t` / `uint64x2_t` / …; nothing
//! outside this file names an intrinsic or a raw pointer. The rest of the backend is then
//! ordinary Rust over an abstract vector type.
//!
//! # Why
//!
//! This is what makes the backend extractable. The NEON vector types are rustc builtins with no
//! MIR definition and the intrinsics are `extern "unadjusted"` declarations with no body, so
//! charon has nothing to lower and aeneas's symbolic interpreter falls over the moment it reaches
//! one. Confining them here lets the extraction treat this one module as opaque
//! (`charon --opaque 'kopis::backend::neon::intrinsics'`), which aeneas emits as an opaque type
//! plus one opaque function per wrapper — and the Lean side supplies their semantics by hand, in
//! `lean/Kopis/Neon/Intrinsics.lean`. That file is the *entire* trusted base this backend adds:
//! one axiom per function below, each stating what the instruction does to a 128-bit word.
//!
//! Three consequences for anything written here:
//!
//! * **The bodies are unverified.** Nothing below is checked against the Lean model, and nothing
//!   in Lean is checked against silicon. Keep each wrapper a single instruction with no
//!   arithmetic of its own, so that "does the body match the axiom" stays a matter of reading
//!   one line against the Arm ARM (DDI 0487, C7.2) and the ACLE intrinsic reference.
//! * **The interface is the specification.** A wrapper's *type* is what the Lean model gets to
//!   assume, which is why the memory accessors below take array and slice references with an
//!   element index rather than raw pointers: a bound the type system states is a bound the model
//!   can state too. This is the same architecture the AVX2 backend uses
//!   ([`crate::backend::avx2::intrinsics`]), and the same one libcrux uses for its own proofs.
//! * **One vector type, not ten.** AArch64 spells `int16x8_t`, `uint16x8_t`, `int32x4_t`,
//!   `uint8x16_t` and `uint64x2_t` as distinct types converted by `vreinterpretq_*`, which are
//!   *no-ops* at the instruction level — a register is 128 bits and nothing more. Collapsing them
//!   into one [`Vec128`] and doing the reinterpretation inside each wrapper generates identical
//!   code and removes the whole `vreinterpretq_*` family from the extraction, where it would
//!   otherwise be dozens of axioms all saying "the identity". The lane width a wrapper reads is
//!   in its *name*, exactly as it is in the assembly mnemonic.
//!
//! # Naming
//!
//! Each wrapper is named for the instruction it emits, with the lane arrangement appended:
//! `sqdmulh_s16` is `sqdmulh.8h`, `trn1_64` is `trn1.2d`, `smull_high_s16` is `smull2.4s`. Where
//! an operation is sign-agnostic because it is defined by wrapping — `add`, `sub`, `mul` — the
//! name carries only the width. The doc comment on each gives the mnemonic and the operation, and
//! those two lines are what a reviewer checks against the architecture manual.
//!
//! # Safety
//!
//! Every function is `#[target_feature(enable = "neon")]` (plus `sha3` for the four FEAT_SHA3
//! instructions), so it is safe to call from any other function carrying the same feature — which
//! is all of this backend — and unsafe to call from outside one, exactly as the intrinsics
//! themselves are. The unaligned loads and stores are the only `unsafe` here; each is preceded by
//! a bounds check that makes the access in-range for *any* arguments, so these are sound as safe
//! functions and the checks are what the Lean preconditions mirror.

use core::arch::aarch64::*;

/// A 128-bit NEON vector (`Vn`, the `q` form).
///
/// Opaque on purpose: the extraction models it as an uninterpreted type with a 128-bit view, so
/// the only thing that can be done with one is to pass it back to a function below. The `u8`
/// arrangement it wraps is arbitrary — it is a register, and every wrapper reinterprets to
/// whatever arrangement its instruction wants.
#[derive(Clone, Copy)]
#[repr(transparent)]
pub(crate) struct Vec128(uint8x16_t);

// ---------------------------------------------------------------------------------------
// Broadcasts and constants
// ---------------------------------------------------------------------------------------

/// `dup.8h`: every 16-bit lane set to `a`
#[inline]
#[target_feature(enable = "neon")]
pub(crate) fn dup_n_s16(a: i16) -> Vec128 {
    Vec128(vreinterpretq_u8_s16(vdupq_n_s16(a)))
}

/// `dup.8h`: every 16-bit lane set to `a`
#[inline]
#[target_feature(enable = "neon")]
pub(crate) fn dup_n_u16(a: u16) -> Vec128 {
    Vec128(vreinterpretq_u8_u16(vdupq_n_u16(a)))
}

/// `dup.4s`: every 32-bit lane set to `a`
#[inline]
#[target_feature(enable = "neon")]
pub(crate) fn dup_n_s32(a: i32) -> Vec128 {
    Vec128(vreinterpretq_u8_s32(vdupq_n_s32(a)))
}

/// `dup.4s`: every 32-bit lane set to `a`
#[inline]
#[target_feature(enable = "neon")]
pub(crate) fn dup_n_u32(a: u32) -> Vec128 {
    Vec128(vreinterpretq_u8_u32(vdupq_n_u32(a)))
}

/// `dup.2d`: both 64-bit lanes set to `a`
///
/// Only [`super::keccak`] works in 64-bit lanes, so this exists on the same condition it does.
#[inline]
#[cfg(kopis_neon_sha3)]
#[target_feature(enable = "neon")]
pub(crate) fn dup_n_u64(a: u64) -> Vec128 {
    Vec128(vreinterpretq_u8_u64(vdupq_n_u64(a)))
}

/// The vector whose low 64-bit lane is `lo` and whose high one is `hi`
///
/// Two `fmov`s and an `ins` rather than one instruction — the only wrapper here that is not a
/// single instruction, because building a vector from two scalars has no single-instruction form.
/// Its meaning is still exactly one equation, which is what the axiom needs.
#[inline]
#[cfg(kopis_neon_sha3)]
#[target_feature(enable = "neon")]
pub(crate) fn set_u64x2(lo: u64, hi: u64) -> Vec128 {
    Vec128(vreinterpretq_u8_u64(vcombine_u64(
        vcreate_u64(lo),
        vcreate_u64(hi),
    )))
}

// ---------------------------------------------------------------------------------------
// Bitwise
// ---------------------------------------------------------------------------------------

/// `and.16b`: bitwise and of all 128 bits
#[inline]
#[target_feature(enable = "neon")]
pub(crate) fn and(a: Vec128, b: Vec128) -> Vec128 {
    Vec128(vandq_u8(a.0, b.0))
}

/// `eor.16b`: bitwise exclusive or of all 128 bits
///
/// Only Keccak's ι step needs a plain xor — the NTT never does — so this exists on the same
/// condition [`super::keccak`] does.
#[inline]
#[cfg(kopis_neon_sha3)]
#[target_feature(enable = "neon")]
pub(crate) fn eor(a: Vec128, b: Vec128) -> Vec128 {
    Vec128(veorq_u8(a.0, b.0))
}

/// `cnt.16b`: the population count of each *byte*, in place
#[inline]
#[target_feature(enable = "neon")]
pub(crate) fn cnt_u8(a: Vec128) -> Vec128 {
    Vec128(vcntq_u8(a.0))
}

// ---------------------------------------------------------------------------------------
// 16-bit lane arithmetic
// ---------------------------------------------------------------------------------------

/// `add.8h`: 8 lanes of wrapping 16-bit addition
#[inline]
#[target_feature(enable = "neon")]
pub(crate) fn add_16(a: Vec128, b: Vec128) -> Vec128 {
    Vec128(vreinterpretq_u8_s16(vaddq_s16(
        vreinterpretq_s16_u8(a.0),
        vreinterpretq_s16_u8(b.0),
    )))
}

/// `sub.8h`: 8 lanes of wrapping 16-bit subtraction
#[inline]
#[target_feature(enable = "neon")]
pub(crate) fn sub_16(a: Vec128, b: Vec128) -> Vec128 {
    Vec128(vreinterpretq_u8_s16(vsubq_s16(
        vreinterpretq_s16_u8(a.0),
        vreinterpretq_s16_u8(b.0),
    )))
}

/// `mul.8h`: 8 lanes of the low half of the 16×16→32 product
#[inline]
#[target_feature(enable = "neon")]
pub(crate) fn mul_16(a: Vec128, b: Vec128) -> Vec128 {
    Vec128(vreinterpretq_u8_s16(vmulq_s16(
        vreinterpretq_s16_u8(a.0),
        vreinterpretq_s16_u8(b.0),
    )))
}

/// `sqdmulh.8h`: 8 lanes of the high half of the *doubled* signed 16×16→32 product, saturating
///
/// That is, lane `i` is `sat((2·a[i]·b[i]) >> 16)`, where the saturation clamps to `i16` range
/// and can only bite when both operands are −2^15. AArch64 has no plain 16-bit high-multiply,
/// which is why this doubled form is what the backend reaches for.
#[inline]
#[target_feature(enable = "neon")]
pub(crate) fn sqdmulh_s16(a: Vec128, b: Vec128) -> Vec128 {
    Vec128(vreinterpretq_u8_s16(vqdmulhq_s16(
        vreinterpretq_s16_u8(a.0),
        vreinterpretq_s16_u8(b.0),
    )))
}

/// `shsub.8h`: 8 lanes of *halving* signed 16-bit subtraction, `(a − b) >> 1`
///
/// The subtraction is done at 17 bits and the shift is arithmetic, so there is no overflow and
/// no rounding: the result is the exact floor of `(a − b)/2`.
#[inline]
#[target_feature(enable = "neon")]
pub(crate) fn shsub_s16(a: Vec128, b: Vec128) -> Vec128 {
    Vec128(vreinterpretq_u8_s16(vhsubq_s16(
        vreinterpretq_s16_u8(a.0),
        vreinterpretq_s16_u8(b.0),
    )))
}

/// `sshr.8h #IMM`: 8 lanes of arithmetic right shift by the immediate `IMM`
#[inline]
#[target_feature(enable = "neon")]
pub(crate) fn sshr_n_s16<const IMM: i32>(a: Vec128) -> Vec128 {
    Vec128(vreinterpretq_u8_s16(vshrq_n_s16::<IMM>(
        vreinterpretq_s16_u8(a.0),
    )))
}

/// `ushl.8h`: 8 lanes of logical shift, each by the *signed* count in its own lane of `counts`
///
/// A negative count shifts right, which is how the backend spells a variable right shift; a
/// count of ±16 or beyond shifts the lane out entirely, giving zero.
#[inline]
#[target_feature(enable = "neon")]
pub(crate) fn ushl_u16(a: Vec128, counts: Vec128) -> Vec128 {
    Vec128(vreinterpretq_u8_u16(vshlq_u16(
        vreinterpretq_u16_u8(a.0),
        vreinterpretq_s16_u8(counts.0),
    )))
}

// ---------------------------------------------------------------------------------------
// 32-bit lane arithmetic
// ---------------------------------------------------------------------------------------

/// `add.4s`: 4 lanes of wrapping 32-bit addition
#[inline]
#[target_feature(enable = "neon")]
pub(crate) fn add_32(a: Vec128, b: Vec128) -> Vec128 {
    Vec128(vreinterpretq_u8_s32(vaddq_s32(
        vreinterpretq_s32_u8(a.0),
        vreinterpretq_s32_u8(b.0),
    )))
}

/// `sub.4s`: 4 lanes of wrapping 32-bit subtraction
#[inline]
#[target_feature(enable = "neon")]
pub(crate) fn sub_32(a: Vec128, b: Vec128) -> Vec128 {
    Vec128(vreinterpretq_u8_s32(vsubq_s32(
        vreinterpretq_s32_u8(a.0),
        vreinterpretq_s32_u8(b.0),
    )))
}

/// `mla.4s`: 4 lanes of wrapping `a + b · c`
#[inline]
#[target_feature(enable = "neon")]
pub(crate) fn mla_32(a: Vec128, b: Vec128, c: Vec128) -> Vec128 {
    Vec128(vreinterpretq_u8_s32(vmlaq_s32(
        vreinterpretq_s32_u8(a.0),
        vreinterpretq_s32_u8(b.0),
        vreinterpretq_s32_u8(c.0),
    )))
}

/// `cmgt.4s`: 4 lanes of signed 32-bit `>`, as an all-ones / all-zeros mask
#[inline]
#[target_feature(enable = "neon")]
pub(crate) fn cmgt_s32(a: Vec128, b: Vec128) -> Vec128 {
    Vec128(vreinterpretq_u8_u32(vcgtq_s32(
        vreinterpretq_s32_u8(a.0),
        vreinterpretq_s32_u8(b.0),
    )))
}

/// `ushl.4s`: 4 lanes of logical shift, each by the *signed* count in its own lane of `counts`
///
/// As with [`ushl_u16`], a negative count shifts right and a count of ±32 or beyond gives zero.
#[inline]
#[target_feature(enable = "neon")]
pub(crate) fn ushl_u32(a: Vec128, counts: Vec128) -> Vec128 {
    Vec128(vreinterpretq_u8_u32(vshlq_u32(
        vreinterpretq_u32_u8(a.0),
        vreinterpretq_s32_u8(counts.0),
    )))
}

// ---------------------------------------------------------------------------------------
// Widening and narrowing
//
// Each of these pairs the `.4s` form with its `2` variant so that one wrapper covers a whole
// 128-bit result. Splitting them would need a 64-bit vector type, which exists only as the
// input or output of the split — so the pairing is what keeps `Vec128` the only vector type.
// ---------------------------------------------------------------------------------------

/// `smull.4s`: the signed 16×16→32 products of the *low* four lanes of `a` and `b`
#[inline]
#[target_feature(enable = "neon")]
pub(crate) fn smull_low_s16(a: Vec128, b: Vec128) -> Vec128 {
    Vec128(vreinterpretq_u8_s32(vmull_s16(
        vget_low_s16(vreinterpretq_s16_u8(a.0)),
        vget_low_s16(vreinterpretq_s16_u8(b.0)),
    )))
}

/// `smull2.4s`: the signed 16×16→32 products of the *high* four lanes of `a` and `b`
#[inline]
#[target_feature(enable = "neon")]
pub(crate) fn smull_high_s16(a: Vec128, b: Vec128) -> Vec128 {
    Vec128(vreinterpretq_u8_s32(vmull_high_s16(
        vreinterpretq_s16_u8(a.0),
        vreinterpretq_s16_u8(b.0),
    )))
}

/// `sxtl.4s`: the *low* four 16-bit lanes of `a`, sign-extended to 32 bits
#[inline]
#[target_feature(enable = "neon")]
pub(crate) fn sxtl_low_s16(a: Vec128) -> Vec128 {
    Vec128(vreinterpretq_u8_s32(vmovl_s16(vget_low_s16(
        vreinterpretq_s16_u8(a.0),
    ))))
}

/// `sxtl2.4s`: the *high* four 16-bit lanes of `a`, sign-extended to 32 bits
#[inline]
#[target_feature(enable = "neon")]
pub(crate) fn sxtl_high_s16(a: Vec128) -> Vec128 {
    Vec128(vreinterpretq_u8_s32(vmovl_high_s16(vreinterpretq_s16_u8(
        a.0,
    ))))
}

/// `xtn.4h` + `xtn2.8h`: the low 16 bits of each 32-bit lane of `a` then of `b`, in order
///
/// Truncating, not saturating, so the signedness of the lanes does not arise.
#[inline]
#[target_feature(enable = "neon")]
pub(crate) fn xtn_pair_32(a: Vec128, b: Vec128) -> Vec128 {
    Vec128(vreinterpretq_u8_s16(vmovn_high_s32(
        vmovn_s32(vreinterpretq_s32_u8(a.0)),
        vreinterpretq_s32_u8(b.0),
    )))
}

/// `shrn.4h #16` + `shrn2.8h #16`: the *high* 16 bits of each 32-bit lane of `a` then of `b`
///
/// The shift-and-narrow discards exactly the bits the shift brought in, so whether the shift is
/// arithmetic or logical makes no difference to the result: each output lane is bits 16..32 of
/// its input lane. The count is fixed at 16 because that is the only one the backend uses — a
/// Montgomery reduction with R = 2^16.
#[inline]
#[target_feature(enable = "neon")]
pub(crate) fn shrn16_pair_s32(a: Vec128, b: Vec128) -> Vec128 {
    Vec128(vreinterpretq_u8_s16(vshrn_high_n_s32::<16>(
        vshrn_n_s32::<16>(vreinterpretq_s32_u8(a.0)),
        vreinterpretq_s32_u8(b.0),
    )))
}

// ---------------------------------------------------------------------------------------
// Permutes
// ---------------------------------------------------------------------------------------

/// `trn1.8h`: the even-indexed 16-bit lanes of `a` and `b`, interleaved
#[inline]
#[target_feature(enable = "neon")]
pub(crate) fn trn1_16(a: Vec128, b: Vec128) -> Vec128 {
    Vec128(vreinterpretq_u8_s16(vtrn1q_s16(
        vreinterpretq_s16_u8(a.0),
        vreinterpretq_s16_u8(b.0),
    )))
}

/// `trn2.8h`: the odd-indexed 16-bit lanes of `a` and `b`, interleaved
#[inline]
#[target_feature(enable = "neon")]
pub(crate) fn trn2_16(a: Vec128, b: Vec128) -> Vec128 {
    Vec128(vreinterpretq_u8_s16(vtrn2q_s16(
        vreinterpretq_s16_u8(a.0),
        vreinterpretq_s16_u8(b.0),
    )))
}

/// `trn1.4s`: the even-indexed 32-bit lanes of `a` and `b`, interleaved
#[inline]
#[target_feature(enable = "neon")]
pub(crate) fn trn1_32(a: Vec128, b: Vec128) -> Vec128 {
    Vec128(vreinterpretq_u8_s32(vtrn1q_s32(
        vreinterpretq_s32_u8(a.0),
        vreinterpretq_s32_u8(b.0),
    )))
}

/// `trn2.4s`: the odd-indexed 32-bit lanes of `a` and `b`, interleaved
#[inline]
#[target_feature(enable = "neon")]
pub(crate) fn trn2_32(a: Vec128, b: Vec128) -> Vec128 {
    Vec128(vreinterpretq_u8_s32(vtrn2q_s32(
        vreinterpretq_s32_u8(a.0),
        vreinterpretq_s32_u8(b.0),
    )))
}

/// `trn1.2d`: the low 64-bit lane of `a`, then that of `b`
#[inline]
#[target_feature(enable = "neon")]
pub(crate) fn trn1_64(a: Vec128, b: Vec128) -> Vec128 {
    Vec128(vreinterpretq_u8_u64(vtrn1q_u64(
        vreinterpretq_u64_u8(a.0),
        vreinterpretq_u64_u8(b.0),
    )))
}

/// `trn2.2d`: the high 64-bit lane of `a`, then that of `b`
#[inline]
#[target_feature(enable = "neon")]
pub(crate) fn trn2_64(a: Vec128, b: Vec128) -> Vec128 {
    Vec128(vreinterpretq_u8_u64(vtrn2q_u64(
        vreinterpretq_u64_u8(a.0),
        vreinterpretq_u64_u8(b.0),
    )))
}

/// `tbl.16b`: byte `i` of the result is byte `idx[i]` of `table`, or zero when `idx[i] ≥ 16`
///
/// Note the difference from x86's `vpshufb`, which indexes within each 128-bit half and zeroes
/// on the *high bit* of the control byte: here the table is the whole register and any index at
/// or above 16 — not merely one with bit 7 set — selects zero.
#[inline]
#[target_feature(enable = "neon")]
pub(crate) fn tbl1_u8(table: Vec128, idx: Vec128) -> Vec128 {
    Vec128(vqtbl1q_u8(table.0, idx.0))
}

// ---------------------------------------------------------------------------------------
// FEAT_SHA3
//
// Compiled only where `build.rs` has confirmed the ARMv8.2 SHA3 extension for the target, which
// is the same condition under which `super::keccak` — their only caller — exists at all.
// ---------------------------------------------------------------------------------------

/// `eor3.16b`: bitwise exclusive or of all three arguments, over all 128 bits
#[inline]
#[cfg(kopis_neon_sha3)]
#[target_feature(enable = "neon,sha3")]
pub(crate) fn eor3(a: Vec128, b: Vec128, c: Vec128) -> Vec128 {
    Vec128(vreinterpretq_u8_u64(veor3q_u64(
        vreinterpretq_u64_u8(a.0),
        vreinterpretq_u64_u8(b.0),
        vreinterpretq_u64_u8(c.0),
    )))
}

/// `bcax.16b`: `a ^ (b & ~c)`, over all 128 bits
///
/// Note which operand is complemented: the *third*. Keccak's χ step is
/// `B[x] ^ (~B[x+1] & B[x+2])`, so it is `bcax(B[x], B[x+2], B[x+1])` with the last two
/// arguments swapped relative to the reading order of the formula.
#[inline]
#[cfg(kopis_neon_sha3)]
#[target_feature(enable = "neon,sha3")]
pub(crate) fn bcax(a: Vec128, b: Vec128, c: Vec128) -> Vec128 {
    Vec128(vreinterpretq_u8_u64(vbcaxq_u64(
        vreinterpretq_u64_u8(a.0),
        vreinterpretq_u64_u8(b.0),
        vreinterpretq_u64_u8(c.0),
    )))
}

/// `rax1.2d`: 2 lanes of `a ^ rotl(b, 1)`, the 64-bit rotate being Keccak's θ mixing step
#[inline]
#[cfg(kopis_neon_sha3)]
#[target_feature(enable = "neon,sha3")]
pub(crate) fn rax1(a: Vec128, b: Vec128) -> Vec128 {
    Vec128(vreinterpretq_u8_u64(vrax1q_u64(
        vreinterpretq_u64_u8(a.0),
        vreinterpretq_u64_u8(b.0),
    )))
}

/// `xar.2d #IMM`: 2 lanes of `rotr(a ^ b, IMM)`, the 64-bit rotate being Keccak's ρ
///
/// A *right* rotation, so a left rotation by `r` — which is how ρ is defined — is this with
/// `IMM = (64 − r) % 64`.
#[inline]
#[cfg(kopis_neon_sha3)]
#[target_feature(enable = "neon,sha3")]
pub(crate) fn xar<const IMM: i32>(a: Vec128, b: Vec128) -> Vec128 {
    Vec128(vreinterpretq_u8_u64(vxarq_u64::<IMM>(
        vreinterpretq_u64_u8(a.0),
        vreinterpretq_u64_u8(b.0),
    )))
}

// ---------------------------------------------------------------------------------------
// Memory
//
// One accessor per element type the backend needs. The 16- and 32-bit ones are indexed in whole
// vectors rather than elements; the byte ones are indexed in bytes, because their callers read
// at offsets that are multiples of a coefficient width or of a 64-bit word rather than of 16.
// Every one is bounds-checked, which is what lets `ntt`, `ser`, `sample` and `keccak` contain no
// `unsafe` and no raw pointers at all.
//
// `NttElem` and the pointwise accumulator are `[i16; 512]` and `[i32; 512]` outright — the two
// residue blocks are the two halves — so these are plain typed loads and stores, with no
// reinterpretation to state.
// ---------------------------------------------------------------------------------------

/// Loads the 8 `i16` at `src[8 * i ..]`
#[inline]
#[target_feature(enable = "neon")]
pub(crate) fn load_i16<const N: usize>(src: &[i16; N], i: usize) -> Vec128 {
    assert!(8 * (i + 1) <= N);
    // SAFETY: the assert puts all 8 elements in bounds; the load is unaligned.
    Vec128(unsafe { vld1q_u8(src.as_ptr().add(8 * i).cast()) })
}

/// Stores 8 `i16` at `dst[8 * i ..]`
#[inline]
#[target_feature(enable = "neon")]
pub(crate) fn store_i16<const N: usize>(dst: &mut [i16; N], i: usize, v: Vec128) {
    assert!(8 * (i + 1) <= N);
    // SAFETY: the assert puts all 8 elements in bounds; the store is unaligned.
    unsafe { vst1q_u8(dst.as_mut_ptr().add(8 * i).cast(), v.0) }
}

/// Loads the 8 `u16` at `src[8 * i ..]`
#[inline]
#[target_feature(enable = "neon")]
pub(crate) fn load_u16<const N: usize>(src: &[u16; N], i: usize) -> Vec128 {
    assert!(8 * (i + 1) <= N);
    // SAFETY: the assert puts all 8 elements in bounds; the load is unaligned.
    Vec128(unsafe { vld1q_u8(src.as_ptr().add(8 * i).cast()) })
}

/// Stores 8 `u16` at `dst[8 * i ..]`
#[inline]
#[target_feature(enable = "neon")]
pub(crate) fn store_u16<const N: usize>(dst: &mut [u16; N], i: usize, v: Vec128) {
    assert!(8 * (i + 1) <= N);
    // SAFETY: the assert puts all 8 elements in bounds; the store is unaligned.
    unsafe { vst1q_u8(dst.as_mut_ptr().add(8 * i).cast(), v.0) }
}

/// Loads the 4 `i32` at `src[4 * i ..]`
#[inline]
#[target_feature(enable = "neon")]
pub(crate) fn load_i32<const N: usize>(src: &[i32; N], i: usize) -> Vec128 {
    assert!(4 * (i + 1) <= N);
    // SAFETY: the assert puts all 4 elements in bounds; the load is unaligned.
    Vec128(unsafe { vld1q_u8(src.as_ptr().add(4 * i).cast()) })
}

/// Stores 4 `i32` at `dst[4 * i ..]`
#[inline]
#[target_feature(enable = "neon")]
pub(crate) fn store_i32<const N: usize>(dst: &mut [i32; N], i: usize, v: Vec128) {
    assert!(4 * (i + 1) <= N);
    // SAFETY: the assert puts all 4 elements in bounds; the store is unaligned.
    unsafe { vst1q_u8(dst.as_mut_ptr().add(4 * i).cast(), v.0) }
}

/// Loads the 16 bytes at `src[offset ..]`
///
/// Byte-indexed rather than vector-indexed: [`super::keccak`] reads the sponge state a 64-bit
/// word at a time, so its offsets are multiples of 8 and not of 16, and [`super::ser`] reads
/// groups at multiples of the coefficient width. Slice-typed rather than array-typed because
/// `ser`'s input has a length that depends on that width; the fixed-size buffers coerce.
#[inline]
#[target_feature(enable = "neon")]
pub(crate) fn load_u8x16(src: &[u8], offset: usize) -> Vec128 {
    assert!(offset + 16 <= src.len());
    // SAFETY: the assert puts all 16 bytes in bounds; the load is unaligned.
    Vec128(unsafe { vld1q_u8(src.as_ptr().add(offset)) })
}

/// Stores 16 bytes at `dst[offset ..]`
///
/// Only [`super::keccak`] writes bytes through a vector, so this exists on the same condition it
/// does; everything else stores whole `u16` or `i32` vectors.
#[inline]
#[cfg(kopis_neon_sha3)]
#[target_feature(enable = "neon")]
pub(crate) fn store_u8x16(dst: &mut [u8], offset: usize, v: Vec128) {
    assert!(offset + 16 <= dst.len());
    // SAFETY: the assert puts all 16 bytes in bounds; the store is unaligned.
    unsafe { vst1q_u8(dst.as_mut_ptr().add(offset), v.0) }
}
