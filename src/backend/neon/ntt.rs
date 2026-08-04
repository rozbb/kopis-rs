//! NEON negacyclic NTT over two 16-bit primes, combined by the CRT.
//!
//! The scheme, its constants and its correctness argument are shared with the other backends and
//! live in [`crate::backend::crt`]; this file is the AArch64 half — the intrinsics and the
//! per-lane ψ tables, whose grouping depends on how many coefficients fit a vector.
//!
//! # Why two primes here too
//!
//! AArch64 does have a 32-bit high-multiply, so the missing-instruction argument that motivates
//! this on AVX2 does not apply in the same form. The win comes from what a 32-bit Montgomery
//! multiply actually costs here: over a single 26-bit prime it needs widening `vmull_s32` /
//! `vmull_high_s32`, which cover two lanes per instruction, so a butterfly runs about two
//! multiply-class instructions per coefficient. Over two 16-bit primes, `sqdmulh.8h` and
//! `mul.8h` cover eight lanes and [`mont_mul`] is three multiplies plus a halving subtract for
//! eight coefficients — about one instruction per coefficient once both primes are counted.
//! Pulling the other way, an `i16` lane holds only 3.05·q₂ against the 42.7·p an `i32` lane
//! holds for the 26-bit prime, so reductions go from two Barrett passes per transform to six.
//!
//! # Layout
//!
//! 256 `i16` are 32 vectors of 8. The first five levels (`len` ≥ 8) pair whole vectors. The
//! last three live inside a vector, so each group of 8 vectors is transposed as an 8×8 matrix:
//! lane `m` of transposed group `g` then owns the whole 8-coefficient block `8g + m`, and the
//! remaining three levels become vertical butterflies with a per-lane ψ. Then we transpose
//! back. Four groups cover the block, and a group needs only 8 of AArch64's 32 vector
//! registers, so it stays in registers across all three levels.
//!
//! Reductions, stated by level number: forward, a Barrett pass after levels 3 and 6 plus one
//! at the end (runs of 3, 3, 2, which the crude 0.75q-per-level budget in
//! [`crate::backend::crt`] covers); inverse, after levels 2, 4 and 6. Note this forward
//! schedule does *not* match AVX2's, which re-centers after levels 3 and 7 and rests on a
//! sharper, table-dependent bound — growth bounds do not transfer between the two backends.

// Explicit `for i in 0..N` index loops, as in the rest of the crate.
#![allow(clippy::needless_range_loop)]

use core::arch::aarch64::*;

use crate::backend::crt::{
    self, BARRETT_SH, CRT_Q, CRT_Q_HALF, CRT_Q1_INV_MONT, Q1, Q1_INV, Q2, Q2_INV, ZETAS_Q1,
    ZETAS_Q2,
};
use crate::consts::RING_DEG;

/// Vectors per 256-coefficient residue block
const VECS: usize = RING_DEG / 8;

/// A 16-byte-aligned per-lane ψ table for the transposed levels, with its q⁻¹-scaled twin.
/// Group `g` occupies entries `8g..8g + 8`; lane `m` of that group serves one coefficient block.
#[repr(align(16))]
struct Tbl<const N: usize> {
    z: [i16; N],
    zq: [i16; N],
}

/// Builds one per-lane ψ table.
///
/// Entry `8g + m` is `zetas[base + g_hi·q_stride + g_lo·h_stride + m·m_stride]`, where
/// `g = g_hi · h_count + g_lo` splits the group index into "which group of 8 vectors" and
/// "which butterfly pair within the level". `neg` produces the negated ψ the inverse
/// transform's Gentleman-Sande butterfly wants.
// The strides genuinely are six independent parameters; bundling them in a struct would only
// move the same list one level down, and this is a `const fn` evaluated at compile time.
#[allow(clippy::too_many_arguments)]
const fn lane_tbl<const N: usize>(
    zetas: &[i16; 256],
    qinv: i16,
    base: isize,
    q_stride: isize,
    h_stride: isize,
    m_stride: isize,
    h_count: usize,
    neg: bool,
) -> Tbl<N> {
    let mut z = [0i16; N];
    let mut zq = [0i16; N];
    let mut g = 0;
    while g * 8 < N {
        let g_hi = (g / h_count) as isize;
        let g_lo = (g % h_count) as isize;
        let mut m = 0;
        while m < 8 {
            let idx = base + g_hi * q_stride + g_lo * h_stride + (m as isize) * m_stride;
            let value = zetas[idx as usize];
            let value = if neg { -value } else { value };
            z[g * 8 + m] = value;
            zq[g * 8 + m] = value.wrapping_mul(qinv);
            m += 1;
        }
        g += 1;
    }
    Tbl { z, zq }
}

// Forward transform, transposed levels. Group `g` covers vectors 8g..8g+8, i.e. coefficients
// 64g..64g+64, so lane `m` of the transposed group holds coefficient block `8g + m`:
//
//  * level len=4: one block of 8 per lane,   ψ index 32 + (8g + m)
//  * level len=2: two blocks of 4 per lane,  ψ index 64 + 2(8g + m) + h, h ∈ {0,1}
//  * level len=1: four blocks of 2 per lane, ψ index 128 + 4(8g + m) + r, r ∈ {0..3}
//
// which are exactly the ψ entries the serial transform's `k` counter reaches at those points.
static FWD4_Q1: Tbl<32> = lane_tbl(&ZETAS_Q1, Q1_INV, 32, 8, 0, 1, 1, false);
static FWD2_Q1: Tbl<64> = lane_tbl(&ZETAS_Q1, Q1_INV, 64, 16, 1, 2, 2, false);
static FWD1_Q1: Tbl<128> = lane_tbl(&ZETAS_Q1, Q1_INV, 128, 32, 1, 4, 4, false);

// Inverse transform, transposed levels. The Gentleman-Sande pass walks the ψ table downwards:
// len=1 consumes 255..128, len=2 consumes 127..64 and len=4 consumes 63..32, each in reverse
// block order. All entries are negated, as the inverse butterfly multiplies by -ψ.
static INV1_Q1: Tbl<128> = lane_tbl(&ZETAS_Q1, Q1_INV, 255, -32, -1, -4, 4, true);
static INV2_Q1: Tbl<64> = lane_tbl(&ZETAS_Q1, Q1_INV, 127, -16, -1, -2, 2, true);
static INV4_Q1: Tbl<32> = lane_tbl(&ZETAS_Q1, Q1_INV, 63, -8, 0, -1, 1, true);

static FWD4_Q2: Tbl<32> = lane_tbl(&ZETAS_Q2, Q2_INV, 32, 8, 0, 1, 1, false);
static FWD2_Q2: Tbl<64> = lane_tbl(&ZETAS_Q2, Q2_INV, 64, 16, 1, 2, 2, false);
static FWD1_Q2: Tbl<128> = lane_tbl(&ZETAS_Q2, Q2_INV, 128, 32, 1, 4, 4, false);

static INV1_Q2: Tbl<128> = lane_tbl(&ZETAS_Q2, Q2_INV, 255, -32, -1, -4, 4, true);
static INV2_Q2: Tbl<64> = lane_tbl(&ZETAS_Q2, Q2_INV, 127, -16, -1, -2, 2, true);
static INV4_Q2: Tbl<32> = lane_tbl(&ZETAS_Q2, Q2_INV, 63, -8, 0, -1, 1, true);

/// The per-lane ψ tables for one prime. Unlike everything in [`crate::backend::crt`], these are
/// specific to this backend: their grouping is by NEON's 8 `i16` lanes.
struct LaneTables {
    fwd4: &'static Tbl<32>,
    fwd2: &'static Tbl<64>,
    fwd1: &'static Tbl<128>,
    inv1: &'static Tbl<128>,
    inv2: &'static Tbl<64>,
    inv4: &'static Tbl<32>,
}

static L1: LaneTables = LaneTables {
    fwd4: &FWD4_Q1,
    fwd2: &FWD2_Q1,
    fwd1: &FWD1_Q1,
    inv1: &INV1_Q1,
    inv2: &INV2_Q1,
    inv4: &INV4_Q1,
};

static L2: LaneTables = LaneTables {
    fwd4: &FWD4_Q2,
    fwd2: &FWD2_Q2,
    fwd1: &FWD1_Q2,
    inv1: &INV1_Q2,
    inv2: &INV2_Q2,
    inv4: &INV4_Q2,
};

/// This backend's tables for prime `SECOND`, selected by const generic for the same reason
/// [`crate::backend::crt::q`] and its siblings are: so each monomorphization folds the addresses in.
const fn lanes<const SECOND: bool>() -> &'static LaneTables {
    if SECOND { &L2 } else { &L1 }
}

// ---------------------------------------------------------------------------------------
// Lane primitives
// ---------------------------------------------------------------------------------------

/// Loads vector `i` (coefficients `8i..8i+8`) of a 256-`i16` block
///
/// # Safety
///
/// `ptr` must be valid for reads of at least `8 * (i + 1)` `i16`s.
#[inline]
#[target_feature(enable = "neon")]
unsafe fn ld(ptr: *const i16, i: usize) -> int16x8_t {
    // SAFETY: guaranteed by this function's contract.
    unsafe { vld1q_s16(ptr.add(8 * i)) }
}

/// Stores vector `i` (coefficients `8i..8i+8`) of a 256-`i16` block
///
/// # Safety
///
/// `ptr` must be valid for writes of at least `8 * (i + 1)` `i16`s.
#[inline]
#[target_feature(enable = "neon")]
unsafe fn st(ptr: *mut i16, i: usize, v: int16x8_t) {
    // SAFETY: guaranteed by this function's contract.
    unsafe { vst1q_s16(ptr.add(8 * i), v) }
}

/// Loads group `g` of a per-lane ψ table, as `(ψ, ψ·q⁻¹)`
///
/// # Safety
///
/// `8g + 8` must be within the table.
#[inline]
#[target_feature(enable = "neon")]
unsafe fn ld_tbl<const N: usize>(table: &Tbl<N>, g: usize) -> (int16x8_t, int16x8_t) {
    // SAFETY: guaranteed by this function's contract.
    unsafe {
        (
            vld1q_s16(table.z.as_ptr().add(8 * g)),
            vld1q_s16(table.zq.as_ptr().add(8 * g)),
        )
    }
}

/// The high half of `a · b`, for 8 lanes.
///
/// AArch64 has no plain 16-bit high-multiply; `sqdmulh` returns the *doubled* high half, so
/// shifting the doubling back out gives it. `sqdmulh` saturates only when both operands are
/// −2^15, which no ψ, Barrett multiplier or modulus here ever is.
#[inline]
#[target_feature(enable = "neon")]
fn mulhi(a: int16x8_t, b: int16x8_t) -> int16x8_t {
    vshrq_n_s16::<1>(vqdmulhq_s16(a, b))
}

/// Signed Montgomery multiply on 8 lanes: `a · ψ · 2⁻¹⁶ mod q`, centered.
///
/// `zq` is `ψ·q⁻¹ mod 2^16`, so `t = a·zq` is the Montgomery quotient outright, and `t·q`
/// agrees with `a·ψ` in its low 16 bits by construction. Rather than shift each `sqdmulh`
/// result down separately, subtract them doubled and halve once: writing `a·ψ = 2¹⁶p + r` and
/// `t·q = 2¹⁶k + r` with the same low half `r`, each `sqdmulh` yields `2p + b` and `2k + b` for
/// the *same* carry bit `b` — it depends only on `r` — so `vhsub` gives `p − k` exactly.
#[inline]
#[target_feature(enable = "neon")]
fn mont_mul(a: int16x8_t, z: int16x8_t, zq: int16x8_t, q: int16x8_t) -> int16x8_t {
    let t = vmulq_s16(a, zq);
    vhsubq_s16(vqdmulhq_s16(a, z), vqdmulhq_s16(t, q))
}

/// Centered Barrett reduction of 8 lanes: `r ≡ x (mod q)` with `|r| ≤ q/2`.
///
/// `t ≈ round(x/q)` is formed as `(hi(x·M) + 2^(SH-1)) >> SH`; the rounding addend is what
/// makes the result centered rather than merely bounded by q.
#[inline]
#[target_feature(enable = "neon")]
fn barrett(x: int16x8_t, m: int16x8_t, round: int16x8_t, q: int16x8_t) -> int16x8_t {
    let t = vshrq_n_s16::<BARRETT_SH>(vaddq_s16(mulhi(x, m), round));
    vsubq_s16(x, vmulq_s16(t, q))
}

/// One Cooley-Tukey butterfly pair: `(lo, hi) ← (lo + ψ·hi, lo − ψ·hi)`
#[inline]
#[target_feature(enable = "neon")]
fn ct_butterfly(lo: &mut int16x8_t, hi: &mut int16x8_t, z: int16x8_t, zq: int16x8_t, q: int16x8_t) {
    let t = mont_mul(*hi, z, zq, q);
    *hi = vsubq_s16(*lo, t);
    *lo = vaddq_s16(*lo, t);
}

/// One Gentleman-Sande butterfly pair: `(lo, hi) ← (lo + hi, −ψ·(lo − hi))`. The tables and
/// broadcasts feeding `z` already carry the negation.
#[inline]
#[target_feature(enable = "neon")]
fn gs_butterfly(lo: &mut int16x8_t, hi: &mut int16x8_t, z: int16x8_t, zq: int16x8_t, q: int16x8_t) {
    let diff = vsubq_s16(*lo, *hi);
    *lo = vaddq_s16(*lo, *hi);
    *hi = mont_mul(diff, z, zq, q);
}

/// Barrett-reduces a whole 256-coefficient block
///
/// # Safety
///
/// `ptr` must be valid for reads and writes of 256 `i16`s.
#[inline]
#[target_feature(enable = "neon")]
unsafe fn barrett_block(ptr: *mut i16, m: int16x8_t, round: int16x8_t, q: int16x8_t) {
    for i in 0..VECS {
        // SAFETY: `i < VECS` indexes within the 256-coefficient block.
        unsafe { st(ptr, i, barrett(ld(ptr, i), m, round, q)) };
    }
}

/// Transposes 8 vectors as an 8×8 `i16` matrix, in place.
///
/// Three `trn` stages, at element strides 1, 2 and 4 — the last two by viewing the vector as
/// `i32` and `i64` lanes. After this, `v[k]` lane `m` holds what was `v[m]` lane `k`. Applied
/// twice it is the identity, which is how the transform gets back to coefficient order.
#[inline]
#[target_feature(enable = "neon")]
fn transpose8(v: &mut [int16x8_t; 8]) {
    let b0 = vreinterpretq_s32_s16(vtrn1q_s16(v[0], v[1]));
    let b1 = vreinterpretq_s32_s16(vtrn2q_s16(v[0], v[1]));
    let b2 = vreinterpretq_s32_s16(vtrn1q_s16(v[2], v[3]));
    let b3 = vreinterpretq_s32_s16(vtrn2q_s16(v[2], v[3]));
    let b4 = vreinterpretq_s32_s16(vtrn1q_s16(v[4], v[5]));
    let b5 = vreinterpretq_s32_s16(vtrn2q_s16(v[4], v[5]));
    let b6 = vreinterpretq_s32_s16(vtrn1q_s16(v[6], v[7]));
    let b7 = vreinterpretq_s32_s16(vtrn2q_s16(v[6], v[7]));

    let c0 = vreinterpretq_s64_s32(vtrn1q_s32(b0, b2));
    let c2 = vreinterpretq_s64_s32(vtrn2q_s32(b0, b2));
    let c1 = vreinterpretq_s64_s32(vtrn1q_s32(b1, b3));
    let c3 = vreinterpretq_s64_s32(vtrn2q_s32(b1, b3));
    let c4 = vreinterpretq_s64_s32(vtrn1q_s32(b4, b6));
    let c6 = vreinterpretq_s64_s32(vtrn2q_s32(b4, b6));
    let c5 = vreinterpretq_s64_s32(vtrn1q_s32(b5, b7));
    let c7 = vreinterpretq_s64_s32(vtrn2q_s32(b5, b7));

    v[0] = vreinterpretq_s16_s64(vtrn1q_s64(c0, c4));
    v[4] = vreinterpretq_s16_s64(vtrn2q_s64(c0, c4));
    v[1] = vreinterpretq_s16_s64(vtrn1q_s64(c1, c5));
    v[5] = vreinterpretq_s16_s64(vtrn2q_s64(c1, c5));
    v[2] = vreinterpretq_s16_s64(vtrn1q_s64(c2, c6));
    v[6] = vreinterpretq_s16_s64(vtrn2q_s64(c2, c6));
    v[3] = vreinterpretq_s16_s64(vtrn1q_s64(c3, c7));
    v[7] = vreinterpretq_s16_s64(vtrn2q_s64(c3, c7));
}

/// Loads the 8 vectors of group `g` and transposes them, so lane `m` owns coefficient block
/// `8g + m`
///
/// # Safety
///
/// `ptr` must be valid for reads of 256 `i16`s and `g < 4`.
#[inline]
#[target_feature(enable = "neon")]
unsafe fn load_group(ptr: *const i16, g: usize) -> [int16x8_t; 8] {
    // SAFETY: guaranteed by this function's contract; `8g + 7 < 32`.
    let mut v = unsafe {
        [
            ld(ptr, 8 * g),
            ld(ptr, 8 * g + 1),
            ld(ptr, 8 * g + 2),
            ld(ptr, 8 * g + 3),
            ld(ptr, 8 * g + 4),
            ld(ptr, 8 * g + 5),
            ld(ptr, 8 * g + 6),
            ld(ptr, 8 * g + 7),
        ]
    };
    transpose8(&mut v);
    v
}

/// Transposes group `g` back to coefficient order and stores it
///
/// # Safety
///
/// `ptr` must be valid for writes of 256 `i16`s and `g < 4`.
#[inline]
#[target_feature(enable = "neon")]
unsafe fn store_group(ptr: *mut i16, g: usize, v: &mut [int16x8_t; 8]) {
    transpose8(v);
    for j in 0..8 {
        // SAFETY: guaranteed by this function's contract; `8g + 7 < 32`.
        unsafe { st(ptr, 8 * g + j, v[j]) };
    }
}

// ---------------------------------------------------------------------------------------
// The transforms
// ---------------------------------------------------------------------------------------

/// In-place forward negacyclic NTT of one 256-coefficient block, modulo the prime `SECOND`
/// selects.
///
/// # Safety
///
/// Requires NEON. `ptr` must be valid for reads and writes of 256 `i16`s, whose values must be
/// centered residues, `|a| ≤ q/2`.
#[target_feature(enable = "neon")]
unsafe fn ntt_block<const SECOND: bool>(ptr: *mut i16) {
    let t = lanes::<SECOND>();
    let q = vdupq_n_s16(crt::q::<SECOND>());
    let bm = vdupq_n_s16(crt::barrett_m::<SECOND>());
    let round = vdupq_n_s16(1i16 << (BARRETT_SH - 1));

    // Levels with len ≥ 8: both halves of every butterfly are whole vectors, and ψ is constant
    // across a block, so it is simply broadcast.
    let mut k = 0usize;
    let mut half = 16usize; // len/8, the block half-width in vectors
    let mut level = 0usize;
    while half >= 1 {
        let mut start = 0usize;
        while start < VECS {
            k += 1;
            let z = vdupq_n_s16(crt::zeta::<SECOND>(k));
            let zq = vdupq_n_s16(crt::zeta_q::<SECOND>(k));
            let mut i = start;
            while i < start + half {
                // SAFETY: `i + half < VECS` because `start + 2*half ≤ VECS`.
                unsafe {
                    let mut lo = ld(ptr, i);
                    let mut hi = ld(ptr, i + half);
                    ct_butterfly(&mut lo, &mut hi, z, zq, q);
                    st(ptr, i, lo);
                    st(ptr, i + half, hi);
                }
                i += 1;
            }
            start += 2 * half;
        }
        // Three levels of Cooley-Tukey growth reach 2.75q; re-center before a fourth.
        if level == 2 {
            // SAFETY: `ptr` covers the whole block.
            unsafe { barrett_block(ptr, bm, round, q) };
        }
        half /= 2;
        level += 1;
    }

    // Levels with len < 8: transpose each group of 8 so every lane owns a whole coefficient
    // block, then three more vertical levels with per-lane ψ.
    for g in 0..4 {
        // SAFETY: `g < 4`, and `ptr` covers all 256 coefficients.
        let mut v = unsafe { load_group(ptr, g) };

        // len = 4: pair k with k+4, one ψ per lane
        // SAFETY: group index `g < 4` is in range for a 4-group table.
        let (z, zq) = unsafe { ld_tbl(t.fwd4, g) };
        for i in 0..4 {
            let (mut lo, mut hi) = (v[i], v[i + 4]);
            ct_butterfly(&mut lo, &mut hi, z, zq, q);
            v[i] = lo;
            v[i + 4] = hi;
        }

        // Six levels done since the start; re-center again before the last two.
        for slot in v.iter_mut() {
            *slot = barrett(*slot, bm, round, q);
        }

        // len = 2: pair k with k+2; the low pair and the high pair are different blocks and so
        // take different ψ
        for h in 0..2 {
            // SAFETY: `2g + h < 8` is in range for an 8-group table.
            let (z, zq) = unsafe { ld_tbl(t.fwd2, 2 * g + h) };
            for i in 0..2 {
                let base = 4 * h + i;
                let (mut lo, mut hi) = (v[base], v[base + 2]);
                ct_butterfly(&mut lo, &mut hi, z, zq, q);
                v[base] = lo;
                v[base + 2] = hi;
            }
        }

        // len = 1: adjacent pairs, four distinct blocks per lane
        for r in 0..4 {
            // SAFETY: `4g + r < 16` is in range for a 16-group table.
            let (z, zq) = unsafe { ld_tbl(t.fwd1, 4 * g + r) };
            let (mut lo, mut hi) = (v[2 * r], v[2 * r + 1]);
            ct_butterfly(&mut lo, &mut hi, z, zq, q);
            v[2 * r] = lo;
            v[2 * r + 1] = hi;
        }

        // SAFETY: as for `load_group`.
        unsafe { store_group(ptr, g, &mut v) };
    }

    // SAFETY: `ptr` covers the whole block. Leaves every coefficient centered, |a| ≤ q/2.
    unsafe { barrett_block(ptr, bm, round, q) };
}

/// In-place inverse negacyclic NTT of one 256-coefficient block, including the final scaling
/// that undoes both the 1/256 and the Montgomery factor left by the pointwise step.
///
/// # Safety
///
/// Requires NEON. `ptr` must be valid for reads and writes of 256 `i16`s, whose values must
/// satisfy `|a| < q`.
#[target_feature(enable = "neon")]
unsafe fn invntt_block<const SECOND: bool>(ptr: *mut i16) {
    let t = lanes::<SECOND>();
    let q = vdupq_n_s16(crt::q::<SECOND>());
    let bm = vdupq_n_s16(crt::barrett_m::<SECOND>());
    let round = vdupq_n_s16(1i16 << (BARRETT_SH - 1));

    // Levels with len < 8, in transposed form: len = 1, then 2, then 4.
    for g in 0..4 {
        // SAFETY: `g < 4`, and `ptr` covers all 256 coefficients.
        let mut v = unsafe { load_group(ptr, g) };

        for r in 0..4 {
            // SAFETY: `4g + r < 16` is in range for a 16-group table.
            let (z, zq) = unsafe { ld_tbl(t.inv1, 4 * g + r) };
            let (mut lo, mut hi) = (v[2 * r], v[2 * r + 1]);
            gs_butterfly(&mut lo, &mut hi, z, zq, q);
            v[2 * r] = lo;
            v[2 * r + 1] = hi;
        }

        for h in 0..2 {
            // SAFETY: `2g + h < 8` is in range for an 8-group table.
            let (z, zq) = unsafe { ld_tbl(t.inv2, 2 * g + h) };
            for i in 0..2 {
                let base = 4 * h + i;
                let (mut lo, mut hi) = (v[base], v[base + 2]);
                gs_butterfly(&mut lo, &mut hi, z, zq, q);
                v[base] = lo;
                v[base + 2] = hi;
            }
        }

        // The Gentleman-Sande sum path doubles per level; re-center every two levels so that
        // both `lo + hi` and `lo - hi` keep fitting a lane.
        for slot in v.iter_mut() {
            *slot = barrett(*slot, bm, round, q);
        }

        // SAFETY: group index `g < 4` is in range for a 4-group table.
        let (z, zq) = unsafe { ld_tbl(t.inv4, g) };
        for i in 0..4 {
            let (mut lo, mut hi) = (v[i], v[i + 4]);
            gs_butterfly(&mut lo, &mut hi, z, zq, q);
            v[i] = lo;
            v[i + 4] = hi;
        }

        // SAFETY: as for `load_group`.
        unsafe { store_group(ptr, g, &mut v) };
    }

    // Levels with len ≥ 8. `k` continues downward from where the transposed levels stopped:
    // they consumed 128 + 64 + 32 = 224 of the 256 ψ entries.
    let mut k = 32usize;
    let mut half = 1usize;
    let mut level = 3usize;
    while half < VECS {
        let mut start = 0usize;
        while start < VECS {
            k -= 1;
            // The table entries are centered, so |ψ| ≤ q/2 and the negation cannot overflow.
            let neg_zeta = crt::zeta::<SECOND>(k).wrapping_neg();
            let z = vdupq_n_s16(neg_zeta);
            let zq = vdupq_n_s16(neg_zeta.wrapping_mul(crt::qinv::<SECOND>()));
            let mut i = start;
            while i < start + half {
                // SAFETY: `i + half < VECS` because `start + 2*half ≤ VECS`.
                unsafe {
                    let mut lo = ld(ptr, i);
                    let mut hi = ld(ptr, i + half);
                    gs_butterfly(&mut lo, &mut hi, z, zq, q);
                    st(ptr, i, lo);
                    st(ptr, i + half, hi);
                }
                i += 1;
            }
            start += 2 * half;
        }
        if level == 3 || level == 5 {
            // SAFETY: `ptr` covers the whole block.
            unsafe { barrett_block(ptr, bm, round, q) };
        }
        half *= 2;
        level += 1;
    }

    // One final Montgomery multiply undoes both the 1/256 and the Montgomery factor.
    let scale = vdupq_n_s16(crt::invntt_scale::<SECOND>());
    let scale_q = vdupq_n_s16(crt::invntt_scale::<SECOND>().wrapping_mul(crt::qinv::<SECOND>()));
    for i in 0..VECS {
        // SAFETY: `i < VECS`.
        unsafe { st(ptr, i, mont_mul(ld(ptr, i), scale, scale_q, q)) };
    }
}

// ---------------------------------------------------------------------------------------
// Entry points, matching the portable ones they stand in for
// ---------------------------------------------------------------------------------------

/// Reduces a ring element into one prime's centered residue block and transforms it.
///
/// `REDUCE` says whether the input needs reducing at all: uniform coefficients go up to 2^13,
/// which exceeds q₁, whereas CBD secrets satisfy |·| ≤ μ/2 ≤ 5 and are already centered
/// residues for both primes.
///
/// # Safety
///
/// Requires NEON. `ptr` must be valid for writes of 256 `i16`s.
#[inline]
#[target_feature(enable = "neon")]
unsafe fn split_and_transform<const SECOND: bool, const REDUCE: bool>(
    elem: &[u16; RING_DEG],
    ptr: *mut i16,
) {
    let q = vdupq_n_s16(crt::q::<SECOND>());
    let bm = vdupq_n_s16(crt::barrett_m::<SECOND>());
    let round = vdupq_n_s16(1i16 << (BARRETT_SH - 1));
    for i in 0..VECS {
        // SAFETY: `i < VECS` is in range for both the 256-`u16` source and the block.
        // Coefficients below 2^13 fit an `i16` lane, so the Barrett reduction is in range;
        // secret coefficients need none, and the `i16` reinterpretation of the load is their
        // sign extension.
        unsafe {
            let x = vld1q_s16(elem.as_ptr().cast::<i16>().add(8 * i));
            let x = if REDUCE { barrett(x, bm, round, q) } else { x };
            st(ptr, i, x);
        }
    }
    // SAFETY: the block is 256 `i16` and now holds centered residues.
    unsafe { ntt_block::<SECOND>(ptr) };
}

/// Splits a ring element into both residue blocks and transforms each
///
/// # Safety
///
/// Requires NEON.
#[inline]
#[target_feature(enable = "neon")]
unsafe fn from_ring_elem<const REDUCE: bool>(elem: &[u16; RING_DEG]) -> [i16; 2 * RING_DEG] {
    let mut out = [0i16; 2 * RING_DEG];
    let base = out.as_mut_ptr();
    // SAFETY: `out` is 512 `i16`, so the q₂ block starts at `i16` offset 256 and both blocks
    // are 256 `i16` long.
    unsafe {
        split_and_transform::<false, REDUCE>(elem, base);
        split_and_transform::<true, REDUCE>(elem, base.add(RING_DEG));
    }
    out
}

/// Forward-transforms a ring element with plain coefficients in `[0, 2^13)`
///
/// # Safety
///
/// Requires NEON.
#[target_feature(enable = "neon")]
pub(crate) fn from_uniform(elem: &[u16; RING_DEG]) -> [i16; 2 * RING_DEG] {
    // SAFETY: the caller guarantees NEON.
    unsafe { from_ring_elem::<true>(elem) }
}

/// Forward-transforms a CBD secret, reading each coefficient as the signed value it encodes
///
/// # Safety
///
/// Requires NEON.
#[target_feature(enable = "neon")]
pub(crate) fn from_secret(elem: &[u16; RING_DEG]) -> [i16; 2 * RING_DEG] {
    // SAFETY: the caller guarantees NEON.
    unsafe { from_ring_elem::<false>(elem) }
}

/// Adds the pointwise product `lhs ∘ rhs` into an unreduced accumulator, per prime.
///
/// The accumulator's 512 `i32` are two blocks of 256, matching the two residue blocks of the
/// operands. Products of centered values are below (q/2 + 1)² and callers
/// accumulate at most 4 (= `MAX_L`) of them, so each lane stays under 1.2·10⁸ — well inside an
/// `i32`, and inside the 2^15·q input range of the Montgomery reduction that consumes it.
///
/// # Safety
///
/// Requires NEON.
#[target_feature(enable = "neon")]
pub(crate) fn pointwise_mul_acc(
    acc: &mut [i32; 2 * RING_DEG],
    lhs: &[i16; 2 * RING_DEG],
    rhs: &[i16; 2 * RING_DEG],
) {
    let acc_base = acc.as_mut_ptr();
    let lhs_base = lhs.as_ptr();
    let rhs_base = rhs.as_ptr();

    for block in 0..2 {
        // SAFETY: the accumulator is 512 `i32` and each operand 512 `i16`, so both blocks are
        // in range for their respective buffers, as is every `i < VECS` within a block.
        unsafe {
            let acc_ptr = acc_base.add(RING_DEG * block);
            let l_ptr = lhs_base.add(RING_DEG * block);
            let r_ptr = rhs_base.add(RING_DEG * block);

            for i in 0..VECS {
                let l = ld(l_ptr, i);
                let r = ld(r_ptr, i);
                // The widening multiplies give the 32-bit products already in coefficient
                // order, so unlike the AVX2 path there is nothing to un-permute.
                let first = vmull_s16(vget_low_s16(l), vget_low_s16(r));
                let second = vmull_high_s16(l, r);

                let a0 = acc_ptr.add(8 * i);
                let a1 = acc_ptr.add(8 * i + 4);
                vst1q_s32(a0, vaddq_s32(vld1q_s32(a0), first));
                vst1q_s32(a1, vaddq_s32(vld1q_s32(a1), second));
            }
        }
    }
}

/// Montgomery-reduces one accumulator block into `i16` lanes, then inverse-transforms it
///
/// # Safety
///
/// Requires NEON. `acc_ptr` must be valid for reads of 256 `i32`s and `ptr` for reads and
/// writes of 256 `i16`s.
#[inline]
#[target_feature(enable = "neon")]
unsafe fn reduce_block<const SECOND: bool>(acc_ptr: *const i32, ptr: *mut i16) {
    let q = vdupq_n_s16(crt::q::<SECOND>());
    let qinv = vdupq_n_s16(crt::qinv::<SECOND>());

    for i in 0..VECS {
        // SAFETY: `i < VECS` covers the 8 `i32` at `8i` and the 8 `i16` of output vector `i`.
        unsafe {
            let a0 = vld1q_s32(acc_ptr.add(8 * i));
            let a1 = vld1q_s32(acc_ptr.add(8 * i + 4));
            // Signed Montgomery reduction of an `i32` with R = 2^16: `vmovn` truncates to the
            // low halves and `vshrn` takes the high ones. As in `mont_mul`, the low halves
            // cancel, so subtracting the high halves is the whole answer.
            let lo = vmovn_high_s32(vmovn_s32(a0), a1);
            let hi = vshrn_high_n_s32::<16>(vshrn_n_s32::<16>(a0), a1);
            let t = vmulq_s16(lo, qinv);
            st(ptr, i, vsubq_s16(hi, mulhi(t, q)));
        }
    }

    // SAFETY: the block now holds residues with |a| < q, as `invntt_block` requires.
    unsafe { invntt_block::<SECOND>(ptr) };
}

/// Montgomery-reduces the accumulator, inverse-transforms both residue blocks, reconstructs the
/// exact integer product by the CRT and packs it into wrapping-`u16` coefficients.
///
/// # Safety
///
/// Requires NEON.
#[target_feature(enable = "neon")]
pub(crate) fn reduce_invntt(acc: &[i32; 2 * RING_DEG]) -> [u16; RING_DEG] {
    let acc_base = acc.as_ptr();
    let mut v = [0i16; 2 * RING_DEG];

    // SAFETY: the accumulator is 512 `i32`, so both of its blocks are in range, as are both
    // halves of the 512-`i16` scratch buffer.
    unsafe {
        reduce_block::<false>(acc_base, v.as_mut_ptr());
        reduce_block::<true>(acc_base.add(RING_DEG), v.as_mut_ptr().add(RING_DEG));
    }

    // CRT reconstruction, by Garner: with a₁ = r₁ mod q₁ and a₂ = r₂ mod q₂ taken in [0, q),
    // the unique x ≡ rᵢ (mod qᵢ) in [0, q₁q₂) is a₁ + q₁·((a₂ − a₁)·q₁⁻¹ mod q₂). Subtracting
    // q₁q₂ above the midpoint centers it; truncating to 16 bits then gives the wrapping-`u16`
    // coefficient, exactly as `to_wrapping_u16` does for the single prime. This is exact
    // because the true product lies in (−q₁q₂/2, q₁q₂/2] — the bound in `crt`'s docs.
    let q1 = vdupq_n_s16(Q1);
    let q2 = vdupq_n_s16(Q2);
    let q1_inv_mont = vdupq_n_s16(CRT_Q1_INV_MONT);
    let q1_inv_mont_q = vdupq_n_s16(CRT_Q1_INV_MONT.wrapping_mul(Q2_INV));
    let q1_wide = vdupq_n_s32(Q1 as i32);
    let crt_q = vdupq_n_s32(CRT_Q);
    let crt_q_half = vdupq_n_s32(CRT_Q_HALF);

    let mut out = [0u16; RING_DEG];
    for i in 0..VECS {
        // SAFETY: `i < VECS` indexes both 256-coefficient residue blocks of the scratch buffer
        // and the 8 `u16` at `out[8i..8i + 8]`.
        unsafe {
            let r1 = ld(v.as_ptr(), i);
            let r2 = ld(v.as_ptr().add(RING_DEG), i);

            // Canonicalize both residues to [0, q) by adding q where negative.
            let a1 = vaddq_s16(r1, vandq_s16(vshrq_n_s16::<15>(r1), q1));
            let a2 = vaddq_s16(r2, vandq_s16(vshrq_n_s16::<15>(r2), q2));

            // t = (a₂ − a₁)·q₁⁻¹ mod q₂, centered, then canonicalized to [0, q₂).
            let t = mont_mul(vsubq_s16(a2, a1), q1_inv_mont, q1_inv_mont_q, q2);
            let t = vaddq_s16(t, vandq_s16(vshrq_n_s16::<15>(t), q2));

            // a₁ + q₁·t needs 32 bits, so widen each half. Both operands are non-negative and
            // below their prime, so the sign-extending widen is the right one.
            let mut wide = [
                vmlaq_s32(
                    vmovl_s16(vget_low_s16(a1)),
                    vmovl_s16(vget_low_s16(t)),
                    q1_wide,
                ),
                vmlaq_s32(vmovl_high_s16(a1), vmovl_high_s16(t), q1_wide),
            ];
            for x in wide.iter_mut() {
                // Center: subtract q₁q₂ above the midpoint.
                let over = vreinterpretq_s32_u32(vcgtq_s32(*x, crt_q_half));
                *x = vsubq_s32(*x, vandq_s32(crt_q, over));
            }

            // `vmovn` truncates each to its low 16 bits, which is the wrapping-`u16` value.
            let packed = vmovn_high_s32(vmovn_s32(wide[0]), wide[1]);
            vst1q_u16(out.as_mut_ptr().add(8 * i), vreinterpretq_u16_s16(packed));
        }
    }
    out
}

#[cfg(test)]
mod test {
    use super::*;

    // The transposed levels are only correct if `transpose8` really does put coefficient block
    // `8g + m` in lane `m` — and if applying it twice gets back to coefficient order.
    #[allow(unsafe_code)]
    #[test]
    fn transpose8_permutes_as_documented() {
        let mut a: [i16; 64] = core::array::from_fn(|i| i as i16);
        let mut probe = [0i16; 64];

        // SAFETY: NEON is baseline on AArch64, and `a` holds exactly 8 vectors of 8.
        unsafe {
            let mut v = load_group(a.as_ptr(), 0);
            for j in 0..8 {
                st(probe.as_mut_ptr(), j, v[j]);
            }
            store_group(a.as_mut_ptr(), 0, &mut v);
        }

        // Vector `k` lane `m` — linear index 8k + m — must hold what was `v[m]` lane `k`.
        for k in 0..8 {
            for m in 0..8 {
                assert_eq!(probe[8 * k + m], (8 * m + k) as i16, "vector {k} lane {m}");
            }
        }
        for i in 0..64 {
            assert_eq!(a[i], i as i16, "transposing twice is the identity");
        }
    }
}
