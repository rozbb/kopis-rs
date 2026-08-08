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

use crate::backend::crt::{
    self, BARRETT_SH, CRT_Q, CRT_Q_HALF, CRT_Q1_INV_MONT, Q1, Q1_INV, Q2, Q2_INV, ZETAS_Q1,
    ZETAS_Q2,
};
use crate::consts::RING_DEG;

use super::intrinsics::{
    Vec128, add_16, add_32, and, cmgt_s32, dup_n_s16, dup_n_s32, load_i16, load_i32, load_u16,
    mla_32, mul_16, shrn16_pair_s32, shsub_s16, smull_high_s16, smull_low_s16, sqdmulh_s16,
    sshr_n_s16, store_i16, store_i32, store_u16, sub_16, sub_32, sxtl_high_s16, sxtl_low_s16,
    trn1_16, trn1_32, trn1_64, trn2_16, trn2_32, trn2_64, xtn_pair_32,
};

/// One prime's 256 centered residues, as 32 vectors of 8 `i16`.
///
/// The transform works in these blocks throughout; the two-blocks-in-one-buffer layout that
/// [`crate::arithmetic::ntt::NttElem`] presents to the rest of the crate is applied only at this
/// module's entry points.
type Block = [i16; RING_DEG];

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

// Unlike everything in [`crate::backend::crt`], these tables are specific to this backend: their
// grouping is by NEON's 8 `i16` lanes. They are reached through the six value-returning
// accessors below rather than through a `&'static Tbl<N>` held in a struct or returned from one:
// a function that returns a reference to a static is one of the things aeneas cannot translate,
// and neither is a struct with a reference field reached by reference.

// ---------------------------------------------------------------------------------------
// Lane primitives
// ---------------------------------------------------------------------------------------

/// Loads group `g` of a per-lane ψ table, as `(ψ, ψ·q⁻¹)`
#[inline]
#[target_feature(enable = "neon")]
fn ld_tbl<const N: usize>(table: &Tbl<N>, g: usize) -> (Vec128, Vec128) {
    (load_i16(&table.z, g), load_i16(&table.zq, g))
}

// One accessor per transposed level, each selecting between the two primes' tables and returning
// the loaded pair *by value*.
//
// The selection has to happen inside a function body rather than at the use site. Written there
// as `let (z, zq) = if SECOND { … } else { … }`, aeneas fails with "Internal error, please file an
// issue" out of `simplify_let_branching` — a `let` bound to a branch, in a position where the
// tuple is then consumed by a following loop. As the tail expression of its own function the
// same branch translates normally. See `lean/NEON_VERIFICATION_PLAN.md`.
//
// Returning the `&'static Tbl<N>` instead and loading at the use site would not work either:
// a function returning a reference to a static is one of the things aeneas cannot translate at
// all. Both constraints together are why these return `(Vec128, Vec128)`.
//
// The `if SECOND` still folds away per monomorphization, so this costs nothing.

/// Group `g` of the forward len = 4 table
#[inline]
#[target_feature(enable = "neon")]
fn fwd4<const SECOND: bool>(g: usize) -> (Vec128, Vec128) {
    if SECOND {
        ld_tbl(&FWD4_Q2, g)
    } else {
        ld_tbl(&FWD4_Q1, g)
    }
}

/// Group `h` of the forward len = 2 table
#[inline]
#[target_feature(enable = "neon")]
fn fwd2<const SECOND: bool>(h: usize) -> (Vec128, Vec128) {
    if SECOND {
        ld_tbl(&FWD2_Q2, h)
    } else {
        ld_tbl(&FWD2_Q1, h)
    }
}

/// Group `h` of the forward len = 1 table
#[inline]
#[target_feature(enable = "neon")]
fn fwd1<const SECOND: bool>(h: usize) -> (Vec128, Vec128) {
    if SECOND {
        ld_tbl(&FWD1_Q2, h)
    } else {
        ld_tbl(&FWD1_Q1, h)
    }
}

/// Group `h` of the inverse len = 1 table
#[inline]
#[target_feature(enable = "neon")]
fn inv1<const SECOND: bool>(h: usize) -> (Vec128, Vec128) {
    if SECOND {
        ld_tbl(&INV1_Q2, h)
    } else {
        ld_tbl(&INV1_Q1, h)
    }
}

/// Group `h` of the inverse len = 2 table
#[inline]
#[target_feature(enable = "neon")]
fn inv2<const SECOND: bool>(h: usize) -> (Vec128, Vec128) {
    if SECOND {
        ld_tbl(&INV2_Q2, h)
    } else {
        ld_tbl(&INV2_Q1, h)
    }
}

/// Group `g` of the inverse len = 4 table
#[inline]
#[target_feature(enable = "neon")]
fn inv4<const SECOND: bool>(g: usize) -> (Vec128, Vec128) {
    if SECOND {
        ld_tbl(&INV4_Q2, g)
    } else {
        ld_tbl(&INV4_Q1, g)
    }
}

/// The high half of `a · b`, for 8 lanes.
///
/// AArch64 has no plain 16-bit high-multiply; `sqdmulh` returns the *doubled* high half, so
/// shifting the doubling back out gives it. `sqdmulh` saturates only when both operands are
/// −2^15, which no ψ, Barrett multiplier or modulus here ever is.
#[inline]
#[target_feature(enable = "neon")]
fn mulhi(a: Vec128, b: Vec128) -> Vec128 {
    sshr_n_s16::<1>(sqdmulh_s16(a, b))
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
fn mont_mul(a: Vec128, z: Vec128, zq: Vec128, q: Vec128) -> Vec128 {
    let t = mul_16(a, zq);
    shsub_s16(sqdmulh_s16(a, z), sqdmulh_s16(t, q))
}

/// Centered Barrett reduction of 8 lanes: `r ≡ x (mod q)` with `|r| ≤ q/2`.
///
/// `t ≈ round(x/q)` is formed as `(hi(x·M) + 2^(SH-1)) >> SH`; the rounding addend is what
/// makes the result centered rather than merely bounded by q.
#[inline]
#[target_feature(enable = "neon")]
fn barrett(x: Vec128, m: Vec128, round: Vec128, q: Vec128) -> Vec128 {
    let t = sshr_n_s16::<BARRETT_SH>(add_16(mulhi(x, m), round));
    sub_16(x, mul_16(t, q))
}

/// One Cooley-Tukey butterfly pair: `(lo, hi) ← (lo + ψ·hi, lo − ψ·hi)`
#[inline]
#[target_feature(enable = "neon")]
fn ct_butterfly(lo: &mut Vec128, hi: &mut Vec128, z: Vec128, zq: Vec128, q: Vec128) {
    let t = mont_mul(*hi, z, zq, q);
    *hi = sub_16(*lo, t);
    *lo = add_16(*lo, t);
}

/// One Gentleman-Sande butterfly pair: `(lo, hi) ← (lo + hi, −ψ·(lo − hi))`. The tables and
/// broadcasts feeding `z` already carry the negation.
#[inline]
#[target_feature(enable = "neon")]
fn gs_butterfly(lo: &mut Vec128, hi: &mut Vec128, z: Vec128, zq: Vec128, q: Vec128) {
    let diff = sub_16(*lo, *hi);
    *lo = add_16(*lo, *hi);
    *hi = mont_mul(diff, z, zq, q);
}

/// Barrett-reduces a whole 256-coefficient block
#[inline]
#[target_feature(enable = "neon")]
fn barrett_block(b: &mut Block, m: Vec128, round: Vec128, q: Vec128) {
    for i in 0..VECS {
        store_i16(b, i, barrett(load_i16(b, i), m, round, q));
    }
}

/// Transposes 8 vectors as an 8×8 `i16` matrix, in place.
///
/// Three `trn` stages, at element strides 1, 2 and 4 — the last two by viewing the vector as
/// `i32` and `i64` lanes. After this, `v[k]` lane `m` holds what was `v[m]` lane `k`. Applied
/// twice it is the identity, which is how the transform gets back to coefficient order.
#[inline]
#[target_feature(enable = "neon")]
fn transpose8(v: &mut [Vec128; 8]) {
    let b0 = trn1_16(v[0], v[1]);
    let b1 = trn2_16(v[0], v[1]);
    let b2 = trn1_16(v[2], v[3]);
    let b3 = trn2_16(v[2], v[3]);
    let b4 = trn1_16(v[4], v[5]);
    let b5 = trn2_16(v[4], v[5]);
    let b6 = trn1_16(v[6], v[7]);
    let b7 = trn2_16(v[6], v[7]);

    let c0 = trn1_32(b0, b2);
    let c2 = trn2_32(b0, b2);
    let c1 = trn1_32(b1, b3);
    let c3 = trn2_32(b1, b3);
    let c4 = trn1_32(b4, b6);
    let c6 = trn2_32(b4, b6);
    let c5 = trn1_32(b5, b7);
    let c7 = trn2_32(b5, b7);

    v[0] = trn1_64(c0, c4);
    v[4] = trn2_64(c0, c4);
    v[1] = trn1_64(c1, c5);
    v[5] = trn2_64(c1, c5);
    v[2] = trn1_64(c2, c6);
    v[6] = trn2_64(c2, c6);
    v[3] = trn1_64(c3, c7);
    v[7] = trn2_64(c3, c7);
}

/// Loads the 8 vectors of group `g` and transposes them, so lane `m` owns coefficient block
/// `8g + m`
#[inline]
#[target_feature(enable = "neon")]
fn load_group(b: &Block, g: usize) -> [Vec128; 8] {
    let mut v = [
        load_i16(b, 8 * g),
        load_i16(b, 8 * g + 1),
        load_i16(b, 8 * g + 2),
        load_i16(b, 8 * g + 3),
        load_i16(b, 8 * g + 4),
        load_i16(b, 8 * g + 5),
        load_i16(b, 8 * g + 6),
        load_i16(b, 8 * g + 7),
    ];
    transpose8(&mut v);
    v
}

/// Transposes group `g` back to coefficient order and stores it
#[inline]
#[target_feature(enable = "neon")]
fn store_group(b: &mut Block, g: usize, v: &mut [Vec128; 8]) {
    transpose8(v);
    for j in 0..8 {
        store_i16(b, 8 * g + j, v[j]);
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
/// Requires NEON. The block's values must be centered residues, `|a| ≤ q/2`.
#[target_feature(enable = "neon")]
fn ntt_block<const SECOND: bool>(b: &mut Block) {
    let q = dup_n_s16(crt::q::<SECOND>());
    let bm = dup_n_s16(crt::barrett_m::<SECOND>());
    let round = dup_n_s16(1i16 << (BARRETT_SH - 1));

    // Levels with len ≥ 8: both halves of every butterfly are whole vectors, and ψ is constant
    // across a block, so it is simply broadcast.
    let mut k = 0usize;
    let mut half = 16usize; // len/8, the block half-width in vectors
    let mut level = 0usize;
    while half >= 1 {
        let mut start = 0usize;
        while start < VECS {
            k += 1;
            let z = dup_n_s16(crt::zeta::<SECOND>(k));
            let zq = dup_n_s16(crt::zeta_q::<SECOND>(k));
            let mut i = start;
            while i < start + half {
                let mut lo = load_i16(b, i);
                let mut hi = load_i16(b, i + half);
                ct_butterfly(&mut lo, &mut hi, z, zq, q);
                store_i16(b, i, lo);
                store_i16(b, i + half, hi);
                i += 1;
            }
            start += 2 * half;
        }
        // Three levels of Cooley-Tukey growth reach 2.75q; re-center before a fourth.
        if level == 2 {
            barrett_block(b, bm, round, q);
        }
        half /= 2;
        level += 1;
    }

    // Levels with len < 8: transpose each group of 8 so every lane owns a whole coefficient
    // block, then three more vertical levels with per-lane ψ.
    for g in 0..4 {
        let mut v = load_group(b, g);

        // len = 4: pair k with k+4, one ψ per lane. Group index `g < 4` is in range for a
        // 4-group table.
        let (z, zq) = fwd4::<SECOND>(g);
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
        // take different ψ. `2g + h < 8` is in range for an 8-group table.
        for h in 0..2 {
            let (z, zq) = fwd2::<SECOND>(2 * g + h);
            for i in 0..2 {
                let base = 4 * h + i;
                let (mut lo, mut hi) = (v[base], v[base + 2]);
                ct_butterfly(&mut lo, &mut hi, z, zq, q);
                v[base] = lo;
                v[base + 2] = hi;
            }
        }

        // len = 1: adjacent pairs, four distinct blocks per lane. `4g + r < 16` is in range for
        // a 16-group table.
        for r in 0..4 {
            let (z, zq) = fwd1::<SECOND>(4 * g + r);
            let (mut lo, mut hi) = (v[2 * r], v[2 * r + 1]);
            ct_butterfly(&mut lo, &mut hi, z, zq, q);
            v[2 * r] = lo;
            v[2 * r + 1] = hi;
        }

        store_group(b, g, &mut v);
    }

    // Leaves every coefficient centered, |a| ≤ q/2.
    barrett_block(b, bm, round, q);
}

/// In-place inverse negacyclic NTT of one 256-coefficient block, including the final scaling
/// that undoes both the 1/256 and the Montgomery factor left by the pointwise step.
///
/// # Safety
///
/// Requires NEON. The block's values must satisfy `|a| < q`.
#[target_feature(enable = "neon")]
fn invntt_block<const SECOND: bool>(b: &mut Block) {
    let q = dup_n_s16(crt::q::<SECOND>());
    let bm = dup_n_s16(crt::barrett_m::<SECOND>());
    let round = dup_n_s16(1i16 << (BARRETT_SH - 1));

    // Levels with len < 8, in transposed form: len = 1, then 2, then 4.
    for g in 0..4 {
        let mut v = load_group(b, g);

        // `4g + r < 16` is in range for a 16-group table.
        for r in 0..4 {
            let (z, zq) = inv1::<SECOND>(4 * g + r);
            let (mut lo, mut hi) = (v[2 * r], v[2 * r + 1]);
            gs_butterfly(&mut lo, &mut hi, z, zq, q);
            v[2 * r] = lo;
            v[2 * r + 1] = hi;
        }

        // `2g + h < 8` is in range for an 8-group table.
        for h in 0..2 {
            let (z, zq) = inv2::<SECOND>(2 * g + h);
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

        // Group index `g < 4` is in range for a 4-group table.
        let (z, zq) = inv4::<SECOND>(g);
        for i in 0..4 {
            let (mut lo, mut hi) = (v[i], v[i + 4]);
            gs_butterfly(&mut lo, &mut hi, z, zq, q);
            v[i] = lo;
            v[i + 4] = hi;
        }

        store_group(b, g, &mut v);
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
            let z = dup_n_s16(neg_zeta);
            let zq = dup_n_s16(neg_zeta.wrapping_mul(crt::qinv::<SECOND>()));
            let mut i = start;
            while i < start + half {
                let mut lo = load_i16(b, i);
                let mut hi = load_i16(b, i + half);
                gs_butterfly(&mut lo, &mut hi, z, zq, q);
                store_i16(b, i, lo);
                store_i16(b, i + half, hi);
                i += 1;
            }
            start += 2 * half;
        }
        if level == 3 || level == 5 {
            barrett_block(b, bm, round, q);
        }
        half *= 2;
        level += 1;
    }

    // One final Montgomery multiply undoes both the 1/256 and the Montgomery factor.
    let scale = dup_n_s16(crt::invntt_scale::<SECOND>());
    let scale_q = dup_n_s16(crt::invntt_scale::<SECOND>().wrapping_mul(crt::qinv::<SECOND>()));
    for i in 0..VECS {
        store_i16(b, i, mont_mul(load_i16(b, i), scale, scale_q, q));
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
/// Requires NEON.
#[inline]
#[target_feature(enable = "neon")]
fn split_and_transform<const SECOND: bool, const REDUCE: bool>(
    elem: &[u16; RING_DEG],
    b: &mut Block,
) {
    let q = dup_n_s16(crt::q::<SECOND>());
    let bm = dup_n_s16(crt::barrett_m::<SECOND>());
    let round = dup_n_s16(1i16 << (BARRETT_SH - 1));
    for i in 0..VECS {
        // Coefficients below 2^13 fit an `i16` lane, so the Barrett reduction is in range;
        // secret coefficients need none, and the `i16` reading of the load is their sign
        // extension.
        let x = load_u16(elem, i);
        let x = if REDUCE { barrett(x, bm, round, q) } else { x };
        store_i16(b, i, x);
    }
    // The block is 256 `i16` and now holds centered residues.
    ntt_block::<SECOND>(b);
}

/// Splits a ring element into both residue blocks and transforms each
///
/// The two blocks are written into the halves of one `[i16; 512]`, which is what
/// [`crate::arithmetic::ntt::NttElem`] is: the q₁ block occupies `i16` vectors 0..32 and the q₂
/// block vectors 32..64.
///
/// # Safety
///
/// Requires NEON.
#[inline]
#[target_feature(enable = "neon")]
fn from_ring_elem<const REDUCE: bool>(elem: &[u16; RING_DEG]) -> [i16; 2 * RING_DEG] {
    let mut out = [0i16; 2 * RING_DEG];
    let mut b = [0i16; RING_DEG];

    split_and_transform::<false, REDUCE>(elem, &mut b);
    for i in 0..VECS {
        store_i16(&mut out, i, load_i16(&b, i));
    }

    split_and_transform::<true, REDUCE>(elem, &mut b);
    for i in 0..VECS {
        store_i16(&mut out, VECS + i, load_i16(&b, i));
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
    from_ring_elem::<true>(elem)
}

/// Forward-transforms a CBD secret, reading each coefficient as the signed value it encodes
///
/// # Safety
///
/// Requires NEON.
#[target_feature(enable = "neon")]
pub(crate) fn from_secret(elem: &[u16; RING_DEG]) -> [i16; 2 * RING_DEG] {
    from_ring_elem::<false>(elem)
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
    for block in 0..2 {
        for i in 0..VECS {
            // Vector `VECS * block + i` of the operands read as 512 `i16`, and the two `i32`
            // vectors `2 * VECS * block + 2i` and `+ 1` of the accumulator read as 512 `i32`,
            // are the same 8 coefficients of the same prime.
            let l = load_i16(lhs, VECS * block + i);
            let r = load_i16(rhs, VECS * block + i);
            // The widening multiplies give the 32-bit products already in coefficient order,
            // so unlike the AVX2 path there is nothing to un-permute.
            let first = smull_low_s16(l, r);
            let second = smull_high_s16(l, r);

            let a0 = 2 * VECS * block + 2 * i;
            let a1 = a0 + 1;
            store_i32(acc, a0, add_32(load_i32(acc, a0), first));
            store_i32(acc, a1, add_32(load_i32(acc, a1), second));
        }
    }
}

/// Montgomery-reduces one accumulator block into `i16` lanes, then inverse-transforms it.
///
/// `base` is the accumulator's first `i32` vector for this prime: 0 for q₁, 64 for q₂.
///
/// # Safety
///
/// Requires NEON.
#[inline]
#[target_feature(enable = "neon")]
fn reduce_block<const SECOND: bool>(acc: &[i32; 2 * RING_DEG], base: usize, b: &mut Block) {
    let q = dup_n_s16(crt::q::<SECOND>());
    let qinv = dup_n_s16(crt::qinv::<SECOND>());

    for i in 0..VECS {
        let a0 = load_i32(acc, base + 2 * i);
        let a1 = load_i32(acc, base + 2 * i + 1);
        // Signed Montgomery reduction of an `i32` with R = 2^16: `xtn` truncates to the low
        // halves and `shrn` takes the high ones. As in `mont_mul`, the low halves cancel, so
        // subtracting the high halves is the whole answer.
        let lo = xtn_pair_32(a0, a1);
        let hi = shrn16_pair_s32(a0, a1);
        let t = mul_16(lo, qinv);
        store_i16(b, i, sub_16(hi, mulhi(t, q)));
    }

    // The block now holds residues with |a| < q, as `invntt_block` requires.
    invntt_block::<SECOND>(b);
}

/// Montgomery-reduces the accumulator, inverse-transforms both residue blocks, reconstructs the
/// exact integer product by the CRT and packs it into wrapping-`u16` coefficients.
///
/// # Safety
///
/// Requires NEON.
#[target_feature(enable = "neon")]
pub(crate) fn reduce_invntt(acc: &[i32; 2 * RING_DEG]) -> [u16; RING_DEG] {
    let mut v1 = [0i16; RING_DEG];
    let mut v2 = [0i16; RING_DEG];

    // The accumulator is 512 `i32`, so the q₂ block starts at `i32` vector 64.
    reduce_block::<false>(acc, 0, &mut v1);
    reduce_block::<true>(acc, 2 * VECS, &mut v2);

    // CRT reconstruction, by Garner: with a₁ = r₁ mod q₁ and a₂ = r₂ mod q₂ taken in [0, q),
    // the unique x ≡ rᵢ (mod qᵢ) in [0, q₁q₂) is a₁ + q₁·((a₂ − a₁)·q₁⁻¹ mod q₂). Subtracting
    // q₁q₂ above the midpoint centers it; truncating to 16 bits then gives the wrapping-`u16`
    // coefficient, exactly as `to_wrapping_u16` does for the single prime. This is exact
    // because the true product lies in (−q₁q₂/2, q₁q₂/2] — the bound in `crt`'s docs.
    let q1 = dup_n_s16(Q1);
    let q2 = dup_n_s16(Q2);
    let q1_inv_mont = dup_n_s16(CRT_Q1_INV_MONT);
    let q1_inv_mont_q = dup_n_s16(CRT_Q1_INV_MONT.wrapping_mul(Q2_INV));
    let q1_wide = dup_n_s32(Q1 as i32);
    let crt_q = dup_n_s32(CRT_Q);
    let crt_q_half = dup_n_s32(CRT_Q_HALF);

    let mut out = [0u16; RING_DEG];
    for i in 0..VECS {
        let r1 = load_i16(&v1, i);
        let r2 = load_i16(&v2, i);

        // Canonicalize both residues to [0, q) by adding q where negative.
        let a1 = add_16(r1, and(sshr_n_s16::<15>(r1), q1));
        let a2 = add_16(r2, and(sshr_n_s16::<15>(r2), q2));

        // t = (a₂ − a₁)·q₁⁻¹ mod q₂, centered, then canonicalized to [0, q₂).
        let t = mont_mul(sub_16(a2, a1), q1_inv_mont, q1_inv_mont_q, q2);
        let t = add_16(t, and(sshr_n_s16::<15>(t), q2));

        // a₁ + q₁·t needs 32 bits, so widen each half. Both operands are non-negative and
        // below their prime, so the sign-extending widen is the right one.
        let mut wide = [
            mla_32(sxtl_low_s16(a1), sxtl_low_s16(t), q1_wide),
            mla_32(sxtl_high_s16(a1), sxtl_high_s16(t), q1_wide),
        ];
        for x in wide.iter_mut() {
            // Center: subtract q₁q₂ above the midpoint.
            let over = cmgt_s32(*x, crt_q_half);
            *x = sub_32(*x, and(crt_q, over));
        }

        // `xtn` truncates each to its low 16 bits, which is the wrapping-`u16` value. The store
        // covers `out[8i .. 8i + 8]`, within `RING_DEG = 8 * VECS`.
        store_u16(&mut out, i, xtn_pair_32(wide[0], wide[1]));
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
        if !super::super::available() {
            return;
        }

        let mut a: Block = core::array::from_fn(|i| i as i16);
        let mut probe: Block = [0i16; RING_DEG];

        // SAFETY: `available()` returned true, and group 0 is vectors 0..8 of a 32-vector block.
        unsafe {
            let mut v = load_group(&a, 0);
            for j in 0..8 {
                store_i16(&mut probe, j, v[j]);
            }
            store_group(&mut a, 0, &mut v);
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
