//! AVX2 negacyclic NTT over *two* 16-bit primes, combined by the CRT.
//!
//! This computes the same ring products as [`crate::arithmetic::ntt`] — the same `[u16; 256]`
//! come out — but by a different route: instead of one 26-bit prime in `i32` lanes, it runs the
//! transform twice in `i16` lanes, over q₁ = 7681 and q₂ = 10753, and reconstructs the exact
//! integer product from the two residues. This is the arrangement Chung, Hwang, Kannwischer,
//! Seiler, Shih and Yang use for Saber on AVX2 (TCHES 2021, §4.2).
//!
//! # Why two primes
//!
//! AVX2 has `vpmulhw` (16 lanes of 16×16→high-16) but no 32-bit equivalent. Over a single
//! 26-bit prime every high product has to be built out of `vpmuldq`, which covers only the four
//! even lanes, plus a `vpshufd` to reach the odd ones: six multiplies and three shuffles for 8
//! coefficients, against three multiplies for 16 here. Two transforms at 4× the per-multiply
//! density is a net win.
//!
//! Every other path arrives at the same answer by its own route, so all of them are two-prime
//! now — see [`crate::backend::crt`] for the shared scheme. NEON has `sqdmulh` at both widths,
//! so the lane-width argument above cancels there, but the single-prime code reached for
//! widening `vmull_s32` (two lanes) against `vmulhq_s16`'s eight, which does not. The portable
//! code compiles to baseline SSE2 on x86-64, which has no 64-bit multiply at all and must
//! emulate the single-prime product; see [`crate::arithmetic::ntt_crt`]. What would *not* want
//! two primes is a genuinely scalar target, where a 32×32→64 multiply costs the same as a
//! 16×16→32 one and the doubled work buys nothing.
//!
//! Measured on kopis768, with this and the single-prime transform compiled into one binary and
//! selected at runtime (the only way to compare them fairly — built separately, code moves
//! around enough to swamp the difference and even reverse its sign), this is about 17% faster
//! on encapsulation's NTT work and about 9% faster on encapsulation end to end.
//!
//! # Correctness
//!
//! q₁·q₂ = 82_593_793, so the centered range ±41_296_896 comfortably covers the exactness
//! bound ℓ·256·(2^13 − 1)·(μ/2) ≤ 25_162_752 that [`crate::arithmetic::ntt`] establishes; the
//! margin is 16_134_144. Both primes are 1 mod 512, so X^256 + 1 splits completely over each
//! and the same complete 8-layer transform applies, with the same ψ-table layout and the same
//! Cooley-Tukey / Gentleman-Sande structure as the serial code.
//!
//! # What this costs, and it is not nothing
//!
//! The bit-packing and the binomial sampler are lane-parallel restatements of portable code
//! that produce *bit-identical* values, and are tested against it stage by stage. That is what
//! lets the Lean correspondence proof, which is about the portable code, keep covering the
//! shipped binary.
//!
//! The two-prime NTT breaks that, here and everywhere else it is used. Its NTT-domain values
//! are different integers entirely; only the endpoints agree, so `avx2_matches_serial` in
//! [`crate::arithmetic::ntt`] checks the pipeline end to end rather than stage by stage.
//!
//! Note the scope carefully: the Lean proof is about the *single-prime* transform in
//! [`crate::arithmetic::ntt`], and since the portable path moved to two primes as well (see
//! [`crate::arithmetic::ntt_crt`]) that transform no longer ships in any configuration. So
//! **the Lean proof does not currently cover the ring multiplication in any build**, not just
//! AVX2 ones. What is verified is that the algorithm is right — the same negacyclic transform,
//! over moduli whose product covers the product bound — not that these implementations of it
//! are. That guarantee now rests entirely on tests: `crt_matches_single` against the retained
//! single-prime reference, `avx2_matches_serial` and `neon_matches_serial` for the vector
//! backends, the schoolbook and extremal-coefficient tests over all three parameter sets, and
//! the KATs. Re-establishing the proof means porting it to the two-prime transform.
//!
//! # Layout
//!
//! [`crate::arithmetic::ntt::NttElem`] is `[i16; 512]`: two 256-coefficient blocks, residues
//! mod q₁ in the first and mod q₂ in the second. The pointwise accumulator is `[i32; 512]`,
//! split the same way. Those are the types the portable two-prime transform in
//! [`crate::arithmetic::ntt_crt`] uses too, so this backend and the portable path agree on the
//! representation outright rather than by reinterpretation. Since neither
//! `NttElem` nor `NttMatrix` is ever serialized (a public key stores `matrix_seed` and
//! re-derives its NTT form — see `crate::pke::PkePublicKey`) the representation never escapes
//! the process that computed it.
//!
//! 256 `i16` are 16 vectors of 16. The first four levels (`len` ≥ 16) pair whole vectors. The
//! last four live inside a vector, so the 16 vectors are transposed as a 16×16 matrix: lane `m`
//! then holds coefficient block `m` in its entirety and all four remaining levels become
//! vertical butterflies with a per-lane ψ. Then we transpose back. The transpose is done in two
//! 8-register halves (an in-lane 8×8 transpose each) plus a `vperm2i128` pass, which keeps its
//! working set inside the 16 available `ymm` registers.
//!
//! # Growth
//!
//! An `i16` lane holds only 3.05·q₂, so both transforms need interior reductions. The bounds,
//! taken over the worst case q₂ = 10753:
//!
//! * Forward: inputs are centered, |a| ≤ q/2. Barrett after levels 3 and 7 re-centers to q/2,
//!   and the final Barrett leaves the output at |a| ≤ q/2. Note the second run is *four*
//!   levels (len = 16, 8, 4, 2): the crude 0.75q-per-level budget in [`crate::backend::crt`]
//!   does not cover it (it predicts 3.5q > 3.05q). The run is safe because the ψ magnitudes at
//!   levels 4–7 are small enough — interval propagation with the actual per-butterfly ψ values
//!   bounds the worst lane below 30_700 of 32_767. This differs from NEON, which re-centers
//!   after levels 3 and 6; see [`crate::backend::crt`] for the shared argument and the caveat
//!   about re-deriving the bound if the schedule or tables change.
//! * Inverse: the Gentleman-Sande sum path doubles per level and both `lo ± hi` must fit, so
//!   the usable bound is 1.52q. Starting under 0.7q, two levels reach 2.66q — as a *sum*,
//!   which fits — and a Barrett after levels 2, 4 and 6 keeps it there. The last two levels
//!   end at 2.0q, which the final Montgomery scaling brings back under q.
//!
//! Every one of those sites was checked against the `i16` range by the scalar model the
//! constants were generated with, on random and extremal inputs for all three parameter sets;
//! the worst lane value observed in those runs was 20411 of 32767 (the certified worst-case
//! bound above is higher because it quantifies over all possible inputs).

// Explicit `for i in 0..N` index loops, as in the rest of the crate.
#![allow(clippy::needless_range_loop)]

use crate::consts::RING_DEG;

use crate::backend::crt::{
    self, BARRETT_SH, CRT_Q, CRT_Q_HALF, CRT_Q1_INV_MONT, Q1, Q1_INV, Q2, Q2_INV, ZETAS_Q1,
    ZETAS_Q2,
};

use super::intrinsics::{
    Vec256, add_epi16, add_epi32, and_si256, castsi256_si128, cmpgt_epi32, cvtepu16_epi32,
    extracti128_si256, load_i16, load_i32, load_u16, mulhi_epi16, mullo_epi16, mullo_epi32,
    packs_epi32, packus_epi32, permute2x128_si256, permute4x64_epi64, set1_epi16, set1_epi32,
    slli_epi32, srai_epi16, srai_epi32, store_i16, store_i32, store_u16, sub_epi16, sub_epi32,
    unpackhi_epi16, unpackhi_epi32, unpackhi_epi64, unpacklo_epi16, unpacklo_epi32, unpacklo_epi64,
};

/// One prime's 256 centered residues, as 16 vectors of 16 `i16`.
///
/// The transform works in these blocks throughout; the two-blocks-in-one-buffer layout that
/// [`crate::arithmetic::ntt::NttElem`] presents to the rest of the crate is applied only at this
/// module's entry points, by the `*_of_*` accessors in [`super::intrinsics`].
type Block = [i16; RING_DEG];

/// A 32-byte-aligned per-lane ψ table for the transposed levels, with its q⁻¹-scaled twin.
/// Group `h` occupies entries `16h..16h + 16`; lane `m` of that group serves coefficient
/// block `m`.
#[repr(align(32))]
struct Tbl<const N: usize> {
    z: [i16; N],
    zq: [i16; N],
}

/// Builds one per-lane ψ table. Entry `16h + m` is `zetas[base + h·h_stride + m·m_stride]`,
/// negated when `neg` — which is what the inverse transform's Gentleman-Sande butterfly wants.
const fn lane_tbl<const N: usize>(
    zetas: &[i16; 256],
    qinv: i16,
    base: isize,
    h_stride: isize,
    m_stride: isize,
    neg: bool,
) -> Tbl<N> {
    let mut z = [0i16; N];
    let mut zq = [0i16; N];
    let mut h = 0;
    while h * 16 < N {
        let mut m = 0;
        while m < 16 {
            let idx = base + (h as isize) * h_stride + (m as isize) * m_stride;
            let value = zetas[idx as usize];
            let value = if neg { -value } else { value };
            z[h * 16 + m] = value;
            zq[h * 16 + m] = value.wrapping_mul(qinv);
            m += 1;
        }
        h += 1;
    }
    Tbl { z, zq }
}

// Forward transform, transposed levels. Lane `m` holds coefficient block `m` (coefficients
// 16m..16m+16), so the ψ index for sub-block `h` of that block is:
//
//  * level len=8: one sub-block,    index 16 + m
//  * level len=4: two sub-blocks,   index 32 + 2m + h
//  * level len=2: four sub-blocks,  index 64 + 4m + h
//  * level len=1: eight sub-blocks, index 128 + 8m + h
//
// which are exactly the ψ entries the serial transform's `k` counter reaches at those points.
static FWD8_Q1: Tbl<16> = lane_tbl(&ZETAS_Q1, Q1_INV, 16, 0, 1, false);
static FWD4_Q1: Tbl<32> = lane_tbl(&ZETAS_Q1, Q1_INV, 32, 1, 2, false);
static FWD2_Q1: Tbl<64> = lane_tbl(&ZETAS_Q1, Q1_INV, 64, 1, 4, false);
static FWD1_Q1: Tbl<128> = lane_tbl(&ZETAS_Q1, Q1_INV, 128, 1, 8, false);

// Inverse transform, transposed levels: the Gentleman-Sande pass walks the table downwards,
// consuming 255..128 at len=1, 127..64 at len=2, 63..32 at len=4 and 31..16 at len=8. All
// entries are negated, as the inverse butterfly multiplies by -ψ.
static INV1_Q1: Tbl<128> = lane_tbl(&ZETAS_Q1, Q1_INV, 255, -1, -8, true);
static INV2_Q1: Tbl<64> = lane_tbl(&ZETAS_Q1, Q1_INV, 127, -1, -4, true);
static INV4_Q1: Tbl<32> = lane_tbl(&ZETAS_Q1, Q1_INV, 63, -1, -2, true);
static INV8_Q1: Tbl<16> = lane_tbl(&ZETAS_Q1, Q1_INV, 31, 0, -1, true);

static FWD8_Q2: Tbl<16> = lane_tbl(&ZETAS_Q2, Q2_INV, 16, 0, 1, false);
static FWD4_Q2: Tbl<32> = lane_tbl(&ZETAS_Q2, Q2_INV, 32, 1, 2, false);
static FWD2_Q2: Tbl<64> = lane_tbl(&ZETAS_Q2, Q2_INV, 64, 1, 4, false);
static FWD1_Q2: Tbl<128> = lane_tbl(&ZETAS_Q2, Q2_INV, 128, 1, 8, false);

static INV1_Q2: Tbl<128> = lane_tbl(&ZETAS_Q2, Q2_INV, 255, -1, -8, true);
static INV2_Q2: Tbl<64> = lane_tbl(&ZETAS_Q2, Q2_INV, 127, -1, -4, true);
static INV4_Q2: Tbl<32> = lane_tbl(&ZETAS_Q2, Q2_INV, 63, -1, -2, true);
static INV8_Q2: Tbl<16> = lane_tbl(&ZETAS_Q2, Q2_INV, 31, 0, -1, true);

// Unlike everything in [`crate::backend::crt`], these tables are specific to this backend: their
// grouping is by AVX2's 16 `i16` lanes. They are selected between at each use site, by the
// `vertical!` macros below, rather than through a `&'static Tbl<N>` returned from an accessor:
// a function that returns a reference to a static is one of the things aeneas cannot translate.
// The `if SECOND` still folds away per monomorphization.

// ---------------------------------------------------------------------------------------
// Lane primitives
// ---------------------------------------------------------------------------------------

/// Loads group `h` of a per-lane ψ table, as `(ψ, ψ·q⁻¹)`
#[inline]
#[target_feature(enable = "avx2")]
fn ld_tbl<const N: usize>(table: &Tbl<N>, h: usize) -> (Vec256, Vec256) {
    (load_i16(&table.z, h), load_i16(&table.zq, h))
}

/// Signed Montgomery multiply on 16 lanes: `a · ψ · 2⁻¹⁶ mod q`, centered.
///
/// `zq` is `ψ·q⁻¹ mod 2^16`, so `t = a·zq` is the Montgomery quotient outright. `t·q` and
/// `a·ψ` agree in their low 16 bits by construction, so their difference has a zero low half
/// and the high halves alone give the exact quotient — no borrow to account for. Requires
/// `|a·ψ| < 2^15·q`, which every call site satisfies by the growth bounds in the module docs.
#[inline]
#[target_feature(enable = "avx2")]
fn mont_mul(a: Vec256, z: Vec256, zq: Vec256, q: Vec256) -> Vec256 {
    let t = mullo_epi16(a, zq);
    sub_epi16(mulhi_epi16(a, z), mulhi_epi16(t, q))
}

/// Centered Barrett reduction of 16 lanes: `r ≡ x (mod q)` with `|r| ≤ q/2`.
///
/// `t ≈ round(x/q)` is formed as `(hi(x·M) + 2^(SH-1)) >> SH`; the rounding addend is what
/// makes the result centered rather than merely bounded by q. The addition cannot overflow a
/// lane: `hi(x·M) ≤ 2^15·M/2^16 < 2^14` and the addend is 2^10.
#[inline]
#[target_feature(enable = "avx2")]
fn barrett(x: Vec256, m: Vec256, round: Vec256, q: Vec256) -> Vec256 {
    let t = add_epi16(mulhi_epi16(x, m), round);
    let t = srai_epi16::<BARRETT_SH>(t);
    sub_epi16(x, mullo_epi16(t, q))
}

/// One Cooley-Tukey butterfly pair: `(lo, hi) ← (lo + ψ·hi, lo − ψ·hi)`
#[inline]
#[target_feature(enable = "avx2")]
fn ct_butterfly(lo: &mut Vec256, hi: &mut Vec256, z: Vec256, zq: Vec256, q: Vec256) {
    let t = mont_mul(*hi, z, zq, q);
    *hi = sub_epi16(*lo, t);
    *lo = add_epi16(*lo, t);
}

/// One Gentleman-Sande butterfly pair: `(lo, hi) ← (lo + hi, −ψ·(lo − hi))`. The tables and
/// broadcasts feeding `z` already carry the negation.
#[inline]
#[target_feature(enable = "avx2")]
fn gs_butterfly(lo: &mut Vec256, hi: &mut Vec256, z: Vec256, zq: Vec256, q: Vec256) {
    let diff = sub_epi16(*lo, *hi);
    *lo = add_epi16(*lo, *hi);
    *hi = mont_mul(diff, z, zq, q);
}

/// Barrett-reduces a whole 256-coefficient block
#[inline]
#[target_feature(enable = "avx2")]
fn barrett_block(b: &mut Block, m: Vec256, round: Vec256, q: Vec256) {
    for i in 0..16 {
        store_i16(b, i, barrett(load_i16(b, i), m, round, q));
    }
}

/// Transposes eight vectors as an 8×8 `i16` matrix *within each 128-bit lane*, in place.
///
/// Interleave by words, then dwords, then qwords: after this, lane `c` of `v[r]` (within a
/// 128-bit half) holds what was lane `r` of `v[c]` of that same half.
#[inline]
#[target_feature(enable = "avx2")]
fn inlane_transpose8(v: &mut [Vec256; 8]) {
    let a0 = unpacklo_epi16(v[0], v[1]);
    let a1 = unpackhi_epi16(v[0], v[1]);
    let a2 = unpacklo_epi16(v[2], v[3]);
    let a3 = unpackhi_epi16(v[2], v[3]);
    let a4 = unpacklo_epi16(v[4], v[5]);
    let a5 = unpackhi_epi16(v[4], v[5]);
    let a6 = unpacklo_epi16(v[6], v[7]);
    let a7 = unpackhi_epi16(v[6], v[7]);

    let b0 = unpacklo_epi32(a0, a2);
    let b1 = unpackhi_epi32(a0, a2);
    let b2 = unpacklo_epi32(a1, a3);
    let b3 = unpackhi_epi32(a1, a3);
    let b4 = unpacklo_epi32(a4, a6);
    let b5 = unpackhi_epi32(a4, a6);
    let b6 = unpacklo_epi32(a5, a7);
    let b7 = unpackhi_epi32(a5, a7);

    v[0] = unpacklo_epi64(b0, b4);
    v[1] = unpackhi_epi64(b0, b4);
    v[2] = unpacklo_epi64(b1, b5);
    v[3] = unpackhi_epi64(b1, b5);
    v[4] = unpacklo_epi64(b2, b6);
    v[5] = unpackhi_epi64(b2, b6);
    v[6] = unpacklo_epi64(b3, b7);
    v[7] = unpackhi_epi64(b3, b7);
}

/// Transposes a 256-coefficient block as a 16×16 `i16` matrix, in place.
///
/// After this, `v[k]` lane `m` holds coefficient `16m + k` — so lane `m` owns coefficient block
/// `m` entirely, and the four innermost transform levels become vertical butterflies. Applied
/// twice it is the identity, which is how the transform gets back to coefficient order.
///
/// Viewing the matrix as four 8×8 blocks, the two 128-bit halves of `v[0..8]` hold the top two
/// and those of `v[8..16]` the bottom two. [`inlane_transpose8`] transposes all four in place;
/// a `vperm2i128` pass then swaps the off-diagonal pair. Doing it in two halves keeps the
/// working set at 8 vectors, which fits in registers.
#[target_feature(enable = "avx2")]
fn transpose16(b: &mut Block) {
    let mut scratch = [0i16; RING_DEG];
    for half in 0..2 {
        let mut v = [
            load_i16(b, 8 * half),
            load_i16(b, 8 * half + 1),
            load_i16(b, 8 * half + 2),
            load_i16(b, 8 * half + 3),
            load_i16(b, 8 * half + 4),
            load_i16(b, 8 * half + 5),
            load_i16(b, 8 * half + 6),
            load_i16(b, 8 * half + 7),
        ];
        inlane_transpose8(&mut v);
        for j in 0..8 {
            store_i16(&mut scratch, 8 * half + j, v[j]);
        }
    }

    for r in 0..8 {
        let a = load_i16(&scratch, r);
        let c = load_i16(&scratch, 8 + r);
        store_i16(b, r, permute2x128_si256::<0x20>(a, c));
        store_i16(b, 8 + r, permute2x128_si256::<0x31>(a, c));
    }
}

// ---------------------------------------------------------------------------------------
// The transforms
// ---------------------------------------------------------------------------------------

/// In-place forward negacyclic NTT of one 256-coefficient block, modulo `p.q`.
///
/// # Safety
///
/// Requires AVX2. The block's values must be centered residues, `|a| ≤ q/2`.
#[target_feature(enable = "avx2")]
fn ntt_block<const SECOND: bool>(b: &mut Block) {
    let q = set1_epi16(crt::q::<SECOND>());
    let bm = set1_epi16(crt::barrett_m::<SECOND>());
    let round = set1_epi16(1i16 << (BARRETT_SH - 1));

    // Levels with len ≥ 16: both halves of every butterfly are whole vectors, and ψ is constant
    // across a block, so it is simply broadcast.
    let mut k = 0usize;
    let mut half = 8usize; // len/16, the block half-width in vectors
    let mut level = 0usize;
    while half >= 1 {
        let mut start = 0usize;
        while start < 16 {
            k += 1;
            let z = set1_epi16(crt::zeta::<SECOND>(k));
            let zq = set1_epi16(crt::zeta_q::<SECOND>(k));
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

    // Levels with len < 16: transpose so each lane owns a whole coefficient block, then four
    // more vertical levels with per-lane ψ.
    transpose16(b);

    /// Applies one butterfly between two whole vectors of the transposed block, taking ψ from
    /// group `$h` of `$tbl`.
    macro_rules! vertical {
        ($fly:ident, $t1:expr, $t2:expr, $h:expr, $lo:expr, $hi:expr) => {{
            let (z, zq) = if SECOND {
                ld_tbl($t2, $h)
            } else {
                ld_tbl($t1, $h)
            };
            let mut lo = load_i16(b, $lo);
            let mut hi = load_i16(b, $hi);
            $fly(&mut lo, &mut hi, z, zq, q);
            store_i16(b, $lo, lo);
            store_i16(b, $hi, hi);
        }};
    }

    for j in 0..8 {
        vertical!(ct_butterfly, &FWD8_Q1, &FWD8_Q2, 0, j, j + 8); // len = 8
    }
    for h in 0..2 {
        for j in 0..4 {
            vertical!(
                ct_butterfly,
                &FWD4_Q1,
                &FWD4_Q2,
                h,
                8 * h + j,
                8 * h + j + 4
            ); // len = 4
        }
    }
    for h in 0..4 {
        for j in 0..2 {
            vertical!(
                ct_butterfly,
                &FWD2_Q1,
                &FWD2_Q2,
                h,
                4 * h + j,
                4 * h + j + 2
            ); // len = 2
        }
    }
    // Four levels of growth since the last Barrett (len = 16, 8, 4, 2); re-center before the
    // final level. The crude per-level budget does not cover a four-level run — the module
    // docs give the sharper, table-dependent bound that does.
    barrett_block(b, bm, round, q);
    for h in 0..8 {
        vertical!(ct_butterfly, &FWD1_Q1, &FWD1_Q2, h, 2 * h, 2 * h + 1); // len = 1
    }

    transpose16(b);

    // Leaves every coefficient centered, |a| ≤ q/2.
    barrett_block(b, bm, round, q);
}

/// In-place inverse negacyclic NTT of one 256-coefficient block, including the final scaling
/// that undoes both the 1/256 and the Montgomery factor left by the pointwise step.
///
/// # Safety
///
/// Requires AVX2. The block's values must satisfy `|a| < q`.
#[target_feature(enable = "avx2")]
fn invntt_block<const SECOND: bool>(b: &mut Block) {
    let q = set1_epi16(crt::q::<SECOND>());
    let bm = set1_epi16(crt::barrett_m::<SECOND>());
    let round = set1_epi16(1i16 << (BARRETT_SH - 1));

    transpose16(b);

    macro_rules! vertical {
        ($t1:expr, $t2:expr, $h:expr, $lo:expr, $hi:expr) => {{
            let (z, zq) = if SECOND {
                ld_tbl($t2, $h)
            } else {
                ld_tbl($t1, $h)
            };
            let mut lo = load_i16(b, $lo);
            let mut hi = load_i16(b, $hi);
            gs_butterfly(&mut lo, &mut hi, z, zq, q);
            store_i16(b, $lo, lo);
            store_i16(b, $hi, hi);
        }};
    }

    for h in 0..8 {
        vertical!(&INV1_Q1, &INV1_Q2, h, 2 * h, 2 * h + 1); // len = 1
    }
    for h in 0..4 {
        for j in 0..2 {
            vertical!(&INV2_Q1, &INV2_Q2, h, 4 * h + j, 4 * h + j + 2); // len = 2
        }
    }
    // The Gentleman-Sande sum path doubles per level; re-center every two levels so that both
    // `lo + hi` and `lo - hi` keep fitting a lane.
    barrett_block(b, bm, round, q);
    for h in 0..2 {
        for j in 0..4 {
            vertical!(&INV4_Q1, &INV4_Q2, h, 8 * h + j, 8 * h + j + 4); // len = 4
        }
    }
    for j in 0..8 {
        vertical!(&INV8_Q1, &INV8_Q2, 0, j, j + 8); // len = 8
    }
    barrett_block(b, bm, round, q);

    transpose16(b);

    // Levels with len ≥ 16. `k` continues downward from where the transposed levels stopped:
    // they consumed 128 + 64 + 32 + 16 = 240 of the 256 ψ entries.
    let mut k = 16usize;
    let mut half = 1usize;
    while half < 16 {
        let mut start = 0usize;
        while start < 16 {
            k -= 1;
            // The table entries are centered, so |ψ| ≤ q/2 and the negation cannot overflow.
            // `0 - z` rather than `z.wrapping_neg()`: aeneas leaves `i16::wrapping_neg` opaque
            // (it extracts to an axiom with no definition), whereas `wrapping_sub` gets real
            // semantics. Identical codegen, one fewer assumption in the Lean trust base. Same
            // reasoning as `src/arithmetic/ntt.rs`; see the note there.
            let neg_zeta = 0i16.wrapping_sub(crt::zeta::<SECOND>(k));
            let z = set1_epi16(neg_zeta);
            let zq = set1_epi16(neg_zeta.wrapping_mul(crt::qinv::<SECOND>()));
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
        half *= 2;
        // Two more levels since the last Barrett (the one closing the transposed section).
        if half == 4 {
            barrett_block(b, bm, round, q);
        }
    }

    // One final Montgomery multiply undoes both the 1/256 and the Montgomery factor.
    let scale = set1_epi16(crt::invntt_scale::<SECOND>());
    let scale_q = set1_epi16(crt::invntt_scale::<SECOND>().wrapping_mul(crt::qinv::<SECOND>()));
    for i in 0..16 {
        store_i16(b, i, mont_mul(load_i16(b, i), scale, scale_q, q));
    }
}

// ---------------------------------------------------------------------------------------
// Entry points. These have exactly the signatures of their `super::ntt` twins, so the dispatch
// in `crate::arithmetic::ntt` is unchanged; only the meaning of the bytes differs.
// ---------------------------------------------------------------------------------------

/// Reduces a ring element into one prime's centered residue block and transforms it.
///
/// `REDUCE` says whether the input needs reducing at all: uniform coefficients go up to 2^13,
/// which exceeds q₁, whereas CBD secrets satisfy |·| ≤ μ/2 ≤ 5 and are already centered
/// residues for both primes.
///
/// # Safety
///
/// Requires AVX2.
#[inline]
#[target_feature(enable = "avx2")]
fn split_and_transform<const SECOND: bool, const REDUCE: bool>(
    elem: &[u16; RING_DEG],
    b: &mut Block,
) {
    let q = set1_epi16(crt::q::<SECOND>());
    let bm = set1_epi16(crt::barrett_m::<SECOND>());
    let round = set1_epi16(1i16 << (BARRETT_SH - 1));
    for i in 0..16 {
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
/// [`crate::arithmetic::ntt::NttElem`] is: the q₁ block occupies `i16` vectors 0..16 and the q₂
/// block vectors 16..32.
///
/// # Safety
///
/// Requires AVX2.
#[inline]
#[target_feature(enable = "avx2")]
fn from_ring_elem<const REDUCE: bool>(elem: &[u16; RING_DEG]) -> [i16; 2 * RING_DEG] {
    let mut out = [0i16; 2 * RING_DEG];
    let mut b = [0i16; RING_DEG];

    split_and_transform::<false, REDUCE>(elem, &mut b);
    for i in 0..16 {
        store_i16(&mut out, i, load_i16(&b, i));
    }

    split_and_transform::<true, REDUCE>(elem, &mut b);
    for i in 0..16 {
        store_i16(&mut out, 16 + i, load_i16(&b, i));
    }

    out
}

/// Forward-transforms a ring element with plain coefficients in `[0, 2^13)`
///
/// # Safety
///
/// Requires AVX2.
#[target_feature(enable = "avx2")]
pub(crate) fn from_uniform(elem: &[u16; RING_DEG]) -> [i16; 2 * RING_DEG] {
    from_ring_elem::<true>(elem)
}

/// Forward-transforms a CBD secret, reading each coefficient as the signed value it encodes
///
/// # Safety
///
/// Requires AVX2.
#[target_feature(enable = "avx2")]
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
/// Requires AVX2.
#[target_feature(enable = "avx2")]
pub(crate) fn pointwise_mul_acc(
    acc: &mut [i32; 2 * RING_DEG],
    lhs: &[i16; 2 * RING_DEG],
    rhs: &[i16; 2 * RING_DEG],
) {
    for block in 0..2 {
        for i in 0..16 {
            // Vector `16 * block + i` of the operands read as 512 `i16`, and the two `i32`
            // vectors `32 * block + 2i` and `+ 1` of the accumulator read as 512 `i32`, are the
            // same 16 coefficients of the same prime.
            let l = load_i16(lhs, 16 * block + i);
            let r = load_i16(rhs, 16 * block + i);
            // The 32-bit products, as low and high halves re-joined by `vpunpck`: the low
            // unpack gives the products of lanes 0..4 and 8..12, the high one the rest.
            let lo = mullo_epi16(l, r);
            let hi = mulhi_epi16(l, r);
            let p0 = unpacklo_epi16(lo, hi);
            let p1 = unpackhi_epi16(lo, hi);
            // `vperm2i128` puts them back in coefficient order.
            let first = permute2x128_si256::<0x20>(p0, p1);
            let second = permute2x128_si256::<0x31>(p0, p1);

            let a0 = 32 * block + 2 * i;
            let a1 = a0 + 1;
            store_i32(acc, a0, add_epi32(load_i32(acc, a0), first));
            store_i32(acc, a1, add_epi32(load_i32(acc, a1), second));
        }
    }
}

/// Montgomery-reduces one accumulator block into `i16` lanes, then inverse-transforms it.
///
/// `base` is the accumulator's first `i32` vector for this prime: 0 for q₁, 32 for q₂.
///
/// # Safety
///
/// Requires AVX2.
#[inline]
#[target_feature(enable = "avx2")]
fn reduce_block<const SECOND: bool>(acc: &[i32; 2 * RING_DEG], base: usize, b: &mut Block) {
    let q = set1_epi16(crt::q::<SECOND>());
    let qinv = set1_epi16(crt::qinv::<SECOND>());

    for i in 0..16 {
        let a0 = load_i32(acc, base + 2 * i);
        let a1 = load_i32(acc, base + 2 * i + 1);
        // Signed Montgomery reduction of an `i32` with R = 2^16. Both the sign-extended low
        // halves and the arithmetic-shifted high halves are already in `i16` range, so
        // `vpackssdw` is exact; the qword permute repairs its lane interleaving. As in
        // `mont_mul`, the low halves cancel, so subtracting the high halves is the whole
        // answer.
        let lo = permute4x64_epi64::<0xD8>(packs_epi32(
            srai_epi32::<16>(slli_epi32::<16>(a0)),
            srai_epi32::<16>(slli_epi32::<16>(a1)),
        ));
        let hi = permute4x64_epi64::<0xD8>(packs_epi32(srai_epi32::<16>(a0), srai_epi32::<16>(a1)));
        let t = mullo_epi16(lo, qinv);
        store_i16(b, i, sub_epi16(hi, mulhi_epi16(t, q)));
    }

    // The block now holds residues with |a| < q, as `invntt_block` requires.
    invntt_block::<SECOND>(b);
}

/// Montgomery-reduces the accumulator, inverse-transforms both residue blocks, reconstructs the
/// exact integer product by the CRT and packs it into wrapping-`u16` coefficients.
///
/// # Safety
///
/// Requires AVX2.
#[target_feature(enable = "avx2")]
pub(crate) fn reduce_invntt(acc: &[i32; 2 * RING_DEG]) -> [u16; RING_DEG] {
    let mut v1 = [0i16; RING_DEG];
    let mut v2 = [0i16; RING_DEG];

    // The accumulator is 512 `i32`, so the q₂ block starts at `i32` vector 32.
    reduce_block::<false>(acc, 0, &mut v1);
    reduce_block::<true>(acc, 32, &mut v2);

    // CRT reconstruction, by Garner: with a₁ = r₁ mod q₁ and a₂ = r₂ mod q₂ taken in [0, q),
    // the unique x ≡ rᵢ (mod qᵢ) in [0, q₁q₂) is a₁ + q₁·((a₂ − a₁)·q₁⁻¹ mod q₂). Subtracting
    // q₁q₂ above the midpoint centers it; truncating to 16 bits then gives the wrapping-`u16`
    // coefficient, exactly as `to_wrapping_u16` does for the single prime. This is exact
    // because the true product lies in (-q₁q₂/2, q₁q₂/2] — the bound in the module docs.
    let q1 = set1_epi16(Q1);
    let q2 = set1_epi16(Q2);
    let q1_inv_mont = set1_epi16(CRT_Q1_INV_MONT);
    let q1_inv_mont_q = set1_epi16(CRT_Q1_INV_MONT.wrapping_mul(Q2_INV));
    let q1_wide = set1_epi32(Q1 as i32);
    let crt_q = set1_epi32(CRT_Q);
    let crt_q_half = set1_epi32(CRT_Q_HALF);
    let low16 = set1_epi32(0xFFFF);

    /// Combines eight widened residue pairs into the low 16 bits of the centered product
    macro_rules! combine {
        ($a1:expr, $t:expr) => {{
            let x = add_epi32($a1, mullo_epi32($t, q1_wide));
            let over = cmpgt_epi32(x, crt_q_half);
            and_si256(sub_epi32(x, and_si256(crt_q, over)), low16)
        }};
    }

    let mut out = [0u16; RING_DEG];
    for i in 0..16 {
        let r1 = load_i16(&v1, i);
        let r2 = load_i16(&v2, i);

        // Canonicalize both residues to [0, q) by adding q where negative.
        let a1 = add_epi16(r1, and_si256(srai_epi16::<15>(r1), q1));
        let a2 = add_epi16(r2, and_si256(srai_epi16::<15>(r2), q2));

        // t = (a₂ − a₁)·q₁⁻¹ mod q₂, centered, then canonicalized to [0, q₂).
        let t = mont_mul(sub_epi16(a2, a1), q1_inv_mont, q1_inv_mont_q, q2);
        let t = add_epi16(t, and_si256(srai_epi16::<15>(t), q2));

        // a₁ + q₁·t needs 32 bits, so widen the two 128-bit halves separately. Both
        // operands are non-negative and below their prime, so zero extension is right.
        let first = combine!(
            cvtepu16_epi32(castsi256_si128(a1)),
            cvtepu16_epi32(castsi256_si128(t))
        );
        let second = combine!(
            cvtepu16_epi32(extracti128_si256::<1>(a1)),
            cvtepu16_epi32(extracti128_si256::<1>(t))
        );

        // Both inputs are masked to 16 bits, so the unsigned saturating pack is exact; the
        // qword permute repairs the lane interleaving `vpackusdw` introduces.
        let packed = permute4x64_epi64::<0xD8>(packus_epi32(first, second));
        store_u16(&mut out, i, packed);
    }
    out
}

#[cfg(test)]
mod test {
    use super::*;

    // The transposed levels are only correct if `transpose16` really does put coefficient
    // block `m` in lane `m` — and if applying it twice gets back to coefficient order.
    #[allow(unsafe_code)]
    #[test]
    fn transpose16_permutes_as_documented() {
        if !super::super::available() {
            return;
        }

        let mut a: Block = core::array::from_fn(|i| i as i16);
        // SAFETY: `available()` returned true.
        unsafe { transpose16(&mut a) };

        // Vector `k` lane `m` — linear index 16k + m — must now hold coefficient 16m + k.
        for k in 0..16 {
            for m in 0..16 {
                assert_eq!(a[16 * k + m], (16 * m + k) as i16, "vector {k} lane {m}");
            }
        }

        // SAFETY: as above.
        unsafe { transpose16(&mut a) };
        for i in 0..RING_DEG {
            assert_eq!(a[i], i as i16, "transposing twice is the identity");
        }
    }
}
