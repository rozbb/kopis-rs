//! This file defines the two-prime NTT that every backend uses
//!
//! Rather than one 26-bit prime in `i32` lanes, the transform runs twice in `i16` lanes, over
//! q₁ = 7681 and q₂ = 10753, and the exact integer product is reconstructed from the two
//! residues. This is the arrangement Chung, Hwang, Kannwischer, Seiler, Shih and Yang use for
//! Saber on AVX2 (TCHES 2021, §4.2). Two 16-bit transforms cost fewer multiplies per
//! coefficient than one 32-bit transform on every ISA here, the portable path included, since
//! LLVM auto-vectorizes its butterfly loops.
//!
//! The moduli, Montgomery and Barrett constants and ψ tables below are shared:
//! `backend::avx2::ntt` and `backend::neon::ntt` read them too, each adding its own intrinsics
//! and its own per-lane ψ tables, whose shape depends on the vector width. The rest of the file
//! is the portable transform, which is what [`crate::arithmetic::ntt_arith`] uses when no vector
//! backend is available.
//!
//! # Correctness
//!
//! q₁·q₂ = 82_593_793, so the centered range ±41_296_896 covers the exactness bound
//! ℓ·256·(2^13 − 1)·(μ/2) ≤ 25_162_752 that [`crate::arithmetic::ntt_arith`] establishes. Both
//! primes are 1 mod 512, so X^256 + 1 splits completely over each and the same complete 8-layer
//! Cooley-Tukey / Gentleman-Sande transform applies to both.
//!
//! Only the endpoints of the pipeline agree between implementations — the NTT-domain values are
//! different integers — so the backends are checked end to end by `avx2_matches_serial` and
//! `neon_matches_serial` in [`crate::arithmetic::ntt_arith`] rather than stage by stage.
//!
//! # Layout
//!
//! An [`NttElem`](crate::arithmetic::NttElem) is `[i16; 512]`: the q₁ residues in the first 256
//! lanes, the q₂ residues in the second. The pointwise accumulator is `[i32; 512]`, split the
//! same way. Neither is ever serialized, so the representation never escapes the process that
//! computed it.
//!
//! # Growth
//!
//! An `i16` lane holds 3.05·q₂, so both directions need interior reductions. Forward, a
//! Cooley-Tukey level maps |a| to at most |a|·(1 + q/2^17) + q/2, since the ψ are centered and
//! the Montgomery quotient is an `i16`; from a centered start that reaches 2.95q after four
//! levels and 3.19q after five, so at most four levels may run between reductions. Inverse, the
//! Gentleman-Sande sum path doubles per level and both `lo ± hi` must fit, giving a usable bound
//! of 1.52q that a Barrett pass every second level holds.
//!
//! The portable transform reduces forward after levels 3 and 6 plus a final pass, and inverse
//! after levels 2, 4 and 6. Each backend documents its own schedule.

// Explicit `for i in 0..N` index loops, as in the rest of the arithmetic: they are what the
// Lean extractor handles best, and here they are also what vectorizes most predictably.
#![allow(clippy::needless_range_loop)]

// Both Barrett constants were verified exhaustively over the whole i16 input range, and the CRT
// reconstruction against exact integer arithmetic.

/// The first NTT prime
pub(crate) const Q1: i16 = 7681;
/// The second NTT prime
pub(crate) const Q2: i16 = 10753;
/// q₁⁻¹ mod 2^16, for signed Montgomery reduction with R = 2^16
pub(crate) const Q1_INV: i16 = -7679;
/// q₂⁻¹ mod 2^16
pub(crate) const Q2_INV: i16 = -10751;
/// round(2^(16+11) / q₁), the Barrett multiplier for q₁
pub(crate) const Q1_BARRETT_M: i16 = 17474;
/// round(2^(16+11) / q₂)
pub(crate) const Q2_BARRETT_M: i16 = 12482;
/// The Barrett shift, shared by both primes: q₁ cannot go higher without its multiplier leaving
/// an `i16` lane, and q₂ reaches the same `|r| ≤ q/2` at 11 as it does at 12
pub(crate) const BARRETT_SH: i32 = 11;
/// 256⁻¹ · 2^32 mod q₁: undoes both the 1/256 of the inverse transform and the 2^-16 the
/// pointwise Montgomery reduction introduces
pub(crate) const INVNTT_SCALE_1: i16 = 1912;
/// 256⁻¹ · 2^32 mod q₂
pub(crate) const INVNTT_SCALE_2: i16 = 2536;
/// q₁·q₂, the CRT modulus
pub(crate) const CRT_Q: i32 = 82593793;
/// ⌊q₁q₂/2⌋, the centering threshold for the reconstructed product
pub(crate) const CRT_Q_HALF: i32 = 41296896;
/// (q₁⁻¹ mod q₂) · 2^16 mod q₂, the Garner coefficient in Montgomery form
pub(crate) const CRT_Q1_INV_MONT: i16 = 3563;

/// Powers of ψ₁ = 62 (a primitive 512th root of unity mod q₁) in bit-reversed order and
/// Montgomery form: `ZETAS_Q1[k] = ψ₁^brv8(k) · 2^16 mod q₁`, centered. The
/// `zetas_tables_are_correct` test recomputes both tables from ψ and checks every entry.
#[rustfmt::skip]
pub(crate) const ZETAS_Q1: [i16; 256] = [
    -3593, 3777, -3182, 3625, -3696, -1100, 2456, 2194, 121, -2250, 834, -2495, -2319, 2876, -1701, 1414,
    2816, -2088, -2237, 1986, -1599, 1993, 3706, -2006, -1525, -2557, 1296, 1483, -2830, 3364, 617, 1921,
    -3689, -1738, 3266, -3600, 810, 1887, -638, -7, -438, -679, -1305, -1760, 396, -3174, -3555, -1881,
    3772, -2535, -2440, -2555, 1535, -549, 3153, 2310, -1399, 1321, 514, -2956, -103, 2804, -2043, -1431,
    -1054, 1698, -3456, 1166, 2426, 3831, 915, -2, -3417, -194, 2919, 2789, 3405, 2385, -2113, -2732,
    2175, 373, 3692, -730, -1756, 3135, -2391, 660, -1497, 2572, -3145, 1350, -2224, -3588, -1681, 2883,
    -1390, 1598, 3750, 2762, 2835, 2764, -2233, 3816, -1533, 1464, -727, 1521, 1386, -3428, -921, -2743,
    -2160, 2649, -859, 2579, 1532, 1919, -486, 404, -1056, 783, 1799, -2665, 3480, 2133, -3310, -1168,
    -17, 3744, 2422, 2001, 1278, 929, -1348, -2230, -179, -1242, -2059, -1070, 2161, 1649, 2072, 3177,
    -2071, 1121, -436, 236, 715, 670, -658, -1476, -2378, 2767, 3542, -226, 1203, 1181, -151, -3794,
    1712, -222, 2786, -451, -3547, 1779, -1151, -434, 3568, -3693, 3581, -1586, 1509, 2918, 2339, -1407,
    3434, -3550, 2340, 2891, 2998, -3314, 3461, -2719, -2247, -2589, 1144, 1072, 1295, -2815, -3770, 3450,
    3781, -2258, 796, 3163, -3208, -589, 2963, -124, 3214, 3334, -3366, -3745, 3723, 1931, -429, -402,
    -3408, 83, -1526, 826, -1338, 2345, -2303, 2515, -642, -1837, -2965, -791, 370, 293, 3312, 2083,
    -1689, -777, 2070, 2262, -893, 2386, -188, -1519, -2874, -1404, 1012, 2130, 1441, 2532, -3335, -1084,
    -3343, 2937, 509, -1403, 2812, 3763, 592, 2005, 3657, 2460, -3677, 3752, 692, 1669, 2167, -3287,
];

/// Powers of ψ₂ = 10 (a primitive 512th root of unity mod q₂), laid out as for [`ZETAS_Q1`]
#[rustfmt::skip]
pub(crate) const ZETAS_Q2: [i16; 256] = [
    1018, 223, 4188, -3688, 2413, -3686, 357, -376, 2695, -730, 4855, 2236, -425, 4544, 3364, -3784,
    4875, -1520, -5063, -4035, 2503, 918, -3012, 4347, 1931, -1341, -3823, -341, -4095, -5175, -2629, -5213,
    -3091, 4129, -2935, 2790, 268, 1284, 4, 3550, 2982, 1287, 205, 4513, -2565, -2178, 4616, -193,
    -4102, 4742, -4876, -4744, -2984, -3062, -847, -4379, -2388, -1009, -3085, -1299, -2576, 4189, 1085, 544,
    5023, 794, -567, -3198, 4734, -2998, 3441, -5341, 675, 2271, 1615, -2213, 512, 2774, 3057, -2045,
    3615, -1458, -909, 5114, 2981, -4977, -116, 4580, -454, -5064, 4808, -1841, -886, -1356, -4828, -5156,
    2737, 4286, -3169, -578, 5294, -636, 400, 151, -2884, -336, -1006, -326, 1572, -2740, -779, 2206,
    -1586, 1068, -3715, -1268, 2684, -5116, 1324, 2973, -2234, -4123, 3337, -864, 472, -467, 970, 635,
    -573, 2230, -1132, -4621, 2624, -4601, 3570, -3760, -5309, 3453, -5215, 854, -4250, 2428, 1381, 5172,
    -5015, -4447, 3135, 2662, 3524, -1573, 2139, 458, -2196, -2657, 4782, -3410, 2062, 2015, -4784, 1635,
    1349, -1722, 2909, -4359, 2680, 2087, 40, 3241, -2439, 2117, 2050, 2118, -4144, -274, 3148, -1930,
    1992, 4408, 5005, -4428, 2419, 1639, 2283, -778, -2374, 663, 1409, -2237, -4254, -1122, 97, -5313,
    -3535, -2813, 5083, 279, 4328, 2279, 2151, 355, -4003, 1204, -5356, -624, 5120, -4519, -1689, 1056,
    3891, -3827, 1663, -2625, -2449, 3995, -1160, 2788, -4540, 3125, 5068, 3096, 1893, -2807, -5268, 2205,
    -4889, -152, 569, 4973, -825, 4393, 4000, 1510, 3419, -3360, 693, -3260, 4967, 4859, 2963, 554,
    -5107, -73, -4891, -1927, 5334, 2605, 2487, -2529, -834, 1782, 1111, 2113, 4720, -4670, -1053, -4403,
];

/// Elementwise `ZETAS · q⁻¹ mod 2^16`, the multiplier that produces the Montgomery quotient in
/// one step
pub(crate) const fn zetas_qinv(zetas: &[i16; 256], qinv: i16) -> [i16; 256] {
    let mut table = [0i16; 256];
    let mut k = 0;
    while k < 256 {
        table[k] = zetas[k].wrapping_mul(qinv);
        k += 1;
    }
    table
}

pub(crate) const ZETAS_Q1_QINV: [i16; 256] = zetas_qinv(&ZETAS_Q1, Q1_INV);
pub(crate) const ZETAS_Q2_QINV: [i16; 256] = zetas_qinv(&ZETAS_Q2, Q2_INV);

// The per-prime parameters, one accessor each, so a level loop can be written once and
// specialized per prime. These return values rather than a `&'static Prime` because aeneas
// cannot translate a function that returns a reference to a static.

/// The modulus
pub(crate) const fn q<const SECOND: bool>() -> i16 {
    if SECOND { Q2 } else { Q1 }
}

/// q⁻¹ mod 2^16, for signed Montgomery reduction
pub(crate) const fn qinv<const SECOND: bool>() -> i16 {
    if SECOND { Q2_INV } else { Q1_INV }
}

/// The Barrett multiplier, round(2^(16+`BARRETT_SH`) / q)
pub(crate) const fn barrett_m<const SECOND: bool>() -> i16 {
    if SECOND { Q2_BARRETT_M } else { Q1_BARRETT_M }
}

/// 256⁻¹ · 2^32 mod q, the inverse transform's final scaling
pub(crate) const fn invntt_scale<const SECOND: bool>() -> i16 {
    if SECOND {
        INVNTT_SCALE_2
    } else {
        INVNTT_SCALE_1
    }
}

/// ψ entry `k`, in bit-reversed order and Montgomery form
pub(crate) fn zeta<const SECOND: bool>(k: usize) -> i16 {
    if SECOND { ZETAS_Q2[k] } else { ZETAS_Q1[k] }
}

/// The matching `ψ·q⁻¹ mod 2^16`, which produces the Montgomery quotient in one step
pub(crate) fn zeta_q<const SECOND: bool>(k: usize) -> i16 {
    if SECOND {
        ZETAS_Q2_QINV[k]
    } else {
        ZETAS_Q1_QINV[k]
    }
}

use crate::consts::RING_DEG;

/// One residue block: 256 coefficients modulo one of the two primes
type Block = [i16; RING_DEG];

/// Signed Montgomery multiply: `a · z · 2⁻¹⁶ mod q`, centered.
///
/// `zq` is `z·q⁻¹ mod 2^16`, so `t = a·zq` is the Montgomery quotient outright. `t·q` and `a·z`
/// agree in their low 16 bits by construction, so their difference has a zero low half and the
/// high halves alone give the exact quotient, with no borrow to account for. Requires
/// `|a·z| < 2^15·q`, which the growth bounds in the module docs give at every call site.
///
/// Both products are written as `i32` multiplies whose high half is taken, the shape LLVM turns
/// into a single 16-lane high-multiply (`pmulhw` / `sqdmulh`).
#[inline(always)]
fn mont_mul(a: i16, z: i16, zq: i16, q: i16) -> i16 {
    let t = a.wrapping_mul(zq);
    let hi = ((a as i32).wrapping_mul(z as i32) >> 16) as i16;
    let th = ((t as i32).wrapping_mul(q as i32) >> 16) as i16;
    hi.wrapping_sub(th)
}

/// Centered Barrett reduction: `r ≡ x (mod q)` with `|r| ≤ q/2`, for any `i16` input.
///
/// `t ≈ round(x/q)` is `(hi(x·M) + 2^(SH-1)) >> SH`; the rounding addend is what makes the
/// result centered rather than merely bounded by q. It cannot overflow the lane:
/// `hi(x·M) ≤ 2^15·M/2^16 < 2^14` and the addend is 2^10.
#[inline(always)]
fn barrett(x: i16, m: i16, q: i16) -> i16 {
    let t = ((x as i32).wrapping_mul(m as i32) >> 16) as i16;
    let t = t.wrapping_add(1 << (BARRETT_SH - 1)) >> BARRETT_SH;
    x.wrapping_sub(t.wrapping_mul(q))
}

#[inline(always)]
fn barrett_block<const SECOND: bool>(b: &mut Block) {
    let q = q::<SECOND>();
    let m = barrett_m::<SECOND>();
    for i in 0..RING_DEG {
        b[i] = barrett(b[i], m, q);
    }
}

/// One Cooley-Tukey level: `(lo, hi) ← (lo + ψ·hi, lo − ψ·hi)` over every butterfly pair.
///
/// `LEN` is a const generic rather than a variable so that each level's inner loop has a
/// compile-time trip count, which is what lets LLVM vectorize it.
#[inline(always)]
fn ct_level<const LEN: usize, const SECOND: bool>(b: &mut Block, k: &mut usize) {
    let q = q::<SECOND>();
    let mut start = 0usize;
    while start < RING_DEG {
        *k += 1;
        let z = zeta::<SECOND>(*k);
        let zq = zeta_q::<SECOND>(*k);
        for j in start..start + LEN {
            let t = mont_mul(b[j + LEN], z, zq, q);
            b[j + LEN] = b[j].wrapping_sub(t);
            b[j] = b[j].wrapping_add(t);
        }
        start += 2 * LEN;
    }
}

/// One Gentleman-Sande level: `(lo, hi) ← (lo + hi, −ψ·(lo − hi))`
#[inline(always)]
fn gs_level<const LEN: usize, const SECOND: bool>(b: &mut Block, k: &mut usize) {
    let q = q::<SECOND>();
    let qinv = qinv::<SECOND>();
    let mut start = 0usize;
    while start < RING_DEG {
        *k -= 1;
        // The negation the Gentleman-Sande butterfly wants, taken here rather than baked into a
        // second table. `0 - z` rather than `z.wrapping_neg()` because aeneas extracts
        // `i16::wrapping_neg` as an axiom with no definition, whereas `wrapping_sub` gets real
        // semantics.
        let z = 0i16.wrapping_sub(zeta::<SECOND>(*k));
        let zq = z.wrapping_mul(qinv);
        for j in start..start + LEN {
            let lo = b[j];
            let hi = b[j + LEN];
            b[j] = lo.wrapping_add(hi);
            b[j + LEN] = mont_mul(lo.wrapping_sub(hi), z, zq, q);
        }
        start += 2 * LEN;
    }
}

/// Forward transform of one residue block. Inputs must be centered, `|a| ≤ q/2`.
fn ntt_block<const SECOND: bool>(b: &mut Block) {
    let mut k = 0usize;
    ct_level::<128, SECOND>(b, &mut k);
    ct_level::<64, SECOND>(b, &mut k);
    ct_level::<32, SECOND>(b, &mut k);
    // Three levels of Cooley-Tukey growth reach 2.75q; re-center before a fourth.
    barrett_block::<SECOND>(b);
    ct_level::<16, SECOND>(b, &mut k);
    ct_level::<8, SECOND>(b, &mut k);
    ct_level::<4, SECOND>(b, &mut k);
    barrett_block::<SECOND>(b);
    ct_level::<2, SECOND>(b, &mut k);
    ct_level::<1, SECOND>(b, &mut k);
    // Leaves the output centered, which is what the pointwise step's product bound assumes.
    barrett_block::<SECOND>(b);
}

/// Inverse transform of one residue block, including the final `256⁻¹·2³²` scaling.
fn invntt_block<const SECOND: bool>(b: &mut Block) {
    let q = q::<SECOND>();
    let scale = invntt_scale::<SECOND>();
    let scale_q = scale.wrapping_mul(qinv::<SECOND>());

    let mut k = RING_DEG;
    gs_level::<1, SECOND>(b, &mut k);
    gs_level::<2, SECOND>(b, &mut k);
    // The Gentleman-Sande sum path doubles per level; re-center every two levels so that both
    // `lo + hi` and `lo - hi` stay inside the lane.
    barrett_block::<SECOND>(b);
    gs_level::<4, SECOND>(b, &mut k);
    gs_level::<8, SECOND>(b, &mut k);
    barrett_block::<SECOND>(b);
    gs_level::<16, SECOND>(b, &mut k);
    gs_level::<32, SECOND>(b, &mut k);
    barrett_block::<SECOND>(b);
    gs_level::<64, SECOND>(b, &mut k);
    gs_level::<128, SECOND>(b, &mut k);
    // The last two levels end at 2.0q, which this scaling brings back under q.
    for i in 0..RING_DEG {
        b[i] = mont_mul(b[i], scale, scale_q, q);
    }
}

/// Splits a ring element into one residue block and transforms it.
///
/// `REDUCE` says whether the input needs reducing at all: uniform coefficients go up to 2^13,
/// which exceeds q₁, whereas CBD secrets satisfy |·| ≤ μ/2 ≤ 5 and are already centered
/// residues for both primes. Coefficients below 2^13 fit an `i16`, so the Barrett reduction is
/// in range; for secrets the `i16` reading of the `u16` is exactly the signed value it encodes.
#[inline(always)]
fn split_and_transform<const SECOND: bool, const REDUCE: bool>(
    elem: &[u16; RING_DEG],
    b: &mut Block,
) {
    let q = q::<SECOND>();
    let m = barrett_m::<SECOND>();
    for i in 0..RING_DEG {
        let x = elem[i] as i16;
        b[i] = if REDUCE { barrett(x, m, q) } else { x };
    }
    ntt_block::<SECOND>(b);
}

/// Splits a ring element into both residue blocks and transforms each
#[inline(always)]
fn from_ring_elem<const REDUCE: bool>(elem: &[u16; RING_DEG]) -> [i16; 2 * RING_DEG] {
    let mut out = [0i16; 2 * RING_DEG];
    let mut b = [0i16; RING_DEG];

    split_and_transform::<false, REDUCE>(elem, &mut b);
    out[..RING_DEG].copy_from_slice(&b);

    split_and_transform::<true, REDUCE>(elem, &mut b);
    out[RING_DEG..].copy_from_slice(&b);

    out
}

/// Forward-transforms a ring element with plain coefficients in `[0, 2^13)`
pub(crate) fn from_uniform(elem: &[u16; RING_DEG]) -> [i16; 2 * RING_DEG] {
    from_ring_elem::<true>(elem)
}

/// Forward-transforms a CBD secret, reading each coefficient as the signed value it encodes
pub(crate) fn from_secret(elem: &[u16; RING_DEG]) -> [i16; 2 * RING_DEG] {
    from_ring_elem::<false>(elem)
}

/// Adds the pointwise product `lhs ∘ rhs` into an unreduced accumulator, per prime.
///
/// Products of centered values are below (q/2 + 1)² and callers accumulate at most 4 (= `MAX_L`)
/// of them, so each lane stays under 1.2·10⁸ — well inside an `i32`, and inside the 2^15·q input
/// range of the Montgomery reduction that consumes it.
pub(crate) fn pointwise_mul_acc(
    acc: &mut [i32; 2 * RING_DEG],
    lhs: &[i16; 2 * RING_DEG],
    rhs: &[i16; 2 * RING_DEG],
) {
    for i in 0..2 * RING_DEG {
        acc[i] = acc[i].wrapping_add((lhs[i] as i32).wrapping_mul(rhs[i] as i32));
    }
}

/// Signed Montgomery reduction of one accumulator block into `i16` residues, with R = 2^16.
///
/// As in [`mont_mul`], the low halves cancel by construction, so subtracting the high halves is
/// the whole answer.
#[inline(always)]
fn reduce_block<const SECOND: bool>(acc: &[i32], b: &mut Block) {
    let q = q::<SECOND>();
    let qinv = qinv::<SECOND>();
    for i in 0..RING_DEG {
        let a = acc[i];
        let t = (a as i16).wrapping_mul(qinv);
        let th = ((t as i32).wrapping_mul(q as i32) >> 16) as i16;
        b[i] = ((a >> 16) as i16).wrapping_sub(th);
    }
}

/// Montgomery-reduces the accumulator, inverse-transforms both residue blocks, reconstructs the
/// exact integer product by the CRT and packs it into wrapping-`u16` coefficients.
pub(crate) fn reduce_invntt(acc: &[i32; 2 * RING_DEG]) -> [u16; RING_DEG] {
    let mut v1 = [0i16; RING_DEG];
    let mut v2 = [0i16; RING_DEG];

    reduce_block::<false>(&acc[..RING_DEG], &mut v1);
    reduce_block::<true>(&acc[RING_DEG..], &mut v2);
    invntt_block::<false>(&mut v1);
    invntt_block::<true>(&mut v2);

    // CRT reconstruction, by Garner: with a₁ = r₁ mod q₁ and a₂ = r₂ mod q₂ taken in [0, q),
    // the unique x ≡ rᵢ (mod qᵢ) in [0, q₁q₂) is a₁ + q₁·((a₂ − a₁)·q₁⁻¹ mod q₂). Subtracting
    // q₁q₂ above the midpoint centers it; truncating to 16 bits then gives the wrapping-`u16`
    // coefficient, exactly as `to_wrapping_u16` does for the single prime. This is exact because
    // the true product lies in (−q₁q₂/2, q₁q₂/2] — the bound in [`crate::arithmetic::ntt_arith`].
    let q1_inv_mont_q = CRT_Q1_INV_MONT.wrapping_mul(Q2_INV);
    let mut out = [0u16; RING_DEG];
    for i in 0..RING_DEG {
        let r1 = v1[i];
        let r2 = v2[i];
        // Canonicalize both residues to [0, q) by adding q where negative, branch-free.
        let a1 = r1.wrapping_add((r1 >> 15) & Q1);
        let a2 = r2.wrapping_add((r2 >> 15) & Q2);

        let t = mont_mul(a2.wrapping_sub(a1), CRT_Q1_INV_MONT, q1_inv_mont_q, Q2);
        let t = t.wrapping_add((t >> 15) & Q2);

        // a₁ + q₁·t needs 32 bits. Both operands are non-negative and below their prime, so the
        // widening is a zero extension.
        let x = (a1 as i32).wrapping_add((t as i32).wrapping_mul(Q1 as i32));
        // Branch-free `if x > CRT_Q_HALF { x - CRT_Q } else { x }`.
        let over = (CRT_Q_HALF.wrapping_sub(x)) >> 31;
        out[i] = x.wrapping_sub(CRT_Q & over) as u16;
    }
    out
}

#[cfg(test)]
mod test {
    use super::*;

    /// The two primitive 512th roots of unity underlying the ψ tables
    const PSI1: u64 = 62;
    const PSI2: u64 = 10;

    fn pow_mod(mut base: u64, mut exp: u64, modulus: u64) -> u64 {
        let mut acc = 1u64;
        base %= modulus;
        while exp > 0 {
            if exp & 1 == 1 {
                acc = acc * base % modulus;
            }
            base = base * base % modulus;
            exp >>= 1;
        }
        acc
    }

    // The constants that stand in for derived expressions must equal what they stand for.
    #[test]
    fn literal_constants_are_correct() {
        assert_eq!(CRT_Q, Q1 as i32 * Q2 as i32);
        assert_eq!(CRT_Q_HALF, CRT_Q / 2);
        // Each q⁻¹ really inverts q mod 2^16.
        assert_eq!((Q1 as u16).wrapping_mul(Q1_INV as u16), 1);
        assert_eq!((Q2 as u16).wrapping_mul(Q2_INV as u16), 1);
        // The Barrett multipliers are round(2^(16+SH) / q), at the shared shift.
        for (q, m) in [(Q1, Q1_BARRETT_M), (Q2, Q2_BARRETT_M)] {
            assert_eq!(
                m as i64,
                ((1i64 << (16 + BARRETT_SH)) + q as i64 / 2) / q as i64
            );
        }
        // The Garner coefficient is (q₁⁻¹ mod q₂) in Montgomery form: q₁·M·2^-16 ≡ 1 (mod q₂).
        let lifted = (CRT_Q1_INV_MONT as i64).rem_euclid(Q2 as i64);
        assert_eq!(lifted * Q1 as i64 % Q2 as i64, (1i64 << 16) % Q2 as i64);
        // The exactness bound really does fit the centered CRT range.
        assert!(2 * 25_162_752 < CRT_Q as i64);
    }

    // Recompute both ψ tables from their roots and check every entry, plus the defining
    // properties that make the transform negacyclic.
    #[test]
    fn zetas_tables_are_correct() {
        for (q, psi, table, qinv, scale) in [
            (Q1 as u64, PSI1, &ZETAS_Q1, Q1_INV, INVNTT_SCALE_1),
            (Q2 as u64, PSI2, &ZETAS_Q2, Q2_INV, INVNTT_SCALE_2),
        ] {
            assert_eq!(pow_mod(psi, 256, q), q - 1, "ψ^256 = -1 mod {q}");
            assert_eq!(pow_mod(psi, 512, q), 1, "ψ^512 = 1 mod {q}");

            for (k, &z) in table.iter().enumerate() {
                let brv = (k as u8).reverse_bits() as u64;
                let expected = pow_mod(psi, brv, q) * (1u64 << 16) % q;
                // The table is centered, so compare after lifting back to [0, q).
                assert_eq!(
                    (z as i64).rem_euclid(q as i64) as u64,
                    expected,
                    "ZETAS[{k}]"
                );
            }

            // INVNTT_SCALE = 256⁻¹ · 2^32 mod q, so 256 · scale ≡ 2^32.
            let lifted = (scale as i64).rem_euclid(q as i64) as u128;
            assert_eq!(
                (lifted * 256) % q as u128,
                (1u128 << 32) % q as u128,
                "INVNTT_SCALE for {q}"
            );
            // qinv is used to form the Montgomery quotient, so it must invert q mod 2^16.
            assert_eq!((q as u16).wrapping_mul(qinv as u16), 1);
        }
    }
}
