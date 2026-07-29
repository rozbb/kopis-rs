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
//! That reasoning is specific to this instruction set, which is why it is not what the other
//! backends do. On a scalar core the doubled work buys nothing, since a 32×32→64 multiply costs
//! the same as a 16×16→32 one; on NEON `sqdmulh.4s` supplies the 32-bit high product AVX2 is
//! missing, so halving the lane width doubles the lanes and the transforms in equal measure and
//! cancels; and on Cortex-M4 it is a straight regression. The portable, NEON and M4 paths all
//! keep the single prime — see [`crate::arithmetic::ntt`] for that arithmetic.
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
//! Every other accelerated routine in this crate — the bit-packing, the binomial sampler, the
//! whole NEON backend — is a lane-parallel restatement of portable code that produces
//! *bit-identical* values, and is tested against it stage by stage. That is what lets the Lean
//! correspondence proof, which is about the portable code, keep covering the shipped binary.
//!
//! This module breaks that. Its NTT-domain values are different integers entirely; only the
//! endpoints agree. So `avx2_matches_serial` in [`crate::arithmetic::ntt`] checks the pipeline
//! end to end rather than stage by stage, and **the Lean proof does not extend to AVX2 builds
//! of the ring multiplication**. What is verified is that the algorithm is right — the exact
//! same negacyclic transform, over moduli whose product covers the product bound — not that
//! this implementation of it is. On x86 that guarantee now rests on tests: the end-to-end
//! check against the portable pipeline, the schoolbook and extremal-coefficient tests, and the
//! KATs. Builds with `--cfg kopis_backend="serial"`, and all AArch64 builds, are unaffected.
//!
//! # Layout
//!
//! [`crate::arithmetic::ntt::NttElem`] is `[i32; 256]`, which is exactly 512 `i16`. This
//! backend reinterprets that buffer as two 256-coefficient blocks: residues mod q₁ in the
//! first, mod q₂ in the second. The `i64` pointwise accumulator is reinterpreted the same way,
//! as two blocks of 256 `i32`. So no type outside this file changes, and since neither
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
//! * Forward: inputs are centered, |a| ≤ q/2. A Cooley-Tukey level adds at most 0.75q, so
//!   three levels reach 2.75q < 3.05q. Barrett after levels 3 and 6 re-centers to q/2, and the
//!   final Barrett leaves the output at |a| ≤ q/2.
//! * Inverse: the Gentleman-Sande sum path doubles per level and both `lo ± hi` must fit, so
//!   the usable bound is 1.52q. Starting under 0.7q, two levels reach 2.66q — as a *sum*,
//!   which fits — and a Barrett after levels 2, 4 and 6 keeps it there. The last two levels
//!   end at 2.0q, which the final Montgomery scaling brings back under q.
//!
//! Every one of those sites was checked against the `i16` range by the scalar model the
//! constants were generated with, on random and extremal inputs for all three parameter sets;
//! the worst lane value observed was 20411 of 32767.

// Explicit `for i in 0..N` index loops, as in the rest of the crate.
#![allow(clippy::needless_range_loop)]

#[cfg(target_arch = "x86")]
use core::arch::x86::*;
#[cfg(target_arch = "x86_64")]
use core::arch::x86_64::*;

use crate::consts::RING_DEG;

// ---------------------------------------------------------------------------------------
// Constants, generated and checked by the scalar model described above: both primes prime and
// 1 mod 512, both Barrett constants verified exhaustively over the whole i16 input range, and
// the CRT reconstruction verified against exact integer arithmetic.
// ---------------------------------------------------------------------------------------

/// The first NTT prime
const Q1: i16 = 7681;
/// The second NTT prime
const Q2: i16 = 10753;
/// q₁⁻¹ mod 2^16, for signed Montgomery reduction with R = 2^16
const Q1_INV: i16 = -7679;
/// q₂⁻¹ mod 2^16
const Q2_INV: i16 = -10751;
/// round(2^(16+11) / q₁), the Barrett multiplier for q₁
const Q1_BARRETT_M: i16 = 17474;
/// round(2^(16+11) / q₂)
const Q2_BARRETT_M: i16 = 12482;
/// The Barrett shift, shared by both primes. q₁ cannot go higher without its multiplier leaving
/// an `i16` lane, and q₂ reaches the same `|r| ≤ q/2` at 11 as it does at 12, so one value
/// serves both. That it *is* shared matters for more than tidiness: the shift is a `vpsraw`
/// immediate, so a per-prime value would make every function below a const generic and
/// monomorphize the whole transform twice, doubling this backend's instruction footprint.
const BARRETT_SH: i32 = 11;
/// 256⁻¹ · 2^32 mod q₁: undoes both the 1/256 of the inverse transform and the 2^-16 the
/// pointwise Montgomery reduction introduces
const INVNTT_SCALE_1: i16 = 1912;
/// 256⁻¹ · 2^32 mod q₂
const INVNTT_SCALE_2: i16 = 2536;
/// q₁·q₂, the CRT modulus
const CRT_Q: i32 = 82593793;
/// ⌊q₁q₂/2⌋, the centering threshold for the reconstructed product
const CRT_Q_HALF: i32 = 41296896;
/// (q₁⁻¹ mod q₂) · 2^16 mod q₂, the Garner coefficient in Montgomery form
const CRT_Q1_INV_MONT: i16 = 3563;

/// Powers of ψ₁ = 62 (a primitive 512th root of unity mod q₁) in bit-reversed order and
/// Montgomery form: `ZETAS_Q1[k] = ψ₁^brv8(k) · 2^16 mod q₁`, centered. Same layout as
/// [`crate::arithmetic::ntt::ZETAS`]; the `crt_zetas_tables_are_correct` test recomputes both
/// tables from ψ and checks every entry.
#[rustfmt::skip]
const ZETAS_Q1: [i16; 256] = [
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
const ZETAS_Q2: [i16; 256] = [
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
/// one step (as `ZETAS_QINV` does in `ntt.rs`)
const fn zetas_qinv(zetas: &[i16; 256], qinv: i16) -> [i16; 256] {
    let mut table = [0i16; 256];
    let mut k = 0;
    while k < 256 {
        table[k] = zetas[k].wrapping_mul(qinv);
        k += 1;
    }
    table
}

const ZETAS_Q1_QINV: [i16; 256] = zetas_qinv(&ZETAS_Q1, Q1_INV);
const ZETAS_Q2_QINV: [i16; 256] = zetas_qinv(&ZETAS_Q2, Q2_INV);

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

/// Everything the transform needs for one of the two primes, so the level loops can be written
/// once. The Barrett shift is *not* here: `vpsraw` takes an immediate, so it rides as a const
/// generic on the functions that need it.
struct Prime {
    q: i16,
    qinv: i16,
    barrett_m: i16,
    invntt_scale: i16,
    zetas: &'static [i16; 256],
    zetas_q: &'static [i16; 256],
    fwd8: &'static Tbl<16>,
    fwd4: &'static Tbl<32>,
    fwd2: &'static Tbl<64>,
    fwd1: &'static Tbl<128>,
    inv1: &'static Tbl<128>,
    inv2: &'static Tbl<64>,
    inv4: &'static Tbl<32>,
    inv8: &'static Tbl<16>,
}

static P1: Prime = Prime {
    q: Q1,
    qinv: Q1_INV,
    barrett_m: Q1_BARRETT_M,
    invntt_scale: INVNTT_SCALE_1,
    zetas: &ZETAS_Q1,
    zetas_q: &ZETAS_Q1_QINV,
    fwd8: &FWD8_Q1,
    fwd4: &FWD4_Q1,
    fwd2: &FWD2_Q1,
    fwd1: &FWD1_Q1,
    inv1: &INV1_Q1,
    inv2: &INV2_Q1,
    inv4: &INV4_Q1,
    inv8: &INV8_Q1,
};

/// The parameters for prime `SECOND` (`false` = q₁, `true` = q₂).
///
/// Selected by a const generic rather than passed as a `&Prime`, so that each monomorphization
/// constant-folds the modulus, the Montgomery constant and the ψ-table addresses into the
/// instruction stream. Specializing measurably beats sharing one copy between the primes, even
/// though it doubles the instruction footprint of the transforms.
const fn prime<const SECOND: bool>() -> &'static Prime {
    if SECOND { &P2 } else { &P1 }
}

static P2: Prime = Prime {
    q: Q2,
    qinv: Q2_INV,
    barrett_m: Q2_BARRETT_M,
    invntt_scale: INVNTT_SCALE_2,
    zetas: &ZETAS_Q2,
    zetas_q: &ZETAS_Q2_QINV,
    fwd8: &FWD8_Q2,
    fwd4: &FWD4_Q2,
    fwd2: &FWD2_Q2,
    fwd1: &FWD1_Q2,
    inv1: &INV1_Q2,
    inv2: &INV2_Q2,
    inv4: &INV4_Q2,
    inv8: &INV8_Q2,
};

// ---------------------------------------------------------------------------------------
// Lane primitives
// ---------------------------------------------------------------------------------------

/// Loads vector `i` (coefficients `16i..16i+16`) of a 256-`i16` block
///
/// # Safety
///
/// `ptr` must be valid for reads of at least `16 * (i + 1)` `i16`s.
#[inline]
#[target_feature(enable = "avx2")]
unsafe fn ld(ptr: *const i16, i: usize) -> __m256i {
    // SAFETY: guaranteed by this function's contract; the load is unaligned.
    unsafe { _mm256_loadu_si256(ptr.add(16 * i).cast()) }
}

/// Stores vector `i` (coefficients `16i..16i+16`) of a 256-`i16` block
///
/// # Safety
///
/// `ptr` must be valid for writes of at least `16 * (i + 1)` `i16`s.
#[inline]
#[target_feature(enable = "avx2")]
unsafe fn st(ptr: *mut i16, i: usize, v: __m256i) {
    // SAFETY: guaranteed by this function's contract; the store is unaligned.
    unsafe { _mm256_storeu_si256(ptr.add(16 * i).cast(), v) }
}

/// Loads group `h` of a per-lane ψ table, as `(ψ, ψ·q⁻¹)`
///
/// # Safety
///
/// `16h + 16` must be within the table.
#[inline]
#[target_feature(enable = "avx2")]
unsafe fn ld_tbl<const N: usize>(table: &Tbl<N>, h: usize) -> (__m256i, __m256i) {
    // SAFETY: guaranteed by this function's contract.
    unsafe {
        (
            _mm256_loadu_si256(table.z.as_ptr().add(16 * h).cast()),
            _mm256_loadu_si256(table.zq.as_ptr().add(16 * h).cast()),
        )
    }
}

/// Signed Montgomery multiply on 16 lanes: `a · ψ · 2⁻¹⁶ mod q`, centered.
///
/// `zq` is `ψ·q⁻¹ mod 2^16`, so `t = a·zq` is the Montgomery quotient outright. `t·q` and
/// `a·ψ` agree in their low 16 bits by construction, so their difference has a zero low half
/// and the high halves alone give the exact quotient — no borrow to account for. Requires
/// `|a·ψ| < 2^15·q`, which every call site satisfies by the growth bounds in the module docs.
#[inline]
#[target_feature(enable = "avx2")]
fn mont_mul(a: __m256i, z: __m256i, zq: __m256i, q: __m256i) -> __m256i {
    let t = _mm256_mullo_epi16(a, zq);
    _mm256_sub_epi16(_mm256_mulhi_epi16(a, z), _mm256_mulhi_epi16(t, q))
}

/// Centered Barrett reduction of 16 lanes: `r ≡ x (mod q)` with `|r| ≤ q/2`.
///
/// `t ≈ round(x/q)` is formed as `(hi(x·M) + 2^(SH-1)) >> SH`; the rounding addend is what
/// makes the result centered rather than merely bounded by q. The addition cannot overflow a
/// lane: `hi(x·M) ≤ 2^15·M/2^16 < 2^14` and the addend is 2^10.
#[inline]
#[target_feature(enable = "avx2")]
fn barrett(x: __m256i, m: __m256i, round: __m256i, q: __m256i) -> __m256i {
    let t = _mm256_add_epi16(_mm256_mulhi_epi16(x, m), round);
    let t = _mm256_srai_epi16::<BARRETT_SH>(t);
    _mm256_sub_epi16(x, _mm256_mullo_epi16(t, q))
}

/// One Cooley-Tukey butterfly pair: `(lo, hi) ← (lo + ψ·hi, lo − ψ·hi)`
#[inline]
#[target_feature(enable = "avx2")]
fn ct_butterfly(lo: &mut __m256i, hi: &mut __m256i, z: __m256i, zq: __m256i, q: __m256i) {
    let t = mont_mul(*hi, z, zq, q);
    *hi = _mm256_sub_epi16(*lo, t);
    *lo = _mm256_add_epi16(*lo, t);
}

/// One Gentleman-Sande butterfly pair: `(lo, hi) ← (lo + hi, −ψ·(lo − hi))`. The tables and
/// broadcasts feeding `z` already carry the negation.
#[inline]
#[target_feature(enable = "avx2")]
fn gs_butterfly(lo: &mut __m256i, hi: &mut __m256i, z: __m256i, zq: __m256i, q: __m256i) {
    let diff = _mm256_sub_epi16(*lo, *hi);
    *lo = _mm256_add_epi16(*lo, *hi);
    *hi = mont_mul(diff, z, zq, q);
}

/// Barrett-reduces a whole 256-coefficient block
///
/// # Safety
///
/// `ptr` must be valid for reads and writes of 256 `i16`s.
#[inline]
#[target_feature(enable = "avx2")]
unsafe fn barrett_block(ptr: *mut i16, m: __m256i, round: __m256i, q: __m256i) {
    for i in 0..16 {
        // SAFETY: `i < 16` indexes within the 256-coefficient block.
        unsafe { st(ptr, i, barrett(ld(ptr, i), m, round, q)) };
    }
}

/// Transposes eight vectors as an 8×8 `i16` matrix *within each 128-bit lane*, in place.
///
/// Interleave by words, then dwords, then qwords: after this, lane `c` of `v[r]` (within a
/// 128-bit half) holds what was lane `r` of `v[c]` of that same half.
#[inline]
#[target_feature(enable = "avx2")]
fn inlane_transpose8(v: &mut [__m256i; 8]) {
    let a0 = _mm256_unpacklo_epi16(v[0], v[1]);
    let a1 = _mm256_unpackhi_epi16(v[0], v[1]);
    let a2 = _mm256_unpacklo_epi16(v[2], v[3]);
    let a3 = _mm256_unpackhi_epi16(v[2], v[3]);
    let a4 = _mm256_unpacklo_epi16(v[4], v[5]);
    let a5 = _mm256_unpackhi_epi16(v[4], v[5]);
    let a6 = _mm256_unpacklo_epi16(v[6], v[7]);
    let a7 = _mm256_unpackhi_epi16(v[6], v[7]);

    let b0 = _mm256_unpacklo_epi32(a0, a2);
    let b1 = _mm256_unpackhi_epi32(a0, a2);
    let b2 = _mm256_unpacklo_epi32(a1, a3);
    let b3 = _mm256_unpackhi_epi32(a1, a3);
    let b4 = _mm256_unpacklo_epi32(a4, a6);
    let b5 = _mm256_unpackhi_epi32(a4, a6);
    let b6 = _mm256_unpacklo_epi32(a5, a7);
    let b7 = _mm256_unpackhi_epi32(a5, a7);

    v[0] = _mm256_unpacklo_epi64(b0, b4);
    v[1] = _mm256_unpackhi_epi64(b0, b4);
    v[2] = _mm256_unpacklo_epi64(b1, b5);
    v[3] = _mm256_unpackhi_epi64(b1, b5);
    v[4] = _mm256_unpacklo_epi64(b2, b6);
    v[5] = _mm256_unpackhi_epi64(b2, b6);
    v[6] = _mm256_unpacklo_epi64(b3, b7);
    v[7] = _mm256_unpackhi_epi64(b3, b7);
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
///
/// # Safety
///
/// `ptr` must be valid for reads and writes of 256 `i16`s.
#[target_feature(enable = "avx2")]
unsafe fn transpose16(ptr: *mut i16) {
    let mut scratch = [0i16; RING_DEG];
    for half in 0..2 {
        // SAFETY: `8 * half + 7 < 16`, so every index is inside the 256-coefficient block.
        let mut v = unsafe {
            [
                ld(ptr, 8 * half),
                ld(ptr, 8 * half + 1),
                ld(ptr, 8 * half + 2),
                ld(ptr, 8 * half + 3),
                ld(ptr, 8 * half + 4),
                ld(ptr, 8 * half + 5),
                ld(ptr, 8 * half + 6),
                ld(ptr, 8 * half + 7),
            ]
        };
        inlane_transpose8(&mut v);
        for j in 0..8 {
            // SAFETY: as above, into a 256-`i16` scratch buffer.
            unsafe { st(scratch.as_mut_ptr(), 8 * half + j, v[j]) };
        }
    }

    for r in 0..8 {
        // SAFETY: `r < 8` and `8 + r < 16`, both in range for the block and the scratch buffer.
        unsafe {
            let a = ld(scratch.as_ptr(), r);
            let b = ld(scratch.as_ptr(), 8 + r);
            st(ptr, r, _mm256_permute2x128_si256(a, b, 0x20));
            st(ptr, 8 + r, _mm256_permute2x128_si256(a, b, 0x31));
        }
    }
}

// ---------------------------------------------------------------------------------------
// The transforms
// ---------------------------------------------------------------------------------------

/// In-place forward negacyclic NTT of one 256-coefficient block, modulo `p.q`.
///
/// # Safety
///
/// Requires AVX2. `ptr` must be valid for reads and writes of 256 `i16`s, whose values must be
/// centered residues, `|a| ≤ q/2`.
#[target_feature(enable = "avx2")]
unsafe fn ntt_block<const SECOND: bool>(ptr: *mut i16) {
    let p = prime::<SECOND>();
    let q = _mm256_set1_epi16(p.q);
    let bm = _mm256_set1_epi16(p.barrett_m);
    let round = _mm256_set1_epi16(1i16 << (BARRETT_SH - 1));

    // Levels with len ≥ 16: both halves of every butterfly are whole vectors, and ψ is constant
    // across a block, so it is simply broadcast.
    let mut k = 0usize;
    let mut half = 8usize; // len/16, the block half-width in vectors
    let mut level = 0usize;
    while half >= 1 {
        let mut start = 0usize;
        while start < 16 {
            k += 1;
            let z = _mm256_set1_epi16(p.zetas[k]);
            let zq = _mm256_set1_epi16(p.zetas_q[k]);
            let mut i = start;
            while i < start + half {
                // SAFETY: `i + half < 16` because `start + 2*half ≤ 16`.
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

    // Levels with len < 16: transpose so each lane owns a whole coefficient block, then four
    // more vertical levels with per-lane ψ.
    // SAFETY: `ptr` covers the whole block.
    unsafe { transpose16(ptr) };

    /// Applies one butterfly between two whole vectors of the transposed block, taking ψ from
    /// group `$h` of `$tbl`.
    macro_rules! vertical {
        ($fly:ident, $tbl:expr, $h:expr, $lo:expr, $hi:expr) => {
            // SAFETY: every vector index below is `< 16`, and the group index is in range for
            // its table; see the ψ-index derivation above the table definitions.
            unsafe {
                let (z, zq) = ld_tbl($tbl, $h);
                let mut lo = ld(ptr, $lo);
                let mut hi = ld(ptr, $hi);
                $fly(&mut lo, &mut hi, z, zq, q);
                st(ptr, $lo, lo);
                st(ptr, $hi, hi);
            }
        };
    }

    for j in 0..8 {
        vertical!(ct_butterfly, p.fwd8, 0, j, j + 8); // len = 8
    }
    for h in 0..2 {
        for j in 0..4 {
            vertical!(ct_butterfly, p.fwd4, h, 8 * h + j, 8 * h + j + 4); // len = 4
        }
    }
    for h in 0..4 {
        for j in 0..2 {
            vertical!(ct_butterfly, p.fwd2, h, 4 * h + j, 4 * h + j + 2); // len = 2
        }
    }
    // Three more levels of growth since the last Barrett; re-center again.
    // SAFETY: `ptr` covers the whole block.
    unsafe { barrett_block(ptr, bm, round, q) };
    for h in 0..8 {
        vertical!(ct_butterfly, p.fwd1, h, 2 * h, 2 * h + 1); // len = 1
    }

    // SAFETY: `ptr` covers the whole block.
    unsafe { transpose16(ptr) };

    // SAFETY: as above. Leaves every coefficient centered, |a| ≤ q/2.
    unsafe { barrett_block(ptr, bm, round, q) };
}

/// In-place inverse negacyclic NTT of one 256-coefficient block, including the final scaling
/// that undoes both the 1/256 and the Montgomery factor left by the pointwise step.
///
/// # Safety
///
/// Requires AVX2. `ptr` must be valid for reads and writes of 256 `i16`s, whose values must
/// satisfy `|a| < q`.
#[target_feature(enable = "avx2")]
unsafe fn invntt_block<const SECOND: bool>(ptr: *mut i16) {
    let p = prime::<SECOND>();
    let q = _mm256_set1_epi16(p.q);
    let bm = _mm256_set1_epi16(p.barrett_m);
    let round = _mm256_set1_epi16(1i16 << (BARRETT_SH - 1));

    // SAFETY: `ptr` covers the whole block.
    unsafe { transpose16(ptr) };

    macro_rules! vertical {
        ($tbl:expr, $h:expr, $lo:expr, $hi:expr) => {
            // SAFETY: as in `ntt_block`.
            unsafe {
                let (z, zq) = ld_tbl($tbl, $h);
                let mut lo = ld(ptr, $lo);
                let mut hi = ld(ptr, $hi);
                gs_butterfly(&mut lo, &mut hi, z, zq, q);
                st(ptr, $lo, lo);
                st(ptr, $hi, hi);
            }
        };
    }

    for h in 0..8 {
        vertical!(p.inv1, h, 2 * h, 2 * h + 1); // len = 1
    }
    for h in 0..4 {
        for j in 0..2 {
            vertical!(p.inv2, h, 4 * h + j, 4 * h + j + 2); // len = 2
        }
    }
    // The Gentleman-Sande sum path doubles per level; re-center every two levels so that both
    // `lo + hi` and `lo - hi` keep fitting a lane.
    // SAFETY: `ptr` covers the whole block.
    unsafe { barrett_block(ptr, bm, round, q) };
    for h in 0..2 {
        for j in 0..4 {
            vertical!(p.inv4, h, 8 * h + j, 8 * h + j + 4); // len = 4
        }
    }
    for j in 0..8 {
        vertical!(p.inv8, 0, j, j + 8); // len = 8
    }
    // SAFETY: `ptr` covers the whole block.
    unsafe { barrett_block(ptr, bm, round, q) };

    // SAFETY: `ptr` covers the whole block.
    unsafe { transpose16(ptr) };

    // Levels with len ≥ 16. `k` continues downward from where the transposed levels stopped:
    // they consumed 128 + 64 + 32 + 16 = 240 of the 256 ψ entries.
    let mut k = 16usize;
    let mut half = 1usize;
    while half < 16 {
        let mut start = 0usize;
        while start < 16 {
            k -= 1;
            // The table entries are centered, so |ψ| ≤ q/2 and the negation cannot overflow.
            let neg_zeta = p.zetas[k].wrapping_neg();
            let z = _mm256_set1_epi16(neg_zeta);
            let zq = _mm256_set1_epi16(neg_zeta.wrapping_mul(p.qinv));
            let mut i = start;
            while i < start + half {
                // SAFETY: `i + half < 16` because `start + 2*half ≤ 16`.
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
        half *= 2;
        // Two more levels since the last Barrett (the one closing the transposed section).
        if half == 4 {
            // SAFETY: `ptr` covers the whole block.
            unsafe { barrett_block(ptr, bm, round, q) };
        }
    }

    // One final Montgomery multiply undoes both the 1/256 and the Montgomery factor.
    let scale = _mm256_set1_epi16(p.invntt_scale);
    let scale_q = _mm256_set1_epi16(p.invntt_scale.wrapping_mul(p.qinv));
    for i in 0..16 {
        // SAFETY: `i < 16`.
        unsafe { st(ptr, i, mont_mul(ld(ptr, i), scale, scale_q, q)) };
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
/// Requires AVX2. `ptr` must be valid for writes of 256 `i16`s.
#[inline]
#[target_feature(enable = "avx2")]
unsafe fn split_and_transform<const SECOND: bool, const REDUCE: bool>(
    elem: &[u16; RING_DEG],
    ptr: *mut i16,
) {
    let p = prime::<SECOND>();
    let q = _mm256_set1_epi16(p.q);
    let bm = _mm256_set1_epi16(p.barrett_m);
    let round = _mm256_set1_epi16(1i16 << (BARRETT_SH - 1));
    for i in 0..16 {
        // SAFETY: `i < 16` is in range for both the 256-`u16` source and the block. Coefficients
        // below 2^13 fit an `i16` lane, so the Barrett reduction is in range; secret
        // coefficients need none, and the `i16` reinterpretation of the load is their sign
        // extension.
        unsafe {
            let x = _mm256_loadu_si256(elem.as_ptr().add(16 * i).cast());
            let x = if REDUCE {
                barrett(x, bm, round, q)
            } else {
                x
            };
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
/// Requires AVX2.
#[inline]
#[target_feature(enable = "avx2")]
unsafe fn from_ring_elem<const REDUCE: bool>(elem: &[u16; RING_DEG]) -> [i32; RING_DEG] {
    let mut out = [0i32; RING_DEG];
    let base = out.as_mut_ptr().cast::<i16>();
    // SAFETY: `out` is 256 `i32` = 512 `i16`, so the q₂ block starts at `i16` offset 256 and
    // both blocks are 256 `i16` long.
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
/// Requires AVX2.
#[target_feature(enable = "avx2")]
pub(crate) fn from_uniform(elem: &[u16; RING_DEG]) -> [i32; RING_DEG] {
    // SAFETY: the caller guarantees AVX2.
    unsafe { from_ring_elem::<true>(elem) }
}

/// Forward-transforms a CBD secret, reading each coefficient as the signed value it encodes
///
/// # Safety
///
/// Requires AVX2.
#[target_feature(enable = "avx2")]
pub(crate) fn from_secret(elem: &[u16; RING_DEG]) -> [i32; RING_DEG] {
    // SAFETY: the caller guarantees AVX2.
    unsafe { from_ring_elem::<false>(elem) }
}

/// Adds the pointwise product `lhs ∘ rhs` into an unreduced accumulator, per prime.
///
/// The accumulator's 256 `i64` are reinterpreted as two blocks of 256 `i32`, matching the two
/// residue blocks of the operands. Products of centered values are below (q/2 + 1)² and callers
/// accumulate at most 4 (= `MAX_L`) of them, so each lane stays under 1.2·10⁸ — well inside an
/// `i32`, and inside the 2^15·q input range of the Montgomery reduction that consumes it.
///
/// # Safety
///
/// Requires AVX2.
#[target_feature(enable = "avx2")]
pub(crate) fn pointwise_mul_acc(
    acc: &mut [i64; RING_DEG],
    lhs: &[i32; RING_DEG],
    rhs: &[i32; RING_DEG],
) {
    let acc_base = acc.as_mut_ptr().cast::<i32>();
    let lhs_base = lhs.as_ptr().cast::<i16>();
    let rhs_base = rhs.as_ptr().cast::<i16>();

    for block in 0..2 {
        // SAFETY: 256 `i64` are 512 `i32` and 256 `i32` are 512 `i16`, so both blocks are in
        // range for their respective buffers, as is every `i < 16` within a block.
        unsafe {
            let acc_ptr = acc_base.add(RING_DEG * block);
            let l_ptr = lhs_base.add(RING_DEG * block);
            let r_ptr = rhs_base.add(RING_DEG * block);

            for i in 0..16 {
                let l = ld(l_ptr, i);
                let r = ld(r_ptr, i);
                // The 32-bit products, as low and high halves re-joined by `vpunpck`: the low
                // unpack gives the products of lanes 0..4 and 8..12, the high one the rest.
                let lo = _mm256_mullo_epi16(l, r);
                let hi = _mm256_mulhi_epi16(l, r);
                let p0 = _mm256_unpacklo_epi16(lo, hi);
                let p1 = _mm256_unpackhi_epi16(lo, hi);
                // `vperm2i128` puts them back in coefficient order.
                let first = _mm256_permute2x128_si256(p0, p1, 0x20);
                let second = _mm256_permute2x128_si256(p0, p1, 0x31);

                let a0 = acc_ptr.add(16 * i).cast::<__m256i>();
                let a1 = acc_ptr.add(16 * i + 8).cast::<__m256i>();
                _mm256_storeu_si256(a0, _mm256_add_epi32(_mm256_loadu_si256(a0), first));
                _mm256_storeu_si256(a1, _mm256_add_epi32(_mm256_loadu_si256(a1), second));
            }
        }
    }
}

/// Montgomery-reduces one accumulator block into `i16` lanes, then inverse-transforms it
///
/// # Safety
///
/// Requires AVX2. `acc_ptr` must be valid for reads of 256 `i32`s and `ptr` for reads and
/// writes of 256 `i16`s.
#[inline]
#[target_feature(enable = "avx2")]
unsafe fn reduce_block<const SECOND: bool>(acc_ptr: *const i32, ptr: *mut i16) {
    let p = prime::<SECOND>();
    let q = _mm256_set1_epi16(p.q);
    let qinv = _mm256_set1_epi16(p.qinv);

    for i in 0..16 {
        // SAFETY: `i < 16` covers the 16 `i32` at `16i` and the 16 `i16` of output vector `i`.
        unsafe {
            let a0 = _mm256_loadu_si256(acc_ptr.add(16 * i).cast());
            let a1 = _mm256_loadu_si256(acc_ptr.add(16 * i + 8).cast());
            // Signed Montgomery reduction of an `i32` with R = 2^16. Both the sign-extended low
            // halves and the arithmetic-shifted high halves are already in `i16` range, so
            // `vpackssdw` is exact; the qword permute repairs its lane interleaving. As in
            // `mont_mul`, the low halves cancel, so subtracting the high halves is the whole
            // answer.
            let lo = _mm256_permute4x64_epi64::<0xD8>(_mm256_packs_epi32(
                _mm256_srai_epi32::<16>(_mm256_slli_epi32::<16>(a0)),
                _mm256_srai_epi32::<16>(_mm256_slli_epi32::<16>(a1)),
            ));
            let hi = _mm256_permute4x64_epi64::<0xD8>(_mm256_packs_epi32(
                _mm256_srai_epi32::<16>(a0),
                _mm256_srai_epi32::<16>(a1),
            ));
            let t = _mm256_mullo_epi16(lo, qinv);
            st(ptr, i, _mm256_sub_epi16(hi, _mm256_mulhi_epi16(t, q)));
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
/// Requires AVX2.
#[target_feature(enable = "avx2")]
pub(crate) fn reduce_invntt(acc: &[i64; RING_DEG]) -> [u16; RING_DEG] {
    let acc_base = acc.as_ptr().cast::<i32>();
    let mut v = [0i16; 2 * RING_DEG];

    // SAFETY: 256 `i64` are 512 `i32`, so both accumulator blocks are in range, as are both
    // halves of the 512-`i16` scratch buffer.
    unsafe {
        reduce_block::<false>(acc_base, v.as_mut_ptr());
        reduce_block::<true>(acc_base.add(RING_DEG), v.as_mut_ptr().add(RING_DEG));
    }

    // CRT reconstruction, by Garner: with a₁ = r₁ mod q₁ and a₂ = r₂ mod q₂ taken in [0, q),
    // the unique x ≡ rᵢ (mod qᵢ) in [0, q₁q₂) is a₁ + q₁·((a₂ − a₁)·q₁⁻¹ mod q₂). Subtracting
    // q₁q₂ above the midpoint centers it; truncating to 16 bits then gives the wrapping-`u16`
    // coefficient, exactly as `to_wrapping_u16` does for the single prime. This is exact
    // because the true product lies in (-q₁q₂/2, q₁q₂/2] — the bound in the module docs.
    let q1 = _mm256_set1_epi16(Q1);
    let q2 = _mm256_set1_epi16(Q2);
    let q1_inv_mont = _mm256_set1_epi16(CRT_Q1_INV_MONT);
    let q1_inv_mont_q = _mm256_set1_epi16(CRT_Q1_INV_MONT.wrapping_mul(Q2_INV));
    let q1_wide = _mm256_set1_epi32(Q1 as i32);
    let crt_q = _mm256_set1_epi32(CRT_Q);
    let crt_q_half = _mm256_set1_epi32(CRT_Q_HALF);
    let low16 = _mm256_set1_epi32(0xFFFF);

    /// Combines eight widened residue pairs into the low 16 bits of the centered product
    macro_rules! combine {
        ($a1:expr, $t:expr) => {{
            let x = _mm256_add_epi32($a1, _mm256_mullo_epi32($t, q1_wide));
            let over = _mm256_cmpgt_epi32(x, crt_q_half);
            _mm256_and_si256(_mm256_sub_epi32(x, _mm256_and_si256(crt_q, over)), low16)
        }};
    }

    let mut out = [0u16; RING_DEG];
    for i in 0..16 {
        // SAFETY: `i < 16` indexes both 256-coefficient residue blocks of the scratch buffer and
        // the 16 `u16` at `out[16i..16i + 16]`.
        unsafe {
            let r1 = ld(v.as_ptr(), i);
            let r2 = ld(v.as_ptr().add(RING_DEG), i);

            // Canonicalize both residues to [0, q) by adding q where negative.
            let a1 = _mm256_add_epi16(r1, _mm256_and_si256(_mm256_srai_epi16::<15>(r1), q1));
            let a2 = _mm256_add_epi16(r2, _mm256_and_si256(_mm256_srai_epi16::<15>(r2), q2));

            // t = (a₂ − a₁)·q₁⁻¹ mod q₂, centered, then canonicalized to [0, q₂).
            let t = mont_mul(_mm256_sub_epi16(a2, a1), q1_inv_mont, q1_inv_mont_q, q2);
            let t = _mm256_add_epi16(t, _mm256_and_si256(_mm256_srai_epi16::<15>(t), q2));

            // a₁ + q₁·t needs 32 bits, so widen the two 128-bit halves separately. Both
            // operands are non-negative and below their prime, so zero extension is right.
            let first = combine!(
                _mm256_cvtepu16_epi32(_mm256_castsi256_si128(a1)),
                _mm256_cvtepu16_epi32(_mm256_castsi256_si128(t))
            );
            let second = combine!(
                _mm256_cvtepu16_epi32(_mm256_extracti128_si256::<1>(a1)),
                _mm256_cvtepu16_epi32(_mm256_extracti128_si256::<1>(t))
            );

            // Both inputs are masked to 16 bits, so the unsigned saturating pack is exact; the
            // qword permute repairs the lane interleaving `vpackusdw` introduces.
            let packed = _mm256_permute4x64_epi64::<0xD8>(_mm256_packus_epi32(first, second));
            _mm256_storeu_si256(out.as_mut_ptr().add(16 * i).cast(), packed);
        }
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
    fn crt_literal_constants_are_correct() {
        assert_eq!(CRT_Q, Q1 as i32 * Q2 as i32);
        assert_eq!(CRT_Q_HALF, CRT_Q / 2);
        // Each q⁻¹ really inverts q mod 2^16.
        assert_eq!((Q1 as u16).wrapping_mul(Q1_INV as u16), 1);
        assert_eq!((Q2 as u16).wrapping_mul(Q2_INV as u16), 1);
        // The Barrett multipliers are round(2^(16+SH) / q).
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
    fn crt_zetas_tables_are_correct() {
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
                assert_eq!((z as i64).rem_euclid(q as i64) as u64, expected, "ZETAS[{k}]");
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

    // The transposed levels are only correct if `transpose16` really does put coefficient
    // block `m` in lane `m` — and if applying it twice gets back to coefficient order.
    #[allow(unsafe_code)]
    #[test]
    fn transpose16_permutes_as_documented() {
        if !super::super::available() {
            return;
        }

        let mut a: [i16; RING_DEG] = core::array::from_fn(|i| i as i16);
        // SAFETY: `available()` returned true, and `a` is exactly 256 `i16`.
        unsafe { transpose16(a.as_mut_ptr()) };

        // Vector `k` lane `m` — linear index 16k + m — must now hold coefficient 16m + k.
        for k in 0..16 {
            for m in 0..16 {
                assert_eq!(a[16 * k + m], (16 * m + k) as i16, "vector {k} lane {m}");
            }
        }

        // SAFETY: as above.
        unsafe { transpose16(a.as_mut_ptr()) };
        for i in 0..RING_DEG {
            assert_eq!(a[i], i as i16, "transposing twice is the identity");
        }
    }
}
