//! The two-prime NTT scheme every backend uses.
//!
//! Rather than one 26-bit prime in `i32` lanes, the transform runs twice in `i16` lanes, over
//! q₁ = 7681 and q₂ = 10753, and the exact integer product is reconstructed from the two
//! residues. This is the arrangement Chung, Hwang, Kannwischer, Seiler, Shih and Yang use for
//! Saber on AVX2 (TCHES 2021, §4.2). [`crate::arithmetic::ntt_crt`] is the portable
//! implementation; [`crate::backend::avx2::ntt`] and [`crate::backend::neon::ntt`] are the
//! vector ones.
//!
//! Everything here is the part of that scheme which does not depend on the instruction set: the
//! moduli, the Montgomery and Barrett constants, the ψ tables, and the correctness argument.
//! The portable transform reads them directly. Each vector backend additionally supplies its own
//! intrinsics and its own *per-lane* ψ tables, whose shape depends on how many coefficients fit
//! a vector — 16 for AVX2, 8 for NEON — and so cannot be shared.
//!
//! # Why two primes
//!
//! No ISA here has a 32-bit high-multiply as cheap as its 16-bit one. AVX2 has `vpmulhw` over
//! 16 lanes but nothing equivalent for 32 bits, so a single-prime Montgomery multiply has to be
//! built from `vpmuldq` (four even lanes) plus a `vpshufd` to reach the odd ones. AArch64 has
//! `sqdmulh` at both widths, but the single-prime code reached for widening `vmull_s32`, which
//! covers two lanes per instruction against `vmulhq_s16`'s eight. Baseline SSE2, which is what
//! the portable code is compiled to on x86-64, has no 64-bit multiply at all and has to emulate
//! the single-prime product outright. Either way, two 16-bit transforms cost fewer multiplies
//! per coefficient than one 32-bit transform.
//!
//! What this trade needs is not a vector *unit* but a vector *lane*: it pays wherever 16-bit
//! SIMD is what the multiply lands on, which on the portable path means wherever LLVM
//! auto-vectorizes. On a genuinely scalar core a 32×32→64 multiply costs the same as a
//! 16×16→32 one, so doubling the transforms would just double the work; see
//! [`crate::arithmetic::ntt_crt`] for the measurements and for what a scalar target would want
//! instead.
//!
//! # Correctness
//!
//! q₁·q₂ = 82_593_793, so the centered range ±41_296_896 covers the exactness bound
//! ℓ·256·(2^13 − 1)·(μ/2) ≤ 25_162_752 that [`crate::arithmetic::ntt`] establishes, with
//! 16_134_144 to spare. Both primes are 1 mod 512, so X^256 + 1 splits completely over each and
//! the same complete 8-layer transform applies, with the same ψ-table layout and the same
//! Cooley-Tukey / Gentleman-Sande structure as the serial code.
//!
//! Only the endpoints of the pipeline agree with the portable code — the NTT-domain values are
//! different integers entirely — so the backends are checked end to end by `avx2_matches_serial`
//! and `neon_matches_serial` in [`crate::arithmetic::ntt`] rather than stage by stage.
//!
//! # Growth
//!
//! An `i16` lane holds only 3.05·q₂, against the 42.7·p an `i32` lane holds for the portable
//! prime, so both transforms need interior reductions where the single-prime code needs almost
//! none. The bounds, taken over the worst case q₂ = 10753:
//!
//! * Forward: inputs are centered, |a| ≤ q/2, and a Cooley-Tukey level adds at most 0.75q per
//!   level under the crude per-level budget. The two backends place their interior passes
//!   *differently*. NEON re-centers after levels 3 and 6 plus a final pass (runs of 3, 3, 2),
//!   which the crude budget covers: three levels reach at most 2.75q < 3.05q. AVX2 re-centers
//!   after levels 3 and 7 plus a final pass (runs of 3, 4, 1), and the crude budget does *not*
//!   cover a four-level run — it predicts 3.5q > 3.05q. AVX2's schedule is safe anyway
//!   because the ψ magnitudes at its levels 4–7 are small enough: interval propagation with
//!   the actual per-butterfly ψ values bounds the worst AVX2 lane below 30_700 of 32_767
//!   (NEON's below 23_700). Anyone reordering the reductions or regenerating the ψ tables must
//!   redo that propagation; the per-level budget alone does not justify the AVX2 schedule.
//! * Inverse: the Gentleman-Sande sum path doubles per level and both `lo ± hi` must fit, so
//!   the usable bound is 1.52q. Starting under 0.7q, two levels reach 2.66q — as a *sum*,
//!   which fits — and a Barrett pass after the second, fourth and sixth levels keeps it there.
//!   The last two levels end at 2.0q, which the final Montgomery scaling brings back under q.
//!   Both backends follow this inverse schedule.
//!
//! Every one of those sites was checked against the `i16` range by the scalar model these
//! constants were generated with, on random and extremal inputs for all three parameter sets;
//! the worst lane value observed in those runs was 20411 of 32767 (the certified worst-case
//! bounds above are higher because they quantify over all possible inputs).

// ---------------------------------------------------------------------------------------
// Constants, generated and checked by the scalar model described above: both primes prime and
// 1 mod 512, both Barrett constants verified exhaustively over the whole i16 input range, and
// the CRT reconstruction verified against exact integer arithmetic.
// ---------------------------------------------------------------------------------------

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
/// The Barrett shift, shared by both primes. q₁ cannot go higher without its multiplier leaving
/// an `i16` lane, and q₂ reaches the same `|r| ≤ q/2` at 11 as it does at 12, so one value
/// serves both. That it *is* shared matters for more than tidiness: on both backends the shift
/// is an instruction immediate, so a per-prime value would make every function that reduces a
/// const generic and monomorphize the whole transform twice.
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
/// Montgomery form: `ZETAS_Q1[k] = ψ₁^brv8(k) · 2^16 mod q₁`, centered. Same layout as
/// [`crate::arithmetic::ntt::ZETAS`]; the `zetas_tables_are_correct` test recomputes both
/// tables from ψ and checks every entry.
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

// ---------------------------------------------------------------------------------------
// The per-prime parameters, as one accessor each.
//
// Everything a transform needs for one of the two primes that is not instruction-set specific,
// so each backend's level loops can be written once and specialized per prime. The Barrett
// shift is deliberately absent: it is an instruction immediate, so it lives as `BARRETT_SH`,
// shared by both primes precisely so that it need not be a const generic.
//
// `SECOND` is a const generic rather than a `&Prime` parameter so that each monomorphization
// constant-folds the modulus, the Montgomery constant and the ψ-table addresses into the
// instruction stream. Specializing measurably beats sharing one copy between the primes, even
// though it doubles the instruction footprint of the transforms.
//
// These return values rather than a `&'static Prime` because a function that *returns* a
// reference to a static is one of the things aeneas cannot translate (it fails with
// `Unreachable` at the first field read); reading a static inside a function is fine. Each of
// these still folds to a constant, or to one load from a fixed address, per monomorphization.
// ---------------------------------------------------------------------------------------

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
