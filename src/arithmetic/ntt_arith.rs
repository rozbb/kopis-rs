//! This file defines NTT-domain data structures and arithmetic
//!
//! This module owns the NTT-domain types — [`NttElem`], [`NttMatrix`] and the pointwise
//! accumulator — and the four entry points the rest of the crate goes through. The arithmetic
//! underneath them lives elsewhere: [`crate::arithmetic::ntt_crt`] portably, or a vector backend
//! when the CPU has one. All of those transform over two 16-bit primes combined by the CRT.
//!
//! # Why the products come out exact
//!
//! Every ring multiplication in Kopis has one operand with small coefficients: a CBD secret with
//! coefficients in [-μ/2, μ/2]. The other operand has coefficients in [0, 2^13). The
//! coefficients of the *exact integer* product of such polynomials — even accumulated over an
//! ℓ-term matrix-vector product — are bounded in magnitude by
//!     ℓ · 256 · (2^13 - 1) · (μ/2) ≤ 3 · 256 · 8191 · 4 = 25_162_752,
//! the maximum over all three parameter sets. Every modulus the transforms work over is picked
//! so that this bound fits strictly inside it, so the product can be computed exactly: do the
//! arithmetic mod that modulus, lift to the centered representative, and reduce mod 2^16. The
//! result is bit-identical to schoolbook multiplication of the wrapping-u16 ring elements, which
//! is what the tests below check it against.
//!
//! Each prime is ≡ 1 (mod 512), so ℤ/q has a primitive 512th root of unity ψ and X^256 + 1
//! splits completely: a full 8-level negacyclic NTT applies, and products of transformed
//! elements are plain pointwise products. Each entry of a matrix-vector product then costs one
//! pointwise multiply-accumulate instead of a full ring multiplication, and the transforms are
//! shared across rows and columns. Callers cache fixed operands (the matrix A, the public vector
//! b, the secret s) in NTT form.

// The explicit `for i in 0..N` index loops that trigger this lint are deliberate: aeneas (the
// Lean extractor) handles them better than the iterator patterns clippy suggests
#![allow(clippy::needless_range_loop)]

use crate::{
    arithmetic::{Matrix, RingElem},
    consts::RING_DEG,
};

use zeroize::Zeroize;

/// A ring element in the NTT domain. Coefficients are centered mod-q values, |·| ≤ q/2 + 41.
#[derive(Clone, Copy, Zeroize)]
pub(crate) struct NttElem(pub(crate) [i16; 2 * RING_DEG]);

impl Default for NttElem {
    fn default() -> Self {
        NttElem([0i16; 2 * RING_DEG])
    }
}

/// The unreduced pointwise accumulator: one `i32` per residue lane, split into the same two
/// blocks as [`NttElem`].
pub(crate) type Acc = [i32; 2 * RING_DEG];

/// A zeroed accumulator
pub(crate) const ACC_ZERO: Acc = [0i32; 2 * RING_DEG];

impl NttElem {
    /// Forward-transforms a ring element to the NTT domain. The coefficients MUST be in
    /// [0, 2^13).
    pub(crate) fn from_uniform(elem: &RingElem) -> Self {
        #[cfg(kopis_avx2)]
        #[allow(unsafe_code)]
        if crate::backend::avx2_available() {
            // SAFETY: `avx2_available()` has just confirmed this CPU supports AVX2, which is
            // the whole of the backend's precondition.
            return NttElem(unsafe { crate::backend::avx2::ntt::from_uniform(&elem.0) });
        }

        #[cfg(kopis_neon)]
        #[allow(unsafe_code)]
        if crate::backend::neon_available() {
            // SAFETY: `neon_available()` has just confirmed this CPU supports NEON, which is
            // the whole of the backend's precondition.
            return NttElem(unsafe { crate::backend::neon::ntt::from_uniform(&elem.0) });
        }

        NttElem(crate::arithmetic::ntt_crt::from_uniform(&elem.0))
    }

    /// Forward-transforms a CBD secret, interpreting each wrapping-u16 coefficient as the
    /// signed value it represents (e.g. 0xFFFB is -5).
    ///
    /// As with [`NttElem::from_uniform`], the bound on the coefficients — here |·| ≤ μ/2 — is
    /// a proof-side precondition rather than a runtime check.
    pub(crate) fn from_secret(elem: &RingElem) -> Self {
        #[cfg(kopis_avx2)]
        #[allow(unsafe_code)]
        if crate::backend::avx2_available() {
            // SAFETY: as in `from_uniform`.
            return NttElem(unsafe { crate::backend::avx2::ntt::from_secret(&elem.0) });
        }

        #[cfg(kopis_neon)]
        #[allow(unsafe_code)]
        if crate::backend::neon_available() {
            // SAFETY: as in `from_uniform`.
            return NttElem(unsafe { crate::backend::neon::ntt::from_secret(&elem.0) });
        }

        NttElem(crate::arithmetic::ntt_crt::from_secret(&elem.0))
    }
}

/// A matrix of NTT-domain ring elements, stored in row-major order like [`Matrix`]
#[derive(Clone, Zeroize)]
pub(crate) struct NttMatrix<const X: usize, const Y: usize>(pub(crate) [[NttElem; Y]; X]);

impl<const X: usize, const Y: usize> Default for NttMatrix<X, Y> {
    fn default() -> Self {
        NttMatrix([[NttElem::default(); Y]; X])
    }
}

/// Adds the pointwise product lhs ∘ rhs into the i64 accumulator, without reducing.
///
/// Products of centered values are below (p/2 + 41)² and callers accumulate at most 4 (= MAX_L)
/// of them, so the accumulator stays below 4·(p/2 + 41)² ≈ 2.54·10^15 < 2^52, comfortably
/// within Montgomery reduction's valid input range of 2^31 · p.
pub(crate) fn pointwise_mul_acc(acc: &mut Acc, lhs: &NttElem, rhs: &NttElem) {
    #[cfg(kopis_avx2)]
    #[allow(unsafe_code)]
    if crate::backend::avx2_available() {
        // SAFETY: as in `NttElem::from_uniform`.
        unsafe { crate::backend::avx2::ntt::pointwise_mul_acc(acc, &lhs.0, &rhs.0) };
        return;
    }

    #[cfg(kopis_neon)]
    #[allow(unsafe_code)]
    if crate::backend::neon_available() {
        // SAFETY: as in `NttElem::from_uniform`.
        unsafe { crate::backend::neon::ntt::pointwise_mul_acc(acc, &lhs.0, &rhs.0) };
        return;
    }

    crate::arithmetic::ntt_crt::pointwise_mul_acc(acc, &lhs.0, &rhs.0)
}

/// Montgomery-reduces an accumulator of pointwise products, inverse-transforms it, and returns
/// the coefficient-domain result as a wrapping-u16 ring element.
pub(crate) fn reduce_invntt_to_ring_elem(acc: &Acc) -> RingElem {
    #[cfg(kopis_avx2)]
    #[allow(unsafe_code)]
    if crate::backend::avx2_available() {
        // SAFETY: as in `NttElem::from_uniform`.
        return RingElem(unsafe { crate::backend::avx2::ntt::reduce_invntt(acc) });
    }

    #[cfg(kopis_neon)]
    #[allow(unsafe_code)]
    if crate::backend::neon_available() {
        // SAFETY: as in `NttElem::from_uniform`.
        return RingElem(unsafe { crate::backend::neon::ntt::reduce_invntt(acc) });
    }

    RingElem(crate::arithmetic::ntt_crt::reduce_invntt(acc))
}

impl<const X: usize, const Y: usize> NttMatrix<X, Y> {
    /// Forward-transforms a matrix of uniform (≤ 13-bit) ring elements, entry by entry
    pub(crate) fn from_uniform_matrix(mat: &Matrix<X, Y>) -> Self {
        let mut ret = NttMatrix::default();
        for i in 0..X {
            for j in 0..Y {
                ret.0[i][j] = NttElem::from_uniform(&mat.0[i][j]);
            }
        }
        ret
    }

    /// Forward-transforms a matrix of CBD secrets, entry by entry
    pub(crate) fn from_secret_matrix(mat: &Matrix<X, Y>) -> Self {
        let mut ret = NttMatrix::default();
        for i in 0..X {
            for j in 0..Y {
                ret.0[i][j] = NttElem::from_secret(&mat.0[i][j]);
            }
        }
        ret
    }

    /// Multiplies two NTT-domain matrices, returning the result in the coefficient domain.
    /// Equivalent to schoolbook multiplication of the corresponding coefficient-domain matrices.
    pub(crate) fn mul<const Z: usize>(&self, other: &NttMatrix<Y, Z>) -> Matrix<X, Z> {
        // The inner dimension bounds the pointwise accumulator (see pointwise_mul_acc)
        debug_assert!(Y <= crate::consts::MAX_L);

        let mut result = Matrix::default();
        for i in 0..X {
            for k in 0..Z {
                let mut acc = ACC_ZERO;
                for j in 0..Y {
                    pointwise_mul_acc(&mut acc, &self.0[i][j], &other.0[j][k]);
                }
                result.0[i][k] = reduce_invntt_to_ring_elem(&acc);
            }
        }
        result
    }

    /// Multiplies the transpose of this NTT-domain matrix by another, returning the result in
    /// the coefficient domain. Equivalent to schoolbook multiplication by the transpose.
    pub(crate) fn mul_transpose<const Z: usize>(&self, other: &NttMatrix<X, Z>) -> Matrix<Y, Z> {
        // The inner dimension bounds the pointwise accumulator (see pointwise_mul_acc)
        debug_assert!(X <= crate::consts::MAX_L);

        let mut result = Matrix::default();
        for j in 0..Y {
            for k in 0..Z {
                let mut acc = ACC_ZERO;
                for i in 0..X {
                    pointwise_mul_acc(&mut acc, &self.0[i][j], &other.0[i][k]);
                }
                result.0[j][k] = reduce_invntt_to_ring_elem(&acc);
            }
        }
        result
    }
}

#[cfg(test)]
mod test {
    use super::*;

    use rand::{RngExt, rng};

    /// A random CBD-like secret: wrapping-u16 coefficients in [-mu/2, mu/2]
    fn rand_secret(rng: &mut impl RngExt, half_mu: u16) -> RingElem {
        let mut ret = RingElem::default();
        for coeff in ret.0.iter_mut() {
            *coeff = rng.random_range(0..=2 * half_mu).wrapping_sub(half_mu);
        }
        ret
    }

    /// A random uniform ring element with `bits`-bit coefficients
    fn rand_uniform(rng: &mut impl RngExt, bits: usize) -> RingElem {
        let mut ret = RingElem::default();
        for coeff in ret.0.iter_mut() {
            *coeff = rng.random_range(0..(1u16 << bits));
        }
        ret
    }

    // Multiplying by the polynomial "1" via the NTT pipeline must return the input unchanged
    #[test]
    fn mul_by_one_roundtrip() {
        let mut rng = rng();
        for _ in 0..50 {
            let a = rand_uniform(&mut rng, 13);
            let mut one = RingElem::default();
            one.0[0] = 1;

            let a_ntt = NttMatrix::<1, 1>([[NttElem::from_uniform(&a)]]);
            let one_ntt = NttMatrix::<1, 1>([[NttElem::from_secret(&one)]]);
            let prod = a_ntt.mul(&one_ntt);
            assert_eq!(prod.0[0][0], a);
        }
    }

    /// Naive schoolbook multiply-accumulate directly in Z[X]/(X^256+1): adds `a·b` into `acc`.
    /// O(n²) with explicit ring reduction — the simplest correct implementation, and the
    /// reference every product in this module is checked against.
    fn schoolbook_ring_mul_acc(acc: &mut RingElem, a: &RingElem, b: &RingElem) {
        for i in 0..RING_DEG {
            for j in 0..RING_DEG {
                let prod = a.0[i].wrapping_mul(b.0[j]);
                let idx = i + j;
                if idx < RING_DEG {
                    acc.0[idx] = acc.0[idx].wrapping_add(prod);
                } else {
                    // X^256 = -1 in our ring, so wrap and negate
                    acc.0[idx - RING_DEG] = acc.0[idx - RING_DEG].wrapping_sub(prod);
                }
            }
        }
    }

    /// Schoolbook `a · b`, entry by entry
    fn schoolbook_mul<const X: usize, const Y: usize, const Z: usize>(
        a: &Matrix<X, Y>,
        b: &Matrix<Y, Z>,
    ) -> Matrix<X, Z> {
        let mut result = Matrix::default();
        for i in 0..X {
            for j in 0..Y {
                for k in 0..Z {
                    schoolbook_ring_mul_acc(&mut result.0[i][k], &a.0[i][j], &b.0[j][k]);
                }
            }
        }
        result
    }

    /// Schoolbook `aᵀ · b`, entry by entry
    fn schoolbook_mul_transpose<const X: usize, const Y: usize, const Z: usize>(
        a: &Matrix<X, Y>,
        b: &Matrix<X, Z>,
    ) -> Matrix<Y, Z> {
        let mut result = Matrix::default();
        for i in 0..X {
            for j in 0..Y {
                for k in 0..Z {
                    schoolbook_ring_mul_acc(&mut result.0[j][k], &a.0[i][j], &b.0[i][k]);
                }
            }
        }
        result
    }

    // One NTT-domain ring product must match naive schoolbook multiplication in
    // Z[X]/(X^256 + 1). `matches_schoolbook` below covers the matrix layer on top of this.
    #[test]
    fn ring_mul_matches_schoolbook() {
        let mut rng = rng();
        // One secret range per parameter set, as in `matches_schoolbook`
        for half_mu in [5u16, 4, 3] {
            for _ in 0..20 {
                let a = rand_uniform(&mut rng, 13);
                let s = rand_secret(&mut rng, half_mu);

                let a_ntt = NttMatrix::<1, 1>([[NttElem::from_uniform(&a)]]);
                let s_ntt = NttMatrix::<1, 1>([[NttElem::from_secret(&s)]]);

                let mut expected = RingElem::default();
                schoolbook_ring_mul_acc(&mut expected, &a, &s);

                assert_eq!(a_ntt.mul(&s_ntt).0[0][0], expected);
            }
        }
    }

    // NTT-domain matrix products must match the schoolbook matrix products exactly, for the
    // shapes and operand ranges of all three parameter sets
    #[test]
    fn matches_schoolbook() {
        fn check<const L: usize>(half_mu: u16) {
            let mut rng = rng();
            for _ in 0..20 {
                // A is L×L uniform 13-bit, b is L×1 uniform 10-bit, s is an L×1 secret
                let mut mat_a = Matrix::<L, L>::default();
                for row in mat_a.0.iter_mut() {
                    for entry in row.iter_mut() {
                        *entry = rand_uniform(&mut rng, 13);
                    }
                }
                let mut vec_b = Matrix::<L, 1>::default();
                let mut vec_s = Matrix::<L, 1>::default();
                for i in 0..L {
                    vec_b.0[i][0] = rand_uniform(&mut rng, 10);
                    vec_s.0[i][0] = rand_secret(&mut rng, half_mu);
                }

                let a_ntt = NttMatrix::from_uniform_matrix(&mat_a);
                let b_ntt = NttMatrix::from_uniform_matrix(&vec_b);
                let s_ntt = NttMatrix::from_secret_matrix(&vec_s);

                assert_eq!(a_ntt.mul(&s_ntt), schoolbook_mul(&mat_a, &vec_s));
                assert_eq!(
                    a_ntt.mul_transpose(&s_ntt),
                    schoolbook_mul_transpose(&mat_a, &vec_s)
                );
                assert_eq!(
                    b_ntt.mul_transpose(&s_ntt),
                    schoolbook_mul_transpose(&vec_b, &vec_s)
                );
            }
        }

        check::<2>(5); // kopis512: L=2, mu=10
        check::<3>(4); // kopis768: L=3, mu=8
        check::<4>(3); // kopis1024: L=4, mu=6
    }

    // The worst-case accumulated product coefficient over all parameter sets is exactly
    // L·256·8191·(μ/2) = 25_162_752 (L=3, μ=8), just under p/2. Hit it exactly: with
    // a_i = 8191 for all i, s_0 = μ/2, and s_j = -μ/2 for j > 0, coefficient 0 of a·s is
    // Σ_i 8191·(μ/2) = 256·8191·(μ/2), and the matrix product accumulates it L times.
    #[test]
    fn extremal_coefficients() {
        // Every parameter set, since each has its own (ℓ, μ/2) and so its own accumulator
        // bound: the product grows with ℓ·(μ/2), and it is that bound the CRT reconstruction
        // has to stay exact within.
        check_extremal::<{ crate::consts::KOPIS512_L }, { crate::consts::KOPIS512_MU }>();
        check_extremal::<{ crate::consts::KOPIS768_L }, { crate::consts::KOPIS768_MU }>();
        check_extremal::<{ crate::consts::KOPIS1024_L }, { crate::consts::KOPIS1024_MU }>();
    }

    /// Drives the worst case for one parameter set: every uniform coefficient at its maximum
    /// 2^13 − 1, and every secret coefficient at −μ/2 (the largest magnitude the CBD produces)
    /// except one at +μ/2, so the accumulated product reaches the top of its range.
    fn check_extremal<const L: usize, const MU: usize>() {
        let half_mu = (MU / 2) as u16;

        let mut mat_a = Matrix::<L, L>::default();
        for row in mat_a.0.iter_mut() {
            for entry in row.iter_mut() {
                *entry = RingElem([8191u16; RING_DEG]);
            }
        }
        let mut vec_s = Matrix::<L, 1>::default();
        for i in 0..L {
            let mut s = RingElem([0u16.wrapping_sub(half_mu); RING_DEG]);
            s.0[0] = half_mu;
            vec_s.0[i][0] = s;
        }

        let a_ntt = NttMatrix::from_uniform_matrix(&mat_a);
        let s_ntt = NttMatrix::from_secret_matrix(&vec_s);

        // Schoolbook multiplication over the wrapping-u16 ring is an exact integer reference,
        // independent of either transform.
        assert_eq!(
            a_ntt.mul(&s_ntt),
            schoolbook_mul(&mat_a, &vec_s),
            "mul, L={L} MU={MU}"
        );
        assert_eq!(
            a_ntt.mul_transpose(&s_ntt),
            schoolbook_mul_transpose(&mat_a, &vec_s),
            "mul_transpose, L={L} MU={MU}"
        );
    }

    // Neither vector backend shares any code with the portable transform, but both work over
    // the same two 16-bit primes, so the endpoints must agree exactly: feeding the same ring
    // elements through both routes has to produce the very same coefficients. Check that over
    // the accumulator shape of every parameter set, since those shapes are what keep the product
    // inside the bound the CRT reconstruction is exact within.
    #[allow(unused_macros)]
    macro_rules! backend_matches_serial {
        ($name:ident, $backend:path) => {
            #[allow(unsafe_code)]
            #[test]
            fn $name() {
                use crate::arithmetic::ntt_crt;
                use $backend as backend;

                if !backend::available() {
                    return;
                }
                let mut rng = rng();

                // (ℓ, μ/2) for kopis512, kopis768 and kopis1024
                for (ell, half_mu) in [(2usize, 5u16), (3, 4), (4, 3)] {
                    for _ in 0..100 {
                        let uniform = rand_uniform(&mut rng, 13);
                        let secret = rand_secret(&mut rng, half_mu);

                        // The portable route: transform, accumulate ℓ products, reduce, invert.
                        // Safe code, so it stays outside the `unsafe` block below — a serial
                        // build is `forbid(unsafe_code)`.
                        let serial_packed = {
                            let u = ntt_crt::from_uniform(&uniform.0);
                            let s = ntt_crt::from_secret(&secret.0);
                            let mut acc = [0i32; 2 * RING_DEG];
                            for _ in 0..ell {
                                ntt_crt::pointwise_mul_acc(&mut acc, &u, &s);
                            }
                            ntt_crt::reduce_invntt(&acc)
                        };

                        // The same journey through the vector backend.
                        // SAFETY: `available()` returned true just above.
                        let vector_packed = unsafe {
                            let u = backend::ntt::from_uniform(&uniform.0);
                            let s = backend::ntt::from_secret(&secret.0);
                            let mut acc = [0i32; 2 * RING_DEG];
                            for _ in 0..ell {
                                backend::ntt::pointwise_mul_acc(&mut acc, &u, &s);
                            }
                            backend::ntt::reduce_invntt(&acc)
                        };

                        assert_eq!(serial_packed, vector_packed, "two-prime pipeline, ℓ={ell}");
                    }
                }
            }
        };
    }

    #[cfg(kopis_avx2)]
    backend_matches_serial!(avx2_matches_serial, crate::backend::avx2);

    #[cfg(kopis_neon)]
    backend_matches_serial!(neon_matches_serial, crate::backend::neon);
}
