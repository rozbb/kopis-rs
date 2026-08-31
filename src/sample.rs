//! This file implements methods for generating uniform matrices and binomially distributed vectors

use crate::{
    arithmetic::{Matrix, RingElem},
    consts::{DOMSEP_GENMAT, DOMSEP_GENSEC, MAX_MU, RING_DEG},
};

use turboshake::digest::{ExtendableOutput, Update, XofReader};
use turboshake::{CTurboShake128, CTurboShake256};

/// One CBD coefficient: popcount of the low `half_mu` bits of `raw`, minus popcount of
/// the next `half_mu` bits
///
/// This is a standalone function because aeneas doesn't like when it's a lambda inside a
/// const-generic function.
fn cbd_diff(raw: u16, half_mu: u32) -> u16 {
    let mask = (1 << half_mu) - 1;
    let a = (raw & mask).count_ones() as u16;
    let b = ((raw >> half_mu) & mask).count_ones() as u16;
    a.wrapping_sub(b)
}

/// Computes the Centered Binomial Distribution using the given bytes as randomness
pub(crate) fn cbd<const MU: usize>(buf: &[u8], out: &mut RingElem) {
    assert_eq!(buf.len(), RING_DEG * MU / 8);

    // We optimize sampling based on MU
    if MU == 8 {
        // Each coefficient uses exactly 1 byte, with the low nibble as the positive half
        // and the high nibble as the negative half. So we don't need a buffer to read
        // bits
        for (i, &byte) in buf.iter().enumerate() {
            let a = (byte & 0x0F).count_ones() as u16;
            let b = (byte >> 4).count_ones() as u16;
            out.0[i] = a.wrapping_sub(b);
        }
    } else if MU == 10 {
        // 4 coefficients per 5-byte group. Coefficient k of a group occupies bits [10k,
        // 10k+10), which always fit in the two bytes starting at byte 10k/8. The low 5
        // bits are the positive half and the next 5 bits are the negative half.
        for g in 0..RING_DEG / 4 {
            let i = 5 * g;
            let b0 = buf[i] as u16;
            let b1 = buf[i + 1] as u16;
            let b2 = buf[i + 2] as u16;
            let b3 = buf[i + 3] as u16;
            let b4 = buf[i + 4] as u16;

            let o = 4 * g;
            let half_mu = (MU / 2) as u32;

            out.0[o] = cbd_diff(b0 | (b1 << 8), half_mu);
            out.0[o + 1] = cbd_diff((b1 | (b2 << 8)) >> 2, half_mu);
            out.0[o + 2] = cbd_diff((b2 | (b3 << 8)) >> 4, half_mu);
            out.0[o + 3] = cbd_diff((b3 | (b4 << 8)) >> 6, half_mu);
        }
    } else if MU == 6 {
        // 4 coefficients per 3-byte group. Coefficient k of a group occupies bits [6k,
        // 6k+6). The low 3 bits are the positive half, the next 3 the negative half.
        for g in 0..RING_DEG / 4 {
            let i = 3 * g;
            let b0 = buf[i] as u16;
            let b1 = buf[i + 1] as u16;
            let b2 = buf[i + 2] as u16;

            let o = 4 * g;
            let half_mu = (MU / 2) as u32;

            out.0[o] = cbd_diff(b0, half_mu);
            out.0[o + 1] = cbd_diff((b0 | (b1 << 8)) >> 6, half_mu);
            out.0[o + 2] = cbd_diff((b1 | (b2 << 8)) >> 4, half_mu);
            out.0[o + 3] = cbd_diff(b2 >> 2, half_mu);
        }
    } else {
        panic!("Invalid μ value {MU}");
    }
}

/// Uses a random seed to generate an MLWR secret, i.e., an element in R^ℓ whose entries are
/// sampled according to a binomial distribution.
pub(crate) fn gen_secret_from_seed<const L: usize, const MU: usize>(
    seed: &[u8; 32],
) -> Matrix<L, 1> {
    // ℓ ≤ 4 for every parameter set, so the whole vector is one four-lane XOF batch.
    #[cfg(kopis_avx2)]
    #[allow(unsafe_code)]
    if crate::backend::avx2_available() {
        // SAFETY: `avx2_available()` has just confirmed this CPU supports AVX2.
        return unsafe { crate::backend::avx2::sample::gen_secret_from_seed::<L, MU>(seed) };
    }

    // The same, two lanes at a time, where NEON has the SHA3 extension to make it worthwhile.
    #[cfg(kopis_neon_sha3)]
    #[allow(unsafe_code)]
    if crate::backend::neon_available() {
        // SAFETY: `neon_available()` has just confirmed this CPU supports NEON, and this arm is
        // compiled only when `build.rs` confirmed the SHA3 extension for the target.
        return unsafe { crate::backend::neon::sample::gen_secret_from_seed::<L, MU>(seed) };
    }

    let mut secret = Matrix::default();
    // Buffer to hold XOF bytes. Can't do const math here, so we make it the max size
    // and cut it down
    let mut backing_buf = [0u8; RING_DEG * MAX_MU / 8];
    let buf = &mut backing_buf[..RING_DEG * MU / 8];

    // Sample the secret using the Centered Binomial Distribution
    for i in 0..L {
        let mut hasher = CTurboShake256::<DOMSEP_GENSEC>::default();
        hasher.update(seed);
        hasher.update(&[i as u8]);
        let mut reader = hasher.finalize_xof();
        reader.read(buf);

        #[cfg(kopis_neon)]
        #[allow(unsafe_code)]
        if !MU.is_multiple_of(8) && crate::backend::neon_available() {
            // SAFETY: `neon_available()` has just confirmed this CPU supports NEON.
            secret.0[i][0] = unsafe { crate::backend::neon::sample::cbd_lanes::<MU>(buf) };
            continue;
        }
    }

    secret
}

/// Uses a random seed to generate a uniform matrix in R^{ℓ×ℓ}.
///
/// For each element (i,j), we compute TurboSHAKE128(seed || i || j, 256*13/8, DOMSEP_GENMAT).
pub(crate) fn gen_matrix_from_seed<const L: usize>(seed: &[u8; 32]) -> Matrix<L, L> {
    // The ℓ² entries are independent XOF calls, so they batch four to a vector.
    #[cfg(kopis_avx2)]
    #[allow(unsafe_code)]
    if crate::backend::avx2_available() {
        // SAFETY: `avx2_available()` has just confirmed this CPU supports AVX2.
        return unsafe { crate::backend::avx2::sample::gen_matrix_from_seed::<L>(seed) };
    }

    // Two to a vector on NEON, where a `uint64x2_t` holds two 64-bit lanes to a `Vec256`'s four.
    #[cfg(kopis_neon_sha3)]
    #[allow(unsafe_code)]
    if crate::backend::neon_available() {
        // SAFETY: `neon_available()` has just confirmed this CPU supports NEON, and this arm is
        // compiled only when `build.rs` confirmed the SHA3 extension for the target.
        return unsafe { crate::backend::neon::sample::gen_matrix_from_seed::<L>(seed) };
    }

    // Our output is a matrix of ring elements
    let mut mat = Matrix::default();
    // For each ring element we need to sample the same number of bytes
    let mut buf = [0u8; RING_DEG * 13 / 8];

    // Construct the matrix entries
    for i in 0..L {
        for j in 0..L {
            let mut hasher = CTurboShake128::<DOMSEP_GENMAT>::default();
            hasher.update(seed);
            hasher.update(&[i as u8]);
            hasher.update(&[j as u8]);
            let mut reader = hasher.finalize_xof();
            reader.read(&mut buf);
            mat.0[i][j] = RingElem::deserialize(&buf, 13);
        }
    }

    mat
}

#[cfg(test)]
mod test {
    use super::*;

    use rand::RngCore;

    /// Naive bit-by-bit CBD for testing: coefficient c is
    /// popcount(bits [c*MU, c*MU + MU/2)) - popcount(bits [c*MU + MU/2, c*MU + MU))
    fn naive_cbd<const MU: usize>(buf: &[u8], out: &mut RingElem) {
        let bit = |i: usize| ((buf[i / 8] >> (i % 8)) & 1) as u16;
        for (c, coeff) in out.0.iter_mut().enumerate() {
            let mut a = 0u16;
            let mut b = 0u16;
            for k in 0..MU / 2 {
                a += bit(c * MU + k);
                b += bit(c * MU + MU / 2 + k);
            }
            *coeff = a.wrapping_sub(b);
        }
    }

    // The specialized MU=6, 8, and 10 paths must agree with the naive bit-by-bit CBD
    #[test]
    fn specialized_cbd_matches_reference() {
        fn check<const MU: usize>(rng: &mut impl RngCore) {
            let mut backing_buf = [0u8; RING_DEG * MAX_MU / 8];
            let buf = &mut backing_buf[..RING_DEG * MU / 8];

            for _ in 0..100 {
                rng.fill_bytes(buf);
                let mut fast = RingElem::default();
                let mut reference = RingElem::default();
                cbd::<MU>(buf, &mut fast);
                naive_cbd::<MU>(buf, &mut reference);
                assert_eq!(fast.0, reference.0);
            }
        }

        let mut rng = rand::rng();
        check::<6>(&mut rng);
        check::<8>(&mut rng);
        check::<10>(&mut rng);
    }
}
