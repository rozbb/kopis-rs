//! This file implements methods for generating uniform matrices and binomially distributed vectors

use crate::{
    arithmetic::{Matrix, RingElem},
    consts::{DOMSEP_GENMAT, DOMSEP_GENSEC, MAX_MU, MODULUS_Q_BITS, RING_DEG},
};

use turboshake::digest::{ExtendableOutput, Update, XofReader};
use turboshake::{CTurboShake128, CTurboShake256};

/// One CBD coefficient: popcount of the low `half` bits of `raw`, minus popcount of the
/// next `half` bits. `mask` must be `(1 << half) - 1`.
///
/// This is a free function rather than a closure inside `cbd` on purpose: aeneas extracts a
/// closure declared inside a const-generic function as a type parameterized by that const
/// (`gen.cbd.closure_1 (MU : Usize) := Slice U8`), which does not mention it, so `MU` becomes
/// un-inferable at every call site and the generated Lean does not typecheck.
fn cbd_diff(raw: u32, half: u32, mask: u32) -> u16 {
    let a = (raw & mask).count_ones() as u16;
    let b = ((raw >> half) & mask).count_ones() as u16;
    a.wrapping_sub(b)
}

/// Computes the Centered Binomial Distribution using the given bytes as randomness
pub(crate) fn cbd<const MU: usize>(buf: &[u8], out: &mut RingElem) {
    assert_eq!(buf.len(), RING_DEG * MU / 8);

    // The three parameter sets use MU = 8, 10, and 6, and each gets a specialized branchless
    // path. Since MU is a const generic, this dispatch is resolved at compile time. The final
    // branch is a generic fallback for any other MU.
    if MU == 8 {
        // Kopis-768: Each coefficient uses exactly 1 byte, with the low nibble as the positive
        // half and the high nibble as the negative half. So we don't need a buffer to read bits
        for (i, &byte) in buf.iter().enumerate() {
            let a = (byte & 0x0F).count_ones() as u16;
            let b = (byte >> 4).count_ones() as u16;
            out.0[i] = a.wrapping_sub(b);
        }
    } else if MU == 10 {
        // Kopis-512: 4 coefficients per 5-byte group. Coefficient k of a group occupies bits
        // [10k, 10k+10), which always fit in the two bytes starting at byte 10k/8. The low 5
        // bits are the positive half and the next 5 bits are the negative half.
        for g in 0..RING_DEG / 4 {
            let i = 5 * g;
            let b0 = buf[i] as u32;
            let b1 = buf[i + 1] as u32;
            let b2 = buf[i + 2] as u32;
            let b3 = buf[i + 3] as u32;
            let b4 = buf[i + 4] as u32;
            let o = 4 * g;
            out.0[o] = cbd_diff(b0 | (b1 << 8), 5, 0x1f);
            out.0[o + 1] = cbd_diff((b1 | (b2 << 8)) >> 2, 5, 0x1f);
            out.0[o + 2] = cbd_diff((b2 | (b3 << 8)) >> 4, 5, 0x1f);
            out.0[o + 3] = cbd_diff((b3 | (b4 << 8)) >> 6, 5, 0x1f);
        }
    } else if MU == 6 {
        // Kopis-1024: 4 coefficients per 3-byte group. Coefficient k of a group occupies bits
        // [6k, 6k+6). The low 3 bits are the positive half, the next 3 the negative half.
        for g in 0..RING_DEG / 4 {
            let i = 3 * g;
            let b0 = buf[i] as u32;
            let b1 = buf[i + 1] as u32;
            let b2 = buf[i + 2] as u32;
            let o = 4 * g;
            out.0[o] = cbd_diff(b0, 3, 0x07);
            out.0[o + 1] = cbd_diff((b0 | (b1 << 8)) >> 6, 3, 0x07);
            out.0[o + 2] = cbd_diff((b1 | (b2 << 8)) >> 4, 3, 0x07);
            out.0[o + 3] = cbd_diff(b2 >> 2, 3, 0x07);
        }
    } else {
        // Generic fallback: read MU bits at a time, spanning up to 3 bytes when not
        // byte-aligned. Worst case: MU=10 starting at bit 7 needs bits 7..16, spanning 3 bytes.
        let half = MU / 2;
        let mask: u32 = (1 << half) - 1;

        let mut bit_pos = 0;
        for coeff in out.0.iter_mut() {
            let byte_idx = bit_pos / 8;
            let bit_in_byte = bit_pos % 8;

            let mut raw: u32 = buf[byte_idx] as u32;
            if byte_idx + 1 < buf.len() {
                raw |= (buf[byte_idx + 1] as u32) << 8;
            }
            if byte_idx + 2 < buf.len() {
                raw |= (buf[byte_idx + 2] as u32) << 16;
            }
            raw >>= bit_in_byte;

            let a = (raw & mask).count_ones() as u16;
            let b = ((raw >> half) & mask).count_ones() as u16;
            *coeff = a.wrapping_sub(b);

            bit_pos += MU;
        }
    }
}

/// Uses a random seed to generate an MLWR secret, i.e., an element in R^ℓ whose entries are
/// sampled according to a binomial distribution.
pub(crate) fn gen_secret_from_seed<const L: usize, const MU: usize>(
    seed: &[u8; 32],
) -> Matrix<L, 1> {
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

        // Only the widths whose coefficients straddle byte boundaries are worth diverting.
        // When MU is a multiple of 8 the loop below is a flat pass over bytes that the
        // compiler already vectorizes, and beating it needs no help; when it is not, the
        // AVX2 path's field extraction is a clear win. MU is a const generic, so this test
        // costs nothing at run time.
        #[cfg(kopis_avx2)]
        #[allow(unsafe_code)]
        if !MU.is_multiple_of(8) && crate::backend::avx2_available() {
            // SAFETY: `avx2_available()` has just confirmed this CPU supports AVX2.
            secret.0[i][0] = unsafe { crate::backend::avx2::sample::cbd::<MU>(buf) };
            continue;
        }

        #[cfg(kopis_neon)]
        #[allow(unsafe_code)]
        if !MU.is_multiple_of(8) && crate::backend::neon_available() {
            // SAFETY: `neon_available()` has just confirmed this CPU supports NEON.
            secret.0[i][0] = unsafe { crate::backend::neon::sample::cbd::<MU>(buf) };
            continue;
        }

        cbd::<MU>(buf, &mut secret.0[i][0]);
    }

    secret
}

/// Uses a random seed to generate a uniform matrix in R^{ℓ×ℓ}.
///
/// For each element (i,j), we compute TurboSHAKE128(seed || i || j, 256*13/8, DOMSEP_GENMAT).
pub(crate) fn gen_matrix_from_seed<const L: usize>(seed: &[u8; 32]) -> Matrix<L, L> {
    // Our output is a matrix of ring elements
    let mut mat = Matrix::default();
    // For each ring element we need to sample the same number of bytes
    let mut buf = [0u8; RING_DEG * MODULUS_Q_BITS / 8];

    // Construct the matrix entries
    for i in 0..L {
        for j in 0..L {
            let mut hasher = CTurboShake128::<DOMSEP_GENMAT>::default();
            hasher.update(seed);
            hasher.update(&[i as u8]);
            hasher.update(&[j as u8]);
            let mut reader = hasher.finalize_xof();
            reader.read(&mut buf);
            mat.0[i][j] = RingElem::deserialize(&buf, MODULUS_Q_BITS);
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
    fn cbd_reference<const MU: usize>(buf: &[u8], out: &mut RingElem) {
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
                cbd_reference::<MU>(buf, &mut reference);
                assert_eq!(fast.0, reference.0);
            }
        }

        let mut rng = rand::rng();
        check::<6>(&mut rng);
        check::<8>(&mut rng);
        check::<10>(&mut rng);
    }
}
