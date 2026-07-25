//! AVX2 sampling: batched XOF expansion for the public matrix and the secret vector.
//!
//! [`crate::sample`] derives each ring element from its own independent TurboSHAKE call, which
//! makes the whole of matrix generation a batch of ℓ² sponges that differ only in a two-byte
//! index. [`super::keccak::xof4`] runs four of those at once, so this module's job is just to
//! group the calls up and unpack the results. The bytes each element sees are unchanged, so the
//! sampled values are identical to the serial code's.

#[cfg(target_arch = "x86")]
use core::arch::x86::*;
#[cfg(target_arch = "x86_64")]
use core::arch::x86_64::*;

use crate::{
    arithmetic::{Matrix, RingElem},
    consts::{DOMSEP_GENMAT, DOMSEP_GENSEC, MAX_MU, MODULUS_Q_BITS, RING_DEG},
};

use super::{keccak::xof4, ser};

/// TurboSHAKE128's rate, used for matrix expansion
const RATE_128: usize = 168;
/// TurboSHAKE256's rate, used for secret expansion
const RATE_256: usize = 136;

/// Bytes of XOF output one matrix entry consumes: 256 coefficients at 13 bits
const MATRIX_ELEM_BYTES: usize = RING_DEG * MODULUS_Q_BITS / 8;

/// Popcounts of the values 0..16, duplicated across both 128-bit halves so `vpshufb` can look
/// up each half independently
#[repr(align(32))]
struct Nibbles([u8; 32]);

const NIBBLE_POPCOUNT: Nibbles = Nibbles([
    0, 1, 1, 2, 1, 2, 2, 3, 1, 2, 2, 3, 2, 3, 3, 4, //
    0, 1, 1, 2, 1, 2, 2, 3, 1, 2, 2, 3, 2, 3, 3, 4,
]);

/// Population count of each 16-bit lane, valid for values below 32.
///
/// A `vpshufb` lookup covers the low nibble — the high byte of each lane is zero, so its lookup
/// yields zero and does not disturb the 16-bit sum — and bit 4, the only other bit that can be
/// set, contributes itself.
#[inline]
#[target_feature(enable = "avx2")]
fn popcount_small(v: __m256i, lut: __m256i) -> __m256i {
    let low = _mm256_shuffle_epi8(lut, _mm256_and_si256(v, _mm256_set1_epi16(0x000F)));
    let bit4 = _mm256_and_si256(_mm256_srli_epi16::<4>(v), _mm256_set1_epi16(1));
    _mm256_add_epi16(low, bit4)
}

/// Samples one ring element from the centered binomial distribution.
///
/// Matches [`crate::sample::cbd`]: coefficient `c` is the population count of bits
/// `[c·MU, c·MU + MU/2)` minus that of `[c·MU + MU/2, c·MU + MU)`, as a wrapping `u16`. Those
/// two halves are exactly the low and high parts of the `MU`-bit field at `c·MU`, so the bit
/// extraction is the same one deserialization does and is shared with it.
///
/// # Safety
///
/// Requires AVX2. `buf.len()` must be `RING_DEG * MU / 8` and `MU` must be even and in `2..=13`.
#[target_feature(enable = "avx2")]
fn cbd<const MU: usize>(buf: &[u8]) -> RingElem {
    let fields = ser::deserialize(buf, MU);

    let lut = {
        // SAFETY: `Nibbles` is 32-byte aligned and exactly 32 bytes long.
        unsafe { _mm256_load_si256(NIBBLE_POPCOUNT.0.as_ptr().cast()) }
    };
    let half_mask = _mm256_set1_epi16(((1u16 << (MU / 2)) - 1) as i16);

    let mut out = RingElem::default();
    for i in 0..RING_DEG / 16 {
        // SAFETY: `i < RING_DEG / 16`, so the 16-`u16` load and store are both in bounds.
        unsafe {
            let field = _mm256_loadu_si256(fields.as_ptr().add(16 * i).cast());
            let low = _mm256_and_si256(field, half_mask);
            // `MU / 2 < 16`, so a 16-bit shift is enough to bring the high half down.
            let high = _mm256_and_si256(shift_right_dynamic(field, MU / 2), half_mask);
            let coeff = _mm256_sub_epi16(popcount_small(low, lut), popcount_small(high, lut));
            _mm256_storeu_si256(out.0.as_mut_ptr().add(16 * i).cast(), coeff);
        }
    }
    out
}

/// Shifts each 16-bit lane right by a count that is constant per call but not a literal.
///
/// `vpsrlw` takes its count from a register as well as an immediate, which is what
/// `_mm256_srl_epi16` exposes; that avoids having to monomorphize the caller over the shift.
#[inline]
#[target_feature(enable = "avx2")]
fn shift_right_dynamic(v: __m256i, count: usize) -> __m256i {
    _mm256_srl_epi16(v, _mm_cvtsi32_si128(count as i32))
}

/// Generates the uniform public matrix, four XOF lanes at a time.
///
/// # Safety
///
/// Requires AVX2.
#[target_feature(enable = "avx2")]
pub(crate) fn gen_matrix_from_seed<const L: usize>(seed: &[u8; 32]) -> Matrix<L, L> {
    let mut mat = Matrix::default();
    let entries = L * L;

    let mut first = 0;
    while first < entries {
        // Entries are numbered in row-major order, matching the serial nested loop. A batch
        // that runs past the end repeats the last entry rather than inventing an index; the
        // extra lane's output is simply dropped below.
        let indices: [[u8; 2]; 4] = core::array::from_fn(|lane| {
            let entry = core::cmp::min(first + lane, entries - 1);
            [(entry / L) as u8, (entry % L) as u8]
        });
        let suffixes: [&[u8]; 4] = core::array::from_fn(|lane| indices[lane].as_slice());

        let mut bufs = [[0u8; MATRIX_ELEM_BYTES]; 4];
        xof4::<RATE_128, DOMSEP_GENMAT, MATRIX_ELEM_BYTES>(seed, &suffixes, &mut bufs);

        for (lane, buf) in bufs.iter().enumerate() {
            let entry = first + lane;
            if entry < entries {
                mat.0[entry / L][entry % L] = RingElem(ser::deserialize(buf, MODULUS_Q_BITS));
            }
        }

        first += 4;
    }

    mat
}

/// Generates the binomially-distributed secret vector in a single XOF batch (ℓ ≤ 4).
///
/// # Safety
///
/// Requires AVX2.
#[target_feature(enable = "avx2")]
pub(crate) fn gen_secret_from_seed<const L: usize, const MU: usize>(
    seed: &[u8; 32],
) -> Matrix<L, 1> {
    // The squeeze length has to be a constant, and Rust will not let `RING_DEG * MU / 8` be one
    // on the stable const-generic rules, so pick it per parameter set. The fallback squeezes
    // the largest length any parameter set uses; extra output beyond `RING_DEG * MU / 8` is
    // discarded, and squeezing further never changes the earlier bytes.
    match MU {
        10 => secret::<L, MU, { RING_DEG * 10 / 8 }>(seed),
        8 => secret::<L, MU, { RING_DEG * 8 / 8 }>(seed),
        6 => secret::<L, MU, { RING_DEG * 6 / 8 }>(seed),
        _ => secret::<L, MU, { RING_DEG * MAX_MU / 8 }>(seed),
    }
}

/// The body of [`gen_secret_from_seed`], with the XOF output length pinned down
///
/// # Safety
///
/// Requires AVX2. `N` must be at least `RING_DEG * MU / 8`.
#[target_feature(enable = "avx2")]
fn secret<const L: usize, const MU: usize, const N: usize>(seed: &[u8; 32]) -> Matrix<L, 1> {
    const {
        assert!(
            L <= 4,
            "the secret vector must fit in one four-lane XOF batch"
        );
    }

    let indices: [[u8; 1]; 4] = core::array::from_fn(|lane| [core::cmp::min(lane, L - 1) as u8]);
    let suffixes: [&[u8]; 4] = core::array::from_fn(|lane| indices[lane].as_slice());

    let mut bufs = [[0u8; N]; 4];
    xof4::<RATE_256, DOMSEP_GENSEC, N>(seed, &suffixes, &mut bufs);

    let mut secret = Matrix::default();
    for (i, row) in secret.0.iter_mut().enumerate() {
        row[0] = cbd::<MU>(&bufs[i][..RING_DEG * MU / 8]);
    }
    secret
}

#[cfg(test)]
mod test {
    use super::*;

    use turboshake::digest::{ExtendableOutput, Update, XofReader};
    use turboshake::{CTurboShake128, CTurboShake256};

    // The vector CBD must agree with the portable one on every parameter set's MU, over
    // arbitrary input bytes rather than just XOF output.
    #[test]
    fn cbd_matches_serial() {
        if !super::super::available() {
            return;
        }
        let mut rng = rand::rng();

        fn check<const MU: usize>(rng: &mut impl rand::RngCore) {
            let mut buf = [0u8; RING_DEG * MAX_MU / 8];
            let buf = &mut buf[..RING_DEG * MU / 8];
            for _ in 0..200 {
                rng.fill_bytes(buf);
                let mut expected = RingElem::default();
                crate::sample::cbd::<MU>(buf, &mut expected);
                // SAFETY: guarded by the `available()` check above.
                let actual = unsafe { cbd::<MU>(buf) };
                assert_eq!(actual.0, expected.0, "MU = {MU}");
            }
        }

        check::<6>(&mut rng);
        check::<8>(&mut rng);
        check::<10>(&mut rng);
    }

    // Batching four XOF lanes must not disturb which bytes each element is derived from. Check
    // against the definition — TurboSHAKE128 over `seed || i || j` — rather than against the
    // serial function, which the dispatcher has already diverted.
    #[test]
    fn gen_matrix_matches_definition() {
        if !super::super::available() {
            return;
        }

        fn check<const L: usize>(seed: &[u8; 32]) {
            // SAFETY: guarded by the `available()` check above.
            let actual = unsafe { gen_matrix_from_seed::<L>(seed) };

            for i in 0..L {
                for j in 0..L {
                    let mut buf = [0u8; MATRIX_ELEM_BYTES];
                    let mut hasher = CTurboShake128::<DOMSEP_GENMAT>::default();
                    hasher.update(seed);
                    hasher.update(&[i as u8]);
                    hasher.update(&[j as u8]);
                    hasher.finalize_xof().read(&mut buf);
                    let expected = RingElem::deserialize(&buf, MODULUS_Q_BITS);
                    assert_eq!(actual.0[i][j], expected, "L = {L}, entry ({i}, {j})");
                }
            }
        }

        // ℓ = 2 fills a batch exactly, ℓ = 3 leaves a partial one, ℓ = 4 fills four
        for byte in 0..8u8 {
            let seed = [byte; 32];
            check::<2>(&seed);
            check::<3>(&seed);
            check::<4>(&seed);
        }
    }

    // Likewise for the secret vector, against TurboSHAKE256 over `seed || i`
    #[test]
    fn gen_secret_matches_definition() {
        if !super::super::available() {
            return;
        }

        fn check<const L: usize, const MU: usize>(seed: &[u8; 32]) {
            // SAFETY: guarded by the `available()` check above.
            let actual = unsafe { gen_secret_from_seed::<L, MU>(seed) };

            for i in 0..L {
                let mut backing = [0u8; RING_DEG * MAX_MU / 8];
                let buf = &mut backing[..RING_DEG * MU / 8];
                let mut hasher = CTurboShake256::<DOMSEP_GENSEC>::default();
                hasher.update(seed);
                hasher.update(&[i as u8]);
                hasher.finalize_xof().read(buf);
                let mut expected = RingElem::default();
                crate::sample::cbd::<MU>(buf, &mut expected);
                assert_eq!(actual.0[i][0], expected, "L = {L}, MU = {MU}, entry {i}");
            }
        }

        for byte in 0..8u8 {
            let seed = [byte; 32];
            check::<2, 10>(&seed);
            check::<3, 8>(&seed);
            check::<4, 6>(&seed);
        }
    }
}
