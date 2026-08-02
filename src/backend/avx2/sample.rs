//! AVX2 centered-binomial sampling.
//!
//! This is the only part of [`crate::sample`] with an accelerated counterpart. Producing the
//! XOF bytes is the `turboshake` crate's job and stays there; what happens afterwards — turning
//! each `MU`-bit field of those bytes into `popcount(low half) − popcount(high half)` — is
//! ordinary bit work, and it vectorizes.
//!
//! Those two halves are the low and high parts of the `MU`-bit field at bit `c·MU`, so pulling
//! the fields out is exactly the extraction [`super::ser`] already does for deserialization and
//! is shared with it. What is left is two small population counts per coefficient.

use crate::{arithmetic::RingElem, consts::RING_DEG};

use super::intrinsics::{
    Vec256, add_epi16, and_si256, cvtsi32_si128, load_u16, load_u8, set1_epi16, shuffle_epi8,
    srl_epi16, srli_epi16, store_u16, sub_epi16,
};
use super::ser;

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
fn popcount_small(v: Vec256, lut: Vec256) -> Vec256 {
    let low = shuffle_epi8(lut, and_si256(v, set1_epi16(0x000F)));
    let bit4 = and_si256(srli_epi16::<4>(v), set1_epi16(1));
    add_epi16(low, bit4)
}

/// Shifts each 16-bit lane right by a count that is constant per call but not a literal.
///
/// `vpsrlw` takes its count from a register as well as an immediate, which is what
/// `_mm256_srl_epi16` exposes; that saves monomorphizing the caller over the shift.
#[inline]
#[target_feature(enable = "avx2")]
fn shift_right_dynamic(v: Vec256, count: usize) -> Vec256 {
    srl_epi16(v, cvtsi32_si128(count as i32))
}

/// Samples one ring element from the centered binomial distribution.
///
/// Produces exactly what [`crate::sample::cbd`] does: coefficient `c` is the population count of
/// bits `[c·MU, c·MU + MU/2)` minus that of `[c·MU + MU/2, c·MU + MU)`, as a wrapping `u16`.
///
/// # Safety
///
/// Requires AVX2. `buf.len()` must be `RING_DEG * MU / 8`, and `MU` must be even and in `2..=13`.
#[target_feature(enable = "avx2")]
pub(crate) fn cbd<const MU: usize>(buf: &[u8]) -> RingElem {
    let fields = ser::deserialize(buf, MU);

    let lut = load_u8(&NIBBLE_POPCOUNT.0, 0);
    let half_mask = set1_epi16(((1u16 << (MU / 2)) - 1) as i16);

    let mut out = RingElem::default();
    for i in 0..RING_DEG / 16 {
        let field = load_u16(&fields, i);
        let low = and_si256(field, half_mask);
        // `MU / 2 < 16`, so a 16-bit shift is enough to bring the high half down.
        let high = and_si256(shift_right_dynamic(field, MU / 2), half_mask);
        let coeff = sub_epi16(popcount_small(low, lut), popcount_small(high, lut));
        store_u16(&mut out.0, i, coeff);
    }
    out
}

#[cfg(test)]
mod test {
    use super::*;

    use crate::consts::MAX_MU;

    // The vector CBD must agree with the portable one on every parameter set's MU, over
    // arbitrary input bytes rather than just XOF output.
    #[test]
    fn matches_serial() {
        if !super::super::available() {
            return;
        }
        let mut rng = rand::rng();

        fn check<const MU: usize>(rng: &mut impl rand::RngCore) {
            let mut backing = [0u8; RING_DEG * MAX_MU / 8];
            let buf = &mut backing[..RING_DEG * MU / 8];
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
}
