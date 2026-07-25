//! NEON centered-binomial sampling.
//!
//! As in the AVX2 backend, this is the only part of [`crate::sample`] with an accelerated
//! counterpart. Producing the XOF bytes is the `turboshake` crate's job; what happens
//! afterwards — turning each `MU`-bit field of those bytes into
//! `popcount(low half) − popcount(high half)` — is ordinary bit work, and it vectorizes.
//!
//! Pulling the `MU`-bit fields out is exactly the extraction [`super::ser`] already does for
//! deserialization and is shared with it. What is left is two small population counts per
//! coefficient, which NEON's per-byte `vcnt` handles directly: each field's two halves fit in a
//! single byte (`MU/2 ≤ 5`), so a byte-wise popcount of the 16-bit lane is the lane's popcount.

use core::arch::aarch64::*;

use crate::{arithmetic::RingElem, consts::RING_DEG};

use super::ser;

/// Population count of each 16-bit lane, valid when the value fits in the low byte.
///
/// `vcntq_u8` counts bits per byte; the high byte of each lane is zero (its count is zero and
/// does not disturb the 16-bit value), so reinterpreting the per-byte counts as 16-bit lanes
/// gives each lane's popcount directly.
#[inline]
#[target_feature(enable = "neon")]
fn popcount_small(v: uint16x8_t) -> uint16x8_t {
    vreinterpretq_u16_u8(vcntq_u8(vreinterpretq_u8_u16(v)))
}

/// Samples one ring element from the centered binomial distribution.
///
/// Produces exactly what [`crate::sample::cbd`] does: coefficient `c` is the population count of
/// bits `[c·MU, c·MU + MU/2)` minus that of `[c·MU + MU/2, c·MU + MU)`, as a wrapping `u16`.
///
/// # Safety
///
/// Requires NEON. `buf.len()` must be `RING_DEG * MU / 8`, and `MU` must be even and in `2..=13`.
#[target_feature(enable = "neon")]
pub(crate) fn cbd<const MU: usize>(buf: &[u8]) -> RingElem {
    let fields = ser::deserialize(buf, MU);

    let half_mask = vdupq_n_u16((1u16 << (MU / 2)) - 1);
    // `MU/2 < 16`, so a 16-bit logical right shift by the negated count brings the high half down.
    let half_shift = vdupq_n_s16(-((MU / 2) as i16));

    let mut out = RingElem::default();
    for i in 0..RING_DEG / 8 {
        // SAFETY: `i < RING_DEG / 8`, so the 8-`u16` load and store are both in bounds.
        unsafe {
            let field = vld1q_u16(fields.as_ptr().add(8 * i));
            let low = vandq_u16(field, half_mask);
            let high = vandq_u16(vshlq_u16(field, half_shift), half_mask);
            let coeff = vsubq_u16(popcount_small(low), popcount_small(high));
            vst1q_u16(out.0.as_mut_ptr().add(8 * i), coeff);
        }
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
