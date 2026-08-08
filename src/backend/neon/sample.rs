//! NEON sampling: centered-binomial sampling, and batched XOF expansion where it is available.
//!
//! Two things happen here. The first is the centered-binomial step: turning each `MU`-bit field
//! of the XOF bytes into `popcount(low half) − popcount(high half)`, which is ordinary bit work
//! and vectorizes. Pulling the `MU`-bit fields out is exactly the extraction [`super::ser`]
//! already does for deserialization and is shared with it. What is left is two small population
//! counts per coefficient, which NEON's per-byte `vcnt` handles directly: each field's two halves
//! fit in a single byte (`MU/2 ≤ 5`), so a byte-wise popcount of the 16-bit lane is the lane's
//! popcount.
//!
//! The second is producing those bytes in the first place. [`crate::sample`] derives each ring
//! element from its own independent TurboSHAKE call, so the whole of matrix generation is a batch
//! of ℓ² sponges that differ only in a two-byte index. [`super::keccak::xof2`] runs two of those
//! at once, and [`gen_matrix_from_seed`] and [`gen_secret_from_seed`] group the calls up and
//! unpack the results. The bytes each element sees are unchanged, so the sampled values are
//! identical to the serial code's.
//!
//! That half exists only when the target has the ARMv8.2 SHA3 extension — see [`super::keccak`]
//! for why, and `build.rs` for how it is decided. Without it, this module is just the CBD step,
//! as it was before, and [`crate::sample`] drives the scalar sponge itself.

use crate::{arithmetic::RingElem, consts::RING_DEG};

use super::intrinsics::{
    Vec128, and, cnt_u8, dup_n_s16, dup_n_u16, load_u16, store_u16, sub_16, ushl_u16,
};
use super::ser;

#[cfg(kopis_neon_sha3)]
use super::keccak::{WAYS, xof2};
#[cfg(kopis_neon_sha3)]
use crate::{
    arithmetic::Matrix,
    consts::{DOMSEP_GENMAT, DOMSEP_GENSEC, MAX_MU, MODULUS_Q_BITS},
};

/// TurboSHAKE128's rate, used for matrix expansion
#[cfg(kopis_neon_sha3)]
const RATE_128: usize = 168;
/// TurboSHAKE256's rate, used for secret expansion
#[cfg(kopis_neon_sha3)]
const RATE_256: usize = 136;

/// Bytes of XOF output one matrix entry consumes: 256 coefficients at 13 bits
#[cfg(kopis_neon_sha3)]
const MATRIX_ELEM_BYTES: usize = RING_DEG * MODULUS_Q_BITS / 8;

/// Population count of each 16-bit lane, valid when the value fits in the low byte.
///
/// `cnt` counts bits per byte; the high byte of each lane is zero (its count is zero and does not
/// disturb the 16-bit value), so reading the per-byte counts as 16-bit lanes gives each lane's
/// popcount directly.
#[inline]
#[target_feature(enable = "neon")]
fn popcount_small(v: Vec128) -> Vec128 {
    cnt_u8(v)
}

/// Samples one ring element from the centered binomial distribution.
///
/// Produces exactly what [`crate::sample::cbd`] does: coefficient `c` is the population count of
/// bits `[c·MU, c·MU + MU/2)` minus that of `[c·MU + MU/2, c·MU + MU)`, as a wrapping `u16`.
///
/// Not called `cbd`, unlike its AVX2 sibling, and the reason is extraction rather than taste.
/// [`secret`] below calls *both* this and the portable [`crate::sample::cbd`]; aeneas emits them
/// as `backend.neon.sample.cbd` and `sample.cbd`, and Lean resolves the latter, written inside a
/// declaration named `backend.neon.sample.…`, against the enclosing namespaces first — so it
/// finds this one and the extraction fails to typecheck on the arity mismatch. The AVX2 backend
/// does not hit this because its `secret` never reaches for the portable sampler.
///
/// # Safety
///
/// Requires NEON. `buf.len()` must be `RING_DEG * MU / 8`, and `MU` must be even and in `2..=13`.
#[target_feature(enable = "neon")]
pub(crate) fn cbd_lanes<const MU: usize>(buf: &[u8]) -> RingElem {
    let fields = ser::deserialize(buf, MU);

    let half_mask = dup_n_u16((1u16 << (MU / 2)) - 1);
    // `MU/2 < 16`, so a 16-bit logical right shift by the negated count brings the high half down.
    let half_shift = dup_n_s16(-((MU / 2) as i16));

    let mut out = RingElem::default();
    for i in 0..RING_DEG / 8 {
        let field = load_u16(&fields, i);
        let low = and(field, half_mask);
        let high = and(ushl_u16(field, half_shift), half_mask);
        let coeff = sub_16(popcount_small(low), popcount_small(high));
        store_u16(&mut out.0, i, coeff);
    }
    out
}

/// Generates the uniform public matrix, two XOF lanes at a time.
///
/// # Safety
///
/// Requires NEON and the SHA3 extension.
///
// `needless_range_loop`: the index is used to derive the matrix position as well as to index the
// batch, so the iterator form would need `enumerate()` and read worse, not better. The AVX2
// sibling writes it this way too, there for extraction reasons.
#[allow(clippy::needless_range_loop)]
#[cfg(kopis_neon_sha3)]
#[target_feature(enable = "neon,sha3")]
pub(crate) fn gen_matrix_from_seed<const L: usize>(seed: &[u8; 32]) -> Matrix<L, L> {
    let mut mat = Matrix::default();
    let entries = L * L;

    // Hoisted out of the loop: `xof2` overwrites every byte of both lanes, so re-creating this
    // per batch would be a pure memset of 2 * 416 bytes that nothing reads.
    let mut bufs = [[0u8; MATRIX_ELEM_BYTES]; WAYS];

    let mut first = 0;
    while first < entries {
        // Entries are numbered in row-major order, matching the serial nested loop. A batch that
        // runs past the end repeats the last entry rather than inventing an index; the extra
        // lane's output is simply dropped below.
        let mut indices = [[0u8; 2]; WAYS];
        for lane in 0..WAYS {
            let entry = core::cmp::min(first + lane, entries - 1);
            indices[lane][0] = (entry / L) as u8;
            indices[lane][1] = (entry % L) as u8;
        }

        xof2::<RATE_128, DOMSEP_GENMAT, 2, MATRIX_ELEM_BYTES>(seed, &indices, &mut bufs);

        for lane in 0..WAYS {
            let entry = first + lane;
            if entry < entries {
                mat.0[entry / L][entry % L] =
                    RingElem(ser::deserialize(&bufs[lane], MODULUS_Q_BITS));
            }
        }

        first += WAYS;
    }

    mat
}

/// Generates the binomially-distributed secret vector, two XOF lanes at a time.
///
/// # Safety
///
/// Requires NEON and the SHA3 extension.
#[cfg(kopis_neon_sha3)]
#[target_feature(enable = "neon,sha3")]
pub(crate) fn gen_secret_from_seed<const L: usize, const MU: usize>(
    seed: &[u8; 32],
) -> Matrix<L, 1> {
    // The squeeze length has to be a constant, and Rust will not let `RING_DEG * MU / 8` be one
    // on the stable const-generic rules, so pick it per parameter set. The fallback squeezes the
    // largest length any parameter set uses; extra output beyond `RING_DEG * MU / 8` is
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
/// Requires NEON and the SHA3 extension. `N` must be at least `RING_DEG * MU / 8`.
///
// `needless_range_loop`: see `gen_matrix_from_seed` above.
#[allow(clippy::needless_range_loop)]
#[cfg(kopis_neon_sha3)]
#[target_feature(enable = "neon,sha3")]
fn secret<const L: usize, const MU: usize, const N: usize>(seed: &[u8; 32]) -> Matrix<L, 1> {
    let mut secret = Matrix::default();

    let mut first = 0;
    while first < L {
        // As in the matrix above, a batch running past the end repeats the last index and the
        // extra lane's output is dropped.
        let mut indices = [[0u8; 1]; WAYS];
        for lane in 0..WAYS {
            indices[lane][0] = core::cmp::min(first + lane, L - 1) as u8;
        }

        let mut bufs = [[0u8; N]; WAYS];
        xof2::<RATE_256, DOMSEP_GENSEC, 1, N>(seed, &indices, &mut bufs);

        for lane in 0..WAYS {
            let i = first + lane;
            if i < L {
                let buf = &bufs[lane][..RING_DEG * MU / 8];
                // Only the widths whose coefficients straddle byte boundaries are worth
                // diverting, which is the same call [`crate::sample`] makes when it drives the
                // sponge itself: at `MU` a multiple of 8 the portable loop is a flat pass over
                // bytes that the compiler already vectorizes. `MU` is a const generic, so this
                // test costs nothing at run time.
                if MU.is_multiple_of(8) {
                    crate::sample::cbd::<MU>(buf, &mut secret.0[i][0]);
                } else {
                    secret.0[i][0] = cbd_lanes::<MU>(buf);
                }
            }
        }

        first += WAYS;
    }

    secret
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
                let actual = unsafe { cbd_lanes::<MU>(buf) };
                assert_eq!(actual.0, expected.0, "MU = {MU}");
            }
        }

        check::<6>(&mut rng);
        check::<8>(&mut rng);
        check::<10>(&mut rng);
    }

    // Batching two XOF lanes must not disturb which bytes each element is derived from. Check
    // against the definition — TurboSHAKE128 over `seed || i || j` — rather than against the
    // serial function, which the dispatcher has already diverted.
    #[cfg(kopis_neon_sha3)]
    #[test]
    fn gen_matrix_matches_definition() {
        use turboshake::CTurboShake128;
        use turboshake::digest::{ExtendableOutput, Update, XofReader};

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

        // With two lanes to a batch, ℓ = 2 is two full batches, ℓ = 3 is four full plus a half,
        // and ℓ = 4 is eight full — so the partial-batch path is covered.
        for byte in 0..8u8 {
            let seed = [byte; 32];
            check::<2>(&seed);
            check::<3>(&seed);
            check::<4>(&seed);
        }
    }

    // Likewise for the secret vector, against TurboSHAKE256 over `seed || i`
    #[cfg(kopis_neon_sha3)]
    #[test]
    fn gen_secret_matches_definition() {
        use turboshake::CTurboShake256;
        use turboshake::digest::{ExtendableOutput, Update, XofReader};

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

        // ℓ = 3 is the odd one out, whose last batch has an idle lane. Each ℓ is paired with the
        // MU its parameter set uses, so both the `is_multiple_of(8)` arm and the other are hit.
        for byte in 0..8u8 {
            let seed = [byte; 32];
            check::<2, 10>(&seed);
            check::<3, 8>(&seed);
            check::<4, 6>(&seed);
        }
    }
}
