//! Four-way TurboSHAKE on AVX2.
//!
//! Keccak's permutation is inherently serial — there is nothing inside one round to
//! vectorize — so the speedup comes from running four *independent* sponges side by side, one
//! per 64-bit lane of a `__m256i`. Kopis samples in batches that are exactly this shape: the
//! public matrix is ℓ² independent XOF calls that differ only in a two-byte index, and the
//! secret is ℓ more. Four at a time turns the dominant cost of key generation into a quarter
//! as many permutations.
//!
//! Only the shape Kopis needs is implemented: an input short enough to fit in a single block
//! (a 32-byte seed plus a one- or two-byte index), and an equal-length output for all four
//! lanes. That removes the whole absorb state machine — one block is built, XORed in, and
//! squeezed.
//!
//! The permutation itself is a direct transliteration of the reference Keccak-p[1600, 12]:
//! same θ, ρ, π, χ, ι in the same order, same rotation offsets, and the same round constants
//! (TurboSHAKE's 12 rounds are the *last* 12 of Keccak-f[1600], per FIPS 202 §3.4). The
//! `matches_scalar` test checks the whole thing against the `turboshake` crate.

#[cfg(target_arch = "x86")]
use core::arch::x86::*;
#[cfg(target_arch = "x86_64")]
use core::arch::x86_64::*;

/// Lanes in the Keccak state
const PLEN: usize = 25;

/// Rounds in Keccak-p[1600, 12], the permutation TurboSHAKE is built on
const ROUNDS: usize = 12;

/// Keccak-f[1600] round constants. Keccak-p[1600, n] uses the last `n` of them.
#[rustfmt::skip]
const RC: [u64; 24] = [
    0x0000000000000001, 0x0000000000008082, 0x800000000000808a, 0x8000000080008000,
    0x000000000000808b, 0x0000000080000001, 0x8000000080008081, 0x8000000000008009,
    0x000000000000008a, 0x0000000000000088, 0x0000000080008009, 0x000000008000000a,
    0x000000008000808b, 0x800000000000008b, 0x8000000000008089, 0x8000000000008003,
    0x8000000000008002, 0x8000000000000080, 0x000000000000800a, 0x800000008000000a,
    0x8000000080008081, 0x8000000000008080, 0x0000000080000001, 0x8000000080008008,
];

/// The 12 constants this permutation uses, each broadcast to all four lanes so ι is one load
/// and one XOR. Built rather than written out, so it cannot drift from [`RC`].
#[repr(align(32))]
struct RoundConsts([u64; 4 * ROUNDS]);

const RC4: RoundConsts = {
    let mut broadcast = [0u64; 4 * ROUNDS];
    let mut round = 0;
    while round < ROUNDS {
        let rc = RC[24 - ROUNDS + round];
        let mut lane = 0;
        while lane < 4 {
            broadcast[4 * round + lane] = rc;
            lane += 1;
        }
        round += 1;
    }
    RoundConsts(broadcast)
};

/// Rotates each 64-bit lane left by `L`.
///
/// `R` must be `64 - L`; it is a second parameter only because the shift counts have to be
/// literal immediates and Rust will not compute one from the other in that position.
#[inline]
#[target_feature(enable = "avx2")]
fn rotl<const L: i32, const R: i32>(v: __m256i) -> __m256i {
    const {
        assert!(L + R == 64, "rotate halves must sum to the lane width");
    }
    _mm256_or_si256(_mm256_slli_epi64::<L>(v), _mm256_srli_epi64::<R>(v))
}

/// The combined ρ-and-π step, as a `destination <= source, rotation` table.
///
/// `A[x, y]` lives at `5y + x`, and the step is `B[y, 2x + 3y] = rot(A[x, y], r[x, y])`.
/// Spelling it out as 25 independent rotates into a scratch array, rather than as the usual
/// 24-element cycle-in-place, is deliberate: in the cycle each step waits on the previous one,
/// whereas these have no dependencies between them and fill the pipeline.
macro_rules! rho_pi {
    ($src:ident, $dst:ident, $($to:literal <= $from:literal, $rot:literal),* $(,)?) => {
        $( $dst[$to] = rotl::<$rot, { 64 - $rot }>($src[$from]); )*
    };
}

/// Applies Keccak-p[1600, 12] to four independent states held one per 64-bit lane
#[target_feature(enable = "avx2")]
fn permute(state: &mut [__m256i; PLEN]) {
    let mut b = [_mm256_setzero_si256(); PLEN];

    for round in 0..ROUNDS {
        // SAFETY: `RC4` is 32-byte aligned and holds `4 * ROUNDS` words, so the load for
        // `round < ROUNDS` is aligned and in bounds.
        let rc = unsafe { _mm256_load_si256(RC4.0.as_ptr().add(4 * round).cast()) };

        // θ: fold each column, then mix each column with its two neighbours
        let mut column = [_mm256_setzero_si256(); 5];
        for (x, slot) in column.iter_mut().enumerate() {
            *slot = _mm256_xor_si256(
                _mm256_xor_si256(
                    _mm256_xor_si256(state[x], state[x + 5]),
                    _mm256_xor_si256(state[x + 10], state[x + 15]),
                ),
                state[x + 20],
            );
        }
        for x in 0..5 {
            let d = _mm256_xor_si256(column[(x + 4) % 5], rotl::<1, 63>(column[(x + 1) % 5]));
            for y in 0..5 {
                state[5 * y + x] = _mm256_xor_si256(state[5 * y + x], d);
            }
        }

        // ρ and π, into `b`
        rho_pi!(
            state,
            b,
            0 <= 0,
            0,
            10 <= 1,
            1,
            20 <= 2,
            62,
            5 <= 3,
            28,
            15 <= 4,
            27,
            16 <= 5,
            36,
            1 <= 6,
            44,
            11 <= 7,
            6,
            21 <= 8,
            55,
            6 <= 9,
            20,
            7 <= 10,
            3,
            17 <= 11,
            10,
            2 <= 12,
            43,
            12 <= 13,
            25,
            22 <= 14,
            39,
            23 <= 15,
            41,
            8 <= 16,
            45,
            18 <= 17,
            15,
            3 <= 18,
            21,
            13 <= 19,
            8,
            14 <= 20,
            18,
            24 <= 21,
            2,
            9 <= 22,
            61,
            19 <= 23,
            56,
            4 <= 24,
            14,
        );

        // χ: the row-wise nonlinear step, reading `b` and writing back to the state
        for y in (0..PLEN).step_by(5) {
            for x in 0..5 {
                state[y + x] = _mm256_xor_si256(
                    b[y + x],
                    _mm256_andnot_si256(b[y + (x + 1) % 5], b[y + (x + 2) % 5]),
                );
            }
        }

        // ι
        state[0] = _mm256_xor_si256(state[0], rc);
    }
}

/// Runs four TurboSHAKE instances at once, each absorbing `prefix || suffixes[lane]` and
/// squeezing `N` bytes into `out[lane]`.
///
/// `RATE` selects the variant: 168 for TurboSHAKE128, 136 for TurboSHAKE256. `DS` is the
/// domain separator. Every `prefix || suffix` must fit in one block with room for the padding,
/// i.e. `32 + suffix.len() < RATE`, which holds by a wide margin for the 1- and 2-byte indices
/// Kopis uses.
///
/// # Safety
///
/// Requires AVX2.
#[target_feature(enable = "avx2")]
pub(crate) fn xof4<const RATE: usize, const DS: u8, const N: usize>(
    prefix: &[u8; 32],
    suffixes: &[&[u8]; 4],
    out: &mut [[u8; N]; 4],
) {
    const {
        assert!(RATE == 168 || RATE == 136, "unsupported TurboSHAKE rate");
        assert!(DS >= 0x01 && DS <= 0x7F, "invalid domain separator");
    }

    // The entire input fits in one block, so absorption is just "build the block". Pad as
    // TurboSHAKE does: the domain separator at the first free byte, and the high bit of the
    // block's last byte.
    let mut block = [[0u8; RATE]; 4];
    for (lane, bytes) in block.iter_mut().enumerate() {
        let suffix = suffixes[lane];
        assert!(32 + suffix.len() < RATE);
        bytes[..32].copy_from_slice(prefix);
        bytes[32..32 + suffix.len()].copy_from_slice(suffix);
        bytes[32 + suffix.len()] = DS;
        bytes[RATE - 1] |= 0x80;
    }

    // Transpose the four blocks into the lane-parallel state. Words past the rate stay zero,
    // which is the capacity.
    let mut state = [_mm256_setzero_si256(); PLEN];
    for (word, slot) in state.iter_mut().enumerate().take(RATE / 8) {
        let lanes: [u64; 4] = core::array::from_fn(|lane| {
            let mut chunk = [0u8; 8];
            chunk.copy_from_slice(&block[lane][8 * word..8 * word + 8]);
            u64::from_le_bytes(chunk)
        });
        // SAFETY: `lanes` is 4 `u64`s, exactly the 32 bytes the load reads.
        *slot = unsafe { _mm256_loadu_si256(lanes.as_ptr().cast()) };
    }

    // Squeeze. Each permutation yields one rate-sized block per lane.
    let mut done = 0;
    while done < N {
        permute(&mut state);

        let take = core::cmp::min(RATE, N - done);
        for (word, packed) in state.iter().enumerate().take(take.div_ceil(8)) {
            let mut lanes = [0u64; 4];
            // SAFETY: `lanes` is 4 `u64`s, exactly the 32 bytes the store writes.
            unsafe { _mm256_storeu_si256(lanes.as_mut_ptr().cast(), *packed) };
            for (lane, &value) in lanes.iter().enumerate() {
                let bytes = value.to_le_bytes();
                // The last word of a partial output contributes only part of itself.
                let start = done + 8 * word;
                let len = core::cmp::min(8, N - start);
                out[lane][start..start + len].copy_from_slice(&bytes[..len]);
            }
        }

        done += take;
    }
}

#[cfg(test)]
mod test {
    use super::*;

    extern crate std;

    use turboshake::digest::{ExtendableOutput, Update, XofReader};
    use turboshake::{CTurboShake128, CTurboShake256};

    // Each lane must reproduce, byte for byte, what the scalar TurboSHAKE would have produced
    // for that lane's input — over both rates, several output lengths (including ones that end
    // mid-block and mid-word), and both suffix widths Kopis uses.
    #[test]
    fn matches_scalar() {
        if !super::super::available() {
            return;
        }

        fn check<const RATE: usize, const DS: u8, const N: usize>(
            prefix: &[u8; 32],
            suffixes: &[&[u8]; 4],
            scalar: impl Fn(&[u8], &[u8], &mut [u8; N]),
        ) {
            let mut vector = [[0u8; N]; 4];
            // SAFETY: guarded by the `available()` check above.
            unsafe { xof4::<RATE, DS, N>(prefix, suffixes, &mut vector) };

            for lane in 0..4 {
                let mut expected = [0u8; N];
                scalar(prefix, suffixes[lane], &mut expected);
                assert_eq!(
                    vector[lane], expected,
                    "lane {lane}, rate {RATE}, {N} bytes"
                );
            }
        }

        fn shake128<const DS: u8, const N: usize>(prefix: &[u8], suffix: &[u8], out: &mut [u8; N]) {
            let mut hasher = CTurboShake128::<DS>::default();
            hasher.update(prefix);
            hasher.update(suffix);
            hasher.finalize_xof().read(out);
        }

        fn shake256<const DS: u8, const N: usize>(prefix: &[u8], suffix: &[u8], out: &mut [u8; N]) {
            let mut hasher = CTurboShake256::<DS>::default();
            hasher.update(prefix);
            hasher.update(suffix);
            hasher.finalize_xof().read(out);
        }

        let prefix: [u8; 32] = core::array::from_fn(|i| (7 * i + 3) as u8);
        let two_byte: [[u8; 2]; 4] = [[0, 0], [0, 1], [1, 0], [2, 3]];
        let two_byte: [&[u8]; 4] = core::array::from_fn(|i| two_byte[i].as_slice());
        let one_byte: [[u8; 1]; 4] = [[0], [1], [2], [255]];
        let one_byte: [&[u8]; 4] = core::array::from_fn(|i| one_byte[i].as_slice());

        // The two shapes the crate actually uses
        check::<168, 0x02, 416>(&prefix, &two_byte, shake128::<0x02, 416>);
        check::<136, 0x03, 320>(&prefix, &one_byte, shake256::<0x03, 320>);
        check::<136, 0x03, 256>(&prefix, &one_byte, shake256::<0x03, 256>);
        check::<136, 0x03, 192>(&prefix, &one_byte, shake256::<0x03, 192>);

        // Lengths that stress the block and word boundaries
        check::<168, 0x1F, 1>(&prefix, &two_byte, shake128::<0x1F, 1>);
        check::<168, 0x1F, 167>(&prefix, &two_byte, shake128::<0x1F, 167>);
        check::<168, 0x1F, 168>(&prefix, &two_byte, shake128::<0x1F, 168>);
        check::<168, 0x7F, 171>(&prefix, &two_byte, shake128::<0x7F, 171>);
        check::<136, 0x01, 137>(&prefix, &one_byte, shake256::<0x01, 137>);
        check::<136, 0x01, 600>(&prefix, &one_byte, shake256::<0x01, 600>);
    }
}
