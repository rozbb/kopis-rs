//! Four-way TurboSHAKE on AVX2.
//!
//! Keccak's permutation is inherently serial — there is nothing inside one round to
//! vectorize — so the speedup comes from running four *independent* sponges side by side, one
//! per 64-bit lane of a `Vec256`. Kopis samples in batches that are exactly this shape: the
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

use super::intrinsics::{
    Vec256, andnot_si256, load_u8x32, or_si256, permute2x128_si256, set1_epi64x, setzero_si256,
    slli_epi64, srli_epi64, store_u8x32, unpackhi_epi64, unpacklo_epi64, xor_si256,
};

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

/// Rotates each 64-bit lane left by `L`.
///
/// `R` must be `64 - L`; it is a second parameter only because the shift counts have to be
/// literal immediates and Rust will not compute one from the other in that position.
#[inline]
#[target_feature(enable = "avx2")]
fn rotl<const L: i32, const R: i32>(v: Vec256) -> Vec256 {
    const {
        assert!(L + R == 64, "rotate halves must sum to the lane width");
    }
    or_si256(slli_epi64::<L>(v), srli_epi64::<R>(v))
}

/// Transposes a 4×4 block of 64-bit lanes.
///
/// Given four vectors each holding one word of all four sponges, returns four vectors each
/// holding four consecutive words of one sponge — and vice versa, since a transpose is its own
/// inverse. This is the whole of the conversion between the state's word-major layout and each
/// sponge's byte-major input and output, and it replaces doing that conversion a word and a
/// lane at a time.
#[inline]
#[target_feature(enable = "avx2")]
fn transpose4x64(a: Vec256, b: Vec256, c: Vec256, d: Vec256) -> (Vec256, Vec256, Vec256, Vec256) {
    let t0 = unpacklo_epi64(a, b);
    let t1 = unpackhi_epi64(a, b);
    let t2 = unpacklo_epi64(c, d);
    let t3 = unpackhi_epi64(c, d);
    (
        permute2x128_si256::<0x20>(t0, t2),
        permute2x128_si256::<0x20>(t1, t3),
        permute2x128_si256::<0x31>(t0, t2),
        permute2x128_si256::<0x31>(t1, t3),
    )
}

/// Loads the four consecutive 64-bit words starting at `word` from one lane's block.
#[inline]
#[target_feature(enable = "avx2")]
fn load_words<const RATE: usize>(block: &[u8; RATE], word: usize) -> Vec256 {
    load_u8x32(block, 8 * word)
}

/// The round constant for `round`, broadcast to all four lanes.
#[inline]
#[target_feature(enable = "avx2")]
fn round_const(round: usize) -> Vec256 {
    assert!(round < ROUNDS);
    // Keccak-p[1600, n] uses the *last* n of Keccak-f's constants, per FIPS 202 section 3.4.
    set1_epi64x(RC[24 - ROUNDS + round] as i64)
}

/// One output row of the fused ρ-π-χ step, as a `source, rotation` table.
///
/// `A[x, y]` lives at `5y + x`, and ρ-π is `B[y, 2x + 3y] = rot(A[x, y], r[x, y])`. Read by
/// destination rather than by source, that map sends each *row* of `B` to a diagonal of `A`:
/// row 0 comes from lanes 0, 6, 12, 18, 24, row 1 from 3, 9, 10, 16, 22, and so on. Every
/// diagonal meets all five columns exactly once, so a row needs the whole of `d` and nothing
/// else — which is what lets θ's per-lane xor, ρ, π and χ all happen here, and lets the `B`
/// array disappear rather than being written and read back once per round.
///
/// The five rotations within a row are independent and fill the pipeline, as in the older
/// 25-rotate form; what has gone is the round trip through memory between them and χ.
macro_rules! chi_row {
    ($src:ident, $dst:ident, $d:ident, $y:literal,
     $f0:literal, $r0:literal, $f1:literal, $r1:literal, $f2:literal, $r2:literal,
     $f3:literal, $r3:literal, $f4:literal, $r4:literal) => {{
        let t0 = rotl::<$r0, { 64 - $r0 }>(xor_si256($src[$f0], $d[$f0 % 5]));
        let t1 = rotl::<$r1, { 64 - $r1 }>(xor_si256($src[$f1], $d[$f1 % 5]));
        let t2 = rotl::<$r2, { 64 - $r2 }>(xor_si256($src[$f2], $d[$f2 % 5]));
        let t3 = rotl::<$r3, { 64 - $r3 }>(xor_si256($src[$f3], $d[$f3 % 5]));
        let t4 = rotl::<$r4, { 64 - $r4 }>(xor_si256($src[$f4], $d[$f4 % 5]));
        $dst[5 * $y] = xor_si256(t0, andnot_si256(t1, t2));
        $dst[5 * $y + 1] = xor_si256(t1, andnot_si256(t2, t3));
        $dst[5 * $y + 2] = xor_si256(t2, andnot_si256(t3, t4));
        $dst[5 * $y + 3] = xor_si256(t3, andnot_si256(t4, t0));
        $dst[5 * $y + 4] = xor_si256(t4, andnot_si256(t0, t1));
    }};
}

/// One round of Keccak-p[1600, 12], reading `src` and writing `dst`.
///
/// Same θ, ρ, π, χ, ι as the reference, in the same order and with the same constants; only the
/// scheduling differs. θ is split: the column fold and the `d` values are computed up front,
/// and θ's per-lane xor is deferred into [`chi_row`], where the lane is already in a register.
#[inline]
#[target_feature(enable = "avx2")]
fn round(src: &[Vec256; PLEN], dst: &mut [Vec256; PLEN], rc: Vec256) {
    // θ: fold each column, then mix each column with its two neighbours. `d` stays in registers
    // for the rest of the round — five vectors, which is what makes the fusion below fit.
    //
    // Written out rather than looped: the indices `(x ± 1) % 5` are computed, and aeneas cannot
    // symbolically execute an array read at a computed index, so a loop here does not extract.
    // Written out rather than looped or closed over: the mixing indices `(x ± 1) % 5` are
    // computed, and aeneas can neither execute an array read at a computed index nor produce a
    // workable model of a closure — it extracts one as a `Fn` trait instance, which every proof
    // about this function would then have to unfold.
    let c0 = xor_si256(
        xor_si256(xor_si256(src[0], src[5]), xor_si256(src[10], src[15])),
        src[20],
    );
    let c1 = xor_si256(
        xor_si256(xor_si256(src[1], src[6]), xor_si256(src[11], src[16])),
        src[21],
    );
    let c2 = xor_si256(
        xor_si256(xor_si256(src[2], src[7]), xor_si256(src[12], src[17])),
        src[22],
    );
    let c3 = xor_si256(
        xor_si256(xor_si256(src[3], src[8]), xor_si256(src[13], src[18])),
        src[23],
    );
    let c4 = xor_si256(
        xor_si256(xor_si256(src[4], src[9]), xor_si256(src[14], src[19])),
        src[24],
    );
    let d = [
        xor_si256(c4, rotl::<1, 63>(c1)),
        xor_si256(c0, rotl::<1, 63>(c2)),
        xor_si256(c1, rotl::<1, 63>(c3)),
        xor_si256(c2, rotl::<1, 63>(c4)),
        xor_si256(c3, rotl::<1, 63>(c0)),
    ];

    // The rest of θ, then ρ, π and χ, one output row at a time.
    chi_row!(src, dst, d, 0, 0, 0, 6, 44, 12, 43, 18, 21, 24, 14);
    chi_row!(src, dst, d, 1, 3, 28, 9, 20, 10, 3, 16, 45, 22, 61);
    chi_row!(src, dst, d, 2, 1, 1, 7, 6, 13, 25, 19, 8, 20, 18);
    chi_row!(src, dst, d, 3, 4, 27, 5, 36, 11, 10, 17, 15, 23, 56);
    chi_row!(src, dst, d, 4, 2, 62, 8, 55, 14, 39, 15, 41, 21, 2);

    // ι
    dst[0] = xor_si256(dst[0], rc);
}

/// Applies Keccak-p[1600, 12] to four independent states held one per 64-bit lane
#[target_feature(enable = "avx2")]
fn permute(state: &mut [Vec256; PLEN]) {
    const {
        assert!(
            ROUNDS.is_multiple_of(2),
            "the round pair below assumes an even round count"
        );
    }

    // π is a permutation, so a round cannot write into the array it is reading. Rounds alternate
    // between the state and one scratch buffer instead, taken two at a time so that the second
    // of each pair lands back in `state` and nothing is ever copied.
    let mut scratch = [setzero_si256(); PLEN];
    for pair in 0..ROUNDS / 2 {
        round(state, &mut scratch, round_const(2 * pair));
        round(&scratch, state, round_const(2 * pair + 1));
    }
}

/// Builds one lane's padded input block.
///
/// TurboSHAKE's padding: the message, then the domain separator at the first free byte, then
/// the high bit of the block's last byte. The whole message fits in this one block, which is
/// what lets absorption be "build the block" with no state machine.
#[inline]
#[target_feature(enable = "avx2")]
fn pad_block<const RATE: usize, const DS: u8, const S: usize>(
    prefix: &[u8; 32],
    suffix: &[u8; S],
) -> [u8; RATE] {
    let mut bytes = [0u8; RATE];
    bytes[..32].copy_from_slice(prefix);
    bytes[32..32 + S].copy_from_slice(suffix);
    bytes[32 + S] = DS;
    bytes[RATE - 1] |= 0x80;
    bytes
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
#[allow(clippy::manual_div_ceil)] // See comment below about div_ceil
pub(crate) fn xof4<const RATE: usize, const DS: u8, const S: usize, const N: usize>(
    prefix: &[u8; 32],
    suffixes: &[[u8; S]; 4],
    out: &mut [[u8; N]; 4],
) {
    const {
        assert!(RATE == 168 || RATE == 136, "unsupported TurboSHAKE rate");
        assert!(DS >= 0x01 && DS <= 0x7F, "invalid domain separator");
        assert!(
            32 + S < RATE,
            "input must leave room for the padding in one block"
        );
    }

    // The entire input fits in one block, so absorption is just "build the block". Pad as
    // TurboSHAKE does: the domain separator at the first free byte, and the high bit of the
    // block's last byte.
    // Four separate arrays rather than a `[[u8; RATE]; 4]`: aeneas cannot symbolically execute
    // a borrow into a nested array, and the loads below need one reference per lane.
    let s0 = suffixes[0];
    let s1 = suffixes[1];
    let s2 = suffixes[2];
    let s3 = suffixes[3];
    let b0 = pad_block::<RATE, DS, S>(prefix, &s0);
    let b1 = pad_block::<RATE, DS, S>(prefix, &s1);
    let b2 = pad_block::<RATE, DS, S>(prefix, &s2);
    let b3 = pad_block::<RATE, DS, S>(prefix, &s3);

    // Transpose the four blocks into the lane-parallel state. Words past the rate stay zero,
    // which is the capacity. Four words at a time where four remain — one 32-byte load per lane
    // and eight shuffles, rather than sixteen 8-byte copies — then any odd words singly. The
    // split is on the word index alone, so it does not depend on what the block contains.
    let mut state = [setzero_si256(); PLEN];
    let words = RATE / 8;
    let mut word = 0;
    while word + 4 <= words {
        let (r0, r1, r2, r3) = transpose4x64(
            load_words(&b0, word),
            load_words(&b1, word),
            load_words(&b2, word),
            load_words(&b3, word),
        );
        // Element by element, not `copy_from_slice` on `state[word..word + 4]`: aeneas cannot
        // build a mutable subslice of an array at a computed offset.
        state[word] = r0;
        state[word + 1] = r1;
        state[word + 2] = r2;
        state[word + 3] = r3;
        word += 4;
    }
    while word < words {
        // Gather the four lanes' copies of this one word into the layout a vector load wants:
        // lane `l`'s eight bytes at `8 * l`. Little-endian throughout, as Keccak is.
        let mut packed = [0u8; 32];
        for i in 0..8 {
            packed[i] = b0[8 * word + i];
            packed[8 + i] = b1[8 * word + i];
            packed[16 + i] = b2[8 * word + i];
            packed[24 + i] = b3[8 * word + i];
        }
        state[word] = load_u8x32(&packed, 0);
        word += 1;
    }

    // Squeeze. Each permutation yields one rate-sized block per lane.
    let mut done = 0;
    while done < N {
        permute(&mut state);

        let take = core::cmp::min(RATE, N - done);
        // `(take + 7) / 8`, not `take.div_ceil(8)`: charon leaves `div_ceil` opaque, so the
        // Lean proof of this loop would have to axiomatize a stdlib function. `take <= RATE
        // <= 200`, so the `+ 7` cannot overflow.
        let words = (take + 7) / 8;
        let mut word = 0;

        // Four words at a time, for as long as four whole words remain *and* the resulting
        // 32-byte store lands entirely inside `out`. Both conditions are on lengths only.
        while word + 4 <= words && done + 8 * word + 32 <= N {
            let (l0, l1, l2, l3) = transpose4x64(
                state[word],
                state[word + 1],
                state[word + 2],
                state[word + 3],
            );
            let start = done + 8 * word;
            store_u8x32(&mut out[0], start, l0);
            store_u8x32(&mut out[1], start, l1);
            store_u8x32(&mut out[2], start, l2);
            store_u8x32(&mut out[3], start, l3);
            word += 4;
        }

        // Whatever is left: a partial group of words, and a final word the output may only
        // want part of.
        while word < words {
            // The mirror of the absorb tail: one word of all four lanes, spread out to bytes.
            let mut packed = [0u8; 32];
            store_u8x32(&mut packed, 0, state[word]);
            for lane in 0..4 {
                // The last word of a partial output contributes only part of itself.
                let start = done + 8 * word;
                let len = core::cmp::min(8, N - start);
                for i in 0..len {
                    out[lane][start + i] = packed[8 * lane + i];
                }
            }
            word += 1;
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
    // for that lane's input.
    //
    // The output lengths below are chosen for the squeeze's two paths: it moves four 64-bit
    // words at a time while four whole words remain and the resulting 32-byte store still fits
    // in the output, and one word at a time after that. So the interesting lengths are around
    // multiples of 32 (where the wide path stops), around multiples of 8 (where a word becomes
    // partial), and around the rate (where a block ends and another permutation follows). Both
    // rates are covered, and a rate is not a multiple of 32 either way: 168 is 5 wide groups
    // plus a word, 136 is 4 plus a word, so the narrow tail runs on every full block.
    //
    // Suffix lengths vary too. They are uniform across lanes within a call, because the length
    // is a const generic: `xof4` cannot take `&[&[u8]; 4]`, since aeneas rejects nested borrows.
    #[test]
    fn matches_scalar() {
        if !super::super::available() {
            return;
        }

        fn check<const RATE: usize, const DS: u8, const S: usize, const N: usize>(
            prefix: &[u8; 32],
            suffixes: &[[u8; S]; 4],
            scalar: impl Fn(&[u8], &[u8], &mut [u8; N]),
        ) {
            let mut vector = [[0u8; N]; 4];
            // SAFETY: guarded by the `available()` check above.
            unsafe { xof4::<RATE, DS, S, N>(prefix, suffixes, &mut vector) };

            for lane in 0..4 {
                let mut expected = [0u8; N];
                scalar(prefix, &suffixes[lane], &mut expected);
                assert_eq!(
                    vector[lane],
                    expected,
                    "lane {lane}, rate {RATE}, {N} bytes, suffix {} bytes",
                    suffixes[lane].len()
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

        // A few unrelated prefixes, so no result rests on one seed.
        let prefixes: [[u8; 32]; 3] = [
            core::array::from_fn(|i| (7 * i + 3) as u8),
            [0u8; 32],
            core::array::from_fn(|i| (251u16.wrapping_mul(i as u16 + 1) ^ 0xA5) as u8),
        ];

        // Suffix shapes: the two Kopis uses, none at all, ones of differing length within a
        // single call, and long ones that push the padding deep into the block.
        let two: [[u8; 2]; 4] = [[0, 0], [0, 1], [1, 0], [2, 3]];
        let one: [[u8; 1]; 4] = [[0], [1], [2], [255]];
        let empty: [[u8; 0]; 4] = [[], [], [], []];
        let long: [[u8; 64]; 4] = core::array::from_fn(|l| core::array::from_fn(|i| (i + l) as u8));

        for prefix in &prefixes {
            // Lengths shorter than one wide group, so the narrow path does all the work.
            check::<168, 0x1F, 2, 1>(prefix, &two, shake128::<0x1F, 1>);
            check::<168, 0x1F, 2, 7>(prefix, &two, shake128::<0x1F, 7>);
            check::<168, 0x1F, 2, 8>(prefix, &two, shake128::<0x1F, 8>);
            check::<168, 0x1F, 2, 9>(prefix, &two, shake128::<0x1F, 9>);
            check::<168, 0x1F, 0, 31>(prefix, &empty, shake128::<0x1F, 31>);

            // The wide path switching on, and its boundary with the narrow tail.
            check::<168, 0x1F, 2, 32>(prefix, &two, shake128::<0x1F, 32>);
            check::<168, 0x1F, 2, 33>(prefix, &two, shake128::<0x1F, 33>);
            check::<168, 0x1F, 64, 39>(prefix, &long, shake128::<0x1F, 39>);
            check::<168, 0x1F, 2, 40>(prefix, &two, shake128::<0x1F, 40>);
            check::<168, 0x02, 2, 160>(prefix, &two, shake128::<0x02, 160>);
            check::<168, 0x02, 64, 161>(prefix, &long, shake128::<0x02, 161>);

            // Block boundaries: one short of the rate, exactly the rate, one over.
            check::<168, 0x1F, 2, 167>(prefix, &two, shake128::<0x1F, 167>);
            check::<168, 0x1F, 2, 168>(prefix, &two, shake128::<0x1F, 168>);
            check::<168, 0x1F, 64, 169>(prefix, &long, shake128::<0x1F, 169>);
            check::<168, 0x7F, 2, 171>(prefix, &two, shake128::<0x7F, 171>);

            // Several blocks, including the length Kopis actually squeezes.
            check::<168, 0x02, 2, 336>(prefix, &two, shake128::<0x02, 336>);
            check::<168, 0x02, 1, 337>(prefix, &one, shake128::<0x02, 337>);
            check::<168, 0x02, 2, 416>(prefix, &two, shake128::<0x02, 416>);
            check::<168, 0x02, 64, 512>(prefix, &long, shake128::<0x02, 512>);

            // The same shape of coverage at rate 136, whose block is 17 words.
            check::<136, 0x01, 1, 1>(prefix, &one, shake256::<0x01, 1>);
            check::<136, 0x01, 64, 31>(prefix, &long, shake256::<0x01, 31>);
            check::<136, 0x01, 1, 32>(prefix, &one, shake256::<0x01, 32>);
            check::<136, 0x01, 1, 33>(prefix, &one, shake256::<0x01, 33>);
            check::<136, 0x01, 0, 127>(prefix, &empty, shake256::<0x01, 127>);
            check::<136, 0x01, 1, 128>(prefix, &one, shake256::<0x01, 128>);
            check::<136, 0x01, 1, 129>(prefix, &one, shake256::<0x01, 129>);
            check::<136, 0x01, 1, 135>(prefix, &one, shake256::<0x01, 135>);
            check::<136, 0x01, 1, 136>(prefix, &one, shake256::<0x01, 136>);
            check::<136, 0x01, 1, 137>(prefix, &one, shake256::<0x01, 137>);
            check::<136, 0x03, 1, 192>(prefix, &one, shake256::<0x03, 192>);
            check::<136, 0x03, 64, 256>(prefix, &long, shake256::<0x03, 256>);
            check::<136, 0x03, 1, 320>(prefix, &one, shake256::<0x03, 320>);
            check::<136, 0x01, 1, 600>(prefix, &one, shake256::<0x01, 600>);
        }
    }
}
