//! Two-way TurboSHAKE on NEON, using the ARMv8.2 SHA3 extension.
//!
//! Keccak's permutation is inherently serial — there is nothing inside one round to vectorize —
//! so the speedup comes from running *independent* sponges side by side, one per 64-bit lane.
//! Kopis samples in exactly that shape: the public matrix is ℓ² independent XOF calls that differ
//! only in a two-byte index, and the secret is ℓ more.
//!
//! A `uint64x2_t` holds two of those lanes where AVX2's `Vec256` holds four, so this is the
//! two-way counterpart of [`super::super::avx2::keccak`]: the same scheme, the same round
//! constants, the same fused round read by destination, half the batch. Two-way also *wastes*
//! less on the batch sizes Kopis actually uses — ℓ = 3 means nine matrix entries, which is five
//! two-lane batches with one idle lane against three four-lane batches with three idle ones.
//!
//! # Why the SHA3 extension
//!
//! Plain NEON would be a poor trade here. Scalar AArch64 gets its rotates free in the second
//! operand, so a scalar Keccak round is already tight, and a two-way `uint64x2_t` version that
//! has to spell each rotate as a shift-shift-or does not clearly beat two scalar sponges.
//!
//! FEAT_SHA3 is what changes the arithmetic, because all four of its instructions are Keccak
//! steps rather than general bit tricks:
//!
//! * `eor3` folds a three-way xor, so θ's five-lane column fold is two instructions, not four.
//! * `rax1` is `a ^ rotl(b, 1)` — exactly θ's mixing of a column with its neighbour.
//! * `xar` is `rotr(a ^ b, imm)`, which is θ's per-lane xor *and* ρ's rotation in one.
//! * `bcax` is `a ^ (b & ~c)`, which is the whole of χ for one lane.
//!
//! That takes a round to 10 `eor3` + 5 `rax1` + 25 `xar` + 25 `bcax` + 1 `eor` — 66 vector
//! instructions covering two sponges, which is what the generated code actually contains. Round
//! for round against the `turboshake` crate's scalar sponge that works out to roughly 1.7x per
//! lane, measured; the rest of the win is the batching, which halves the number of permutations.
//!
//! Because this is the bulk of what the NEON backend buys, the extension is a condition on the
//! whole backend rather than on this module alone: `build.rs` decides at build time — the crate
//! is `no_std` and `core` has no AArch64 run-time feature detection — and a target without it
//! gets the portable serial code, scalar sponge included.
//!
//! # Scope
//!
//! Only the shape Kopis needs is implemented: an input short enough to fit in a single block (a
//! 32-byte seed plus a one- or two-byte index), and an equal-length output for both lanes. That
//! removes the whole absorb state machine — one block is built, xored in, and squeezed.
//!
//! The permutation is a direct transliteration of the reference Keccak-p[1600, 12]: same θ, ρ,
//! π, χ, ι in the same order, same rotation offsets, and the same round constants (TurboSHAKE's
//! 12 rounds are the *last* 12 of Keccak-f[1600], per FIPS 202 §3.4). `matches_scalar` checks
//! every lane against the `turboshake` crate; the Lean correspondence proof is what will replace
//! that as the primary evidence, and like the rest of this backend it reaches the instruction set
//! only through [`super::intrinsics`] so that it can be extracted at all.

use super::intrinsics::{
    Vec128, bcax, dup_n_u64, eor, eor3, load_u8x16, rax1, set_u64x2, store_u8x16, trn1_64, trn2_64,
    xar,
};

/// Lanes in the Keccak state
const PLEN: usize = 25;

/// Rounds in Keccak-p[1600, 12], the permutation TurboSHAKE is built on
const ROUNDS: usize = 12;

/// Sponges run side by side, one per 64-bit lane of a `uint64x2_t`
pub(crate) const WAYS: usize = 2;

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

/// θ's per-lane xor followed by ρ's rotation, as one `xar`.
///
/// `xar` computes `rotr(a ^ b, IMM)`, so a *left* rotation by `r` — which is what ρ is defined
/// as — is a right rotation by `64 - r`. The `% 64` keeps `r = 0` at 0 rather than turning it
/// into an out-of-range 64; lane 0 is the one entry of ρ with no rotation.
macro_rules! theta_rho {
    ($src:ident, $d:ident, $f:literal, $r:literal) => {
        xar::<{ (64 - $r) % 64 }>($src[$f], $d[$f % 5])
    };
}

/// One output row of the fused ρ-π-χ step, as a `source, rotation` table.
///
/// `A[x, y]` lives at `5y + x`, and ρ-π is `B[y, 2x + 3y] = rot(A[x, y], r[x, y])`. Read by
/// destination rather than by source, that map sends each *row* of `B` to a diagonal of `A`: row
/// 0 comes from lanes 0, 6, 12, 18, 24, row 1 from 3, 9, 10, 16, 22, and so on. Every diagonal
/// meets all five columns exactly once, so a row needs the whole of `d` and nothing else — which
/// is what lets θ's per-lane xor, ρ, π and χ all happen here, and lets the `B` array disappear
/// rather than being written and read back once per round.
///
/// χ is `B[x] ^ (~B[x + 1] & B[x + 2])`, which is `bcax(B[x], B[x + 2], B[x + 1])` — note the
/// swapped last two arguments, since `bcax` negates its *third* operand.
macro_rules! chi_row {
    ($src:ident, $dst:ident, $d:ident, $y:literal,
     $f0:literal, $r0:literal, $f1:literal, $r1:literal, $f2:literal, $r2:literal,
     $f3:literal, $r3:literal, $f4:literal, $r4:literal) => {{
        let t0 = theta_rho!($src, $d, $f0, $r0);
        let t1 = theta_rho!($src, $d, $f1, $r1);
        let t2 = theta_rho!($src, $d, $f2, $r2);
        let t3 = theta_rho!($src, $d, $f3, $r3);
        let t4 = theta_rho!($src, $d, $f4, $r4);
        $dst[5 * $y] = bcax(t0, t2, t1);
        $dst[5 * $y + 1] = bcax(t1, t3, t2);
        $dst[5 * $y + 2] = bcax(t2, t4, t3);
        $dst[5 * $y + 3] = bcax(t3, t0, t4);
        $dst[5 * $y + 4] = bcax(t4, t1, t0);
    }};
}

/// The round constant for `round`, broadcast to both lanes.
#[inline]
#[target_feature(enable = "neon,sha3")]
fn round_const(round: usize) -> Vec128 {
    debug_assert!(round < ROUNDS);
    // Keccak-p[1600, n] uses the *last* n of Keccak-f's constants, per FIPS 202 section 3.4.
    dup_n_u64(RC[24 - ROUNDS + round])
}

/// One round of Keccak-p[1600, 12], reading `src` and writing `dst`.
///
/// Same θ, ρ, π, χ, ι as the reference, in the same order and with the same constants; only the
/// scheduling differs. θ is split: the column fold and the `d` values are computed up front, and
/// θ's per-lane xor is deferred into [`chi_row`], where the lane is already in a register.
#[inline]
#[target_feature(enable = "neon,sha3")]
fn round(src: &[Vec128; PLEN], dst: &mut [Vec128; PLEN], rc: Vec128) {
    // θ: fold each column, then mix each column with its two neighbours. `d` stays in registers
    // for the rest of the round — five vectors, which is what makes the fusion below fit.
    // `eor3` takes each five-lane fold to two instructions.
    let c0 = eor3(eor3(src[0], src[5], src[10]), src[15], src[20]);
    let c1 = eor3(eor3(src[1], src[6], src[11]), src[16], src[21]);
    let c2 = eor3(eor3(src[2], src[7], src[12]), src[17], src[22]);
    let c3 = eor3(eor3(src[3], src[8], src[13]), src[18], src[23]);
    let c4 = eor3(eor3(src[4], src[9], src[14]), src[19], src[24]);

    // `d[x] = c[x - 1] ^ rotl(c[x + 1], 1)`, which is exactly what `rax1` computes.
    let d = [
        rax1(c4, c1),
        rax1(c0, c2),
        rax1(c1, c3),
        rax1(c2, c4),
        rax1(c3, c0),
    ];

    // The rest of θ, then ρ, π and χ, one output row at a time.
    chi_row!(src, dst, d, 0, 0, 0, 6, 44, 12, 43, 18, 21, 24, 14);
    chi_row!(src, dst, d, 1, 3, 28, 9, 20, 10, 3, 16, 45, 22, 61);
    chi_row!(src, dst, d, 2, 1, 1, 7, 6, 13, 25, 19, 8, 20, 18);
    chi_row!(src, dst, d, 3, 4, 27, 5, 36, 11, 10, 17, 15, 23, 56);
    chi_row!(src, dst, d, 4, 2, 62, 8, 55, 14, 39, 15, 41, 21, 2);

    // ι
    dst[0] = eor(dst[0], rc);
}

/// Applies Keccak-p[1600, 12] to two independent states held one per 64-bit lane
#[target_feature(enable = "neon,sha3")]
fn permute(state: &mut [Vec128; PLEN]) {
    const {
        assert!(
            ROUNDS.is_multiple_of(2),
            "the round pair below assumes an even round count"
        );
    }

    // π is a permutation, so a round cannot write into the array it is reading. Rounds alternate
    // between the state and one scratch buffer instead, taken two at a time so that the second of
    // each pair lands back in `state` and nothing is ever copied.
    let mut scratch = [dup_n_u64(0); PLEN];
    for pair in 0..ROUNDS / 2 {
        round(state, &mut scratch, round_const(2 * pair));
        round(&scratch, state, round_const(2 * pair + 1));
    }
}

/// Builds one lane's padded input block.
///
/// TurboSHAKE's padding: the message, then the domain separator at the first free byte, then the
/// high bit of the block's last byte. The whole message fits in this one block, which is what
/// lets absorption be "build the block" with no state machine.
#[inline]
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

/// Reads the two 64-bit words at `word` and `word + 1` of one lane's block.
///
/// The load is byte-addressed, so the block needs no alignment beyond its own; `8 * word + 16`
/// must be within it, which [`load_u8x16`] checks.
#[inline]
#[target_feature(enable = "neon")]
fn load_words<const RATE: usize>(block: &[u8; RATE], word: usize) -> Vec128 {
    load_u8x16(block, 8 * word)
}

/// Runs two TurboSHAKE instances at once, each absorbing `prefix || suffixes[lane]` and squeezing
/// `N` bytes into `out[lane]`.
///
/// `RATE` selects the variant: 168 for TurboSHAKE128, 136 for TurboSHAKE256. `DS` is the domain
/// separator. Every `prefix || suffix` must fit in one block with room for the padding, i.e.
/// `32 + suffix.len() < RATE`, which holds by a wide margin for the 1- and 2-byte indices Kopis
/// uses.
///
/// # Safety
///
/// Requires NEON and the SHA3 extension.
#[target_feature(enable = "neon,sha3")]
pub(crate) fn xof2<const RATE: usize, const DS: u8, const S: usize, const N: usize>(
    prefix: &[u8; 32],
    suffixes: &[[u8; S]; WAYS],
    out: &mut [[u8; N]; WAYS],
) {
    const {
        assert!(RATE == 168 || RATE == 136, "unsupported TurboSHAKE rate");
        assert!(DS >= 0x01 && DS <= 0x7F, "invalid domain separator");
        assert!(
            32 + S < RATE,
            "input must leave room for the padding in one block"
        );
        // Both rates are an odd number of words, so the paths below always leave exactly one
        // word for the narrow tail. Nothing depends on that being *one*, but it is worth
        // recording that the tail is never dead code.
        assert!(
            !(RATE / 8).is_multiple_of(2),
            "rate should be an odd word count"
        );
    }

    // The entire input fits in one block, so absorption is just "build the block".
    let b0 = pad_block::<RATE, DS, S>(prefix, &suffixes[0]);
    let b1 = pad_block::<RATE, DS, S>(prefix, &suffixes[1]);

    // Transpose the two blocks into the lane-parallel state: state word `w` holds `b0`'s word `w`
    // in lane 0 and `b1`'s in lane 1. Words past the rate stay zero, which is the capacity.
    //
    // A 2x2 transpose is just `trn1`/`trn2`, so two words are placed with two loads and two
    // shuffles rather than four narrow loads and four inserts. The split is on the word index
    // alone, so it does not depend on what the block contains.
    let mut state = [dup_n_u64(0); PLEN];
    let words = RATE / 8;
    let mut word = 0;
    while word + 2 <= words {
        // `word + 2 <= words` gives `8 * word + 16 <= RATE` for both blocks.
        let v0 = load_words(&b0, word);
        let v1 = load_words(&b1, word);
        state[word] = trn1_64(v0, v1);
        state[word + 1] = trn2_64(v0, v1);
        word += 2;
    }
    while word < words {
        // The odd last word, built scalar-side. Little-endian throughout, as Keccak is.
        let lane0 = u64::from_le_bytes(read8(&b0, 8 * word));
        let lane1 = u64::from_le_bytes(read8(&b1, 8 * word));
        state[word] = set_u64x2(lane0, lane1);
        word += 1;
    }

    // Squeeze. Each permutation yields one rate-sized block per lane.
    let (head, tail) = out.split_at_mut(1);
    let out0 = &mut head[0];
    let out1 = &mut tail[0];

    let mut done = 0;
    while done < N {
        permute(&mut state);

        let take = core::cmp::min(RATE, N - done);
        let words = take.div_ceil(8);
        let mut word = 0;

        // Two words at a time, for as long as two whole words remain *and* the resulting 16-byte
        // store lands entirely inside the output. Both conditions are on lengths only.
        while word + 2 <= words && done + 8 * word + 16 <= N {
            let v0 = trn1_64(state[word], state[word + 1]);
            let v1 = trn2_64(state[word], state[word + 1]);
            let start = done + 8 * word;
            // The loop condition puts the 16 bytes at `start` inside both outputs, which are `N`
            // bytes each. The two stores are to distinct arrays.
            store_u8x16(out0, start, v0);
            store_u8x16(out1, start, v1);
            word += 2;
        }

        // Whatever is left: a partial group of words, and a final word the output may only want
        // part of.
        while word < words {
            // The mirror of the absorb tail: one word of both lanes, spread out to bytes.
            let mut packed = [0u8; 16];
            store_u8x16(&mut packed, 0, state[word]);

            let start = done + 8 * word;
            // The last word of a partial output contributes only part of itself.
            let len = core::cmp::min(8, N - start);
            out0[start..start + len].copy_from_slice(&packed[..len]);
            out1[start..start + len].copy_from_slice(&packed[8..8 + len]);
            word += 1;
        }

        done += take;
    }
}

/// The eight bytes of `block` starting at `offset`, as an array.
///
/// A helper only because `copy_from_slice` onto a fixed-size array needs a `try_into` that would
/// otherwise want an `expect` at each call site, and the crate warns on `unwrap_used`.
#[inline]
fn read8<const RATE: usize>(block: &[u8; RATE], offset: usize) -> [u8; 8] {
    let mut word = [0u8; 8];
    word.copy_from_slice(&block[offset..offset + 8]);
    word
}

#[cfg(test)]
mod test {
    use super::*;

    use turboshake::digest::{ExtendableOutput, Update, XofReader};
    use turboshake::{CTurboShake128, CTurboShake256};

    // Each lane must reproduce, byte for byte, what the scalar TurboSHAKE would have produced for
    // that lane's input.
    //
    // The output lengths below are chosen for the squeeze's two paths: it moves two 64-bit words
    // at a time while two whole words remain and the resulting 16-byte store still fits in the
    // output, and one word at a time after that. So the interesting lengths are around multiples
    // of 16 (where the wide path stops), around multiples of 8 (where a word becomes partial),
    // and around the rate (where a block ends and another permutation follows). Both rates are
    // covered, and each is an odd number of words — 168 is 21, 136 is 17 — so the narrow tail
    // runs on every full block.
    //
    // Suffix lengths vary too. They are uniform across lanes within a call because the length is
    // a const generic, matching the AVX2 sibling's shape.
    #[test]
    fn matches_scalar() {
        if !super::super::available() {
            return;
        }

        fn check<const RATE: usize, const DS: u8, const S: usize, const N: usize>(
            prefix: &[u8; 32],
            suffixes: &[[u8; S]; WAYS],
            scalar: impl Fn(&[u8], &[u8], &mut [u8; N]),
        ) {
            let mut vector = [[0u8; N]; WAYS];
            // SAFETY: guarded by the `available()` check above, and this module is only compiled
            // when `build.rs` has confirmed the SHA3 extension for the target.
            unsafe { xof2::<RATE, DS, S, N>(prefix, suffixes, &mut vector) };

            for lane in 0..WAYS {
                let mut expected = [0u8; N];
                scalar(prefix, &suffixes[lane], &mut expected);
                assert_eq!(
                    vector[lane], expected,
                    "lane {lane}, rate {RATE}, {N} bytes, suffix {S} bytes"
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

        // Suffix shapes: the two Kopis uses, none at all, and long ones that push the padding
        // deep into the block. Lanes differ within each call.
        let two: [[u8; 2]; WAYS] = [[0, 1], [2, 3]];
        let one: [[u8; 1]; WAYS] = [[0], [255]];
        let empty: [[u8; 0]; WAYS] = [[], []];
        let long: [[u8; 64]; WAYS] =
            core::array::from_fn(|l| core::array::from_fn(|i| (i + l) as u8));

        for prefix in &prefixes {
            // Lengths shorter than one wide group, so the narrow path does all the work.
            check::<168, 0x1F, 2, 1>(prefix, &two, shake128::<0x1F, 1>);
            check::<168, 0x1F, 2, 7>(prefix, &two, shake128::<0x1F, 7>);
            check::<168, 0x1F, 2, 8>(prefix, &two, shake128::<0x1F, 8>);
            check::<168, 0x1F, 2, 9>(prefix, &two, shake128::<0x1F, 9>);
            check::<168, 0x1F, 0, 15>(prefix, &empty, shake128::<0x1F, 15>);

            // The wide path switching on, and its boundary with the narrow tail.
            check::<168, 0x1F, 2, 16>(prefix, &two, shake128::<0x1F, 16>);
            check::<168, 0x1F, 2, 17>(prefix, &two, shake128::<0x1F, 17>);
            check::<168, 0x1F, 64, 23>(prefix, &long, shake128::<0x1F, 23>);
            check::<168, 0x1F, 2, 24>(prefix, &two, shake128::<0x1F, 24>);
            check::<168, 0x1F, 2, 31>(prefix, &two, shake128::<0x1F, 31>);
            check::<168, 0x1F, 2, 32>(prefix, &two, shake128::<0x1F, 32>);
            check::<168, 0x02, 2, 160>(prefix, &two, shake128::<0x02, 160>);
            check::<168, 0x02, 64, 161>(prefix, &long, shake128::<0x02, 161>);

            // Block boundaries: one short of the rate, exactly the rate, one over.
            check::<168, 0x1F, 2, 167>(prefix, &two, shake128::<0x1F, 167>);
            check::<168, 0x1F, 2, 168>(prefix, &two, shake128::<0x1F, 168>);
            check::<168, 0x1F, 64, 169>(prefix, &long, shake128::<0x1F, 169>);
            check::<168, 0x7F, 2, 171>(prefix, &two, shake128::<0x7F, 171>);

            // Several blocks, including the length Kopis actually squeezes for a matrix entry.
            check::<168, 0x02, 2, 336>(prefix, &two, shake128::<0x02, 336>);
            check::<168, 0x02, 1, 337>(prefix, &one, shake128::<0x02, 337>);
            check::<168, 0x02, 2, 416>(prefix, &two, shake128::<0x02, 416>);
            check::<168, 0x02, 64, 512>(prefix, &long, shake128::<0x02, 512>);

            // The same shape of coverage at rate 136, whose block is 17 words.
            check::<136, 0x01, 1, 1>(prefix, &one, shake256::<0x01, 1>);
            check::<136, 0x01, 64, 15>(prefix, &long, shake256::<0x01, 15>);
            check::<136, 0x01, 1, 16>(prefix, &one, shake256::<0x01, 16>);
            check::<136, 0x01, 1, 17>(prefix, &one, shake256::<0x01, 17>);
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
