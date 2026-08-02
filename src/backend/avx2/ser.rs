//! AVX2 bit-unpacking for ring-element deserialization.
//!
//! [`crate::ser`] has one hand-written unpacker per hot width plus a scalar sliding-window
//! fallback. This is a single routine that covers every width the crate uses (1..=13) with the
//! same instruction sequence, differing only in a table lookup.
//!
//! The observation that makes one routine enough: a group of 8 coefficients of `w` bits always
//! occupies exactly `w` bytes, and within that group coefficient `k` starts at byte `⌊kw/8⌋`
//! and bit `kw mod 8`. Since `w ≤ 13`, no coefficient spans more than three bytes, so a 4-byte
//! window per coefficient always covers it. So: broadcast the group's 16 bytes to both halves
//! of a vector, `vpshufb` each lane's window into place, `vpsrlvd` by the per-lane bit offset,
//! and mask. Eight coefficients per pass, with the group's width entering only through the
//! shuffle and shift vectors.

// Explicit `for i in 0..N` index loops, as in the rest of the crate: an `iter_mut().enumerate()`
// here does extract, but as an iterator state machine that the correspondence proof would then
// have to reason through.
#![allow(clippy::needless_range_loop)]

use crate::consts::RING_DEG;

use super::intrinsics::{
    and_si256, broadcastsi128_si256, load_i32, load_u8, load_u8x16, packus_epi32,
    permute4x64_epi64, set1_epi32, setzero_si256, shuffle_epi8, srlv_epi32, store_u16,
};

/// The widest packing the crate uses, and so the largest width [`PLANS`] covers
const MAX_BITS: usize = 13;

/// Number of 8-coefficient groups in one ring element
const GROUPS: usize = RING_DEG / 8;

/// How to extract one group of 8 coefficients of a given width.
///
/// `shuffle` is a `vpshufb` control selecting, for lane `k`, the four bytes starting at that
/// coefficient's first byte; `shift` is the matching `vpsrlvd` count. Aligned so both can be
/// loaded with an aligned move.
#[derive(Clone, Copy)]
#[repr(align(32))]
struct Plan {
    shuffle: [u8; 32],
    shift: [i32; 8],
}

/// Builds the plan for one width
const fn plan(bits: usize) -> Plan {
    let mut shuffle = [0u8; 32];
    let mut shift = [0i32; 8];
    let mut k = 0;
    while k < 8 {
        let offset = (k * bits) / 8;
        shift[k] = ((k * bits) % 8) as i32;
        let mut byte = 0;
        while byte < 4 {
            // `vpshufb` indexes within its own 128-bit half, and both halves hold the same
            // broadcast group, so lanes 4..7 can name bytes 0..15 just as lanes 0..3 do. The
            // largest index reached is ⌊7·13/8⌋ + 3 = 14, comfortably inside a half.
            shuffle[4 * k + byte] = (offset + byte) as u8;
            byte += 1;
        }
        k += 1;
    }
    Plan { shuffle, shift }
}

/// Builds every plan.
///
/// A `const fn` rather than the loop written directly in `PLANS`'s initializer, because aeneas
/// cannot translate a `const`/`static` initializer block that contains a loop — it reports an
/// internal error — whereas a `const fn` the initializer calls is translated normally.
const fn plans() -> [Plan; MAX_BITS + 1] {
    let mut plans = [plan(0); MAX_BITS + 1];
    let mut bits = 1;
    while bits <= MAX_BITS {
        plans[bits] = plan(bits);
        bits += 1;
    }
    plans
}

/// One plan per supported width. Index 0 is unused padding so `bits` indexes directly.
const PLANS: [Plan; MAX_BITS + 1] = plans();

/// Deserializes `RING_DEG` coefficients of `bits` bits each from `bytes`.
///
/// Produces exactly what [`crate::ser::deserialize_generic`] does. `bytes.len()` must be
/// `bits * RING_DEG / 8` and `bits` must be in `1..=13`, both of which the caller has already
/// asserted.
///
/// # Safety
///
/// Requires AVX2.
#[target_feature(enable = "avx2")]
pub(crate) fn deserialize(bytes: &[u8], bits: usize) -> [u16; RING_DEG] {
    let plan = &PLANS[bits];
    let shuffle = load_u8(&plan.shuffle, 0);
    let shift = load_i32(&plan.shift, 0);
    let mask = set1_epi32((1i32 << bits) - 1);

    // A group is 8 coefficients packed into `bits` bytes, and the vector path reads a whole
    // 16 bytes from a group's start, so the last few groups would read past the end of a
    // buffer that is only `32 * bits` long. Exactly `⌊15 / bits⌋` of them do — the ones
    // starting within 15 bytes of the end — so we copy that short remainder (at most 15 bytes)
    // into a zero-padded scratch buffer and read those groups from there. Everything stays
    // vectorized, and the copy is a few bytes rather than the whole buffer.
    let tail_groups = 15 / bits;
    let head_groups = GROUPS - tail_groups;
    let tail_start = head_groups * bits;
    let mut tail = [0u8; 32];
    tail[..bytes.len() - tail_start].copy_from_slice(&bytes[tail_start..]);

    let mut out = [0u16; RING_DEG];
    for pair in 0..GROUPS / 2 {
        let mut wide = [setzero_si256(); 2];
        for half in 0..2 {
            // For a group in the head, `group * bits + 16 ≤ 32 * bits = bytes.len()`, so the
            // load is in bounds. For one in the tail, its offset into `tail` is at most
            // `31 * bits - tail_start = (⌊15/bits⌋ - 1) * bits ≤ 15 - bits`, so the 16-byte
            // load stays inside the 32-byte scratch buffer.
            let group = 2 * pair + half;
            let raw = if group < head_groups {
                broadcastsi128_si256(load_u8x16(bytes, group * bits))
            } else {
                broadcastsi128_si256(load_u8x16(&tail, group * bits - tail_start))
            };
            let windows = shuffle_epi8(raw, shuffle);
            wide[half] = and_si256(srlv_epi32(windows, shift), mask);
        }
        // Every value is at most 13 bits, so the unsigned saturating pack is exact; the
        // qword permute repairs the lane interleaving `vpackusdw` introduces.
        let packed = packus_epi32(wide[0], wide[1]);
        // The store covers `out[16 * pair .. 16 * pair + 16]`, within
        // `RING_DEG = 16 * (GROUPS / 2)`.
        store_u16(&mut out, pair, permute4x64_epi64::<0b11_01_10_00>(packed));
    }

    out
}
