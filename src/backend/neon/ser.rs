//! NEON bit-unpacking for ring-element deserialization.
//!
//! Like [`super::super::avx2::ser`], this is a single routine that covers every width the crate
//! uses (1..=13) with one instruction sequence, differing only in a table lookup.
//!
//! The observation that makes one routine enough: a group of 8 coefficients of `w` bits always
//! occupies exactly `w` bytes, and within that group coefficient `k` starts at byte `⌊kw/8⌋`
//! and bit `kw mod 8`. Since `w ≤ 13`, no coefficient spans more than three bytes, so a 4-byte
//! window per coefficient always covers it. NEON works four lanes at a time, so each group is
//! done in two passes of four coefficients: load the group's 16 bytes, `tbl` each lane's window
//! into place, logical-shift each lane right by its bit offset (`ushl` with a negative count),
//! and mask. The group's width enters only through the shuffle and shift vectors.

// Explicit `for i in 0..N` index loops, as in the rest of the crate: an `iter_mut().enumerate()`
// here does extract, but as an iterator state machine that the correspondence proof would then
// have to reason through.
#![allow(clippy::needless_range_loop)]

use crate::consts::RING_DEG;

use super::intrinsics::{
    and, dup_n_u32, load_i32, load_u8x16, store_u16, tbl1_u8, ushl_u32, xtn_pair_32,
};

/// The widest packing the crate uses, and so the largest width [`PLANS`] covers
const MAX_BITS: usize = 13;

/// Number of 8-coefficient groups in one ring element
const GROUPS: usize = RING_DEG / 8;

/// How to extract one group of 8 coefficients of a given width.
///
/// `shuffle` is a `tbl` control selecting, for lane `k`, the four bytes starting at that
/// coefficient's first byte (lanes 0..3 in the first 16 bytes, lanes 4..7 in the second, each
/// indexing the same 16-byte group). `shift` is the matching *negated* `ushl` count, so a
/// positive right shift becomes the negative left shift NEON wants. Aligned so each 16-byte half
/// loads with an aligned move.
#[derive(Clone, Copy)]
#[repr(align(16))]
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
        shift[k] = -(((k * bits) % 8) as i32);
        let mut byte = 0;
        while byte < 4 {
            // `tbl` indexes the whole 16-byte group, and every coefficient's window lies
            // inside it: the largest byte reached is ⌊7·13/8⌋ + 3 = 14 < 16.
            shuffle[4 * k + byte] = (offset + byte) as u8;
            byte += 1;
        }
        k += 1;
    }
    Plan { shuffle, shift }
}

/// Builds every plan.
///
/// A `const fn` rather than the loop written directly in [`PLANS`]'s initializer, because aeneas
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
/// Requires NEON.
#[target_feature(enable = "neon")]
pub(crate) fn deserialize(bytes: &[u8], bits: usize) -> [u16; RING_DEG] {
    let plan = &PLANS[bits];
    let shuf_lo = load_u8x16(&plan.shuffle, 0);
    let shuf_hi = load_u8x16(&plan.shuffle, 16);
    let shift_lo = load_i32(&plan.shift, 0);
    let shift_hi = load_i32(&plan.shift, 1);
    let mask = dup_n_u32((1u32 << bits) - 1);

    // A group reads a whole 16 bytes from its start, so the last few groups would read past the
    // end of a buffer that is only `32 * bits` long. Exactly `⌊15 / bits⌋` of them do — the ones
    // starting within 15 bytes of the end — so copy that short remainder (at most 15 bytes) into
    // a zero-padded scratch buffer and read those groups from there. Everything stays
    // vectorized, and the copy is a few bytes rather than the whole buffer.
    let tail_groups = 15 / bits;
    let head_groups = GROUPS - tail_groups;
    let tail_start = head_groups * bits;
    let mut tail = [0u8; 32];
    tail[..bytes.len() - tail_start].copy_from_slice(&bytes[tail_start..]);

    let mut out = [0u16; RING_DEG];
    for group in 0..GROUPS {
        // For a group in the head, `group * bits + 16 ≤ 32 * bits = bytes.len()`, so the load is
        // in bounds. For one in the tail, its offset into `tail` is at most
        // `31 * bits - tail_start = (⌊15/bits⌋ - 1) * bits ≤ 15 - bits`, so the 16-byte load
        // stays inside the 32-byte scratch buffer.
        let raw = if group < head_groups {
            load_u8x16(bytes, group * bits)
        } else {
            load_u8x16(&tail, group * bits - tail_start)
        };

        let win_lo = tbl1_u8(raw, shuf_lo);
        let win_hi = tbl1_u8(raw, shuf_hi);
        let val_lo = and(ushl_u32(win_lo, shift_lo), mask);
        let val_hi = and(ushl_u32(win_hi, shift_hi), mask);

        // Every value is at most 13 bits, so narrowing to u16 is exact. The store covers
        // `out[8g .. 8g + 8]`, within `RING_DEG = 8 * GROUPS`.
        store_u16(&mut out, group, xtn_pair_32(val_lo, val_hi));
    }

    out
}
