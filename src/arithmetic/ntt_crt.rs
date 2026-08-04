//! Portable negacyclic NTT over *two* 16-bit primes, combined by the CRT.
//!
//! This computes exactly the same ring products as [`crate::arithmetic::ntt`]'s single-prime
//! transform — the same `[u16; 256]` come out — but over q₁ = 7681 and q₂ = 10753 instead of
//! the 26-bit prime p, reconstructing the exact integer product from the two residues. It is
//! the same scheme the vector backends use; [`crate::backend::crt`] holds the moduli, the ψ
//! tables and the correctness argument, and this module is a plain-Rust transcription of it.
//!
//! # Why the portable path uses two primes
//!
//! [`crate::backend::crt`] introduces the two-prime trade as one made for vector units, on the
//! grounds that "on a scalar core a 32×32→64 multiply costs the same as a 16×16→32 one, so
//! doubling the transforms just doubles the work". That reasoning is sound for a *scalar* core.
//! It does not apply here, because the portable code is not scalar on any target this crate is
//! built for: LLVM auto-vectorizes the butterfly loops, and what it can vectorize them *into*
//! is the whole difference.
//!
//! The single-prime butterfly needs a 64-bit product, and baseline SSE2 has no 64-bit multiply,
//! so LLVM emits an emulation — sign-extension shuffles, four `pmuludq`, and `psllq`/`paddq`
//! recombination, about 35 instructions for four butterflies. The 16-bit butterfly needs only
//! `pmullw` and `pmulhw`, each one instruction over eight lanes, so eight butterflies cost about
//! ten. Two transforms at that density comfortably beat one at the other — the opposite of the
//! scalar conclusion.
//!
//! Measured on a 12th-gen Core i9 at baseline x86-64 (so SSE2), against the single-prime code
//! compiled the same way: the forward transform is 1.68× faster counting *both* primes, the
//! Montgomery-reduce/inverse-transform/recombine pipeline 2.40× faster, and the pointwise
//! multiply-accumulate 1.53× faster. End to end that is 20–45% off every KEM operation; see the
//! benchmark note in the README.
//!
//! So the axis is not portable-versus-vector but scalar-versus-auto-vectorized, and every target
//! this crate builds for falls on the auto-vectorized side. A genuinely scalar target — a
//! Cortex-M-class core with no SIMD and no auto-vectorization to speak of — would want the
//! single prime back; [`crate::arithmetic::ntt`] keeps that transform as a test-only reference
//! and would be the place to start.
//!
//! # Layout
//!
//! An [`NttElem`](crate::arithmetic::NttElem) is `[i16; 512]`: the q₁ residues in the first 256
//! lanes, the q₂ residues in the second. The pointwise accumulator is `[i32; 512]`, split the
//! same way. Those are the same sizes the single-prime form used (`[i32; 256]` and
//! `[i64; 256]`), they are what the vector backends read too, and neither is ever serialized, so
//! the representation never escapes the process that computed it.
//!
//! # Growth
//!
//! The reduction schedule is the NEON one from [`crate::backend::crt`], which its crude
//! per-level budget covers without needing the interval-propagation argument the AVX2 schedule
//! rests on: forward, Barrett after levels 3 and 6 plus a final pass (runs of 3, 3, 2); inverse,
//! Barrett after levels 2, 4 and 6.

// Explicit `for i in 0..N` index loops, as in the rest of the arithmetic: they are what the
// Lean extractor handles best, and here they are also what vectorizes most predictably.
#![allow(clippy::needless_range_loop)]

use crate::{
    backend::crt::{self, BARRETT_SH, CRT_Q, CRT_Q_HALF, CRT_Q1_INV_MONT, Q1, Q2, Q2_INV},
    consts::RING_DEG,
};

/// One residue block: 256 coefficients modulo one of the two primes
type Block = [i16; RING_DEG];

/// Signed Montgomery multiply: `a · z · 2⁻¹⁶ mod q`, centered.
///
/// `zq` is `z·q⁻¹ mod 2^16`, so `t = a·zq` is the Montgomery quotient outright. `t·q` and `a·z`
/// agree in their low 16 bits by construction, so their difference has a zero low half and the
/// high halves alone give the exact quotient, with no borrow to account for. Requires
/// `|a·z| < 2^15·q`, which the growth bounds in the module docs give at every call site.
///
/// Both products are written as `i32` multiplies whose high half is taken, which is the shape
/// LLVM turns into a single 16-lane high-multiply (`pmulhw` / `sqdmulh`).
#[inline(always)]
fn mont_mul(a: i16, z: i16, zq: i16, q: i16) -> i16 {
    let t = a.wrapping_mul(zq);
    let hi = ((a as i32).wrapping_mul(z as i32) >> 16) as i16;
    let th = ((t as i32).wrapping_mul(q as i32) >> 16) as i16;
    hi.wrapping_sub(th)
}

/// Centered Barrett reduction: `r ≡ x (mod q)` with `|r| ≤ q/2`, for any `i16` input.
///
/// `t ≈ round(x/q)` is `(hi(x·M) + 2^(SH-1)) >> SH`; the rounding addend is what makes the
/// result centered rather than merely bounded by q. It cannot overflow the lane:
/// `hi(x·M) ≤ 2^15·M/2^16 < 2^14` and the addend is 2^10.
#[inline(always)]
fn barrett(x: i16, m: i16, q: i16) -> i16 {
    let t = ((x as i32).wrapping_mul(m as i32) >> 16) as i16;
    let t = t.wrapping_add(1 << (BARRETT_SH - 1)) >> BARRETT_SH;
    x.wrapping_sub(t.wrapping_mul(q))
}

#[inline(always)]
fn barrett_block<const SECOND: bool>(b: &mut Block) {
    let q = crt::q::<SECOND>();
    let m = crt::barrett_m::<SECOND>();
    for i in 0..RING_DEG {
        b[i] = barrett(b[i], m, q);
    }
}

/// One Cooley-Tukey level: `(lo, hi) ← (lo + ψ·hi, lo − ψ·hi)` over every butterfly pair.
///
/// `LEN` is a const generic rather than a variable so that each level's inner loop has a
/// compile-time trip count. That is what lets LLVM vectorize it cleanly; with a runtime `len`
/// it emits a generic loop with a `cmov` bounds prologue that is several times slower.
#[inline(always)]
fn ct_level<const LEN: usize, const SECOND: bool>(b: &mut Block, k: &mut usize) {
    let q = crt::q::<SECOND>();
    let mut start = 0usize;
    while start < RING_DEG {
        *k += 1;
        let z = crt::zeta::<SECOND>(*k);
        let zq = crt::zeta_q::<SECOND>(*k);
        for j in start..start + LEN {
            let t = mont_mul(b[j + LEN], z, zq, q);
            b[j + LEN] = b[j].wrapping_sub(t);
            b[j] = b[j].wrapping_add(t);
        }
        start += 2 * LEN;
    }
}

/// One Gentleman-Sande level: `(lo, hi) ← (lo + hi, −ψ·(lo − hi))`
#[inline(always)]
fn gs_level<const LEN: usize, const SECOND: bool>(b: &mut Block, k: &mut usize) {
    let q = crt::q::<SECOND>();
    let qinv = crt::qinv::<SECOND>();
    let mut start = 0usize;
    while start < RING_DEG {
        *k -= 1;
        // The negation the Gentleman-Sande butterfly wants, taken here rather than baked into
        // a second table; it folds into the loop-invariant broadcast either way.
        let z = crt::zeta::<SECOND>(*k).wrapping_neg();
        let zq = z.wrapping_mul(qinv);
        for j in start..start + LEN {
            let lo = b[j];
            let hi = b[j + LEN];
            b[j] = lo.wrapping_add(hi);
            b[j + LEN] = mont_mul(lo.wrapping_sub(hi), z, zq, q);
        }
        start += 2 * LEN;
    }
}

/// Forward transform of one residue block. Inputs must be centered, `|a| ≤ q/2`.
fn ntt_block<const SECOND: bool>(b: &mut Block) {
    let mut k = 0usize;
    ct_level::<128, SECOND>(b, &mut k);
    ct_level::<64, SECOND>(b, &mut k);
    ct_level::<32, SECOND>(b, &mut k);
    // Three levels of Cooley-Tukey growth reach 2.75q; re-center before a fourth.
    barrett_block::<SECOND>(b);
    ct_level::<16, SECOND>(b, &mut k);
    ct_level::<8, SECOND>(b, &mut k);
    ct_level::<4, SECOND>(b, &mut k);
    barrett_block::<SECOND>(b);
    ct_level::<2, SECOND>(b, &mut k);
    ct_level::<1, SECOND>(b, &mut k);
    // Leaves the output centered, which is what the pointwise step's product bound assumes.
    barrett_block::<SECOND>(b);
}

/// Inverse transform of one residue block, including the final `256⁻¹·2³²` scaling.
fn invntt_block<const SECOND: bool>(b: &mut Block) {
    let q = crt::q::<SECOND>();
    let scale = crt::invntt_scale::<SECOND>();
    let scale_q = scale.wrapping_mul(crt::qinv::<SECOND>());

    let mut k = RING_DEG;
    gs_level::<1, SECOND>(b, &mut k);
    gs_level::<2, SECOND>(b, &mut k);
    // The Gentleman-Sande sum path doubles per level; re-center every two levels so that both
    // `lo + hi` and `lo - hi` stay inside the lane.
    barrett_block::<SECOND>(b);
    gs_level::<4, SECOND>(b, &mut k);
    gs_level::<8, SECOND>(b, &mut k);
    barrett_block::<SECOND>(b);
    gs_level::<16, SECOND>(b, &mut k);
    gs_level::<32, SECOND>(b, &mut k);
    barrett_block::<SECOND>(b);
    gs_level::<64, SECOND>(b, &mut k);
    gs_level::<128, SECOND>(b, &mut k);
    // The last two levels end at 2.0q, which this scaling brings back under q.
    for i in 0..RING_DEG {
        b[i] = mont_mul(b[i], scale, scale_q, q);
    }
}

/// Splits a ring element into one residue block and transforms it.
///
/// `REDUCE` says whether the input needs reducing at all: uniform coefficients go up to 2^13,
/// which exceeds q₁, whereas CBD secrets satisfy |·| ≤ μ/2 ≤ 5 and are already centered
/// residues for both primes. Coefficients below 2^13 fit an `i16`, so the Barrett reduction is
/// in range; for secrets the `i16` reading of the `u16` is exactly the signed value it encodes.
#[inline(always)]
fn split_and_transform<const SECOND: bool, const REDUCE: bool>(
    elem: &[u16; RING_DEG],
    b: &mut Block,
) {
    let q = crt::q::<SECOND>();
    let m = crt::barrett_m::<SECOND>();
    for i in 0..RING_DEG {
        let x = elem[i] as i16;
        b[i] = if REDUCE { barrett(x, m, q) } else { x };
    }
    ntt_block::<SECOND>(b);
}

/// Splits a ring element into both residue blocks and transforms each
#[inline(always)]
fn from_ring_elem<const REDUCE: bool>(elem: &[u16; RING_DEG]) -> [i16; 2 * RING_DEG] {
    let mut out = [0i16; 2 * RING_DEG];
    let mut b = [0i16; RING_DEG];

    split_and_transform::<false, REDUCE>(elem, &mut b);
    out[..RING_DEG].copy_from_slice(&b);

    split_and_transform::<true, REDUCE>(elem, &mut b);
    out[RING_DEG..].copy_from_slice(&b);

    out
}

/// Forward-transforms a ring element with plain coefficients in `[0, 2^13)`
pub(crate) fn from_uniform(elem: &[u16; RING_DEG]) -> [i16; 2 * RING_DEG] {
    from_ring_elem::<true>(elem)
}

/// Forward-transforms a CBD secret, reading each coefficient as the signed value it encodes
pub(crate) fn from_secret(elem: &[u16; RING_DEG]) -> [i16; 2 * RING_DEG] {
    from_ring_elem::<false>(elem)
}

/// Adds the pointwise product `lhs ∘ rhs` into an unreduced accumulator, per prime.
///
/// Products of centered values are below (q/2 + 1)² and callers accumulate at most 4 (= `MAX_L`)
/// of them, so each lane stays under 1.2·10⁸ — well inside an `i32`, and inside the 2^15·q input
/// range of the Montgomery reduction that consumes it.
pub(crate) fn pointwise_mul_acc(
    acc: &mut [i32; 2 * RING_DEG],
    lhs: &[i16; 2 * RING_DEG],
    rhs: &[i16; 2 * RING_DEG],
) {
    for i in 0..2 * RING_DEG {
        acc[i] = acc[i].wrapping_add((lhs[i] as i32).wrapping_mul(rhs[i] as i32));
    }
}

/// Signed Montgomery reduction of one accumulator block into `i16` residues, with R = 2^16.
///
/// As in [`mont_mul`], the low halves cancel by construction, so subtracting the high halves is
/// the whole answer.
#[inline(always)]
fn reduce_block<const SECOND: bool>(acc: &[i32], b: &mut Block) {
    let q = crt::q::<SECOND>();
    let qinv = crt::qinv::<SECOND>();
    for i in 0..RING_DEG {
        let a = acc[i];
        let t = (a as i16).wrapping_mul(qinv);
        let th = ((t as i32).wrapping_mul(q as i32) >> 16) as i16;
        b[i] = ((a >> 16) as i16).wrapping_sub(th);
    }
}

/// Montgomery-reduces the accumulator, inverse-transforms both residue blocks, reconstructs the
/// exact integer product by the CRT and packs it into wrapping-`u16` coefficients.
pub(crate) fn reduce_invntt(acc: &[i32; 2 * RING_DEG]) -> [u16; RING_DEG] {
    let mut v1 = [0i16; RING_DEG];
    let mut v2 = [0i16; RING_DEG];

    reduce_block::<false>(&acc[..RING_DEG], &mut v1);
    reduce_block::<true>(&acc[RING_DEG..], &mut v2);
    invntt_block::<false>(&mut v1);
    invntt_block::<true>(&mut v2);

    // CRT reconstruction, by Garner: with a₁ = r₁ mod q₁ and a₂ = r₂ mod q₂ taken in [0, q),
    // the unique x ≡ rᵢ (mod qᵢ) in [0, q₁q₂) is a₁ + q₁·((a₂ − a₁)·q₁⁻¹ mod q₂). Subtracting
    // q₁q₂ above the midpoint centers it; truncating to 16 bits then gives the wrapping-`u16`
    // coefficient, exactly as `to_wrapping_u16` does for the single prime. This is exact because
    // the true product lies in (−q₁q₂/2, q₁q₂/2] — the bound in [`crate::arithmetic::ntt`].
    let q1_inv_mont_q = CRT_Q1_INV_MONT.wrapping_mul(Q2_INV);
    let mut out = [0u16; RING_DEG];
    for i in 0..RING_DEG {
        let r1 = v1[i];
        let r2 = v2[i];
        // Canonicalize both residues to [0, q) by adding q where negative, branch-free.
        let a1 = r1.wrapping_add((r1 >> 15) & Q1);
        let a2 = r2.wrapping_add((r2 >> 15) & Q2);

        let t = mont_mul(a2.wrapping_sub(a1), CRT_Q1_INV_MONT, q1_inv_mont_q, Q2);
        let t = t.wrapping_add((t >> 15) & Q2);

        // a₁ + q₁·t needs 32 bits. Both operands are non-negative and below their prime, so the
        // widening is a zero extension.
        let x = (a1 as i32).wrapping_add((t as i32).wrapping_mul(Q1 as i32));
        // Branch-free `if x > CRT_Q_HALF { x - CRT_Q } else { x }`.
        let over = (CRT_Q_HALF.wrapping_sub(x)) >> 31;
        out[i] = x.wrapping_sub(CRT_Q & over) as u16;
    }
    out
}
