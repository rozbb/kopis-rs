//! NEON negacyclic NTT over the auxiliary prime p = 50330113.
//!
//! This is a lane-parallel rewrite of [`crate::arithmetic::ntt`]. It computes *exactly* the
//! same integers: same prime, same ψ table, same signed Montgomery reduction (R = 2^32), same
//! Barrett re-centering at the same points. The `matches_serial` test checks that bit for bit,
//! which is the property the Lean correspondence proof needs in order to keep covering the
//! shipped code — the NEON backend is a different route to the same values, not a different
//! algorithm.
//!
//! # Layout
//!
//! 256 `i32` coefficients are 64 vectors of 4. The first six levels of the transform have
//! `len ≥ 4`, so a butterfly pairs two whole vectors and needs no shuffling at all. The last
//! two (`len` = 2, 1) live *inside* a vector. Unlike the AVX2 backend — whose 8-wide vectors
//! leave a three-level tail that it handles with an 8×8 transpose — NEON's in-vector span is
//! exactly one vector, so no transpose helps: instead the two innermost levels process a pair
//! of vectors with `zip`/`uzp` de-interleaving. `len = 2` splits each vector into its low and
//! high halves; `len = 1` splits into even and odd lanes. Both then become vertical butterflies
//! with a per-lane ψ vector read from a precomputed table.
//!
//! The inverse transform is the same picture run backwards: the two innermost Gentleman-Sande
//! levels first (`len` = 1 then 2), then six vertical levels.
//!
//! # Multiplication
//!
//! [`mont_mul`] uses NEON's widening `vmull_s32` / `vmull_high_s32`, which give the full 64-bit
//! products of two lanes at a time directly — so, unlike the AVX2 path, there is no even/odd
//! lane juggling. With `ζ' = ζ·p⁻¹ mod 2^32` precomputed, the reduction is
//! `hi(a·ζ) − hi((a·ζ' mod 2^32)·p)`; the two low halves are equal by construction, so the
//! high half of the 64-bit difference is the exact, already-centered answer.

use core::arch::aarch64::*;

use crate::arithmetic::ntt::{BARRETT_M, BARRETT_ROUND, INVNTT_SCALE, P, P_HALF, P_INV, ZETAS};
use crate::consts::RING_DEG;

/// A 16-byte-aligned constant table of `N` `i32`s
#[repr(align(16))]
struct Aligned<const N: usize>([i32; N]);

/// ζ·p⁻¹ mod 2^32, the multiplier that produces the Montgomery quotient in one step
const fn qinv(z: i32) -> i32 {
    (z as u32).wrapping_mul(P_INV) as i32
}

/// [`ZETAS`] pre-multiplied by p⁻¹, for the six whole-vector levels (which broadcast a scalar ψ)
const ZETAS_QINV: [i32; 256] = {
    let mut table = [0i32; 256];
    let mut k = 0;
    while k < 256 {
        table[k] = qinv(ZETAS[k]);
        k += 1;
    }
    table
};

// The two innermost levels each process a pair of vectors (`2g`, `2g+1`) at once, so each of the
// 32 groups needs a 4-lane ψ vector. These const fns lay those out, alongside the matching
// p⁻¹-scaled twins. The lane assignments are worked out in `ntt` / `invntt` below.

/// Forward `len = 2`: vector `2g+d` is one block with ψ = `ZETAS[64 + 2g + d]`, and the two
/// lanes the butterfly touches in it share that ψ; the group's four lanes are `[ψ0,ψ0,ψ1,ψ1]`.
const fn fwd2_tables() -> (Aligned<128>, Aligned<128>) {
    let mut z = [0i32; 128];
    let mut zq = [0i32; 128];
    let mut g = 0;
    while g < 32 {
        let lane = [
            ZETAS[64 + 2 * g],
            ZETAS[64 + 2 * g],
            ZETAS[64 + 2 * g + 1],
            ZETAS[64 + 2 * g + 1],
        ];
        let mut m = 0;
        while m < 4 {
            z[4 * g + m] = lane[m];
            zq[4 * g + m] = qinv(lane[m]);
            m += 1;
        }
        g += 1;
    }
    (Aligned(z), Aligned(zq))
}

/// Forward `len = 1`: the four blocks a group touches take the four consecutive ψ values
/// `ZETAS[128 + 4g .. 128 + 4g + 4]`.
const fn fwd1_tables() -> (Aligned<128>, Aligned<128>) {
    let mut z = [0i32; 128];
    let mut zq = [0i32; 128];
    let mut i = 0;
    while i < 128 {
        z[i] = ZETAS[128 + i];
        zq[i] = qinv(ZETAS[128 + i]);
        i += 1;
    }
    (Aligned(z), Aligned(zq))
}

/// Inverse `len = 1` (Gentleman-Sande, walking ψ downward from 255): group `g`'s four blocks
/// take `−ZETAS[255 − 4g .. 252 − 4g]`, one per lane.
const fn inv1_tables() -> (Aligned<128>, Aligned<128>) {
    let mut z = [0i32; 128];
    let mut zq = [0i32; 128];
    let mut g = 0;
    while g < 32 {
        let mut m = 0;
        while m < 4 {
            let value = -ZETAS[255 - 4 * g - m];
            z[4 * g + m] = value;
            zq[4 * g + m] = qinv(value);
            m += 1;
        }
        g += 1;
    }
    (Aligned(z), Aligned(zq))
}

/// Inverse `len = 2`: vector `2g+d` is one block with ψ = `−ZETAS[127 − 2g − d]`; lanes
/// `[ψ0,ψ0,ψ1,ψ1]`.
const fn inv2_tables() -> (Aligned<128>, Aligned<128>) {
    let mut z = [0i32; 128];
    let mut zq = [0i32; 128];
    let mut g = 0;
    while g < 32 {
        let lane = [
            -ZETAS[127 - 2 * g],
            -ZETAS[127 - 2 * g],
            -ZETAS[127 - 2 * g - 1],
            -ZETAS[127 - 2 * g - 1],
        ];
        let mut m = 0;
        while m < 4 {
            z[4 * g + m] = lane[m];
            zq[4 * g + m] = qinv(lane[m]);
            m += 1;
        }
        g += 1;
    }
    (Aligned(z), Aligned(zq))
}

const FWD2: (Aligned<128>, Aligned<128>) = fwd2_tables();
const FWD1: (Aligned<128>, Aligned<128>) = fwd1_tables();
const INV1: (Aligned<128>, Aligned<128>) = inv1_tables();
const INV2: (Aligned<128>, Aligned<128>) = inv2_tables();

/// Loads vector `i` (coefficients `4i..4i+4`) of a 256-coefficient array
///
/// # Safety
///
/// `ptr` must be valid for reads of at least `4 * (i + 1)` `i32`s.
#[inline]
#[target_feature(enable = "neon")]
unsafe fn ld(ptr: *const i32, i: usize) -> int32x4_t {
    // SAFETY: guaranteed by this function's contract. The load is unaligned.
    unsafe { vld1q_s32(ptr.add(4 * i)) }
}

/// Stores vector `i` (coefficients `4i..4i+4`) of a 256-coefficient array
///
/// # Safety
///
/// `ptr` must be valid for writes of at least `4 * (i + 1)` `i32`s.
#[inline]
#[target_feature(enable = "neon")]
unsafe fn st(ptr: *mut i32, i: usize, v: int32x4_t) {
    // SAFETY: guaranteed by this function's contract; the store is unaligned.
    unsafe { vst1q_s32(ptr.add(4 * i), v) }
}

/// Loads the 4-lane ψ vector at group `g` of a 128-entry table
///
/// # Safety
///
/// `4g + 4` must be within the table.
#[inline]
#[target_feature(enable = "neon")]
unsafe fn ld_table(table: &Aligned<128>, g: usize) -> int32x4_t {
    // SAFETY: guaranteed by this function's contract.
    unsafe { vld1q_s32(table.0.as_ptr().add(4 * g)) }
}

/// Signed Montgomery multiply: returns `a · z · 2⁻³² mod p`, centered, for each of the 4 lanes.
///
/// `z` holds ψ per lane and `zq` the matching `ψ·p⁻¹ mod 2^32`. `p` is `[p, p]` (the widening
/// multiplies work two lanes at a time).
#[inline]
#[target_feature(enable = "neon")]
fn mont_mul(a: int32x4_t, z: int32x4_t, zq: int32x4_t, p: int32x2_t) -> int32x4_t {
    let a_lo = vget_low_s32(a);

    // Full 64-bit products a·ψ, two lanes at a time.
    let az_lo = vmull_s32(a_lo, vget_low_s32(z));
    let az_hi = vmull_high_s32(a, z);

    // The Montgomery quotient t = (a·ψ·p⁻¹) mod 2^32 is the low dword of a·(ψ·p⁻¹); `vmovn`
    // takes exactly that. Multiplying it by p gives t·p, whose low dword equals a·ψ's.
    let t_lo = vmovn_s64(vmull_s32(a_lo, vget_low_s32(zq)));
    let t_hi = vmovn_s64(vmull_high_s32(a, zq));
    let tp_lo = vmull_s32(t_lo, p);
    let tp_hi = vmull_s32(t_hi, p);

    // Subtract while still 64-bit; the two low dwords are equal by construction, so the high
    // dword of the difference is the whole (already centered, `|·| < p`) answer. `vshrn` by 32
    // reads exactly that high dword.
    let r_lo = vshrn_n_s64::<32>(vsubq_s64(az_lo, tp_lo));
    let r_hi = vshrn_n_s64::<32>(vsubq_s64(az_hi, tp_hi));
    vcombine_s32(r_lo, r_hi)
}

/// Centered Barrett reduction of 4 lanes: `r ≡ x (mod p)` with `|r| ≤ p/2 + 1`
#[inline]
#[target_feature(enable = "neon")]
fn barrett(x: int32x4_t, p: int32x4_t) -> int32x4_t {
    let m = vdup_n_s32(BARRETT_M as i32);
    let round = vdupq_n_s64(BARRETT_ROUND);

    // q = (x·M + 2^47) >> 48, arithmetic, narrowed to i32. NEON's narrowing shift caps at 32,
    // so shift the 64-bit product then narrow separately.
    let prod_lo = vaddq_s64(vmull_s32(vget_low_s32(x), m), round);
    let prod_hi = vaddq_s64(vmull_high_s32(x, vcombine_s32(m, m)), round);
    let q_lo = vmovn_s64(vshrq_n_s64::<48>(prod_lo));
    let q_hi = vmovn_s64(vshrq_n_s64::<48>(prod_hi));
    let q = vcombine_s32(q_lo, q_hi);

    vmlsq_s32(x, q, p)
}

/// One Cooley-Tukey butterfly pair: `(lo, hi) ← (lo + ψ·hi, lo − ψ·hi)`
#[inline]
#[target_feature(enable = "neon")]
fn ct_butterfly(
    lo: int32x4_t,
    hi: int32x4_t,
    z: int32x4_t,
    zq: int32x4_t,
    p: int32x2_t,
) -> (int32x4_t, int32x4_t) {
    let t = mont_mul(hi, z, zq, p);
    (vaddq_s32(lo, t), vsubq_s32(lo, t))
}

/// One Gentleman-Sande butterfly pair: `(lo, hi) ← (lo + hi, −ψ·(lo − hi))`
#[inline]
#[target_feature(enable = "neon")]
fn gs_butterfly(
    lo: int32x4_t,
    hi: int32x4_t,
    z: int32x4_t,
    zq: int32x4_t,
    p: int32x2_t,
) -> (int32x4_t, int32x4_t) {
    let diff = vsubq_s32(lo, hi);
    (vaddq_s32(lo, hi), mont_mul(diff, z, zq, p))
}

/// In-place forward negacyclic NTT, then Barrett centering — the vector twin of
/// [`crate::arithmetic::ntt`]'s `ntt`, producing identical output for identical input.
///
/// # Safety
///
/// Requires NEON. Input coefficients must satisfy `|a[i]| < 2^13`, as in the serial version.
#[target_feature(enable = "neon")]
pub(crate) fn ntt(a: &mut [i32; RING_DEG]) {
    let p = vdup_n_s32(P);
    let ptr = a.as_mut_ptr();

    // Levels with len ≥ 4: both halves of every butterfly are whole vectors, and ψ is constant
    // across a block, so it is simply broadcast. `half` is the block half-width in vectors.
    let mut k = 0usize;
    let mut half = 32usize;
    while half >= 1 {
        let mut start = 0usize;
        while start < 64 {
            k += 1;
            let z = vdupq_n_s32(ZETAS[k]);
            let zq = vdupq_n_s32(ZETAS_QINV[k]);
            let mut i = start;
            while i < start + half {
                // SAFETY: `i + half < 64` because `start + 2*half ≤ 64`, so both loads and
                // stores stay inside the 256-coefficient array.
                unsafe {
                    let (lo, hi) = ct_butterfly(ld(ptr, i), ld(ptr, i + half), z, zq, p);
                    st(ptr, i, lo);
                    st(ptr, i + half, hi);
                }
                i += 1;
            }
            start += 2 * half;
        }
        half /= 2;
    }

    // Levels with len < 4: process vectors (2g, 2g+1) together, len = 2 then len = 1.
    for g in 0..32 {
        // SAFETY: `2g + 1 < 64`, so both loads and stores below are in range.
        unsafe {
            let mut va = ld(ptr, 2 * g);
            let mut vb = ld(ptr, 2 * g + 1);

            // len = 2: pair each vector's low half with its high half. lo/hi gather the two
            // vectors' halves so all four lanes stay busy.
            let z = ld_table(&FWD2.0, g);
            let zq = ld_table(&FWD2.1, g);
            let lo = vcombine_s32(vget_low_s32(va), vget_low_s32(vb));
            let hi = vcombine_s32(vget_high_s32(va), vget_high_s32(vb));
            let (lo, hi) = ct_butterfly(lo, hi, z, zq, p);
            va = vcombine_s32(vget_low_s32(lo), vget_low_s32(hi));
            vb = vcombine_s32(vget_high_s32(lo), vget_high_s32(hi));

            // len = 1: pair even lanes with odd lanes.
            let z = ld_table(&FWD1.0, g);
            let zq = ld_table(&FWD1.1, g);
            let evens = vuzp1q_s32(va, vb);
            let odds = vuzp2q_s32(va, vb);
            let (lo, hi) = ct_butterfly(evens, odds, z, zq, p);
            va = vzip1q_s32(lo, hi);
            vb = vzip2q_s32(lo, hi);

            st(ptr, 2 * g, va);
            st(ptr, 2 * g + 1, vb);
        }
    }

    let p4 = vdupq_n_s32(P);
    for i in 0..64 {
        // SAFETY: `i < 64` indexes within the 256-coefficient array.
        unsafe { st(ptr, i, barrett(ld(ptr, i), p4)) };
    }
}

/// In-place inverse negacyclic NTT — the vector twin of [`crate::arithmetic::ntt`]'s `invntt`,
/// including its mid-transform Barrett pass and final scaling.
///
/// # Safety
///
/// Requires NEON. Input coefficients must satisfy `|a[i]| < p`, as in the serial version.
#[target_feature(enable = "neon")]
fn invntt(a: &mut [i32; RING_DEG]) {
    let p = vdup_n_s32(P);
    let ptr = a.as_mut_ptr();

    // Levels with len < 4, in reverse: len = 1 then len = 2, per vector pair (2g, 2g+1).
    for g in 0..32 {
        // SAFETY: `2g + 1 < 64`.
        unsafe {
            let mut va = ld(ptr, 2 * g);
            let mut vb = ld(ptr, 2 * g + 1);

            // len = 1: even/odd lanes.
            let z = ld_table(&INV1.0, g);
            let zq = ld_table(&INV1.1, g);
            let evens = vuzp1q_s32(va, vb);
            let odds = vuzp2q_s32(va, vb);
            let (lo, hi) = gs_butterfly(evens, odds, z, zq, p);
            va = vzip1q_s32(lo, hi);
            vb = vzip2q_s32(lo, hi);

            // len = 2: low/high halves.
            let z = ld_table(&INV2.0, g);
            let zq = ld_table(&INV2.1, g);
            let lo = vcombine_s32(vget_low_s32(va), vget_low_s32(vb));
            let hi = vcombine_s32(vget_high_s32(va), vget_high_s32(vb));
            let (lo, hi) = gs_butterfly(lo, hi, z, zq, p);
            va = vcombine_s32(vget_low_s32(lo), vget_low_s32(hi));
            vb = vcombine_s32(vget_high_s32(lo), vget_high_s32(hi));

            st(ptr, 2 * g, va);
            st(ptr, 2 * g + 1, vb);
        }
    }

    // Levels with len ≥ 4. `k` continues downward from where the in-vector levels stopped:
    // they consumed 128 + 64 = 192 of the 256 ψ entries, leaving k at 64.
    let p4 = vdupq_n_s32(P);
    let mut k = 64usize;
    let mut half = 1usize;
    while half < 64 {
        let mut start = 0usize;
        while start < 64 {
            k -= 1;
            let z = vdupq_n_s32(-ZETAS[k]);
            let zq = vdupq_n_s32(qinv(-ZETAS[k]));
            let mut i = start;
            while i < start + half {
                // SAFETY: `i + half < 64` because `start + 2*half ≤ 64`.
                unsafe {
                    let (lo, hi) = gs_butterfly(ld(ptr, i), ld(ptr, i + half), z, zq, p);
                    st(ptr, i, lo);
                    st(ptr, i + half, hi);
                }
                i += 1;
            }
            start += 2 * half;
        }
        half *= 2;

        // After the len = 8 level (half now 4), re-center so the un-reduced sum path cannot
        // outgrow an i32 over the remaining levels. Matches the serial `len == 16` check.
        if half == 4 {
            for i in 0..64 {
                // SAFETY: `i < 64`.
                unsafe { st(ptr, i, barrett(ld(ptr, i), p4)) };
            }
        }
    }

    // One final Montgomery multiply undoes both the 1/256 and the Montgomery factor.
    let scale = vdupq_n_s32(INVNTT_SCALE);
    let scale_q = vdupq_n_s32(qinv(INVNTT_SCALE));
    for i in 0..64 {
        // SAFETY: `i < 64`.
        unsafe { st(ptr, i, mont_mul(ld(ptr, i), scale, scale_q, p)) };
    }
}

/// Widens 4 `u16`s at `src[4i..]` to `i32`, zero-extending (uniform coefficients)
///
/// # Safety
///
/// `src` must be valid for reads of at least `4 * (i + 1)` `u16`s.
#[inline]
#[target_feature(enable = "neon")]
unsafe fn widen_u16(src: *const u16, i: usize) -> int32x4_t {
    // SAFETY: guaranteed by this function's contract.
    unsafe { vreinterpretq_s32_u32(vmovl_u16(vld1_u16(src.add(4 * i)))) }
}

/// Widens 4 `u16`s at `src[4i..]` to `i32`, sign-extending (CBD secret coefficients, which are
/// wrapping-`u16` encodings of small signed values)
///
/// # Safety
///
/// `src` must be valid for reads of at least `4 * (i + 1)` `u16`s.
#[inline]
#[target_feature(enable = "neon")]
unsafe fn widen_i16(src: *const u16, i: usize) -> int32x4_t {
    // SAFETY: guaranteed by this function's contract.
    unsafe { vmovl_s16(vreinterpret_s16_u16(vld1_u16(src.add(4 * i)))) }
}

/// Forward-transforms a ring element with plain coefficients in `[0, 2^13)`
///
/// # Safety
///
/// Requires NEON.
#[target_feature(enable = "neon")]
pub(crate) fn from_uniform(elem: &[u16; RING_DEG]) -> [i32; RING_DEG] {
    let mut a = [0i32; RING_DEG];
    for i in 0..64 {
        // SAFETY: `i < 64` is in range for both the 256-`u16` source and the 256-`i32` output.
        unsafe { st(a.as_mut_ptr(), i, widen_u16(elem.as_ptr(), i)) };
    }
    ntt(&mut a);
    a
}

/// Forward-transforms a CBD secret, reading each coefficient as the signed value it encodes
///
/// # Safety
///
/// Requires NEON.
#[target_feature(enable = "neon")]
pub(crate) fn from_secret(elem: &[u16; RING_DEG]) -> [i32; RING_DEG] {
    let mut a = [0i32; RING_DEG];
    for i in 0..64 {
        // SAFETY: `i < 64` is in range for both the 256-`u16` source and the 256-`i32` output.
        unsafe { st(a.as_mut_ptr(), i, widen_i16(elem.as_ptr(), i)) };
    }
    ntt(&mut a);
    a
}

/// Adds the pointwise product `lhs ∘ rhs` into an unreduced `i64` accumulator
///
/// # Safety
///
/// Requires NEON.
#[target_feature(enable = "neon")]
pub(crate) fn pointwise_mul_acc(
    acc: &mut [i64; RING_DEG],
    lhs: &[i32; RING_DEG],
    rhs: &[i32; RING_DEG],
) {
    let acc_ptr = acc.as_mut_ptr();
    for i in 0..64 {
        // SAFETY: `i < 64` indexes 4 coefficients of each 256-element operand; the accumulator
        // slots for those coefficients are the two 2-wide vectors at `4i` and `4i + 2`.
        unsafe {
            let l = ld(lhs.as_ptr(), i);
            let r = ld(rhs.as_ptr(), i);
            let lo = vmull_s32(vget_low_s32(l), vget_low_s32(r)); // coeffs 4i, 4i+1
            let hi = vmull_high_s32(l, r); // coeffs 4i+2, 4i+3

            let a0 = acc_ptr.add(4 * i);
            let a1 = acc_ptr.add(4 * i + 2);
            vst1q_s64(a0, vaddq_s64(vld1q_s64(a0), lo));
            vst1q_s64(a1, vaddq_s64(vld1q_s64(a1), hi));
        }
    }
}

/// Montgomery-reduces the accumulator, inverse-transforms it, and packs the result back into
/// wrapping-`u16` coefficients
///
/// # Safety
///
/// Requires NEON.
#[target_feature(enable = "neon")]
pub(crate) fn reduce_invntt(acc: &[i64; RING_DEG]) -> [u16; RING_DEG] {
    let p = vdup_n_s32(P);
    let p_inv = vdup_n_s32(P_INV as i32);

    let mut v = [0i32; RING_DEG];
    for i in 0..64 {
        // SAFETY: `i < 64`, so the two 2-wide accumulator vectors at `4i` and `4i + 2` and the
        // 4-wide output vector `i` are all in range.
        unsafe {
            let a0 = vld1q_s64(acc.as_ptr().add(4 * i));
            let a1 = vld1q_s64(acc.as_ptr().add(4 * i + 2));
            // Montgomery reduction of an i64: t = (a mod 2^32)·p⁻¹, then (a − t·p) >> 32. As in
            // `mont_mul`, the low dwords cancel, so the high dword is the whole answer.
            let t0 = vmul_s32(vmovn_s64(a0), p_inv);
            let t1 = vmul_s32(vmovn_s64(a1), p_inv);
            let d0 = vsubq_s64(a0, vmull_s32(t0, p));
            let d1 = vsubq_s64(a1, vmull_s32(t1, p));
            let r = vcombine_s32(vshrn_n_s64::<32>(d0), vshrn_n_s64::<32>(d1));
            st(v.as_mut_ptr(), i, r);
        }
    }

    invntt(&mut v);

    // Lift each coefficient to its centered representative and truncate to 16 bits.
    let p4 = vdupq_n_s32(P);
    let p_half = vdupq_n_s32(P_HALF);
    let mut out = [0u16; RING_DEG];
    for i in 0..64 {
        // SAFETY: `i < 64` reads one coefficient vector; the packed result is the 4 `u16`s at
        // `out[4i..4i + 4]`.
        unsafe {
            let x = ld(v.as_ptr(), i);
            // to_canonical: add p where negative, giving [0, p)
            let x = vaddq_s32(x, vandq_s32(vshrq_n_s32::<31>(x), p4));
            // then subtract p above ⌊p/2⌋, giving (-p/2, p/2]
            let over = vshrq_n_s32::<31>(vsubq_s32(p_half, x));
            let x = vsubq_s32(x, vandq_s32(p4, over));
            // Truncate to 16 bits, exactly matching `x as u16`.
            let packed = vmovn_u32(vreinterpretq_u32_s32(x));
            vst1_u16(out.as_mut_ptr().add(4 * i), packed);
        }
    }
    out
}
