//! AVX2 negacyclic NTT over the auxiliary prime p = 50330113.
//!
//! This is a lane-parallel rewrite of [`crate::arithmetic::ntt`]. It computes *exactly* the
//! same integers: same prime, same ψ table, same signed Montgomery reduction (R = 2^32), same
//! Barrett re-centering at the same points. The `matches_serial` test checks that bit for bit,
//! which is the property the Lean correspondence proof needs in order to keep covering the
//! shipped code — the AVX2 backend is a different route to the same values, not a different
//! algorithm.
//!
//! # Layout
//!
//! 256 `i32` coefficients are 32 vectors of 8. The first five levels of the transform have
//! `len ≥ 8`, so a butterfly pairs two whole vectors and needs no shuffling at all. The last
//! three (`len` = 4, 2, 1) live *inside* a vector. Rather than shuffle per level, we transpose
//! each group of 8 vectors as an 8×8 matrix: lane `m` of the transposed vectors then holds one
//! whole 8-coefficient block, so all three remaining levels become vertical butterflies too,
//! with a per-lane ψ vector read from a precomputed table. Then we transpose back.
//!
//! The inverse transform is the same picture run backwards: the three innermost
//! Gentleman-Sande levels first (in transposed form), transpose back, then five vertical
//! levels.
//!
//! # Multiplication
//!
//! AVX2 has no 32×32→high-32 multiply, so [`mont_mul`] follows the standard Dilithium trick:
//! `vpmuldq` gives full 64-bit products of the even lanes, and a `vpshufd` of the input gives
//! the odd ones. With `ζ' = ζ·p⁻¹ mod 2^32` precomputed, the reduction is
//! `hi(a·ζ) − hi((a·ζ' mod 2^32)·p)`; the two low halves are equal by construction, so the
//! 32-bit difference of the high halves is the exact 64-bit difference shifted down — no
//! borrow to worry about.

#[cfg(target_arch = "x86")]
use core::arch::x86::*;
#[cfg(target_arch = "x86_64")]
use core::arch::x86_64::*;

use crate::arithmetic::ntt::{BARRETT_M, BARRETT_ROUND, INVNTT_SCALE, P, P_HALF, P_INV, ZETAS};
use crate::consts::RING_DEG;

/// A 32-byte-aligned constant table of `N` `i32`s
#[repr(align(32))]
struct Aligned<const N: usize>([i32; N]);

/// ζ·p⁻¹ mod 2^32, the multiplier that produces the Montgomery quotient in one step
const fn qinv(z: i32) -> i32 {
    (z as u32).wrapping_mul(P_INV) as i32
}

/// [`ZETAS`] pre-multiplied by p⁻¹, for the five whole-vector levels (which broadcast a
/// scalar ψ and so need no permuted table)
const ZETAS_QINV: [i32; 256] = {
    let mut table = [0i32; 256];
    let mut k = 0;
    while k < 256 {
        table[k] = qinv(ZETAS[k]);
        k += 1;
    }
    table
};

/// Builds one of the per-lane ψ tables for the transposed levels.
///
/// Entry `(g * 8 + m)` is `ZETAS[base + g_hi·q_stride + g_lo·h_stride + m·m_stride]`, where
/// `g = g_hi * h_count + g_lo` splits the group index into "which group of 8 vectors" and
/// "which butterfly pair within the level". `neg` produces the negated ψ the inverse
/// transform's Gentleman-Sande butterfly wants. Returns the table and its p⁻¹-scaled twin.
const fn lane_table<const N: usize>(
    base: isize,
    q_stride: isize,
    h_stride: isize,
    m_stride: isize,
    h_count: usize,
    neg: bool,
) -> (Aligned<N>, Aligned<N>) {
    let mut z = [0i32; N];
    let mut zq = [0i32; N];
    let mut g = 0;
    while g * 8 < N {
        let g_hi = (g / h_count) as isize;
        let g_lo = (g % h_count) as isize;
        let mut m = 0;
        while m < 8 {
            let idx = base + g_hi * q_stride + g_lo * h_stride + (m as isize) * m_stride;
            let value = ZETAS[idx as usize];
            let value = if neg { -value } else { value };
            z[g * 8 + m] = value;
            zq[g * 8 + m] = qinv(value);
            m += 1;
        }
        g += 1;
    }
    (Aligned(z), Aligned(zq))
}

// Forward transform, transposed levels. Group `q` covers vectors 8q..8q+8, i.e. coefficients
// 64q..64q+64, so lane `m` of the transposed group is coefficient block `8q + m`.
//
//  * level len=4: one block of 8 per lane, ψ index 32 + (8q + m)
//  * level len=2: two blocks of 4 per lane, ψ index 64 + 2(8q + m) + h, h ∈ {0,1}
//  * level len=1: four blocks of 2 per lane, ψ index 128 + 4(8q + m) + r, r ∈ {0..3}
const FWD4: (Aligned<32>, Aligned<32>) = lane_table(32, 8, 0, 1, 1, false);
const FWD2: (Aligned<64>, Aligned<64>) = lane_table(64, 16, 1, 2, 2, false);
const FWD1: (Aligned<128>, Aligned<128>) = lane_table(128, 32, 1, 4, 4, false);

// Inverse transform, transposed levels. The Gentleman-Sande pass walks the ψ table downwards:
// the len=1 level consumes indices 255..128, len=2 consumes 127..64, len=4 consumes 63..32,
// each in reverse block order. All entries are negated, as the inverse butterfly multiplies
// by -ψ.
const INV1: (Aligned<128>, Aligned<128>) = lane_table(255, -32, -1, -4, 4, true);
const INV2: (Aligned<64>, Aligned<64>) = lane_table(127, -16, -1, -2, 2, true);
const INV4: (Aligned<32>, Aligned<32>) = lane_table(63, -8, 0, -1, 1, true);

/// Loads vector `i` (coefficients `8i..8i+8`) of a 256-coefficient array
///
/// # Safety
///
/// `ptr` must be valid for reads of at least `8 * (i + 1)` `i32`s.
#[inline]
#[target_feature(enable = "avx2")]
unsafe fn ld(ptr: *const i32, i: usize) -> __m256i {
    // SAFETY: guaranteed by this function's contract. The load is unaligned, so the caller
    // owes us nothing beyond the address being readable.
    unsafe { _mm256_loadu_si256(ptr.add(8 * i).cast()) }
}

/// Stores vector `i` (coefficients `8i..8i+8`) of a 256-coefficient array
///
/// # Safety
///
/// `ptr` must be valid for writes of at least `8 * (i + 1)` `i32`s.
#[inline]
#[target_feature(enable = "avx2")]
unsafe fn st(ptr: *mut i32, i: usize, v: __m256i) {
    // SAFETY: guaranteed by this function's contract; the store is unaligned.
    unsafe { _mm256_storeu_si256(ptr.add(8 * i).cast(), v) }
}

/// Loads the 8-lane ψ vector at group `g` of a table
///
/// # Safety
///
/// `g * 8 + 8` must be within the table.
#[inline]
#[target_feature(enable = "avx2")]
unsafe fn ld_table<const N: usize>(table: &Aligned<N>, g: usize) -> __m256i {
    // SAFETY: guaranteed by this function's contract.
    unsafe { _mm256_loadu_si256(table.0.as_ptr().add(8 * g).cast()) }
}

/// Combines the high halves of two vectors of four 64-bit values into one vector of eight
/// 32-bit values, preserving order: `[hi(a0), hi(a1), hi(a2), hi(a3), hi(b0), ..., hi(b3)]`.
#[inline]
#[target_feature(enable = "avx2")]
fn pack_high(a: __m256i, b: __m256i) -> __m256i {
    // `shuffle_ps` with 0xDD selects dwords 1 and 3 of each 128-bit lane from each operand,
    // giving [a0,a1,b0,b1 | a2,a3,b2,b3]; the 64-bit permute then unscrambles the lanes.
    let interleaved = _mm256_castps_si256(_mm256_shuffle_ps(
        _mm256_castsi256_ps(a),
        _mm256_castsi256_ps(b),
        0xDD,
    ));
    _mm256_permute4x64_epi64(interleaved, 0b11_01_10_00)
}

/// Signed Montgomery multiply: returns `a · z · 2⁻³² mod p`, centered, for each of the 8 lanes.
///
/// `z` holds ψ per lane and `zq` the matching `ψ·p⁻¹ mod 2^32`. `z_odd`/`zq_odd` are those two
/// with their odd dwords moved down (`vpshufd` 0xF5); when ψ is broadcast across all lanes they
/// are just `z`/`zq` again, which is why the whole-vector levels pass the same value twice.
#[inline]
#[target_feature(enable = "avx2")]
fn mont_mul(
    a: __m256i,
    z: __m256i,
    zq: __m256i,
    z_odd: __m256i,
    zq_odd: __m256i,
    p: __m256i,
) -> __m256i {
    let a_odd = _mm256_shuffle_epi32(a, 0xF5);

    // Full 64-bit products a·ψ, split into the even and odd lanes of the input.
    let az_even = _mm256_mul_epi32(a, z);
    let az_odd = _mm256_mul_epi32(a_odd, z_odd);

    // The Montgomery quotient t = (a·ψ·p⁻¹) mod 2^32 lands in the low dword; multiplying that
    // by p (which again reads only the low dword) gives t·p, whose low dword equals a·ψ's.
    let t_even = _mm256_mul_epi32(a, zq);
    let t_odd = _mm256_mul_epi32(a_odd, zq_odd);
    let tp_even = _mm256_mul_epi32(t_even, p);
    let tp_odd = _mm256_mul_epi32(t_odd, p);

    // Subtract while still 64-bit, then gather the high dwords back into lane order. The two
    // low dwords are equal by construction, so the difference's low half is zero and its high
    // half is the whole (already centered, `|·| < p`) answer.
    let diff_even = _mm256_sub_epi64(az_even, tp_even);
    let diff_odd = _mm256_sub_epi64(az_odd, tp_odd);
    _mm256_blend_epi32(_mm256_shuffle_epi32(diff_even, 0xF5), diff_odd, 0xAA)
}

/// Centered Barrett reduction of 8 lanes: `r ≡ x (mod p)` with `|r| ≤ p/2 + 1`
#[inline]
#[target_feature(enable = "avx2")]
fn barrett(x: __m256i, p: __m256i) -> __m256i {
    let m = _mm256_set1_epi32(BARRETT_M as i32);
    // 2^47 as a pair of dwords, so the constant needs no 64-bit broadcast intrinsic
    let round = _mm256_setr_epi32(
        BARRETT_ROUND as i32,
        (BARRETT_ROUND >> 32) as i32,
        BARRETT_ROUND as i32,
        (BARRETT_ROUND >> 32) as i32,
        BARRETT_ROUND as i32,
        (BARRETT_ROUND >> 32) as i32,
        BARRETT_ROUND as i32,
        (BARRETT_ROUND >> 32) as i32,
    );

    let x_odd = _mm256_shuffle_epi32(x, 0xF5);
    let even = _mm256_add_epi64(_mm256_mul_epi32(x, m), round);
    let odd = _mm256_add_epi64(_mm256_mul_epi32(x_odd, m), round);

    // q = (x·M + 2^47) >> 48, arithmetic. AVX2 has no 64-bit arithmetic shift, but shifting
    // each dword right by 16 puts exactly that value, sign-extended, in the high dword — which
    // is where the gather below reads from anyway.
    let q_even = _mm256_srai_epi32(even, 16);
    let q_odd = _mm256_srai_epi32(odd, 16);
    let q = _mm256_blend_epi32(_mm256_shuffle_epi32(q_even, 0xF5), q_odd, 0xAA);

    _mm256_sub_epi32(x, _mm256_mullo_epi32(q, p))
}

/// Transposes 8 vectors as an 8×8 `i32` matrix, in place.
///
/// After this, `v[k]` lane `m` holds what was `v[m]` lane `k`. Applied twice it is the
/// identity, which is how the transform gets back to coefficient order.
#[inline]
#[target_feature(enable = "avx2")]
fn transpose8(v: &mut [__m256i; 8]) {
    // Interleave dwords, then qwords, then 128-bit lanes.
    let t0 = _mm256_unpacklo_epi32(v[0], v[1]);
    let t1 = _mm256_unpackhi_epi32(v[0], v[1]);
    let t2 = _mm256_unpacklo_epi32(v[2], v[3]);
    let t3 = _mm256_unpackhi_epi32(v[2], v[3]);
    let t4 = _mm256_unpacklo_epi32(v[4], v[5]);
    let t5 = _mm256_unpackhi_epi32(v[4], v[5]);
    let t6 = _mm256_unpacklo_epi32(v[6], v[7]);
    let t7 = _mm256_unpackhi_epi32(v[6], v[7]);

    let s0 = _mm256_unpacklo_epi64(t0, t2);
    let s1 = _mm256_unpackhi_epi64(t0, t2);
    let s2 = _mm256_unpacklo_epi64(t1, t3);
    let s3 = _mm256_unpackhi_epi64(t1, t3);
    let s4 = _mm256_unpacklo_epi64(t4, t6);
    let s5 = _mm256_unpackhi_epi64(t4, t6);
    let s6 = _mm256_unpacklo_epi64(t5, t7);
    let s7 = _mm256_unpackhi_epi64(t5, t7);

    v[0] = _mm256_permute2x128_si256(s0, s4, 0x20);
    v[1] = _mm256_permute2x128_si256(s1, s5, 0x20);
    v[2] = _mm256_permute2x128_si256(s2, s6, 0x20);
    v[3] = _mm256_permute2x128_si256(s3, s7, 0x20);
    v[4] = _mm256_permute2x128_si256(s0, s4, 0x31);
    v[5] = _mm256_permute2x128_si256(s1, s5, 0x31);
    v[6] = _mm256_permute2x128_si256(s2, s6, 0x31);
    v[7] = _mm256_permute2x128_si256(s3, s7, 0x31);
}

/// One Cooley-Tukey butterfly pair: `(lo, hi) ← (lo + ψ·hi, lo − ψ·hi)`
#[inline]
#[target_feature(enable = "avx2")]
fn ct_butterfly(
    lo: &mut __m256i,
    hi: &mut __m256i,
    z: __m256i,
    zq: __m256i,
    z_odd: __m256i,
    zq_odd: __m256i,
    p: __m256i,
) {
    let t = mont_mul(*hi, z, zq, z_odd, zq_odd, p);
    *hi = _mm256_sub_epi32(*lo, t);
    *lo = _mm256_add_epi32(*lo, t);
}

/// One Gentleman-Sande butterfly pair: `(lo, hi) ← (lo + hi, −ψ·(lo − hi))`
#[inline]
#[target_feature(enable = "avx2")]
fn gs_butterfly(
    lo: &mut __m256i,
    hi: &mut __m256i,
    z: __m256i,
    zq: __m256i,
    z_odd: __m256i,
    zq_odd: __m256i,
    p: __m256i,
) {
    let diff = _mm256_sub_epi32(*lo, *hi);
    *lo = _mm256_add_epi32(*lo, *hi);
    *hi = mont_mul(diff, z, zq, z_odd, zq_odd, p);
}

/// Loads the 8 vectors of transposed group `q` (coefficients `64q..64q+64`)
///
/// # Safety
///
/// `ptr` must be valid for reads of 256 `i32`s and `q < 4`.
#[inline]
#[target_feature(enable = "avx2")]
unsafe fn load_group(ptr: *const i32, q: usize) -> [__m256i; 8] {
    // SAFETY: guaranteed by this function's contract; `8q + 7 < 32`.
    let mut v = unsafe {
        [
            ld(ptr, 8 * q),
            ld(ptr, 8 * q + 1),
            ld(ptr, 8 * q + 2),
            ld(ptr, 8 * q + 3),
            ld(ptr, 8 * q + 4),
            ld(ptr, 8 * q + 5),
            ld(ptr, 8 * q + 6),
            ld(ptr, 8 * q + 7),
        ]
    };
    transpose8(&mut v);
    v
}

/// Transposes group `q` back to coefficient order and stores it
///
/// # Safety
///
/// `ptr` must be valid for writes of 256 `i32`s and `q < 4`.
#[inline]
#[target_feature(enable = "avx2")]
unsafe fn store_group(ptr: *mut i32, q: usize, v: &mut [__m256i; 8]) {
    transpose8(v);
    // SAFETY: guaranteed by this function's contract; `8q + 7 < 32`.
    unsafe {
        st(ptr, 8 * q, v[0]);
        st(ptr, 8 * q + 1, v[1]);
        st(ptr, 8 * q + 2, v[2]);
        st(ptr, 8 * q + 3, v[3]);
        st(ptr, 8 * q + 4, v[4]);
        st(ptr, 8 * q + 5, v[5]);
        st(ptr, 8 * q + 6, v[6]);
        st(ptr, 8 * q + 7, v[7]);
    }
}

/// In-place forward negacyclic NTT, then Barrett centering — the vector twin of
/// [`crate::arithmetic::ntt`]'s `ntt`, producing identical output for identical input.
///
/// # Safety
///
/// Requires AVX2. Input coefficients must satisfy `|a[i]| < 2^13`, as in the serial version.
#[target_feature(enable = "avx2")]
pub(crate) fn ntt(a: &mut [i32; RING_DEG]) {
    let p = _mm256_set1_epi32(P);
    let ptr = a.as_mut_ptr();

    // Levels with len ≥ 8: both halves of every butterfly are whole vectors, and ψ is constant
    // across a block, so it is simply broadcast.
    let mut k = 0usize;
    let mut half = 16usize; // len/8, i.e. the block half-width in vectors
    while half >= 1 {
        let mut start = 0usize;
        while start < 32 {
            k += 1;
            let z = _mm256_set1_epi32(ZETAS[k]);
            let zq = _mm256_set1_epi32(ZETAS_QINV[k]);
            let mut i = start;
            while i < start + half {
                // SAFETY: `i + half < 32` because `start + 2*half ≤ 32`, so both loads and
                // stores stay inside the 256-coefficient array.
                unsafe {
                    let mut lo = ld(ptr, i);
                    let mut hi = ld(ptr, i + half);
                    ct_butterfly(&mut lo, &mut hi, z, zq, z, zq, p);
                    st(ptr, i, lo);
                    st(ptr, i + half, hi);
                }
                i += 1;
            }
            start += 2 * half;
        }
        half /= 2;
    }

    // Levels with len < 8: transpose so each lane owns a whole block, then three more vertical
    // levels with per-lane ψ.
    for q in 0..4 {
        // SAFETY: `q < 4`, and `ptr` covers all 256 coefficients.
        let mut v = unsafe { load_group(ptr, q) };

        // len = 4: pair k with k+4, one ψ per lane
        // SAFETY: group index `q < 4` is in range for a 4-group table.
        let (z, zq) = unsafe { (ld_table(&FWD4.0, q), ld_table(&FWD4.1, q)) };
        let (z_odd, zq_odd) = (
            _mm256_shuffle_epi32(z, 0xF5),
            _mm256_shuffle_epi32(zq, 0xF5),
        );
        for i in 0..4 {
            let (mut lo, mut hi) = (v[i], v[i + 4]);
            ct_butterfly(&mut lo, &mut hi, z, zq, z_odd, zq_odd, p);
            v[i] = lo;
            v[i + 4] = hi;
        }

        // len = 2: pair k with k+2; the low pair and the high pair are different blocks and so
        // take different ψ
        for h in 0..2 {
            // SAFETY: `2q + h < 8` is in range for an 8-group table.
            let (z, zq) = unsafe { (ld_table(&FWD2.0, 2 * q + h), ld_table(&FWD2.1, 2 * q + h)) };
            let (z_odd, zq_odd) = (
                _mm256_shuffle_epi32(z, 0xF5),
                _mm256_shuffle_epi32(zq, 0xF5),
            );
            for i in 0..2 {
                let base = 4 * h + i;
                let (mut lo, mut hi) = (v[base], v[base + 2]);
                ct_butterfly(&mut lo, &mut hi, z, zq, z_odd, zq_odd, p);
                v[base] = lo;
                v[base + 2] = hi;
            }
        }

        // len = 1: adjacent pairs, four distinct blocks per lane
        for r in 0..4 {
            // SAFETY: `4q + r < 16` is in range for a 16-group table.
            let (z, zq) = unsafe { (ld_table(&FWD1.0, 4 * q + r), ld_table(&FWD1.1, 4 * q + r)) };
            let (z_odd, zq_odd) = (
                _mm256_shuffle_epi32(z, 0xF5),
                _mm256_shuffle_epi32(zq, 0xF5),
            );
            let (mut lo, mut hi) = (v[2 * r], v[2 * r + 1]);
            ct_butterfly(&mut lo, &mut hi, z, zq, z_odd, zq_odd, p);
            v[2 * r] = lo;
            v[2 * r + 1] = hi;
        }

        // SAFETY: as for `load_group`.
        unsafe { store_group(ptr, q, &mut v) };
    }

    for i in 0..32 {
        // SAFETY: `i < 32` indexes within the 256-coefficient array.
        unsafe { st(ptr, i, barrett(ld(ptr, i), p)) };
    }
}

/// In-place inverse negacyclic NTT — the vector twin of [`crate::arithmetic::ntt`]'s `invntt`,
/// including its mid-transform Barrett pass and final scaling.
///
/// # Safety
///
/// Requires AVX2. Input coefficients must satisfy `|a[i]| < p`, as in the serial version.
#[target_feature(enable = "avx2")]
fn invntt(a: &mut [i32; RING_DEG]) {
    let p = _mm256_set1_epi32(P);
    let ptr = a.as_mut_ptr();

    // Levels with len < 8, in transposed form: len = 1, then 2, then 4.
    for q in 0..4 {
        // SAFETY: `q < 4`, and `ptr` covers all 256 coefficients.
        let mut v = unsafe { load_group(ptr, q) };

        for r in 0..4 {
            // SAFETY: `4q + r < 16` is in range for a 16-group table.
            let (z, zq) = unsafe { (ld_table(&INV1.0, 4 * q + r), ld_table(&INV1.1, 4 * q + r)) };
            let (z_odd, zq_odd) = (
                _mm256_shuffle_epi32(z, 0xF5),
                _mm256_shuffle_epi32(zq, 0xF5),
            );
            let (mut lo, mut hi) = (v[2 * r], v[2 * r + 1]);
            gs_butterfly(&mut lo, &mut hi, z, zq, z_odd, zq_odd, p);
            v[2 * r] = lo;
            v[2 * r + 1] = hi;
        }

        for h in 0..2 {
            // SAFETY: `2q + h < 8` is in range for an 8-group table.
            let (z, zq) = unsafe { (ld_table(&INV2.0, 2 * q + h), ld_table(&INV2.1, 2 * q + h)) };
            let (z_odd, zq_odd) = (
                _mm256_shuffle_epi32(z, 0xF5),
                _mm256_shuffle_epi32(zq, 0xF5),
            );
            for i in 0..2 {
                let base = 4 * h + i;
                let (mut lo, mut hi) = (v[base], v[base + 2]);
                gs_butterfly(&mut lo, &mut hi, z, zq, z_odd, zq_odd, p);
                v[base] = lo;
                v[base + 2] = hi;
            }
        }

        // SAFETY: group index `q < 4` is in range for a 4-group table.
        let (z, zq) = unsafe { (ld_table(&INV4.0, q), ld_table(&INV4.1, q)) };
        let (z_odd, zq_odd) = (
            _mm256_shuffle_epi32(z, 0xF5),
            _mm256_shuffle_epi32(zq, 0xF5),
        );
        for i in 0..4 {
            let (mut lo, mut hi) = (v[i], v[i + 4]);
            gs_butterfly(&mut lo, &mut hi, z, zq, z_odd, zq_odd, p);
            v[i] = lo;
            v[i + 4] = hi;
        }

        // SAFETY: as for `load_group`.
        unsafe { store_group(ptr, q, &mut v) };
    }

    // Levels with len ≥ 8. `k` continues downward from where the transposed levels stopped:
    // they consumed 128 + 64 + 32 = 224 of the 256 ψ entries.
    let mut k = 32usize;
    let mut half = 1usize;
    while half < 32 {
        let mut start = 0usize;
        while start < 32 {
            k -= 1;
            let z = _mm256_set1_epi32(-ZETAS[k]);
            let zq = _mm256_set1_epi32(qinv(-ZETAS[k]));
            let mut i = start;
            while i < start + half {
                // SAFETY: `i + half < 32` because `start + 2*half ≤ 32`.
                unsafe {
                    let mut lo = ld(ptr, i);
                    let mut hi = ld(ptr, i + half);
                    gs_butterfly(&mut lo, &mut hi, z, zq, z, zq, p);
                    st(ptr, i, lo);
                    st(ptr, i + half, hi);
                }
                i += 1;
            }
            start += 2 * half;
        }
        half *= 2;

        // Halfway through (after the len=8 level), re-center so the un-reduced sum path cannot
        // outgrow an i32 over the remaining four levels. Matches the serial `len == 16` check.
        if half == 2 {
            for i in 0..32 {
                // SAFETY: `i < 32`.
                unsafe { st(ptr, i, barrett(ld(ptr, i), p)) };
            }
        }
    }

    // One final Montgomery multiply undoes both the 1/256 and the Montgomery factor.
    let scale = _mm256_set1_epi32(INVNTT_SCALE);
    let scale_q = _mm256_set1_epi32(qinv(INVNTT_SCALE));
    for i in 0..32 {
        // SAFETY: `i < 32`.
        unsafe {
            st(
                ptr,
                i,
                mont_mul(ld(ptr, i), scale, scale_q, scale, scale_q, p),
            )
        };
    }
}

/// Widens 8 `u16`s at `src[8i..]` to `i32`, zero-extending (uniform coefficients)
///
/// # Safety
///
/// `src` must be valid for reads of at least `8 * (i + 1)` `u16`s.
#[inline]
#[target_feature(enable = "avx2")]
unsafe fn widen_u16(src: *const u16, i: usize) -> __m256i {
    // SAFETY: guaranteed by this function's contract.
    unsafe { _mm256_cvtepu16_epi32(_mm_loadu_si128(src.add(8 * i).cast())) }
}

/// Widens 8 `u16`s at `src[8i..]` to `i32`, sign-extending (CBD secret coefficients, which are
/// wrapping-`u16` encodings of small signed values)
///
/// # Safety
///
/// `src` must be valid for reads of at least `8 * (i + 1)` `u16`s.
#[inline]
#[target_feature(enable = "avx2")]
unsafe fn widen_i16(src: *const u16, i: usize) -> __m256i {
    // SAFETY: guaranteed by this function's contract.
    unsafe { _mm256_cvtepi16_epi32(_mm_loadu_si128(src.add(8 * i).cast())) }
}

/// Forward-transforms a ring element with plain coefficients in `[0, 2^13)`
///
/// # Safety
///
/// Requires AVX2.
#[target_feature(enable = "avx2")]
pub(crate) fn from_uniform(elem: &[u16; RING_DEG]) -> [i32; RING_DEG] {
    let mut a = [0i32; RING_DEG];
    for i in 0..32 {
        // SAFETY: `i < 32` is in range for both the 256-`u16` source and the 256-`i32` output.
        unsafe { st(a.as_mut_ptr(), i, widen_u16(elem.as_ptr(), i)) };
    }
    ntt(&mut a);
    a
}

/// Forward-transforms a CBD secret, reading each coefficient as the signed value it encodes
///
/// # Safety
///
/// Requires AVX2.
#[target_feature(enable = "avx2")]
pub(crate) fn from_secret(elem: &[u16; RING_DEG]) -> [i32; RING_DEG] {
    let mut a = [0i32; RING_DEG];
    for i in 0..32 {
        // SAFETY: `i < 32` is in range for both the 256-`u16` source and the 256-`i32` output.
        unsafe { st(a.as_mut_ptr(), i, widen_i16(elem.as_ptr(), i)) };
    }
    ntt(&mut a);
    a
}

/// Adds the pointwise product `lhs ∘ rhs` into an unreduced `i64` accumulator
///
/// # Safety
///
/// Requires AVX2.
#[target_feature(enable = "avx2")]
pub(crate) fn pointwise_mul_acc(
    acc: &mut [i64; RING_DEG],
    lhs: &[i32; RING_DEG],
    rhs: &[i32; RING_DEG],
) {
    let acc_ptr = acc.as_mut_ptr();
    for i in 0..32 {
        // SAFETY: `i < 32` indexes 8 coefficients of each 256-element operand; the accumulator
        // slots for those coefficients are the two 4-wide vectors at `16i` and `16i + 4`.
        unsafe {
            let l = ld(lhs.as_ptr(), i);
            let r = ld(rhs.as_ptr(), i);
            let l_odd = _mm256_shuffle_epi32(l, 0xF5);
            let r_odd = _mm256_shuffle_epi32(r, 0xF5);
            let even = _mm256_mul_epi32(l, r); // lanes 0,2,4,6
            let odd = _mm256_mul_epi32(l_odd, r_odd); // lanes 1,3,5,7

            // Re-interleave the two halves back into coefficient order.
            let low = _mm256_unpacklo_epi64(even, odd);
            let high = _mm256_unpackhi_epi64(even, odd);
            let first = _mm256_permute2x128_si256(low, high, 0x20);
            let second = _mm256_permute2x128_si256(low, high, 0x31);

            let a0 = acc_ptr.add(8 * i).cast::<__m256i>();
            let a1 = acc_ptr.add(8 * i + 4).cast::<__m256i>();
            _mm256_storeu_si256(a0, _mm256_add_epi64(_mm256_loadu_si256(a0), first));
            _mm256_storeu_si256(a1, _mm256_add_epi64(_mm256_loadu_si256(a1), second));
        }
    }
}

/// Montgomery-reduces the accumulator, inverse-transforms it, and packs the result back into
/// wrapping-`u16` coefficients
///
/// # Safety
///
/// Requires AVX2.
#[target_feature(enable = "avx2")]
pub(crate) fn reduce_invntt(acc: &[i64; RING_DEG]) -> [u16; RING_DEG] {
    let p = _mm256_set1_epi32(P);
    let p_inv = _mm256_set1_epi32(P_INV as i32);

    let mut v = [0i32; RING_DEG];
    for i in 0..32 {
        // SAFETY: `i < 32`, so the two 4-wide accumulator vectors at `8i` and `8i + 4` and the
        // 8-wide output vector `i` are all in range.
        unsafe {
            let a0 = _mm256_loadu_si256(acc.as_ptr().add(8 * i).cast());
            let a1 = _mm256_loadu_si256(acc.as_ptr().add(8 * i + 4).cast());
            // Montgomery reduction of an i64: t = (a mod 2^32)·p⁻¹, then (a − t·p) >> 32. As in
            // `mont_mul`, the low dwords cancel, so the high dword is the whole answer.
            let t0 = _mm256_mul_epi32(a0, p_inv);
            let t1 = _mm256_mul_epi32(a1, p_inv);
            let d0 = _mm256_sub_epi64(a0, _mm256_mul_epi32(t0, p));
            let d1 = _mm256_sub_epi64(a1, _mm256_mul_epi32(t1, p));
            st(v.as_mut_ptr(), i, pack_high(d0, d1));
        }
    }

    invntt(&mut v);

    // Lift each coefficient to its centered representative and truncate to 16 bits.
    let p_half = _mm256_set1_epi32(P_HALF);
    let low16 = _mm256_set1_epi32(0xFFFF);
    let mut out = [0u16; RING_DEG];
    for i in 0..16 {
        // SAFETY: `2i + 1 < 32` reads two coefficient vectors; the packed result is the 16
        // `u16`s at `out[16i..16i + 16]`.
        unsafe {
            let mut wide = [_mm256_setzero_si256(); 2];
            for (half, slot) in wide.iter_mut().enumerate() {
                let x = ld(v.as_ptr(), 2 * i + half);
                // to_canonical: add p where negative, giving [0, p)
                let x = _mm256_add_epi32(x, _mm256_and_si256(_mm256_srai_epi32(x, 31), p));
                // then subtract p above ⌊p/2⌋, giving (-p/2, p/2]
                let over = _mm256_srai_epi32(_mm256_sub_epi32(p_half, x), 31);
                let x = _mm256_sub_epi32(x, _mm256_and_si256(p, over));
                *slot = _mm256_and_si256(x, low16);
            }
            // Both inputs are masked to 16 bits, so the unsigned saturating pack is exact; the
            // qword permute repairs the lane interleaving `vpackusdw` introduces.
            let packed = _mm256_packus_epi32(wide[0], wide[1]);
            let packed = _mm256_permute4x64_epi64(packed, 0b11_01_10_00);
            _mm256_storeu_si256(out.as_mut_ptr().add(16 * i).cast(), packed);
        }
    }
    out
}
