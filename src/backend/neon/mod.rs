//! The AArch64 NEON backend.
//!
//! [`sample`] and [`ser`] are lane-parallel restatements of portable routines and produce
//! bit-identical output; the tests in each check that against the serial code directly, which
//! is what keeps the Lean correspondence proof meaningful for them.
//!
//! [`ntt`] is not. It transforms over the two 16-bit primes of [`super::crt`] rather than the
//! portable code's single 26-bit one, so only the endpoints of the pipeline agree and it is
//! tested end to end by `neon_matches_serial` in [`crate::arithmetic::ntt`]. That module makes
//! the argument for the trade; both vector backends do the same thing, and differ only in
//! vector width — 8 `i16` here against AVX2's 16, so the NTT's whole-vector levels run down to
//! `len = 8` and the last three live inside a vector.
//!
//! Hashing is deliberately absent, exactly as in the AVX2 backend: TurboSHAKE stays behind the
//! `turboshake` crate, and Kopis samples its matrix in ℓ² independent XOF calls, so there is no
//! four-way Keccak permutation to keep in step with here. What this module does with XOF output
//! is another matter: see [`sample`].
//!
//! # Safety
//!
//! This module is where a NEON build's `unsafe` lives, and it is there for two reasons:
//!
//! * SIMD intrinsics. Every function that uses them carries `#[target_feature(enable = "neon")]`,
//!   so calling one from outside is unsafe: the caller must know the CPU has NEON. On AArch64
//!   that is unconditional (NEON is baseline), and [`available`] is what states it; every entry
//!   point is reached through a call site guarded by it.
//! * Unaligned pointer loads and stores over fixed-size arrays. The arrays are all
//!   `[_; RING_DEG]` with `RING_DEG = 256`, or short fixed scratch buffers; the indices are all
//!   bounded by construction, and each site carries the bound that makes it in-range.
//!
//! There is no raw allocation, no lifetime erasure, and no aliasing: inputs are `&` and outputs
//! are `&mut` or returned by value, so the borrow checker still separates them.

mod cpu;
pub(crate) mod ntt;
pub(crate) mod sample;
pub(crate) mod ser;

pub(crate) use cpu::available;
