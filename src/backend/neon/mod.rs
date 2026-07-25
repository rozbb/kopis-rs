//! The AArch64 NEON backend.
//!
//! Every routine here is a lane-parallel restatement of a portable one and produces
//! bit-identical output; the tests in each submodule check that against the serial code
//! directly, which is what keeps the Lean correspondence proof meaningful for NEON builds. It
//! mirrors [`super::avx2`] operation for operation — the only structural difference is that a
//! NEON vector is four `i32`s rather than eight, so the negacyclic NTT's whole-vector levels run
//! down to `len = 4` and only the last two levels (`len = 2, 1`) live inside a vector.
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
