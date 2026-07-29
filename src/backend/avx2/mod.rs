//! The x86-64 / x86 AVX2 backend.
//!
//! [`sample`] and [`ser`] are lane-parallel restatements of portable routines and produce
//! bit-identical output; the tests in each check that against the serial code directly, which
//! is what keeps the Lean correspondence proof meaningful for them.
//!
//! [`ntt`] is not, and this is the one place in the crate where an accelerated backend departs
//! from the portable code it stands in for. It transforms over two 16-bit primes rather than
//! one 26-bit one, because AVX2 has a 16-bit high-multiply and no 32-bit equivalent; only the
//! endpoints of the pipeline agree with the portable version, so it is tested end to end and
//! the Lean proof does not cover it. [`super::crt`] makes the full argument; the NEON backend
//! does the same thing with the same constants.
//!
//! Hashing is deliberately absent. TurboSHAKE stays behind the `turboshake` crate for both
//! backends, so there is no Keccak permutation here to keep in step with it — no matter how
//! attractive a four-way one looks, since Kopis samples its matrix in ℓ² independent XOF calls.
//! What this module does with XOF output, once the `turboshake` crate has produced it, is
//! another matter: see [`sample`].
//!
//! # Safety
//!
//! This module is where the crate's `unsafe` lives, and it is there for exactly two reasons:
//!
//! * SIMD intrinsics, which require the `avx2` target feature. Every function that uses them
//!   carries `#[target_feature(enable = "avx2")]`, so the compiler emits the instructions
//!   without them being enabled crate-wide, and calling such a function from outside is unsafe
//!   precisely because the caller must know the CPU has AVX2. [`available`] is the only thing
//!   that establishes that, and every entry point is reached through a call site guarded by it.
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
