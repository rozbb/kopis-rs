//! The x86-64 / x86 AVX2 backend.
//!
//! Every routine here is a lane-parallel restatement of a portable one and produces
//! bit-identical output; the tests in each submodule check that against the serial code
//! directly, which is what keeps the Lean correspondence proof meaningful for AVX2 builds.
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
pub(crate) mod keccak;
pub(crate) mod ntt;
pub(crate) mod sample;
pub(crate) mod ser;

pub(crate) use cpu::available;
