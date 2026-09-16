//! The x86-64 / x86 AVX2 backend
//!
//! [`sample`] and [`ser`] are lane-parallel restatements of the portable routines and produce
//! bit-identical output. [`ntt`] is not: it transforms over the same two primes as
//! [`crate::arithmetic::ntt_crt`] but with its own per-lane ψ tables and reduction schedule, so
//! only the endpoints of the pipeline agree with the portable code and the Lean proof does not
//! cover it.
//!
//! [`keccak`] is a four-way TurboSHAKE: four independent sponges, one per 64-bit lane, which is
//! the shape Kopis samples in (ℓ² independent XOF calls for the matrix, ℓ more for the secret).
//!
//! # Safety
//!
//! Apart from [`keccak`], all of this module's `unsafe` is confined to [`intrinsics`] and
//! [`cpu`], for two reasons:
//!
//! * SIMD intrinsics require the `avx2` target feature. Every function that uses them carries
//!   `#[target_feature(enable = "avx2")]`, so calling one from outside the backend is unsafe:
//!   the caller must know the CPU has AVX2. [`available`] is the only thing that establishes
//!   that, and every entry point is reached through a call site guarded by it.
//! * Unaligned loads and stores over fixed-size arrays. These are [`intrinsics`]' memory
//!   accessors, which take an array reference and a vector index and bounds-check it, so
//!   [`ntt`], [`ser`] and [`sample`] contain no `unsafe` and no raw pointers at all.
//!
//! # Extraction
//!
//! [`intrinsics`] is the one module charon is told to keep opaque; the Lean side supplies its
//! semantics by hand. See `lean/AVX2_VERIFICATION_PLAN.md`. [`keccak`] names intrinsics outside
//! [`intrinsics`], so it must be marked opaque in its own right, which puts the four-way
//! permutation in the trusted base rather than the verified one, backed only by its
//! `matches_scalar` test against the `turboshake` crate.

mod cpu;
mod intrinsics;
#[cfg(test)]
mod intrinsics_vectors;
pub(crate) mod keccak;
pub(crate) mod ntt;
pub(crate) mod sample;
pub(crate) mod ser;

pub(crate) use cpu::available;
