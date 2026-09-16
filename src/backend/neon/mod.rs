//! The AArch64 NEON backend
//!
//! [`sample`] and [`ser`] are lane-parallel restatements of the portable routines and produce
//! bit-identical output. [`ntt`] is not: it transforms over the same two primes as
//! [`crate::arithmetic::ntt_crt`] but with its own per-lane ψ tables, so only the endpoints of
//! the pipeline agree with the portable code and the Lean proof does not cover it. It differs
//! from the AVX2 backend only in vector width — 8 `i16` here against 16 — so the NTT's
//! whole-vector levels run down to `len = 8` and the last three live inside a vector.
//!
//! [`keccak`] is a two-way TurboSHAKE: two independent sponges, one per 64-bit lane, which is
//! the shape Kopis samples in (ℓ² independent XOF calls for the matrix, ℓ more for the secret).
//! It needs the ARMv8.2 SHA3 extension, which `build.rs` makes a condition on the *whole*
//! module: there is exactly one NEON configuration, the `+sha3` one, and every other target
//! falls back to the portable code.
//!
//! # Safety
//!
//! All of this module's `unsafe` is confined to [`intrinsics`], for two reasons:
//!
//! * SIMD intrinsics require the `neon` target feature (and `sha3` for the four FEAT_SHA3
//!   instructions [`keccak`] uses). Every function that uses them carries
//!   `#[target_feature(enable = "neon")]`, so calling one from outside is unsafe: the caller
//!   must know the CPU has NEON. On AArch64 that is unconditional, and [`available`] is what
//!   states it; every entry point is reached through a call site guarded by it. FEAT_SHA3 is
//!   not baseline, which is why it is a build-time condition on the whole module rather than
//!   something [`available`] could check.
//! * Unaligned loads and stores over fixed-size arrays. These are [`intrinsics`]' memory
//!   accessors, which take an array or slice reference and an index and bounds-check it, so
//!   [`ntt`], [`ser`], [`sample`] and [`keccak`] contain no `unsafe` and no raw pointers at all.
//!
//! # Extraction
//!
//! [`intrinsics`] is the one module charon is told to keep opaque; the Lean side supplies its
//! semantics by hand. See `lean/NEON_VERIFICATION_PLAN.md`. Unlike the AVX2 backend, [`cpu`] is
//! not kept opaque: on AArch64 `available()` is a compile-time constant `true`, so it extracts
//! as an ordinary definition.

mod cpu;
mod intrinsics;
#[cfg(test)]
mod intrinsics_vectors;
pub(crate) mod keccak;
pub(crate) mod ntt;
pub(crate) mod sample;
pub(crate) mod ser;

pub(crate) use cpu::available;
