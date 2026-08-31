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
//! [`keccak`] is a two-way TurboSHAKE: two independent sponges, one per 64-bit lane, which is the
//! shape Kopis samples in (ℓ² independent XOF calls for the matrix, ℓ more for the secret). It is
//! the counterpart of the AVX2 backend's four-way version, narrower only because a `uint64x2_t`
//! holds two 64-bit lanes to a `Vec256`'s four. It needs the ARMv8.2 SHA3 extension to be worth
//! using at all — its own docs make the case — and it is enough of what this backend is for that
//! the extension is a condition on the *whole* module: `build.rs` compiles the NEON backend only
//! for targets that have it, and everything else falls back to the portable serial code. So
//! there is exactly one NEON configuration, the `+sha3` one, and no target gets a half-built
//! version of it.
//!
//! # Safety
//!
//! All of this module's `unsafe` is confined to [`intrinsics`], and it is there for exactly two
//! reasons:
//!
//! * SIMD intrinsics, which require the `neon` target feature (and `sha3` for the four FEAT_SHA3
//!   instructions [`keccak`] uses). Every function that uses them carries
//!   `#[target_feature(enable = "neon")]`, so calling one from outside is unsafe: the caller must
//!   know the CPU has NEON. On AArch64 that is unconditional (NEON is baseline), and [`available`]
//!   is what states it; every entry point is reached through a call site guarded by it. FEAT_SHA3
//!   is not baseline, which is why it is a *build-time* condition on the whole module rather than
//!   something [`available`] could check. Within the backend, where every function carries the
//!   attribute, the calls are safe.
//! * Unaligned loads and stores over fixed-size arrays. These are [`intrinsics`]' memory
//!   accessors, which take an array or slice reference and an index and bounds-check it, so
//!   [`ntt`], [`ser`], [`sample`] and [`keccak`] contain no `unsafe` and no raw pointers at all.
//!
//! There is no raw allocation, no lifetime erasure, and no aliasing: inputs are `&` and outputs
//! are `&mut` or returned by value, so the borrow checker still separates them.
//!
//! # Extraction
//!
//! [`intrinsics`] exists so that this backend can be extracted to Lean: it is the one module
//! charon is told to keep opaque, and the Lean side supplies its semantics by hand. See its
//! module docs and `lean/NEON_VERIFICATION_PLAN.md`.
//!
//! Unlike the AVX2 backend, [`cpu`] is *not* kept opaque: on AArch64 `available()` is a
//! compile-time constant `true` with nothing to probe, so it extracts as an ordinary definition
//! and costs no assumption at all.

mod cpu;
mod intrinsics;
#[cfg(test)]
mod intrinsics_vectors;
pub(crate) mod keccak;
pub(crate) mod ntt;
pub(crate) mod sample;
pub(crate) mod ser;

pub(crate) use cpu::available;
