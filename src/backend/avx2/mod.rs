//! The x86-64 / x86 AVX2 backend.
//!
//! [`sample`] and [`ser`] are lane-parallel restatements of portable routines and produce
//! bit-identical output. [`sample`]'s own test checks that against the portable sampler
//! directly; [`ser`] has no test module of its own and is instead exercised against the
//! portable code through `RingElem::deserialize`'s tests (which dispatch here on AVX2
//! hardware) and the KATs. That equivalence is what keeps the Lean correspondence proof
//! meaningful for them.
//!
//! [`ntt`] is not, and this is the one place in the crate where an accelerated backend departs
//! from the portable code it stands in for. It transforms over two 16-bit primes rather than
//! one 26-bit one, because AVX2 has a 16-bit high-multiply and no 32-bit equivalent; only the
//! endpoints of the pipeline agree with the portable version, so it is tested end to end and
//! the Lean proof does not cover it. [`super::crt`] makes the full argument; the NEON backend
//! does the same thing with the same constants.
//!
//! [`keccak`] is a four-way TurboSHAKE: four independent sponges, one per 64-bit lane, which is
//! the shape Kopis samples in (ℓ² independent XOF calls for the matrix, ℓ more for the secret).
//! It stands apart from the rest of the backend in two ways — it names `core::arch` intrinsics
//! directly rather than going through [`intrinsics`], and it is therefore not extractable. See
//! the note under *Extraction* below.
//!
//! # Safety
//!
//! Apart from [`keccak`], all of this module's `unsafe` is confined to [`intrinsics`] and
//! [`cpu`], and it is there for exactly two reasons:
//!
//! * SIMD intrinsics, which require the `avx2` target feature. Every function that uses them
//!   carries `#[target_feature(enable = "avx2")]`, so the compiler emits the instructions
//!   without them being enabled crate-wide, and calling such a function from outside one is
//!   unsafe precisely because the caller must know the CPU has AVX2. [`available`] is the only
//!   thing that establishes that, and every entry point is reached through a call site guarded
//!   by it. Within the backend, where every function carries the attribute, the calls are safe.
//! * Unaligned loads and stores over fixed-size arrays. These are [`intrinsics`]' memory
//!   accessors, which take an array reference and a vector index and bounds-check it, so
//!   [`ntt`], [`ser`] and [`sample`] contain no `unsafe` and no raw pointers at all.
//!
//! There is no raw allocation, no lifetime erasure, and no aliasing: inputs are `&` and outputs
//! are `&mut` or returned by value, so the borrow checker still separates them.
//!
//! # Extraction
//!
//! [`intrinsics`] exists so that this backend can be extracted to Lean: it is the one module
//! charon is told to keep opaque, and the Lean side supplies its semantics by hand. See its
//! module docs and `lean/AVX2_VERIFICATION_PLAN.md`.
//!
//! [`keccak`] breaks that arrangement. It names intrinsics outside [`intrinsics`], so charon has
//! nothing to lower for it and it must be marked opaque in its own right — which puts the whole
//! four-way permutation in the trusted base rather than the verified one, backed only by its
//! `matches_scalar` test against the `turboshake` crate. Porting it to [`intrinsics`] would need
//! wrappers (and matching Lean axioms) for the 64-bit shifts, `or`, `andnot` and `xor` that
//! Keccak needs and the NTT does not.

mod cpu;
mod intrinsics;
#[cfg(test)]
mod intrinsics_vectors;
pub(crate) mod keccak;
pub(crate) mod ntt;
pub(crate) mod sample;
pub(crate) mod ser;

pub(crate) use cpu::available;
