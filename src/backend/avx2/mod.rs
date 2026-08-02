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
//! Hashing is deliberately absent. TurboSHAKE stays behind the `turboshake` crate for both
//! backends, so there is no Keccak permutation here to keep in step with it — no matter how
//! attractive a four-way one looks, since Kopis samples its matrix in ℓ² independent XOF calls.
//! What this module does with XOF output, once the `turboshake` crate has produced it, is
//! another matter: see [`sample`].
//!
//! # Safety
//!
//! All of this module's `unsafe` is confined to [`intrinsics`] and [`cpu`], and it is there for
//! exactly two reasons:
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

mod cpu;
mod intrinsics;
pub(crate) mod ntt;
pub(crate) mod sample;
pub(crate) mod ser;

pub(crate) use cpu::available;
