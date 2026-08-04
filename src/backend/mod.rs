//! Architecture-specific backends.
//!
//! The portable ("serial") implementation of every operation lives in its natural home
//! (`arithmetic/`, `ser.rs`, `sample.rs`) and is the *only* thing that exists when the crate is
//! built with `--cfg kopis_backend="serial"`. That is also the form that gets extracted to
//! Lean, so it is deliberately left untouched by everything here.
//!
//! This module holds the accelerated alternatives — [`avx2`] on x86/x86-64 and [`neon`] on
//! AArch64. Each serial entry point that has one starts with a small `#[cfg(kopis_avx2)]` /
//! `#[cfg(kopis_neon)]` block that hands off to the backend when it is usable; with the
//! accelerated backends disabled those blocks do not exist at all and the source reduces
//! *exactly* to the portable code. At most one of the two is ever compiled, since a target is
//! either x86 or AArch64.
//!
//! All the `unsafe` in the crate lives either in [`avx2`] / [`neon`] or in those dispatch
//! blocks, and the blocks contain nothing but the guarded call. Everything else is under a
//! crate-level `deny(unsafe_code)`, which becomes `forbid` outright in a serial build. See
//! [`avx2`] for the safety argument the calls rely on.

/// The instruction-set-independent half of the two-prime NTT every backend uses: the moduli,
/// the ψ tables and the correctness argument. The portable transform in
/// [`crate::arithmetic::ntt_crt`] reads them directly; each vector backend adds its own
/// intrinsics and per-lane tables, whose shape depends on the vector width.
pub(crate) mod crt;

#[cfg(kopis_avx2)]
#[allow(unsafe_code)]
pub(crate) mod avx2;

#[cfg(kopis_avx2)]
pub(crate) use avx2::available as avx2_available;

#[cfg(kopis_neon)]
#[allow(unsafe_code)]
pub(crate) mod neon;

#[cfg(kopis_neon)]
pub(crate) use neon::available as neon_available;
