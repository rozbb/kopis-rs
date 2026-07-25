//! Runtime NEON detection.
//!
//! On AArch64, Advanced SIMD (NEON) is part of the base ISA — every AArch64 CPU has it, and it
//! needs no OS opt-in the way x86's YMM state does — so there is nothing to probe. The backend
//! is only ever compiled for AArch64 (see `build.rs`), so this check is a compile-time constant
//! `true`, and every dispatch site that consults it folds away exactly as it does under
//! `--cfg kopis_backend="neon"`.

/// Whether the NEON backend may be used on this CPU.
///
/// Always `true`: `kopis_neon` is only set for AArch64 targets, where NEON is mandatory.
#[inline(always)]
pub(crate) fn available() -> bool {
    cfg!(target_arch = "aarch64")
}
