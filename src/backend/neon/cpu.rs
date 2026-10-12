//! Runtime NEON + SHA3 detection
//!
//! NEON is part of the AArch64 base ISA, and `build.rs` only compiles this backend for targets
//! that enable it with a non-softfloat ABI, so there is nothing to probe for NEON. The ARMv8.2
//! SHA3 extension the backend's Keccak needs is not baseline, so that is checked at runtime via
//! `cpufeatures`, which asks the OS (`getauxval` on Linux and Android, `sysctlbyname` on Apple
//! platforms) and reports `false` on any other OS.

cpufeatures::new!(cpuid_sha3, "sha3");

/// Whether the NEON backend may be used on this CPU.
///
/// When the target already enables `sha3` (always the case with `--cfg kopis_backend="neon"`)
/// the build script sets `kopis_neon_assume`, so this collapses to a constant `true` and every
/// dispatch site folds away.
#[inline(always)]
pub(crate) fn available() -> bool {
    cfg!(kopis_neon_assume) || cpuid_sha3::get()
}
