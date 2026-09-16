//! Runtime AVX2 detection
//!
//! `is_x86_feature_detected!` lives in `std`, which a `no_std` crate cannot use, so this goes
//! through `cpufeatures`, whose x86 backend is a `no_std` CPUID probe.
//!
//! Checking the AVX2 feature bit alone is not enough: a CPU can report AVX2 while the OS leaves
//! YMM state out of its context switches, in which case using `ymm` registers corrupts other
//! threads. `cpufeatures` checks OSXSAVE and XCR0 bits 1 and 2 (SSE and AVX state) alongside the
//! feature bit, which is the sequence Intel documents for this.

cpufeatures::new!(cpuid_avx2, "avx2");

/// Whether the AVX2 backend may be used on this CPU.
///
/// When the crate was built with `--cfg kopis_backend="avx2"` the build script already proved
/// AVX2 is available, so this collapses to a constant `true` and every dispatch site folds away.
/// `cpufeatures` folds the same way on its own when the target enables `avx2` outright; the
/// explicit check keeps that guarantee tied to the cfg the build script reasons about.
#[inline(always)]
pub(crate) fn available() -> bool {
    cfg!(kopis_avx2_assume) || cpuid_avx2::get()
}
