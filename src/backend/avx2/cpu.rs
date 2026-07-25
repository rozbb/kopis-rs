//! Runtime AVX2 detection.
//!
//! `is_x86_feature_detected!` lives in `std`, which a `no_std` crate cannot use, so we ask the
//! CPU ourselves. On x86 that is a pure computation — CPUID and XGETBV have no side effects and
//! need no OS support — so the whole check is a handful of instructions with no allocation.

#[cfg(target_arch = "x86")]
use core::arch::x86 as arch;
#[cfg(target_arch = "x86_64")]
use core::arch::x86_64 as arch;

use core::sync::atomic::{AtomicU8, Ordering};

/// Cached result of [`detect`]: `UNKNOWN`, `ABSENT`, or `PRESENT`.
///
/// Racing threads may both run the detection, but CPUID is deterministic so they compute the
/// same answer and the store is idempotent. `Relaxed` is enough: the value is a plain bool with
/// no data hanging off it.
static CACHE: AtomicU8 = AtomicU8::new(UNKNOWN);

const UNKNOWN: u8 = 0;
const ABSENT: u8 = 1;
const PRESENT: u8 = 2;

/// Whether the AVX2 backend may be used on this CPU.
///
/// When the crate was built with `--cfg kopis_backend="avx2"` the build script already proved
/// AVX2 is available, so this collapses to a constant `true` and every dispatch site folds away.
#[inline(always)]
pub(crate) fn available() -> bool {
    if cfg!(kopis_avx2_assume) {
        return true;
    }

    match CACHE.load(Ordering::Relaxed) {
        PRESENT => true,
        ABSENT => false,
        _ => {
            let found = detect();
            CACHE.store(if found { PRESENT } else { ABSENT }, Ordering::Relaxed);
            found
        }
    }
}

/// Asks the CPU whether it supports AVX2 *and* whether the OS has enabled the register state
/// AVX2 needs.
///
/// Checking OS support is not optional: a CPU can report AVX2 while the OS leaves YMM state out
/// of its context switches, in which case using `ymm` registers corrupts other threads. The
/// sequence below is the one Intel documents for this — OSXSAVE, then XCR0 bits 1 and 2 (SSE
/// and AVX state), then the AVX2 feature bit itself.
fn detect() -> bool {
    // SAFETY: `__cpuid`/`__cpuid_count` are available on every x86 CPU this crate can be
    // compiled for (CPUID predates the 32-bit targets Rust supports), read no memory, and have
    // no side effects. We query leaf 0 first for the maximum supported leaf so the leaf-7 query
    // below is in range.
    unsafe {
        if arch::__cpuid(0).eax < 7 {
            return false;
        }

        let leaf1 = arch::__cpuid(1);
        // Bit 27 of ECX: the OS has enabled XSAVE/XGETBV. Without it, XGETBV faults.
        const OSXSAVE: u32 = 1 << 27;
        if leaf1.ecx & OSXSAVE == 0 {
            return false;
        }

        // Bits 1 and 2 of XCR0: the OS saves and restores XMM and YMM state on context switch.
        if xcr0() & 0b110 != 0b110 {
            return false;
        }

        // Bit 5 of leaf 7's EBX: AVX2.
        arch::__cpuid_count(7, 0).ebx & (1 << 5) != 0
    }
}

/// Reads XCR0, the OS's mask of enabled extended-state components.
///
/// # Safety
///
/// The caller must have confirmed the OSXSAVE bit of CPUID leaf 1; XGETBV raises #UD otherwise.
#[target_feature(enable = "xsave")]
unsafe fn xcr0() -> u64 {
    // SAFETY: guaranteed by this function's own contract, which the sole caller upholds.
    unsafe { arch::_xgetbv(0) }
}
