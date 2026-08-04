//! Build script for `kopis`.
//!
//! Its only job is to decide which arithmetic backend the crate compiles: the portable
//! `serial` backend (which is also what gets extracted to Lean), or the x86-64 `avx2`
//! backend layered on top of it.
//!
//! # Selection
//!
//! By default the choice is made automatically: on x86/x86-64 targets the AVX2 backend is
//! compiled in alongside the serial one and selected at *runtime* by a CPUID check, and on
//! AArch64 targets that carry the `neon` target feature with a hardfloat ABI the NEON backend
//! is compiled in (it is always selected there, since the feature is confirmed at build time).
//! Either way the resulting binary runs everywhere for its architecture. On every other target
//! — including softfloat AArch64 targets such as `aarch64-unknown-none-softfloat`, where
//! enabling NEON is ABI-unsound — only the serial backend exists.
//!
//! The choice can be overridden with the `kopis_backend` cfg, e.g.
//!
//! ```sh
//! RUSTFLAGS='--cfg kopis_backend="serial"' cargo build
//! RUSTFLAGS='--cfg kopis_backend="avx2"'   cargo build
//! RUSTFLAGS='--cfg kopis_backend="neon"'   cargo build
//! ```
//!
//! * `serial` compiles only the portable backend; no `unsafe`, no runtime dispatch.
//! * `avx2` asserts at build time that AVX2 really is available for the target and then
//!   compiles the AVX2 backend *unconditionally*, with no runtime check and no fallback.
//!   If AVX2 is not available the build fails with a panic from this script.
//! * `neon` does the same for AArch64 NEON: it asserts NEON is available for the target and
//!   compiles the NEON backend unconditionally, or fails the build if it is not.
//!
//! Every backend, the portable one included, transforms over the same two 16-bit primes
//! combined by the CRT: see `src/backend/crt.rs` for the scheme and `src/arithmetic/ntt_crt.rs`
//! for the portable implementation. So this choice is only about which instruction set does the
//! work, not about which arithmetic gets used.
//!
//! "Available" is decided at build time, because that is the only time a compile-time panic
//! can happen. For AVX2 it means: the target is x86/x86-64, and either `avx2` is in the
//! target's enabled feature set (e.g. `-C target-feature=+avx2` or `-C target-cpu=native`), or
//! we are not cross-compiling and the build host's CPU reports AVX2 support. For NEON it
//! means: the target is AArch64, `neon` is in the target's enabled feature set, and the ABI is
//! not softfloat. NEON is a mandatory part of the AArch64 base ISA, but rustc also supports
//! softfloat AArch64 targets whose ABI is incompatible with the vector registers — enabling
//! the `neon` feature there is unsound and slated to become a hard error
//! (rust-lang/rust#134375) — so the architecture alone is not enough.

use std::env;

/// The backend a `--cfg kopis_backend="..."` override asks for
enum Override {
    Serial,
    Avx2,
    Neon,
}

fn main() {
    println!("cargo::rerun-if-changed=build.rs");
    println!("cargo::rerun-if-env-changed=CARGO_ENCODED_RUSTFLAGS");
    println!("cargo::rerun-if-env-changed=RUSTFLAGS");

    // Declare every cfg we set or read, so `unexpected_cfgs` stays quiet.
    println!("cargo::rustc-check-cfg=cfg(kopis_backend, values(\"serial\", \"avx2\", \"neon\"))");
    println!("cargo::rustc-check-cfg=cfg(kopis_avx2)");
    println!("cargo::rustc-check-cfg=cfg(kopis_avx2_assume)");
    println!("cargo::rustc-check-cfg=cfg(kopis_neon)");
    println!("cargo::rustc-check-cfg=cfg(kopis_neon_assume)");

    let arch = env::var("CARGO_CFG_TARGET_ARCH").unwrap_or_default();
    let is_x86 = arch == "x86_64" || arch == "x86";
    let is_aarch64 = arch == "aarch64";

    match backend_override() {
        // Portable backend only. Nothing to emit: the AVX2 code is behind `kopis_avx2`.
        Some(Override::Serial) => {}

        // Forced AVX2: verify it is actually available, then compile it in with no runtime
        // check. A failed verification is a hard build error, as requested.
        Some(Override::Avx2) => {
            if !is_x86 {
                panic!(
                    "kopis: --cfg kopis_backend=\"avx2\" requires an x86 or x86-64 target, \
                     but the target architecture is `{}`. Remove the override to use the \
                     portable backend.",
                    arch
                );
            }
            if !avx2_is_available() {
                panic!(
                    "kopis: --cfg kopis_backend=\"avx2\" was requested but AVX2 could not be \
                     confirmed for this target. Either build with `-C target-feature=+avx2` \
                     (or `-C target-cpu=native`) on a machine whose CPU supports AVX2, or drop \
                     the override to get automatic runtime detection."
                );
            }
            println!("cargo::rustc-cfg=kopis_avx2");
            println!("cargo::rustc-cfg=kopis_avx2_assume");
        }

        // Forced NEON: verify it is actually available, then compile it in with no runtime
        // check. A failed verification is a hard build error, as requested.
        Some(Override::Neon) => {
            if !neon_is_available(is_aarch64) {
                panic!(
                    "kopis: --cfg kopis_backend=\"neon\" requires an AArch64 target with the \
                     `neon` target feature and a non-softfloat ABI, but the target is `{}`. \
                     (On softfloat AArch64 targets enabling NEON is ABI-unsound; see \
                     rust-lang/rust#134375.) Remove the override to use the portable backend.",
                    env::var("TARGET").unwrap_or(arch)
                );
            }
            println!("cargo::rustc-cfg=kopis_neon");
            println!("cargo::rustc-cfg=kopis_neon_assume");
        }

        // Autodetect: compile in the accelerated backend for the target's architecture and pick
        // at runtime. On x86 that is AVX2 behind a CPUID check; on AArch64 it is NEON whenever
        // the target's feature set and ABI actually permit it (see `neon_is_available`), in
        // which case the runtime check is a constant `true`.
        None => {
            if is_x86 {
                println!("cargo::rustc-cfg=kopis_avx2");
            } else if neon_is_available(is_aarch64) {
                println!("cargo::rustc-cfg=kopis_neon");
            }
        }
    }
}

/// Whether NEON can be assumed present for the target being built.
///
/// AArch64 mandates NEON in the base ISA, but that alone is not sufficient: rustc supports
/// softfloat AArch64 targets (e.g. `aarch64-unknown-none-softfloat`) whose ABI is incompatible
/// with the vector registers, where enabling the `neon` target feature is unsound and slated
/// to become a hard error (rust-lang/rust#134375). So require the target to actually enable
/// the `neon` feature *and* to not use the softfloat ABI.
fn neon_is_available(is_aarch64: bool) -> bool {
    if !is_aarch64 {
        return false;
    }
    let features = env::var("CARGO_CFG_TARGET_FEATURE").unwrap_or_default();
    let has_neon = features.split(',').any(|feature| feature == "neon");
    let softfloat = env::var("CARGO_CFG_TARGET_ABI").unwrap_or_default() == "softfloat";
    has_neon && !softfloat
}

/// Parses `--cfg kopis_backend="..."` out of the flags cargo is passing to rustc.
///
/// We read the flags rather than testing `cfg!(kopis_backend = ...)` directly because cargo
/// does not reliably apply `RUSTFLAGS` to build scripts themselves (it does not when
/// cross-compiling), so the cfg may well not be set for *this* crate.
fn backend_override() -> Option<Override> {
    // `CARGO_ENCODED_RUSTFLAGS` is the authoritative, unambiguously-split form; it is always
    // set for build scripts by any cargo new enough to matter. `RUSTFLAGS` is a fallback for
    // odd invocations, split on whitespace.
    let flags: Vec<String> = match env::var("CARGO_ENCODED_RUSTFLAGS") {
        Ok(encoded) => encoded.split('\x1f').map(String::from).collect(),
        Err(_) => env::var("RUSTFLAGS")
            .unwrap_or_default()
            .split_whitespace()
            .map(String::from)
            .collect(),
    };

    let mut requested = None;
    let mut iter = flags.iter();
    while let Some(flag) = iter.next() {
        // Accept both `--cfg foo` (value in the next argument) and `--cfg=foo`.
        let spec = if flag == "--cfg" {
            match iter.next() {
                Some(next) => next.as_str(),
                None => break,
            }
        } else if let Some(rest) = flag.strip_prefix("--cfg=") {
            rest
        } else {
            continue;
        };

        let Some(value) = spec.strip_prefix("kopis_backend=") else {
            continue;
        };
        // Strip the quotes rustc's cfg syntax puts around the value, if present.
        let value = value.trim_matches('"');

        // Later flags win, matching how rustc itself would resolve a repeated cfg.
        requested = match value {
            "serial" => Some(Override::Serial),
            "avx2" => Some(Override::Avx2),
            "neon" => Some(Override::Neon),
            other => panic!(
                "kopis: unknown backend `{}` in --cfg kopis_backend. \
                 Valid values are \"serial\", \"avx2\", and \"neon\".",
                other
            ),
        };
    }

    requested
}

/// Whether AVX2 can be assumed present for the target being built.
///
/// Two ways to know: it is in the target feature set the crate is compiled with, or the build
/// is not a cross-compile and the host CPU has it.
fn avx2_is_available() -> bool {
    let features = env::var("CARGO_CFG_TARGET_FEATURE").unwrap_or_default();
    if features.split(',').any(|feature| feature == "avx2") {
        return true;
    }

    let host = env::var("HOST").unwrap_or_default();
    let target = env::var("TARGET").unwrap_or_default();
    if host.is_empty() || host != target {
        return false;
    }

    host_has_avx2()
}

#[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
fn host_has_avx2() -> bool {
    std::arch::is_x86_feature_detected!("avx2")
}

#[cfg(not(any(target_arch = "x86", target_arch = "x86_64")))]
fn host_has_avx2() -> bool {
    false
}
