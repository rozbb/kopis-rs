//! Build script for `kopis`
//!
//! Its only job is to decide which arithmetic backend the crate compiles: the portable `serial`
//! backend, or a vector backend layered on top of it.
//!
//! # Selection
//!
//! By default the choice is automatic:
//! * If the target CPU is x86/x86-64, the AVX2 backend is unconditionally compiled in alongside the serial one and selected at runtime via `cpufeatures`
//! * If the target CPU is AArch64 with the `neon` target feature and a hardfloat ABI, the NEON backend is compiled in alongside the serial one and selected at runtime if the CPU has the SHA3 extension (always, if `sha3` is a target feature)
//! * For any other architectures or softfloat AArch64, the serial backend is used.
//!
//! The choice can be overridden with the `kopis_backend` cfg:
//!
//! ```sh
//! RUSTFLAGS='--cfg kopis_backend="serial"' cargo build
//! RUSTFLAGS='--cfg kopis_backend="avx2"'   cargo build
//! RUSTFLAGS='--cfg kopis_backend="neon"'   cargo build
//! ```
//!
//! * `serial` compiles only the portable backend
//! * `avx2` and `neon` assert at build time that the target is compatible with the selected backend
//!   (panicking if false), then compile that backend unconditionally with no runtime check and no
//!   fallback.
//!
//! Finally, the build panics if any internal-only cfgs are passed in (`kopis_avx2`, `kopis_neon`,
//! and their `_assume` forms).

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
            if !target_has_feature("avx2") {
                panic!(
                    "kopis: --cfg kopis_backend=\"avx2\" requires `avx2` in the target \
                     features. Build with `-C target-feature=+avx2` (or a `-C target-cpu` that \
                     implies it), or drop the override to get automatic runtime detection."
                );
            }
            println!("cargo::rustc-cfg=kopis_avx2");
            println!("cargo::rustc-cfg=kopis_avx2_assume");
        }

        // Forced NEON: verify it is actually available, then compile it in with no runtime
        // check. A failed verification is a hard build error, as requested.
        Some(Override::Neon) => {
            if !(neon_is_sound_on_target(is_aarch64) && target_has_feature("sha3")) {
                panic!(
                    "kopis: --cfg kopis_backend=\"neon\" requires an AArch64 target with the \
                     `neon` and `sha3` target features and a non-softfloat ABI, but the target \
                     is `{}`. (The backend's two-way TurboSHAKE needs the ARMv8.2 SHA3 \
                     extension; build with `-C target-feature=+sha3` or `-C target-cpu=native` \
                     on a CPU that has it. On softfloat AArch64 targets enabling NEON is \
                     ABI-unsound; see rust-lang/rust#134375.) Remove the override to use the \
                     portable backend.",
                    env::var("TARGET").unwrap_or(arch)
                );
            }
            println!("cargo::rustc-cfg=kopis_neon");
            println!("cargo::rustc-cfg=kopis_neon_assume");
        }

        // Autodetect: compile in the accelerated backend for the target's architecture and pick
        // at runtime. On x86 that is AVX2 behind a CPUID check. On AArch64 it is NEON whenever
        // the target's ABI permits it (see `neon_is_sound_on_target`), behind a check for the
        // ARMv8.2 SHA3 extension its Keccak needs; that check is a constant `true` if the target
        // already enables `sha3`.
        None => {
            if is_x86 {
                println!("cargo::rustc-cfg=kopis_avx2");
            } else if neon_is_sound_on_target(is_aarch64) {
                println!("cargo::rustc-cfg=kopis_neon");
                if target_has_feature("sha3") {
                    println!("cargo::rustc-cfg=kopis_neon_assume");
                }
            }
        }
    }
}

/// Whether the NEON backend can be compiled for the target being built.
///
/// AArch64 mandates NEON in the base ISA, but rustc also supports softfloat AArch64 targets (e.g.
/// `aarch64-unknown-none-softfloat`) whose ABI is incompatible with the vector registers, where
/// enabling the `neon` target feature is unsound and slated to become a hard error
/// (rust-lang/rust#134375). So require the target to actually enable `neon` *and* to not use the
/// softfloat ABI. This is a property of the target, not the CPU, so unlike the ARMv8.2 SHA3
/// extension the backend also needs, it cannot be checked at runtime.
fn neon_is_sound_on_target(is_aarch64: bool) -> bool {
    let softfloat = env::var("CARGO_CFG_TARGET_ABI").unwrap_or_default() == "softfloat";
    is_aarch64 && target_has_feature("neon") && !softfloat
}

/// Whether `feature` is in the target feature set the crate is compiled with
fn target_has_feature(feature: &str) -> bool {
    let features = env::var("CARGO_CFG_TARGET_FEATURE").unwrap_or_default();
    features.split(',').any(|f| f == feature)
}

/// The cfgs this script emits. Passing them in directly would bypass its checks.
const INTERNAL_CFGS: [&str; 4] = [
    "kopis_avx2",
    "kopis_avx2_assume",
    "kopis_neon",
    "kopis_neon_assume",
];

/// Parses `--cfg kopis_backend="..."` out of the flags cargo is passing to rustc, rejecting any
/// of [`INTERNAL_CFGS`].
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

        if INTERNAL_CFGS.contains(&spec) {
            panic!(
                "kopis: --cfg {} is internal to the build script. Use --cfg kopis_backend=... \
                 instead.",
                spec
            );
        }

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
