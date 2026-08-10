#!/bin/bash

set -euo pipefail

usage() {
    echo "Usage: $0 <serial|auto> [extra cargo bench args...]" >&2
    exit 1
}

if [[ $# -lt 1 ]]; then
    usage
fi

BACKEND="$1"
shift

# Alignment flags come from https://www.bazhenov.me/posts/2024-02-performance-roulette/
RUST_PERF_FLAGS="-C llvm-args=-align-all-functions=6 -C llvm-args=-align-all-nofallthru-blocks=6"

# Criterion has no exclusion flag — its only selector is the positional FILTER regex, and the
# `regex` crate has no negative lookahead — so "everything but X" has to be spelled as an allowlist
# of the benchmark-group prefixes we do want. Keep these in sync with the group names in
# `benches/all.rs`.
#
# libcrux registers a separate benchmark group per SIMD backend, and each run takes only the variant
# that matches it: `libcrux_serial_*` (portable) on the serial run, `libcrux_avx2_*` on the AVX2 one.
# libcrux has no NEON backend at all, so the NEON run drops it rather than comparing NEON kopis
# against portable libcrux, which would not be a like-for-like measurement. Graviola has hand-written
# assembly for both AVX2 and NEON, so it joins both of those runs, but has nothing for the serial one.
SERIAL_FILTER='^(kopis|libcrux_serial|awslc)'
AVX2_FILTER='^(kopis|libcrux_avx2|awslc|graviola)'
NEON_FILTER='^(kopis|awslc|graviola)'

# Sets BENCH_ARGS to the arguments to pass after `--`: the caller's, or $1 — this run's allowlist
# filter — when the caller gave none. Criterion accepts only one positional filter, so a
# caller-supplied one would collide with ours; there theirs wins and the note says so.
set_filtered_bench_args() {
    local filter="$1"
    shift

    if [[ $# -eq 0 ]]; then
        BENCH_ARGS=("${filter}")
    else
        BENCH_ARGS=("$@")
        echo "note: extra bench args given, so this run is NOT filtered to its backend's benches." >&2
        echo "      Pass '${filter}' as your filter to restrict it." >&2
    fi
}

case "${BACKEND}" in
    serial)
        # Serial benches

        RUST_SERIAL_FLAGS="--cfg kopis_backend=\"serial\" --cfg keccak_backend=\"soft\" \
            --cfg mlkem_selkie_backend=\"scalar\" --cfg sha3_selkie_backend=\"scalar\""
        C_SERIAL_FLAGS="-DMY_ASSEMBLER_IS_TOO_OLD_FOR_AVX"

        set_filtered_bench_args "${SERIAL_FILTER}" "$@"

	rm -rf target/criterion
        RUSTFLAGS="${RUST_SERIAL_FLAGS} ${RUST_PERF_FLAGS}" AWS_LC_SYS_CFLAGS="${C_SERIAL_FLAGS}" \
            cargo bench --bench all -- "${BENCH_ARGS[@]}"
        OUTDIR="target/criterion-serial"
        ;;

    auto)
        # Autodetect benches

        # Name the output directory after the SIMD backend the host CPU will
        # actually select. `uname -m` reports x86_64 on Linux/macOS Intel, and
        # aarch64 (Linux) / arm64 (macOS) on ARM.
        ARCH="$(uname -m)"
        case "${ARCH}" in
            x86_64 | amd64)
                SIMD="avx2"
                set_filtered_bench_args "${AVX2_FILTER}" "$@"
                ;;
            aarch64 | arm64)
                SIMD="neon"
                set_filtered_bench_args "${NEON_FILTER}" "$@"
                ;;
            *)
                echo "Unsupported CPU architecture for autodetect benches: ${ARCH}" >&2
                exit 1
                ;;
        esac

	rm -rf target/criterion
        RUSTFLAGS="${RUST_PERF_FLAGS}" cargo bench --bench all -- "${BENCH_ARGS[@]}"
        OUTDIR="target/criterion-${SIMD}"
        ;;
    *)
        usage
        ;;
esac

rm -rf "${OUTDIR}"
mv target/criterion "${OUTDIR}"

echo "DONE"
echo "Benchmarks can be found in ${OUTDIR}"
