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

# Criterion bench filters for whene we're using different backends
SERIAL_FILTER='^(kopis|libcrux_serial|awslc|selkie)'
AVX2_FILTER='^(kopis|libcrux_avx2|awslc|graviola|selkie)'
NEON_FILTER='^(kopis|awslc|graviola|selkie)'

# If this script got no inputs, then set BENCH_ARGS to the function's arg. Otherwise, we got a
# user-supplied keyword filter, so ignore the arg and set BENCH_ARGS to that
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

        RUST_ARCH_FLAGS=""
        ARCH="$(uname -m)"
        case "${ARCH}" in
            x86_64 | amd64)
                SIMD="avx2"
		# Use a target that supports AVX2 but not AVX512. This is so that mlkem-selkie
		# doesn't use AVX512
                RUST_ARCH_FLAGS="-C target-cpu=x86-64-v3"
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
        RUSTFLAGS="${RUST_ARCH_FLAGS} ${RUST_PERF_FLAGS}" cargo bench --bench all -- "${BENCH_ARGS[@]}"
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
