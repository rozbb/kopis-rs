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

case "${BACKEND}" in
    serial)
        # Serial benches

        RUST_SERIAL_FLAGS="--cfg kopis_backend=\"serial\" --cfg keccak_backend=\"soft\""

	rm -rf target/criterion
        RUSTFLAGS="${RUST_SERIAL_FLAGS} ${RUST_PERF_FLAGS}" \
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
                RUST_ARCH_FLAGS="-C target-cpu=native"
                ;;
            aarch64 | arm64)
                SIMD="neon"
                ;;
            *)
                echo "Unsupported CPU architecture for autodetect benches: ${ARCH}" >&2
                exit 1
                ;;
        esac

	rm -rf target/criterion
        RUSTFLAGS="${RUST_ARCH_FLAGS} ${RUST_PERF_FLAGS}" \
	    cargo bench --bench all -- "${BENCH_ARGS[@]}"
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
