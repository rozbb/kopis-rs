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

# Graviola's ML-KEM is AVX2-only, so it has no place in the serial or NEON runs. Criterion has no
# exclusion flag — its only selector is the positional FILTER regex, and the `regex` crate has no
# negative lookahead — so "everything but graviola" has to be spelled as an allowlist of the
# benchmark-group prefixes we do want. Keep in sync with the group names in `benches/all.rs`.
NO_GRAVIOLA_FILTER='^(kopis|libcrux|awslc)'

# Sets BENCH_ARGS to the arguments to pass after `--`: the caller's, or the graviola-excluding
# filter when the caller gave none. Criterion accepts only one positional filter, so a
# caller-supplied one would collide with ours; there theirs wins and the note says so.
set_filtered_bench_args() {
    if [[ $# -eq 0 ]]; then
        BENCH_ARGS=("${NO_GRAVIOLA_FILTER}")
    else
        BENCH_ARGS=("$@")
        echo "note: extra bench args given, so the graviola benches are NOT filtered out." >&2
        echo "      Pass '${NO_GRAVIOLA_FILTER}' as your filter to exclude them." >&2
    fi
}

case "${BACKEND}" in
    serial)
        # Serial benches

        RUST_SERIAL_FLAGS='--cfg kopis_backend="serial" --cfg keccak_backend="soft"'
        C_SERIAL_FLAGS="-DMY_ASSEMBLER_IS_TOO_OLD_FOR_AVX"

        set_filtered_bench_args "$@"

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
                # AVX2 is the one configuration graviola belongs in, so run everything.
                BENCH_ARGS=("$@")
                ;;
            aarch64 | arm64)
                SIMD="neon"
                set_filtered_bench_args "$@"
                ;;
            *)
                echo "Unsupported CPU architecture for autodetect benches: ${ARCH}" >&2
                exit 1
                ;;
        esac

        RUSTFLAGS="${RUST_PERF_FLAGS}" cargo bench --bench all -- ${BENCH_ARGS[@]+"${BENCH_ARGS[@]}"}
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
