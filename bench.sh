#!/bin/bash

set -euo pipefail

# Just does serial benches for now

SERIAL_FLAGS='--cfg kopis_backend="serial" --cfg keccak_backend="soft"'

# Alignment flags come from https://www.bazhenov.me/posts/2024-02-performance-roulette/
PERF_FLAGS="-C llvm-args=-align-all-functions=6 -C llvm-args=-align-all-nofallthru-blocks=6 -C target-cpu=native"

RUSTFLAGS="${SERIAL_FLAGS} ${PERF_FLAGS}" cargo bench $@
