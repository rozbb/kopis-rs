#!/bin/bash

set -euo pipefail

# Alignment flags come from https://www.bazhenov.me/posts/2024-02-performance-roulette/
RUSTFLAGS="-C llvm-args=-align-all-functions=6 -C llvm-args=-align-all-nofallthru-blocks=6 -C target-cpu=native" \
    cargo bench $@
