#!/bin/bash

set -eux

# Extract the *serial* backend only. The AVX2 backend is x86 intrinsics behind `unsafe`, which
# charon cannot translate and which the Lean proofs say nothing about. Forcing the backend here
# makes every `#[cfg(kopis_avx2)]` dispatch block disappear before rustc hands the crate over,
# so what gets extracted is exactly the portable code the proofs are written against.
#
# This goes through RUSTFLAGS rather than charon's --rustc-arg because build.rs has to see it
# too: build.rs is what turns the cfg into the backend selection.
export RUSTFLAGS='--cfg kopis_backend="serial"'

/home/dev/aeneas/charon/bin/charon cargo --preset=aeneas
/home/dev/aeneas/bin/aeneas kopis.llbc -backend lean -loops-to-rec -namespace RustKopis
mv Kopis.lean ./lean/ExtractedRust.lean
rm kopis.llbc
