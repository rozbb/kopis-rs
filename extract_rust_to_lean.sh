#!/bin/bash

set -eux

/home/dev/aeneas/charon/bin/charon cargo --preset=aeneas
/home/dev/aeneas/bin/aeneas kopis.llbc -backend lean -loops-to-rec -namespace RustKopis
# aeneas names the output file after the crate (kopis -> Kopis.lean) and there is no flag
# to override that, so rename.  `-namespace RustKopis` above puts the extracted
# definitions under `RustKopis.*` rather than `kopis.*`, so that a reader of the proofs
# can tell at a glance which names came from the Rust and which are Lean-side.
mv Kopis.lean ./lean/ExtractedRust.lean
rm kopis.llbc
