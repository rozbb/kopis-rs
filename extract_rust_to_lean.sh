#!/bin/bash

set -eux

/home/dev/aeneas/charon/bin/charon cargo --preset=aeneas
/home/dev/aeneas/bin/aeneas kopis.llbc -backend lean -loops-to-rec -namespace RustKopis
mv Kopis.lean ./lean/ExtractedRust.lean
rm kopis.llbc
