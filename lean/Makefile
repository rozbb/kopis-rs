# Kopis verification convenience targets.
#
# Run from this directory (kopis-rs/lean).  These wrap the `lake` invocations
# for the Kopis KEM correspondence proofs and the spec test-vector runner.
# Extraction (Rust -> Lean) lives in `../extract_rust_to_lean.sh`, which
# regenerates `ExtractedRustSerial.lean`; this file only builds/checks what is already
# extracted.

LAKE ?= lake

# Cap the number of parallel Lean workers.  Each Lean+Mathlib worker resident set
# is ~1.75 GB; `lake` defaults its build parallelism to the core count (nproc).  On
# a memory-constrained host (e.g. 4 cores / 4 GB RAM) that over-subscribes RAM and
# the build swap-thrashes — a clean build takes ~15-20 min instead of ~4 min.
# Set this to 2 to keep peak memory ~3.5 GB and avoid the thrash.
LEAN_NUM_THREADS ?= 8
export LEAN_NUM_THREADS

.DEFAULT_GOAL := help

# ---------------------------------------------------------------------------
# Proofs
# ---------------------------------------------------------------------------

# Build (= kernel-verify) the Kopis proof library: the extracted ExtractedRustSerial.lean
# plus every Kopis/Properties/*.lean, then TopLevelTheoremsSerial.lean, which restates the
# top-level results, and TrustBase.lean, which re-checks their axiom footprint against
# the audited list.  A green build IS the machine-checked proof.
.PHONY: prove-kopis
prove-kopis:
	$(LAKE) build Kopis TopLevelTheoremsSerial TrustBase

# Build the AVX2 side: the second extraction (ExtractedRustAvx2.lean, from an
# `--cfg kopis_backend="avx2"` build) plus Kopis/Avx2/*, whose Intrinsics.lean supplies the
# hand-written semantics of the opaque SIMD wrappers.  Kept out of `prove-kopis` because the
# audited claim is still about the serial backend and this is a second 7k-line extraction.
.PHONY: prove-avx2
prove-avx2:
	$(LAKE) build KopisAvx2

# ---------------------------------------------------------------------------
# Spec tests
# ---------------------------------------------------------------------------

# Run the audited Lean spec against the standard Kopis test vectors + KAT
# (SpecTests/Kopis/Run.lean).  `lake exe` builds the executable first.
# Must be run from this directory: the runner reads ../tests/ref_test_vectors-*.jsonl
# relative to the current directory.
.PHONY: test-kopis-spec
test-kopis-spec:
	$(LAKE) exe kopisTests

# ---------------------------------------------------------------------------
# Help
# ---------------------------------------------------------------------------

.PHONY: help
help:
	@echo "Kopis targets (run from kopis-rs/lean):"
	@echo "  make prove-kopis       build + kernel-verify the Kopis proofs (lake build Kopis)"
	@echo "  make prove-avx2        build the AVX2 extraction + its intrinsic semantics"
	@echo "  make test-kopis-spec   run the Lean spec test vectors + KAT (lake exe kopisTests)"
	@echo ""
	@echo "  Parallelism is capped at LEAN_NUM_THREADS=$(LEAN_NUM_THREADS) to fit RAM on small hosts."
	@echo "  On a machine with more memory, raise it: make prove-kopis LEAN_NUM_THREADS=8"
