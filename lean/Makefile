# Kopis verification convenience targets.
#
# Run from this directory (kopis-rs/lean).  These wrap the `lake` invocations
# for the Kopis KEM correspondence proofs and the spec test-vector runner.
# Extraction (Rust -> Lean) lives in `../extract_rust_to_lean.sh`, which
# regenerates `ExtractedRust.lean`; this file only builds/checks what is already
# extracted.

LAKE ?= lake

# Cap the number of parallel Lean workers.  Each Lean+Mathlib worker resident set
# is ~1.75 GB; `lake` defaults its build parallelism to the core count (nproc).  On
# a memory-constrained host (e.g. 4 cores / 4 GB RAM) that over-subscribes RAM and
# the build swap-thrashes — a clean build takes ~15-20 min instead of ~4 min.
# Capping to 2 keeps peak memory ~3.5 GB and avoids the thrash.  Raise it on hosts
# with more RAM, e.g. `make prove-kopis LEAN_NUM_THREADS=8`.
LEAN_NUM_THREADS ?= 2
export LEAN_NUM_THREADS

.DEFAULT_GOAL := help

# ---------------------------------------------------------------------------
# Proofs
# ---------------------------------------------------------------------------

# Build (= kernel-verify) the Kopis proof library: the extracted ExtractedRust.lean
# plus every Kopis/Properties/*.lean, then TopLevelTheorems.lean, which restates
# the top-level results and re-checks the axiom footprint.  A green build IS the
# machine-checked proof.
.PHONY: prove-kopis
prove-kopis:
	$(LAKE) build Kopis TopLevelTheorems

# ---------------------------------------------------------------------------
# Spec tests
# ---------------------------------------------------------------------------

# Run the audited Lean spec against the standard Kopis test vectors + KAT
# (SpecTests/Kopis/Run.lean).  `lake exe` builds the executable first.
# Must be run from this directory: the runner reads SpecTests/Kopis/vectors/*
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
	@echo "  make test-kopis-spec   run the Lean spec test vectors + KAT (lake exe kopisTests)"
	@echo ""
	@echo "  Parallelism is capped at LEAN_NUM_THREADS=$(LEAN_NUM_THREADS) to fit RAM on small hosts."
	@echo "  On a machine with more memory, raise it: make prove-kopis LEAN_NUM_THREADS=8"
