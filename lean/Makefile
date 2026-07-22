# Kopis verification convenience targets.
#
# Run from this directory (kopis-rs/lean).  These wrap the `lake` invocations
# for the Kopis KEM correspondence proofs and the spec test-vector runner.
# Extraction (Rust -> Lean) lives in `../extract_rust_to_lean.sh`, which
# regenerates `ExtractedRust.lean`; this file only builds/checks what is already
# extracted.

LAKE ?= lake

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
