import Lake
open Lake DSL

require aeneas from "../../aeneas/backends/lean"

package «kopis»

/-! ## Aeneas-extracted Rust code

    `ExtractedRustSerial.lean` is generated verbatim by `../extract_rust_to_lean.sh`
    (charon + aeneas, `-loops-to-rec`) from the `kopis-rs` crate. Never edit it
    by hand: re-run the extraction script instead. It is the *only* link
    between the Rust source and the proofs below. -/
lean_lib «ExtractedRustSerial»

/-! ## The AVX2 backend

    `ExtractedRustAvx2.lean` is the same crate extracted from an
    `--cfg kopis_backend="avx2"` build, in its own namespace: the AVX2 backend
    plus the dispatch blocks that reach it. `backend::avx2::intrinsics` and
    `backend::avx2::cpu` are extracted opaquely, so what it contains for those
    is uninterpreted axioms; `Kopis/Avx2/Intrinsics.lean` supplies their
    semantics and is the *only* place that does.

    Neither is in the default target: the audited claim is still about the
    serial backend, and `make prove-kopis` should not pay for a second
    extraction. Build this side with `make prove-kopis-avx2`. -/
lean_lib «ExtractedRustAvx2»

lean_lib «KopisAvx2» where
  roots := #[`Kopis.Avx2.Intrinsics]

/-! ## Specifications library

    `Spec` collects the audited, executable specification the Rust code is
    proved against: Kopis (`kopis-spec.md`) plus the hash primitives it builds
    on (SHA-3 / Keccak from FIPS 202, TurboSHAKE from RFC 9861). Kept as a
    separate root namespace so the file layout mirrors the conceptual layer
    (audited spec vs. proof) and so reviewers can build just the specs via
    `lake build Spec`. -/
lean_lib «Spec»

/-! ## Kopis KEM correspondence proofs

    `Kopis` collects the correspondence proofs tying the extracted code
    (`ExtractedRustSerial`) to the audited `Spec.Kopis` specification. A green
    `lake build Kopis` (= `make prove-kopis`) IS the machine-checked proof:
    it must compile with no errors and no `sorry`s. -/
@[default_target]
lean_lib «Kopis»

/-! ## The audit surface

    `TopLevelTheoremsSerial.lean` restates the top-level correspondence theorems and the
    translation functions they are stated through — what a human reviewer needs in
    order to check what has actually been proved. It re-proves nothing (each
    statement is discharged by the theorem proved in `Kopis`), so a restatement that
    drifted would fail to compile. Start here when reviewing, then `TrustBase`. -/
@[default_target]
lean_lib «TopLevelTheoremsSerial»

/-! ## The trust base

    `TrustBase.lean` is the other half of the audit surface: the assumptions the
    theorems rest on, and a build-time check that recomputes the axiom footprint
    of every top-level theorem and fails if it is not exactly the audited list.
    Separate from `TopLevelTheoremsSerial.lean` because the trust base is the one part
    of the audit that differs per backend. -/
@[default_target]
lean_lib «TrustBase»

/-! ## Spec test vectors

    `SpecTests` runs the audited specification against the Kopis test vectors
    and KAT files under the crate's `tests/` directory (the same `.jsonl` files
    the Rust `tests/ref_kat.rs` consumes). Not part of the default `lake build`
    closure; run it via the `kopisTests` executable below
    (`lake exe kopisTests` = `make test-kopis-spec`). The runner reads the
    `.jsonl` vectors at run time relative to the current directory, so invoke
    it from this directory. -/
lean_lib «SpecTests» where
  globs := #[.andSubmodules `SpecTests]

lean_exe kopisTests where
  root := `SpecTests.Kopis.Run
