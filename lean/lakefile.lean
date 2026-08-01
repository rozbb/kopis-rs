import Lake
open Lake DSL

require aeneas from "../../aeneas/backends/lean"

package «kopis»

/-! ## Aeneas-extracted Rust code

    `ExtractedRust.lean` is generated verbatim by `../extract_rust_to_lean.sh`
    (charon + aeneas, `-loops-to-rec`) from the `kopis-rs` crate. Never edit it
    by hand: re-run the extraction script instead. It is the *only* link
    between the Rust source and the proofs below. -/
lean_lib «ExtractedRust»

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
    (`ExtractedRust`) to the audited `Spec.Kopis` specification. A green
    `lake build Kopis` (= `make prove-kopis`) IS the machine-checked proof:
    it must compile with no errors and no `sorry`s. -/
@[default_target]
lean_lib «Kopis»

/-! ## The audit surface

    `TopLevelTheorems.lean` restates the top-level correspondence theorems, the
    translation functions they are stated through, and the full list of assumed
    axioms — everything a human reviewer needs to read in order to check what has
    actually been proved. It re-proves nothing (each statement is discharged by
    the theorem proved in `Kopis`), so a restatement that drifted would fail to
    compile, and it contains a build-time check that fails if the trust base ever
    changes. Start here when reviewing. -/
@[default_target]
lean_lib «TopLevelTheorems»

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
