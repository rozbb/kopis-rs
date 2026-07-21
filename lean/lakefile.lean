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

/-! ## Spec test vectors

    `SpecTests` runs the audited specification against the Kopis test vectors
    and KAT files under `SpecTests/Kopis/vectors/`. Not part of the default
    `lake build` closure; run it via the `kopisTests` executable below
    (`lake exe kopisTests` = `make test-kopis-spec`). The runner reads the
    `.jsonl` vectors at run time relative to the current directory, so invoke
    it from this directory. -/
lean_lib «SpecTests» where
  globs := #[.andSubmodules `SpecTests]

lean_exe kopisTests where
  root := `SpecTests.Kopis.Run
