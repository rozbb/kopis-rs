import Lake
open Lake DSL

require aeneas from "../../aeneas/backends/lean"

package «kopis»

/-! ## Aeneas-extracted Rust code

    `ExtractedRustSerial.lean` is generated verbatim by `../extract_rust_to_lean.sh`
    (charon + aeneas, `-loops-to-rec`) from the `kopis-rs` crate. Never edit it
    by hand: re-run the extraction script instead. It is the *only* link
    between the Rust source and the proofs below. -/
lean_lib «ExtractedRustSerial» where
  -- charon/aeneas output, never hand-edited: its generated names carry `__`, which the mathlib
  -- style linter objects to.  Silencing it here is the only place the objection can be answered.
  leanOptions := #[⟨`linter.style.nameCheck, false⟩]

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
lean_lib «ExtractedRustAvx2» where
  -- charon/aeneas output, never hand-edited: its generated names carry `__`, which the mathlib
  -- style linter objects to.  Silencing it here is the only place the objection can be answered.
  leanOptions := #[⟨`linter.style.nameCheck, false⟩]

lean_lib «KopisAvx2» where
  roots := #[`Kopis.Avx2]

/-! ## The NEON backend

    `ExtractedRustNeon.lean` is the same crate extracted from an
    `--cfg kopis_backend="neon" -C target-feature=+sha3` build *for
    `aarch64-unknown-linux-gnu`*, in its own namespace: the NEON backend plus
    the dispatch blocks that reach it. Only `backend::neon::intrinsics` is
    extracted opaquely — unlike AVX2, the CPU probe is not, because on AArch64
    `available()` is a compile-time `true` — so what it contains for that one
    module is uninterpreted axioms; `Kopis/Neon/Intrinsics.lean` supplies their
    semantics and is the *only* place that does.

    Not in the default target, for the same reasons as the AVX2 extraction.
    Build this side with `make prove-kopis-neon`. -/
lean_lib «ExtractedRustNeon» where
  -- charon/aeneas output, never hand-edited: its generated names carry `__`, which the mathlib
  -- style linter objects to.  Silencing it here is the only place the objection can be answered.
  leanOptions := #[⟨`linter.style.nameCheck, false⟩]

lean_lib «KopisNeon» where
  roots := #[`Kopis.Neon]

/-! ## The generated twin proof stack (phase E)

    `Kopis/Avx2/Properties/*.lean` is `Kopis/Properties/*.lean` with the extraction and this
    stack's namespace renamed, produced by `scripts/gen_avx2_twins.py`. It is a *separate*
    library, and deliberately not part of `KopisAvx2`, so that a twin which does not yet compile
    — the ones touching the six runtime-dispatch points — cannot block the results that do.
    Build it with `lake build KopisAvx2Properties`; expect a cold build to take hours. -/
lean_lib «KopisAvx2Properties» where
  roots := #[`Kopis.Avx2.Properties]
  globs := #[.andSubmodules `Kopis.Avx2.Properties]

/-- The same, for NEON: `Kopis/Neon/Properties/*.lean` from `scripts/gen_neon_twins.py`. -/
lean_lib «KopisNeonProperties» where
  roots := #[`Kopis.Neon.Properties]
  globs := #[.andSubmodules `Kopis.Neon.Properties]

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

/-! ## The audit surface, AVX2

    The same restatement against the `RustKopisAvx2` extraction, generated from
    `TopLevelTheoremsSerial.lean` by `make generated`. Not a default target: it is built by
    `make prove-kopis-avx2` alongside `KopisAvx2`. -/
lean_lib «TopLevelTheoremsAvx2»

/-! ## The audit surface, NEON

    The same restatement against the `RustKopisNeon` extraction, generated from
    `TopLevelTheoremsSerial.lean` by `make generated`. Declared here so that the generator has a
    library to target and a reviewer sees the statements at the commit they review, but **it does
    not compile yet**: it imports `Kopis.Neon.Properties`, the twin proof stack, which does not
    exist. Nothing builds it — not the default target, and not `make prove-kopis-neon`. See
    `NEON_VERIFICATION_PLAN.md`. -/
lean_lib «TopLevelTheoremsNeon»

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

/-! ## The AVX2 intrinsic model, checked against silicon

    `SpecTests/Avx2/Run.lean` replays `../tests/intrinsics_vectors.jsonl` — recorded by running
    the real instructions on a real CPU (`src/backend/avx2/intrinsics_vectors.rs`) — through the
    computable models in `Kopis/Avx2/Model.lean`, which are proved equal to the axioms in
    `Kopis/Avx2/Intrinsics.lean`. It is the only thing in the tree that checks those axioms
    against hardware. Run it with `lake exe avx2Tests` (= `make test-avx2-model`). -/
lean_exe avx2Tests where
  root := `SpecTests.Avx2.Run

/-! ## The NEON intrinsic model, checked against silicon

    The same, for `Kopis/Neon/Model.lean`: `SpecTests/Neon/Run.lean` replays
    `../tests/neon_intrinsics_vectors.jsonl` — 50 176 vectors recorded on an Apple M1 by
    `src/backend/neon/intrinsics_vectors.rs` — through the models proved equal to the axioms in
    `Kopis/Neon/Intrinsics.lean`. Run it with `lake exe neonTests` (= `make test-neon-model`). -/
lean_exe neonTests where
  root := `SpecTests.Neon.Run
