import TopLevelTheorems

/-!
# The trust base — what `kopis-rs`'s proofs assume

`TopLevelTheorems.lean` states what is proved. This file states what it is proved *on top of*,
and contains the build-time check that keeps the two honest: it recomputes the axiom footprint
of every top-level theorem and fails the build if it is not exactly the audited list below.
Read this file second.

## Why this is a separate file

The trust base is the one part of the audit that is **per backend**. The crate is extracted
twice (`../extract_rust_to_lean.sh`) — the portable code into `RustKopisSerial` and the AVX2
code into `RustKopisAvx2` — and the two make different assumptions: the AVX2 build additionally
assumes the semantics of every SIMD instruction it uses (`Kopis/Avx2/Intrinsics.lean`) and the
CPUID probe. The theorem *statements* do not differ in that way, so keeping them in one file
and the assumptions in another means an auditor reads the statements once and sees the whole
per-backend difference in one place, rather than diffing two near-identical files.

**Each backend is checked against its own list, and the lists are never merged.** A union check
would let a theorem about the portable code start depending on an AVX2 intrinsic axiom and
still pass — exactly the drift this file exists to catch. Adding a backend means adding a
`def`-pair below and one row to `backends`, not extending an existing list.

As of 2026-08-02 there is one row: nothing has been proved about the AVX2 extraction yet, so it
has no theorems whose footprint could be checked. See `AVX2_VERIFICATION_PLAN.md`.
-/

open Lean

/-! ## The portable (`RustKopisSerial`) backend

Everything in `TopLevelTheorems.lean` §3 rests on exactly the assumptions listed here. Beyond
Lean's own three axioms they fall into four groups.

**(a) The `turboshake` crate (5 assumptions).** `turboshake` is an external crates.io
dependency, so aeneas has no Lean model of its body and axiomatizes its stateful API.
`hasher_default_spec`, `hasher_update_spec`, `hasher_finalize_spec`, `reader_read136_spec` and
`reader_read168_spec` (in `Kopis/Properties/GenMatrix.lean`) say that this API implements
RFC 9861 — i.e. that absorbing bytes and then reading `n` bytes yields
`Spec.TurboSHAKE.turboSHAKE128/256`. This is the single largest assumption in the development,
and discharging it would mean verifying the `turboshake` crate itself. Note it is a
*functional* claim only: nothing about timing or memory behaviour.

**(b) The `subtle` crate (2 assumptions).** `conditional_select_array_u8_spec` and
`ct_eq_slice_u8_spec` (in `Kopis/Properties/SubtleModel.lean`) give the functional meaning of
`subtle`'s constant-time select and equality: select returns one of its two arguments according
to the choice bit, and `ct_eq` is byte equality. These are what the implicit-rejection branch of
decapsulation is proved against. Again functional only — that these operations are *actually*
constant-time is a claim about compiled machine code and is out of scope for this development
entirely.

**(c) Opaque arithmetic intrinsics (2 assumptions).** `U8.count_ones_spec` and
`U32.count_ones_spec` give the meaning of Rust's popcount intrinsics —
`RustKopisSerial.core.num.U8.count_ones` and `RustKopisSerial.core.num.U32.count_ones` are
intrinsics that aeneas leaves opaque, carrying no definition to unfold, so their meaning has to
be assumed.

The inverse NTT used to add a third entry here, `RustKopisSerial.core.num.I64.wrapping_neg`
(Rust's `i64::wrapping_neg`, used to negate a twiddle factor), with an assumed
`I64.wrapping_neg_spec` alongside it.  **Both are now gone.**  `src/arithmetic/ntt.rs` writes the
negation as `0i64.wrapping_sub(ZETAS[k] as i64)` instead, which extracts to
`IScalar.wrapping_sub` — a real `def` with real semantics (`@[simp]` value lemma
`(wrapping_sub x y).val = Int.bmod (x.val - y.val) (2 ^ 64)`) rather than an axiom. Identical
codegen, one fewer assumption. See the header note in `Kopis/Properties/NttInverse.lean`; do not
"simplify" that call back to `wrapping_neg`, which would silently re-add both entries to this
list.

**(d) Lean-side.** `propext`, `Classical.choice` and `Quot.sound` are the standard axioms of
Lean's logic — every Mathlib development uses them, and they are consistent.
`Aeneas.Std.core.fmt.Formatter` is an opaque type standing in for Rust's formatting machinery,
which no proof reasons about. The `RustKopisSerial.*` entries are the opaque types and functions
aeneas emits for the extern crates named in (a) and (b) — they carry no logical content of their
own.

One entry deserves singling out: `Spec.testBit_byte_of_bools._native.native_decide.ax` comes
from a `native_decide` in `Spec/Defs.lean:380`, which discharges a small finite bit-manipulation
fact by *compiled evaluation* rather than kernel reduction. That means trusting the Lean
compiler and runtime for that one step, which is a strictly larger trust base than the kernel
alone. It is a 2⁸-case check about byte bit-extraction, not a cryptographic claim, but it is a
real (if small) hole and could be closed by replacing `native_decide` with `decide`.

**`sorryAx` is NOT in the list.** There are no `sorry`s left anywhere in the dependency closure
of the top-level theorems — the NTT-multiplication hole `ntt_spec` is discharged
(`Kopis/Properties/NttBridge.lean`: `ntt_mul_spec` / `ntt_mul_transpose_spec`, on top of the
transform-network proofs in `NttForward`/`NttInverse`, the pointwise and inverse pipeline in
`NttMul`, and the pure-mathematical CRT/convolution layer in `NttMath`). Because the check below
demands an exact match, `sorryAx` is treated like any other unaudited assumption and *fails* the
build if one ever reappears. Do not re-add an exemption for it. -/

def serialAudited : List String :=
  ["Aeneas.Std.core.fmt.Formatter",
   "Classical.choice",
   "Kopis.Properties.U32.count_ones_spec",
   "Kopis.Properties.U8.count_ones_spec",
   "Kopis.Properties.conditional_select_array_u8_spec",
   "Kopis.Properties.ct_eq_slice_u8_spec",
   "Kopis.Properties.hasher_default_spec",
   "Kopis.Properties.hasher_finalize_spec",
   "Kopis.Properties.hasher_update_spec",
   "Kopis.Properties.reader_read136_spec",
   "Kopis.Properties.reader_read168_spec",
   "Quot.sound",
   "_private.Spec.Defs.0.Spec.testBit_byte_of_bools._native.native_decide.ax_1_1",
   "RustKopisSerial.Array.Insts.SubtleConditionallySelectable.conditional_select",
   "RustKopisSerial.Slice.Insts.SubtleConstantTimeEq.ct_eq",
   "RustKopisSerial.U8.Insts.SubtleConditionallySelectable.conditional_select",
   "RustKopisSerial.U8.Insts.SubtleConstantTimeEq.ct_eq",
   "RustKopisSerial.core.num.U32.count_ones",
   "RustKopisSerial.core.num.U8.count_ones",
   "RustKopisSerial.subtle.Choice",
   "RustKopisSerial.turboshake.TurboShake",
   "RustKopisSerial.turboshake.TurboShake.Insts.CoreDefaultDefault.default",
   "RustKopisSerial.turboshake.TurboShake.Insts.DigestExtendableOutputTurboShakeReader.finalize_xof",
   "RustKopisSerial.turboshake.TurboShake.Insts.DigestUpdate.update",
   "RustKopisSerial.turboshake.TurboShakeReader",
   "RustKopisSerial.turboshake.TurboShakeReader.Insts.DigestXofReader.read",
   "propext"]

/-- The theorems whose footprint `serialAudited` describes: **every** theorem in
`Kopis.TopLevel`, which the coverage check below enforces. That is the thirteen top-level
results of `TopLevelTheorems.lean` §3, plus the two lemmas that explain how to read them —
`triple_means_success` (§1), which is what licenses reading each `⦃ … ⦄` as "terminates without
panicking", and `arrayToBytes_is_identity` (§2), which is what says the translation layer is not
throwing information away. Those two are as load-bearing for an auditor as the theorems they
explain, and auditing them costs nothing: their axioms are a subset of the list above. -/
def serialTheorems : List Name :=
  [``Kopis.TopLevel.triple_means_success,
   ``Kopis.TopLevel.arrayToBytes_is_identity,
   ``Kopis.TopLevel.kopis512_keygen,
   ``Kopis.TopLevel.kopis768_keygen,
   ``Kopis.TopLevel.kopis1024_keygen,
   ``Kopis.TopLevel.kopis512_keygen_then_encapsulate,
   ``Kopis.TopLevel.kopis768_keygen_then_encapsulate,
   ``Kopis.TopLevel.kopis1024_keygen_then_encapsulate,
   ``Kopis.TopLevel.kopis512_keygen_then_decapsulate,
   ``Kopis.TopLevel.kopis768_keygen_then_decapsulate,
   ``Kopis.TopLevel.kopis1024_keygen_then_decapsulate,
   ``Kopis.TopLevel.pk_serialize_matches_translation,
   ``Kopis.TopLevel.kopis512_from_bytes_then_encapsulate,
   ``Kopis.TopLevel.kopis768_from_bytes_then_encapsulate,
   ``Kopis.TopLevel.kopis1024_from_bytes_then_encapsulate]

/-! ## The check

One row per backend: a label, the namespace its theorems live in, its audited assumptions, and
the theorems those are the assumptions *of*. Each row is checked on its own — see the header on
why the lists must not be merged.

Two things are checked, because the audited list and the theorem list can each rot:

* **Footprint.** The axioms actually reachable from the listed theorems are exactly the audited
  ones. A new assumption means the audit is incomplete; an unused one means it is stale.
* **Coverage.** Every theorem in the backend's namespace is audited. There is no exemption
  list, and there should not be one: a theorem sitting in the audit surface that nothing checks
  the assumptions of is exactly the situation this file exists to prevent, and "it only explains
  the notation" is not a reason — an explanatory lemma proved by `sorry` would mislead an
  auditor about how to read every theorem below it. Without this check, adding a theorem to
  `TopLevelTheorems.lean` and forgetting to list it here would leave it unaudited while the
  build stayed green, which is an easy mistake now that the statements and the assumptions live
  in different files. -/

open Lean in
run_cmd do
  let backends : List (String × Name × List String × List Name) :=
    [("RustKopisSerial", `Kopis.TopLevel, serialAudited, serialTheorems)]
  let env ← getEnv
  for (label, ns, audited, theorems) in backends do
    -- Footprint.
    let mut found : Array String := #[]
    for t in theorems do
      for a in (← Lean.collectAxioms t) do
        let s := a.toString
        if !found.contains s then found := found.push s
    let unexpected := found.filter (fun a => !audited.contains a)
    let unused := audited.filter (fun a => !found.contains a)
    unless unexpected.isEmpty && unused.isEmpty do
      throwError "TRUST BASE CHANGED for {label} — TrustBase.lean is out of date.\n\
        New assumptions not in the audited list: {unexpected.toList}\n\
        Audited assumptions no longer used: {unused}"
    -- Coverage.
    let mut unaudited : Array Name := #[]
    for (n, ci) in env.constants.toList do
      if ns.isPrefixOf n && !n.isInternal then
        if ci matches .thmInfo _ then
          unless theorems.contains n do
            unaudited := unaudited.push n
    unless unaudited.isEmpty do
      throwError "UNAUDITED THEOREM in {ns} — TrustBase.lean is out of date.\n\
        Nothing is checking what these theorems assume — add them to the backend's \
        theorem list: {unaudited.toList}"
