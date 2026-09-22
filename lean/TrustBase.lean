import TopLevelTheoremsSerial
import TopLevelTheoremsAvx2
import TopLevelTheoremsNeon

/-!
# The trust base — what `kopis-rs`'s proofs assume

`TopLevelTheoremsSerial.lean` states what is proved. This file states what it is proved *on top of*,
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

As of 2026-09-22 there are three rows: every twin in `TopLevelTheoremsAvx2.lean` and
`TopLevelTheoremsNeon.lean` is discharged, so both SIMD trust bases are now *enforced* rather
than documented. Note that this file therefore imports all three audit surfaces, and so
`make prove-kopis-serial` — which builds `TrustBase` — pulls the AVX2 and NEON extractions in
with it. That is the price of checking the whole trust base in one place; run
`lake build Kopis TopLevelTheoremsSerial` if you want the serial proofs alone.
-/

open Lean

/-! ## The portable (`RustKopisSerial`) backend

Everything in `TopLevelTheoremsSerial.lean` §3 rests on exactly the assumptions listed here. Beyond
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
`U16.count_ones_spec` give the meaning of Rust's popcount intrinsics —
`RustKopisSerial.core.num.U8.count_ones` and `RustKopisSerial.core.num.U16.count_ones` are
intrinsics that aeneas leaves opaque, carrying no definition to unfold, so their meaning has to
be assumed.

The inverse NTT used to add a third entry here, `RustKopisSerial.core.num.I64.wrapping_neg`
(Rust's `i64::wrapping_neg`, used to negate a twiddle factor), with an assumed
`I64.wrapping_neg_spec` alongside it.  **Both are now gone.**  `src/arithmetic/ntt_arith.rs` writes the
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

`Spec/Defs.lean` used to discharge two small finite bit-manipulation facts with `native_decide`,
which put the Lean compiler and runtime in the trust base for those steps. They are now
`decide +kernel`, which reduces the same 2⁸ cases in the kernel in about a second and adds no
axiom, so **no compiled-evaluation assumption remains anywhere in the serial closure**. That is
a claim about *this* row only: the AVX2 row still carries four, from `bv_decide` — see (h).

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
   "Kopis.Properties.U16.count_ones_spec",
   "Kopis.Properties.U8.count_ones_spec",
   "Kopis.Properties.conditional_select_array_u8_spec",
   "Kopis.Properties.ct_eq_slice_u8_spec",
   "Kopis.Properties.hasher_default_spec",
   "Kopis.Properties.hasher_finalize_spec",
   "Kopis.Properties.hasher_update_spec",
   "Kopis.Properties.reader_read136_spec",
   "Kopis.Properties.reader_read168_spec",
   "Quot.sound",
   "RustKopisSerial.Array.Insts.SubtleConditionallySelectable.conditional_select",
   "RustKopisSerial.Slice.Insts.SubtleConstantTimeEq.ct_eq",
   "RustKopisSerial.U8.Insts.SubtleConditionallySelectable.conditional_select",
   "RustKopisSerial.U8.Insts.SubtleConstantTimeEq.ct_eq",
   "RustKopisSerial.core.num.U16.count_ones",
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
`Kopis.TopLevelSerial`, which the coverage check below enforces. That is the thirteen top-level
results of `TopLevelTheoremsSerial.lean` §3, plus the two lemmas that explain how to read them —
`triple_means_success` (§1), which is what licenses reading each `⦃ … ⦄` as "terminates without
panicking", and `arrayToBytes_is_identity` (§2), which is what says the translation layer is not
throwing information away. Those two are as load-bearing for an auditor as the theorems they
explain, and auditing them costs nothing: their axioms are a subset of the list above. -/
def serialTheorems : List Name :=
  [``Kopis.TopLevelSerial.triple_means_success,
   ``Kopis.TopLevelSerial.arrayToBytes_is_identity,
   ``Kopis.TopLevelSerial.kopis512_keygen,
   ``Kopis.TopLevelSerial.kopis768_keygen,
   ``Kopis.TopLevelSerial.kopis1024_keygen,
   ``Kopis.TopLevelSerial.kopis512_keygen_then_encapsulate,
   ``Kopis.TopLevelSerial.kopis768_keygen_then_encapsulate,
   ``Kopis.TopLevelSerial.kopis1024_keygen_then_encapsulate,
   ``Kopis.TopLevelSerial.kopis512_keygen_then_decapsulate,
   ``Kopis.TopLevelSerial.kopis768_keygen_then_decapsulate,
   ``Kopis.TopLevelSerial.kopis1024_keygen_then_decapsulate,
   ``Kopis.TopLevelSerial.pk_serialize_matches_translation,
   ``Kopis.TopLevelSerial.kopis512_from_bytes_then_encapsulate,
   ``Kopis.TopLevelSerial.kopis768_from_bytes_then_encapsulate,
   ``Kopis.TopLevelSerial.kopis1024_from_bytes_then_encapsulate]


/-! ## The AVX2 (`RustKopisAvx2`) backend

The same theorems, about the `--cfg kopis_backend="avx2"` extraction. Its assumptions are the
portable backend's, restated for the second extraction's opaque constants, **plus four groups
that exist only here**.

**(e) The SIMD instruction semantics (50 assumptions + 2 bit views + 2 opaque types).**
`Kopis/Avx2/Intrinsics.lean` gives one axiom per wrapper in `src/backend/avx2/intrinsics.rs` —
there are 50 of them, one per `pub(crate) fn` in that file — phrased over the two uninterpreted
bit views `bits : Vec256 → BitVec 256` and `bits' : Vec128 → BitVec 128`.
This is the largest addition and the file a reviewer must read. It is not proved, but it *is*
tested: `Kopis/Avx2/Model.lean` derives a computable model from each axiom, and
`make test-avx2-model` replays 47 858 vectors recorded from real silicon
(`src/backend/avx2/intrinsics_vectors.rs`) through those models. A wrong axiom is therefore caught
by `cargo test` on an AVX2 host, not silently believed.

**(f) The dispatch guard (1 assumption).** `available_ok` says the CPUID probe returns —
`∃ b, cpu.available = ok b`. It does not say *which* answer is given, and does not need to: every
dispatch point is proved on both branches. That is the whole of feature detection's contribution
to the trust base.

The *width* guard at the top of `plain_arith::RingElem::{serialize,deserialize}` costs nothing.
It was briefly an assumption: written `debug_assert!((1..=13).contains(&BITS_PER_ELEM))` it
extracted through an uninterpreted `RangeInclusive::contains` — charon does not lower it — and a
`massert` on an opaque `Bool` can neither be discharged nor case-split away, since `⦃ ⦄` forbids
failure. Spelling the same guard as `BITS_PER_ELEM >= 1 && BITS_PER_ELEM <= 13` extracts to two
ordinary `massert`s on `Usize` comparisons, both discharged from the width bounds the callers
already carry. Keep it spelled that way.

**(g) Popcount, twice more.** `CbdGeneric.U{8,16}.count_ones_spec` are the same assumption as (c),
for the copy of the portable sampler that `Kopis/Avx2/CbdGeneric.lean` carries; the extracted
`RustKopisAvx2.core.num.U{8,16}.count_ones` are different opaque constants from the serial ones,
so they are genuinely new for this backend.

**(h) Four `bv_decide` calls (4 assumptions).** The entries named
`…_native.bv_decide.ax_1_5`. One is minted by each `bv_decide` in the tree that a top-level
theorem reaches — `shl_sar_eq`, `sar_eq` and `and_low16` in `Kopis/Avx2/Reduce.lean` and
`join_prod` in `Kopis/Avx2/NttMulLane.lean` — and each has the form

    Std.Tactic.BVDecide.Reflect.verifyBVExpr <the goal, bitblasted> <the certificate> = true

**The SAT solver is not what is trusted.** `bv_decide` runs CaDiCaL, gets back an LRAT
refutation certificate, and checks that certificate with `verifyBVExpr` — a checker written *and
proved correct* in Lean. A lying solver is caught. What is trusted is the *execution* of that
checker: Lean runs it under the compiled evaluator rather than in the kernel and asserts the
resulting `Bool` as the axiom above. `Lean/Meta/Native.lean` in the toolchain says so in as many
words — "proofs by native evaluation (`native decide`, `bv_decide`) … involve a native
computation … and then assert the result of that computation as an axiom towards the logic".

So these four are in the same trust class as the `native_decide` that (d) records retiring: they
put the Lean compiler, its runtime and its GMP-backed `Nat`/`UInt` operations in the trust base,
scoped to four `Bool` evaluations. Getting a wrong answer out of one needs a compiler or runtime
bug, not a solver bug.

**Why they are still here.** In `leanprover/lean4:v4.31.0` `bv_decide` has no kernel-checking
mode — `BVDecideConfig` carries no such field, and `LratCert.toReflectionProof` has exactly the
one path. Nor can `decide +kernel` stand in as it does in (d): all four goals quantify over
`BitVec 32`, so there are 2³² cases, not 2⁸. Retiring one means replacing it with a
`getLsbD`-level proof, which is what was done to the NEON row's fifth such axiom
(`Kopis.Neon.sshr15_bits`, over `BitVec 16` — see the note on that theorem); that row now has
none.

Two things worth knowing when reviewing this group. The axiom names embed a per-declaration
counter, so adding or moving a `bv_decide` call renames one and the exact-match check below
fails **loudly** rather than letting a new one in unnoticed. And grepping for `Lean.ofReduceBool`
or `sorryAx` will not find these: `bv_decide` mints a fresh axiom per call rather than routing
through the shared `ofReduceBool`, which is exactly why they have to be listed here by name.

Everything else in the list below is the portable backend's list with `RustKopisSerial` renamed to
`RustKopisAvx2` and `Kopis.Properties` to `Kopis.Avx2.Properties` — the same turboshake, subtle and
Lean-side assumptions, reached through the generated twin proof stack. `sorryAx` is not in the
list, and the exact-match check below fails the build if it ever appears. -/

def avx2Audited : List String :=
  ["Aeneas.Std.core.fmt.Formatter",
   "Classical.choice",
   "Kopis.Avx2.CbdGeneric.U16.count_ones_spec",
   "Kopis.Avx2.CbdGeneric.U8.count_ones_spec",
   "Kopis.Avx2.Properties.U16.count_ones_spec",
   "Kopis.Avx2.Properties.U8.count_ones_spec",
   "Kopis.Avx2.Properties.conditional_select_array_u8_spec",
   "Kopis.Avx2.Properties.ct_eq_slice_u8_spec",
   "Kopis.Avx2.Properties.hasher_default_spec",
   "Kopis.Avx2.Properties.hasher_finalize_spec",
   "Kopis.Avx2.Properties.hasher_update_spec",
   "Kopis.Avx2.Properties.reader_read136_spec",
   "Kopis.Avx2.Properties.reader_read168_spec",
   "Kopis.Avx2.add_epi16_spec",
   "Kopis.Avx2.add_epi32_spec",
   "Kopis.Avx2.and_si256_spec",
   "Kopis.Avx2.available_ok",
   "Kopis.Avx2.bits",
   "Kopis.Avx2.bits'",
   "Kopis.Avx2.broadcastsi128_si256_spec",
   "Kopis.Avx2.castsi256_si128_spec",
   "Kopis.Avx2.cmpgt_epi32_spec",
   "Kopis.Avx2.cvtepu16_epi32_spec",
   "Kopis.Avx2.cvtsi32_si128_spec",
   "Kopis.Avx2.extracti128_si256_spec",
   "Kopis.Avx2.load_i16_spec",
   "Kopis.Avx2.load_i32_spec",
   "Kopis.Avx2.load_u16_spec",
   "Kopis.Avx2.load_u8_spec",
   "Kopis.Avx2.load_u8x16_spec",
   "Kopis.Avx2.mulhi_epi16_spec",
   "Kopis.Avx2.mullo_epi16_spec",
   "Kopis.Avx2.mullo_epi32_spec",
   "Kopis.Avx2.packs_epi32_spec",
   "Kopis.Avx2.packus_epi32_spec",
   "Kopis.Avx2.permute2x128_si256_spec",
   "Kopis.Avx2.permute4x64_epi64_spec",
   "Kopis.Avx2.set1_epi16_spec",
   "Kopis.Avx2.set1_epi32_spec",
   "Kopis.Avx2.setzero_si256_spec",
   "Kopis.Avx2.shuffle_epi8_spec",
   "Kopis.Avx2.slli_epi32_spec",
   "Kopis.Avx2.srai_epi16_spec",
   "Kopis.Avx2.srai_epi32_spec",
   "Kopis.Avx2.srl_epi16_spec",
   "Kopis.Avx2.srli_epi16_spec",
   "Kopis.Avx2.srlv_epi32_spec",
   "Kopis.Avx2.store_i16_spec",
   "Kopis.Avx2.store_i32_spec",
   "Kopis.Avx2.store_u16_spec",
   "Kopis.Avx2.sub_epi16_spec",
   "Kopis.Avx2.sub_epi32_spec",
   "Kopis.Avx2.unpackhi_epi16_spec",
   "Kopis.Avx2.unpackhi_epi32_spec",
   "Kopis.Avx2.unpackhi_epi64_spec",
   "Kopis.Avx2.unpacklo_epi16_spec",
   "Kopis.Avx2.unpacklo_epi32_spec",
   "Kopis.Avx2.unpacklo_epi64_spec",
   "Kopis.Avx2.andnot_si256_spec",
   "Kopis.Avx2.load_u8x32_spec",
   "Kopis.Avx2.or_si256_spec",
   "Kopis.Avx2.set1_epi64x_spec",
   "Kopis.Avx2.slli_epi64_spec",
   "Kopis.Avx2.srli_epi64_spec",
   "Kopis.Avx2.store_u8x32_spec",
   "Kopis.Avx2.xor_si256_spec",
   "Quot.sound",
   "RustKopisAvx2.Array.Insts.SubtleConditionallySelectable.conditional_select",
   "RustKopisAvx2.Slice.Insts.SubtleConstantTimeEq.ct_eq",
   "RustKopisAvx2.U8.Insts.SubtleConditionallySelectable.conditional_select",
   "RustKopisAvx2.U8.Insts.SubtleConstantTimeEq.ct_eq",
   "RustKopisAvx2.backend.avx2.cpu.available",
   "RustKopisAvx2.backend.avx2.intrinsics.Vec128",
   "RustKopisAvx2.backend.avx2.intrinsics.andnot_si256",
   "RustKopisAvx2.backend.avx2.intrinsics.load_u8x32",
   "RustKopisAvx2.backend.avx2.intrinsics.or_si256",
   "RustKopisAvx2.backend.avx2.intrinsics.set1_epi64x",
   "RustKopisAvx2.backend.avx2.intrinsics.slli_epi64",
   "RustKopisAvx2.backend.avx2.intrinsics.srli_epi64",
   "RustKopisAvx2.backend.avx2.intrinsics.store_u8x32",
   "RustKopisAvx2.backend.avx2.intrinsics.xor_si256",
   "RustKopisAvx2.backend.avx2.intrinsics.Vec256",
   "RustKopisAvx2.backend.avx2.intrinsics.add_epi16",
   "RustKopisAvx2.backend.avx2.intrinsics.add_epi32",
   "RustKopisAvx2.backend.avx2.intrinsics.and_si256",
   "RustKopisAvx2.backend.avx2.intrinsics.broadcastsi128_si256",
   "RustKopisAvx2.backend.avx2.intrinsics.castsi256_si128",
   "RustKopisAvx2.backend.avx2.intrinsics.cmpgt_epi32",
   "RustKopisAvx2.backend.avx2.intrinsics.cvtepu16_epi32",
   "RustKopisAvx2.backend.avx2.intrinsics.cvtsi32_si128",
   "RustKopisAvx2.backend.avx2.intrinsics.extracti128_si256",
   "RustKopisAvx2.backend.avx2.intrinsics.load_i16",
   "RustKopisAvx2.backend.avx2.intrinsics.load_i32",
   "RustKopisAvx2.backend.avx2.intrinsics.load_u16",
   "RustKopisAvx2.backend.avx2.intrinsics.load_u8",
   "RustKopisAvx2.backend.avx2.intrinsics.load_u8x16",
   "RustKopisAvx2.backend.avx2.intrinsics.mulhi_epi16",
   "RustKopisAvx2.backend.avx2.intrinsics.mullo_epi16",
   "RustKopisAvx2.backend.avx2.intrinsics.mullo_epi32",
   "RustKopisAvx2.backend.avx2.intrinsics.packs_epi32",
   "RustKopisAvx2.backend.avx2.intrinsics.packus_epi32",
   "RustKopisAvx2.backend.avx2.intrinsics.permute2x128_si256",
   "RustKopisAvx2.backend.avx2.intrinsics.permute4x64_epi64",
   "RustKopisAvx2.backend.avx2.intrinsics.set1_epi16",
   "RustKopisAvx2.backend.avx2.intrinsics.set1_epi32",
   "RustKopisAvx2.backend.avx2.intrinsics.setzero_si256",
   "RustKopisAvx2.backend.avx2.intrinsics.shuffle_epi8",
   "RustKopisAvx2.backend.avx2.intrinsics.slli_epi32",
   "RustKopisAvx2.backend.avx2.intrinsics.srai_epi16",
   "RustKopisAvx2.backend.avx2.intrinsics.srai_epi32",
   "RustKopisAvx2.backend.avx2.intrinsics.srl_epi16",
   "RustKopisAvx2.backend.avx2.intrinsics.srli_epi16",
   "RustKopisAvx2.backend.avx2.intrinsics.srlv_epi32",
   "RustKopisAvx2.backend.avx2.intrinsics.store_i16",
   "RustKopisAvx2.backend.avx2.intrinsics.store_i32",
   "RustKopisAvx2.backend.avx2.intrinsics.store_u16",
   "RustKopisAvx2.backend.avx2.intrinsics.sub_epi16",
   "RustKopisAvx2.backend.avx2.intrinsics.sub_epi32",
   "RustKopisAvx2.backend.avx2.intrinsics.unpackhi_epi16",
   "RustKopisAvx2.backend.avx2.intrinsics.unpackhi_epi32",
   "RustKopisAvx2.backend.avx2.intrinsics.unpackhi_epi64",
   "RustKopisAvx2.backend.avx2.intrinsics.unpacklo_epi16",
   "RustKopisAvx2.backend.avx2.intrinsics.unpacklo_epi32",
   "RustKopisAvx2.backend.avx2.intrinsics.unpacklo_epi64",
   "RustKopisAvx2.core.num.U16.count_ones",
   "RustKopisAvx2.core.num.U8.count_ones",
   "RustKopisAvx2.subtle.Choice",
   "RustKopisAvx2.turboshake.TurboShake",
   "RustKopisAvx2.turboshake.TurboShake.Insts.CoreDefaultDefault.default",
   "RustKopisAvx2.turboshake.TurboShake.Insts.DigestExtendableOutputTurboShakeReader.finalize_xof",
   "RustKopisAvx2.turboshake.TurboShake.Insts.DigestUpdate.update",
   "RustKopisAvx2.turboshake.TurboShakeReader",
   "RustKopisAvx2.turboshake.TurboShakeReader.Insts.DigestXofReader.read",
   "_private.Kopis.Avx2.NttMulLane.0.Kopis.Avx2.join_prod._native.bv_decide.ax_1_5",
   "_private.Kopis.Avx2.Reduce.0.Kopis.Avx2.and_low16._native.bv_decide.ax_1_5",
   "_private.Kopis.Avx2.Reduce.0.Kopis.Avx2.sar_eq._native.bv_decide.ax_1_5",
   "_private.Kopis.Avx2.Reduce.0.Kopis.Avx2.shl_sar_eq._native.bv_decide.ax_1_5",
   "propext"]

/-- The AVX2 twins of `serialTheorems`; the coverage check enforces that this is every theorem in
`Kopis.TopLevelAvx2`. -/
def avx2Theorems : List Name :=
  [``Kopis.TopLevelAvx2.triple_means_success,
   ``Kopis.TopLevelAvx2.arrayToBytes_is_identity,
   ``Kopis.TopLevelAvx2.kopis512_keygen,
   ``Kopis.TopLevelAvx2.kopis768_keygen,
   ``Kopis.TopLevelAvx2.kopis1024_keygen,
   ``Kopis.TopLevelAvx2.kopis512_keygen_then_encapsulate,
   ``Kopis.TopLevelAvx2.kopis768_keygen_then_encapsulate,
   ``Kopis.TopLevelAvx2.kopis1024_keygen_then_encapsulate,
   ``Kopis.TopLevelAvx2.kopis512_keygen_then_decapsulate,
   ``Kopis.TopLevelAvx2.kopis768_keygen_then_decapsulate,
   ``Kopis.TopLevelAvx2.kopis1024_keygen_then_decapsulate,
   ``Kopis.TopLevelAvx2.pk_serialize_matches_translation,
   ``Kopis.TopLevelAvx2.kopis512_from_bytes_then_encapsulate,
   ``Kopis.TopLevelAvx2.kopis768_from_bytes_then_encapsulate,
   ``Kopis.TopLevelAvx2.kopis1024_from_bytes_then_encapsulate]

/-! ## The NEON (`RustKopisNeon`) backend

Extracted from an `--cfg kopis_backend="neon" -C target-feature=+sha3` build cross-compiled for
AArch64, and proved against the same statements as the other two — `TopLevelTheoremsNeon.lean` is
generated from `TopLevelTheoremsSerial.lean` by `make generated`, so a statement that drifted
would fail to compile.

Two differences from the AVX2 row are worth stating, because together they are the whole of what
makes this row shorter.

* **No `available_ok`.** On AArch64 NEON is baseline and `cpu::available()` is
  `cfg!(target_arch = "aarch64")` — a compile-time `true`. aeneas extracts it as an ordinary
  definition (`ok true`) rather than opaquely, so every dispatch point resolves at elaboration
  time and nothing at all is assumed about feature detection. Both branches are still proved
  where the generated twins case-split on it; the `false` branch is the portable proof.
* **No `bv_decide` axiom.** Group (h) of the AVX2 row has no counterpart here, so nothing in
  this row's closure is believed on the word of the compiled evaluator. `sshr15_bits` in
  `Kopis/Neon/Reduce.lean` — arithmetic-shifting an `i16` right by 15 gives all-ones or zero
  according to the sign — was the one NEON goal discharged by `bv_decide`, and it is now proved
  bit by bit. It could go where the AVX2 four cannot for a mundane reason: it quantifies over
  `BitVec 16`, so the bitwise argument is four lines, while theirs are over `BitVec 32`.

**The intrinsic axioms are checked against silicon**, as the AVX2 ones are, and this row is no
longer the weaker of the two on that point. Both halves of the check exist and both have run:
`Kopis/Neon/Model.lean` gives every wrapper a computable model and proves the axiom pins the
result down to exactly it, `src/backend/neon/intrinsics_vectors.rs` records what the real
instructions do, and `SpecTests/Neon/Run.lean` (`make test-neon-model`) replays one through the
other. `tests/neon_intrinsics_vectors.jsonl` is committed — 50 176 vectors over all 46 wrappers,
≥ 1 000 each, recorded on an Apple M1 (`aarch64-apple-darwin`, FEAT_SHA3) — and a plain
`cargo test` on any such host re-checks it against that CPU, so drift is caught continuously
rather than when someone remembers to look.

What that is and is not: a differential test over ~1 000 inputs per operation, so it is strong
evidence and not a proof. What it rules out is the failure mode that matters — an axiom that is
simply *wrong* — and nothing else in the tree would catch that. The negative check was run: a
deliberately corrupted saturation bound in `satS16` is caught immediately, and corrupting a model
alone does not even compile, because `Kopis/Neon/Model.lean` proves each model equal to its axiom.

One assumption is NEON-only and has no AVX2 counterpart: `Usize.div_ceil_spec`. `usize::div_ceil`
is a compiler intrinsic whose body charon does not translate, so aeneas leaves it opaque; Kopis
calls it once, to turn a byte count into a word count, and the assumption is exactly `⌈x / y⌉`. -/

def neonAudited : List String :=
  ["Aeneas.Std.core.fmt.Formatter",
   "Classical.choice",
   "Kopis.Neon.CbdGeneric.U16.count_ones_spec",
   "Kopis.Neon.CbdGeneric.U8.count_ones_spec",
   "Kopis.Neon.I16.wrapping_neg_spec",
   "Kopis.Neon.Keccak.Usize.div_ceil_spec",
   "Kopis.Neon.Properties.U16.count_ones_spec",
   "Kopis.Neon.Properties.U8.count_ones_spec",
   "Kopis.Neon.Properties.conditional_select_array_u8_spec",
   "Kopis.Neon.Properties.ct_eq_slice_u8_spec",
   "Kopis.Neon.Properties.hasher_default_spec",
   "Kopis.Neon.Properties.hasher_finalize_spec",
   "Kopis.Neon.Properties.hasher_update_spec",
   "Kopis.Neon.Properties.reader_read136_spec",
   "Kopis.Neon.Properties.reader_read168_spec",
   "Kopis.Neon.add_16_spec",
   "Kopis.Neon.add_32_spec",
   "Kopis.Neon.and_spec",
   "Kopis.Neon.bcax_spec",
   "Kopis.Neon.bits",
   "Kopis.Neon.cmgt_s32_spec",
   "Kopis.Neon.cnt_u8_spec",
   "Kopis.Neon.dup_n_s16_spec",
   "Kopis.Neon.dup_n_s32_spec",
   "Kopis.Neon.dup_n_u16_spec",
   "Kopis.Neon.dup_n_u32_spec",
   "Kopis.Neon.dup_n_u64_spec",
   "Kopis.Neon.eor3_spec",
   "Kopis.Neon.eor_spec",
   "Kopis.Neon.load_i16_spec",
   "Kopis.Neon.load_i32_spec",
   "Kopis.Neon.load_u16_spec",
   "Kopis.Neon.load_u8x16_spec",
   "Kopis.Neon.mla_32_spec",
   "Kopis.Neon.mul_16_spec",
   "Kopis.Neon.rax1_spec",
   "Kopis.Neon.set_u64x2_spec",
   "Kopis.Neon.shrn16_pair_s32_spec",
   "Kopis.Neon.shsub_s16_spec",
   "Kopis.Neon.smull_high_s16_spec",
   "Kopis.Neon.smull_low_s16_spec",
   "Kopis.Neon.sqdmulh_s16_spec",
   "Kopis.Neon.sshr_n_s16_spec",
   "Kopis.Neon.store_i16_spec",
   "Kopis.Neon.store_i32_spec",
   "Kopis.Neon.store_u16_spec",
   "Kopis.Neon.store_u8x16_spec",
   "Kopis.Neon.sub_16_spec",
   "Kopis.Neon.sub_32_spec",
   "Kopis.Neon.sxtl_high_s16_spec",
   "Kopis.Neon.sxtl_low_s16_spec",
   "Kopis.Neon.tbl1_u8_spec",
   "Kopis.Neon.trn1_16_spec",
   "Kopis.Neon.trn1_32_spec",
   "Kopis.Neon.trn1_64_spec",
   "Kopis.Neon.trn2_16_spec",
   "Kopis.Neon.trn2_32_spec",
   "Kopis.Neon.trn2_64_spec",
   "Kopis.Neon.ushl_u16_spec",
   "Kopis.Neon.ushl_u32_spec",
   "Kopis.Neon.xar_spec",
   "Kopis.Neon.xtn_pair_32_spec",
   "Quot.sound",
   "RustKopisNeon.Array.Insts.SubtleConditionallySelectable.conditional_select",
   "RustKopisNeon.Slice.Insts.SubtleConstantTimeEq.ct_eq",
   "RustKopisNeon.U8.Insts.SubtleConditionallySelectable.conditional_select",
   "RustKopisNeon.U8.Insts.SubtleConstantTimeEq.ct_eq",
   "RustKopisNeon.backend.neon.intrinsics.Vec128",
   "RustKopisNeon.backend.neon.intrinsics.add_16",
   "RustKopisNeon.backend.neon.intrinsics.add_32",
   "RustKopisNeon.backend.neon.intrinsics.and",
   "RustKopisNeon.backend.neon.intrinsics.bcax",
   "RustKopisNeon.backend.neon.intrinsics.cmgt_s32",
   "RustKopisNeon.backend.neon.intrinsics.cnt_u8",
   "RustKopisNeon.backend.neon.intrinsics.dup_n_s16",
   "RustKopisNeon.backend.neon.intrinsics.dup_n_s32",
   "RustKopisNeon.backend.neon.intrinsics.dup_n_u16",
   "RustKopisNeon.backend.neon.intrinsics.dup_n_u32",
   "RustKopisNeon.backend.neon.intrinsics.dup_n_u64",
   "RustKopisNeon.backend.neon.intrinsics.eor",
   "RustKopisNeon.backend.neon.intrinsics.eor3",
   "RustKopisNeon.backend.neon.intrinsics.load_i16",
   "RustKopisNeon.backend.neon.intrinsics.load_i32",
   "RustKopisNeon.backend.neon.intrinsics.load_u16",
   "RustKopisNeon.backend.neon.intrinsics.load_u8x16",
   "RustKopisNeon.backend.neon.intrinsics.mla_32",
   "RustKopisNeon.backend.neon.intrinsics.mul_16",
   "RustKopisNeon.backend.neon.intrinsics.rax1",
   "RustKopisNeon.backend.neon.intrinsics.set_u64x2",
   "RustKopisNeon.backend.neon.intrinsics.shrn16_pair_s32",
   "RustKopisNeon.backend.neon.intrinsics.shsub_s16",
   "RustKopisNeon.backend.neon.intrinsics.smull_high_s16",
   "RustKopisNeon.backend.neon.intrinsics.smull_low_s16",
   "RustKopisNeon.backend.neon.intrinsics.sqdmulh_s16",
   "RustKopisNeon.backend.neon.intrinsics.sshr_n_s16",
   "RustKopisNeon.backend.neon.intrinsics.store_i16",
   "RustKopisNeon.backend.neon.intrinsics.store_i32",
   "RustKopisNeon.backend.neon.intrinsics.store_u16",
   "RustKopisNeon.backend.neon.intrinsics.store_u8x16",
   "RustKopisNeon.backend.neon.intrinsics.sub_16",
   "RustKopisNeon.backend.neon.intrinsics.sub_32",
   "RustKopisNeon.backend.neon.intrinsics.sxtl_high_s16",
   "RustKopisNeon.backend.neon.intrinsics.sxtl_low_s16",
   "RustKopisNeon.backend.neon.intrinsics.tbl1_u8",
   "RustKopisNeon.backend.neon.intrinsics.trn1_16",
   "RustKopisNeon.backend.neon.intrinsics.trn1_32",
   "RustKopisNeon.backend.neon.intrinsics.trn1_64",
   "RustKopisNeon.backend.neon.intrinsics.trn2_16",
   "RustKopisNeon.backend.neon.intrinsics.trn2_32",
   "RustKopisNeon.backend.neon.intrinsics.trn2_64",
   "RustKopisNeon.backend.neon.intrinsics.ushl_u16",
   "RustKopisNeon.backend.neon.intrinsics.ushl_u32",
   "RustKopisNeon.backend.neon.intrinsics.xar",
   "RustKopisNeon.backend.neon.intrinsics.xtn_pair_32",
   "RustKopisNeon.core.num.I16.wrapping_neg",
   "RustKopisNeon.core.num.U16.count_ones",
   "RustKopisNeon.core.num.U8.count_ones",
   "RustKopisNeon.core.num.Usize.div_ceil",
   "RustKopisNeon.subtle.Choice",
   "RustKopisNeon.turboshake.TurboShake",
   "RustKopisNeon.turboshake.TurboShake.Insts.CoreDefaultDefault.default",
   "RustKopisNeon.turboshake.TurboShake.Insts.DigestExtendableOutputTurboShakeReader.finalize_xof",
   "RustKopisNeon.turboshake.TurboShake.Insts.DigestUpdate.update",
   "RustKopisNeon.turboshake.TurboShakeReader",
   "RustKopisNeon.turboshake.TurboShakeReader.Insts.DigestXofReader.read",
   "propext"]

/-- The NEON twins of `serialTheorems`; the coverage check enforces that this is every theorem in
`Kopis.TopLevelNeon`. -/
def neonTheorems : List Name :=
  [``Kopis.TopLevelNeon.triple_means_success,
   ``Kopis.TopLevelNeon.arrayToBytes_is_identity,
   ``Kopis.TopLevelNeon.kopis512_keygen,
   ``Kopis.TopLevelNeon.kopis768_keygen,
   ``Kopis.TopLevelNeon.kopis1024_keygen,
   ``Kopis.TopLevelNeon.kopis512_keygen_then_encapsulate,
   ``Kopis.TopLevelNeon.kopis768_keygen_then_encapsulate,
   ``Kopis.TopLevelNeon.kopis1024_keygen_then_encapsulate,
   ``Kopis.TopLevelNeon.kopis512_keygen_then_decapsulate,
   ``Kopis.TopLevelNeon.kopis768_keygen_then_decapsulate,
   ``Kopis.TopLevelNeon.kopis1024_keygen_then_decapsulate,
   ``Kopis.TopLevelNeon.pk_serialize_matches_translation,
   ``Kopis.TopLevelNeon.kopis512_from_bytes_then_encapsulate,
   ``Kopis.TopLevelNeon.kopis768_from_bytes_then_encapsulate,
   ``Kopis.TopLevelNeon.kopis1024_from_bytes_then_encapsulate]

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
  `TopLevelTheoremsSerial.lean` and forgetting to list it here would leave it unaudited while the
  build stayed green, which is an easy mistake now that the statements and the assumptions live
  in different files. -/

open Lean in
run_cmd do
  let backends : List (String × Name × List String × List Name) :=
    [("RustKopisSerial", `Kopis.TopLevelSerial, serialAudited, serialTheorems),
     ("RustKopisAvx2", `Kopis.TopLevelAvx2, avx2Audited, avx2Theorems),
     ("RustKopisNeon", `Kopis.TopLevelNeon, neonAudited, neonTheorems)]
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
