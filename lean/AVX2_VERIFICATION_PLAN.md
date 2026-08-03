# Verifying the AVX2 backend — plan of work

> Rewritten 2026-08-02 as an execution plan. Written to be read cold: everything needed to pick
> this up with no prior context is here or is one command away. Companion to
> `NTT_REFACTOR_STATUS.md` (the serial NTT proof, complete) and `TrustBase.lean` (the assumptions).

## 0. Where things stand

The scaffolding is done and committed; **no AVX2 correspondence proof exists yet**. Concretely:

* `../extract_rust_to_lean.sh` extracts the crate twice, with no errors:
  `ExtractedRustSerial.lean` (namespace `RustKopisSerial`, 4684 lines) and
  `ExtractedRustAvx2.lean` (namespace `RustKopisAvx2`, 6947 lines).
* `src/backend/avx2/intrinsics.rs` wraps all 45 SIMD operations behind `Vec256`/`Vec128`
  newtypes. `charon --opaque` keeps that module and `backend::avx2::cpu` opaque, so aeneas emits
  them as uninterpreted constants; the rest of the backend translates normally. Nothing outside
  `intrinsics.rs` contains `unsafe` or a raw pointer.
* `Kopis/Avx2/Intrinsics.lean` gives those constants meaning: one axiom per operation, over
  `bits : Vec256 → BitVec 256` with lane views derived from it. **This is the added trust base
  and the file a reviewer must read.** It is assumed, not proved, and not checked against
  silicon — Phase A below is about that.
* `make prove-kopis` builds both backends; `make prove-kopis-serial` is the machine-checked
  serial proof; `make prove-kopis-avx2` builds the AVX2 extraction and the intrinsic axioms and
  proves nothing (the target name is aspirational).
* `TopLevelTheoremsAvx2.lean` is generated from `TopLevelTheoremsSerial.lean` by `make generated`
  and is **not** in the build graph — it cannot compile until the proofs below exist.

Re-verify all of that with `make prove-kopis` from `lean/`. If it is not green, stop and fix that
first; nothing below is meaningful on a red tree.

## 1. The measurement that shapes everything

Compare the two extractions declaration by declaration (re-run this if you doubt it):

```
declarations: serial=304  avx2=460  shared-name=304
  identical body : 298
  differing body : 6
  only in avx2   : 156      (ntt 67, intrinsics 47, ser 15, sample 6, crt ~19, cpu 1)
```

The six whose bodies differ are exactly the runtime-dispatch points:

```
arithmetic.ntt.NttElem.from_uniform          arithmetic.ring_arith.RingElem.deserialize
arithmetic.ntt.NttElem.from_secret           sample.gen_secret_from_seed_loop
arithmetic.ntt.pointwise_mul_acc
arithmetic.ntt.reduce_invntt_to_ring_elem
```

Three consequences that drive the plan:

**(a) Every constant is new, even where the code is identical.**
`RustKopisAvx2.pke.PkePublicKey.serialize` is a different Lean constant from the serial one with
a byte-identical body. So the AVX2 top-level theorems need a parallel proof stack — but 298/304
of it should transfer by renaming the namespace, because the goals are identical modulo names.
That is mechanical work (Phase E), not mathematics.

**(b) The dispatch points extract as an honest case split.** For example:

```lean
let b1 ← backend.avx2.cpu.available
if b1 then (let a ← backend.avx2.ser.deserialize bytes bits_per_elem; ok a)
      else (…the portable code, unchanged…)
```

`backend.avx2.cpu.available : Result Bool` is an axiom with **no** semantic assumption attached,
and none is needed: prove the postcondition on *both* branches and it holds whatever CPUID says.
The only thing that must be assumed about it is that it does not fail or diverge —

```lean
axiom available_ok : ∃ b, RustKopisAvx2.backend.avx2.cpu.available = ok b
```

— which is far weaker than "it correctly detects AVX2", and is the whole of the CPU probe's
contribution to the trust base. (An earlier draft of this document said `available()` should be
recorded as an assumption about feature detection. That was wrong; this is better.)

**(c) The real mathematical work is small and identifiable**: `ser` (15 declarations), `sample`
(6), and `ntt` (67). `ser` and `sample` claim *bit-identical* output to the portable routines, so
their theorems are equalities between two functions in the same namespace. `ntt` does not — it
computes over two 16-bit primes and only the endpoints agree — so it needs a genuine end-to-end
theorem through the CRT. That asymmetry is why the order below is ser → sample → ntt.

## 2. Operating notes

**Build.** From `lean/`: `make prove-kopis-serial` (≈1788 jobs), `make prove-kopis-avx2` (≈1697),
`make prove-kopis` for both. Incremental builds after touching one proof file are seconds; a cold
build is minutes. To check a scratch file without adding it to a library:
`lake env lean Scratch.lean`.

**Memory.** The host is 4 cores / 4 GB. `LEAN_NUM_THREADS` is 8 in the Makefile; if a build dies
with exit 137 (OOM) or starts swap-thrashing, re-run with
`make prove-kopis LEAN_NUM_THREADS=2`. Keep new proof files small and separately importable
rather than growing one big file — heavy WP-monadic proofs co-elaborated in one module have OOMed
this box before.

**Git.** Commit after every green milestone; never commit a red tree, and never commit a `sorry`.
`TrustBase.lean` fails the build if any serial theorem's axiom footprint changes, so a stray
`sorry` in the serial stack breaks `prove-kopis-serial` loudly — that is intended, do not weaken
it. Use `sorry` freely in scratch files that are in no library.

**Generated files.** `ExtractedRust*.lean` are charon/aeneas output and `TopLevelTheoremsAvx2.lean`
is `make generated` output. Never hand-edit any of them; change the source and regenerate.

**Skills.** `lean4:prove` / `lean4:autoprove` for guided and autonomous proving,
`lean4:proof-repair` for compiler-guided repair, `lean4:golf` once something compiles. The
lean-lsp MCP tools (`lean_goal`, `lean_multi_attempt`, `lean_local_search`, `lean_hammer_premise`)
are far cheaper than rebuilding to see a goal state.

**Aeneas traps found the hard way.** Each was isolated with a ~10-line file through
`charon rustc --preset=aeneas` + `aeneas`; whole-crate error spans point somewhere misleading, so
reach for a minimal repro early.

1. **A function returning a `&'static` reference cannot be translated** — `Unreachable` at
   `interp/Interp.ml:609`, reported at the first *field read* through the reference, not at the
   function. Reading a static inside a function is fine. This is why `crt::prime::<SECOND>()`
   became six value-returning accessors.
2. **A `const`/`static` initializer block containing a loop cannot be translated** — `Internal
   error, please file an issue`. The same loop inside a `const fn` the initializer calls is fine.
3. **A reference field in a struct reached by reference** kills the run with
   `Invalid_argument "option is None"` from `translate_global_eval`.

`#[target_feature]`, `unsafe`, const generics, `#[repr(align)]`, statics holding large arrays,
`copy_from_slice` and `iter_mut().enumerate()` all extract fine — though the last produces
iterator-state-machine Lean that is unpleasant to prove about, so prefer indexed loops.

---

## Phase A — make the intrinsic model testable, and test it

**Why first.** `Kopis/Avx2/Intrinsics.lean` is 45 assumptions about what Intel silicon does,
written by reading the SDM. Nothing checks them. Every AVX2 theorem is worthless if one is wrong,
and the failure is silent. This is the highest-value work in the plan and it is self-contained.

**Do it additively — do not rewrite the axioms.** Their content has been reviewed; keep one axiom
per operation in its current form. Add, in a new file `Kopis/Avx2/Model.lean`:

1. A **computable** model per operation, e.g. `def addEpi16 (a b : BitVec 256) : BitVec 256 := …`
   built from `BitVec.extractLsb'` / `++` so that it evaluates under `#eval`.
2. A theorem per operation deriving the model from the axiom — for the lane-wise ones,
   `∀ i < 16, laneOf 16 (addEpi16 (bits a) (bits b)) i = lane16 a i + lane16 b i`, i.e. the model
   satisfies exactly what the axiom asserts. These are proofs, not assumptions.

Then differential-test the models against real hardware:

3. A Rust test (`tests/intrinsics_vectors.rs`, or a `#[cfg(test)]` module inside
   `src/backend/avx2/intrinsics.rs` since the wrappers are `pub(crate)`) that evaluates each of
   the 45 wrappers on N random inputs (N ≥ 1000, fixed seed so it is reproducible) and writes
   `tests/intrinsics_vectors.jsonl`: one record per call, inputs and output as hex bytes.
4. A Lean runner under `SpecTests/Avx2/`, following the existing `SpecTests/Kopis/Run.lean`
   pattern (it already reads `.jsonl` from `../tests/`), evaluating each model on the same inputs
   and comparing. Wire it as a `lean_exe` alongside `kopisTests`.

**Acceptance:** `make prove-kopis` green; the runner passes on ≥1000 vectors per operation; and a
deliberately corrupted model (flip a bound in `satS`, say) makes it fail — record that negative
check in the session log, do not commit the corruption.

**Expected trouble.** `permute2x128_si256` and `permute4x64_epi64` take their immediate as a
runtime argument after extraction, so cover the immediates the backend actually uses (`0x20`,
`0x31`, `0xD8`, `0b11_01_10_00`) rather than all 256. `shuffle_epi8`'s control bytes should
include the zeroing high-bit case, which the backend never exercises but the axiom claims.

## Phase B — lane algebra

The downstream proofs will drown without rewriting machinery. In `Kopis/Avx2/Lanes.lean`:

* `laneOf` simp lemmas: lane of `++`, lane of `extractLsb'`, lane at a shifted index.
* The bridge both ways: 16 lanes determine the 256-bit word
  (`(∀ i < 16, laneOf 16 x i = laneOf 16 y i) → x = y`) and its 8-, 32- and 64-bit analogues.
  This is what lets a lane-wise axiom be used where a whole-register fact is needed and vice
  versa — it is the thing libcrux `admit()`s and we said we would prove.
* A `@[progress]`-shaped restatement of each intrinsic spec, so `progress` drives the extracted
  monadic code without manual `obtain`.

**Acceptance:** every lemma proved, no `sorry`; plus a smoke test that `mont_mul`'s extracted form
has the expected lane value, closed by `progress` + `simp` with no manual bit surgery.

## Phase C — `ser::deserialize` is bit-identical to the portable unpacker

**Target.**

```lean
theorem avx2_deserialize_eq (bytes : Slice U8) (bits : Usize) (h : …) :
  RustKopisAvx2.backend.avx2.ser.deserialize bytes bits
    = RustKopisAvx2.ser.deserialize_generic bytes bits
```

Both sides are in the *same* namespace, so this needs no serial proof and no spec — a
self-contained equality between two functions, and the cleanest first real target.

**Shape of the argument.** A group of 8 coefficients of `w` bits occupies exactly `w` bytes;
coefficient `k` starts at byte `⌊kw/8⌋`, bit `kw mod 8`. The vector path broadcasts the group's 16
bytes to both halves, `vpshufb`s each lane's 4-byte window into place, `vpsrlvd`s by the per-lane
bit offset, masks, then `vpackusdw` + `vpermq` to reassemble. So: the byte selected by the shuffle
control for lane `k` is the byte the scalar code reads, and the shift and mask extract the same
bit field. Do one lane, then quantify.

**Watch for:** the tail. The last `⌊15/bits⌋` groups are read from a zero-padded 32-byte scratch
buffer because a 16-byte load would run past the end; the proof must cover head and tail paths,
and the `copy_from_slice` bound (`bytes.len() - tail_start`) is where an off-by-one would hide.
`PLANS` is a const table built by a `const fn`, so its 14 entries are concrete — `decide` on a
single width may be cheaper than reasoning about `plan`, but prefer `decide` over `native_decide`
(the latter widens the trust base, and `TrustBase.lean` already flags the one that exists).

**Acceptance:** proved for all `bits ∈ 1..=13`, no `sorry`. Composing it with the spec comes later,
via Phase E's twin of the serial `deserialize_generic` proof.

## Phase D — `sample::cbd` is bit-identical to the portable sampler

**Target.** `RustKopisAvx2.backend.avx2.sample.cbd MU buf = RustKopisAvx2.sample.cbd MU buf` for
`MU ∈ {6, 8, 10}`.

Builds directly on Phase C: `cbd` starts by calling `ser::deserialize buf MU`, then per 16-bit
lane computes `popcount(low half) − popcount(high half)` via a nibble `vpshufb` lookup plus bit 4.
`popcount_small` is valid only for values below 32 — derive that side condition from the parameter
bound (`MU/2 ≤ 6`) rather than assuming it.

**Acceptance:** proved for the three `MU` values the crate instantiates, no `sorry`.

## Phase E — the parallel proof stack and the six dispatch theorems

Only start this with a few hours in hand: it touches ~60 files and is mechanical, so it is a poor
use of an unattended night compared with C and D, and a fine use of a morning.

1. **Restructure.** `Kopis/Properties/` → `Kopis/Serial/Properties/`, namespace
   `Kopis.Properties` → `Kopis.Serial.Properties`, aggregator `Kopis.lean` → `Kopis/Serial.lean`.
   Update `TrustBase.lean`'s eleven `Kopis.Properties.…_spec` strings and its theorem list, and
   the lakefile. This makes the aggregator backend-named, so the generated audit copy's
   `import Kopis` becomes `import Kopis.Serial` and substitutes cleanly — see the note in
   `Makefile`, since that import is currently the one thing the three `sed` rules cannot reach.
2. **Generate the twins.** Extend `make generated` to produce `Kopis/Avx2/Properties/*` from
   `Kopis/Serial/Properties/*` with the same substitutions. The 298 identical-bodied declarations
   should transfer; the generated files that fail to compile are exactly those touching the six
   dispatch points, and that failure list *is* the work list. Do not fight it — let the build tell
   you.
3. **The six dispatch theorems.** Each is `if available then <avx2> else <serial>`: discharge the
   serial branch with the generated twin, the AVX2 branch with Phases C/D (for `deserialize` and
   `gen_secret_from_seed_loop`) or Phase F (for the four NTT entry points). State `available_ok`
   as in §1(b) and put it in the AVX2 row of `TrustBase.lean`.
4. **Wire it up.** `lean_lib «TopLevelTheoremsAvx2»`, add it to `prove-kopis-avx2`, and add the
   second row to `backends` in `TrustBase.lean` with its own audited list (which will include the
   45 intrinsic axioms and `available_ok`). The lists must stay separate — a union check would let
   a serial theorem depend on an intrinsic axiom unnoticed.

**Acceptance:** `make prove-kopis` green with `TopLevelTheoremsAvx2` in the graph and
`TrustBase.lean` reporting two rows. Probe the gate as before: dropping an audited axiom, or a
theorem from the AVX2 row, must fail the build.

## Phase F — the NTT

The hard one, and it will not be finished in a night. Four separable pieces, in dependency order:

1. **`mont_mul` / `barrett` lane specs.** These mirror `mont_reduce_spec` / `barrett_reduce_spec`
   already proved in `Kopis/Properties/NttReduce*.lean` — reuse those statements, re-proved at
   16-bit lane width over the Phase B algebra.
2. **`transpose16` is a permutation.** After it, `v[k]` lane `m` holds coefficient `16m + k`, and
   applying it twice is the identity. No prior art anywhere — libcrux does not model the
   unpack/permute family — so this is ours to do from the SDM. The Rust test
   `transpose16_permutes_as_documented` states exactly the property to prove.
3. **The growth bound.** `crt.rs:52-60` records that the crude 0.75q-per-level budget predicts
   3.5q > 3.05q for AVX2's four-level run (levels 4–7), and that safety rests instead on interval
   propagation with the actual per-butterfly ψ values, bounding the worst lane below 30 700 of
   32 767. **That argument exists only as prose.** Mechanizing it is the highest-value single
   theorem in this phase: it is what breaks silently if anyone reorders a reduction or regenerates
   a ψ table, and no test would catch it.
4. **The end-to-end CRT theorem.** `split_and_transform → pointwise_mul_acc → reduce_block →
   invntt_block` computes the same ring product as `arithmetic::ntt`, discharged through the
   existing `NttMath.lean` (`nconvR`, `Ev_nconv`, `cst_leaf_pow`). The NTT-domain values are
   *different integers* from the serial ones — only the endpoints agree — so there is no
   stage-by-stage correspondence to lean on, unlike everything in Phases C–E.

## 3. Priorities if the night is short

A (testable model) → B (lane algebra) → C (`deserialize`) → D (`cbd`). If only A lands, the night
was still worth it: it is the difference between 45 assumptions and 45 *tested* assumptions, and
it is the one piece whose absence undermines everything else.

Do **not** start Phase F speculatively. Do **not** restructure directories (E1) unless C and D are
done and committed.

## 4. Prior art and licensing

Lane-level specs for the arithmetic operations follow libcrux's
`crates/utils/intrinsics/src/avx2_extract.rs`; the bit-level ones follow
`fstar-helpers/fstar-bitvec/BitVec.Intrinsics.fsti`. The arithmetic core is fully covered there;
the transpose network (`unpacklo/unpackhi_epi16`, `permute2x128_si256`, `permute4x64_epi64`,
`cvtepu16_epi32`) is not covered at all. Do not copy F* source into Lean — `bit_vec n` there is
`i:nat{i<n} -> bit` with a `Tactics.*` normalization stack that has no Lean counterpart; the
*specs* are reusable ideas, the code is not. libcrux `admit()`s its bit↔lane bridge and ships
`mm256_set1_epi16_no_semantics`; we prove ours (Phase B).

libcrux is Apache-2.0 with an MIT file also shipped; kopis is MIT/Apache-2.0. The Rust wrappers
were authored fresh rather than vendored, and the specs are cited as prior art here.

## 5. Session log

*(Append: date, what was attempted, what landed, what blocked, where to resume.)*

**2026-08-02.** Scaffolding complete and committed: both extractions clean, `intrinsics.rs`
wrappers, `Kopis/Avx2/Intrinsics.lean` axioms, `TrustBase.lean` split out of the audit file with
per-backend footprint and coverage checks, Makefile restructured into
`prove-kopis{,-serial,-avx2}` with a generate-and-verify rule for `TopLevelTheoremsAvx2.lean`. No
correspondence proof attempted yet. Resume at Phase A.

**2026-08-02 (later).** Phases A and B done, Phase C substantially done. No `sorry` anywhere;
`make prove-kopis` green throughout.

*Phase A — landed.* `Kopis/Avx2/Model.lean` gives a computable `BitVec` model per intrinsic and
proves, from each axiom, `∃ c, f a b = ok c ∧ bits c = Model.f (bits a) (bits b)` — so each axiom
pins its result down to exactly the model, and the model runs.
`src/backend/avx2/intrinsics_vectors.rs` records 47 858 vectors (≥ 1000 per wrapper, all 45)
from real silicon into `tests/intrinsics_vectors.jsonl`; `SpecTests/Avx2/Run.lean`
(`make test-avx2-model`, ~2 s) replays them through the models and refuses to report success if
an operation is missing or thin. A plain `cargo test` on an AVX2 host now re-checks the
committed file against that CPU, so drift is caught continuously.

Two findings worth keeping. (i) The first negative check — flipping `satS`'s upper bound from
32767 to 32766 — *passed*, because the two agree after truncation; that is a genuinely
equivalent change, not a hole. (ii) The second — 32767 to 32000 — initially also passed, because
uniform random 32-bit lanes essentially never land near the 16-bit saturation boundary. The
generator now draws a third of its inputs from a boundary-hugging distribution, and with that the
corruption is caught immediately. **A differential test over uniform inputs does not exercise
saturation at all**; if anyone adds an operation here, add the matching structured inputs.

*Phase B — landed.* `Kopis/Avx2/Lanes.lean`: `laneOf_concatLanes` (build a word from its lanes),
`eq_of_laneOf_eq` and the `Vec256`/`Vec128` corollaries (the bit↔lane bridge libcrux `admit()`s),
`laneOf_split`, `laneOf_laneOf`, `laneOf_and`. The `@[progress]`-shaped restatements in the
original plan turned out not to be needed: this repo's proofs use `let*`/`step`, not `progress`,
and the `∃ c, … = ok c ∧ …` axioms feed `obtain`+`rw` directly.

*Phase C — landed in full.* `avx2_deserialize_eq` (`Kopis/Avx2/SerEq.lean`):

```
backend::avx2::ser::deserialize bytes bits = ser::deserialize_generic bytes bits
```

for every width `1 ≤ bits ≤ 13` and every correctly-sized input. Its axiom footprint is exactly
the eleven intrinsics the vector path uses — the ones Phase A tested against silicon — plus
`propext`/`Classical.choice`/`Quot.sound`. Proved in dependency order:

* `Kopis/Bits/Stream.lean` — the bit stream, lifted out of `Kopis/Properties/Serialize.lean` so
  both backends are proved against the same object. New: `streamNat_of_byteWindow`, the four-byte
  window lemma the vector path needs.
* `Kopis/Avx2/SerPlan.lean` — `PLANS_spec`: for every width 1..=13 the table holds
  `⌊k·w/8⌋ + b` and `(k·w) % 8`. Three loop specs; `w` stays symbolic.
* `Kopis/Avx2/SerLane.lean` — `lane_chain_value`: `vpshufb`+`vpsrlvd`+`vpand` puts coefficient
  `8·group + k` in lane `k`. And `pack_permute_value`: `vpackusdw` + `vpermq 0b11_01_10_00`
  reassembles two groups into sixteen coefficients in order.
* `Kopis/Avx2/SerTail.lean` — head and tail loads made to say the same thing.
  `head_load_in_bounds` is the tight one.
* `Kopis/Avx2/Ser.lean` — `inner_loop_spec` (a pair's two groups) and `outer_loop_spec` (sixteen
  pairs, each store covering `out[16·pair .. +16]`).

* `Kopis/Avx2/Ser.lean` — `inner_loop_spec` (a pair's two groups), `outer_loop_spec` (sixteen
  pairs), `tail_buffer_bytes`, and `deserialize_streamNat`, the whole routine including its
  constant setup.
* `Kopis/Avx2/SerGeneric.lean` — the AVX2-namespace twin of the generic decoder's loop specs,
  and `generic_streamNat`.

**A correction to §C of this plan.** "Both sides are in the *same* namespace, so this needs no
serial proof" is almost right but not quite: it needs no serial *theorem*, but
`RustKopisAvx2.ser.deserialize_generic` is a different Lean constant from the serial one, so it
needs that theorem's **twin**. `SerGeneric.lean` is that twin — `DeserializeCm.lean`'s and
`Serialize.lean`'s loop specs with `RustKopisSerial → RustKopisAvx2` and *nothing else changed*.
It compiled first try, which is direct evidence for §E's premise that the 298 identical-bodied
declarations transfer mechanically. When E automates the generation, this file should become one
of its outputs rather than a hand copy.

*Phase D — landed in full.* `avx2_cbd_eq` (`Kopis/Avx2/CbdEq.lean`):

```
backend::avx2::sample::cbd MU buf = sample::cbd MU buf out
```

for `MU ∈ {6, 8, 10}`. `Kopis/Avx2/Cbd.lean` proves `cbd_streamNat`: for
`MU = 2·half` with `1 ≤ half ≤ 5`,

```
backend::avx2::sample::cbd MU buf  →  out[k] = cbdU16 buf half (MU·k)
```

i.e. coefficient `k` is `popcount(low half of its field) − popcount(high half)` as a wrapping
`u16`. Along the way: `popcount_small_spec` (one `vpshufb` over the nibble table plus bit 4 is
the popcount of any lane below 32 — the high byte of each lane is zero, so its lookup yields
`nibblePop 0 = 0` and does not disturb the 16-bit sum, which is the step `sample.rs`'s comment
asserts), and `shift_right_dynamic_spec`. The `< 32` bound comes from `half ≤ 5`, as intended.

`cbdX` moved to `Kopis/Bits/Stream.lean` alongside `streamNat`, so both backends are proved
against one definition; `testBit_streamNat` is what lets a popcount of the *deserializer's
output* be read as a popcount of the *stream*, which is what makes the AVX2 side cheap.

The portable side is ported in `Kopis/Avx2/CbdGeneric.lean` (1672 lines: `GenSecret.lean`'s
helper block plus `GenSecretLoops.lean` up to its spec bridge, one substitution, nothing else).
It is genuinely three correspondence proofs and not one — the portable `sample::cbd` is not a
generic routine but three hand-written specialised branches (`MU = 8` nibble, `MU = 10` five-byte
group, `MU = 6` three-byte group) plus a fallback — but they were already proved on the serial
side, so the port carries them over.

The one thing worth recording about D: the two sides are characterised in *different types*.
`cbd_streamNat` gives a raw `u16`; `cbd_spec` gives a value in `ZMod (2¹³)` and `cbd_bd` a
magnitude bound. A `u16` that is small-signed with bound `b` is determined by its residue mod
`2¹³` once `2b < 2¹³`, and `b = MU/2 ≤ 5`, so the two pin down the same word
(`u16_eq_of_smallSigned`). Any later phase needing a raw equality against a `ZMod`-valued serial
spec can reuse that bridge.

**Two new assumptions.** `CbdGeneric.U8.count_ones_spec` and `CbdGeneric.U32.count_ones_spec`:
`RustKopisAvx2.core.num.{U8,U32}.count_ones` are different opaque constants from the serial ones,
so these are genuinely new for this backend and belong in the AVX2 row of `TrustBase.lean`
exactly as their twins are in the serial row.

*Phase E — the generator exists and was trialled; the stack is not built.*
`scripts/gen_avx2_twins.py` implements E2 without needing E1's restructure: it writes
`Kopis/Avx2/Properties/*.lean` from `Kopis/Properties/*.lean` under three substitutions
(`RustKopisSerial`, `ExtractedRustSerial`, and `Kopis.Properties → Kopis.Avx2.Properties`),
plus an `import Kopis.Bits.Stream` and a re-open of the shared bit-stream vocabulary, which is
deliberately *not* duplicated. Renaming this stack's own namespace in the copy is what makes the
E1 restructure unnecessary — the serial files are untouched, and the aggregator
`Kopis/Avx2/Properties.lean` is generated too, so a generated `TopLevelTheoremsAvx2` can import
it. (The Makefile note about `import Kopis` needing "a rule of its own" is the alternative that
was taken.)

Trial run: all 59 modules generate, and the build got far enough to show two kinds of failure.
One was a generator bug (a file with no bit-stream use got the `open` without the `import`), now
fixed. The other is the real thing: `Kopis/Avx2/Properties/Serialize.lean`'s `from_bytes_spec`
fails at the `WP.spec_bind` for `RingElem::deserialize` — one of the six dispatch points, exactly
as §E2 predicts. **The generated output is not checked in**, because a red tree must not be
committed; regenerate with `python3 scripts/gen_avx2_twins.py` from `lean/`.

**Budget warning for whoever picks this up.** A cold build of the twin stack is *hours*, not
minutes — the AVX2 extraction is 6947 lines against the serial 4684, so every twin elaborates
more slowly than its original, and there are 59 of them. Start it early, let it run, and collect
the failure list; do not expect to iterate on it interactively.

*Phase F — not started, but scouted.* Two notes for whoever takes it:

* **F1's prerequisite is built.** `barrett` and `mont_mul` are three lines each, but their
  *value* specs need a bridge from signed `BitVec 16` arithmetic to `ℤ`, because the serial
  `mont_reduce_spec` / `barrett_reduce_spec` are stated over `I32`/`I64` with `Int.bmod`.
  `Kopis/Avx2/LaneArith.lean` is that bridge: `mulhi_lane_toInt` (lane `i` of `vpmulhw` is
  `⌊aᵢ·bᵢ / 2¹⁶⌋` — the step Montgomery reduction rests on, and the one where a sign-extension
  error would be invisible at the bit level), plus `mullo`, `add`, `sub` and `srai` restated on
  lanes over ℤ. With those, an F1 lane spec is ordinary integer arithmetic in the same shape as
  `Kopis/Properties/NttReduce*.lean`. F3 and F4 will want the same bridge.
* **F2's shape, from reading the code.** `inlane_transpose8` claims: for each 128-bit half `h`
  and `r, c < 8`, `lane16 v'[r] (8h+c) = lane16 v[c] (8h+r)`. The three passes are word, dword
  and qword interleaves, and `v'[2i] = unpacklo_epi64(b_i, b_{i+4})`,
  `v'[2i+1] = unpackhi_epi64(b_i, b_{i+4})`. The 32- and 64-bit unpack axioms need restating on
  16-bit lanes; one lemma does both — from `laneOf (w·q) x i = laneOf (w·q) y j` conclude
  `∀ t < q, laneOf w x (q·i+t) = laneOf w y (q·j+t)`, which follows from `laneOf_laneOf` in
  `Lanes.lean`. `transpose16` then wraps it with the `vperm2i128 0x20/0x31` pass that swaps the
  off-diagonal 8×8 blocks.

*Phase E3 — dispatch point 1 is written but not yet verified.* `scripts/gen_avx2_twins.py`
gained declarative **patches**: a theorem whose serial proof unfolds a dispatch point cannot
transfer, so its proof is replaced by an entry in `PATCHES` rather than hand-edited in the
generated file. A patch that stops applying makes the generator fail loudly; a hand edit would
be silently overwritten or silently stale. The first patch is `from_bytes_spec`.

Two things that patch taught us, both recorded because they will recur:

* **The AVX2 dispatch adds a second opaque guard.** The Rust is
  `if (1..=13).contains(&bits) && avx2_available()`, and *`contains` is opaque too* — charon does
  not lower it, so aeneas emits it as an axiom, and it appears nowhere in the serial extraction.
  So the dispatch needs `rangeInclusive_contains_ok` alongside `available_ok`. Both are
  termination-only assumptions ("it returns"), not behavioural ones; all three reachable paths
  are proved to compute the same bit stream.
* **Elaborating the dispatch inside `Serialize.lean` is very slow, and three separate fixes did
  not help.** The unpatched file takes 106 s; with the patch it did not finish in fifty minutes.
  Ruled out by experiment: `step*` (replaced with the by-hand assertion discharge that
  `DeserializeCm.lean` uses — still >30 min), and `grind` inside the statements' `getElem` proof
  terms (replaced with `getElem!` throughout so no proof term is re-elaborated — still >30 min).
  The remaining suspect is the `simp only [core.array.TryFromSharedArraySlice.try_from,
  dif_pos hb, reduceIte, …]` applied to the *whole* nested dispatch body, three times over
  (once per reachable path).

  That recommendation was then tested and **found wanting**, which is the more useful result:
  extracting the `deserialize_13` block on its own into `Kopis/Avx2/Ser13.lean`
  (`ExtractedRustAvx2` + `Kopis/Bits/Stream.lean`, no `Spec` import) did *not* build in seconds
  either — it was still going after ten minutes, for a block the twin had previously got through
  in under 106 s. So the cost is not the dispatch proof and not the file it lives in: **the
  width-13 block is expensive in the AVX2 environment specifically.**

  The "raised heartbeats are hiding a failing tactic" hypothesis was then tested and **also
  refuted**: the same block with the *default* heartbeat limit ran for eight minutes without
  reporting an error. So nothing is failing — the block is simply slow to elaborate here, and
  the remaining variable is the environment it elaborates in.

  **One concrete lead, and a design smell worth fixing either way.** `Kopis/Avx2/Lanes.lean`
  marks eight lemmas `@[simp]` — `getLsbD_laneOf` and the seven `laneOf_ofLanes*`. Those join
  the *global* simp set, so once the twin gains `import Kopis.Avx2.Ser` (which the dispatch
  patch needs) every `simp` call in `Serialize.lean`'s heavy width-13 proofs has eight more
  lemmas to try. Making them `@[local simp]`, or dropping the attribute and passing them
  explicitly at their (few) use sites, is worth doing on its own account and is the cheapest
  thing left to try. Note it does *not* explain the standalone `Ser13.lean` measurement, which
  never imported them — so if that does not help, the next experiment is to time the *serial*
  block in the same isolated shape, which separates "AVX2 environment" from "isolated from
  `Spec.Kopis.Spec`" as the cause.

  The patch as written is **unverified**; treat it as a draft of the argument, not as working
  code. `Kopis/Avx2/Ser13.lean` was not kept — regenerate it from `Serialize.lean`'s
  `deserialize_13` block if you want to retry that route.

*Where to resume.* Verify the `from_bytes_spec` patch compiles (`lake build
Kopis.Avx2.Properties.Serialize`), then work outwards: `Serialize.lean` is near the dependency
root, so until it is green the other 58 twins cannot even be attempted. Then E1/E2/E4 and the
remaining five dispatch points, then F. E is better understood now than when this plan was
written: `SerGeneric.lean` and `CbdGeneric.lean` are two hand-made instances of exactly the twin
generation E1/E2 describe, and both compiled under the `RustKopisSerial → RustKopisAvx2`
substitution with no other change — 1672 lines in one case, first try. That is strong evidence
the mechanical transfer works; when E automates it, those two files should become its outputs
rather than hand copies. E's remaining work: the restructure (E1), the generator (E2), the six
dispatch theorems (E3) — of which the `deserialize` and `gen_secret_from_seed_loop` points are
now discharged by `avx2_deserialize_eq` and `avx2_cbd_eq` — and wiring `TopLevelTheoremsAvx2`
into the build with its own `TrustBase` row (E4).

**2026-08-02 (still later).** Phase E is as done as it can be without the NTT, and phase F2's
mathematics is done. No `sorry` anywhere; `make prove-kopis` green throughout.

*Phase E — 46 of 59 twins green.* The generator (`scripts/gen_avx2_twins.py`) works as designed:
declarative patches keyed on the serial proof text, failing loudly when an anchor stops matching.
Dispatch points 1 (`RingElem::deserialize`, at widths 13, 10 and generic — reached from three
different twins) and 2 (`gen_secret_from_seed_loop`) are discharged, by
`Kopis/Avx2/SerDispatch.lean` and `Kopis/Avx2/CbdDispatch.lean`.

Two mechanisms were worth adding. (i) A dispatch argument does **not** belong in the twin that
needs it: taking the width-13 spec as a *hypothesis* in `SerDispatch.lean` took `Serialize.lean`
from "over thirty minutes, cause unknown" to seconds, and the same shape then served two more
call sites for free. (ii) `GenSecretTop.lean` needed a *post-transform*, not a patch: the AVX2
guard makes `step*` split where the serial file has one goal, so the generated proof collapses
the vector branch and then runs the unchanged serial argument under `all_goals`. Patches edit
text; post-transforms restructure it. Both fail loudly.

*The remaining 13 twins are all NTT, and they cannot be transferred at all.* This is the finding
of the session, and it is worth stating precisely because it changes what phase F has to prove.
`arithmetic::ntt::pointwise_mul_acc`'s portable branch computes `acc[i] += (lhs[i] as i64) *
(rhs[i] as i64)` — a full 32×32→64 product. Its AVX2 branch reads the *same arrays* as 512 `i16`
and 512 `i32` and computes `acc32[t] += lhs16[t] * rhs16[t]`, with no carry between the two
halves of each `i64`. Those are different functions of the same bits: writing `a = a₁·2¹⁶ + a₀`,
the scalar path keeps the cross terms `a₁b₀ + a₀b₁` and the vector path drops them.

They are not meant to agree. The AVX2 build carries each coefficient as *two* 16-bit residues
(mod `q₁ = 7681` and mod `q₂ = 10753`) packed into one `i32`, where the portable build carries a
single residue mod `p = 50330113`; `NttElem::from_uniform` chooses the representation and
`reduce_invntt_to_ring_elem` collapses it, and both dispatch on the same `avx2_available()`, so a
run is internally consistent. But it means the twin specs — which are stated about `aZ`/`accZ`,
the integer *value* of a lane — are false on the AVX2 branch, and no amount of generator work
will transfer them. Plan §F4 anticipated exactly this ("the NTT-domain values are *different
integers* from the serial ones — only the endpoints agree"); what is new is knowing that it bites
at `pointwise_mul_acc`, not only at the transform, and that it therefore blocks all 13 twins
downstream of `NttMul.lean` — which is to say the entire KEM top level.

So phase F4 is not optional polish: it is the only route to `TopLevelTheoremsAvx2`. The four NTT
dispatch points have to be discharged end-to-end, against `Spec.Kopis`, not stage by stage.

*Phase F2 — the mathematics landed.* `Kopis/Avx2/Transpose.lean` proves `transpose16` is the
16×16 transpose: vector `k` lane `m` of the result is vector `m` lane `k` of the input, hence
coefficient `16m + k`, hence its own inverse. Three parts: the six interleaves read at 16-bit
granularity (`vpunpckldq` is specified on 32-bit lanes, so a lane has to be read back as two
16-bit ones), `inlane_transpose8`'s three levels, and the `vperm2i128` pass.
`Kopis/Avx2/TransposeSpec.lean` connects the extracted `inlane_transpose8` to that model by
unrolling — the loops have literal bounds, so there is no invariant to design, and numeral
indices let the bookkeeping discharge by `omega`.

*Where to resume.* Items 1 and 2 below landed in this session; 3 is what is left.

1. ~~`transpose16`~~ — done, end to end. `transpose16_coeff` (the `i16` at `16m + k` moves to
   `16k + m`) and `transpose16_involutive`. Both loops got invariants rather than unrolling, and
   everything is stated at *block* granularity via `blockVec`, so a `store_i16` replaces one
   16-lane block and leaves the other fifteen alone; composing the pointwise store spec sixteen
   times instead leaves sixteen nested range conditions at every index. That block-granularity
   trick is the one to reuse for the rest of the NTT.
2. ~~`pointwise_mul_acc`~~ — done. `Kopis/Avx2/NttMulLane.lean` proves
   `i32View r t = i32View acc t + prod32 lhs rhs t` for every `t < 512`: the first *true*
   statement about an NTT dispatch point, and the concrete form of the representation gap above.
3. ~~`barrett` lane spec~~ — done, so F1 is complete. The bound really is tight: bounding each
   rounding step on its own puts the result about `q/2048` outside `±q/2`, and the term that
   fills the gap is `q·(x·M mod 2¹⁶)/2²⁷`. Work from the exact identity, not from interval
   arithmetic over the steps. Then:
   * **F3, the growth bound.** Still the highest-value single theorem: `crt.rs:52-60` records
     that the crude 0.75q-per-level budget *fails* for AVX2's four-level run, and that safety
     rests on interval propagation with the actual ψ values. That argument exists only as prose.
   * **F4, the CRT endpoint theorem.** `q₁q₂ = 82593793 > p = 50330113`, so the residue pair
     determines the coefficient; `NttElem::from_uniform` builds the pair and
     `reduce_invntt_to_ring_elem` collapses it. Everything between them — `split_and_transform`,
     `ntt_block`, `invntt_block` — only has to be shown to compute *some* NTT of the pair, with
     `transpose16` (done) explaining why the four innermost levels may run vertically.

Do not try to make the 13 NTT twins compile. They are false as stated for this backend; the work
is F, and when F lands the AVX2 top-level theorems should be proved directly rather than
generated.

**2026-08-02 (F3/F4 session).** F1 completed, F3's argument mechanised and composed onto the
extracted code for three of its four critical levels, F4's endpoint theorem done. No `sorry`;
`make prove-kopis` green.

*F1 — complete.* `barrett_lane_spec` joins `mont_mul_lane_spec`. The centred bound `2|r| < q` is
tight and the crude argument does not reach it: bounding each rounding step on its own leaves the
result about `q/2048` outside `±q/2`, and the term that closes the gap is `q·(x·M mod 2¹⁶)/2²⁷`.
Work from the exact identity `2²⁷r = x(2²⁷−qM) + q·a + q·2¹⁶(b−2¹⁰)`, not from interval
arithmetic over the steps.

*F3 — the argument, and most of the binding to code.* Two findings.

(i) **The sharp Montgomery bound is the whole thing.** `mont_mul_lane_spec` originally gave
`|c| < q`, which is what the crude budget uses; four `+q` steps from `q/2` reach `4.5q`. The sharp
form `2¹⁶|c| ≤ |a||z| + 2¹⁵q` makes a level's growth *proportional to the bound already reached*,
so levels compound instead of adding a constant. That single change is what makes the schedule
fit — see `mont_mul_lane_spec`'s fourth conjunct.

(ii) **The bound does not need the ψ values, only that the tables are centred.** With `|ψ| ≤ q/2`
the recurrence `B ↦ B + ⌈(B·q/2 + 2¹⁵q)/2¹⁶⌉` from `B = (q−1)/2` gives, for `q₂ = 10753`,
`5376 → 11194 → 17489 → 24301 → 31671` — inside 32767 with 1096 to spare. `crt.rs` says the
argument rests on "the actual per-butterfly ψ values"; it does not have to. Centredness is a much
more robust hypothesis than the table contents, and `crude_budget_overflows` confirms the
comment's warning is exact: four flat `+0.75q₂` steps reach 37632 and overflow.

Landed: `VecBnd`/`BlockBnd`/`BlockBndAt`/`Split`, value-level load/store, `ct_butterfly_bnd`,
`barrett_block_bnd` (Barrett has no precondition, so re-centring needs no bound going in), the
four vertical levels (`ntt_block_loop1/2/3/4`), the horizontal group loop
(`ntt_block_loop0_loop0_loop0`), `growth_q1`/`growth_q2`, and `vertical_levels_bnd_q2`, which
composes three of the four levels of the critical run against the extracted code.

*F3 — done, for both primes.* `ntt_block_bnd_q1` and `ntt_block_bnd_q2`: the extracted
`ntt_block` leaves every coefficient centred at `|a| ≤ (q−1)/2`, which is what its Rust doc claims
and what the next stage assumes. The chain for `q₂`, the binding prime, is
`3840/5376 → … → 31671 → 5376`, with the worst lane 31671 of 32767 reached inside the four-level
run the crude budget cannot cover. `ntt_block_loop0` is unrolled rather than given an invariant,
because the bound differs at every level and the Barrett resets it after level 2.

*The ψ-table hypotheses are discharged* — `Kopis/Avx2/Tables.lean`, so
`ntt_block_centred_q1` / `ntt_block_centred_q2` are unconditional. Nothing had to be evaluated:
`zetas_qinv` and `lane_tbl` are `partial_fixpoint` loops, so the kernel cannot reduce them at
all. Instead the file rests on two observations.

* **Centredness is a property of `ZETAS_Q1`/`ZETAS_Q2` alone.** Every derived table is built by
  *copying* their entries — `lane_tbl` reads `zetas[base + h·hs + m·ms]` and writes it through —
  so the check is one `decide` per prime over a 256-entry literal array (about 1.5 s each with
  `unseal` and `maxRecDepth 20000`; they are `irreducible`, so the `unseal` is required).
* **The Montgomery pairing needs one numeric fact per prime**, `q⁻¹·q ≡ 1 (mod 2¹⁶)`, plus the
  structural fact that every `zq` entry is `wrapping_mul` of the matching `z` entry by `q⁻¹`.
  Then `zq·q ≡ z·q⁻¹·q ≡ z` whatever `z` is — `mont_pair`.

The loop specifications that carry those two facts are `zetas_qinv_loop_spec` and
`lane_tbl_loop0_loop0_spec`. The second one is where the ζ *index* has to be shown in range:
`base + h·h_stride + m·m_stride < 256` for the four concrete stride tuples. Two notes for anyone
extending it. The `hcast` steps leave `i_post : i = UScalar.hcast …` — an equation between
*values*, not `.val`s — so `scalar_tac` cannot see `i.val = h.val`; `hcast_usize_isize_val` and
`hcast_isize_usize_val` bridge that. And the stride products are nonlinear for `omega`, so the
strides are hypothesised as literal disjunctions (`h_stride = 0 ∨ 1`, `m_stride ∈ {1,2,4,8}`) and
`rcases`d before the arithmetic — after which everything is linear. Two tactical notes for whoever picks this up. `step*` uses the
theorem's own induction hypothesis for the recursive call, so an explicit `apply` of the lemma
being proved is *wrong* and produces a confusing "could not unify" against a goal that is already
the invariant — see `ntt_block_loop0_loop0_loop0_bnd`, where the fix was to delete the `apply`.
And `step*` names its intermediates inaccessibly when the extraction reuses a binder, so
`by_cases` on the loop condition *before* `step*` keeps the goal single and the names usable.

*F4 — the endpoint, which is the part that is not the transform.* `Kopis/Avx2/Crt.lean`:
`garner_congr` (the backend's Garner step lands in the right class mod `q₁q₂`), `crt_unique` (a
class has one member in the centred range), `exactness_bound_fits`. Together: a coefficient inside
`crt.rs`'s exactness bound is determined by its two residues. So everything the vector code does
between the endpoints only has to *preserve the two residues* — which is the shape the rest of F4
should take, and is much weaker than reproducing the portable intermediates.

*F4's algebra is complete; what is left is the code.* `Kopis/Avx2/NttAlgebra.lean` is
`NttMath.lean`'s Cooley-Tukey / Gentleman-Sande development with the modulus abstracted away: a
commutative ring, a twiddle table, and one hypothesis, `ζ k ² = cst ζ k`. From that alone come
`State_ct` (one CT layer refines the CRT invariant), `State_gs` (one GS layer merges it back, up
to the factor 2 the layer leaves behind), `cst_leaf_pow`, `Ev_nconv`, and `State_leaf_mul` — the
statement that once the leaf state is reached, multiplying lanewise multiplies the polynomials.

`Kopis/Avx2/NttZeta.lean` discharges the hypotheses for both AVX2 tables. The entries are in
Montgomery form, so on the raw arrays the checks are `ZETAS[2j]² ≡ ZETAS[j]·R`,
`ZETAS[2j+1]² ≡ −ZETAS[j]·R`, `ZETAS[1]² ≡ −R²` and `Z_a·Z_b ≡ −R²` for the GS pairing, with
`R = 2¹⁶ mod q`: three `decide`s per prime over the literal arrays, everything else algebra that
holds for any table passing them. The results are `State_ct_q1/q2`, `State_gs_q1/q2`,
`State_leaf_mul_q1/q2`.

`Kopis/Avx2/NttValue.lean` supplies the other half of the bridge: `ct_butterfly_val` says the
AVX2 butterfly computes `(lo + ψ·hi, lo − ψ·hi)` mod `q` with `ψ` the *plain* twiddle — the
stored entry times `2⁻¹⁶`, since `mont_mul` divides by the radix — which is exactly the shape
`State_ct` asks for. Its hypotheses are `ct_butterfly_bnd`'s, and for the same reason: they make
the wrapping `vpaddw`/`vpsubw` exact, so the integer identity survives the cast into `ZMod q`.

`Kopis/Avx2/NttWalk.lean` sets up the coordinates the walk needs: `posZ` (by array position,
which is the coefficient index before the transpose), `tposZ` (by coefficient index afterwards),
and `transpose16_tpos` connecting them. That is what makes the vertical levels readable as
ordinary Cooley-Tukey layers — array position `16j + m` is coefficient `16m + j`, so butterflying
vectors `(j, j+8)` at every lane is exactly pairing offsets `j` and `j+8` inside each of the
sixteen blocks, and the ψ the code takes from lane `m` of `FWD8` is `ζ(16+m)`, the twiddle block
`m` wants.

## F4's code walk: what landed this session

1. **`lane_tbl`'s value payload** — done. `TblAt` rides along on the existing walk, and
   `ld_tbl_psiOk` now hands back the ζ *index* each lane holds.
2. **The four vertical levels** — done. `ntt_block_loop1/2/3/4_walk` (plus the two inner group
   walks) each carry bounds *and* values: after them the coefficient view is exactly one
   Cooley-Tukey layer applied to the input view, with the ψ index matching `State_ct`.
3. **The horizontal group walk and its inner loop** — done,
   `ntt_block_loop0_loop0_loop0_walk` and `ntt_block_loop0_loop0_walk`. Carrying the layer's ζ
   index as `k + 1 = nb + start/(2·half)` put a division by the *variable* `half` in front of
   `omega`; carrying the group index `b` explicitly instead (`start = b·(2·half)`) removes
   division from the horizontal half entirely and makes the recursion `b ↦ b+1`, `k ↦ k+1`
   linear. Do the same anywhere else a group index is needed.
4. **`barrett_block_val`** — done. The re-centring passes change representatives, not classes, so
   the growth schedule's two Barrett passes sit inside the transform without disturbing its
   invariant.

One genuine bug was found and fixed along the way: the innermost horizontal walk's invariant
claimed the value at positions in *earlier* groups was still `a0`, when those have already been
transformed. Its predicate now includes `c / 16 < start`. Check the analogous clause whenever a
walk's "already processed" set spans more than the current group.

Three traps, all of which cost real time and all of which recur:

* **`have` with several goals open lands only in the first.** Facts a branch needs must be
  established *inside* `all_goals`, or hoisted before the tactic that splits. This is what made
  an earlier separate `lane_tbl` walk fail to match, repeatedly and confusingly.
* **`step*` closes recursive calls with the theorem's own induction hypothesis**, and then leaves
  its premises as goals — including metavariables for arguments that appear only in premises
  (`a0`, `nb`, `kk`). When those matter, take the loop's increment step manually
  (`Std.Usize.add_spec` + `WP.spec_imp_exists`) so the IH can be applied explicitly.
* **`scalar_tac` blows `maxRecDepth`** on goals carrying a big `do` block; `omega` fails fast
  instead, so prefer `omega` plus the one or two `Usize` facts it needs, hoisted as `have`s.

## The forward direction is done

`ntt_block_State_q2`: after `ntt_block`, the block holds the evaluation of its input at the 256
leaf constants of `q₂`'s CRT tree — the shape `State_leaf_mul_q2` consumes. Nothing is assumed;
the ψ tables' properties are `decide`d over the literal arrays.

The chain is four horizontal layers (`ntt_block_loop0_walk_q2`, unrolled over `half = 8, 4, 2, 1`),
a transpose into coefficient coordinates, four vertical layers, a transpose back, with both
`barrett_block` passes transparent to the value view (`barrett_block_val`); then eight
applications of `State_ct` from `State_root_intro` (`fwdAll_State`).

The inverse side's atom is done too: `gs_butterfly_bnd` / `gs_butterfly_val` — the GS butterfly is
`(lo, hi) ↦ (lo + hi, ψ·(lo − hi))`, and the inverse tables carry `State_gs`'s negation already,
so no sign is inserted by hand. `gsLvl` / `gsLvl_hbut` mirror `ctLvl` / `ctLvl_hbut`.

## What F4 still needs, and what it costs

Everything left is the code walk, and it is *volume*, not difficulty. Measured against this
session's rate — one loop walk is 100–150 lines and five to fifteen compile-fix cycles — the
inventory is:

1. **`invntt_block`'s loop walks** (~6 + assembly). Structurally the mirror of the forward ones,
   and the templates transfer: `gsLvl` plays `ctLvl`'s part and `gs_butterfly_bnd/val` plays the
   butterfly's. The growth schedule differs — the GS sum path doubles, so the usable bound is
   1.52q and the Barrett passes sit after levels 2, 4 and 6 — so the bound arithmetic has to be
   re-derived, but `State_gs`'s hypotheses are already discharged at both primes.
2. **The final Montgomery scaling** by `INVNTT_SCALE`, then `reduce_invntt`'s Montgomery pass over
   the `i64` accumulator and the Garner combine, at which point `crt_endpoint` closes it. Compose through `transpose16_tpos` and the two `barrett_block`
   passes to `State ζ 256 1 c f a`, at both primes. The Barrett passes change representatives but
   not residues, so they need a `barrett_block` *value* spec too — cheap, from `barrett_lane_spec`'s
   congruence conjunct.
4. **Inverse** (~6 walks + assembly). `invntt_block`'s loops against `State_gs`, plus the final
   Montgomery scaling by `INVNTT_SCALE`.
5. **Endpoints** (~2). `reduce_invntt`'s Montgomery pass over the `i64` accumulator, and the
   Garner combine, at which point `crt_endpoint` closes it. `pointwise_mul_acc` is already done
   (`pointwise_mul_acc_lane_spec`), and `State_leaf_mul_q1/q2` is what turns it into a product.

That is roughly 3000 lines and, at this session's observed rate, tens of hours. There is no
mathematical obstacle left in it — every lemma it needs is stated and proved — but it is not a
session's work, and it should be attacked one walk at a time with the tree kept green between
them.

## Session log: making `make prove-kopis` fail honestly

`prove-kopis-avx2` used to run `lake build KopisAvx2` only, so the target passed while nothing
downstream was checked. It now runs `KopisAvx2 TopLevelTheoremsAvx2 TrustBase`; the
`TopLevelTheoremsAvx2` lean_lib and the sed rules that repoint the generated twin at
`Kopis.Avx2.Properties` are in (commit "Make prove-kopis actually build the AVX2 audit surface").

With that in place the build's *entire* failure surface is two lines:

    Kopis/Avx2/Properties/NttMul.lean:184  -- pointwise_mul_acc
    Kopis/Avx2/Properties/NttMul.lean:344  -- reduce_invntt_to_ring_elem

The other twelve NTT-dependent twins do not fail on their own; they are simply downstream of
`NttMul`, so nothing has been reported about them yet.

### Why those two cannot be patched

Both are stated in terms of `aZ`/`accZ` — the integer *value* of an `i32` lane. On the serial
backend that lane is a residue mod p = 50330113. On AVX2 it is two 16-bit residues, mod
q1 = 7681 and q2 = 10753, packed into one `i32`. The statements are therefore false on the AVX2
branch, not merely unproved, and no amount of generator patching moves them. `NttBridge`'s
`ElemOK` and `ntt_entry_spec` inherit the same problem.

So the twin for `NttMul.lean`, and the parts of `NttBridge.lean` it feeds, have to be *replaced*
rather than patched: same top-level conclusion (`toRingElem r = Σ toRingElem u * toRingElem v`),
a different intermediate representation, routed through the F4 machinery. That is the real shape
of the remaining work, and it sits behind finishing F4.

### Remaining work, in dependency order

1. **Generalize `lane_tbl_spec`** (Tables.lean). It currently hardcodes `neg = false`,
   `0 ≤ base ≤ 128`, `h_stride ∈ {0,1}`, `m_stride ∈ {1,2,4,8}`. The four INV tables need
   `neg = true`, `base ∈ {255,127,63,31}`, `h_stride ∈ {-1,0}`, `m_stride ∈ {-8,-4,-2,-1}`.
   `TblAt` gains a `neg` parameter; the two loop specs and `lane_tbl_spec` follow mechanically.
   Then eight `inv{1,2,4,8}_q{1,2}_ok` lemmas mirroring `fwd1_q1_ok`.
2. **`invntt_block`'s seven walks + assembly** (`invntt_block_loop0`, `loop1_loop0`, `loop1`,
   `loop2_loop0`, `loop2`, `loop3`, `loop4_loop0_loop0`, `loop4_loop0`, `loop4`, `loop5`).
   `ntt_block_loop4_walk` is the template; substitute `gsLvl` for `ctLvl` and
   `gs_butterfly_bnd/val` for the CT pair. Note the growth shape differs: GS gives
   `(2A, T)` from a common input bound `A`, not `(A+T, A+T)`, so `Split` needs a variant whose
   processed bound is an explicit `B` rather than `A + T`.
3. **`reduce_invntt`** — the Montgomery pass over the `i64` accumulator, then the Garner combine,
   closing with `crt_endpoint`.
4. **AVX2 `NttMul` + `NttBridge`**, written against the two-residue representation.
5. **`TrustBase.lean`** — a second `backends` row for `RustKopisAvx2` with its own audited axiom
   list (the 45 intrinsic axioms, `available_ok`, `rangeInclusive_contains_ok`,
   `CbdGeneric.U{8,32}.count_ones_spec`).

Nothing in that list is blocked on a missing idea. It is volume.

### Progress against that list

**1 and 2 are done.**

`lane_tbl_spec` is generalized (`neg`, `base ≤ 255`, negative strides, a two-sided `hidx`), and
`inv{1,2,4,8}_q{1,2}_ok` give all eight inverse tables. One Rust change was needed and is its own
commit: `crt::zeta::<SECOND>(k).wrapping_neg()` became `0i16.wrapping_sub(crt::zeta::<SECOND>(k))`,
because aeneas extracts `i16::wrapping_neg` as an **axiom with no definition** — proving the
horizontal inverse levels against it would have meant assuming its meaning. `src/arithmetic/ntt.rs`
already carried exactly this change for `i64::wrapping_neg`; identical codegen, one fewer
assumption.

The inverse transform is walked end to end, in `Kopis/Avx2/InvWalk.lean`:

* the four vertical levels (`invntt_block_loop0..loop3`), the four horizontal ones
  (`invntt_block_loop4*`), and the `INVNTT_SCALE` pass (`invntt_block_loop5`);
* `invntt_block_walk`, generic in the prime, composing all of it plus the four `barrett_block`
  passes and the two transposes;
* `invAll_State` — `State_gs` eight times, leaf state back to root — and
  `invntt_block_State_q{1,2}`, which instantiate the walk with the real tables.

Two things worth recording. `Split`'s `A + T` shape does not fit Gentleman-Sande: GS takes a
common input bound `A` to `2A` on the sum side and `T` on the product side, so `SplitB` carries an
explicit processed bound. And the growth schedule only closes because of the re-centring passes —
two consecutive GS levels take a centred block to `4·(q/2)`, and a third would overflow the lane,
which is exactly where the code puts its `barrett_block` calls.

Net effect of `invntt_block`: `256 · σ = 2^16`, so the block comes back multiplied by `R`. That is
the Montgomery-domain convention the following reduction expects, not an error.

**3 is half done.** `reduce_block` — the Montgomery pass over the `i64` accumulator, plus the
inverse transform it tails into — is proved at both primes in `Kopis/Avx2/Reduce.lean`
(`reduce_block_q1`, `reduce_block_q2`).  What that needed:

* `mont_reduce32` in `NttReduce.lean`: the same cancellation as `mont_mul_lane_spec` but on a bare
  `i32`, with the sharp `2¹⁶·|R| ≤ |X| + 2¹⁵·q` conjunct.
* `pack_permute_lane` in `SerLane.lean`: the lane routing `vpack**dw` + `vpermq 0xD8` performs is
  the same for both saturations, so `vpackssdw` and `vpackusdw` are two instances of it.
* A correction worth recording. The block `reduce_block` hands to `invntt_block` is bounded by the
  *reduction's output*, not by `(q−1)/2`, and two Gentleman-Sande levels from there is different
  arithmetic than two levels from a centred block — so `invntt_block_walk` takes a separate entry
  triple.  The crude `|R| < q` bound is not enough: it overflows the lane at the second level.
  The sharp bound gives 7141 at `q₂` and 4741 at `q₁`, and the schedule then closes with 28564 of
  32767 used at the worst point.

**What is left in 3** is the Garner combine — `reduce_invntt`'s second half.  Its two ends are
done:

* `Crt.garner_value` — the reconstruction as integers.  Canonicalise both residues, solve for the
  multiplier, form `a₁ + q₁·t`, centre it by subtracting `q₁q₂` above the midpoint, and that *is*
  the coefficient.  This is what makes the truncation to 16 bits afterwards right.
* `Reduce.canon_lane` — the `add(r, and(srai<15>(r), q))` canonicalisation, which the combine uses
  three times.

Everything the combine needs is now proved, piece by piece:

| piece | lemma |
|---|---|
| canonicalise a centred residue | `Reduce.canon_lane` |
| solve for the multiplier | `Crt.garner_mult`, on `crt_q1_inv_mont_ok` |
| widen a 128-bit half to 32-bit lanes | `Reduce.widen_lo`, `Reduce.widen_hi` |
| `a₁ + q₁·t`, centred, masked to 16 bits | `Reduce.combine_lane` |
| pack back down | `SerLane.pack_permute_u16` |
| the reconstruction is the coefficient | `Crt.garner_value` |

**Item 3 is now complete.**  `Reduce.reduce_invntt_walk` closes the whole inverse path: `i64`
accumulator → Montgomery reduction → inverse transform → CRT reconstruction → coefficients, with
the output the wrapping `u16` the caller wants.  The 32-bit lane arithmetic never wraps —
`a₁ + q₁·t < q₁q₂ < 2³¹` — which is why `combine_lane` needs no bound hypotheses beyond the two
residues being canonical.

## Item 4: the shape of it

Two findings that took real digging and that the next session should not have to repeat.

### The `NttElem` layout

`backend.avx2.ntt.from_ring_elem` runs `split_and_transform` twice and writes the results into one
256-`i32` array through `store_i16_of_i32`, at vector indices `0..16` then `16..32`.  Read as 512
`i16` (`NttMulLane.i16View`), that means:

* positions `0 … 255` hold the **q₁** residues, coefficient by coefficient;
* positions `256 … 511` hold the **q₂** residues.

`pointwise_mul_acc` multiplies `i16` lane `t` of each operand into `i32` lane `t` of the
accumulator (`NttMulLane.pointwise_mul_acc_lane_spec`), so the accumulator inherits the same
split — which is exactly why `reduce_invntt` calls `reduce_block false acc 0` and
`reduce_block true acc 32` (`8 · 32 = 256`).  That is the whole two-residue representation, and it
lines up end to end.

### The dispatch is hoistable, but the bodies are not equal

`available_ok` is `∃ b, cpu.available = ok b` — it fixes *one* boolean for every call site, but
says nothing about which.  So both branches must be proved, and the established pattern
(`CbdDispatch.lean`) is `obtain ⟨b, hb⟩ := available_ok; rw [hb, bind_tc_ok]; cases b`.

For CBD the AVX2 branch was then collapsed onto the portable one by proving the two bodies
*equal* (`avx2_cbd_eq`).  **That trick does not transfer here.**  `from_uniform` already produces a
different array on the two branches — two 16-bit residues versus one residue mod `p` — so no
intermediate equality holds anywhere along the chain.  The branches only reconverge at
`toRingElem`.

### What that implies for the twin

The dispatch has to be hoisted to whichever theorem spans *both* the accumulate loop and
`reduce_invntt_to_ring_elem` — that is `ntt_mul_inner_spec`, not `pointwise_mul_acc_spec`.  Below
that point:

* the **serial branch** costs nothing: once the `if` reduces, the existing generated proof applies
  verbatim;
* the **AVX2 branch** needs `from_ring_elem`'s walk (two `split_and_transform` calls, each
  `barrett` then `ntt_block`, both already proved as `ntt_block_centred_q{1,2}` and
  `ntt_block_State_q{1,2}`), the pointwise product, and `Reduce.reduce_invntt_walk`, tied together
  through an AVX2 `ElemOK` that carries a `State` at each prime instead of one mod `p`.

`pointwise_mul_acc_spec` and `ntt_entry_spec` as currently stated should be *deleted* from the
AVX2 twin rather than patched: they name the intermediate representation, and that is the one
thing the two branches do not share.

### Progress on 4

**Both directions of the AVX2 NTT are now proved**, in `Kopis/Avx2/Reduce.lean`:

* `from_ring_elem_walk` — the forward direction end to end. Barrett-reduce the `u16` coefficients,
  `ntt_block` at each prime, written into the packed layout, with a `State` per prime. This is the
  AVX2 counterpart of the serial `from_uniform_elem_spec` and the shape an AVX2 `ElemOK` needs.
  It rests on `split_and_transform_q{1,2}` and `NttWalk.ntt_block_State_q{1,2}` (the `q₁`
  instantiation of the forward transform was missing and is now there too).
* `reduce_invntt_walk` — the inverse direction end to end (item 3).

**The AVX2 NTT correctness core is now complete.**  Three theorems in `Kopis/Avx2/Reduce.lean`
span the whole chain:

* `from_ring_elem_NttOK` — the forward direction, packaged as `NttOK g ne`: both lane bounds and a
  `State` per prime.
* `pointwise_acc_int` — the multiply-accumulate as an integer identity (the `BitVec` version wraps;
  with the operands and running accumulator inside `2³¹` it never fires).
* `ntt_entry_avx` — the composite. `N` transformed pairs, their products accumulated, the inverse
  path, out come the coefficients of the convolution as wrapping `u16`.

The three Montgomery constants cancel exactly, which is `cancel_q1`/`cancel_q2`: `invntt_block`
carries `256·σ = R` out and the reduction's `R⁻¹` undoes it, so what remains is the convolution
itself.  That cancellation is the sharpest check that the whole chain lines up, and it holds at
both primes.

**What is left in 4 is wiring, not mathematics.**  Step 1 below is done; 2–4 are not.

1. ~~Connect `NttOK` to `NttElem.from_uniform` / `from_secret`.~~ **Done** —
   `from_uniform_NttOK` and `from_secret_NttOK`, both stated under `cpu.available = ok true`.
   The `REDUCE = false` path `from_secret` needs is `split_and_transform_walk_nored`: the input is
   already small, so the loop is a plain copy and the caller supplies the bound.
2. ~~The accumulate loop on the AVX2 branch.~~ **Done** — `mul_inner_avx`, `NttMatrix.mul`'s
   innermost loop with `pointwise_mul_acc` taking its AVX2 body, carrying the `i32View` sum and
   the running `n·B²` bound.
3. ~~Relate the AVX2 chain's conclusion to the serial one.~~ **Done** —
   `reduce_invntt_to_ring_elem_avx` proves *exactly the statement*
   `reduce_invntt_to_ring_elem_spec` proves.  That is the important structural fact: the
   postcondition (`(r[n]).val ≡ H n mod 2¹⁶`) is about the coefficients of the answer, not about
   how the accumulator stored them, so the two branches reconverge there and the twin's dispatch
   becomes dischargeable.

**What is genuinely left**, and it is now a small, well-defined edit rather than new proof work:

* An AVX2 `ntt_entry_spec`: same conclusion as the serial one
  (`toRingElem r = Σ toRingElem u * toRingElem v`), with `NttOK` in place of `ElemOK` and the
  `i32View` accumulation in place of `hacc`.  Its proof is `reduce_invntt_to_ring_elem_avx`
  followed by the *unchanged* tail of the serial `ntt_entry_spec` (everything from
  `intro r hr` onward), because that tail only uses the shared postcondition.  Take
  `H := convZ u v N`; the bound `|convZ| ≤ 25165056` is what the relaxed `garner_value` now
  accepts.
* Hoist the dispatch in the twin's `ntt_mul_mid_spec` — the one theorem spanning both the
  accumulate loop and `reduce_invntt_to_ring_elem`.  `obtain ⟨b, hb⟩ := available_ok; cases b`;
  serial branch takes the generated proof verbatim, AVX2 branch takes `mul_inner_avx` then the
  AVX2 `ntt_entry_spec`.  This is a `PATCHES` entry in `scripts/gen_avx2_twins.py`, not a new
  proof.
* Then the other twelve twins follow: they consume only `ntt_mul_spec` /
  `ntt_mul_transpose_spec`, whose statements do not change.

Then item 5: the second `backends` row in `TrustBase.lean`.


Then `reduce_invntt` assembles the two `reduce_block` calls with the combine, and item 4 (the AVX2
`NttMul`/`NttBridge`) and item 5 (the `TrustBase` row) follow.

*Superseded note (kept for the record):* the original text below listed item 3 as all new lane
algebra.
