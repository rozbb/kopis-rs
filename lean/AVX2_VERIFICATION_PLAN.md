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
