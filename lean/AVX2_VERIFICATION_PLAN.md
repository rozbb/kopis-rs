# Formally verifying the AVX2 backend

> Drafted 2026-08-01, after `./extract_rust_to_lean.sh` was run with
> `RUSTFLAGS='--cfg kopis_backend="avx2"'` and aborted. Companion to `NTT_REFACTOR_STATUS.md`.
>
> **Steps 1–4 are done** — see *Status* below. Steps 5–7 (the correspondence proofs) are not
> started.

## Status (2026-08-01)

`./extract_rust_to_lean.sh` now extracts **both** backends and completes with no errors:
`lean/ExtractedRustSerial.lean` (serial, byte-identical to before) and `lean/ExtractedRustAvx2.lean`
(AVX2, 6947 lines, namespace `RustKopisAvx2`). `make prove-kopis` is unaffected and green;
`make prove-avx2` builds the new extraction plus the intrinsic semantics.

What landed:

* **`src/backend/avx2/intrinsics.rs`** — 42 safe wrappers (30 instructions, 12 memory
  accessors) over the `Vec256` / `Vec128` newtypes. `#[target_feature(enable = "avx2")]` makes
  them safe to call from the rest of the backend, which now contains **no `unsafe` and no raw
  pointers at all**.
* **`lean/Kopis/Avx2/Intrinsics.lean`** — one axiom per wrapper, over
  `bits : Vec256 → BitVec 256` with derived lane views. This is the review surface and the whole
  of the added trust base.
* The pointer refactor of step 3, plus three changes forced by aeneas limitations found the
  hard way (below).
* `charon --opaque 'kopis::backend::avx2::intrinsics' --opaque 'kopis::backend::avx2::cpu'`.
  `cpu` is `--opaque` rather than `--exclude` as originally planned: excluding it makes the
  `avx2_available()` dispatch block untranslatable.

Verification of the refactor: `cargo test` green under `--cfg kopis_backend="avx2"` (33 tests,
including `avx2_matches_serial`, `sample::matches_serial`, `transpose16_permutes_as_documented`
and `crt::zetas_tables_are_correct`), under `serial`, and `cargo check` green for
`--cfg kopis_backend="neon"` on aarch64. In the generated assembly every wrapper is inlined —
zero calls or jumps into `intrinsics::` — and no bounds-check panic path survives in the NTT
symbols. Benchmarks: encapsulation 4.7536 → 4.7561 µs (+0.05%), key generation 15.81 →
15.62 µs (−1.2%), decapsulation within a run-to-run spread of ±4% on this 4-core host, which is
too noisy to resolve a change of the size we are looking for. Static instruction count for the
backend rose 2174 → 2413, most of it the one copy the layout change added (`from_ring_elem` now
writes its block through the `i16`-of-`i32` accessor rather than transforming in place).

### Three aeneas limitations, none of them documented

Each was isolated with a ~10-line file through `charon rustc` + `aeneas`, after the whole-crate
error spans pointed somewhere unhelpful. Worth knowing before writing more extractable Rust:

1. **A function that returns a `&'static` reference cannot be translated.** `fn f() -> &'static
   P { &S }` fails with `Unreachable` at `interp/Interp.ml:609` — reported not at the function
   but at the first *field read* through the returned reference, which is why the original
   report blamed `p.q`. Reading a static inside a function is fine. This is what
   `crate::backend::crt::prime::<SECOND>() -> &'static Prime` was, and it is now six accessors
   returning values (`crt::q`, `crt::qinv`, `crt::zeta`, …). The AVX2 per-lane ψ tables took the
   same treatment: selected at the use site instead of through a `&'static Tbl<N>` accessor.
2. **A `const`/`static` initializer *block* containing a loop cannot be translated** —
   `const A: [T; N] = { let mut a = ...; while ... ; a };` gives `Internal error, please file an
   issue`. The identical loop inside a `const fn` that the initializer calls is fine. That is
   the one-line change `ser.rs`'s `PLANS` needed.
3. **A reference inside a struct reached by reference** (`Prime { zetas: &'static [i16; 256] }`
   behind `&'static Prime`) kills the whole run with `Invalid_argument "option is None"` out of
   `translate_global_eval`. Subsumed by fixing (1), but it fails differently and earlier.

`#[target_feature]`, `unsafe`, const generics, `#[repr(align)]` and statics holding large arrays
all extract without trouble.

## Context

`./extract_rust_to_lean.sh` with `RUSTFLAGS='--cfg kopis_backend="avx2"'` aborts
(`236/238` then `Uncaught exception`). The failures are not incidental:

- Four `[Error] Unreachable` at `ntt.rs:420/520/631/750`, all at column 30–33 = `p.q`,
  the argument to the first `_mm256_set1_epi16` in `ntt_block`, `invntt_block`,
  `split_and_transform`, `reduce_block`. The span is misleading — aeneas's symbolic
  interpreter hit the intrinsic call and fell off a match (`interp/Interp.ml:609`,
  an internal assert-false). `__m256i` is a rustc builtin type with no MIR definition
  and `core::arch::x86_64` intrinsics are `extern "unadjusted"` declarations with **no
  body**, so charon has nothing to lower. One root cause, four hits, each poisoning a
  whole function.
- `Raw ptr casts are only supported between pointers to literal types` at
  `pointwise_mul_acc` (`ntt.rs:701-738`) — same root cause, plus `.add(16 * i)` raw
  pointer arithmetic, which aeneas does not model regardless.

No Rust rewrite makes intrinsics extractable. The fix is to stop extracting them:
present the extractor an opaque interface, and supply that interface's semantics by
hand in Lean. This is libcrux's architecture (`libcrux/crates/utils/intrinsics/src/avx2_extract.rs`
+ `libcrux/fstar-helpers/fstar-bitvec/BitVec.Intrinsics.fsti`), adapted to aeneas/Lean.

**Outcome:** the AVX2 backend joins `ExtractedRustSerial.lean` and gets correspondence
proofs alongside the portable code, with a documented trusted base of hand-written
intrinsic semantics.

## What can and cannot be reused from libcrux

Coverage of the 38 intrinsics used across `src/backend/avx2/`:

| Bucket | N | Detail |
|---|---|---|
| Lane-level spec in `avx2_extract.rs` | 8 | `add/sub/mullo/mulhi_epi16`, `srai_epi16`, `set1_epi16`, `setzero`, `and_si256` |
| Bit-level model in `BitVec.Intrinsics.fsti` | 5 | `shuffle_epi8`, `srli_epi16`, `castsi256_si128`, `extracti128_si256`, `mm_loadu_si128` |
| Wrapper, no spec | 15 | the `_epi32` family, `permute2x128`, `permute4x64`, `unpack*_epi32/64`, `packs_epi32` |
| Absent | 10 | `unpacklo/unpackhi_epi16`, `cvtepu16_epi32`, `packus_epi32`, `broadcastsi128_si256`, `srl_epi16`, `cvtsi32_si128`, `load_si256`, `loadu/storeu_si256` |

Two consequences:

1. **The arithmetic core is fully covered.** `mont_mul` (`ntt.rs:271`) and `barrett`
   (`ntt.rs:283`) use only `mullo/mulhi/sub/add/srai_epi16` — all in the lane-spec
   bucket. Their specs (`map2 (+.) (vec256_as_i16x16 lhs) ...`) transcribe directly.
2. **The transpose network is not covered at all.** `unpacklo/unpackhi_epi16` (10 uses
   in `ntt.rs`), `permute2x128_si256` (4), `permute4x64_epi64` (3), `cvtepu16_epi32` (4)
   have no libcrux model. libcrux's AVX2 proof effort is weighted toward serialization;
   ours is weighted toward `transpose16`. That is the work we own.

Do **not** copy F* source into Lean: `bit_vec n` there is `i:nat{i<n} -> bit` with
`mk_bv` plus a `Tactics.*` normalization stack that has no Lean counterpart. The
*specs* are reusable ideas; the code is not. Also note libcrux `admit()`s the
bit↔lane bridge (`lemma_mm256_mullo_epi16 ... = admit()`) and ships
`mm256_set1_epi16_no_semantics` / `mullo_epi16_specialized1..3`. We can prove those
bridges in Lean rather than admit them.

**Licensing:** libcrux `Cargo.toml` says `license = "Apache-2.0"` but the repo ships
`LICENSE-MIT` too; kopis is `MIT/Apache-2.0`. Author the Rust wrappers fresh (they are
`unimplemented!()` stubs — trivial) rather than vendoring, and treat the specs as
prior art to cite in the trust-base doc.

## Architecture

Four layers, bottom up:

1. `src/backend/avx2/intrinsics.rs` — safe wrappers over an opaque `Vec256`/`Vec128`
   newtype, one per intrinsic, unsafety and `#[target_feature]` confined inside,
   `#[inline(always)]`. Slice-typed loads/stores (`loadu_si256_i16(&[i16]) -> Vec256`,
   `storeu_si256_i16(&mut [i16], Vec256)`) following libcrux's shape — this is what
   removes the raw-pointer problem.
2. `charon --opaque 'kopis::backend::avx2::intrinsics::_'` (plus `--exclude` for
   `cpu`). Aeneas already emits opaque items as `axiom Vec256 : Type` /
   `axiom mm256_add_epi16 : Vec256 → Vec256 → Result Vec256` — see
   `/home/dev/aeneas/tests/lean/BuiltinAuto.lean:25` and `LoopSharedBorrowProj.lean:38`.
   **No cfg-swapped shim file is needed**, unlike libcrux; one `intrinsics.rs` serves
   both compilation and extraction.
3. `lean/Kopis/Avx2/Intrinsics.lean` — `Vec256 := BitVec 256` as ground truth, plus
   `toLanes : BitVec 256 → Vector (BitVec 16) 16` and a *proven* lane view. Each
   intrinsic defined bit-level; lane-level lemmas derived, not admitted.
4. `lean/Kopis/Avx2/*.lean` — correspondence proofs against `Spec`.

## Target theorems

These differ per file and this matters:

- **`ser.rs` / `sample.rs` — direct equivalence.** `mod.rs` states both are
  "lane-parallel restatements of portable routines and produce bit-identical output".
  So: `avx2::ser::deserialize bytes bits = Spec.deserialize_generic bytes bits` and
  `avx2::sample::cbd MU buf = Spec.cbd MU buf`. Cleanest targets; do these first.
- **`ntt.rs` — NOT equivalence with the serial NTT.** Per `mod.rs` and
  `src/backend/crt.rs`, AVX2 runs two 16-bit transforms (q₁=7681, q₂=10753) where the
  portable code runs one 26-bit one; "the NTT-domain values are different integers
  entirely" and "only the endpoints of the pipeline agree". The theorem is
  end-to-end over the CRT reconstruction: the `split_and_transform → pointwise_mul_acc
  → reduce_block → invntt_block` pipeline computes the same ring product as
  `arithmetic::ntt`, discharged through the existing `NttMath.lean` (commit `21321dc`).
- **`ntt.rs` growth bounds — a real, separable obligation.** `crt.rs:52-60` notes the
  crude per-level budget predicts 3.5q > 3.05q for AVX2's four-level run (levels 4–7)
  and that safety rests on interval propagation with actual per-butterfly ψ values
  bounding the worst lane below 30 700 of 32 767. That argument is currently prose only
  and is the highest-value thing to mechanize — it is exactly what breaks silently if
  anyone reorders reductions or regenerates ψ tables.
- **`cpu.rs` — out of scope.** CPUID/XGETBV is unverifiable here; `--exclude` it and
  record `available()` as an assumption in `TopLevelTheorems.lean`.

## Steps

1. **Baseline the gap.** Run charon with `--opaque` on the intrinsics path, then
   `aeneas -print-unknown-externals` to get the authoritative list of externals needing
   Lean definitions. Do not trust the 38-name grep — it misses trait-dispatched and
   generic instantiations.
2. **`src/backend/avx2/intrinsics.rs`.** Wrap all 38. Verify codegen is unchanged
   (`cargo asm` or benchmark diff) — `#[inline(always)]` over a newtype should be free,
   but confirm rather than assume, since this is the hot path.
3. **Refactor away raw pointers.** `ld`/`st` (`ntt.rs:229`, `:241`) take `&[i16; 256]` /
   `&mut [i16; 256]` and index; `ld_tbl` (`ntt.rs:253`) slices `table.z`/`table.zq`
   instead of `.as_ptr().add().cast()`; `ntt_block`, `invntt_block`, `reduce_block`,
   `split_and_transform`, `pointwise_mul_acc` take array refs. `ser.rs` `_mm256_load_si256`
   on `Plan`/`Nibbles` fields becomes a slice load. Keep `#[repr(align(32))]`.
4. **`lean/Kopis/Avx2/Intrinsics.lean`.** Ground `Vec256 := BitVec 256`; define
   `toLanes`/`ofLanes` and prove they are inverse. Define each intrinsic; derive
   lane-level rewrite lemmas (`@[simp]`) for the arithmetic ops so downstream proofs
   never see bits. Order of work: arithmetic ops (transcribe libcrux specs) → shifts →
   `shuffle_epi8`/`srlv` (port the `mk_bv` bit-index formulas) → **the transpose family,
   written from scratch against the Intel SDM**.
5. **`ser.rs` + `sample.rs` proofs.** Bit-level throughout; this is where the libcrux
   bit-vector models pay off most. `sample.rs` `cbd` builds on `ser::deserialize`, so
   the deserialize theorem is a prerequisite.
6. **`ntt.rs` proofs.** `mont_mul`/`barrett` lane specs first (they mirror the already-
   proven `mont_reduce_spec`/`barrett_reduce_spec` in `lean/Kopis/Properties/NttReduce.lean`
   — reuse those), then `transpose16` as a permutation lemma, then the growth-bound
   interval propagation, then the CRT end-to-end theorem through `NttMath.lean`.
7. **Update `extract_rust_to_lean.sh`** to emit both backends, and `lean/lakefile.lean`
   for the new `Kopis.Avx2` files. Extend the `TopLevelTheorems.lean` trust-base check
   to enumerate the intrinsic axioms.

## Verification

- `cargo test` — `sample.rs`'s `matches_serial` and `arithmetic::ntt`'s
  `avx2_matches_serial` must stay green across the pointer refactor. These are the
  ground truth that the refactor changed nothing.
- Benchmark before/after the wrapper + pointer refactor; a regression means
  `#[inline(always)]` did not fire and the wrapper needs adjusting.
- `./extract_rust_to_lean.sh` must complete with no `Unreachable` and no
  `Could not translate the body of`.
- `make prove-kopis` green, no new `sorry`. Note the host is 4 cores / 4 GB and
  `NTT_REFACTOR_STATUS.md` records OOM (exit 137) when co-elaborating heavy WP-monadic
  proofs — build with `LEAN_NUM_THREADS=2`, and keep each intrinsic-model file small and
  separately importable from the start rather than splitting later.
- **Differential-test the Lean models.** The intrinsic semantics are axioms; nothing
  checks `mm256_mulhi_epi16`'s Lean definition against silicon. Add a `SpecTests` runner
  that evaluates the Lean model on random inputs and compares against a Rust harness
  dumping real intrinsic outputs (libcrux has `BitVec.Intrinsics.TestShuffle.fst` for
  the same reason). Highest priority for the shuffle/permute family we author ourselves.

## Trust base

Grows by: `Vec256` semantics, 38 intrinsic definitions, and `available()`. All must be
listed explicitly in `TopLevelTheorems.lean`. This is strictly better than the current
state (AVX2 wholly unverified) and comparable to libcrux — minus their `admit()`ed
bit↔lane bridges, which we prove.
