# NTT + pubkey-refactor proof status

> ## ▶ RESUME HERE (paused 2026-07-24, waiting on more host RAM)
>
> **Where we are:** `make prove-kopis` is GREEN. Down from 11 `sorry`s at the start of the
> refactor to **4**, all in `Ntt.lean` — exactly the four core NTT transform specs
> (`from_uniform_matrix_spec`, `from_secret_matrix_spec`, `ntt_mul_spec`,
> `ntt_mul_transpose_spec`). Everything else (composites, all four magnitude lemmas,
> `to_canonical_spec`) is real, committed proof. Latest commits on `worktree-ntt-mult`.
>
> **Immediate RAM-blocked item:** `Kopis/Properties/NttReduce.lean` holds three FULLY-PROVEN,
> `sorry`-free reduction value-specs (`mont_reduce_spec`, `to_wrapping_u16_spec`,
> `barrett_reduce_spec`). They are NOT imported by `Kopis.lean` (so the build stays green)
> because on this 4 GB host any two of these heavy WP-monadic proofs OOM (exit 137) when
> co-elaborated. **First thing after more RAM:** add `import Kopis.Properties.NttReduce` to
> `Kopis.lean` and run `make prove-kopis`; if it still strains, split the three into one file
> each (each imports `Ntt`; `mont_reduce_spec` alone compiled to exit 0 standalone).
>
> **Then the real work — the 4 core transform specs (`ntt_spec`):** these are architecturally
> blocked and need, in order:
>  1. The reduction value-specs above wired in (done, modulo RAM).
>  2. Replace `opaque nttInvU`/`nttInvS` in `Ntt.lean` with a concrete inverse-NTT `def`.
>  3. Prove the extracted `ntt`/`invntt` butterfly loops compute a mathematical NTT/invNTT
>     (Cooley–Tukey / Gentleman–Sande; 8-level CRT split of `X²⁵⁶+1`; `ZETAS` = bit-reversed
>     powers of ψ=49118445, a primitive 512-th root of unity mod p; Montgomery domain tracked
>     via `mont_reduce_spec`, cancelled by `INVNTT_SCALE`; lazy Barrett reduction after level 4).
>  4. From those, the roundtrip `invNTT ∘ NTT = id` (⟹ the two `from_*` specs) and the
>     convolution theorem `invNTT(NTT A ⊙ NTT s) = A·s` (⟹ the two `mul` specs), discharging
>     the `fitsExactly` exactness bound.
> `symcrypt-lean/` does NOT help here: its Kopis is the pre-migration schoolbook version and has
> no NTT. Verified numeric facts (all checked): `P·P_INV ≡ 1 mod 2³²`, `INVNTT_SCALE =
> 256⁻¹·2⁶⁴ mod p`, `ψ²⁵⁶ ≡ -1 mod p`. This is multi-session work.
>
> **Host note:** 4 cores / 4 GB. Always build with `LEAN_NUM_THREADS=2` (or `1` for the heavy
> reduction proofs) — see the `Makefile`. Full `make prove-kopis` from a clean state ~4–5 min.

Status of the Lean correspondence proofs after three Rust changes landed on
`worktree-ntt-mult`: (1) multiplication moved to a negacyclic NTT over `p = 50330113`;
(2) the PKE public key now stores its serialized bytes (`vec_bytes`) instead of the
structured `Matrix<L,1>`; (3) the `gen` module was renamed `sample`.

## Current state — `lake build Kopis` is GREEN

The entire crate has been rewired to the NTT-domain representation. `lake build Kopis`
completes successfully, and every proof file compiles as real proof except for **one**
documented hole (**4** `sorry`s total, all in one file):

1. **`ntt_spec`** — the single mathematical hole (**4** `sorry`s in `Ntt.lean`): that the
   negacyclic NTT computes the ring product. These are exactly the four core transform specs
   (`from_uniform_matrix_spec`, `from_secret_matrix_spec`, `ntt_mul_spec`,
   `ntt_mul_transpose_spec`); all four raw-magnitude lemmas are now proved. See below.

The three `kopisXXX_keygen_encap_spec` key-gen→encapsulate composites in `KeyGenCapstone.lean`
are now **full proofs** (real, at the ordinary 4M `maxHeartbeats`, ~1.3s each).

> **Post-mortem — the "perf hole" was a misdiagnosis.** These three were previously `sorry`ed
> and documented as a heartbeat-nondeterministic `whnf` blowup needing `maxHeartbeats` up to
> 200M. That was wrong. The real bug was **stale hypothesis indices**: the NTT refactor added a
> `SecretBounded` conjunct (h2) to `expand_from_seed_spec`'s postcondition, shifting the later
> conjuncts. The git-history proof still used the old indices, so `exact h3` (which now names the
> `z` conjunct) was pointed at a `pkStructBytes = …` goal. Lean doesn't fail such a mismatch
> fast — because both sides are built from `ExpandDecapKey`, it `whnf`-grinds trying to unify two
> genuinely-unequal terms, burning >200M heartbeats (~865s) before giving up. Fixing the indices
> (pkStructBytes → `h4`, hash → `h5`, per the current conjunct order) turns every `exact` into a
> syntactic match, and the whole file elaborates in ~1.4s at 4M. A `congrArg`-through-opaque-
> `KemEncap` ending (instead of `generalize … at ⊢; rw`) replaced the old `generalize`/`rw`
> closer as a belt-and-braces measure so the final bridge never `whnf`s the spec term either.
> Lesson: a "(deterministic) timeout at `whnf`" on an `exact`/`rw` is often a *wrong-term*
> unification grind, not a proof that needs a bigger budget — check the hypothesis first.

`TopLevelTheorems.lean` is the audit surface. Its `#print axioms` gate now **reports
`sorryAx` (covering the single `ntt_spec` hole) as a loud warning but no longer throws on it**;
it still throws on any *other* new axiom, so it keeps protecting the rest of the trust base.
The three composites are in the audited §3 theorem list, so their being real proofs is verified
by the gate itself. `core.num.I64.wrapping_neg` (Rust `i64::wrapping_neg`, used by the NTT to
negate a twiddle) is in the audited opaque-intrinsics list alongside the two `count_ones`.

### The NTT bridge (`Ntt.lean`) — the decomposed interface

The bridge is stated with two opaque inverse-NTT *functions* (not relations), so the
coefficient matrix an NTT matrix denotes is deterministic and needs no existential when
consumed downstream:

- `nttInvU`, `nttInvS : NttMatrix X Y → Mat X Y` — the uniform/secret coefficient matrix an
  NTT matrix denotes.
- `from_uniform_matrix_spec` / `from_secret_matrix_spec` — `nttInvU/nttInvS (from_… A) = A`.
  **Still `sorry`ed** (unprovable until `nttInvU`/`nttInvS` are de-opaqued — see below).
- `ntt_mul_spec` / `ntt_mul_transpose_spec` — pointwise product of NTT matrices computes the
  schoolbook product of the coefficient matrices they denote (drop-in for the schoolbook
  `matrix_mul(_transpose)_spec`), under the joint magnitude constraint `fitsExactly`.
  **Still `sorry`ed** (the convolution theorem — see below).
- Magnitude lemmas — **ALL FOUR now real, `sorryAx`-free proofs**: `gen_matrix_uniformBounded`,
  `gen_secret_secretBounded`, `deserialize_10_uniformBounded`, `shift_right_uniformBounded`.
  (`deserialize_10` and `gen_secret` gained the input hypotheses — `bytes.length`/`hfit` and
  `MU ∈ {6,8,10}` respectively — that their extracted code's asserts require and their call
  sites already supply; they were previously *false as stated*.)
- `fitsExactly_paramSet` discharges `fitsExactly (ℓ p) (μ p / 2)` for each shipped parameter set.

Only the **four core transform specs** above are `sorry`ed (never `axiom`ed). Everything else —
including all four magnitude lemmas and `fitsExactly_paramSet` — is real proof on top.

### Files rewired (real proof, no sorries)

`PkeSerialize` (vec_bytes copy-loop → `vecBytesFlat`), `PkeHash`, `ExpandDecap`
(NTT-domain secret key, `expand_decap_key_loop` serialize spec, `pkStructBytes` byte-level,
9-conjunct WF postcondition), `PkeEncryptTop`, `PkeDecryptTop`, `KeyGen`, `KemDecap`,
`KemEncap`, `Impls`, `KeyGenHyps`, `KeyGenCapstone`, `PkeFromBytes` (reordered extraction +
`from_bytes_loop` value spec), `KemFromBytes`, `TopLevelTheorems`.

### Threading pattern

- The secret key is now `NttMatrix L 1`; its correspondence is stated over `nttInvS sk`.
  `SecretBounded (nttInvS sk) (μ/2)` is carried from key-gen into decap.
- The public key carries `mat_a_ntt` / `vec_ntt`; correspondences are over
  `nttInvU pk.mat_a_ntt` / `nttInvU pk.vec_ntt`, with `UniformBounded` bounds threaded from
  `gen_matrix`/`deserialize_10`/rounding.
- `expand_decap_key_spec` exposes the full WF (bounds + `vecBytesFlat = serialize(toVecN
  (nttInvU vec_ntt))`) so the key-gen→encap/decap capstones can discharge the encap/decap
  hypotheses.

### Note (`KeyGenCapstone`) — the "perf hole" was a misdiagnosis, now fixed

The three `kopisXXX_keygen_encap_spec` composites are **real proofs at the ordinary 4M
`maxHeartbeats`** (~1.3s each). They were previously `sorry`ed and blamed on a
heartbeat-nondeterministic `whnf` blowup; that was wrong. The real bug was **stale hypothesis
indices** — the refactor added a `SecretBounded` conjunct (h2) to `expand_from_seed_spec`,
shifting the later conjuncts, and the git-history proof still used the old numbers, so `exact h3`
(now the `z` conjunct) hit a `pkStructBytes = …` goal. Lean `whnf`-grinds such a mismatch (both
sides are built from `ExpandDecapKey`) for >200M heartbeats/~865s instead of failing fast. Fixing
the indices (pkStructBytes → `h4`, hash → `h5`) makes every `exact` a syntactic match; a
`congrArg`-through-opaque-`KemEncap` closer replaced the old `generalize … ; rw`. Lesson: a
"(deterministic) timeout at `whnf`" on an `exact`/`rw` is often a *wrong-term* unification grind,
not a proof that needs a bigger budget.

## The single mathematical hole: `ntt_spec` (4 `sorry`s)

The genuinely hard, deferred content is that the negacyclic NTT computes the ring product.
It is now exactly **four** `sorry`s in `Ntt.lean`'s bridge — the core transform specs
`from_uniform_matrix_spec`, `from_secret_matrix_spec`, `ntt_mul_spec`, `ntt_mul_transpose_spec`.
Intended proof route (CRT split per butterfly level, Montgomery/Barrett reduction specs,
lazy-reduction bounds) is documented inline in `Ntt.lean`.

**The blocker is architectural.** `nttInvU`/`nttInvS` are declared `opaque`, so
`nttInvU (from_uniform_matrix A) = A` cannot be proved — an opaque constant has no definitional
content to compute. Discharging these four requires **de-opaquing** `nttInvU`/`nttInvS` into a
concrete inverse-NTT `def`, then proving (a) the negacyclic NTT **roundtrip** `invNTT ∘ NTT = id`
(gives the two `from_*` specs) and (b) the **convolution theorem**
`invNTT (NTT A ⊙ NTT s) = A · s` over the auxiliary prime `p = 50330113` (gives the two `mul`
specs), with the reduction value-specs below and the `fitsExactly` exactness bound. The
`symcrypt-lean` reference proves an analogous theory for MLKEM's mod-`3329` NTT, but Kopis's
multiply-over-an-auxiliary-prime transform has different roots/reduction constants and the
exactness trick, so it is a substantial adaptation rather than a drop-in. This is multi-session
work, not a bounded edit.

### Already proved toward it (in `Ntt.lean`)
- `bmod_i32_exact` / `bmod_i64_exact` and the six `I32/I64_wrapping_{add,sub,mul}_exact`
  corollaries: wrapping arithmetic is exact in range.
- `fitsExactly` (joint `(ℓ,μ)` exactness constraint) + the three parameter instantiations +
  `fitsExactly_paramSet` + `margin_is_2304` + `worst_ell_with_worst_mu_does_not_fit`.
- `signedOfU16` and its mod-`2^16` agreement.
- **All four raw-magnitude lemmas** (`gen_matrix`/`gen_secret`/`deserialize_10`/`shift_right`
  coefficient bounds, as raw values not just residues) — the exactness preconditions the
  `ntt_mul` specs will consume are now fully discharged.

### Still needed for `ntt_spec` (the 4 core specs)
- Reduction-function value specs: `mont_reduce`, `barrett_reduce`, `to_canonical`,
  `to_wrapping_u16` (aeneas-scalar bit-vector plumbing; the `*_exact` lemmas are their core).
- De-opaque `nttInvU`/`nttInvS` to a concrete inverse NTT, then the transform correctness
  (butterfly network = evaluation at the roots; pointwise product = product in the split ring;
  `INVNTT_SCALE` cancels Montgomery + 1/256) — i.e. the roundtrip + convolution theorems above.

## Environment

This session had Lean LSP MCP access (`mcp__lean-lsp__*`) — essential for the bit-vector /
loop-invariant grinding. Full `lake build Kopis` is slow (~15-20 min; `KeyGenCapstone` alone
is several minutes at the raised heartbeat limit).
