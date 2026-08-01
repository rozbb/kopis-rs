# NTT proof status

> ## ▶ RESUME HERE (updated 2026-08-01, branch `avx2`)
>
> **Where we are.** `make prove-kopis` is GREEN (~7 s incremental, ~3.5 min clean) with the same
> **4** `sorry`s as before — the four core transform specs in `Ntt.lean`
> (`from_uniform_matrix_spec`, `from_secret_matrix_spec`, `ntt_mul_spec`,
> `ntt_mul_transpose_spec`). But the machinery to discharge them is now largely built:
>
> **DONE (committed, green, `sorry`-free):**
>
> 1. **`Kopis/Properties/NttMath.lean` — the pure-math layer.** The design decision that makes
>    this tractable: **no roots of unity, no bit-reversal, no Vandermonde.** The `ZETAS` table is
>    treated as *data*; the only things needed from it are three numeric relations, each a
>    `decide`d `Bool` check over a `List ℕ` copy of the table:
>      * root:    `ζ₁² = -1`
>      * CRT tree: `ζ_{2k}² = ζ_k`, `ζ_{2k+1}² = -ζ_k`
>      * GS pairing: `ζ_{nb+b} · ζ_{2·nb-1-b} = -1`
>    `zetas_val` bridges the table to `ExtractedRust` (needs `unseal arithmetic.ntt.ZETAS` — the
>    extracted table is `@[irreducible]`).
>    On top of that sits ONE invariant, `State nb m c f a` ("block `b` holds `f mod (X^m - c_{nb+b})`,
>    scaled by `c`"), with two step lemmas: `State_ct` (one Cooley-Tukey layer) and `State_gs`
>    (one Gentleman-Sande layer, which leaves the factor of 2 per layer that `INVNTT_SCALE`
>    cancels). Plus `cst_leaf_pow` (every leaf constant has `c²⁵⁶ = -1`) and `Ev_nconv`, the
>    convolution theorem.
>
> 2. **`NttReduceMont.lean` / `NttReduceBarrett.lean` / `NttReduceWrap.lean`** (collected by
>    `NttReduce.lean`, now **imported by `Kopis.lean`**) — the three reduction value specs.
>    These were bit-rotted *and* pathologically slow (~14 min, ~15 GB, then
>    `(kernel) deep recursion detected`). Now ~2 s each. Two fixes, both documented in
>    `NttReduce.lean` and worth remembering for any Aeneas WP proof:
>      * **`clear_value` after the value equations.** `set` leaves its abbreviations *let-bound*,
>        so the kernel zeta-expands them and reduces `BitVec` ops on 32-/64-bit literals inside
>        every later side condition.
>      * **Never let `omega` eliminate a division by a huge constant.** Restating Barrett's
>        bounds over the euclidean decomposition `x·M + 2⁴⁷ = q·2⁴⁸ + r` makes them linear, and
>        `linarith` closes them instantly.
>
> 3. **`Kopis/Properties/NttForward.lean` — the extracted forward butterfly network.** `aZ`/`aP`
>    read an `[i32; 256]` as a coefficient function / its residue; `mont_val_Zp` is the single
>    place the Montgomery representation is reasoned about. All three nested loops are proven:
>      * `ntt_inner_spec`  — one butterfly block (innermost loop)
>      * `ntt_mid_spec`    — every block at one level (middle loop)
>      * `ntt_outer_spec`  — all eight levels (outer loop), applying `State_ct` once per level
>    Conclusion: `arithmetic.ntt.ntt_loop0` takes `State 1 256 1 f` to `State 256 1 1 f`, i.e. the
>    extracted network really computes the CRT transform; magnitudes grow by at most `p` per
>    level, so eight levels from `|a| < 2¹⁶` stay well inside `i32`.
>
> 4. **`Kopis/Properties/NttForward.lean` — the whole forward transform, DONE.**
>    `ntt_inner_spec` (one butterfly block) → `ntt_mid_spec` (all blocks at one level) →
>    `ntt_outer_spec` (all eight levels, one `State_ct` per level) → `ntt_barrett_loop_spec`
>    (the closing `IterMut` Barrett pass) → **`ntt_full_spec`**: `arithmetic.ntt.ntt` on an input
>    bounded by `2¹⁶` yields `State 256 1 1 f` with every coefficient centred in `(-p, p)`.
>    Imported by `Kopis.lean`, so it is regression-protected.
>
> 5. **`Kopis/Properties/NttInverse.lean` — the Gentleman-Sande network, DONE up to the final
>    scaling loop.** `invntt_inner_spec` → `invntt_mid_spec` → `invntt_barrett_loop_spec` (the
>    mid-way pass) → `invntt_outer_spec` (all eight merge levels, one `State_gs` per level).
>    The magnitude schedule is `invBnd`: `p, 2p, 4p, 8p`, Barrett reset, `p, 2p, 4p, 8p`, ending
>    at `16p`.  **Watch out:** the loop-exit index `e = 8` needs `16p`, not `2^(e mod 4)·p` — an
>    earlier draft got this wrong and it is a real (caught) bug, not a proof-plumbing detail.
>
>    This file adds ONE axiom, `I64.wrapping_neg_spec`, because aeneas leaves
>    `core.num.I64.wrapping_neg` opaque (it is an `axiom` in `ExtractedRust.lean`, with no
>    definition to unfold).  It is registered in `TopLevelTheorems.lean`'s audited list next to
>    the two `count_ones` intrinsics.  **This assumption is avoidable and should be removed:**
>    writing `0i64.wrapping_sub(ZETAS[k] as i64)` instead of `(ZETAS[k] as i64).wrapping_neg()`
>    in `src/arithmetic/ntt.rs` extracts to `IScalar.wrapping_sub`, which aeneas gives real
>    semantics — that would drop both the opaque function and this axiom from the trust base.
>
> **NEXT STEPS, in order:**
>
> 1. DONE — `invntt_scale_loop_spec` and `invntt_full_spec` are proven.  **Both transform
>    networks are now complete end to end**: `ntt_full_spec` and `invntt_full_spec`.
> 2. `NttElem.from_uniform` / `from_secret` (each: a coefficient-widening loop then `ntt`),
>    `pointwise_mul_acc`, `reduce_invntt_to_ring_elem` (`mont_reduce`, then `invntt`, then
>    `to_wrapping_u16` — `to_wrapping_u16_spec` is already proved).
> 3. The matrix-level loops: `from_uniform_matrix`, `from_secret_matrix`, `mul`, `mul_transpose`.
> 4. De-opaque `nttInvU`/`nttInvS` in `Ntt.lean` and discharge the four `sorry`s, using
>    `Ev_nconv` (the convolution theorem) and `cst_leaf_pow`.  Then flip the
>    `TopLevelTheorems.lean` audit gate back to throwing on `sorryAx`.
>
> **Host notes.** 11 cores / 56 GB — the old 4 GB RAM constraint is gone; `LEAN_NUM_THREADS=8`
> is fine. Iterate with the Lean LSP MCP (`lean_diagnostic_messages` / `lean_goal`), not full
> `lake build`s: it is seconds instead of minutes.
>
> **Gotchas hit repeatedly, worth knowing:**
>   * `step*` leaves a `hmax` side goal per checked arithmetic op; putting the needed bound in
>     context *before* `step*` lets it discharge them itself.
>   * `omega` treats projections of an anonymous `Range` constructor (`{start := s, end := e}.start`)
>     as opaque atoms — add an explicit `rfl` bridge first.
>   * `step*` will auto-apply the theorem *currently being defined* when it sees a recursive call,
>     leaving stray implicit-argument goals. Use an explicit `let* ... spec` for that step.
>   * `all_goals` needs its tactic block on the *following* lines, indented; a multi-line
>     `all_goals have ... := by` on one line breaks parsing.
>   * A `-/` inside a doc comment (e.g. writing "32-/64-bit") silently closes the comment.
>   * With the 256-element `ZN` list literal in context, `scalar_tac` and `scalar_decr_tac` blow
>     the recursion limit trying to normalise it — use explicit bounds and `simp_wf; omega`.
>   * `hBu2 _ (by omega) (by omega)` fails when the index is a metavariable: give it explicitly.

---

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
