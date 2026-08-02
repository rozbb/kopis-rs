# NTT proof status

> ## ▶ DONE (updated 2026-08-01, branch `avx2`)
>
> **`make prove-kopis` is GREEN with ZERO `sorry`s, and the audit gate now throws on `sorryAx`.**
>
> The NTT-multiplication hole (`ntt_spec`) is fully discharged.  `#print axioms` on every §3
> theorem of `TopLevelTheorems.lean` no longer contains `sorryAx`, and the gate has been flipped
> back so that a `sorry` reappearing anywhere in the dependency closure *fails the build*.
> **Do not re-add an exemption for `sorryAx`.**
>
> The remaining trust base is exactly the audited list in `TrustBase.lean` (§4 of
> `TopLevelTheorems.lean` until 2026-08-02, when it moved): Lean's
> three logical axioms, the aeneas-opaque extern types/functions (turboshake, subtle,
> `count_ones`), and one `native_decide` in `Spec/Defs.lean:380`.
>
> ---
>
> ## Module map (bottom-up)
>
> | file | content |
> |---|---|
> | `NttMath.lean` | Pure mathematics. No Hoare triples. The `ZETAS` table as data, the CRT-tree constants `cst`, the `State` invariant with `State_ct`/`State_gs`, `cst_leaf_pow`, `Ev_nconv`, and the single-sum convolution `nconvR` with its ring-hom transport and magnitude bound. |
> | `NttReduce{Mont,Barrett,Wrap}.lean` | The three scalar reduction value specs (`mont_reduce`, `barrett_reduce`, `to_wrapping_u16`); `to_canonical_spec` is in `Ntt.lean`. |
> | `Ntt.lean` | Scalar groundwork: `pNtt`, `fitsExactly`, `signedOfU16`, the six `*_wrapping_*_exact` lemmas, `to_canonical_spec`, and the four raw-magnitude lemmas (`gen_matrix_uniformBounded`, `gen_secret_secretBounded`, `deserialize_10_uniformBounded`, `shift_right_uniformBounded`). |
> | `NttForward.lean` | `aZ`/`aP`, `mont_val_Zp`, the three butterfly loops and the Barrett pass → `ntt_full_spec`. |
> | `NttInverse.lean` | The Gentleman-Sande network, the mid-way Barrett pass, the `INVNTT_SCALE` pass → `invntt_full_spec`. |
> | `NttMul.lean` | `accZ`, `pointwise_mul_acc_spec` (exact `i64` multiply-accumulate) and `reduce_invntt_to_ring_elem_spec` (mont-reduce → `invntt` → `to_wrapping_u16`, including the mod-`p`-determines-the-integer exactness step). |
> | `NttBridge.lean` | `nttFwdU`/`nttFwdS`, the entrywise matrix-loop specs, `ntt_entry_spec` (the convolution theorem for one output element), and the six loops of `mul`/`mul_transpose` → `ntt_mul_spec` / `ntt_mul_transpose_spec`. |
>
> ## How the convolution theorem goes through
>
> 1. `nttFwdU A` / `nttFwdS s` are *forward* denotations: ordinary `def`s via `Result.getD`, not
>    `opaque` constants.  `nttFwdU_entry` / `nttFwdS_entry` say each entry satisfies `ElemOK f ne`
>    — `State 256 1 1 f (aP ne)` plus `|coefficient| < p` — where `f` is `uP`/`sP`, the unsigned
>    resp. signed reading of the stored `u16`s.  (`getD_of_spec`: any postcondition of a triple
>    already forces success, so it transfers verbatim to the total `Result.getD` value.  This is
>    the payoff of pointing the bridge forward — with the old `opaque` inverses these were not
>    merely unproven but *underivable*.)
> 2. `pointwise_mul_acc_spec`: the `i64` accumulator is exact.  Operands are centred mod-`p`, so
>    each product is `< p² ≈ 2.53·10¹⁵`, and `debug_assert!(Y <= MAX_L)` bounds the sum to four
>    terms — hence the `hY : Y.val ≤ 4` (resp. `hX`) hypothesis on the two public specs, which
>    call sites discharge from `hℓ : Spec.Kopis.ℓ p = L.val` by `cases p <;> decide`.
> 3. `ntt_entry_spec` is the whole of the mathematics, stated over two *arbitrary* families
>    `u`, `v` of ring elements so that one proof serves both `mul` and `mul_transpose`:
>    * `mont_reduce` on the accumulator gives `State 256 1 Rinv h (aP v1)` where `h = convP` is
>      the `ℤ/p` convolution — via `Ev_nconv` at each leaf constant (`cst_leaf_pow`) and
>      `Finset.sum_comm`;
>    * `invntt_full_spec` then yields `aP out = invScale · 2⁸ · Rinv · h = h`, because
>      `INVNTT_SCALE = 256⁻¹·2⁶⁴ mod p` cancels the Montgomery factor and the `2` per GS layer
>      exactly (`invScale_cancel`);
>    * `to_wrapping_u16` returns the centred representative; since the *integer* answer `convZ`
>      satisfies `|convZ| ≤ ⌊p/2⌋` (that is `fitsExactly`, via `abs_nconvR_le`) and both it and
>      the centred representative lie within `⌊p/2⌋` of zero while being congruent mod `p`, they
>      are **equal** — so the mod-`p` computation determines the integer answer, and reducing it
>      mod `2¹⁶` is the specification's answer.
> 4. `nconvR` — the convolution written as a single 256-term sum over an arbitrary `CommRing` —
>    is what lets the *same* definition be read over `ℤ` (the exactness bound), `ℤ/p` (where the
>    transform computes) and `ℤ/2¹⁶` (where the spec's `convCoeff` lives), related by
>    `nconvR_intCast` instead of three separate derivations.
>
> ## Lessons worth keeping (all of these cost real time)
>
> * **Rewrite the spec theorem, not the goal.**  `rw [hmata_ntt]` on the goal also rewrites the
>   *program* term, which breaks the `let*` matching of the very next step.  Instead:
>   `have hmt := …; rw [← hmata_ntt, ← hvecs_ntt] at hmt; let* ⟨prod, hprod0⟩ ← hmt`.
> * **`let*` splits bundled existentials** into witness-then-conjuncts, flattened.  A stale
>   destructuring pattern shows up as **`(deterministic) timeout at whnf`**, not as a type error.
>   Fix the pattern; do not raise `maxHeartbeats`.
> * A `"(deterministic) timeout at whnf"` on an `exact`/`rw` is usually a *wrong-term*
>   unification grind (e.g. stale hypothesis indices), not a proof needing a bigger budget.
> * **`clear_value` after `set`** in the reduction proofs, and **never let `omega` eliminate a
>   division by a huge constant** — restate over the euclidean decomposition and use `linarith`.
>   Together these took `NttReduce*` from ~14 min / ~15 GB (failing) to a few seconds each.
> * `step*` leaves a side goal per checked op named after the *hypothesis it could not
>   discharge*; put the needed bound in context **before** `step*` and address the rest with
>   `case hacc => …`.  Put `hend1 : iter1.«end».val = 256` in context before `step*` so it can
>   apply the recursive call itself.
> * **`by` inside `⟨…, …⟩` swallows the comma.**  `⟨fun … => by exfalso; omega, x⟩` parses the
>   whole tail as the tactic block.  Put the `by` last, or use `absurd`/`refine`.
> * **`rw ... at h` inside a nested `have … := by`** does not always reach `by`-arguments
>   elaborated in the same tactic: derive a *fresh* named hypothesis instead of mutating one.
> * `positivity` and `rw` can blow `maxRecDepth` on goals mentioning `pNtt` (a `def` that unfolds
>   to an eight-digit literal).  Prefer explicit `mul_nonneg`/`show`-with-numerals.
> * `omega` treats projections of an anonymous `Range` constructor as opaque atoms — add an
>   explicit `rfl` bridge, or supply the `if_pos`/`if_neg` argument with a full `show` type so the
>   pattern matches syntactically.
> * With the 256-element `ZN` list literal in context, `scalar_tac`/`scalar_decr_tac` blow the
>   recursion limit — use explicit bounds and `simp_wf; omega`.
> * A `-/` inside a doc comment (e.g. writing "32-/64-bit") silently closes the comment.
> * The forward-direction design makes proofs *simpler*, not harder: bound side-conditions go
>   from `(by rw [hmata_ntt]; exact hmatbnd)` to just `hmatbnd`.
>
> ## Do not undo
>
> * `src/arithmetic/ntt.rs:185` writes `0i64.wrapping_sub(ZETAS[k] as i64)`, **not**
>   `(ZETAS[k] as i64).wrapping_neg()`.  aeneas leaves `wrapping_neg` a bodiless `axiom`;
>   `wrapping_sub` gets real semantics.  "Simplifying" it back silently re-adds two trust-base
>   entries.
> * The three `kopisNNN_keygen` theorems are stated over their *observable* conjuncts (`z`,
>   `pkStructBytes`, `pkHash`).  `pke_sk` and `mat_a_ntt` are not observable and are pinned
>   behaviourally, and more strongly, by §3.2/§3.3 (keygen→encap, keygen→decap), which are
>   byte-level end to end.  The rationale is written up in the §3.1 doc block — keep it.
> * The audit gate throws on `sorryAx`.  Keep it that way.
>
> **Host notes.** 11 cores / 56 GB; `LEAN_NUM_THREADS=8` is fine.  Iterate with the Lean LSP MCP
> (`lean_diagnostic_messages` / `lean_goal`) or `lake env lean <file>`, not full `lake build`s.

---

## Background — what the refactor was

Three Rust changes landed on `worktree-ntt-mult`: (1) multiplication moved to a negacyclic NTT
over `p = 50330113`; (2) the PKE public key now stores its serialized bytes (`vec_bytes`) instead
of the structured `Matrix<L,1>`; (3) the `gen` module was renamed `sample`.

### Why an auxiliary prime works at all

The ring is `ℤ[X]/(X²⁵⁶+1)` with `u16` coefficients, which is *not* NTT-friendly.  Every Kopis
multiplication has one operand that is a CBD secret with coefficients in `[-μ/2, μ/2]`, while the
other has coefficients in `[0, 2^13)`.  So the coefficients of the *exact integer* negacyclic
convolution — even summed over an `ℓ`-term matrix row — are bounded by

    ℓ · 256 · (2^13 - 1) · (μ/2) ≤ 3 · 256 · 8191 · 4 = 25 162 752 < p/2 = 25 165 056.

Computing mod `p` therefore determines the integer answer exactly, and reducing that mod `2^16`
gives the `ZMod (2^16)` answer the spec asks for.  The margin is 2304 — 0.009% — which is why
`fitsExactly` carries the *joint* `(ℓ, μ)` constraint: the worst `ℓ = 4` with the worst `μ = 10`
would give 41 937 920, which does not fit.  Only the three shipped pairings do
(`fitsExactly_paramSet`, `margin_is_2304`, `worst_ell_with_worst_mu_does_not_fit`).

### The design decision that made it tractable

**No roots of unity, no bit-reversal, no Vandermonde.**  The `ZETAS` table is treated as *data*;
the only things needed from it are three numeric relations, each a `decide`d `Bool` check over a
`List ℕ` copy of the table:

* root:     `ζ₁² = -1`
* CRT tree: `ζ_{2k}² = ζ_k`, `ζ_{2k+1}² = -ζ_k`
* GS pairing: `ζ_{nb+b} · ζ_{2·nb-1-b} = -1`

`zetas_val` bridges the table to `ExtractedRustSerial` (needs `unseal arithmetic.ntt.ZETAS` — the
extracted table is `@[irreducible]`).  On top sits ONE invariant, `State nb m c f a`, with two
step lemmas `State_ct` / `State_gs`.  The factor of two per Gentleman-Sande layer is exactly what
`INVNTT_SCALE` cancels.

### Files rewired (real proof, no sorries)

`PkeSerialize`, `PkeHash`, `ExpandDecap`, `PkeEncryptTop`, `PkeDecryptTop`, `KeyGen`, `KemDecap`,
`KemEncap`, `Impls`, `KeyGenHyps`, `KeyGenCapstone`, `PkeFromBytes`, `KemFromBytes`,
`TopLevelTheorems`, plus the whole `Ntt*` stack above.

### Threading pattern

* The secret key is an `NttMatrix L 1`; a consumer names its coefficient matrix explicitly and
  carries an equation `stored = nttFwdS S`.  Facts about one stored object are bundled into a
  single existential, so no uniqueness lemma is ever needed.
* The public key carries `mat_a_ntt` / `vec_ntt` with `stored = nttFwdU A`; `UniformBounded`
  bounds are threaded from `gen_matrix` / `deserialize_10` / rounding, and `SecretBounded` from
  `gen_secret`.
* `expand_decap_key_spec` exposes the full WF (bounds + `vecBytesFlat = serialize(toVecN …)`) so
  the key-gen→encap/decap capstones can discharge the encap/decap hypotheses.

### Post-mortem — the `KeyGenCapstone` "perf hole" was a misdiagnosis

The three `kopisXXX_keygen_encap_spec` composites are real proofs at the ordinary 4M
`maxHeartbeats` (~1.3 s each).  They were once `sorry`ed and blamed on a heartbeat-nondeterministic
`whnf` blowup; that was wrong.  The real bug was **stale hypothesis indices** — the refactor added
a `SecretBounded` conjunct to `expand_from_seed_spec`, shifting the later conjuncts, so `exact h3`
was pointed at a `pkStructBytes = …` goal.  Lean `whnf`-grinds such a mismatch for >200M heartbeats
instead of failing fast.  Fixing the indices makes every `exact` a syntactic match.
