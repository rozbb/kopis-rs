# NTT + pubkey-refactor proof status

Status of the Lean correspondence proofs after three Rust changes landed on
`worktree-ntt-mult`: (1) multiplication moved to a negacyclic NTT over `p = 50330113`;
(2) the PKE public key now stores its serialized bytes (`vec_bytes`) instead of the
structured `Matrix<L,1>`; (3) the `gen` module was renamed `sample`.

This file is a working map, not audit surface. `TopLevelTheorems.lean` remains the audit
surface; its `#print axioms` gate is expected to FAIL until `ntt_spec` (below) is discharged.

## What builds now

Everything up to and including the abstract algebra bridges builds green:
`RingArith`, `MatrixArith`, `MulTranspose`, `MatrixMul` (schoolbook kept as the reference
impl), `GenMatrix`, `GenSecret*`, `Serialize*`, `MatVecMul`, `ProdBridge`, `ProdBridgeNT`,
`RoundTop`, `RoundR1/Rt`, `InnerProduct`, `Hash`, `Encrypt/DecryptGlue`, and `Ntt`.

Key surprise from the build: the NTT-domain change did **not** break the algebraic bridge
files. They prove spec-level lemmas (`Spec.Kopis.matVecMul`, `RoundToR10`, …) that never
mention the extracted multiplication. The NTT only meets the extracted code at the top-level
compositions, so breakage is concentrated there.

## What is broken, and why

The first failing target is `PkeSerialize`; everything downstream of it is *blocked*
(unattempted), so their errors are not yet visible. All breakage is one of two kinds:

**(a) Pubkey field change** — `PkePublicKey` is now `{matrix_seed, mat_a_ntt, vec_bytes, vec_ntt}`.
Proofs that referenced `pk.vec` / `pk.mat_a` no longer typecheck. Affected: `PkeSerialize`,
`PkeHash`, `PkeFromBytes`, the `pkStructBytes` definition (in `ExpandDecap.lean`), `KemFromBytes`,
`KemDecap`, `Impls`, and the `pk_serialize_matches_translation` / `pk_from_bytes_matches_spec`
statements in `TopLevelTheorems`.

**(b) NTT domain** — `expand_decap_key`, `encrypt_deterministic`, `decrypt` now call
`NttMatrix.from_uniform_matrix` / `from_secret_matrix` / `mul` / `mul_transpose` instead of
`Matrix.mul(_transpose)`. The proofs of `ExpandDecap`, `PkeEncryptTop`, `PkeDecryptTop` step
through the old schoolbook `matrix_mul_transpose_spec` and must be rewired to the NTT bridge.

## The plan agreed with the user (pubkey serialize/from_bytes)

- **Drop** `pk_from_bytes_matches_spec` (its conjuncts reference dead fields; it was a
  structural lemma). Rely on the existing behavioral `kopisXXX_from_bytes_then_encapsulate`
  as the from_bytes audit statement — it is bytes-in/bytes-out and already representation-agnostic.
- **Add** `serialize ∘ from_bytes = id` (any right-length input). Near-definitional now:
  `from_bytes` stores input bytes verbatim into `vec_bytes ++ matrix_seed`.
- **Restate** `pk_serialize_matches_translation` over `vec_bytes`: serialize emits
  `flatten(vec_bytes) ++ matrix_seed`.
- **Internal lemma** (unpacked-key invariant): `from_bytes` yields
  `deserialize_10(vec_bytes) = spec vector`, `vec_ntt = NTT(that)`, `mat_a_ntt = NTT(GenMat seed)`.

## The single mathematical hole: `ntt_spec`

The genuinely hard, deferred content is that the negacyclic NTT computes the ring product.
It is isolated as `Kopis.Properties.ntt_spec` in `Ntt.lean` (a precise statement, `sorry`ed —
never an `axiom`, so the audit gate reports it). Everything else — totality of the transform,
the pubkey byte layer, and all downstream rewiring — is intended to be real proof on top of it.

`ntt_spec` is stated at the `NttMatrix.mul(_transpose)` level with magnitude preconditions
(uniform operand `< 2^13`; secret operand `|·| ≤ μ/2`) and a schoolbook postcondition, so it is
a drop-in for `matrix_mul_transpose_spec`. Intended proof route (CRT split per butterfly level,
Montgomery/Barrett reduction specs, lazy-reduction bounds) is documented inline.

### Already proved toward it (in `Ntt.lean`)
- `bmod_i32_exact` / `bmod_i64_exact` and the six `I32/I64_wrapping_{add,sub,mul}_exact` corollaries:
  wrapping arithmetic is exact in range. This is the payoff of writing the NTT with explicit
  `wrapping_*`: the extracted arithmetic is total, so correctness reduces to "the value stayed
  in range", proved once via `Int.bmod` identity rather than 36 inline panic-freedom obligations.
- `fitsExactly` (joint `(ℓ,μ)` exactness constraint) + the three parameter instantiations +
  `margin_is_2304` + `worst_ell_with_worst_mu_does_not_fit` (why the constraint must be joint).
- `signedOfU16` and its mod-`2^16` agreement.

### Still needed for `ntt_spec`
- Reduction-function value specs: `mont_reduce`, `barrett_reduce`, `to_canonical`,
  `to_wrapping_u16`. These are concrete but require aeneas-scalar bit-vector plumbing
  (sign-mask AND, `sshiftRight`, cast `bmod`/`emod` semantics). The `*_exact` lemmas above are
  their arithmetic core.
- The transform correctness itself (butterfly network = evaluation at the roots; pointwise
  product = product in the split ring; INVNTT_SCALE cancels Montgomery + 1/256).
- **Magnitude lemmas** (the easy-to-miss obligation): `gen_matrix_from_seed` coeffs are `< 2^13`
  and `gen_secret_from_seed` coeffs are cbd-bounded, as *raw values*, not just residues. The
  existing specs abstract to `ZMod (2^13)` immediately and discard magnitude, which is exactly
  what the exactness bound needs. Needed to discharge `ntt_spec`'s preconditions downstream.

## Suggested order of attack for the remaining work

1. `Ntt.lean`: prove the four reduction specs; state + prove-modulo-`ntt_spec` the bridge
   (`ntt_mul_spec`, `ntt_mul_transpose_spec`, plus `from_uniform_matrix_spec` /
   `from_secret_matrix_spec` giving the NTT-repr relation, since `mat_a_ntt` and `vec_s_ntt`
   escape into the pubkey/secret key).
2. Magnitude lemmas for `gen_matrix` / `gen_secret`.
3. `PkeSerialize` (NTT-free; template is `MatrixSerialize.serialize_col_outer_spec`).
4. Redefine `pkStructBytes` over `vec_bytes`; fix `PkeHash`, `KeyGenHyps`.
5. `PkeFromBytes` + the round-trip.
6. `ExpandDecap`, `PkeEncryptTop`, `PkeDecryptTop` via the bridge + new pubkey construction.
7. `KemFromBytes`, `KemDecap`, `KemEncap`, `Impls`.
8. `TopLevelTheorems`: drop `pk_from_bytes_matches_spec`, restate serialize theorem, add round-trip.
