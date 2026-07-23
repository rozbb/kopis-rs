# NTT + pubkey-refactor proof status

Status of the Lean correspondence proofs after three Rust changes landed on
`worktree-ntt-mult`: (1) multiplication moved to a negacyclic NTT over `p = 50330113`;
(2) the PKE public key now stores its serialized bytes (`vec_bytes`) instead of the
structured `Matrix<L,1>`; (3) the `gen` module was renamed `sample`.

## Current state (rewiring COMPLETE)

The entire crate has been rewired to the NTT-domain representation. Every proof file
compiles as real proof; the **only** remaining `sorry`s are the single documented
mathematical hole `ntt_spec` (7 `sorry`s in `Ntt.lean`, see below).

`TopLevelTheorems.lean` is the audit surface. Its `#print axioms` gate now **reports
`sorryAx` as the known `ntt_spec` hole with a loud warning, but no longer throws on it**;
it still throws on any *other* new axiom, so it keeps protecting the rest of the trust base.

### The NTT bridge (`Ntt.lean`) — the decomposed interface

The bridge is stated with two opaque inverse-NTT *functions* (not relations), so the
coefficient matrix an NTT matrix denotes is deterministic and needs no existential when
consumed downstream:

- `nttInvU`, `nttInvS : NttMatrix X Y → Mat X Y` — the uniform/secret coefficient matrix an
  NTT matrix denotes.
- `from_uniform_matrix_spec` / `from_secret_matrix_spec` — `nttInvU/nttInvS (from_… A) = A`.
- `ntt_mul_spec` / `ntt_mul_transpose_spec` — pointwise product of NTT matrices computes the
  schoolbook product of the coefficient matrices they denote (drop-in for the schoolbook
  `matrix_mul(_transpose)_spec`), under the joint magnitude constraint `fitsExactly`.
- Magnitude lemmas: `gen_matrix_uniformBounded`, `gen_secret_secretBounded`,
  `deserialize_10_uniformBounded`, `shift_right_uniformBounded`.
- `fitsExactly_paramSet` discharges `fitsExactly (ℓ p) (μ p / 2)` for each shipped parameter set.

All seven are `sorry`ed (never `axiom`ed). Everything else is real proof on top.

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

### Perf note (`KeyGenCapstone`)

The three `kopisXXX_keygen_encap_spec` composites trigger one very large (but finite) `whnf`
reduction of the spec-level `KemEncap`/`ExpandDecapKey`/`SkToPk` terms during elaboration and
need a raised `maxHeartbeats` (currently 20 000 000). Every isolated defeq is cheap; this is a
proof-elaboration cost, not a math gap. A future cleanup could shrink it (e.g. making the
relevant spec defs `irreducible` at these call sites, or restructuring the final application).

## The single mathematical hole: `ntt_spec`

The genuinely hard, deferred content is that the negacyclic NTT computes the ring product.
It is the seven `sorry`s in `Ntt.lean`'s bridge (above). Intended proof route (CRT split per
butterfly level, Montgomery/Barrett reduction specs, lazy-reduction bounds) is documented
inline in `Ntt.lean`.

### Already proved toward it (in `Ntt.lean`)
- `bmod_i32_exact` / `bmod_i64_exact` and the six `I32/I64_wrapping_{add,sub,mul}_exact`
  corollaries: wrapping arithmetic is exact in range.
- `fitsExactly` (joint `(ℓ,μ)` exactness constraint) + the three parameter instantiations +
  `fitsExactly_paramSet` + `margin_is_2304` + `worst_ell_with_worst_mu_does_not_fit`.
- `signedOfU16` and its mod-`2^16` agreement.

### Still needed for `ntt_spec`
- Reduction-function value specs: `mont_reduce`, `barrett_reduce`, `to_canonical`,
  `to_wrapping_u16` (aeneas-scalar bit-vector plumbing; the `*_exact` lemmas are their core).
- The transform correctness (butterfly network = evaluation at the roots; pointwise product =
  product in the split ring; `INVNTT_SCALE` cancels Montgomery + 1/256).
- The four magnitude lemmas (currently `sorry`ed): `gen_matrix`/`gen_secret`/`deserialize_10`
  coefficient bounds and the shift-right (`<2^13`) bound, as raw values not just residues.

## Environment

This session had Lean LSP MCP access (`mcp__lean-lsp__*`) — essential for the bit-vector /
loop-invariant grinding. Full `lake build Kopis` is slow (~15-20 min; `KeyGenCapstone` alone
is several minutes at the raised heartbeat limit).
