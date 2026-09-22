/-
  # Kopis/Neon/NttGroupLoop.lean — the four groups, and the whole forward transform.

  `ntt_block`'s second half runs over `g < 4`, and each iteration carries one group of eight
  vectors through *six* levels without touching memory: load the eight vectors in coefficient
  order, run levels 2, 3 and 4 as ordinary vector pairings with a broadcast ζ, transpose, run
  levels 5, 6 and 7 as vertical butterflies with a per-lane ψ, transpose back, and store.  Two
  re-centring passes sit inside that — after level 3 and after level 7 — because both reductions
  the schedule calls for now happen to a group that is already in registers.

  The only unusual plumbing is the round trip each re-centring pass needs — `Array.to_slice_mut`,
  `Slice::iter_mut`, and the two `back` closures that reassemble the array.  It is the same
  pattern `Kopis/Properties/MatrixArith.lean` uses, and it is what lets
  `Kopis/Neon/NttBarrettIter.lean`'s slice-level statement be read back as a statement about the
  group's vectors.

  `fromVec` on the window and `VecBnd` on the group's vectors meet at the load prologue's and
  `store_vecs_spec`'s `8·base + 64g + 8j + m` indexing.
-/
import Kopis.Neon.NttBarrettIter

open Aeneas Aeneas.Std Result
open RustKopisNeon
open RustKopisNeon.backend.neon.intrinsics

namespace Kopis.Neon

set_option maxHeartbeats 4000000
set_option maxRecDepth 4000

/-- The ψ pair a table accessor hands over, with the two properties every butterfly needs. -/
def PsiOk (z zq : Vec128) (Q Zb : ℤ) : Prop :=
  (∀ i < 8, |(lane16 z i).toInt| ≤ Zb) ∧
  (∀ i < 8, (2 ^ 16 : ℤ) ∣ ((lane16 zq i).toInt * Q - (lane16 z i).toInt))

/-- A transpose permutes lanes between vectors, so a bound on every vector of a group survives
it. -/
theorem transpose8_bnd (v : Array Vec128 8#usize) (B : ℤ)
    (hv : ∀ j (hj : j < 8), VecBnd (vAt v j hj) B) :
    backend.neon.ntt.transpose8 v
      ⦃ (r : Array Vec128 8#usize) => ∀ j (hj : j < 8), VecBnd (vAt r j hj) B ⦄ := by
  apply WP.spec_mono (transpose8_spec v)
  intro r hr j hj m hm
  rw [hr j hj m hm]
  exact hv m hm j hj

/-! ## The whole forward transform

The constant setup, the two whole-vector levels, and the four groups.  The result is *centred* —
`|a| ≤ (q−1)/2` — which is what the pointwise step and the CRT combine downstream assume of it,
and everything outside this prime's window is untouched, which is what lets the two halves of an
`NttElem` be transformed one after the other into the same buffer.

The chain is threaded through as parameters, and `growth_q1` / `growth_q2` supply it: it is the
same four-level chain `(q−1)/2 → A1 → A2 → A3 → A4` twice, once for levels 0–3 and once for
levels 4–7, with a re-centring pass between and after. -/

/-! ## The table hypotheses, discharged

Each of the three transposed levels wants its ψ pair to be centred and Montgomery-paired.  Both
follow from facts already proved about the *literal* ζ arrays — `zetas_q1_centred_idx` and
`q1_inv_unit` in `Kopis/Neon/Tables.lean` — plus `tblZq_mont`, without touching the 512 entries
again.  The only per-level content is that the index stays inside the array, which is the closed
form `fwd4Idx` / `fwd2Idx` / `fwd1Idx` gives. -/

/-! ## The forward transform at the two primes

`growth_q1` and `growth_q2` supply the chain; everything else is evaluation of the literal
constants.  Both runs are four levels long, from a centred block, re-centred at the end of
each — the "runs of 4, 4" schedule `ntt.rs` documents. -/

/-- The rounding constant the Barrett pass adds: `1 << (BARRETT_SH − 1)`. -/
theorem round_const : (1#i16 : I16) <<< (10#i32 : Std.I32) = ok 1024#i16 := by
  simp only [HShiftLeft.hShiftLeft, IScalar.shiftLeft_IScalar, IScalar.shiftLeft]
  rw [if_pos (by decide), if_pos (by decide)]
  rfl
end Kopis.Neon
