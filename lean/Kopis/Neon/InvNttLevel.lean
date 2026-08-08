/-
  # Kopis/Neon/InvNttLevel.lean — the inverse transform's transposed levels.

  `invntt_block` runs the same eight levels backwards, blocked the way the forward transform is
  and mirrored: a group of eight vectors carries the first *six* levels — the three that live
  inside a vector (`len = 1`, 2, 4, in transposed form), a transpose back, and the three vector
  pairings at `len = 8`, 16 and 32 — and only the last two, whose partners lie outside the group,
  walk the whole block.  The three re-centring passes the schedule calls for, after levels 1, 3
  and 5, all happen inside the group.

  The butterflies are Gentleman-Sande — `(lo, hi) ↦ (lo + hi, ψ·(lo − hi))`.  The transposed
  levels read the negated ψ straight from `inv1`/`inv2`/`inv4`; the vector-pair levels build it
  at run time, which is what `neg_zeta` is.

  The bound shape differs from the forward direction and that is the only real change.  A
  Cooley-Tukey butterfly sends `B` to `B + T` in both outputs; a Gentleman-Sande one sends it to
  `2B` in the *sum* and to `T` in the *product*, which are different numbers.  So these lemmas
  carry a single `C` bounding both, with `2B ≤ C` and `T ≤ C` as hypotheses — the caller picks
  the max and the schedule arithmetic stays in `LevelStep`.
-/
import Kopis.Neon.NttGroupLoop

open Aeneas Aeneas.Std Result
open RustKopisNeon
open RustKopisNeon.backend.neon.intrinsics

namespace Kopis.Neon

set_option maxHeartbeats 1000000

/-! ## `wrapping_neg` — a *new* assumption, and it belongs in the trust base

The inverse transform does not read `zeta_q` from the precomputed table the way the forward one
does.  It negates the ζ at run time and multiplies by `crt::qinv`:

    neg_zeta = zeta(k).wrapping_neg();   zq = neg_zeta.wrapping_mul(qinv)

`wrapping_mul` is an ordinary aeneas definition, but **`core::num::{i16}::wrapping_neg` extracts
as an opaque axiom** — charon does not lower it — so its meaning has to be assumed, exactly as
`count_ones` does in `Kopis/Neon/CbdGeneric.lean`.  It is therefore a genuinely new item in this
backend's trust base and belongs in the NEON row of `TrustBase.lean` alongside the `count_ones`
pair, not a lemma that could be proved.

What is assumed is the obvious thing: two's-complement negation, i.e. the negation taken
`bmod 2¹⁶`.  On the values the transform feeds it — every ζ satisfies `|ζ| ≤ q/2 < 2¹⁵` — that is
exact negation, which `wrapping_neg_exact` below records. -/

@[step] axiom I16.wrapping_neg_spec (x : I16) :
    core.num.I16.wrapping_neg x ⦃ (r : I16) => r.val = (-x.val).bmod (2 ^ 16) ⦄

/-- On a centred ζ the wrapping negation is exact, and preserves the bound. -/
theorem wrapping_neg_exact (x : I16) (Zb : ℤ) (hZb : Zb ≤ 2 ^ 14) (hx : |x.val| ≤ Zb) :
    ∃ r : I16, core.num.I16.wrapping_neg x = ok r ∧ r.val = -x.val ∧ |r.val| ≤ Zb := by
  obtain ⟨r, hr, hrv⟩ := WP.spec_imp_exists (I16.wrapping_neg_spec x)
  rw [abs_le] at hx
  refine ⟨r, hr, ?_, ?_⟩
  · rw [hrv]
    unfold Int.bmod
    norm_num
    split <;> omega
  · rw [abs_le, hrv]
    unfold Int.bmod
    norm_num
    constructor <;> (split <;> omega)

/-! ## The run-time ψ pair, and the loops that repeat

`neg_zeta k` is `−ζ(k)` broadcast with its `q⁻¹`-scaled twin, built at run time rather than read
from a table.  It is what the three vector-pair levels inside the group and the two that cross
groups all use, so it is worth one spec.

The group also repeats three shapes — the re-centring pass, the `4h+i` pairing, and the `i, i+4`
pairing — and, as on the forward side, the repeated copies are the same fixpoint of the same
functional and are equal by unfolding. -/

/-- **`neg_zeta` broadcasts `−ζ(k)`,** with the Montgomery pairing every butterfly needs. -/
theorem neg_zeta_spec (SECOND : Bool) (Q Zb : ℤ) (kk : Usize)
    (zi : I16) (hzie : backend.crt.zeta SECOND kk = ok zi) (hzib : |zi.val| ≤ Zb)
    (hZb : Zb ≤ 2 ^ 14)
    (qic : I16) (hqinv : backend.crt.qinv SECOND = ok qic)
    (hqinvu : (2 ^ 16 : ℤ) ∣ (qic.val * Q - 1)) :
    ∃ z zq : Vec128, backend.neon.ntt.neg_zeta SECOND kk = ok (z, zq) ∧
      (∀ i < 8, (lane16 z i).toInt = -zi.val) ∧
      (∀ i < 8, |(lane16 z i).toInt| ≤ Zb) ∧
      (∀ i < 8, (2 ^ 16 : ℤ) ∣ ((lane16 zq i).toInt * Q - (lane16 z i).toInt)) := by
  obtain ⟨nz, hnze, hnzv, hnzb⟩ := wrapping_neg_exact zi Zb hZb hzib
  obtain ⟨z, hze, hzl⟩ := dup_n_s16_spec nz
  obtain ⟨zq, hzqe, hzql⟩ := dup_n_s16_spec (core.num.I16.wrapping_mul nz qic)
  refine ⟨z, zq, ?_, ?_, ?_, ?_⟩
  · unfold backend.neon.ntt.neg_zeta
    rw [hzie, bind_tc_ok]
    rw [hnze, bind_tc_ok]
    rw [hze, bind_tc_ok]
    rw [hqinv, bind_tc_ok]
    simp only [lift, bind_tc_ok]
    rw [hzqe, bind_tc_ok]
  · intro i hi; rw [hzl i hi]; exact hnzv
  · intro i hi; rw [hzl i hi]; exact hnzb
  · intro i hi
    rw [hzl i hi, hzql i hi]
    have h1 : ((core.num.I16.wrapping_mul nz qic).bv).toInt = tblZq nz.val qic.val := by
      show ((nz.bv * qic.bv : BitVec 16)).toInt = _
      rw [BitVec.toInt_mul]
      rfl
    rw [h1]
    exact tblZq_mont nz.val qic.val Q hqinvu

/-- The group's three re-centring passes are the same loop. -/
theorem invntt_loop0_loop5_eq :
    @backend.neon.ntt.invntt_block_loop0_loop5
      = @backend.neon.ntt.invntt_block_loop0_loop2 := by
  with_unfolding_all rfl

theorem invntt_loop0_loop8_eq :
    @backend.neon.ntt.invntt_block_loop0_loop8
      = @backend.neon.ntt.invntt_block_loop0_loop2 := by
  with_unfolding_all rfl

/-- Level 4's inner loop and the `len = 2` one are the same loop. -/
theorem invntt_loop0_loop6_loop0_eq :
    @backend.neon.ntt.invntt_block_loop0_loop6_loop0
      = @backend.neon.ntt.invntt_block_loop0_loop1_loop0 := by
  with_unfolding_all rfl

/-- Level 5's butterfly loop and the `len = 4` one are the same loop. -/
theorem invntt_loop0_loop7_eq :
    @backend.neon.ntt.invntt_block_loop0_loop7
      = @backend.neon.ntt.invntt_block_loop0_loop3 := by
  with_unfolding_all rfl

theorem invntt_len1_bnd (SECOND : Bool) (qv : Vec128) (Q Zb B Bt C : ℤ)
    (hQ : ∀ i < 8, (lane16 qv i).toInt = Q) (hQpos : 0 < Q) (hQlt : Q ≤ 2 ^ 14)
    (hZb : Zb ≤ 2 ^ 14)
    (hB0 : 0 ≤ B) (hBZ : 2 * B * Zb < 2 ^ 15 * Q)
    (hBt : 2 * B * Zb + 2 ^ 15 * Q ≤ 2 ^ 16 * Bt) (hfit : 2 * B ≤ 32767)
    (hC1 : 2 * B ≤ C) (hC2 : Bt ≤ C)
    (htbl : ∀ kk : Usize, kk.val < 16 → ∃ z zq : Vec128,
        backend.neon.ntt.inv1 SECOND kk = ok (z, zq) ∧
        (∀ i < 8, |(lane16 z i).toInt| ≤ Zb) ∧
        (∀ i < 8, (2 ^ 16 : ℤ) ∣ ((lane16 zq i).toInt * Q - (lane16 z i).toInt)))
    (g : Usize) (hg : g.val < 4) (v : Array Vec128 8#usize)
    (iter : core.ops.range.Range Usize) (hend : iter.«end».val = 4)
    (hv : ∀ j (hj : j < 8), pend1 iter.start.val j → VecBnd (vAt v j hj) B) :
    backend.neon.ntt.invntt_block_loop0_loop0 SECOND iter qv g v
      ⦃ (r : Array Vec128 8#usize) => ∀ j (hj : j < 8),
          if pend1 iter.start.val j then VecBnd (vAt r j hj) C
          else vAt r j hj = vAt v j hj ⦄ := by
  unfold backend.neon.ntt.invntt_block_loop0_loop0
  by_cases hlt : iter.start.val < iter.«end».val
  · let* ⟨ o, iter1, ho, hstart', hend' ⟩ ← core.iter.range.IteratorRange.next_Usize_some_spec
    rw [ho]
    simp only
    have hr4 : iter.start.val < 4 := by omega
    let* ⟨ i, hi ⟩ ← Std.Usize.mul_spec (x := 4#usize) (y := g) (by scalar_tac)
    let* ⟨ i1, hi1 ⟩ ← Std.Usize.add_spec (x := i) (y := iter.start) (by scalar_tac)
    obtain ⟨z, zq, hzt, hz, hzq⟩ := htbl i1 (by scalar_tac)
    rw [hzt, bind_tc_ok]
    let* ⟨ i2, hi2 ⟩ ← Std.Usize.mul_spec (x := 2#usize) (y := iter.start) (by scalar_tac)
    have hi2v : i2.val = 2 * iter.start.val := by scalar_tac
    let* ⟨ lo, hlo ⟩ ← Array.index_usize_spec v i2 (by scalar_tac)
    have hloe : lo = vAt v i2.val (by omega) := by rw [hlo]; rfl
    let* ⟨ i3, hi3 ⟩ ← Std.Usize.add_spec (x := i2) (y := 1#usize) (by scalar_tac)
    have hi3v : i3.val = i2.val + 1 := by scalar_tac
    let* ⟨ hiv, hhi ⟩ ← Array.index_usize_spec v i3 (by scalar_tac)
    have hhie : hiv = vAt v i3.val (by omega) := by rw [hhi]; rfl
    apply WP.spec_bind (gs_butterfly_spec lo hiv z zq qv Q Zb B Bt hQ hQpos hQlt hz hZb hzq
      (by rw [hloe]; exact hv _ (by omega) ⟨by omega, by omega⟩)
      (by rw [hhie]; exact hv _ (by omega) ⟨by omega, by omega⟩)
      hB0 hBZ hBt hfit)
    rintro ⟨lo1, hi1'⟩ ⟨hlo1b', hhi1b', -⟩
    have hlo1b : VecBnd lo1 C := hlo1b'.mono hC1
    have hhi1b : VecBnd hi1' C := hhi1b'.mono hC2
    show (do let v1 ← Array.update v i2 lo1
             let i4 ← i2 + 1#usize
             let a ← Array.update v1 i4 hi1'
             backend.neon.ntt.invntt_block_loop0_loop0 SECOND iter1 qv g a)
        ⦃ (r : Array Vec128 8#usize) => ∀ j (hj : j < 8),
            if pend1 iter.start.val j then VecBnd (vAt r j hj) C
            else vAt r j hj = vAt v j hj ⦄
    let* ⟨ v1, hv1 ⟩ ← Array.update_spec
    let* ⟨ i4, hi4 ⟩ ← Std.Usize.add_spec (x := i2) (y := 1#usize) (by scalar_tac)
    have hi4v : i4.val = i2.val + 1 := by scalar_tac
    let* ⟨ a, ha ⟩ ← Array.update_spec
    have hav : ∀ j (hj : j < 8), vAt a j hj =
        if j = i4.val then hi1' else if j = i2.val then lo1 else vAt v j hj := by
      intro j hj
      rw [ha, vAt_set, hv1, vAt_set]
    apply WP.spec_mono (invntt_len1_bnd SECOND qv Q Zb B Bt C hQ hQpos hQlt hZb hB0 hBZ hBt hfit hC1 hC2 htbl
      g hg a iter1 (by rw [hend']; exact hend) (by
        intro j hj hpend
        rw [hav j hj, if_neg (by unfold pend1 at hpend; omega),
          if_neg (by unfold pend1 at hpend; omega)]
        exact hv j hj (by unfold pend1 at hpend ⊢; omega)))
    intro r hr j hj
    have hrj := hr j hj
    by_cases hpend : pend1 iter.start.val j
    · rw [if_pos hpend]
      by_cases hnext : pend1 iter1.start.val j
      · rw [if_pos hnext] at hrj
        exact hrj
      · rw [if_neg hnext, hav j hj] at hrj
        rw [hrj]
        by_cases hj1 : j = i4.val
        · rw [if_pos hj1]; exact hhi1b
        · rw [if_neg hj1, if_pos (by unfold pend1 at hpend hnext; omega)]
          exact hlo1b
    · rw [if_neg hpend]
      rw [if_neg (by unfold pend1 at hpend ⊢; omega), hav j hj,
        if_neg (by unfold pend1 at hpend; omega),
        if_neg (by unfold pend1 at hpend; omega)] at hrj
      exact hrj
  · let* ⟨ o, iter1, hnone, _ ⟩ ← core.iter.range.IteratorRange.next_Usize_none_spec
    rw [hnone]
    refine (WP.spec_ok _).mpr (fun j hj => ?_)
    rw [if_neg (by unfold pend1; omega)]
termination_by iter.«end».val - iter.start.val
decreasing_by scalar_decr_tac


/-! ## `len = 2`, inverse -/

theorem invntt_len2_bnd (qv z zq : Vec128) (Q Zb B Bt C : ℤ)
    (hQ : ∀ i < 8, (lane16 qv i).toInt = Q) (hQpos : 0 < Q) (hQlt : Q ≤ 2 ^ 14)
    (hz : ∀ i < 8, |(lane16 z i).toInt| ≤ Zb) (hZb : Zb ≤ 2 ^ 14)
    (hzq : ∀ i < 8, (2 ^ 16 : ℤ) ∣ ((lane16 zq i).toInt * Q - (lane16 z i).toInt))
    (hB0 : 0 ≤ B) (hBZ : 2 * B * Zb < 2 ^ 15 * Q)
    (hBt : 2 * B * Zb + 2 ^ 15 * Q ≤ 2 ^ 16 * Bt) (hfit : 2 * B ≤ 32767)
    (hC1 : 2 * B ≤ C) (hC2 : Bt ≤ C)
    (v : Array Vec128 8#usize) (h : Usize) (hh : h.val < 2)
    (iter : core.ops.range.Range Usize) (hend : iter.«end».val = 2)
    (hv : ∀ j (hj : j < 8), pend2 h.val iter.start.val j → VecBnd (vAt v j hj) B) :
    backend.neon.ntt.invntt_block_loop0_loop1_loop0 iter qv v h z zq
      ⦃ (r : Array Vec128 8#usize) => ∀ j (hj : j < 8),
          if pend2 h.val iter.start.val j then VecBnd (vAt r j hj) C
          else vAt r j hj = vAt v j hj ⦄ := by
  unfold backend.neon.ntt.invntt_block_loop0_loop1_loop0
  by_cases hlt : iter.start.val < iter.«end».val
  · let* ⟨ o, iter1, ho, hstart', hend' ⟩ ← core.iter.range.IteratorRange.next_Usize_some_spec
    rw [ho]
    simp only
    have hi2 : iter.start.val < 2 := by omega
    let* ⟨ i1, hi1 ⟩ ← Std.Usize.mul_spec (x := 4#usize) (y := h) (by scalar_tac)
    let* ⟨ base, hbase ⟩ ← Std.Usize.add_spec (x := i1) (y := iter.start) (by scalar_tac)
    have hbv : base.val = 4 * h.val + iter.start.val := by scalar_tac
    let* ⟨ lo, hlo ⟩ ← Array.index_usize_spec v base (by scalar_tac)
    have hloe : lo = vAt v base.val (by omega) := by rw [hlo]; rfl
    let* ⟨ i2, hi2v ⟩ ← Std.Usize.add_spec (x := base) (y := 2#usize) (by scalar_tac)
    have hi2vv : i2.val = base.val + 2 := by scalar_tac
    let* ⟨ hiv, hhi ⟩ ← Array.index_usize_spec v i2 (by scalar_tac)
    have hhie : hiv = vAt v i2.val (by omega) := by rw [hhi]; rfl
    apply WP.spec_bind (gs_butterfly_spec lo hiv z zq qv Q Zb B Bt hQ hQpos hQlt hz hZb hzq
      (by rw [hloe]; exact hv _ (by omega) (Or.inl ⟨by omega, by omega⟩))
      (by rw [hhie]; exact hv _ (by omega) (Or.inr ⟨by omega, by omega⟩))
      hB0 hBZ hBt hfit)
    rintro ⟨lo1, hi1'⟩ ⟨hlo1b', hhi1b', -⟩
    have hlo1b : VecBnd lo1 C := hlo1b'.mono hC1
    have hhi1b : VecBnd hi1' C := hhi1b'.mono hC2
    show (do let v1 ← Array.update v base lo1
             let a ← Array.update v1 i2 hi1'
             backend.neon.ntt.invntt_block_loop0_loop1_loop0 iter1 qv a h z zq)
        ⦃ (r : Array Vec128 8#usize) => ∀ j (hj : j < 8),
            if pend2 h.val iter.start.val j then VecBnd (vAt r j hj) C
            else vAt r j hj = vAt v j hj ⦄
    let* ⟨ v1, hv1 ⟩ ← Array.update_spec
    let* ⟨ a, ha ⟩ ← Array.update_spec
    have hav : ∀ j (hj : j < 8), vAt a j hj =
        if j = i2.val then hi1' else if j = base.val then lo1 else vAt v j hj := by
      intro j hj
      rw [ha, vAt_set, hv1, vAt_set]
    apply WP.spec_mono (invntt_len2_bnd qv z zq Q Zb B Bt C hQ hQpos hQlt hz hZb hzq hB0 hBZ hBt hfit hC1 hC2
      a h hh iter1 (by rw [hend']; exact hend) (by
        intro j hj hpend
        rw [hav j hj, if_neg (by unfold pend2 at hpend; omega),
          if_neg (by unfold pend2 at hpend; omega)]
        exact hv j hj (by unfold pend2 at hpend ⊢; omega)))
    intro r hr j hj
    have hrj := hr j hj
    by_cases hpend : pend2 h.val iter.start.val j
    · rw [if_pos hpend]
      by_cases hnext : pend2 h.val iter1.start.val j
      · rw [if_pos hnext] at hrj
        exact hrj
      · rw [if_neg hnext, hav j hj] at hrj
        rw [hrj]
        by_cases hj1 : j = i2.val
        · rw [if_pos hj1]; exact hhi1b
        · rw [if_neg hj1, if_pos (by unfold pend2 at hpend hnext; omega)]
          exact hlo1b
    · rw [if_neg hpend]
      rw [if_neg (by unfold pend2 at hpend ⊢; omega), hav j hj,
        if_neg (by unfold pend2 at hpend; omega),
        if_neg (by unfold pend2 at hpend; omega)] at hrj
      exact hrj
  · let* ⟨ o, iter1, hnone, _ ⟩ ← core.iter.range.IteratorRange.next_Usize_none_spec
    rw [hnone]
    refine (WP.spec_ok _).mpr (fun j hj => ?_)
    rw [if_neg (by unfold pend2; omega)]
termination_by iter.«end».val - iter.start.val
decreasing_by scalar_decr_tac


/-! ## `len = 4`, inverse -/

theorem invntt_len4_bnd (qv z zq : Vec128) (Q Zb B Bt C : ℤ)
    (hQ : ∀ i < 8, (lane16 qv i).toInt = Q) (hQpos : 0 < Q) (hQlt : Q ≤ 2 ^ 14)
    (hz : ∀ i < 8, |(lane16 z i).toInt| ≤ Zb) (hZb : Zb ≤ 2 ^ 14)
    (hzq : ∀ i < 8, (2 ^ 16 : ℤ) ∣ ((lane16 zq i).toInt * Q - (lane16 z i).toInt))
    (hB0 : 0 ≤ B) (hBZ : 2 * B * Zb < 2 ^ 15 * Q)
    (hBt : 2 * B * Zb + 2 ^ 15 * Q ≤ 2 ^ 16 * Bt) (hfit : 2 * B ≤ 32767)
    (hC1 : 2 * B ≤ C) (hC2 : Bt ≤ C)
    (v : Array Vec128 8#usize) (iter : core.ops.range.Range Usize) (hend : iter.«end».val = 4)
    (hv : ∀ j (hj : j < 8), pend4 iter.start.val j → VecBnd (vAt v j hj) B) :
    backend.neon.ntt.invntt_block_loop0_loop3 iter qv v z zq
      ⦃ (r : Array Vec128 8#usize) => ∀ j (hj : j < 8),
          if pend4 iter.start.val j then VecBnd (vAt r j hj) C
          else vAt r j hj = vAt v j hj ⦄ := by
  unfold backend.neon.ntt.invntt_block_loop0_loop3
  by_cases hlt : iter.start.val < iter.«end».val
  · let* ⟨ o, iter1, ho, hstart', hend' ⟩ ← core.iter.range.IteratorRange.next_Usize_some_spec
    rw [ho]
    simp only
    have hi4 : iter.start.val < 4 := by omega
    let* ⟨ lo, hlo ⟩ ← Array.index_usize_spec v iter.start (by scalar_tac)
    have hloe : lo = vAt v iter.start.val (by omega) := by rw [hlo]; rfl
    let* ⟨ i1, hi1 ⟩ ← Std.Usize.add_spec (x := iter.start) (y := 4#usize) (by scalar_tac)
    have hi1v : i1.val = iter.start.val + 4 := by scalar_tac
    let* ⟨ hiv, hhi ⟩ ← Array.index_usize_spec v i1 (by scalar_tac)
    have hhie : hiv = vAt v i1.val (by omega) := by rw [hhi]; rfl
    apply WP.spec_bind (gs_butterfly_spec lo hiv z zq qv Q Zb B Bt hQ hQpos hQlt hz hZb hzq
      (by rw [hloe]; exact hv _ (by omega) (Or.inl ⟨by omega, by omega⟩))
      (by rw [hhie]; exact hv _ (by omega) (Or.inr ⟨by omega, by omega⟩))
      hB0 hBZ hBt hfit)
    rintro ⟨lo1, hi1'⟩ ⟨hlo1b', hhi1b', -⟩
    have hlo1b : VecBnd lo1 C := hlo1b'.mono hC1
    have hhi1b : VecBnd hi1' C := hhi1b'.mono hC2
    show (do let v1 ← Array.update v iter.start lo1
             let a ← Array.update v1 i1 hi1'
             backend.neon.ntt.invntt_block_loop0_loop3 iter1 qv a z zq)
        ⦃ (r : Array Vec128 8#usize) => ∀ j (hj : j < 8),
            if pend4 iter.start.val j then VecBnd (vAt r j hj) C
            else vAt r j hj = vAt v j hj ⦄
    let* ⟨ v1, hv1 ⟩ ← Array.update_spec
    let* ⟨ a, ha ⟩ ← Array.update_spec
    -- what `a` is, entry by entry
    have hav : ∀ j (hj : j < 8), vAt a j hj =
        if j = i1.val then hi1' else if j = iter.start.val then lo1 else vAt v j hj := by
      intro j hj
      rw [ha, vAt_set, hv1, vAt_set]
    apply WP.spec_mono (invntt_len4_bnd qv z zq Q Zb B Bt C hQ hQpos hQlt hz hZb hzq hB0 hBZ hBt hfit hC1 hC2
      a iter1 (by rw [hend']; exact hend) (by
        intro j hj hpend
        rw [hav j hj, if_neg (by unfold pend4 at hpend; omega),
          if_neg (by unfold pend4 at hpend; omega)]
        exact hv j hj (by unfold pend4 at hpend ⊢; omega)))
    intro r hr j hj
    have hrj := hr j hj
    by_cases hpend : pend4 iter.start.val j
    · rw [if_pos hpend]
      by_cases hnext : pend4 iter1.start.val j
      · rw [if_pos hnext] at hrj
        exact hrj
      · rw [if_neg hnext, hav j hj] at hrj
        rw [hrj]
        by_cases hj1 : j = i1.val
        · rw [if_pos hj1]; exact hhi1b
        · rw [if_neg hj1, if_pos (by unfold pend4 at hpend hnext; omega)]
          exact hlo1b
    · rw [if_neg hpend]
      rw [if_neg (by unfold pend4 at hpend ⊢; omega), hav j hj,
        if_neg (by unfold pend4 at hpend; omega),
        if_neg (by unfold pend4 at hpend; omega)] at hrj
      exact hrj
  · let* ⟨ o, iter1, hnone, _ ⟩ ← core.iter.range.IteratorRange.next_Usize_none_spec
    rw [hnone]
    refine (WP.spec_ok _).mpr (fun j hj => ?_)
    rw [if_neg (by unfold pend4; omega)]
termination_by iter.«end».val - iter.start.val
decreasing_by scalar_decr_tac


/-! ## The inverse re-centring pass -/

/-- **The inverse transform's transposed re-centring pass.**  Same loop, different extracted
constant: `invntt_block` re-centres after its levels 2 and 4 where `ntt_block` re-centres after
its level 6, and aeneas gives each occurrence its own name.  Every vector of the group comes out with
`2·|r| < q`, so `|r| ≤ (q−1)/2` — which is the bound the last two levels start from. -/
theorem invntt_barrett_iter_bnd (iter : core.slice.iter.IterMut Vec128)
    (back : core.slice.iter.IterMut Vec128 → core.slice.iter.IterMut Vec128)
    (bm round qv : Vec128) (Q M : ℤ)
    (hQ : ∀ i < 8, (lane16 qv i).toInt = Q) (hM : ∀ i < 8, (lane16 bm i).toInt = M)
    (hRnd : ∀ i < 8, (lane16 round i).toInt = 2 ^ 10)
    (hQpos : 0 < Q) (hQlt : Q < 2 ^ 14) (hQodd : ¬ (2 ∣ Q))
    (hMpos : 0 < M) (hMlt : M < 2 ^ 15) (hD : |2 ^ 27 - Q * M| ≤ 2047)
    (h_len8 : iter.slice.val.length = 8) (h_iter_i : iter.i ≤ 8)
    (hback_len : ∀ (im : core.slice.iter.IterMut Vec128),
      im.slice.val.length = 8 → (back im).slice.val.length = 8)
    (hback_writes : ∀ (im : core.slice.iter.IterMut Vec128)
      (_him : im.slice.val.length = 8) (j : ℕ) (_hj : j < iter.i)
      (hb : j < (back im).slice.val.length),
        VecBnd (sAt (back im).slice j hb) ((Q - 1) / 2))
    (hback_rest : ∀ (im : core.slice.iter.IterMut Vec128)
      (_him : im.slice.val.length = 8) (j : ℕ) (_hge : iter.i ≤ j)
      (hb : j < (back im).slice.val.length) (hb' : j < im.slice.val.length),
        sAt (back im).slice j hb = sAt im.slice j hb') :
    backend.neon.ntt.invntt_block_loop0_loop2 iter back qv bm round
      ⦃ (r : core.slice.iter.IterMut Vec128 ×
             (core.slice.iter.IterMut Vec128 → core.slice.iter.IterMut Vec128)) =>
          r.1.slice.val.length = 8 ∧
          ∀ (im : core.slice.iter.IterMut Vec128), im.slice.val.length = 8 →
            (r.2 im).slice.val.length = 8 ∧
            ∀ (j : ℕ) (hj : j < (r.2 im).slice.val.length),
              VecBnd (sAt (r.2 im).slice j hj) ((Q - 1) / 2) ⦄ := by
  unfold backend.neon.ntt.invntt_block_loop0_loop2
  by_cases hlt : iter.i < iter.slice.len
  · let* ⟨ o, iter1, next_back, h_all ⟩ ← CbdGeneric.iter_mut_next_spec
    obtain ⟨ho, hit2_slice, hit2_i, hnb_none, hnb_some⟩ := h_all
    rw [ho]
    simp only []
    have hii : iter.i < 8 := by
      have h := hlt
      rw [← h_len8]
      simpa [Slice.len, Slice.length] using h
    apply WP.spec_bind (barrett_lane_spec _ bm round qv Q M hQ hM hRnd hQpos hQlt hQodd
      hMpos hMlt hD)
    intro slot1 hslot1
    have hslotb : VecBnd slot1 ((Q - 1) / 2) := by
      intro i hi
      have := (hslot1 i hi).2
      omega
    have hnbs : ∀ im : core.slice.iter.IterMut Vec128,
        (next_back im (some slot1)).slice = im.slice.setAtNat iter.i slot1 := by
      intro im
      rw [hnb_some im slot1]
    have hlen' : ∀ (im : core.slice.iter.IterMut Vec128), im.slice.val.length = 8 →
        (next_back im (some slot1)).slice.val.length = 8 := by
      intro im him
      rw [hnbs im]
      simpa [Slice.setAtNat] using him
    apply WP.spec_mono (invntt_barrett_iter_bnd iter1
      (fun im => back (next_back im (some slot1))) bm round qv Q M hQ hM hRnd hQpos hQlt hQodd
      hMpos hMlt hD (by rw [hit2_slice]; exact h_len8) (by omega)
      (fun im him => hback_len _ (hlen' im him))
      (by
        intro im him j hj hb
        by_cases hje : j = iter.i
        · have hbm : j < (next_back im (some slot1)).slice.val.length := by
            rw [hlen' im him]; omega
          rw [hback_rest (next_back im (some slot1)) (hlen' im him) j (by omega) hb hbm]
          have hset : ∀ (h1 : j < (im.slice.setAtNat iter.i slot1).val.length),
              sAt (next_back im (some slot1)).slice j hbm
                = sAt (im.slice.setAtNat iter.i slot1) j h1 := by
            intro h1
            simp only [hnbs im]
          rw [hset (by rw [← hnbs im]; exact hbm),
            sAt_setAtNat im.slice iter.i slot1 j _ (by omega), if_pos hje]
          exact hslotb
        · exact hback_writes (next_back im (some slot1)) (hlen' im him) j (by omega) hb)
      (by
        intro im him j hge hb hb'
        have hbm : j < (next_back im (some slot1)).slice.val.length := by
          rw [hlen' im him]; omega
        rw [hback_rest (next_back im (some slot1)) (hlen' im him) j (by omega) hb hbm]
        have hset : ∀ (h1 : j < (im.slice.setAtNat iter.i slot1).val.length),
            sAt (next_back im (some slot1)).slice j hbm
              = sAt (im.slice.setAtNat iter.i slot1) j h1 := by
          intro h1
          simp only [hnbs im]
        rw [hset (by rw [← hnbs im]; exact hbm),
          sAt_setAtNat im.slice iter.i slot1 j _ hb', if_neg (by omega)]))
    rintro ⟨r1, r2⟩ hr
    exact hr
  · let* ⟨ o, iter1, next_back, h_all ⟩ ← CbdGeneric.iter_mut_next_spec_none
    obtain ⟨ho, hit_eq, hnb⟩ := h_all
    rw [ho]
    have hi8 : iter.i = 8 := by
      have hnot : ¬ (iter.i < 8) := by
        have h := hlt
        rw [← h_len8]
        simpa [Slice.len, Slice.length] using h
      omega
    refine (WP.spec_ok _).mpr ⟨by rw [hit_eq]; exact h_len8, fun im him => ?_⟩
    simp only [hnb]
    exact ⟨hback_len im him, fun j hj => hback_writes im him j
      (by rw [hback_len im him] at hj; omega) hj⟩

/-! ## The two halves of the inverse `len = 2` level -/

theorem invntt_len2_outer_bnd (SECOND : Bool) (qv : Vec128) (Q Zb B Bt C : ℤ)
    (hQ : ∀ i < 8, (lane16 qv i).toInt = Q) (hQpos : 0 < Q) (hQlt : Q ≤ 2 ^ 14)
    (hZb : Zb ≤ 2 ^ 14)
    (hB0 : 0 ≤ B) (hBZ : 2 * B * Zb < 2 ^ 15 * Q)
    (hBt : 2 * B * Zb + 2 ^ 15 * Q ≤ 2 ^ 16 * Bt) (hfit : 2 * B ≤ 32767)
    (hC1 : 2 * B ≤ C) (hC2 : Bt ≤ C) (hCB : B ≤ C)
    (htbl : ∀ kk : Usize, kk.val < 8 → ∃ z zq : Vec128,
        backend.neon.ntt.inv2 SECOND kk = ok (z, zq) ∧
        (∀ i < 8, |(lane16 z i).toInt| ≤ Zb) ∧
        (∀ i < 8, (2 ^ 16 : ℤ) ∣ ((lane16 zq i).toInt * Q - (lane16 z i).toInt)))
    (g : Usize) (hg : g.val < 4) (v : Array Vec128 8#usize)
    (iter : core.ops.range.Range Usize) (hend : iter.«end».val = 2)
    (hv : ∀ j (hj : j < 8), 4 * iter.start.val ≤ j → VecBnd (vAt v j hj) B) :
    backend.neon.ntt.invntt_block_loop0_loop1 SECOND iter qv g v
      ⦃ (r : Array Vec128 8#usize) => ∀ j (hj : j < 8),
          if 4 * iter.start.val ≤ j then VecBnd (vAt r j hj) C
          else vAt r j hj = vAt v j hj ⦄ := by
  unfold backend.neon.ntt.invntt_block_loop0_loop1
  by_cases hlt : iter.start.val < iter.«end».val
  · let* ⟨ o, iter1, ho, hstart', hend' ⟩ ← core.iter.range.IteratorRange.next_Usize_some_spec
    rw [ho]
    simp only
    have hh2 : iter.start.val < 2 := by omega
    let* ⟨ i, hi ⟩ ← Std.Usize.mul_spec (x := 2#usize) (y := g) (by scalar_tac)
    let* ⟨ i1, hi1 ⟩ ← Std.Usize.add_spec (x := i) (y := iter.start) (by scalar_tac)
    obtain ⟨z, zq, hzt, hz, hzq⟩ := htbl i1 (by scalar_tac)
    rw [hzt, bind_tc_ok]
    apply WP.spec_bind (invntt_len2_bnd qv z zq Q Zb B Bt C hQ hQpos hQlt hz hZb hzq hB0 hBZ hBt
      hfit hC1 hC2 v iter.start hh2 ⟨0#usize, 2#usize⟩ rfl (by
        intro j hj hpend
        exact hv j hj (by unfold pend2 at hpend; scalar_tac)))
    intro v1 hv1
    apply WP.spec_mono (invntt_len2_outer_bnd SECOND qv Q Zb B Bt C hQ hQpos hQlt hZb hB0 hBZ
      hBt hfit hC1 hC2 hCB htbl g hg v1 iter1 (by rw [hend']; exact hend) (by
        intro j hj hge
        have := hv1 j hj
        rw [if_neg (by unfold pend2; scalar_tac)] at this
        rw [this]
        exact hv j hj (by omega)))
    intro r hr j hj
    have hrj := hr j hj
    by_cases hge : 4 * iter.start.val ≤ j
    · rw [if_pos hge]
      by_cases hge1 : 4 * iter1.start.val ≤ j
      · rw [if_pos hge1] at hrj
        exact hrj
      · rw [if_neg hge1] at hrj
        rw [hrj]
        have := hv1 j hj
        rw [if_pos (by unfold pend2; scalar_tac)] at this
        exact this
    · rw [if_neg hge]
      rw [if_neg (by omega)] at hrj
      rw [hrj]
      have := hv1 j hj
      rw [if_neg (by unfold pend2; scalar_tac)] at this
      exact this
  · let* ⟨ o, iter1, hnone, _ ⟩ ← core.iter.range.IteratorRange.next_Usize_none_spec
    rw [hnone]
    refine (WP.spec_ok _).mpr (fun j hj => ?_)
    rw [if_neg (by scalar_tac)]
termination_by 2 - iter.start.val
decreasing_by scalar_decr_tac

/-! ## The inverse transform's whole-vector levels

The last five levels of `invntt_block` pair whole vectors, exactly as the first five of
`ntt_block` do.  The only change is Gentleman-Sande's asymmetric bound — `2B` in the sum, `Bt`
in the product — which a single `C` covers. -/

/-- **One whole-vector level of the inverse, as a bound.**  Gentleman-Sande, so the two outputs
have different bounds — `2B` in the sum, `Bt` in the product — and a single `C` covers both. -/
theorem invntt_inner_bnd (b : Array I16 256#usize) (qv z zq : Vec128) (Q Zb B Bt C : ℤ)
    (hQ : ∀ i < 8, (lane16 qv i).toInt = Q) (hQpos : 0 < Q) (hQlt : Q ≤ 2 ^ 14)
    (hz : ∀ i < 8, |(lane16 z i).toInt| ≤ Zb) (hZb : Zb ≤ 2 ^ 14)
    (hzq : ∀ i < 8, (2 ^ 16 : ℤ) ∣ ((lane16 zq i).toInt * Q - (lane16 z i).toInt))
    (hB0 : 0 ≤ B) (hBZ : 2 * B * Zb < 2 ^ 15 * Q)
    (hBt : 2 * B * Zb + 2 ^ 15 * Q ≤ 2 ^ 16 * Bt) (hfit : 2 * B ≤ 32767)
    (hC1 : 2 * B ≤ C) (hC2 : Bt ≤ C)
    (half start i : Usize) (hhalf : 1 ≤ half.val)
    (hrange : start.val + 2 * half.val ≤ 32) (hstart : start.val ≤ i.val)
    (hb : ∀ p < 256, pending start.val half.val i.val p → |(b.val[p]!).val| ≤ B) :
    backend.neon.ntt.invntt_block_loop1_loop0_loop0 b qv half start z zq i
      ⦃ (r : Array I16 256#usize) => ∀ p < 256,
          if pending start.val half.val i.val p then |(r.val[p]!).val| ≤ C
          else (r.val[p]!).val = (b.val[p]!).val ⦄ := by
  unfold backend.neon.ntt.invntt_block_loop1_loop0_loop0
  let* ⟨ i1, hi1 ⟩ ← Std.Usize.add_spec (x := start) (y := half) (by scalar_tac)
  by_cases hlt : i < i1
  · rw [if_pos hlt]
    have hiv : i.val < start.val + half.val := by scalar_tac
    -- the two halves of this butterfly, both still bounded by `B`
    obtain ⟨lo, hlo, hlol⟩ := load_i16_val b i (by omega)
    rw [hlo, bind_tc_ok]
    let* ⟨ i2, hi2 ⟩ ← Std.Usize.add_spec (x := i) (y := half) (by scalar_tac)
    obtain ⟨hiv2, -⟩ : i2.val = i.val + half.val ∧ True := ⟨by scalar_tac, trivial⟩
    obtain ⟨hi', hhi, hhil⟩ := load_i16_val b i2 (by omega)
    rw [hhi, bind_tc_ok]
    have hlob : VecBnd lo B := by
      intro k hk
      rw [hlol k hk]
      exact hb _ (by omega) (Or.inl ⟨by omega, by omega⟩)
    have hhib : VecBnd hi' B := by
      intro k hk
      rw [hhil k hk, hiv2]
      exact hb _ (by omega) (Or.inr ⟨by omega, by omega⟩)
    apply WP.spec_bind (gs_butterfly_spec lo hi' z zq qv Q Zb B Bt hQ hQpos hQlt hz hZb hzq
      hlob hhib hB0 hBZ hBt hfit)
    rintro ⟨lo1, hi1'⟩ ⟨hlo1b', hhi1b', -⟩
    have hlo1b : VecBnd lo1 C := hlo1b'.mono hC1
    have hhi1b : VecBnd hi1' C := hhi1b'.mono hC2
    show (do let b1 ← backend.neon.intrinsics.store_i16 b i lo1
             let b2 ← backend.neon.intrinsics.store_i16 b1 i2 hi1'
             let i3 ← i + 1#usize
             backend.neon.ntt.invntt_block_loop1_loop0_loop0 b2 qv half start z zq i3)
        ⦃ (r : Array I16 256#usize) => ∀ p < 256,
            if pending start.val half.val i.val p then |(r.val[p]!).val| ≤ C
            else (r.val[p]!).val = (b.val[p]!).val ⦄
    obtain ⟨b1, hb1, hb1v⟩ := store_i16_val b i lo1 (by omega)
    rw [hb1, bind_tc_ok]
    obtain ⟨b2, hb2, hb2v⟩ := store_i16_val b1 i2 hi1' (by omega)
    rw [hb2, bind_tc_ok]
    let* ⟨ i3, hi3 ⟩ ← Std.Usize.add_spec (x := i) (y := 1#usize) (by scalar_tac)
    -- what `b2` looks like, in one statement
    have hb2all : ∀ p < 256, (b2.val[p]!).val =
        if 8 * i.val ≤ p ∧ p < 8 * i.val + 8 then (lane16 lo1 (p - 8 * i.val)).toInt
        else if 8 * i2.val ≤ p ∧ p < 8 * i2.val + 8 then
          (lane16 hi1' (p - 8 * i2.val)).toInt
        else (b.val[p]!).val := by
      intro p hp
      rw [hb2v p hp, hb1v p hp]
      by_cases h2 : 8 * i2.val ≤ p ∧ p < 8 * i2.val + 8
      · rw [if_pos h2, if_neg (by scalar_tac), if_pos h2]
      · rw [if_neg h2, if_neg h2]
    -- the pending coefficients of the *next* iteration are still bounded by `B`
    apply WP.spec_mono (invntt_inner_bnd b2 qv z zq Q Zb B Bt C hQ hQpos hQlt hz hZb hzq hB0 hBZ
      hBt hfit hC1 hC2 half start i3 hhalf hrange (by scalar_tac) (by
        intro p hp hpend
        rw [hb2all p hp, if_neg (by unfold pending at hpend; scalar_tac),
          if_neg (by unfold pending at hpend; scalar_tac)]
        exact hb p hp (by unfold pending at hpend ⊢; scalar_tac)))
    intro r hr p hp
    have hrp := hr p hp
    by_cases hpend : pending start.val half.val i.val p
    · rw [if_pos hpend]
      by_cases hnext : pending start.val half.val i3.val p
      · rw [if_pos hnext] at hrp
        exact hrp
      · rw [if_neg hnext, hb2all p hp] at hrp
        rw [hrp]
        by_cases h1 : 8 * i.val ≤ p ∧ p < 8 * i.val + 8
        · rw [if_pos h1]
          exact hlo1b _ (by omega)
        · rw [if_neg h1]
          have h2 : 8 * i2.val ≤ p ∧ p < 8 * i2.val + 8 := by
            unfold pending at hpend hnext; scalar_tac
          rw [if_pos h2]
          exact hhi1b _ (by omega)
    · rw [if_neg hpend]
      rw [if_neg (by unfold pending at hpend ⊢; scalar_tac), hb2all p hp,
        if_neg (by unfold pending at hpend; scalar_tac),
        if_neg (by unfold pending at hpend; scalar_tac)] at hrp
      exact hrp
  · rw [if_neg hlt]
    refine (WP.spec_ok _).mpr (fun p hp => ?_)
    rw [if_neg (by unfold pending; scalar_tac)]
termination_by (start.val + half.val) - i.val
decreasing_by scalar_decr_tac


/-! ## The blocks of one inverse whole-vector level

`start` walks the block boundaries as in the forward direction, but `k` walks *down* and the ψ
pair is built at run time rather than read from a table — `−ζ(k)` and its wrapping product with
`q⁻¹`.  That is the whole difference, and it is why this is not an instance of
`ntt_start_bnd`. -/

theorem invntt_start_bnd (SECOND : Bool) (b : Array I16 256#usize) (qv : Vec128)
    (Q Zb B Bt C : ℤ)
    (hQ : ∀ i < 8, (lane16 qv i).toInt = Q) (hQpos : 0 < Q) (hQlt : Q ≤ 2 ^ 14)
    (hZb : Zb ≤ 2 ^ 14)
    (hB0 : 0 ≤ B) (hBZ : 2 * B * Zb < 2 ^ 15 * Q)
    (hBt : 2 * B * Zb + 2 ^ 15 * Q ≤ 2 ^ 16 * Bt) (hfit : 2 * B ≤ 32767)
    (hC1 : 2 * B ≤ C) (hC2 : Bt ≤ C)
    (hzeta : ∀ kk : Usize, kk.val < 256 → ∃ zi : I16,
        backend.crt.zeta SECOND kk = ok zi ∧ |zi.val| ≤ Zb)
    (qic : I16) (hqinv : backend.crt.qinv SECOND = ok qic)
    (hqinvu : (2 ^ 16 : ℤ) ∣ (qic.val * Q - 1))
    (iv k half start : Usize) (hiv : iv.val = 32)
    (hhalf : 1 ≤ half.val) (hhalfdvd : 2 * half.val ∣ 32) (hdvd : 2 * half.val ∣ start.val)
    (hk : 32 - start.val ≤ k.val * (2 * half.val)) (hk256 : k.val ≤ 256)
    (hb : ∀ p < 256, 8 * start.val ≤ p → |(b.val[p]!).val| ≤ B) :
    backend.neon.ntt.invntt_block_loop1_loop0 SECOND iv b qv k half start
      ⦃ (r : Array I16 256#usize × Usize) =>
          r.2.val + (32 - start.val) / (2 * half.val) = k.val ∧ ∀ p < 256,
            if 8 * start.val ≤ p then |(r.1.val[p]!).val| ≤ C
            else (r.1.val[p]!).val = (b.val[p]!).val ⦄ := by
  unfold backend.neon.ntt.invntt_block_loop1_loop0
  by_cases hlt : start < iv
  · rw [if_pos hlt]
    have hs32 : start.val < 32 := by scalar_tac
    have hh16 : 2 * half.val ≤ 32 := Nat.le_of_dvd (by omega) hhalfdvd
    have hfits : start.val + 2 * half.val ≤ 32 := by
      obtain ⟨c, hc⟩ := hdvd
      obtain ⟨d, hd⟩ := hhalfdvd
      have hcd : c + 1 ≤ d := by
        by_contra hcon
        have hdc : d ≤ c := by omega
        have : 2 * half.val * d ≤ 2 * half.val * c := Nat.mul_le_mul_left _ hdc
        omega
      have hmul : 2 * half.val * (c + 1) ≤ 2 * half.val * d := Nat.mul_le_mul_left _ hcd
      calc start.val + 2 * half.val = 2 * half.val * (c + 1) := by rw [hc]; ring
        _ ≤ 2 * half.val * d := hmul
        _ = 32 := hd.symm
    have hkpos : 1 ≤ k.val := by
      by_contra hcon
      have hk0 : k.val = 0 := by omega
      rw [hk0] at hk
      simp at hk
      omega
    let* ⟨ k1, hk1 ⟩ ← Std.Usize.sub_spec (x := k) (y := 1#usize) (by scalar_tac)
    have hmul : k1.val * (2 * half.val) + 2 * half.val = k.val * (2 * half.val) := by
      have hkk : k.val = k1.val + 1 := by scalar_tac
      rw [hkk]; ring
    obtain ⟨zi, hzie, hzib⟩ := hzeta k1 (by scalar_tac)
    obtain ⟨z, zq, hnz, -, hzlv, hzqlv⟩ :=
      neg_zeta_spec SECOND Q Zb k1 zi hzie hzib hZb qic hqinv hqinvu
    rw [hnz, bind_tc_ok]
    apply WP.spec_bind (invntt_inner_bnd b qv z zq Q Zb B Bt C hQ hQpos hQlt hzlv hZb hzqlv hB0
      hBZ hBt hfit hC1 hC2 half start start hhalf hfits (le_refl _) (by
        intro p hp hpend
        exact hb p hp (by unfold pending at hpend; omega)))
    intro b1 hb1
    let* ⟨ i4, hi4 ⟩ ← Std.Usize.mul_spec (x := 2#usize) (y := half) (by scalar_tac)
    let* ⟨ start1, hstart1 ⟩ ← Std.Usize.add_spec (x := start) (y := i4) (by scalar_tac)
    have hs1v : start1.val = start.val + 2 * half.val := by scalar_tac
    apply WP.spec_mono (invntt_start_bnd SECOND b1 qv Q Zb B Bt C hQ hQpos hQlt hZb hB0 hBZ hBt
      hfit hC1 hC2 hzeta qic hqinv hqinvu iv k1 half start1 hiv hhalf hhalfdvd
      (by rw [hs1v]; exact Nat.dvd_add hdvd dvd_rfl) (by omega) (by scalar_tac) (by
        intro p hp hge
        have := hb1 p hp
        rw [if_neg (by unfold pending; omega)] at this
        rw [this]
        exact hb p hp (by omega)))
    rintro ⟨r, kk⟩ ⟨hkk, hr⟩
    refine ⟨?_, fun p hp => ?_⟩
    · have hdvd32 : 2 * half.val ∣ (32 - start.val) := Nat.dvd_sub hhalfdvd hdvd
      have hstep : (32 - start.val) / (2 * half.val)
          = (32 - start1.val) / (2 * half.val) + 1 := by
        obtain ⟨c, hc⟩ := hdvd32
        have hc1 : 1 ≤ c := by
          rcases Nat.eq_zero_or_pos c with rfl | h
          · omega
          · exact h
        have h2 : 32 - start1.val = 2 * half.val * (c - 1) := by
          rw [hs1v, Nat.mul_sub, ← hc]; omega
        rw [hc, h2, Nat.mul_div_cancel_left _ (by omega), Nat.mul_div_cancel_left _ (by omega)]
        omega
      rw [hstep] at *
      scalar_tac
    have hrp := hr p hp
    by_cases hge : 8 * start.val ≤ p
    · rw [if_pos hge]
      by_cases hge1 : 8 * start1.val ≤ p
      · rw [if_pos hge1] at hrp
        exact hrp
      · rw [if_neg hge1] at hrp
        rw [hrp]
        have := hb1 p hp
        rw [if_pos (by unfold pending; omega)] at this
        exact this
    · rw [if_neg hge]
      rw [if_neg (by omega)] at hrp
      rw [hrp]
      have := hb1 p hp
      rw [if_neg (by unfold pending; omega)] at this
      exact this
  · rw [if_neg hlt]
    have hge32 : 32 ≤ start.val := by scalar_tac
    have hz0 : (32 - start.val) / (2 * half.val) = 0 := by
      apply Nat.div_eq_of_lt
      omega
    refine (WP.spec_ok _).mpr ⟨by rw [hz0]; simp, fun p hp => ?_⟩
    rw [if_neg (by scalar_tac)]
termination_by 32 - start.val
decreasing_by scalar_decr_tac

/-! ## What one inverse level needs, bundled

`invntt_start_bnd` takes six separate arithmetic hypotheses; a level loop supplies all six from
one `LevelStep` plus the two `C` inequalities, so bundling them keeps the unrolling readable.
Note `hfit` is *derived* rather than supplied: `LevelStep Q Zb (2B) T` gives `2B + T ≤ 32767`,
and `0 ≤ T` turns that into the `2B ≤ 32767` the block loop wants. -/

def GSLevel (Q Zb B T C : ℤ) : Prop :=
  (2 * B * Zb < 2 ^ 15 * Q ∧ 2 * B * Zb + 2 ^ 15 * Q ≤ 2 ^ 16 * T ∧ 2 * B ≤ 32767) ∧
    0 ≤ T ∧ 2 * B ≤ C ∧ T ≤ C

theorem GSLevel.bz {Q Zb B T C : ℤ} (h : GSLevel Q Zb B T C) : 2 * B * Zb < 2 ^ 15 * Q := h.1.1
theorem GSLevel.bt {Q Zb B T C : ℤ} (h : GSLevel Q Zb B T C) :
    2 * B * Zb + 2 ^ 15 * Q ≤ 2 ^ 16 * T := h.1.2.1
theorem GSLevel.fit {Q Zb B T C : ℤ} (h : GSLevel Q Zb B T C) : 2 * B ≤ 32767 := h.1.2.2
theorem GSLevel.c1 {Q Zb B T C : ℤ} (h : GSLevel Q Zb B T C) : 2 * B ≤ C := h.2.2.1
theorem GSLevel.c2 {Q Zb B T C : ℤ} (h : GSLevel Q Zb B T C) : T ≤ C := h.2.2.2

/-- `half` doubles each inverse level, and the product is not `rfl` — same reason
`usize_add_one` exists on the forward side. -/
theorem usize_mul_two (a c : Usize) (h : a.val * 2 = c.val) : a * 2#usize = ok c := by
  obtain ⟨v, hv, hvv⟩ :=
    WP.spec_imp_exists (Std.Usize.mul_spec (x := a) (y := 2#usize) (by scalar_tac))
  rw [hv]
  congr 1
  exact UScalar.eq_of_val_eq (by scalar_tac)

/-- Reading a block bound out of the block loop's postcondition at `start = 0`. -/
theorem blockBnd_of_inv_start {r bb : Array I16 256#usize} {B' : ℤ}
    (h : ∀ p < 256, if 8 * (0#usize).val ≤ p then |(r.val[p]!).val| ≤ B'
                    else (r.val[p]!).val = (bb.val[p]!).val) : BlockBnd r B' := by
  intro p hp
  have := h p hp
  rwa [if_pos (by scalar_tac)] at this

theorem usize_add_one' (a c : Usize) (h : a.val + 1 = c.val) : a + 1#usize = ok c := by
  obtain ⟨v, hv, hvv⟩ :=
    WP.spec_imp_exists (Std.Usize.add_spec (x := a) (y := 1#usize) (by scalar_tac))
  rw [hv]
  congr 1
  exact UScalar.eq_of_val_eq (by scalar_tac)

/-! ## Levels 3 and 4, inverse direction

These two run after the transpose back, on vector pairs one and two apart, and take a broadcast
`−ζ` rather than a per-lane table entry — the Gentleman-Sande table walks downwards, so the ψ
indices are `31 − 4g − r` and `15 − 2g − h`.  Level 5 pairs `i` with `i + 4` and so is
`invntt_len4_bnd` with a broadcast ψ; it needs nothing new. -/

theorem invntt_lvl3_bnd (SECOND : Bool) (qv : Vec128) (Q Zb B Bt C : ℤ)
    (hQ : ∀ i < 8, (lane16 qv i).toInt = Q) (hQpos : 0 < Q) (hQlt : Q ≤ 2 ^ 14)
    (hZb : Zb ≤ 2 ^ 14)
    (hB0 : 0 ≤ B) (hBZ : 2 * B * Zb < 2 ^ 15 * Q)
    (hBt : 2 * B * Zb + 2 ^ 15 * Q ≤ 2 ^ 16 * Bt) (hfit : 2 * B ≤ 32767)
    (hC1 : 2 * B ≤ C) (hC2 : Bt ≤ C)
    (hzeta : ∀ kk : Usize, kk.val < 256 → ∃ zi : I16,
        backend.crt.zeta SECOND kk = ok zi ∧ |zi.val| ≤ Zb)
    (qic : I16) (hqinv : backend.crt.qinv SECOND = ok qic)
    (hqinvu : (2 ^ 16 : ℤ) ∣ (qic.val * Q - 1))
    (g : Usize) (hg : g.val < 4) (v : Array Vec128 8#usize)
    (iter : core.ops.range.Range Usize) (hend : iter.«end».val = 4)
    (hv : ∀ j (hj : j < 8), pend1 iter.start.val j → VecBnd (vAt v j hj) B) :
    backend.neon.ntt.invntt_block_loop0_loop4 SECOND iter qv g v
      ⦃ (r : Array Vec128 8#usize) => ∀ j (hj : j < 8),
          if pend1 iter.start.val j then VecBnd (vAt r j hj) C
          else vAt r j hj = vAt v j hj ⦄ := by
  unfold backend.neon.ntt.invntt_block_loop0_loop4
  by_cases hlt : iter.start.val < iter.«end».val
  · let* ⟨ o, iter1, ho, hstart', hend' ⟩ ← core.iter.range.IteratorRange.next_Usize_some_spec
    rw [ho]
    simp only
    have hr4 : iter.start.val < 4 := by omega
    let* ⟨ i, hi ⟩ ← Std.Usize.mul_spec (x := 4#usize) (y := g) (by scalar_tac)
    let* ⟨ i1, hi1 ⟩ ← Std.Usize.sub_spec (x := 31#usize) (y := i) (by scalar_tac)
    let* ⟨ kk, hkk ⟩ ← Std.Usize.sub_spec (x := i1) (y := iter.start) (by scalar_tac)
    obtain ⟨zi, hzie, hzib⟩ := hzeta kk (by scalar_tac)
    obtain ⟨z, zq, hnz, -, hz, hzq⟩ :=
      neg_zeta_spec SECOND Q Zb kk zi hzie hzib hZb qic hqinv hqinvu
    rw [hnz, bind_tc_ok]
    let* ⟨ i2, hi2 ⟩ ← Std.Usize.mul_spec (x := 2#usize) (y := iter.start) (by scalar_tac)
    have hi2v : i2.val = 2 * iter.start.val := by scalar_tac
    let* ⟨ lo, hlo ⟩ ← Array.index_usize_spec v i2 (by scalar_tac)
    have hloe : lo = vAt v i2.val (by omega) := by rw [hlo]; rfl
    let* ⟨ i3, hi3 ⟩ ← Std.Usize.add_spec (x := i2) (y := 1#usize) (by scalar_tac)
    have hi3v : i3.val = i2.val + 1 := by scalar_tac
    let* ⟨ hiv, hhi ⟩ ← Array.index_usize_spec v i3 (by scalar_tac)
    have hhie : hiv = vAt v i3.val (by omega) := by rw [hhi]; rfl
    apply WP.spec_bind (gs_butterfly_spec lo hiv z zq qv Q Zb B Bt hQ hQpos hQlt hz hZb hzq
      (by rw [hloe]; exact hv _ (by omega) ⟨by omega, by omega⟩)
      (by rw [hhie]; exact hv _ (by omega) ⟨by omega, by omega⟩)
      hB0 hBZ hBt hfit)
    rintro ⟨lo1, hi1'⟩ ⟨hlo1b', hhi1b', -⟩
    have hlo1b : VecBnd lo1 C := hlo1b'.mono hC1
    have hhi1b : VecBnd hi1' C := hhi1b'.mono hC2
    show (do let v1 ← Array.update v i2 lo1
             let i4 ← i2 + 1#usize
             let a ← Array.update v1 i4 hi1'
             backend.neon.ntt.invntt_block_loop0_loop4 SECOND iter1 qv g a)
        ⦃ (r : Array Vec128 8#usize) => ∀ j (hj : j < 8),
            if pend1 iter.start.val j then VecBnd (vAt r j hj) C
            else vAt r j hj = vAt v j hj ⦄
    let* ⟨ v1, hv1 ⟩ ← Array.update_spec
    let* ⟨ i4, hi4 ⟩ ← Std.Usize.add_spec (x := i2) (y := 1#usize) (by scalar_tac)
    have hi4v : i4.val = i2.val + 1 := by scalar_tac
    let* ⟨ a, ha ⟩ ← Array.update_spec
    have hav : ∀ j (hj : j < 8), vAt a j hj =
        if j = i4.val then hi1' else if j = i2.val then lo1 else vAt v j hj := by
      intro j hj
      rw [ha, vAt_set, hv1, vAt_set]
    apply WP.spec_mono (invntt_lvl3_bnd SECOND qv Q Zb B Bt C hQ hQpos hQlt hZb hB0 hBZ hBt hfit
      hC1 hC2 hzeta qic hqinv hqinvu g hg a iter1 (by rw [hend']; exact hend) (by
        intro j hj hpend
        rw [hav j hj, if_neg (by unfold pend1 at hpend; omega),
          if_neg (by unfold pend1 at hpend; omega)]
        exact hv j hj (by unfold pend1 at hpend ⊢; omega)))
    intro r hr j hj
    have hrj := hr j hj
    by_cases hpend : pend1 iter.start.val j
    · rw [if_pos hpend]
      by_cases hnext : pend1 iter1.start.val j
      · rw [if_pos hnext] at hrj
        exact hrj
      · rw [if_neg hnext, hav j hj] at hrj
        rw [hrj]
        by_cases hj1 : j = i4.val
        · rw [if_pos hj1]; exact hhi1b
        · rw [if_neg hj1, if_pos (by unfold pend1 at hpend hnext; omega)]
          exact hlo1b
    · rw [if_neg hpend]
      rw [if_neg (by unfold pend1 at hpend ⊢; omega), hav j hj,
        if_neg (by unfold pend1 at hpend; omega),
        if_neg (by unfold pend1 at hpend; omega)] at hrj
      exact hrj
  · let* ⟨ o, iter1, hnone, _ ⟩ ← core.iter.range.IteratorRange.next_Usize_none_spec
    rw [hnone]
    refine (WP.spec_ok _).mpr (fun j hj => ?_)
    rw [if_neg (by unfold pend1; omega)]
termination_by iter.«end».val - iter.start.val
decreasing_by scalar_decr_tac

theorem invntt_lvl4_bnd (SECOND : Bool) (qv : Vec128) (Q Zb B Bt C : ℤ)
    (hQ : ∀ i < 8, (lane16 qv i).toInt = Q) (hQpos : 0 < Q) (hQlt : Q ≤ 2 ^ 14)
    (hZb : Zb ≤ 2 ^ 14)
    (hB0 : 0 ≤ B) (hBZ : 2 * B * Zb < 2 ^ 15 * Q)
    (hBt : 2 * B * Zb + 2 ^ 15 * Q ≤ 2 ^ 16 * Bt) (hfit : 2 * B ≤ 32767)
    (hC1 : 2 * B ≤ C) (hC2 : Bt ≤ C) (hCB : B ≤ C)
    (hzeta : ∀ kk : Usize, kk.val < 256 → ∃ zi : I16,
        backend.crt.zeta SECOND kk = ok zi ∧ |zi.val| ≤ Zb)
    (qic : I16) (hqinv : backend.crt.qinv SECOND = ok qic)
    (hqinvu : (2 ^ 16 : ℤ) ∣ (qic.val * Q - 1))
    (g : Usize) (hg : g.val < 4) (v : Array Vec128 8#usize)
    (iter : core.ops.range.Range Usize) (hend : iter.«end».val = 2)
    (hv : ∀ j (hj : j < 8), 4 * iter.start.val ≤ j → VecBnd (vAt v j hj) B) :
    backend.neon.ntt.invntt_block_loop0_loop6 SECOND iter qv g v
      ⦃ (r : Array Vec128 8#usize) => ∀ j (hj : j < 8),
          if 4 * iter.start.val ≤ j then VecBnd (vAt r j hj) C
          else vAt r j hj = vAt v j hj ⦄ := by
  unfold backend.neon.ntt.invntt_block_loop0_loop6
  by_cases hlt : iter.start.val < iter.«end».val
  · let* ⟨ o, iter1, ho, hstart', hend' ⟩ ← core.iter.range.IteratorRange.next_Usize_some_spec
    rw [ho]
    simp only
    have hh2 : iter.start.val < 2 := by omega
    let* ⟨ i, hi ⟩ ← Std.Usize.mul_spec (x := 2#usize) (y := g) (by scalar_tac)
    let* ⟨ i1, hi1 ⟩ ← Std.Usize.sub_spec (x := 15#usize) (y := i) (by scalar_tac)
    let* ⟨ kk, hkk ⟩ ← Std.Usize.sub_spec (x := i1) (y := iter.start) (by scalar_tac)
    obtain ⟨zi, hzie, hzib⟩ := hzeta kk (by scalar_tac)
    obtain ⟨z, zq, hnz, -, hz, hzq⟩ :=
      neg_zeta_spec SECOND Q Zb kk zi hzie hzib hZb qic hqinv hqinvu
    rw [hnz, bind_tc_ok, invntt_loop0_loop6_loop0_eq]
    apply WP.spec_bind (invntt_len2_bnd qv z zq Q Zb B Bt C hQ hQpos hQlt hz hZb hzq hB0 hBZ hBt
      hfit hC1 hC2 v iter.start hh2 ⟨0#usize, 2#usize⟩ rfl (by
        intro j hj hpend
        exact hv j hj (by unfold pend2 at hpend; scalar_tac)))
    intro v1 hv1
    apply WP.spec_mono (invntt_lvl4_bnd SECOND qv Q Zb B Bt C hQ hQpos hQlt hZb hB0 hBZ
      hBt hfit hC1 hC2 hCB hzeta qic hqinv hqinvu g hg v1 iter1 (by rw [hend']; exact hend) (by
        intro j hj hge
        have := hv1 j hj
        rw [if_neg (by unfold pend2; scalar_tac)] at this
        rw [this]
        exact hv j hj (by omega)))
    intro r hr j hj
    have hrj := hr j hj
    by_cases hge : 4 * iter.start.val ≤ j
    · rw [if_pos hge]
      by_cases hge1 : 4 * iter1.start.val ≤ j
      · rw [if_pos hge1] at hrj
        exact hrj
      · rw [if_neg hge1] at hrj
        rw [hrj]
        have := hv1 j hj
        rw [if_pos (by unfold pend2; scalar_tac)] at this
        exact this
    · rw [if_neg hge]
      rw [if_neg (by omega)] at hrj
      rw [hrj]
      have := hv1 j hj
      rw [if_neg (by unfold pend2; scalar_tac)] at this
      exact this
  · let* ⟨ o, iter1, hnone, _ ⟩ ← core.iter.range.IteratorRange.next_Usize_none_spec
    rw [hnone]
    refine (WP.spec_ok _).mpr (fun j hj => ?_)
    rw [if_neg (by scalar_tac)]
termination_by 2 - iter.start.val
decreasing_by scalar_decr_tac

/-! ## The two inverse whole-vector levels

Only the last two Gentleman-Sande levels have butterfly partners outside a group of eight
vectors, so only they walk the whole block: `half` runs 8 then 16.  Both reductions the schedule
calls for by this point have already happened inside the group, so there is no re-centring pass
here at all. -/

theorem invntt_horizontal_bnd (SECOND : Bool) (b : Array I16 256#usize) (qv : Vec128)
    (Q Zb B0 T6 C6 T7 C7 : ℤ)
    (hQ : ∀ i < 8, (lane16 qv i).toInt = Q) (hQpos : 0 < Q) (hQ14 : Q < 2 ^ 14)
    (hZb : Zb ≤ 2 ^ 14)
    (hzeta : ∀ kk : Usize, kk.val < 256 → ∃ zi : I16,
        backend.crt.zeta SECOND kk = ok zi ∧ |zi.val| ≤ Zb)
    (qic : I16) (hqinv : backend.crt.qinv SECOND = ok qic)
    (hqinvu : (2 ^ 16 : ℤ) ∣ (qic.val * Q - 1))
    (hB0 : 0 ≤ B0) (hC6 : 0 ≤ C6)
    (l6 : GSLevel Q Zb B0 T6 C6) (l7 : GSLevel Q Zb C6 T7 C7)
    (k : Usize) (hk4 : 4 ≤ k.val) (hk256 : k.val ≤ 256)
    (hb : BlockBnd b B0) :
    backend.neon.ntt.invntt_block_loop1 SECOND b qv k 8#usize
      ⦃ (r : Array I16 256#usize) => BlockBnd r C7 ⦄ := by
  have hQ14' : Q ≤ 2 ^ 14 := by omega
  have hvecs : backend.neon.ntt.VECS = ok 32#usize := by
    simp only [backend.neon.ntt.VECS, consts.RING_DEG]; rfl

  -- level 6: half = 8
  unfold backend.neon.ntt.invntt_block_loop1
  rw [hvecs, bind_tc_ok, if_pos (show (8#usize : Usize) < 32#usize by decide)]
  apply WP.spec_bind (invntt_start_bnd SECOND b qv Q Zb B0 T6 C6 hQ hQpos hQ14' hZb
    (by omega) l6.bz l6.bt l6.fit l6.c1 l6.c2 hzeta qic hqinv hqinvu
    32#usize k 8#usize 0#usize rfl (by decide) (by decide) (by decide)
    (by scalar_tac) (by scalar_tac) (fun p hp _ => hb p hp))
  rintro ⟨b1, k1⟩ ⟨hkk1, hsb1⟩
  show (do let half1 ← (8#usize : Usize) * 2#usize
           backend.neon.ntt.invntt_block_loop1 SECOND b1 qv k1 half1)
      ⦃ (r : Array I16 256#usize) => BlockBnd r C7 ⦄
  rw [show (8#usize : Usize) * 2#usize = ok 16#usize from
      usize_mul_two _ _ (by scalar_tac), bind_tc_ok]
  have hb1 : BlockBnd b1 C6 := blockBnd_of_inv_start hsb1

  -- level 7: half = 16
  unfold backend.neon.ntt.invntt_block_loop1
  rw [hvecs, bind_tc_ok, if_pos (show (16#usize : Usize) < 32#usize by decide)]
  apply WP.spec_bind (invntt_start_bnd SECOND b1 qv Q Zb C6 T7 C7 hQ hQpos hQ14' hZb
    (by omega) l7.bz l7.bt l7.fit l7.c1 l7.c2 hzeta qic hqinv hqinvu
    32#usize k1 16#usize 0#usize rfl (by decide) (by decide) (by decide)
    (by scalar_tac) (by scalar_tac) (fun p hp _ => hb1 p hp))
  rintro ⟨b2, k2⟩ ⟨hkk2, hsb2⟩
  show (do let half1 ← (16#usize : Usize) * 2#usize
           backend.neon.ntt.invntt_block_loop1 SECOND b2 qv k2 half1)
      ⦃ (r : Array I16 256#usize) => BlockBnd r C7 ⦄
  rw [show (16#usize : Usize) * 2#usize = ok 32#usize from
      usize_mul_two _ _ (by scalar_tac), bind_tc_ok]
  have hb2 : BlockBnd b2 C7 := blockBnd_of_inv_start hsb2

  -- half = 32: the loop stops
  unfold backend.neon.ntt.invntt_block_loop1
  rw [hvecs, bind_tc_ok, if_neg (by decide)]
  exact (WP.spec_ok _).mpr hb2

/-! ## The four groups, inverse direction

`load_group`, the three transposed levels with a re-centring pass after the second, a transpose
back, the three vector-pair levels that still fit inside the group with a pass after the first
and another at the end, and eight stores — the forward group mirrored, with the passes where the
schedule puts them. -/

set_option maxRecDepth 4000 in
set_option maxHeartbeats 4000000 in
theorem invntt_group_bnd (SECOND : Bool) (b : Array I16 256#usize) (qv bm round : Vec128)
    (Q Zb M Ain T0 C0 T1 C1 Ar T2 C2 T3 C3 T4 C4 T5 C5 : ℤ)
    (hQ : ∀ i < 8, (lane16 qv i).toInt = Q) (hQpos : 0 < Q) (hQ14 : Q < 2 ^ 14)
    (hQodd : ¬ (2 ∣ Q)) (hZb : Zb ≤ 2 ^ 14)
    (hM : ∀ i < 8, (lane16 bm i).toInt = M) (hMpos : 0 < M) (hMlt : M < 2 ^ 15)
    (hD : |2 ^ 27 - Q * M| ≤ 2047)
    (hRnd : ∀ i < 8, (lane16 round i).toInt = 2 ^ 10)
    (hzeta : ∀ kk : Usize, kk.val < 256 → ∃ zi : I16,
        backend.crt.zeta SECOND kk = ok zi ∧ |zi.val| ≤ Zb)
    (qic : I16) (hqinv : backend.crt.qinv SECOND = ok qic)
    (hqinvu : (2 ^ 16 : ℤ) ∣ (qic.val * Q - 1))
    (htbl4 : ∀ kk : Usize, kk.val < 4 → ∃ z zq : Vec128,
        backend.neon.ntt.inv4 SECOND kk = ok (z, zq) ∧ PsiOk z zq Q Zb)
    (htbl2 : ∀ kk : Usize, kk.val < 8 → ∃ z zq : Vec128,
        backend.neon.ntt.inv2 SECOND kk = ok (z, zq) ∧ PsiOk z zq Q Zb)
    (htbl1 : ∀ kk : Usize, kk.val < 16 → ∃ z zq : Vec128,
        backend.neon.ntt.inv1 SECOND kk = ok (z, zq) ∧ PsiOk z zq Q Zb)
    (hAin : 0 ≤ Ain) (hC0 : 0 ≤ C0) (hAr : 0 ≤ Ar) (hC2 : 0 ≤ C2) (hC4 : 0 ≤ C4)
    (hreset : (Q - 1) / 2 ≤ Ar)
    (g0 : GSLevel Q Zb Ain T0 C0) (g1 : GSLevel Q Zb C0 T1 C1) (hCB01 : C0 ≤ C1)
    (g2 : GSLevel Q Zb Ar T2 C2) (g3 : GSLevel Q Zb C2 T3 C3)
    (g4 : GSLevel Q Zb Ar T4 C4) (hCB45 : C4 ≤ C5) (g5 : GSLevel Q Zb C4 T5 C5)
    (iter : core.ops.range.Range Usize) (hend : iter.«end».val = 4)
    (hb : ∀ p < 256, 64 * iter.start.val ≤ p → |(b.val[p]!).val| ≤ Ain) :
    backend.neon.ntt.invntt_block_loop0 SECOND iter b qv bm round
      ⦃ (r : Array I16 256#usize) => ∀ p < 256,
          if 64 * iter.start.val ≤ p then |(r.val[p]!).val| ≤ (Q - 1) / 2
          else (r.val[p]!).val = (b.val[p]!).val ⦄ := by
  have hQ0 : (0 : ℤ) ≤ (Q - 1) / 2 := by omega
  unfold backend.neon.ntt.invntt_block_loop0
  by_cases hlt : iter.start.val < iter.«end».val
  · let* ⟨ o, iter1, ho, hstart', hend' ⟩ ← core.iter.range.IteratorRange.next_Usize_some_spec
    rw [ho]
    simp only
    have hgi : iter.start.val < 4 := by omega
    -- 1. load and transpose
    apply WP.spec_bind (load_group_spec b iter.start hgi)
    intro v hvload
    have hvb : ∀ k (hk : k < 8), VecBnd (vAt v k hk) Ain := by
      intro k hk m hm
      rw [hvload k hk m hm]
      exact hb _ (by omega) (by omega)
    -- 2. level 0, `len = 1`
    apply WP.spec_bind (invntt_len1_bnd SECOND qv Q Zb Ain T0 C0 hQ hQpos (by omega) hZb
      hAin g0.bz g0.bt g0.fit g0.c1 g0.c2 (fun kk hkk => by
        obtain ⟨z, zq, he, hp⟩ := htbl1 kk hkk
        exact ⟨z, zq, he, hp.1, hp.2⟩)
      iter.start hgi v ⟨0#usize, 4#usize⟩ rfl (fun j hj _ => hvb j hj))
    intro v0 hv0
    have hv0b : ∀ j (hj : j < 8), VecBnd (vAt v0 j hj) C0 := by
      intro j hj
      have := hv0 j hj
      rw [if_pos (by unfold pend1; scalar_tac)] at this
      exact this
    -- 3. level 1, `len = 2`
    apply WP.spec_bind (invntt_len2_outer_bnd SECOND qv Q Zb C0 T1 C1 hQ hQpos (by omega) hZb
      hC0 g1.bz g1.bt g1.fit g1.c1 g1.c2 hCB01 (fun kk hkk => by
        obtain ⟨z, zq, he, hp⟩ := htbl2 kk hkk
        exact ⟨z, zq, he, hp.1, hp.2⟩)
      iter.start hgi v0 ⟨0#usize, 2#usize⟩ rfl (fun j hj _ => hv0b j hj))
    intro v1 hv1
    have hv1b : ∀ j (hj : j < 8), VecBnd (vAt v1 j hj) C1 := by
      intro j hj
      have := hv1 j hj
      rw [if_pos (by scalar_tac)] at this
      exact this
    -- 4. the first re-centring pass
    let* ⟨ s, to_back, hs_val, hto_back ⟩ ← Array.to_slice_mut_spec
    let* ⟨ iter2, imb, hi2_slice, hi2_zero, hi2_back ⟩ ← iter_mut_spec
    have hs_len : s.val.length = 8 := by rw [hs_val]; have := v1.property; scalar_tac
    have hi2_len : iter2.slice.val.length = 8 := by rw [hi2_slice]; exact hs_len
    apply WP.spec_bind (invntt_barrett_iter_bnd iter2 (fun im1 => im1) bm round qv Q M hQ hM hRnd
      hQpos hQ14 hQodd hMpos hMlt hD hi2_len (by rw [hi2_zero]; omega)
      (fun im him => him)
      (fun im him j hj hbnd => absurd hj (by rw [hi2_zero]; omega))
      (fun im him j _ hbnd hbnd' => rfl))
    rintro ⟨im, bk⟩ ⟨him_len, hbk⟩
    obtain ⟨hbk_len, hbk_bnd⟩ := hbk im him_len
    obtain ⟨z4, zq4, hz4e, hz4, hzq4⟩ := htbl4 iter.start hgi
    apply WP.spec_bind (show backend.neon.ntt.inv4 SECOND iter.start
        ⦃ (p : Vec128 × Vec128) => p.1 = z4 ∧ p.2 = zq4 ⦄ from by
      rw [hz4e]; exact (WP.spec_ok _).mpr ⟨rfl, rfl⟩)
    rintro ⟨z, zq⟩ ⟨rfl, rfl⟩
    set a := to_back (imb (bk im)) with ha_def
    have ha_val : a.val = (bk im).slice.val := by
      rw [ha_def, hi2_back, hto_back]
      exact Std.Array.from_slice_val _ _ (by rw [hbk_len]; simp)
    have hab : ∀ j (hj : j < 8), VecBnd (vAt a j hj) Ar := by
      intro j hj
      have hjb : j < (bk im).slice.val.length := by rw [hbk_len]; omega
      have := hbk_bnd j hjb
      have heq : vAt a j hj = sAt (bk im).slice j hjb := by
        unfold vAt sAt
        exact List.getElem_of_eq ha_val _
      rw [heq]
      exact this.mono hreset
    -- 5. level 2, `len = 4`
    apply WP.spec_bind (invntt_len4_bnd qv z zq Q Zb Ar T2 C2 hQ hQpos (by omega) hz4 hZb hzq4
      hAr g2.bz g2.bt g2.fit g2.c1 g2.c2 a ⟨0#usize, 4#usize⟩ rfl (fun j hj _ => hab j hj))
    intro v3 hv3
    have hv3b : ∀ j (hj : j < 8), VecBnd (vAt v3 j hj) C2 := by
      intro j hj
      have := hv3 j hj
      rw [if_pos (by unfold pend4; scalar_tac)] at this
      exact this
    -- 6. back to coefficient order
    apply WP.spec_bind (transpose8_bnd v3 C2 hv3b)
    intro v4 hv4b
    -- 7. level 3, adjacent vectors
    apply WP.spec_bind (invntt_lvl3_bnd SECOND qv Q Zb C2 T3 C3 hQ hQpos (by omega) hZb
      hC2 g3.bz g3.bt g3.fit g3.c1 g3.c2 hzeta qic hqinv hqinvu
      iter.start hgi v4 ⟨0#usize, 4#usize⟩ rfl (fun j hj _ => hv4b j hj))
    intro v5 hv5
    have hv5b : ∀ j (hj : j < 8), VecBnd (vAt v5 j hj) C3 := by
      intro j hj
      have := hv5 j hj
      rw [if_pos (by unfold pend1; scalar_tac)] at this
      exact this
    -- 8. the second re-centring pass
    let* ⟨ s2, to_back2, hs2_val, hto_back2 ⟩ ← Array.to_slice_mut_spec
    let* ⟨ iter3, imb3, hi3_slice, hi3_zero, hi3_back ⟩ ← iter_mut_spec
    have hs2_len : s2.val.length = 8 := by rw [hs2_val]; have := v5.property; scalar_tac
    have hi3_len : iter3.slice.val.length = 8 := by rw [hi3_slice]; exact hs2_len
    rw [invntt_loop0_loop5_eq]
    apply WP.spec_bind (invntt_barrett_iter_bnd iter3 (fun im1 => im1) bm round qv Q M hQ hM hRnd
      hQpos hQ14 hQodd hMpos hMlt hD hi3_len (by rw [hi3_zero]; omega)
      (fun im him => him)
      (fun im him j hj hbnd => absurd hj (by rw [hi3_zero]; omega))
      (fun im him j _ hbnd hbnd' => rfl))
    rintro ⟨im2, bk2⟩ ⟨him2_len, hbk2⟩
    obtain ⟨hbk2_len, hbk2_bnd⟩ := hbk2 im2 him2_len
    set a2 := to_back2 (imb3 (bk2 im2)) with ha2_def
    have ha2_val : a2.val = (bk2 im2).slice.val := by
      rw [ha2_def, hi3_back, hto_back2]
      exact Std.Array.from_slice_val _ _ (by rw [hbk2_len]; simp)
    have ha2b : ∀ j (hj : j < 8), VecBnd (vAt a2 j hj) Ar := by
      intro j hj
      have hjb : j < (bk2 im2).slice.val.length := by rw [hbk2_len]; omega
      have := hbk2_bnd j hjb
      have heq : vAt a2 j hj = sAt (bk2 im2).slice j hjb := by
        unfold vAt sAt
        exact List.getElem_of_eq ha2_val _
      rw [heq]
      exact this.mono hreset
    -- 9. level 4
    apply WP.spec_bind (invntt_lvl4_bnd SECOND qv Q Zb Ar T4 C4 hQ hQpos (by omega) hZb
      hAr g4.bz g4.bt g4.fit g4.c1 g4.c2 (by have h := g4.c1; omega) hzeta qic hqinv hqinvu
      iter.start hgi a2 ⟨0#usize, 2#usize⟩ rfl (fun j hj _ => ha2b j hj))
    intro v6 hv6
    have hv6b : ∀ j (hj : j < 8), VecBnd (vAt v6 j hj) C4 := by
      intro j hj
      have := hv6 j hj
      rw [if_pos (by scalar_tac)] at this
      exact this
    -- 10. level 5
    let* ⟨ i7, hi7 ⟩ ← Std.Usize.sub_spec (x := 7#usize) (y := iter.start) (by scalar_tac)
    obtain ⟨zi7, hzie7, hzib7⟩ := hzeta i7 (by scalar_tac)
    obtain ⟨z5, zq5, hnz5, -, hz5b, hzq5b⟩ :=
      neg_zeta_spec SECOND Q Zb i7 zi7 hzie7 hzib7 hZb qic hqinv hqinvu
    rw [hnz5, bind_tc_ok, invntt_loop0_loop7_eq]
    apply WP.spec_bind (invntt_len4_bnd qv z5 zq5 Q Zb C4 T5 C5 hQ hQpos (by omega) hz5b hZb
      hzq5b hC4 g5.bz g5.bt g5.fit g5.c1 g5.c2 v6 ⟨0#usize, 4#usize⟩ rfl
      (fun j hj _ => hv6b j hj))
    intro v7 hv7
    have hv7b : ∀ j (hj : j < 8), VecBnd (vAt v7 j hj) C5 := by
      intro j hj
      have := hv7 j hj
      rw [if_pos (by unfold pend4; scalar_tac)] at this
      exact this
    -- 11. the third re-centring pass, which leaves the group centred
    let* ⟨ s3, to_back3, hs3_val, hto_back3 ⟩ ← Array.to_slice_mut_spec
    let* ⟨ iter4, imb4, hi4_slice, hi4_zero, hi4_back ⟩ ← iter_mut_spec
    have hs3_len : s3.val.length = 8 := by rw [hs3_val]; have := v7.property; scalar_tac
    have hi4_len : iter4.slice.val.length = 8 := by rw [hi4_slice]; exact hs3_len
    rw [invntt_loop0_loop8_eq]
    apply WP.spec_bind (invntt_barrett_iter_bnd iter4 (fun im1 => im1) bm round qv Q M hQ hM hRnd
      hQpos hQ14 hQodd hMpos hMlt hD hi4_len (by rw [hi4_zero]; omega)
      (fun im him => him)
      (fun im him j hj hbnd => absurd hj (by rw [hi4_zero]; omega))
      (fun im him j _ hbnd hbnd' => rfl))
    rintro ⟨im3, bk3⟩ ⟨him3_len, hbk3⟩
    obtain ⟨hbk3_len, hbk3_bnd⟩ := hbk3 im3 him3_len
    -- 12. the eight stores
    let* ⟨ i8, hi8 ⟩ ← Std.Usize.mul_spec (x := 8#usize) (y := iter.start) (by scalar_tac)
    have hi8v : i8.val = 8 * iter.start.val := by scalar_tac
    set a3 := to_back3 (imb4 (bk3 im3)) with ha3_def
    have ha3_val : a3.val = (bk3 im3).slice.val := by
      rw [ha3_def, hi4_back, hto_back3]
      exact Std.Array.from_slice_val _ _ (by rw [hbk3_len]; simp)
    have ha3b : ∀ j (hj : j < 8), VecBnd (vAt a3 j hj) ((Q - 1) / 2) := by
      intro j hj
      have hjb : j < (bk3 im3).slice.val.length := by rw [hbk3_len]; omega
      have := hbk3_bnd j hjb
      have heq : vAt a3 j hj = sAt (bk3 im3).slice j hjb := by
        unfold vAt sAt
        exact List.getElem_of_eq ha3_val _
      rw [heq]
      exact this
    have hstore : ∀ (ju : Usize) (hju : ju.val < 8) (bb : Array I16 256#usize) (idx : Usize)
        (hidx : idx.val = 8 * iter.start.val + ju.val),
        ∃ bb', store_i16 bb idx (vAt a3 ju.val hju) = ok bb' ∧ ∀ p < 256,
          (bb'.val[p]!).val =
            if 8 * idx.val ≤ p ∧ p < 8 * idx.val + 8 then
              (lane16 (vAt a3 ju.val hju) (p - 8 * idx.val)).toInt
            else (bb.val[p]!).val := fun ju hju bb idx hidx =>
      store_i16_val bb idx (vAt a3 ju.val hju) (by omega)
    have hv0e : ∀ (j : Usize) (hj : j.val < 8),
        Array.index_usize a3 j = ok (vAt a3 j.val hj) := by
      intro j hj
      obtain ⟨w, hw⟩ := WP.spec_imp_exists (Array.index_usize_spec a3 j (by scalar_tac))
      rw [hw.1]
      congr 1
      rw [hw.2]
      rfl
    rw [hv0e 0#usize (by decide), bind_tc_ok]
    obtain ⟨b1, hb1e, hb1v⟩ := hstore 0#usize (by decide) b i8 (by scalar_tac)
    rw [hb1e, bind_tc_ok]
    let* ⟨ j1, hj1 ⟩ ← Std.Usize.add_spec (x := i8) (y := 1#usize) (by scalar_tac)
    rw [hv0e 1#usize (by decide), bind_tc_ok]
    obtain ⟨b2, hb2e, hb2v⟩ := hstore 1#usize (by decide) b1 j1 (by scalar_tac)
    rw [hb2e, bind_tc_ok]
    let* ⟨ j2, hj2 ⟩ ← Std.Usize.add_spec (x := i8) (y := 2#usize) (by scalar_tac)
    rw [hv0e 2#usize (by decide), bind_tc_ok]
    obtain ⟨b3, hb3e, hb3v⟩ := hstore 2#usize (by decide) b2 j2 (by scalar_tac)
    rw [hb3e, bind_tc_ok]
    let* ⟨ j3, hj3 ⟩ ← Std.Usize.add_spec (x := i8) (y := 3#usize) (by scalar_tac)
    rw [hv0e 3#usize (by decide), bind_tc_ok]
    obtain ⟨b4, hb4e, hb4v⟩ := hstore 3#usize (by decide) b3 j3 (by scalar_tac)
    rw [hb4e, bind_tc_ok]
    let* ⟨ j4, hj4 ⟩ ← Std.Usize.add_spec (x := i8) (y := 4#usize) (by scalar_tac)
    rw [hv0e 4#usize (by decide), bind_tc_ok]
    obtain ⟨b5, hb5e, hb5v⟩ := hstore 4#usize (by decide) b4 j4 (by scalar_tac)
    rw [hb5e, bind_tc_ok]
    let* ⟨ j5, hj5 ⟩ ← Std.Usize.add_spec (x := i8) (y := 5#usize) (by scalar_tac)
    rw [hv0e 5#usize (by decide), bind_tc_ok]
    obtain ⟨b6, hb6e, hb6v⟩ := hstore 5#usize (by decide) b5 j5 (by scalar_tac)
    rw [hb6e, bind_tc_ok]
    let* ⟨ j6, hj6 ⟩ ← Std.Usize.add_spec (x := i8) (y := 6#usize) (by scalar_tac)
    rw [hv0e 6#usize (by decide), bind_tc_ok]
    obtain ⟨b7, hb7e, hb7v⟩ := hstore 6#usize (by decide) b6 j6 (by scalar_tac)
    rw [hb7e, bind_tc_ok]
    let* ⟨ j7, hj7 ⟩ ← Std.Usize.add_spec (x := i8) (y := 7#usize) (by scalar_tac)
    rw [hv0e 7#usize (by decide), bind_tc_ok]
    obtain ⟨b8, hb8e, hb8v⟩ := hstore 7#usize (by decide) b7 j7 (by scalar_tac)
    rw [hb8e, bind_tc_ok]
    -- what the eight stores leave behind
    have hb8all : ∀ p < 256,
        if 64 * iter.start.val ≤ p ∧ p < 64 * iter.start.val + 64 then
          |(b8.val[p]!).val| ≤ (Q - 1) / 2
        else (b8.val[p]!).val = (b.val[p]!).val := by
      intro p hp
      have e8 := hb8v p hp
      have e7 := hb7v p hp
      have e6 := hb6v p hp
      have e5 := hb5v p hp
      have e4 := hb4v p hp
      have e3 := hb3v p hp
      have e2 := hb2v p hp
      have e1 := hb1v p hp
      by_cases hin : 64 * iter.start.val ≤ p ∧ p < 64 * iter.start.val + 64
      · rw [if_pos hin]
        set d := p - 64 * iter.start.val with hd
        have hd8 : d < 64 := by omega
        rcases show d / 8 = 0 ∨ d / 8 = 1 ∨ d / 8 = 2 ∨ d / 8 = 3 ∨ d / 8 = 4 ∨ d / 8 = 5
            ∨ d / 8 = 6 ∨ d / 8 = 7 from by omega with
          h | h | h | h | h | h | h | h
        · rw [e8, if_neg (by omega), e7, if_neg (by omega), e6, if_neg (by omega),
            e5, if_neg (by omega), e4, if_neg (by omega), e3, if_neg (by omega),
            e2, if_neg (by omega), e1, if_pos (by omega)]
          exact ha3b 0 (by decide) _ (by omega)
        · rw [e8, if_neg (by omega), e7, if_neg (by omega), e6, if_neg (by omega),
            e5, if_neg (by omega), e4, if_neg (by omega), e3, if_neg (by omega),
            e2, if_pos (by omega)]
          exact ha3b 1 (by decide) _ (by omega)
        · rw [e8, if_neg (by omega), e7, if_neg (by omega), e6, if_neg (by omega),
            e5, if_neg (by omega), e4, if_neg (by omega), e3, if_pos (by omega)]
          exact ha3b 2 (by decide) _ (by omega)
        · rw [e8, if_neg (by omega), e7, if_neg (by omega), e6, if_neg (by omega),
            e5, if_neg (by omega), e4, if_pos (by omega)]
          exact ha3b 3 (by decide) _ (by omega)
        · rw [e8, if_neg (by omega), e7, if_neg (by omega), e6, if_neg (by omega),
            e5, if_pos (by omega)]
          exact ha3b 4 (by decide) _ (by omega)
        · rw [e8, if_neg (by omega), e7, if_neg (by omega), e6, if_pos (by omega)]
          exact ha3b 5 (by decide) _ (by omega)
        · rw [e8, if_neg (by omega), e7, if_pos (by omega)]
          exact ha3b 6 (by decide) _ (by omega)
        · rw [e8, if_pos (by omega)]
          exact ha3b 7 (by decide) _ (by omega)
      · rw [if_neg hin, e8, if_neg (by omega), e7, if_neg (by omega), e6, if_neg (by omega),
          e5, if_neg (by omega), e4, if_neg (by omega), e3, if_neg (by omega),
          e2, if_neg (by omega), e1, if_neg (by omega)]
    -- 13. and the remaining groups
    apply WP.spec_mono (invntt_group_bnd SECOND b8 qv bm round Q Zb M Ain T0 C0 T1 C1 Ar T2 C2
      T3 C3 T4 C4 T5 C5 hQ hQpos hQ14 hQodd hZb hM hMpos hMlt hD hRnd hzeta qic hqinv hqinvu
      htbl4 htbl2 htbl1 hAin hC0 hAr hC2 hC4 hreset g0 g1 hCB01 g2 g3 g4 hCB45 g5
      iter1 (by rw [hend']; exact hend) (by
        intro p hp hge
        have := hb8all p hp
        rw [if_neg (by omega)] at this
        rw [this]
        exact hb p hp (by omega)))
    intro r hr p hp
    have hrp := hr p hp
    have hbp := hb8all p hp
    by_cases hge : 64 * iter.start.val ≤ p
    · rw [if_pos hge]
      by_cases hge1 : 64 * iter1.start.val ≤ p
      · rw [if_pos hge1] at hrp
        exact hrp
      · rw [if_neg hge1] at hrp
        rw [hrp, if_pos (by omega)] at *
        exact hbp
    · rw [if_neg hge]
      rw [if_neg (by omega)] at hrp
      rw [if_neg (by omega)] at hbp
      rw [hrp]
      exact hbp
  · let* ⟨ o, iter1, hnone, _ ⟩ ← core.iter.range.IteratorRange.next_Usize_none_spec
    rw [hnone]
    refine (WP.spec_ok _).mpr (fun p hp => ?_)
    rw [if_neg (by scalar_tac)]
termination_by 4 - iter.start.val
decreasing_by scalar_decr_tac

/-! ## The final scaling

`invntt_block` ends by multiplying every coefficient by one constant — the scale that undoes
both the `1/256` the inverse transform leaves behind and the Montgomery factor the pointwise step
introduced.  It is one `mont_mul` per vector, so the bound is `mont_mul_bnd` thirty-two times. -/

theorem invntt_scale_bnd (b : Array I16 256#usize) (qv scale scaleq : Vec128) (Q Zb B Bt : ℤ)
    (hQ : ∀ i < 8, (lane16 qv i).toInt = Q) (hQpos : 0 < Q) (hQlt : Q ≤ 2 ^ 14)
    (hz : ∀ i < 8, |(lane16 scale i).toInt| ≤ Zb) (hZb : Zb ≤ 2 ^ 14)
    (hzq : ∀ i < 8, (2 ^ 16 : ℤ) ∣ ((lane16 scaleq i).toInt * Q - (lane16 scale i).toInt))
    (hB0 : 0 ≤ B) (hBZ : B * Zb < 2 ^ 15 * Q) (hBt : B * Zb + 2 ^ 15 * Q ≤ 2 ^ 16 * Bt)
    (iter : core.ops.range.Range Usize) (hend : iter.«end».val = 32)
    (hb : ∀ p < 256, 8 * iter.start.val ≤ p → |(b.val[p]!).val| ≤ B) :
    backend.neon.ntt.invntt_block_loop2 iter b qv scale scaleq
      ⦃ (r : Array I16 256#usize) => ∀ p < 256,
          if 8 * iter.start.val ≤ p then |(r.val[p]!).val| ≤ Bt
          else (r.val[p]!).val = (b.val[p]!).val ⦄ := by
  unfold backend.neon.ntt.invntt_block_loop2
  by_cases hlt : iter.start.val < iter.«end».val
  · let* ⟨ o, iter1, ho, hstart', hend' ⟩ ← core.iter.range.IteratorRange.next_Usize_some_spec
    rw [ho]
    simp only
    have hi32 : iter.start.val < 32 := by omega
    obtain ⟨vec, hvec, hvecl⟩ := load_i16_val b iter.start hi32
    rw [hvec, bind_tc_ok]
    have hvb : VecBnd vec B := by
      intro k hk
      rw [hvecl k hk]
      exact hb _ (by omega) (by omega)
    apply WP.spec_bind (mont_mul_bnd vec scale scaleq qv Q Zb B Bt hQ hQpos hQlt hz hZb hzq
      hvb hB0 hBZ hBt)
    rintro v1 ⟨hv1b, -⟩
    obtain ⟨b1, hb1, hb1v⟩ := store_i16_val b iter.start v1 hi32
    rw [hb1, bind_tc_ok]
    apply WP.spec_mono (invntt_scale_bnd b1 qv scale scaleq Q Zb B Bt hQ hQpos hQlt hz hZb hzq
      hB0 hBZ hBt iter1 (by rw [hend']; exact hend) (by
        intro p hp hge
        rw [hb1v p hp, if_neg (by scalar_tac)]
        exact hb p hp (by omega)))
    intro r hr p hp
    have hrp := hr p hp
    by_cases hge : 8 * iter.start.val ≤ p
    · rw [if_pos hge]
      by_cases hge1 : 8 * iter1.start.val ≤ p
      · rw [if_pos hge1] at hrp
        exact hrp
      · rw [if_neg hge1] at hrp
        rw [hrp, hb1v p hp, if_pos (by scalar_tac)]
        exact hv1b _ (by omega)
    · rw [if_neg hge]
      rw [if_neg (by omega)] at hrp
      rw [hrp, hb1v p hp, if_neg (by scalar_tac)]
  · let* ⟨ o, iter1, hnone, _ ⟩ ← core.iter.range.IteratorRange.next_Usize_none_spec
    rw [hnone]
    refine (WP.spec_ok _).mpr (fun p hp => ?_)
    rw [if_neg (by scalar_tac)]
termination_by 32 - iter.start.val
decreasing_by scalar_decr_tac

/-! ## The inverse table hypotheses, discharged

The mirror of `psiOk_fwd4` / `_fwd2` / `_fwd1`: the ψ pair each transposed inverse level loads is
centred and Montgomery-paired.  The only difference is the sign flag — the inverse tables hold
`−ζ`, so the bound goes through `abs_neg` — and the closed-form index. -/

theorem psiOk_inv4 (SECOND : Bool) (Q Zb : ℤ)
    (hz : ∀ k < 256, |((zetasOf SECOND).val[k]!).val| ≤ Zb)
    (hinv : (2 ^ 16 : ℤ) ∣ ((qinvOf SECOND).val * Q - 1))
    (kk : Usize) (hkk : kk.val < 4) :
    ∃ z zq : Vec128, backend.neon.ntt.inv4 SECOND kk = ok (z, zq) ∧ PsiOk z zq Q Zb := by
  obtain ⟨r, hr, hp⟩ := WP.spec_imp_exists (inv4_spec SECOND kk (by scalar_tac))
  refine ⟨r.1, r.2, by rw [hr], fun i hi => ?_, fun i hi => ?_⟩
  · rw [(hp i hi).1]
    unfold tblZ
    split
    · rw [abs_neg]; exact hz _ (by unfold inv4Idx; omega)
    · exact hz _ (by unfold inv4Idx; omega)
  · rw [(hp i hi).1, (hp i hi).2]
    exact tblZq_mont _ _ _ hinv

theorem psiOk_inv2 (SECOND : Bool) (Q Zb : ℤ)
    (hz : ∀ k < 256, |((zetasOf SECOND).val[k]!).val| ≤ Zb)
    (hinv : (2 ^ 16 : ℤ) ∣ ((qinvOf SECOND).val * Q - 1))
    (kk : Usize) (hkk : kk.val < 8) :
    ∃ z zq : Vec128, backend.neon.ntt.inv2 SECOND kk = ok (z, zq) ∧ PsiOk z zq Q Zb := by
  obtain ⟨r, hr, hp⟩ := WP.spec_imp_exists (inv2_spec SECOND kk (by scalar_tac))
  refine ⟨r.1, r.2, by rw [hr], fun i hi => ?_, fun i hi => ?_⟩
  · rw [(hp i hi).1]
    unfold tblZ
    split
    · rw [abs_neg]; exact hz _ (by unfold inv2Idx; omega)
    · exact hz _ (by unfold inv2Idx; omega)
  · rw [(hp i hi).1, (hp i hi).2]
    exact tblZq_mont _ _ _ hinv

theorem psiOk_inv1 (SECOND : Bool) (Q Zb : ℤ)
    (hz : ∀ k < 256, |((zetasOf SECOND).val[k]!).val| ≤ Zb)
    (hinv : (2 ^ 16 : ℤ) ∣ ((qinvOf SECOND).val * Q - 1))
    (kk : Usize) (hkk : kk.val < 16) :
    ∃ z zq : Vec128, backend.neon.ntt.inv1 SECOND kk = ok (z, zq) ∧ PsiOk z zq Q Zb := by
  obtain ⟨r, hr, hp⟩ := WP.spec_imp_exists (inv1_spec SECOND kk (by scalar_tac))
  refine ⟨r.1, r.2, by rw [hr], fun i hi => ?_, fun i hi => ?_⟩
  · rw [(hp i hi).1]
    unfold tblZ
    split
    · rw [abs_neg]; exact hz _ (by unfold inv1Idx; omega)
    · exact hz _ (by unfold inv1Idx; omega)
  · rw [(hp i hi).1, (hp i hi).2]
    exact tblZq_mont _ _ _ hinv

/-! ## The inverse transform

`invntt_block` is the constant setup, the four groups (levels 0 to 5), the two whole-vector
levels that cross them, and the final scaling.

The chain collapses to **two** `GSLevel`s.  Every Gentleman–Sande level either starts from a
freshly re-centred block — `|a| ≤ (q−1)/2` — or from the output of the level before it, and the
schedule re-centres often enough that the second case only ever happens once in a row.  So there
are exactly two shapes: `Ar → Clo` and `Clo → Chi`, and the eight levels are
`glo, ghi` (re-centre) `glo` ‖ `ghi` (re-centre) `glo, ghi` (re-centre) `glo, ghi`.
The scaling pass then takes `Chi` to `Bt`. -/

theorem invntt_block_bnd (SECOND : Bool) (b : Array I16 256#usize)
    (Q Zb M Ain T0 C0 T1 C1 Ar Tlo Clo Thi Chi Bt : ℤ) (qc mc rc sc qic : I16)
    (hq : backend.crt.q SECOND = ok qc) (hqv : qc.val = Q)
    (hm : backend.crt.barrett_m SECOND = ok mc) (hmv : mc.val = M)
    (hrc : (1#i16 : I16) <<< (10#i32 : Std.I32) = ok rc) (hrcv : rc.val = 2 ^ 10)
    (hsc : backend.crt.invntt_scale SECOND = ok sc) (hscb : |sc.val| ≤ Zb)
    (hqi : backend.crt.qinv SECOND = ok qic) (hqiu : (2 ^ 16 : ℤ) ∣ (qic.val * Q - 1))
    (hQpos : 0 < Q) (hQ14 : Q < 2 ^ 14) (hQodd : ¬ (2 ∣ Q)) (hZb : Zb ≤ 2 ^ 14)
    (hMpos : 0 < M) (hMlt : M < 2 ^ 15) (hD : |2 ^ 27 - Q * M| ≤ 2047)
    (hzeta : ∀ kk : Usize, kk.val < 256 → ∃ zi : I16,
        backend.crt.zeta SECOND kk = ok zi ∧ |zi.val| ≤ Zb)
    (htbl4 : ∀ kk : Usize, kk.val < 4 → ∃ z zq : Vec128,
        backend.neon.ntt.inv4 SECOND kk = ok (z, zq) ∧ PsiOk z zq Q Zb)
    (htbl2 : ∀ kk : Usize, kk.val < 8 → ∃ z zq : Vec128,
        backend.neon.ntt.inv2 SECOND kk = ok (z, zq) ∧ PsiOk z zq Q Zb)
    (htbl1 : ∀ kk : Usize, kk.val < 16 → ∃ z zq : Vec128,
        backend.neon.ntt.inv1 SECOND kk = ok (z, zq) ∧ PsiOk z zq Q Zb)
    (hAinz : 0 ≤ Ain) (hC0z : 0 ≤ C0)
    (hArz : 0 ≤ Ar) (hCloz : 0 ≤ Clo) (hreset : (Q - 1) / 2 ≤ Ar)
    (g0 : GSLevel Q Zb Ain T0 C0) (g1 : GSLevel Q Zb C0 T1 C1) (hCB01 : C0 ≤ C1)
    (glo : GSLevel Q Zb Ar Tlo Clo) (ghi : GSLevel Q Zb Clo Thi Chi) (hCB : Clo ≤ Chi)
    (hBZ : Chi * Zb < 2 ^ 15 * Q) (hBt : Chi * Zb + 2 ^ 15 * Q ≤ 2 ^ 16 * Bt)
    (hb : BlockBnd b Ain) :
    backend.neon.ntt.invntt_block SECOND b
      ⦃ (r : Array I16 256#usize) => BlockBnd r Bt ⦄ := by
  unfold backend.neon.ntt.invntt_block
  rw [hq, bind_tc_ok]
  obtain ⟨qv, hqe, hql⟩ := dup_n_s16_spec qc
  rw [hqe, bind_tc_ok, hm, bind_tc_ok]
  obtain ⟨bm, hbme, hbml⟩ := dup_n_s16_spec mc
  rw [hbme, bind_tc_ok]
  have hsh : backend.crt.BARRETT_SH - (1#i32 : Std.I32) = ok (10#i32 : Std.I32) := by
    simp only [backend.crt.BARRETT_SH]
    rfl
  rw [hsh, bind_tc_ok, hrc, bind_tc_ok]
  obtain ⟨round, hre, hrl⟩ := dup_n_s16_spec rc
  rw [hre, bind_tc_ok]
  have hQv : ∀ i < 8, (lane16 qv i).toInt = Q := by
    intro i hi; rw [hql i hi]; exact hqv
  have hMv : ∀ i < 8, (lane16 bm i).toInt = M := by
    intro i hi; rw [hbml i hi]; exact hmv
  have hRv : ∀ i < 8, (lane16 round i).toInt = 2 ^ 10 := by
    intro i hi; rw [hrl i hi]; exact hrcv
  -- the four groups: levels 0 to 5
  apply WP.spec_bind (invntt_group_bnd SECOND b qv bm round Q Zb M Ain T0 C0 T1 C1 Ar
    Tlo Clo Thi Chi Tlo Clo Thi Chi
    hQv hQpos hQ14 hQodd hZb hMv hMpos hMlt hD hRv hzeta qic hqi hqiu htbl4 htbl2 htbl1
    hAinz hC0z hArz hCloz hCloz hreset g0 g1 hCB01 glo ghi glo hCB ghi
    ⟨0#usize, 4#usize⟩ rfl (fun p hp _ => hb p hp))
  intro b1 hb1
  have hb1' : BlockBnd b1 Ar := by
    intro p hp
    have h := hb1 p hp
    rw [if_pos (by scalar_tac)] at h
    exact le_trans h hreset
  -- levels 6 and 7, which cross groups
  apply WP.spec_bind (invntt_horizontal_bnd SECOND b1 qv Q Zb Ar Tlo Clo Thi Chi
    hQv hQpos hQ14 hZb hzeta qic hqi hqiu hArz hCloz glo ghi 4#usize (by scalar_tac)
    (by scalar_tac) hb1')
  intro b2 hb2
  -- and the final scaling
  rw [hsc, bind_tc_ok]
  obtain ⟨scale, hse, hsl⟩ := dup_n_s16_spec sc
  rw [hse, bind_tc_ok, hqi, bind_tc_ok]
  simp only [lift, bind_tc_ok]
  obtain ⟨scaleq, hsqe, hsql⟩ := dup_n_s16_spec (core.num.I16.wrapping_mul sc qic)
  rw [hsqe, bind_tc_ok]
  have hvecs : backend.neon.ntt.VECS = ok 32#usize := by
    simp only [backend.neon.ntt.VECS, consts.RING_DEG]; rfl
  rw [hvecs, bind_tc_ok]
  apply WP.spec_mono (invntt_scale_bnd b2 qv scale scaleq Q Zb Chi Bt hQv hQpos (by omega)
    (by intro i hi; rw [hsl i hi]; exact hscb) hZb
    (by
      intro i hi
      rw [hsl i hi, hsql i hi]
      have h1 : ((core.num.I16.wrapping_mul sc qic).bv).toInt = tblZq sc.val qic.val := by
        show ((sc.bv * qic.bv : BitVec 16)).toInt = _
        rw [BitVec.toInt_mul]
        rfl
      rw [h1]
      exact tblZq_mont sc.val qic.val Q hqiu)
    (by omega) hBZ hBt ⟨0#usize, 32#usize⟩ rfl (fun p hp _ => hb2 p hp))
  intro r hr p hp
  have h := hr p hp
  rwa [if_pos (by scalar_tac)] at h

/-! ## The inverse transform at the two primes

The two `GSLevel`s are `Ar → Clo` and `Clo → Chi` with `Clo = 2·Ar` and `Chi = 2·Clo`: the
Gentleman–Sande sum doubles, and the Montgomery product is always smaller than that, so the
doubling *is* the growth.  Three re-centrings keep the run length at two, which is what makes
`Chi = 4·Ar` — comfortably inside an `i16` lane at both primes — and the final scaling brings
that back down below `q`. -/

unseal backend.crt.INVNTT_SCALE_1 in
/-- **The inverse transform on the first prime.** -/
theorem invntt_block_bnd_q1 (b : Array I16 256#usize) (hb : BlockBnd b 4741) :
    backend.neon.ntt.invntt_block false b
      ⦃ (r : Array I16 256#usize) => BlockBnd r 4741 ⦄ := by
  have hzc : ∀ k < 256, |((zetasOf false).val[k]!).val| ≤ 3840 := by
    intro k hk
    simp only [zetasOf, Bool.false_eq_true, if_false]
    exact zetas_q1_centred_idx k hk
  have hinv : (2 ^ 16 : ℤ) ∣ ((qinvOf false).val * 7681 - 1) := by
    simp only [qinvOf, Bool.false_eq_true, if_false]
    rw [← q1_val]
    exact q1_inv_unit
  have hzt : ∀ kk : Usize, kk.val < 256 → ∃ zi : I16,
      backend.crt.zeta false kk = ok zi ∧ |zi.val| ≤ 3840 := by
    intro kk hkk
    obtain ⟨zi, _, hzi, -, hzib, -, -⟩ := zeta_table_ok_q1 kk hkk
    exact ⟨zi, hzi, hzib⟩
  refine invntt_block_bnd false b 7681 3840 17474 4741 4397 9482 4952 18964 3840 4291 7680 4741 15360 4741
    backend.crt.Q1 backend.crt.Q1_BARRETT_M 1024#i16 backend.crt.INVNTT_SCALE_1 backend.crt.Q1_INV
    (by simp only [backend.crt.q, Bool.false_eq_true, if_false]) q1_val
    (by simp only [backend.crt.barrett_m, Bool.false_eq_true, if_false]) q1_m_val
    round_const (by decide)
    (by simp only [backend.crt.invntt_scale, Bool.false_eq_true, if_false]) (by decide)
    (by simp only [backend.crt.qinv, Bool.false_eq_true, if_false]) (by rw [← q1_val]; exact q1_inv_unit)
    (by norm_num) (by norm_num) (by decide) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
    hzt
    (psiOk_inv4 false 7681 3840 hzc hinv) (psiOk_inv2 false 7681 3840 hzc hinv)
    (psiOk_inv1 false 7681 3840 hzc hinv)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    ⟨⟨by norm_num, by norm_num, by norm_num⟩, by norm_num, by norm_num, by norm_num⟩
    ⟨⟨by norm_num, by norm_num, by norm_num⟩, by norm_num, by norm_num, by norm_num⟩
    (by norm_num)
    ⟨⟨by norm_num, by norm_num, by norm_num⟩, by norm_num, by norm_num, by norm_num⟩
    ⟨⟨by norm_num, by norm_num, by norm_num⟩, by norm_num, by norm_num, by norm_num⟩
    (by norm_num) (by norm_num) (by norm_num) hb

unseal backend.crt.INVNTT_SCALE_2 in
/-- **The inverse transform on the second prime.** -/
theorem invntt_block_bnd_q2 (b : Array I16 256#usize) (hb : BlockBnd b 7141) :
    backend.neon.ntt.invntt_block true b
      ⦃ (r : Array I16 256#usize) => BlockBnd r 7141 ⦄ := by
  have hzc : ∀ k < 256, |((zetasOf true).val[k]!).val| ≤ 5376 := by
    intro k hk
    simp only [zetasOf, if_true]
    exact zetas_q2_centred_idx k hk
  have hinv : (2 ^ 16 : ℤ) ∣ ((qinvOf true).val * 10753 - 1) := by
    simp only [qinvOf, if_true]
    rw [← q2_val]
    exact q2_inv_unit
  have hzt : ∀ kk : Usize, kk.val < 256 → ∃ zi : I16,
      backend.crt.zeta true kk = ok zi ∧ |zi.val| ≤ 5376 := by
    intro kk hkk
    obtain ⟨zi, _, hzi, -, hzib, -, -⟩ := zeta_table_ok_q2 kk hkk
    exact ⟨zi, hzi, hzib⟩
  refine invntt_block_bnd true b 10753 5376 12482 7141 6549 14282 7720 28564 5376 6259 10752 7141 21504 7141
    backend.crt.Q2 backend.crt.Q2_BARRETT_M 1024#i16 backend.crt.INVNTT_SCALE_2 backend.crt.Q2_INV
    (by simp only [backend.crt.q, if_true]) q2_val
    (by simp only [backend.crt.barrett_m, if_true]) q2_m_val
    round_const (by decide)
    (by simp only [backend.crt.invntt_scale, if_true]) (by decide)
    (by simp only [backend.crt.qinv, if_true]) (by rw [← q2_val]; exact q2_inv_unit)
    (by norm_num) (by norm_num) (by decide) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
    hzt
    (psiOk_inv4 true 10753 5376 hzc hinv) (psiOk_inv2 true 10753 5376 hzc hinv)
    (psiOk_inv1 true 10753 5376 hzc hinv)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    ⟨⟨by norm_num, by norm_num, by norm_num⟩, by norm_num, by norm_num, by norm_num⟩
    ⟨⟨by norm_num, by norm_num, by norm_num⟩, by norm_num, by norm_num, by norm_num⟩
    (by norm_num)
    ⟨⟨by norm_num, by norm_num, by norm_num⟩, by norm_num, by norm_num, by norm_num⟩
    ⟨⟨by norm_num, by norm_num, by norm_num⟩, by norm_num, by norm_num, by norm_num⟩
    (by norm_num) (by norm_num) (by norm_num) hb

end Kopis.Neon
