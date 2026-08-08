/-
  # Kopis/Neon/NttTransposed.lean — the forward levels that live inside a vector.

  Once a group of eight vectors has been transposed (`Kopis/Neon/Group.lean`), lane `m` owns the
  whole eight-coefficient block `8g + m`, and the last three levels — `len = 4, 2, 1` — become
  ordinary vertical butterflies between *vectors* of the group, with a per-lane ψ from the tables
  `Kopis/Neon/Tables.lean` pins down.

  This file is the first of those three, `len = 4`: pair vector `i` with vector `i + 4`, for
  `i < 4`, all with one ψ pair.  It is stated as a bound, in the same *pending* shape
  `NttLevel.lean` uses for the whole-vector levels — the loop cannot claim a uniform bound on the
  group while it is halfway through it.

  The remaining two levels (`len = 2`, four butterflies in two halves; `len = 1`, four adjacent
  pairs) have the same shape with different index arithmetic, and the Barrett pass between them
  runs over a `slice::IterMut` rather than a range, which is why it is a separate lemma rather
  than another instance of this one.
-/
import Kopis.Neon.NttLevel

open Aeneas Aeneas.Std Result
open RustKopisNeon
open RustKopisNeon.backend.neon.intrinsics

namespace Kopis.Neon

set_option maxHeartbeats 1000000

/-! ## Loops that are the same loop

The group carries six levels, and three of the shapes occur twice in it — pair `i` with `i+4`,
pair `4h+i` with `4h+i+2`, and re-centre the eight vectors.  aeneas gives each occurrence its own
constant, but the two copies are the *same* fixpoint of the *same* functional, so they are equal
by unfolding, and one proof serves both.  (The remaining pairs differ in where ψ comes from — a
broadcast ζ before the transpose, a per-lane table after it — and do need two proofs.) -/

/-- Level 2's butterfly loop and the `len = 4` one are the same loop. -/
theorem loop1_loop4_eq :
    @backend.neon.ntt.ntt_block_loop1_loop4 = @backend.neon.ntt.ntt_block_loop1_loop0 := by
  with_unfolding_all rfl

/-- Level 3's inner loop and the `len = 2` one are the same loop. -/
theorem loop1_loop1_loop0_eq :
    @backend.neon.ntt.ntt_block_loop1_loop1_loop0
      = @backend.neon.ntt.ntt_block_loop1_loop5_loop0 := by
  with_unfolding_all rfl

/-- The vectors of a group the `len = 4` pass has yet to reach, once it has advanced to `i`:
`[i, 4)` and `[i+4, 8)`. -/
def pend4 (i j : ℕ) : Prop := (i ≤ j ∧ j < 4) ∨ (4 + i ≤ j ∧ j < 8)

instance (i j : ℕ) : Decidable (pend4 i j) := by unfold pend4; infer_instance

/-- **The `len = 4` transposed level, as a bound.** -/
theorem ntt_len4_bnd (qv z zq : Vec128) (Q Zb B Bt : ℤ)
    (hQ : ∀ i < 8, (lane16 qv i).toInt = Q) (hQpos : 0 < Q) (hQlt : Q ≤ 2 ^ 14)
    (hz : ∀ i < 8, |(lane16 z i).toInt| ≤ Zb) (hZb : Zb ≤ 2 ^ 14)
    (hzq : ∀ i < 8, (2 ^ 16 : ℤ) ∣ ((lane16 zq i).toInt * Q - (lane16 z i).toInt))
    (hB0 : 0 ≤ B) (hBZ : B * Zb < 2 ^ 15 * Q) (hBt : B * Zb + 2 ^ 15 * Q ≤ 2 ^ 16 * Bt)
    (hfit : B + Bt ≤ 32767)
    (v : Array Vec128 8#usize) (iter : core.ops.range.Range Usize) (hend : iter.«end».val = 4)
    (hv : ∀ j (hj : j < 8), pend4 iter.start.val j → VecBnd (vAt v j hj) B) :
    backend.neon.ntt.ntt_block_loop1_loop0 iter qv v z zq
      ⦃ (r : Array Vec128 8#usize) => ∀ j (hj : j < 8),
          if pend4 iter.start.val j then VecBnd (vAt r j hj) (B + Bt)
          else vAt r j hj = vAt v j hj ⦄ := by
  unfold backend.neon.ntt.ntt_block_loop1_loop0
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
    apply WP.spec_bind (ct_butterfly_spec lo hiv z zq qv Q Zb B Bt hQ hQpos hQlt hz hZb hzq
      (by rw [hloe]; exact hv _ (by omega) (Or.inl ⟨by omega, by omega⟩))
      (by rw [hhie]; exact hv _ (by omega) (Or.inr ⟨by omega, by omega⟩))
      hB0 hBZ hBt hfit)
    rintro ⟨lo1, hi1'⟩ ⟨hlo1b, hhi1b, -⟩
    show (do let v1 ← Array.update v iter.start lo1
             let a ← Array.update v1 i1 hi1'
             backend.neon.ntt.ntt_block_loop1_loop0 iter1 qv a z zq)
        ⦃ (r : Array Vec128 8#usize) => ∀ j (hj : j < 8),
            if pend4 iter.start.val j then VecBnd (vAt r j hj) (B + Bt)
            else vAt r j hj = vAt v j hj ⦄
    let* ⟨ v1, hv1 ⟩ ← Array.update_spec
    let* ⟨ a, ha ⟩ ← Array.update_spec
    -- what `a` is, entry by entry
    have hav : ∀ j (hj : j < 8), vAt a j hj =
        if j = i1.val then hi1' else if j = iter.start.val then lo1 else vAt v j hj := by
      intro j hj
      rw [ha, vAt_set, hv1, vAt_set]
    apply WP.spec_mono (ntt_len4_bnd qv z zq Q Zb B Bt hQ hQpos hQlt hz hZb hzq hB0 hBZ hBt hfit
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

/-! ## `len = 2`

Two butterflies per half of the group, and the two halves are different coefficient blocks so
they take different ψ.  The inner loop is over `i < 2` at a fixed half `h`, pairing `4h + i` with
`4h + i + 2`. -/

/-- The vectors of half `h` the `len = 2` pass has yet to reach. -/
def pend2 (h i j : ℕ) : Prop :=
  (4 * h + i ≤ j ∧ j < 4 * h + 2) ∨ (4 * h + 2 + i ≤ j ∧ j < 4 * h + 4)

instance (h i j : ℕ) : Decidable (pend2 h i j) := by unfold pend2; infer_instance

theorem ntt_len2_bnd (qv z zq : Vec128) (Q Zb B Bt : ℤ)
    (hQ : ∀ i < 8, (lane16 qv i).toInt = Q) (hQpos : 0 < Q) (hQlt : Q ≤ 2 ^ 14)
    (hz : ∀ i < 8, |(lane16 z i).toInt| ≤ Zb) (hZb : Zb ≤ 2 ^ 14)
    (hzq : ∀ i < 8, (2 ^ 16 : ℤ) ∣ ((lane16 zq i).toInt * Q - (lane16 z i).toInt))
    (hB0 : 0 ≤ B) (hBZ : B * Zb < 2 ^ 15 * Q) (hBt : B * Zb + 2 ^ 15 * Q ≤ 2 ^ 16 * Bt)
    (hfit : B + Bt ≤ 32767)
    (v : Array Vec128 8#usize) (h : Usize) (hh : h.val < 2)
    (iter : core.ops.range.Range Usize) (hend : iter.«end».val = 2)
    (hv : ∀ j (hj : j < 8), pend2 h.val iter.start.val j → VecBnd (vAt v j hj) B) :
    backend.neon.ntt.ntt_block_loop1_loop5_loop0 iter qv v h z zq
      ⦃ (r : Array Vec128 8#usize) => ∀ j (hj : j < 8),
          if pend2 h.val iter.start.val j then VecBnd (vAt r j hj) (B + Bt)
          else vAt r j hj = vAt v j hj ⦄ := by
  unfold backend.neon.ntt.ntt_block_loop1_loop5_loop0
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
    apply WP.spec_bind (ct_butterfly_spec lo hiv z zq qv Q Zb B Bt hQ hQpos hQlt hz hZb hzq
      (by rw [hloe]; exact hv _ (by omega) (Or.inl ⟨by omega, by omega⟩))
      (by rw [hhie]; exact hv _ (by omega) (Or.inr ⟨by omega, by omega⟩))
      hB0 hBZ hBt hfit)
    rintro ⟨lo1, hi1'⟩ ⟨hlo1b, hhi1b, -⟩
    show (do let v1 ← Array.update v base lo1
             let a ← Array.update v1 i2 hi1'
             backend.neon.ntt.ntt_block_loop1_loop5_loop0 iter1 qv a h z zq)
        ⦃ (r : Array Vec128 8#usize) => ∀ j (hj : j < 8),
            if pend2 h.val iter.start.val j then VecBnd (vAt r j hj) (B + Bt)
            else vAt r j hj = vAt v j hj ⦄
    let* ⟨ v1, hv1 ⟩ ← Array.update_spec
    let* ⟨ a, ha ⟩ ← Array.update_spec
    have hav : ∀ j (hj : j < 8), vAt a j hj =
        if j = i2.val then hi1' else if j = base.val then lo1 else vAt v j hj := by
      intro j hj
      rw [ha, vAt_set, hv1, vAt_set]
    apply WP.spec_mono (ntt_len2_bnd qv z zq Q Zb B Bt hQ hQpos hQlt hz hZb hzq hB0 hBZ hBt hfit
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

/-! ## `len = 1`

Four adjacent pairs, four distinct coefficient blocks per lane, so a fresh ψ pair per iteration —
which is why the table hypothesis here is a `∀` over `fwd1` rather than a fixed pair. -/

/-- The vectors the `len = 1` pass has yet to reach: it walks pairs `(2r, 2r+1)` upward. -/
def pend1 (i j : ℕ) : Prop := 2 * i ≤ j ∧ j < 8

instance (i j : ℕ) : Decidable (pend1 i j) := by unfold pend1; infer_instance

theorem ntt_len1_bnd (SECOND : Bool) (qv : Vec128) (Q Zb B Bt : ℤ)
    (hQ : ∀ i < 8, (lane16 qv i).toInt = Q) (hQpos : 0 < Q) (hQlt : Q ≤ 2 ^ 14)
    (hZb : Zb ≤ 2 ^ 14)
    (hB0 : 0 ≤ B) (hBZ : B * Zb < 2 ^ 15 * Q) (hBt : B * Zb + 2 ^ 15 * Q ≤ 2 ^ 16 * Bt)
    (hfit : B + Bt ≤ 32767)
    (htbl : ∀ kk : Usize, kk.val < 16 → ∃ z zq : Vec128,
        backend.neon.ntt.fwd1 SECOND kk = ok (z, zq) ∧
        (∀ i < 8, |(lane16 z i).toInt| ≤ Zb) ∧
        (∀ i < 8, (2 ^ 16 : ℤ) ∣ ((lane16 zq i).toInt * Q - (lane16 z i).toInt)))
    (g : Usize) (hg : g.val < 4) (v : Array Vec128 8#usize)
    (iter : core.ops.range.Range Usize) (hend : iter.«end».val = 4)
    (hv : ∀ j (hj : j < 8), pend1 iter.start.val j → VecBnd (vAt v j hj) B) :
    backend.neon.ntt.ntt_block_loop1_loop6 SECOND iter qv g v
      ⦃ (r : Array Vec128 8#usize) => ∀ j (hj : j < 8),
          if pend1 iter.start.val j then VecBnd (vAt r j hj) (B + Bt)
          else vAt r j hj = vAt v j hj ⦄ := by
  unfold backend.neon.ntt.ntt_block_loop1_loop6
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
    apply WP.spec_bind (ct_butterfly_spec lo hiv z zq qv Q Zb B Bt hQ hQpos hQlt hz hZb hzq
      (by rw [hloe]; exact hv _ (by omega) ⟨by omega, by omega⟩)
      (by rw [hhie]; exact hv _ (by omega) ⟨by omega, by omega⟩)
      hB0 hBZ hBt hfit)
    rintro ⟨lo1, hi1'⟩ ⟨hlo1b, hhi1b, -⟩
    show (do let v1 ← Array.update v i2 lo1
             let i4 ← i2 + 1#usize
             let a ← Array.update v1 i4 hi1'
             backend.neon.ntt.ntt_block_loop1_loop6 SECOND iter1 qv g a)
        ⦃ (r : Array Vec128 8#usize) => ∀ j (hj : j < 8),
            if pend1 iter.start.val j then VecBnd (vAt r j hj) (B + Bt)
            else vAt r j hj = vAt v j hj ⦄
    let* ⟨ v1, hv1 ⟩ ← Array.update_spec
    let* ⟨ i4, hi4 ⟩ ← Std.Usize.add_spec (x := i2) (y := 1#usize) (by scalar_tac)
    have hi4v : i4.val = i2.val + 1 := by scalar_tac
    let* ⟨ a, ha ⟩ ← Array.update_spec
    have hav : ∀ j (hj : j < 8), vAt a j hj =
        if j = i4.val then hi1' else if j = i2.val then lo1 else vAt v j hj := by
      intro j hj
      rw [ha, vAt_set, hv1, vAt_set]
    apply WP.spec_mono (ntt_len1_bnd SECOND qv Q Zb B Bt hQ hQpos hQlt hZb hB0 hBZ hBt hfit htbl
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

/-! ## The two halves of the `len = 2` level

`h` walks the two halves of the group, each taking its own ψ pair — `fwd2` at index `2g + h`.
The inner pass leaves the whole of half `h` bounded, so the outer invariant is just "everything
from vector `4·h` on". -/

theorem ntt_len2_outer_bnd (SECOND : Bool) (qv : Vec128) (Q Zb B Bt : ℤ)
    (hQ : ∀ i < 8, (lane16 qv i).toInt = Q) (hQpos : 0 < Q) (hQlt : Q ≤ 2 ^ 14)
    (hZb : Zb ≤ 2 ^ 14)
    (hB0 : 0 ≤ B) (hBZ : B * Zb < 2 ^ 15 * Q) (hBt : B * Zb + 2 ^ 15 * Q ≤ 2 ^ 16 * Bt)
    (hfit : B + Bt ≤ 32767)
    (htbl : ∀ kk : Usize, kk.val < 8 → ∃ z zq : Vec128,
        backend.neon.ntt.fwd2 SECOND kk = ok (z, zq) ∧
        (∀ i < 8, |(lane16 z i).toInt| ≤ Zb) ∧
        (∀ i < 8, (2 ^ 16 : ℤ) ∣ ((lane16 zq i).toInt * Q - (lane16 z i).toInt)))
    (g : Usize) (hg : g.val < 4) (v : Array Vec128 8#usize)
    (iter : core.ops.range.Range Usize) (hend : iter.«end».val = 2)
    (hv : ∀ j (hj : j < 8), 4 * iter.start.val ≤ j → VecBnd (vAt v j hj) B) :
    backend.neon.ntt.ntt_block_loop1_loop5 SECOND iter qv g v
      ⦃ (r : Array Vec128 8#usize) => ∀ j (hj : j < 8),
          if 4 * iter.start.val ≤ j then VecBnd (vAt r j hj) (B + Bt)
          else vAt r j hj = vAt v j hj ⦄ := by
  unfold backend.neon.ntt.ntt_block_loop1_loop5
  by_cases hlt : iter.start.val < iter.«end».val
  · let* ⟨ o, iter1, ho, hstart', hend' ⟩ ← core.iter.range.IteratorRange.next_Usize_some_spec
    rw [ho]
    simp only
    have hh2 : iter.start.val < 2 := by omega
    let* ⟨ i, hi ⟩ ← Std.Usize.mul_spec (x := 2#usize) (y := g) (by scalar_tac)
    let* ⟨ i1, hi1 ⟩ ← Std.Usize.add_spec (x := i) (y := iter.start) (by scalar_tac)
    obtain ⟨z, zq, hzt, hz, hzq⟩ := htbl i1 (by scalar_tac)
    rw [hzt, bind_tc_ok]
    apply WP.spec_bind (ntt_len2_bnd qv z zq Q Zb B Bt hQ hQpos hQlt hz hZb hzq hB0 hBZ hBt hfit
      v iter.start hh2 ⟨0#usize, 2#usize⟩ rfl (by
        intro j hj hpend
        exact hv j hj (by unfold pend2 at hpend; scalar_tac)))
    intro v1 hv1
    apply WP.spec_mono (ntt_len2_outer_bnd SECOND qv Q Zb B Bt hQ hQpos hQlt hZb hB0 hBZ hBt hfit
      htbl g hg v1 iter1 (by rw [hend']; exact hend) (by
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

/-! ## The two levels the group carries *before* the transpose

Levels 2 and 3 pair whole vectors — `i` with `i+4` at level 2, `4h+i` with `4h+i+2` at level 3 —
so they have the shapes above, but they run before the transpose and their ψ is a broadcast ζ
rather than a per-lane table entry.  Level 2 is `ntt_len4_bnd` with a broadcast `z`, and needs
nothing new.  Levels 3 and 4 fetch their own ζ inside the loop, so they do.

The ψ indices are the ones the flat `k` counter reaches over group `g`: `8 + 2g + h` at level 3
and `16 + 4g + r` at level 4. -/

/-- **Level 3, as a bound.**  Like `ntt_len2_outer_bnd`, with ζ broadcast in place of the
per-lane table. -/
theorem ntt_lvl3_bnd (SECOND : Bool) (qv : Vec128) (Q Zb B Bt : ℤ)
    (hQ : ∀ i < 8, (lane16 qv i).toInt = Q) (hQpos : 0 < Q) (hQlt : Q ≤ 2 ^ 14)
    (hZb : Zb ≤ 2 ^ 14)
    (hB0 : 0 ≤ B) (hBZ : B * Zb < 2 ^ 15 * Q) (hBt : B * Zb + 2 ^ 15 * Q ≤ 2 ^ 16 * Bt)
    (hfit : B + Bt ≤ 32767)
    (hzeta : ∀ kk : Usize, kk.val < 256 → ∃ zi zqi : I16,
        backend.crt.zeta SECOND kk = ok zi ∧ backend.crt.zeta_q SECOND kk = ok zqi ∧
        |zi.val| ≤ Zb ∧ (2 ^ 16 : ℤ) ∣ (zqi.val * Q - zi.val))
    (g : Usize) (hg : g.val < 4) (v : Array Vec128 8#usize)
    (iter : core.ops.range.Range Usize) (hend : iter.«end».val = 2)
    (hv : ∀ j (hj : j < 8), 4 * iter.start.val ≤ j → VecBnd (vAt v j hj) B) :
    backend.neon.ntt.ntt_block_loop1_loop1 SECOND iter qv g v
      ⦃ (r : Array Vec128 8#usize) => ∀ j (hj : j < 8),
          if 4 * iter.start.val ≤ j then VecBnd (vAt r j hj) (B + Bt)
          else vAt r j hj = vAt v j hj ⦄ := by
  unfold backend.neon.ntt.ntt_block_loop1_loop1
  by_cases hlt : iter.start.val < iter.«end».val
  · let* ⟨ o, iter1, ho, hstart', hend' ⟩ ← core.iter.range.IteratorRange.next_Usize_some_spec
    rw [ho]
    simp only
    have hh2 : iter.start.val < 2 := by omega
    let* ⟨ i, hi ⟩ ← Std.Usize.mul_spec (x := 2#usize) (y := g) (by scalar_tac)
    let* ⟨ i1, hi1 ⟩ ← Std.Usize.add_spec (x := 8#usize) (y := i) (by scalar_tac)
    let* ⟨ kk, hkk ⟩ ← Std.Usize.add_spec (x := i1) (y := iter.start) (by scalar_tac)
    obtain ⟨zi, zqi, hzi, hzqi, hzib, hzqib⟩ := hzeta kk (by scalar_tac)
    rw [hzi, bind_tc_ok]
    obtain ⟨z, hz, hzl⟩ := dup_n_s16_spec zi
    rw [hz, bind_tc_ok, hzqi, bind_tc_ok]
    obtain ⟨zq, hzq, hzql⟩ := dup_n_s16_spec zqi
    rw [hzq, bind_tc_ok]
    have hzlv : ∀ i < 8, |(lane16 z i).toInt| ≤ Zb := by
      intro i hi; rw [hzl i hi]; exact hzib
    have hzqlv : ∀ i < 8, (2 ^ 16 : ℤ) ∣ ((lane16 zq i).toInt * Q - (lane16 z i).toInt) := by
      intro i hi; rw [hzl i hi, hzql i hi]; exact hzqib
    rw [loop1_loop1_loop0_eq]
    apply WP.spec_bind (ntt_len2_bnd qv z zq Q Zb B Bt hQ hQpos hQlt hzlv hZb hzqlv hB0 hBZ hBt
      hfit v iter.start hh2 ⟨0#usize, 2#usize⟩ rfl (by
        intro j hj hpend
        exact hv j hj (by unfold pend2 at hpend; scalar_tac)))
    intro v1 hv1
    apply WP.spec_mono (ntt_lvl3_bnd SECOND qv Q Zb B Bt hQ hQpos hQlt hZb hB0 hBZ hBt hfit
      hzeta g hg v1 iter1 (by rw [hend']; exact hend) (by
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

/-- **Level 4, as a bound.**  Like `ntt_len1_bnd`, with ζ broadcast in place of `fwd1`. -/
theorem ntt_lvl4_bnd (SECOND : Bool) (qv : Vec128) (Q Zb B Bt : ℤ)
    (hQ : ∀ i < 8, (lane16 qv i).toInt = Q) (hQpos : 0 < Q) (hQlt : Q ≤ 2 ^ 14)
    (hZb : Zb ≤ 2 ^ 14)
    (hB0 : 0 ≤ B) (hBZ : B * Zb < 2 ^ 15 * Q) (hBt : B * Zb + 2 ^ 15 * Q ≤ 2 ^ 16 * Bt)
    (hfit : B + Bt ≤ 32767)
    (hzeta : ∀ kk : Usize, kk.val < 256 → ∃ zi zqi : I16,
        backend.crt.zeta SECOND kk = ok zi ∧ backend.crt.zeta_q SECOND kk = ok zqi ∧
        |zi.val| ≤ Zb ∧ (2 ^ 16 : ℤ) ∣ (zqi.val * Q - zi.val))
    (g : Usize) (hg : g.val < 4) (v : Array Vec128 8#usize)
    (iter : core.ops.range.Range Usize) (hend : iter.«end».val = 4)
    (hv : ∀ j (hj : j < 8), pend1 iter.start.val j → VecBnd (vAt v j hj) B) :
    backend.neon.ntt.ntt_block_loop1_loop3 SECOND iter qv g v
      ⦃ (r : Array Vec128 8#usize) => ∀ j (hj : j < 8),
          if pend1 iter.start.val j then VecBnd (vAt r j hj) (B + Bt)
          else vAt r j hj = vAt v j hj ⦄ := by
  unfold backend.neon.ntt.ntt_block_loop1_loop3
  by_cases hlt : iter.start.val < iter.«end».val
  · let* ⟨ o, iter1, ho, hstart', hend' ⟩ ← core.iter.range.IteratorRange.next_Usize_some_spec
    rw [ho]
    simp only
    have hr4 : iter.start.val < 4 := by omega
    let* ⟨ i, hi ⟩ ← Std.Usize.mul_spec (x := 4#usize) (y := g) (by scalar_tac)
    let* ⟨ i1, hi1 ⟩ ← Std.Usize.add_spec (x := 16#usize) (y := i) (by scalar_tac)
    let* ⟨ kk, hkk ⟩ ← Std.Usize.add_spec (x := i1) (y := iter.start) (by scalar_tac)
    obtain ⟨zi, zqi, hzi, hzqi, hzib, hzqib⟩ := hzeta kk (by scalar_tac)
    rw [hzi, bind_tc_ok]
    obtain ⟨z, hz, hzl⟩ := dup_n_s16_spec zi
    rw [hz, bind_tc_ok, hzqi, bind_tc_ok]
    obtain ⟨zq, hzq, hzql⟩ := dup_n_s16_spec zqi
    rw [hzq, bind_tc_ok]
    have hz' : ∀ i < 8, |(lane16 z i).toInt| ≤ Zb := by
      intro i hi; rw [hzl i hi]; exact hzib
    have hzq' : ∀ i < 8, (2 ^ 16 : ℤ) ∣ ((lane16 zq i).toInt * Q - (lane16 z i).toInt) := by
      intro i hi; rw [hzl i hi, hzql i hi]; exact hzqib
    let* ⟨ i2, hi2 ⟩ ← Std.Usize.mul_spec (x := 2#usize) (y := iter.start) (by scalar_tac)
    have hi2v : i2.val = 2 * iter.start.val := by scalar_tac
    let* ⟨ lo, hlo ⟩ ← Array.index_usize_spec v i2 (by scalar_tac)
    have hloe : lo = vAt v i2.val (by omega) := by rw [hlo]; rfl
    let* ⟨ i3, hi3 ⟩ ← Std.Usize.add_spec (x := i2) (y := 1#usize) (by scalar_tac)
    have hi3v : i3.val = i2.val + 1 := by scalar_tac
    let* ⟨ hiv, hhi ⟩ ← Array.index_usize_spec v i3 (by scalar_tac)
    have hhie : hiv = vAt v i3.val (by omega) := by rw [hhi]; rfl
    apply WP.spec_bind (ct_butterfly_spec lo hiv z zq qv Q Zb B Bt hQ hQpos hQlt hz' hZb hzq'
      (by rw [hloe]; exact hv _ (by omega) ⟨by omega, by omega⟩)
      (by rw [hhie]; exact hv _ (by omega) ⟨by omega, by omega⟩)
      hB0 hBZ hBt hfit)
    rintro ⟨lo1, hi1'⟩ ⟨hlo1b, hhi1b, -⟩
    show (do let v1 ← Array.update v i2 lo1
             let i4 ← i2 + 1#usize
             let a ← Array.update v1 i4 hi1'
             backend.neon.ntt.ntt_block_loop1_loop3 SECOND iter1 qv g a)
        ⦃ (r : Array Vec128 8#usize) => ∀ j (hj : j < 8),
            if pend1 iter.start.val j then VecBnd (vAt r j hj) (B + Bt)
            else vAt r j hj = vAt v j hj ⦄
    let* ⟨ v1, hv1 ⟩ ← Array.update_spec
    let* ⟨ i4, hi4 ⟩ ← Std.Usize.add_spec (x := i2) (y := 1#usize) (by scalar_tac)
    have hi4v : i4.val = i2.val + 1 := by scalar_tac
    let* ⟨ a, ha ⟩ ← Array.update_spec
    have hav : ∀ j (hj : j < 8), vAt a j hj =
        if j = i4.val then hi1' else if j = i2.val then lo1 else vAt v j hj := by
      intro j hj
      rw [ha, vAt_set, hv1, vAt_set]
    apply WP.spec_mono (ntt_lvl4_bnd SECOND qv Q Zb B Bt hQ hQpos hQlt hZb hB0 hBZ hBt hfit hzeta
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

end Kopis.Neon
