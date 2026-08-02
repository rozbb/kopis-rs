import Kopis.Properties.MatrixArith
open Aeneas Aeneas.Std Result RustKopisSerial
open scoped BigOperators
namespace Kopis.Properties

set_option maxHeartbeats 2000000
set_option maxRecDepth 4000

abbrev Mat (X Y : Usize) := arithmetic.matrix_arith.Matrix X Y
-- `AddCommMonoid (Polynomial m)` now comes from `Spec.Kopis` (single canonical `+`).

private theorem getElem!_list_set {α : Type _} [Inhabited α] (l : List α) (j : ℕ)
    (v : α) (k : ℕ) (hj : j < l.length) :
    (l.set j v)[k]! = if k = j then v else l[k]! := by
  by_cases h : k = j
  · subst h
    rw [getElem!_pos _ k (by rw [List.length_set]; exact hj), List.getElem_set_self, if_pos rfl]
  · by_cases hk : k < l.length
    · rw [getElem!_pos _ k (by rw [List.length_set]; exact hk),
        List.getElem_set_of_ne (Ne.symm h), ← getElem!_pos _ k hk, if_neg h]
    · rw [getElem!_neg _ k (by rw [List.length_set]; exact hk), getElem!_neg _ k hk, if_neg h]

private theorem sum_Ico_peel {M : Type*} [AddCommMonoid M] (f : ℕ → M) {a b : ℕ} (h : a < b) :
    ∑ j ∈ Finset.Ico a b, f j = f a + ∑ j ∈ Finset.Ico (a + 1) b, f j := by
  rw [show a + 1 = a.succ from rfl, Nat.Ico_succ_left_eq_erase_Ico,
      Finset.add_sum_erase _ f (Finset.mem_Ico.mpr ⟨le_refl a, h⟩)]

/-- Innermost loop of `mul_transpose` (over k): for fixed i,j, increments
`result[j][k] += self[i][j]·other[i][k]` for `k ∈ [iter.start, Z)`. -/
theorem mul_transpose_loop0_loop0_loop0_spec {X Y Z : Usize}
    (iter : core.ops.range.Range Usize)
    (self : Mat X Y) (other : Mat X Z) (result : Mat Y Z) (i j : Usize)
    (hi : i.val < X.val) (hj : j.val < Y.val)
    (hstart : iter.start.val ≤ Z.val) (hend : iter.«end».val = Z.val) :
    arithmetic.matrix_arith.Matrix.mul_transpose_loop0_loop0_loop0 iter self other result i j
      ⦃ (p : (Mat X Y) × (Mat X Z) × (Mat Y Z)) =>
          p.1 = self ∧ p.2.1 = other ∧
          ∀ (jj kk : Nat),
            toRingElem ((p.2.2.val[jj]!).val[kk]!)
              = if jj = j.val ∧ iter.start.val ≤ kk ∧ kk < Z.val then
                  toRingElem ((result.val[jj]!).val[kk]!)
                    + toRingElem ((self.val[i.val]!).val[j.val]!)
                        * toRingElem ((other.val[i.val]!).val[kk]!)
                else toRingElem ((result.val[jj]!).val[kk]!) ⦄ := by
  unfold arithmetic.matrix_arith.Matrix.mul_transpose_loop0_loop0_loop0
  by_cases hlt : iter.start.val < iter.«end».val
  · let* ⟨ o, iter1, ho, hstart', hend' ⟩ ← core.iter.range.IteratorRange.next_Usize_some_spec
    rw [ho]; simp only
    have hk_lt : iter.start.val < Z.val := by scalar_tac
    let* ⟨ a, imb, ha_val, himb ⟩ ←
      Array.index_mut_usize_spec result j (by have := result.property; have := hj; scalar_tac)
    let* ⟨ re, imb1, hre_val, himb1 ⟩ ←
      Array.index_mut_usize_spec a iter.start (by have := a.property; scalar_tac)
    let* ⟨ a1, ha1 ⟩ ← Array.index_usize_spec self i (by have := self.property; have := hi; scalar_tac)
    let* ⟨ re1, hre1 ⟩ ← Array.index_usize_spec a1 j (by have := a1.property; have := hj; scalar_tac)
    let* ⟨ a2, ha2 ⟩ ← Array.index_usize_spec other i (by have := other.property; have := hi; scalar_tac)
    let* ⟨ re2, hre2 ⟩ ← Array.index_usize_spec a2 iter.start (by have := a2.property; scalar_tac)
    let* ⟨ re3, hre3 ⟩ ← ring_mul_acc_poly_spec
    -- a3 = imb1 re3 = set a k re3;  a4 = imb a3 = set result j a3
    have hstartnew : iter1.start.val ≤ Z.val := by rw [hstart']; scalar_tac
    have hendnew : iter1.«end».val = Z.val := by rw [hend']; exact hend
    -- positional (`!`) forms of the extracted entries
    have hlenY : result.val.length = Y.val := result.property
    have ha_pos : a = result.val[j.val]! :=
      ha_val.trans (getElem!_pos result.val j.val (by rw [hlenY]; exact hj)).symm
    have ha1_pos : a1 = self.val[i.val]! :=
      ha1.trans (getElem!_pos self.val i.val (by rw [self.property]; exact hi)).symm
    have ha2_pos : a2 = other.val[i.val]! :=
      ha2.trans (getElem!_pos other.val i.val (by rw [other.property]; exact hi)).symm
    have hre_pos : re = (result.val[j.val]!).val[iter.start.val]! := by
      rw [hre_val, ha_pos]
      exact (getElem!_pos _ iter.start.val (by have := (result.val[j.val]!).property; scalar_tac)).symm
    have hre1_pos : re1 = (self.val[i.val]!).val[j.val]! := by
      rw [hre1, ha1_pos]
      exact (getElem!_pos _ j.val (by have := (self.val[i.val]!).property; scalar_tac)).symm
    have hre2_pos : re2 = (other.val[i.val]!).val[iter.start.val]! := by
      rw [hre2, ha2_pos]
      exact (getElem!_pos _ iter.start.val (by have := (other.val[i.val]!).property; scalar_tac)).symm
    apply WP.spec_mono
      (mul_transpose_loop0_loop0_loop0_spec iter1 self other (imb (imb1 re3)) i j
        hi hj hstartnew hendnew)
    rintro ⟨p1, p2, p3⟩ ⟨hp1, hp2, hp3⟩
    refine ⟨hp1, hp2, ?_⟩
    intro jj kk
    rw [hp3 jj kk, hstart']
    -- entry of a4 = imb (imb1 re3) at (jj, kk)
    have ha4_entry : toRingElem (((imb (imb1 re3)).val[jj]!).val[kk]!)
        = if jj = j.val ∧ kk = iter.start.val then
            toRingElem ((result.val[j.val]!).val[iter.start.val]!)
              + toRingElem ((self.val[i.val]!).val[j.val]!) * toRingElem ((other.val[i.val]!).val[iter.start.val]!)
          else toRingElem ((result.val[jj]!).val[kk]!) := by
      rw [himb, Std.Array.set_val_eq, getElem!_list_set result.val j.val _ jj (by rw [hlenY]; exact hj)]
      by_cases hjj : jj = j.val
      · rw [if_pos hjj, himb1, Std.Array.set_val_eq,
          getElem!_list_set a.val iter.start.val _ kk (by rw [a.property]; exact hk_lt)]
        by_cases hkk : kk = iter.start.val
        · rw [if_pos hkk, if_pos ⟨hjj, hkk⟩, hre3, hre_pos, hre1_pos, hre2_pos]
        · rw [if_neg hkk, if_neg (by rintro ⟨_, h⟩; exact hkk h), ha_pos, hjj]
      · rw [if_neg hjj, if_neg (by rintro ⟨h, _⟩; exact hjj h)]
    rw [ha4_entry]
    -- combine with the target `if`.  Outer `if` = IH condition (start+1 ≤ kk),
    -- inner `if` = a4's own write (kk = start), target `if` = start ≤ kk.
    by_cases hjj : jj = j.val
    · subst hjj
      by_cases hkk : kk = iter.start.val
      · subst hkk
        rw [if_neg (by rintro ⟨_, h, _⟩; omega),
            if_pos (⟨rfl, rfl⟩ : j.val = j.val ∧ iter.start.val = iter.start.val),
            if_pos (⟨rfl, le_refl _, hk_lt⟩ :
              j.val = j.val ∧ iter.start.val ≤ iter.start.val ∧ iter.start.val < Z.val)]
      · by_cases hkkr : iter.start.val + 1 ≤ kk ∧ kk < Z.val
        · rw [if_pos ⟨rfl, hkkr.1, hkkr.2⟩, if_neg (by rintro ⟨_, h⟩; exact hkk h),
              if_pos ⟨rfl, by omega, hkkr.2⟩]
        · rw [if_neg (by rintro ⟨_, h1, h2⟩; exact hkkr ⟨h1, h2⟩),
              if_neg (by rintro ⟨_, h⟩; exact hkk h),
              if_neg (by rintro ⟨_, h1, h2⟩; exact hkkr ⟨by omega, h2⟩)]
    · rw [if_neg (by rintro ⟨h, _⟩; exact hjj h), if_neg (by rintro ⟨h, _⟩; exact hjj h),
          if_neg (by rintro ⟨h, _⟩; exact hjj h)]
  · let* ⟨ o, iter1, hnone, _ ⟩ ← core.iter.range.IteratorRange.next_Usize_none_spec
    rw [hnone]; simp only [WP.spec_ok]
    refine ⟨by trivial, by trivial, ?_⟩
    intro jj kk
    have hsz : iter.start.val = Z.val := by scalar_tac
    show toRingElem ((result.val[jj]!).val[kk]!) = _
    rw [if_neg (by rintro ⟨_, h1, h2⟩; omega)]
  termination_by Z.val - iter.start.val
  decreasing_by scalar_decr_tac

/-- Middle loop of `mul_transpose` (over j): for fixed i, increments every row
`jj ∈ [iter.start, Y)` of result by `self[i][jj]·other[i][·]`. -/
theorem mul_transpose_loop0_loop0_spec {X Y Z : Usize}
    (iter : core.ops.range.Range Usize)
    (self : Mat X Y) (other : Mat X Z) (result : Mat Y Z) (i : Usize)
    (hi : i.val < X.val)
    (hstart : iter.start.val ≤ Y.val) (hend : iter.«end».val = Y.val) :
    arithmetic.matrix_arith.Matrix.mul_transpose_loop0_loop0 iter self other result i
      ⦃ (p : (Mat X Y) × (Mat X Z) × (Mat Y Z)) =>
          p.1 = self ∧ p.2.1 = other ∧
          ∀ (jj kk : Nat),
            toRingElem ((p.2.2.val[jj]!).val[kk]!)
              = if iter.start.val ≤ jj ∧ jj < Y.val ∧ kk < Z.val then
                  toRingElem ((result.val[jj]!).val[kk]!)
                    + toRingElem ((self.val[i.val]!).val[jj]!) * toRingElem ((other.val[i.val]!).val[kk]!)
                else toRingElem ((result.val[jj]!).val[kk]!) ⦄ := by
  unfold arithmetic.matrix_arith.Matrix.mul_transpose_loop0_loop0
  by_cases hlt : iter.start.val < iter.«end».val
  · let* ⟨ o, iter1, ho, hstart', hend' ⟩ ← core.iter.range.IteratorRange.next_Usize_some_spec
    rw [ho]; simp only
    have hj'_lt : iter.start.val < Y.val := by scalar_tac
    let* ⟨ self1, other1, result1, hs1, ho1, hres1 ⟩ ←
      mul_transpose_loop0_loop0_loop0_spec { start := 0#usize, «end» := Z } self other result i
        iter.start hi hj'_lt (by scalar_tac) rfl
    rw [hs1, ho1]
    have hstartnew : iter1.start.val ≤ Y.val := by rw [hstart']; scalar_tac
    have hendnew : iter1.«end».val = Y.val := by rw [hend']; exact hend
    apply WP.spec_mono
      (mul_transpose_loop0_loop0_spec iter1 self other result1 i hi hstartnew hendnew)
    rintro ⟨p1, p2, p3⟩ ⟨hp1, hp2, hp3⟩
    refine ⟨hp1, hp2, ?_⟩
    intro jj kk
    rw [hp3 jj kk, hstart', hres1 jj kk]
    -- combine: C_ih (start+1 ≤ jj), C_inner (jj = start), C_target (start ≤ jj)
    by_cases hjeq : jj = iter.start.val
    · subst hjeq
      by_cases hkz : kk < Z.val
      · rw [if_neg (by rintro ⟨h, _⟩; omega),
            if_pos ⟨rfl, Nat.zero_le _, hkz⟩,
            if_pos ⟨le_refl _, hj'_lt, hkz⟩]
      · rw [if_neg (by rintro ⟨_, _, h⟩; exact hkz h),
            if_neg (by rintro ⟨_, _, h⟩; exact hkz h),
            if_neg (by rintro ⟨_, _, h⟩; exact hkz h)]
    · by_cases hcih : iter.start.val + 1 ≤ jj ∧ jj < Y.val ∧ kk < Z.val
      · rw [if_pos hcih, if_neg (by rintro ⟨h, _⟩; exact hjeq h),
            if_pos ⟨by omega, hcih.2.1, hcih.2.2⟩]
      · rw [if_neg hcih, if_neg (by rintro ⟨h, _⟩; exact hjeq h),
            if_neg (by rintro ⟨h1, h2, h3⟩; exact hcih ⟨by omega, h2, h3⟩)]
  · let* ⟨ o, iter1, hnone, _ ⟩ ← core.iter.range.IteratorRange.next_Usize_none_spec
    rw [hnone]; simp only [WP.spec_ok]
    refine ⟨by trivial, by trivial, ?_⟩
    intro jj kk
    have hsz : iter.start.val = Y.val := by scalar_tac
    show toRingElem ((result.val[jj]!).val[kk]!) = _
    rw [if_neg (by rintro ⟨h1, h2, _⟩; omega)]
  termination_by Y.val - iter.start.val
  decreasing_by scalar_decr_tac

/-- Outer loop of `mul_transpose` (over i): accumulates `result += self[i]ᵀ·other[i]`
for `i ∈ [iter.start, X)`. -/
theorem mul_transpose_loop0_spec {X Y Z : Usize}
    (iter : core.ops.range.Range Usize)
    (self : Mat X Y) (other : Mat X Z) (result : Mat Y Z)
    (hstart : iter.start.val ≤ X.val) (hend : iter.«end».val = X.val) :
    arithmetic.matrix_arith.Matrix.mul_transpose_loop0 iter self other result
      ⦃ (r : Mat Y Z) =>
          ∀ (jj kk : Nat),
            toRingElem ((r.val[jj]!).val[kk]!)
              = toRingElem ((result.val[jj]!).val[kk]!)
                + (if jj < Y.val ∧ kk < Z.val then
                    ∑ ii ∈ Finset.Ico iter.start.val X.val,
                      toRingElem ((self.val[ii]!).val[jj]!) * toRingElem ((other.val[ii]!).val[kk]!)
                   else 0) ⦄ := by
  unfold arithmetic.matrix_arith.Matrix.mul_transpose_loop0
  by_cases hlt : iter.start.val < iter.«end».val
  · let* ⟨ o, iter1, ho, hstart', hend' ⟩ ← core.iter.range.IteratorRange.next_Usize_some_spec
    rw [ho]; simp only
    have hi_lt : iter.start.val < X.val := by scalar_tac
    let* ⟨ self1, other1, result1, hs1, ho1, hres1 ⟩ ←
      mul_transpose_loop0_loop0_spec { start := 0#usize, «end» := Y } self other result iter.start
        hi_lt (by scalar_tac) rfl
    rw [hs1, ho1]
    have hstartnew : iter1.start.val ≤ X.val := by rw [hstart']; scalar_tac
    have hendnew : iter1.«end».val = X.val := by rw [hend']; exact hend
    apply WP.spec_mono (mul_transpose_loop0_spec iter1 self other result1 hstartnew hendnew)
    intro r hr jj kk
    rw [hr jj kk, hstart', hres1 jj kk]
    by_cases hjk : jj < Y.val ∧ kk < Z.val
    · rw [if_pos hjk, if_pos ⟨Nat.zero_le _, hjk.1, hjk.2⟩, if_pos hjk, sum_Ico_peel _ hi_lt]
      abel
    · rw [if_neg (by rintro ⟨_, h1, h2⟩; exact hjk ⟨h1, h2⟩), if_neg hjk, if_neg hjk]
  · let* ⟨ o, iter1, hnone, _ ⟩ ← core.iter.range.IteratorRange.next_Usize_none_spec
    rw [hnone]; simp only [WP.spec_ok]
    intro jj kk
    have hsx : iter.start.val = X.val := by scalar_tac
    rw [hsx, Finset.Ico_self, Finset.sum_empty]
    split_ifs <;> abel

/-- **Correctness of `Matrix::mul_transpose`** at the physical `2¹⁶` abstraction:
`(self ᵀ · other)[j][k] = Σ_i self[i][j]·other[i][k]`. -/
theorem matrix_mul_transpose_spec {X Y Z : Usize}
    (self : Mat X Y) (other : Mat X Z) :
    arithmetic.matrix_arith.Matrix.mul_transpose self other
      ⦃ (r : Mat Y Z) =>
          ∀ (j : Nat) (_hj : j < Y.val) (k : Nat) (_hk : k < Z.val),
            toRingElem ((r.val[j]!).val[k]!)
              = ∑ ii ∈ Finset.range X.val,
                  toRingElem ((self.val[ii]!).val[j]!) * toRingElem ((other.val[ii]!).val[k]!) ⦄ := by
  unfold arithmetic.matrix_arith.Matrix.mul_transpose
  rw [show (arithmetic.matrix_arith.Matrix.Insts.CoreDefaultDefault.default Y Z : Result (Mat Y Z))
        = ok (Array.repeat Y (Array.repeat Z (Array.repeat 256#usize 0#u16))) from rfl]
  simp only [bind_tc_ok]
  apply WP.spec_mono
    (mul_transpose_loop0_spec { start := 0#usize, «end» := X } self other
      (Array.repeat Y (Array.repeat Z (Array.repeat 256#usize 0#u16))) (by scalar_tac) rfl)
  intro r hr j hj k hk
  rw [hr j k]
  -- the initial `result` is all-zero, so `toRingElem result[j][k] = 0`
  have hrow : (Array.repeat Y (Array.repeat Z (Array.repeat 256#usize 0#u16))).val[j]!
      = Array.repeat Z (Array.repeat 256#usize 0#u16) := by
    rw [show (Array.repeat Y (Array.repeat Z (Array.repeat 256#usize 0#u16))).val
          = List.replicate Y.val (Array.repeat Z (Array.repeat 256#usize 0#u16)) from rfl,
      getElem!_pos _ j (by rw [List.length_replicate]; exact hj), List.getElem_replicate]
  have helem : ((Array.repeat Z (Array.repeat 256#usize 0#u16)).val[k]!)
      = Array.repeat 256#usize 0#u16 := by
    rw [show (Array.repeat Z (Array.repeat 256#usize 0#u16)).val
          = List.replicate Z.val (Array.repeat 256#usize 0#u16) from rfl,
      getElem!_pos _ k (by rw [List.length_replicate]; exact hk), List.getElem_replicate]
  have hzero : toRingElem (((Array.repeat Y (Array.repeat Z (Array.repeat 256#usize 0#u16))).val[j]!).val[k]!)
      = 0 := by simp only [hrow, helem, toRingElem_repeat_zero]
  rw [hzero, if_pos ⟨hj, hk⟩]
  simp
  abel

end Kopis.Properties
