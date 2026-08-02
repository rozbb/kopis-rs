import Kopis.Properties.MulTranspose
open Aeneas Aeneas.Std Result RustKopisSerial
open scoped BigOperators
namespace Kopis.Properties

set_option maxHeartbeats 2000000
set_option maxRecDepth 4000

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

/-- Innermost loop of `mul` (over k): for fixed i,j, increments
`result[i][k] += self[i][j]·other[j][k]` for `k ∈ [iter.start, Z)`. -/
theorem mul_loop0_loop0_loop0_spec {X Y Z : Usize}
    (iter : core.ops.range.Range Usize)
    (self : Mat X Y) (other : Mat Y Z) (result : Mat X Z) (i j : Usize)
    (hi : i.val < X.val) (hj : j.val < Y.val)
    (hstart : iter.start.val ≤ Z.val) (hend : iter.«end».val = Z.val) :
    arithmetic.matrix_arith.Matrix.mul_loop0_loop0_loop0 iter self other result i j
      ⦃ (p : (Mat X Y) × (Mat Y Z) × (Mat X Z)) =>
          p.1 = self ∧ p.2.1 = other ∧
          ∀ (ii kk : Nat),
            toRingElem ((p.2.2.val[ii]!).val[kk]!)
              = if ii = i.val ∧ iter.start.val ≤ kk ∧ kk < Z.val then
                  toRingElem ((result.val[ii]!).val[kk]!)
                    + toRingElem ((self.val[i.val]!).val[j.val]!)
                        * toRingElem ((other.val[j.val]!).val[kk]!)
                else toRingElem ((result.val[ii]!).val[kk]!) ⦄ := by
  unfold arithmetic.matrix_arith.Matrix.mul_loop0_loop0_loop0
  by_cases hlt : iter.start.val < iter.«end».val
  · let* ⟨ o, iter1, ho, hstart', hend' ⟩ ← core.iter.range.IteratorRange.next_Usize_some_spec
    rw [ho]; simp only
    have hk_lt : iter.start.val < Z.val := by scalar_tac
    let* ⟨ a, imb, ha_val, himb ⟩ ←
      Array.index_mut_usize_spec result i (by have := result.property; have := hi; scalar_tac)
    let* ⟨ re, imb1, hre_val, himb1 ⟩ ←
      Array.index_mut_usize_spec a iter.start (by have := a.property; scalar_tac)
    let* ⟨ a1, ha1 ⟩ ← Array.index_usize_spec self i (by have := self.property; have := hi; scalar_tac)
    let* ⟨ re1, hre1 ⟩ ← Array.index_usize_spec a1 j (by have := a1.property; have := hj; scalar_tac)
    let* ⟨ a2, ha2 ⟩ ← Array.index_usize_spec other j (by have := other.property; have := hj; scalar_tac)
    let* ⟨ re2, hre2 ⟩ ← Array.index_usize_spec a2 iter.start (by have := a2.property; scalar_tac)
    let* ⟨ re3, hre3 ⟩ ← ring_mul_acc_poly_spec
    have hstartnew : iter1.start.val ≤ Z.val := by rw [hstart']; scalar_tac
    have hendnew : iter1.«end».val = Z.val := by rw [hend']; exact hend
    have hlenX : result.val.length = X.val := result.property
    have ha_pos : a = result.val[i.val]! :=
      ha_val.trans (getElem!_pos result.val i.val (by rw [hlenX]; exact hi)).symm
    have ha1_pos : a1 = self.val[i.val]! :=
      ha1.trans (getElem!_pos self.val i.val (by rw [self.property]; exact hi)).symm
    have ha2_pos : a2 = other.val[j.val]! :=
      ha2.trans (getElem!_pos other.val j.val (by rw [other.property]; exact hj)).symm
    have hre_pos : re = (result.val[i.val]!).val[iter.start.val]! := by
      rw [hre_val, ha_pos]
      exact (getElem!_pos _ iter.start.val (by have := (result.val[i.val]!).property; scalar_tac)).symm
    have hre1_pos : re1 = (self.val[i.val]!).val[j.val]! := by
      rw [hre1, ha1_pos]
      exact (getElem!_pos _ j.val (by have := (self.val[i.val]!).property; scalar_tac)).symm
    have hre2_pos : re2 = (other.val[j.val]!).val[iter.start.val]! := by
      rw [hre2, ha2_pos]
      exact (getElem!_pos _ iter.start.val (by have := (other.val[j.val]!).property; scalar_tac)).symm
    apply WP.spec_mono
      (mul_loop0_loop0_loop0_spec iter1 self other (imb (imb1 re3)) i j
        hi hj hstartnew hendnew)
    rintro ⟨p1, p2, p3⟩ ⟨hp1, hp2, hp3⟩
    refine ⟨hp1, hp2, ?_⟩
    intro ii kk
    rw [hp3 ii kk, hstart']
    have ha4_entry : toRingElem (((imb (imb1 re3)).val[ii]!).val[kk]!)
        = if ii = i.val ∧ kk = iter.start.val then
            toRingElem ((result.val[i.val]!).val[iter.start.val]!)
              + toRingElem ((self.val[i.val]!).val[j.val]!) * toRingElem ((other.val[j.val]!).val[iter.start.val]!)
          else toRingElem ((result.val[ii]!).val[kk]!) := by
      rw [himb, Std.Array.set_val_eq, getElem!_list_set result.val i.val _ ii (by rw [hlenX]; exact hi)]
      by_cases hii : ii = i.val
      · rw [if_pos hii, himb1, Std.Array.set_val_eq,
          getElem!_list_set a.val iter.start.val _ kk (by rw [a.property]; exact hk_lt)]
        by_cases hkk : kk = iter.start.val
        · rw [if_pos hkk, if_pos ⟨hii, hkk⟩, hre3, hre_pos, hre1_pos, hre2_pos]
        · rw [if_neg hkk, if_neg (by rintro ⟨_, h⟩; exact hkk h), ha_pos, hii]
      · rw [if_neg hii, if_neg (by rintro ⟨h, _⟩; exact hii h)]
    rw [ha4_entry]
    by_cases hii : ii = i.val
    · subst hii
      by_cases hkk : kk = iter.start.val
      · subst hkk
        rw [if_neg (by rintro ⟨_, h, _⟩; omega),
            if_pos (⟨rfl, rfl⟩ : i.val = i.val ∧ iter.start.val = iter.start.val),
            if_pos (⟨rfl, le_refl _, hk_lt⟩ :
              i.val = i.val ∧ iter.start.val ≤ iter.start.val ∧ iter.start.val < Z.val)]
      · by_cases hkkr : iter.start.val + 1 ≤ kk ∧ kk < Z.val
        · rw [if_pos ⟨rfl, hkkr.1, hkkr.2⟩, if_neg (by rintro ⟨_, h⟩; exact hkk h),
              if_pos ⟨rfl, by omega, hkkr.2⟩]
        · rw [if_neg (by rintro ⟨_, h1, h2⟩; exact hkkr ⟨h1, h2⟩),
              if_neg (by rintro ⟨_, h⟩; exact hkk h),
              if_neg (by rintro ⟨_, h1, h2⟩; exact hkkr ⟨by omega, h2⟩)]
    · rw [if_neg (by rintro ⟨h, _⟩; exact hii h), if_neg (by rintro ⟨h, _⟩; exact hii h),
          if_neg (by rintro ⟨h, _⟩; exact hii h)]
  · let* ⟨ o, iter1, hnone, _ ⟩ ← core.iter.range.IteratorRange.next_Usize_none_spec
    rw [hnone]; simp only [WP.spec_ok]
    refine ⟨by trivial, by trivial, ?_⟩
    intro ii kk
    have hsz : iter.start.val = Z.val := by scalar_tac
    show toRingElem ((result.val[ii]!).val[kk]!) = _
    rw [if_neg (by rintro ⟨_, h1, h2⟩; omega)]
  termination_by Z.val - iter.start.val
  decreasing_by scalar_decr_tac

/-- Middle loop of `mul` (over j): for fixed i, accumulates into row i of result
`result[i][k] += Σ_{j ∈ [iter.start, Y)} self[i][j]·other[j][k]`. -/
theorem mul_loop0_loop0_spec {X Y Z : Usize}
    (iter : core.ops.range.Range Usize)
    (self : Mat X Y) (other : Mat Y Z) (result : Mat X Z) (i : Usize)
    (hi : i.val < X.val)
    (hstart : iter.start.val ≤ Y.val) (hend : iter.«end».val = Y.val) :
    arithmetic.matrix_arith.Matrix.mul_loop0_loop0 iter self other result i
      ⦃ (p : (Mat X Y) × (Mat Y Z) × (Mat X Z)) =>
          p.1 = self ∧ p.2.1 = other ∧
          ∀ (ii kk : Nat),
            toRingElem ((p.2.2.val[ii]!).val[kk]!)
              = toRingElem ((result.val[ii]!).val[kk]!)
                + (if ii = i.val ∧ kk < Z.val then
                    ∑ jj ∈ Finset.Ico iter.start.val Y.val,
                      toRingElem ((self.val[i.val]!).val[jj]!) * toRingElem ((other.val[jj]!).val[kk]!)
                   else 0) ⦄ := by
  unfold arithmetic.matrix_arith.Matrix.mul_loop0_loop0
  by_cases hlt : iter.start.val < iter.«end».val
  · let* ⟨ o, iter1, ho, hstart', hend' ⟩ ← core.iter.range.IteratorRange.next_Usize_some_spec
    rw [ho]; simp only
    have hj_lt : iter.start.val < Y.val := by scalar_tac
    let* ⟨ self1, other1, result1, hs1, ho1, hres1 ⟩ ←
      mul_loop0_loop0_loop0_spec { start := 0#usize, «end» := Z } self other result i iter.start
        hi hj_lt (by scalar_tac) rfl
    rw [hs1, ho1]
    have hstartnew : iter1.start.val ≤ Y.val := by rw [hstart']; scalar_tac
    have hendnew : iter1.«end».val = Y.val := by rw [hend']; exact hend
    apply WP.spec_mono
      (mul_loop0_loop0_spec iter1 self other result1 i hi hstartnew hendnew)
    rintro ⟨p1, p2, p3⟩ ⟨hp1, hp2, hp3⟩
    refine ⟨hp1, hp2, ?_⟩
    intro ii kk
    rw [hp3 ii kk, hstart', hres1 ii kk]
    by_cases hik : ii = i.val ∧ kk < Z.val
    · rw [if_pos ⟨hik.1, Nat.zero_le _, hik.2⟩, if_pos hik, if_pos hik, sum_Ico_peel _ hj_lt]
      abel
    · rw [if_neg (by rintro ⟨h1, _, h3⟩; exact hik ⟨h1, h3⟩), if_neg hik, if_neg hik]
  · let* ⟨ o, iter1, hnone, _ ⟩ ← core.iter.range.IteratorRange.next_Usize_none_spec
    rw [hnone]; simp only [WP.spec_ok]
    refine ⟨by trivial, by trivial, ?_⟩
    intro ii kk
    have hsz : iter.start.val = Y.val := by scalar_tac
    show toRingElem ((result.val[ii]!).val[kk]!)
        = toRingElem ((result.val[ii]!).val[kk]!)
          + (if ii = i.val ∧ kk < Z.val then
              ∑ jj ∈ Finset.Ico iter.start.val Y.val,
                toRingElem ((self.val[i.val]!).val[jj]!) * toRingElem ((other.val[jj]!).val[kk]!)
             else 0)
    rw [hsz, Finset.Ico_self, Finset.sum_empty]
    split_ifs <;> abel
  termination_by Y.val - iter.start.val
  decreasing_by scalar_decr_tac

/-- Outer loop of `mul` (over i): writes row `i` of result with the full contraction
`result[i][k] += Σ_{j ∈ [0, Y)} self[i][j]·other[j][k]` for `i ∈ [iter.start, X)`. -/
theorem mul_loop0_spec {X Y Z : Usize}
    (iter : core.ops.range.Range Usize)
    (self : Mat X Y) (other : Mat Y Z) (result : Mat X Z)
    (hstart : iter.start.val ≤ X.val) (hend : iter.«end».val = X.val) :
    arithmetic.matrix_arith.Matrix.mul_loop0 iter self other result
      ⦃ (r : Mat X Z) =>
          ∀ (ii kk : Nat),
            toRingElem ((r.val[ii]!).val[kk]!)
              = if iter.start.val ≤ ii ∧ ii < X.val ∧ kk < Z.val then
                  toRingElem ((result.val[ii]!).val[kk]!)
                    + ∑ jj ∈ Finset.Ico 0 Y.val,
                        toRingElem ((self.val[ii]!).val[jj]!) * toRingElem ((other.val[jj]!).val[kk]!)
                else toRingElem ((result.val[ii]!).val[kk]!) ⦄ := by
  unfold arithmetic.matrix_arith.Matrix.mul_loop0
  by_cases hlt : iter.start.val < iter.«end».val
  · let* ⟨ o, iter1, ho, hstart', hend' ⟩ ← core.iter.range.IteratorRange.next_Usize_some_spec
    rw [ho]; simp only
    have hi_lt : iter.start.val < X.val := by scalar_tac
    let* ⟨ self1, other1, result1, hs1, ho1, hres1 ⟩ ←
      mul_loop0_loop0_spec { start := 0#usize, «end» := Y } self other result iter.start
        hi_lt (by scalar_tac) rfl
    rw [hs1, ho1]
    have hstartnew : iter1.start.val ≤ X.val := by rw [hstart']; scalar_tac
    have hendnew : iter1.«end».val = X.val := by rw [hend']; exact hend
    apply WP.spec_mono (mul_loop0_spec iter1 self other result1 hstartnew hendnew)
    intro r hr ii kk
    rw [hr ii kk, hstart', hres1 ii kk]
    by_cases hiieq : ii = iter.start.val
    · subst hiieq
      by_cases hkz : kk < Z.val
      · rw [if_neg (by rintro ⟨h, _⟩; omega), if_pos ⟨rfl, hkz⟩,
            if_pos ⟨le_refl _, hi_lt, hkz⟩]
      · rw [if_neg (by rintro ⟨_, _, h⟩; exact hkz h),
            if_neg (by rintro ⟨_, h⟩; exact hkz h),
            if_neg (by rintro ⟨_, _, h⟩; exact hkz h)]
        abel
    · by_cases hcih : iter.start.val + 1 ≤ ii ∧ ii < X.val ∧ kk < Z.val
      · rw [if_pos hcih, if_neg (by rintro ⟨h, _⟩; exact hiieq h),
            if_pos ⟨by omega, hcih.2.1, hcih.2.2⟩]
        abel
      · rw [if_neg hcih, if_neg (by rintro ⟨h, _⟩; exact hiieq h),
            if_neg (by rintro ⟨h1, h2, h3⟩; exact hcih ⟨by omega, h2, h3⟩)]
        abel
  · let* ⟨ o, iter1, hnone, _ ⟩ ← core.iter.range.IteratorRange.next_Usize_none_spec
    rw [hnone]; simp only [WP.spec_ok]
    intro ii kk
    have hsx : iter.start.val = X.val := by scalar_tac
    rw [if_neg (by rintro ⟨h1, h2, _⟩; omega)]
  termination_by X.val - iter.start.val
  decreasing_by scalar_decr_tac

/-- **Correctness of `Matrix::mul`** at the physical `2¹⁶` abstraction:
`(self · other)[i][k] = Σ_j self[i][j]·other[j][k]`. -/
theorem matrix_mul_spec {X Y Z : Usize} (self : Mat X Y) (other : Mat Y Z) :
    arithmetic.matrix_arith.Matrix.mul self other
      ⦃ (r : Mat X Z) =>
          ∀ (i : Nat) (_hi : i < X.val) (k : Nat) (_hk : k < Z.val),
            toRingElem ((r.val[i]!).val[k]!)
              = ∑ jj ∈ Finset.range Y.val,
                  toRingElem ((self.val[i]!).val[jj]!) * toRingElem ((other.val[jj]!).val[k]!) ⦄ := by
  unfold arithmetic.matrix_arith.Matrix.mul
  rw [show (arithmetic.matrix_arith.Matrix.Insts.CoreDefaultDefault.default X Z : Result (Mat X Z))
        = ok (Array.repeat X (Array.repeat Z (Array.repeat 256#usize 0#u16))) from rfl]
  simp only [bind_tc_ok]
  apply WP.spec_mono
    (mul_loop0_spec { start := 0#usize, «end» := X } self other
      (Array.repeat X (Array.repeat Z (Array.repeat 256#usize 0#u16))) (by scalar_tac) rfl)
  intro r hr i hi k hk
  rw [hr i k]
  have hrow : (Array.repeat X (Array.repeat Z (Array.repeat 256#usize 0#u16))).val[i]!
      = Array.repeat Z (Array.repeat 256#usize 0#u16) := by
    rw [show (Array.repeat X (Array.repeat Z (Array.repeat 256#usize 0#u16))).val
          = List.replicate X.val (Array.repeat Z (Array.repeat 256#usize 0#u16)) from rfl,
      getElem!_pos _ i (by rw [List.length_replicate]; exact hi), List.getElem_replicate]
  have helem : ((Array.repeat Z (Array.repeat 256#usize 0#u16)).val[k]!)
      = Array.repeat 256#usize 0#u16 := by
    rw [show (Array.repeat Z (Array.repeat 256#usize 0#u16)).val
          = List.replicate Z.val (Array.repeat 256#usize 0#u16) from rfl,
      getElem!_pos _ k (by rw [List.length_replicate]; exact hk), List.getElem_replicate]
  have hzero : toRingElem (((Array.repeat X (Array.repeat Z (Array.repeat 256#usize 0#u16))).val[i]!).val[k]!)
      = 0 := by simp only [hrow, helem, toRingElem_repeat_zero]
  rw [hzero, if_pos ⟨Nat.zero_le _, hi, hk⟩, Finset.range_eq_Ico]
  abel

end Kopis.Properties
