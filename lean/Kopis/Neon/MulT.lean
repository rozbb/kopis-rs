/-
  # Kopis/Neon/MulT.lean — the accumulate loop of `mul_transpose`, on the NEON branch.

  `NttMatrix::mul_transpose`'s innermost loop is `mul`'s with the outer index of `self` playing
  the role of the inner one: entry `(j,k)` of `Aᵀ·s` accumulates over `ii`, reading `A[ii][j]`
  against `s[ii][k]`.  It walks a *shared-name* loop that calls the dispatching
  `arithmetic.ntt.pointwise_mul_acc`, so it needs the dispatch theorem first — and on this
  backend that is free, because `backend::neon::cpu::available` extracts as `ok true`.
-/
import Kopis.Neon.Reduce

open Aeneas Aeneas.Std Result
open RustKopisNeon
open scoped BigOperators

namespace Kopis.Neon

set_option maxHeartbeats 1000000

/-! ## The dispatch point

`available` is `ok true`, so there is no portable branch to discharge — §1(a) of the plan. -/

theorem pointwise_mul_acc_neon (acc : Array I32 512#usize)
    (lhs rhs : arithmetic.ntt.NttElem) (Bl Br Ba : ℤ) (h0 : 0 ≤ Bl) (_h1 : 0 ≤ Br)
    (hl : ∀ t < 512, |(lhs.val[t]!).val| ≤ Bl)
    (hr : ∀ t < 512, |(rhs.val[t]!).val| ≤ Br)
    (ha : ∀ t < 512, |(acc.val[t]!).val| ≤ Ba)
    (hfit : Ba + Bl * Br < 2 ^ 31) :
    arithmetic.ntt.pointwise_mul_acc acc lhs rhs
      ⦃ (r : Array I32 512#usize) => ∀ t < 512,
          (r.val[t]!).val = (acc.val[t]!).val + (lhs.val[t]!).val * (rhs.val[t]!).val ∧
          |(r.val[t]!).val| ≤ Ba + Bl * Br ⦄ := by
  have hstep : ∀ t < 512,
      |(acc.val[t]!).val + (lhs.val[t]!).val * (rhs.val[t]!).val| ≤ Ba + Bl * Br := by
    intro t ht
    have hprod : |(lhs.val[t]!).val * (rhs.val[t]!).val| ≤ Bl * Br := by
      rw [abs_mul]
      exact mul_le_mul (hl t ht) (hr t ht) (abs_nonneg _) h0
    have h1 := abs_le.mp (ha t ht)
    have h2 := abs_le.mp hprod
    rw [abs_le]
    omega
  unfold arithmetic.ntt.pointwise_mul_acc
  rw [show backend.neon.cpu.available = ok true from rfl, bind_tc_ok, if_pos rfl]
  apply WP.spec_mono (pointwise_acc_int acc lhs rhs (Ba + Bl * Br) hstep (by omega))
  intro r hr' t ht
  exact ⟨hr' t ht, by rw [hr' t ht]; exact hstep t ht⟩

/-! ## The accumulate loop -/

private theorem sumT_Ico_peel {M : Type*} [AddCommMonoid M] (f : ℕ → M) {a b : ℕ} (h : a < b) :
    ∑ j ∈ Finset.Ico a b, f j = f a + ∑ j ∈ Finset.Ico (a + 1) b, f j := by
  rw [show a + 1 = a.succ from rfl, Nat.Ico_succ_left_eq_erase_Ico,
    Finset.add_sum_erase _ f (Finset.mem_Ico.mpr ⟨le_refl a, h⟩)]

/-- **The accumulate loop of `mul_transpose`.**  `B` is the common lane bound of both operand
families; after `n` terms the accumulator is inside `n·B²`. -/
theorem mulT_inner_neon {X Y Z : Usize}
    (iter : core.ops.range.Range Usize)
    (self : arithmetic.ntt.NttMatrix X Y) (other : arithmetic.ntt.NttMatrix X Z)
    (j k : Usize) (acc : Array I32 512#usize) (B : ℤ) (h0 : 0 ≤ B) (hB : 4 * (B * B) < 2 ^ 31)
    (hj : j.val < Y.val) (hk : k.val < Z.val)
    (hstart : iter.start.val ≤ X.val) (hend : iter.«end».val = X.val) (hX : X.val ≤ 4)
    (hself : ∀ ii t, ii < X.val → t < 512 →
      |(((self.val[ii]!).val[j.val]!).val[t]!).val| ≤ B)
    (hother : ∀ ii t, ii < X.val → t < 512 →
      |(((other.val[ii]!).val[k.val]!).val[t]!).val| ≤ B)
    (hacc : ∀ t < 512, |(acc.val[t]!).val| ≤ (iter.start.val : ℤ) * (B * B)) :
    arithmetic.ntt.NttMatrix.mul_transpose_loop0_loop0_loop0 iter self other j k acc
      ⦃ (p : (arithmetic.ntt.NttMatrix X Y) × (arithmetic.ntt.NttMatrix X Z) ×
             (Array I32 512#usize)) =>
          p.1 = self ∧ p.2.1 = other ∧
          (∀ t < 512, (p.2.2.val[t]!).val = (acc.val[t]!).val
            + ∑ ii ∈ Finset.Ico iter.start.val X.val,
                (((self.val[ii]!).val[j.val]!).val[t]!).val
                  * (((other.val[ii]!).val[k.val]!).val[t]!).val) ∧
          (∀ t < 512, |(p.2.2.val[t]!).val| ≤ (X.val : ℤ) * (B * B)) ⦄ := by
  unfold arithmetic.ntt.NttMatrix.mul_transpose_loop0_loop0_loop0
  by_cases hlt : iter.start.val < iter.«end».val
  · let* ⟨o, iter1, ho, hstart', hend'⟩ ← core.iter.range.IteratorRange.next_Usize_some_spec
    rw [ho]
    simp only
    have hi_lt : iter.start.val < X.val := by omega
    have hsi : iter.start.val < self.val.length := by have := self.property; scalar_tac
    let* ⟨a, ha⟩ ← Array.index_usize_spec self iter.start hsi
    have ha' : a = self.val[iter.start.val]! := by
      rw [ha, getElem!_pos self.val iter.start.val hsi]
    have haj : j.val < a.val.length := by have := a.property; scalar_tac
    let* ⟨ne, hne⟩ ← Array.index_usize_spec a j haj
    have hne' : ne = (self.val[iter.start.val]!).val[j.val]! := by
      rw [hne, ha', getElem!_pos (self.val[iter.start.val]!).val j.val (by rw [← ha']; exact haj)]
    have hoi : iter.start.val < other.val.length := by have := other.property; scalar_tac
    let* ⟨a1, ha1⟩ ← Array.index_usize_spec other iter.start hoi
    have ha1' : a1 = other.val[iter.start.val]! := by
      rw [ha1, getElem!_pos other.val iter.start.val hoi]
    have ha1k : k.val < a1.val.length := by have := a1.property; scalar_tac
    let* ⟨ne1, hne1⟩ ← Array.index_usize_spec a1 k ha1k
    have hne1' : ne1 = (other.val[iter.start.val]!).val[k.val]! := by
      rw [hne1, ha1',
        getElem!_pos (other.val[iter.start.val]!).val k.val (by rw [← ha1']; exact ha1k)]
    have hstz : (0 : ℤ) ≤ (iter.start.val : ℤ) := Int.natCast_nonneg _
    have hstle : ((iter.start.val : ℤ)) ≤ 3 := by
      exact_mod_cast (by omega : iter.start.val ≤ 3)
    have hBB : (0 : ℤ) ≤ B * B := mul_nonneg h0 h0
    apply WP.spec_bind (pointwise_mul_acc_neon acc ne ne1 B B
      ((iter.start.val : ℤ) * (B * B)) h0 h0
      (by rw [hne']; exact fun t ht => hself iter.start.val t hi_lt ht)
      (by rw [hne1']; exact fun t ht => hother iter.start.val t hi_lt ht) hacc
      (by nlinarith))
    intro acc1 hacc1
    apply WP.spec_mono (mulT_inner_neon iter1 self other j k acc1 B h0 hB hj hk
      (by omega) (by rw [hend']; exact hend) hX hself hother
      (fun t ht => by
        refine le_trans (hacc1 t ht).2 ?_
        rw [hstart']
        push_cast
        linarith))
    rintro ⟨p1, p2, p3⟩ ⟨hp1, hp2, hp3, hp4⟩
    simp only at hp1 hp2 hp3 hp4
    refine ⟨hp1, hp2, ?_, hp4⟩
    intro t ht
    rw [hp3 t ht, (hacc1 t ht).1, hstart', hne', hne1', sumT_Ico_peel _ hi_lt]
    ring
  · let* ⟨o, iter1, hnone, _⟩ ← core.iter.range.IteratorRange.next_Usize_none_spec
    rw [hnone]
    simp only [WP.spec_ok]
    refine ⟨trivial, trivial, fun t ht => ?_, fun t ht => ?_⟩
    · rw [Finset.Ico_eq_empty (by omega), Finset.sum_empty, add_zero]
    · refine le_trans (hacc t ht) ?_
      have : ((iter.start.val : ℤ)) ≤ (X.val : ℤ) := by
        exact_mod_cast (by omega : iter.start.val ≤ X.val)
      nlinarith [mul_nonneg h0 h0]
termination_by iter.«end».val - iter.start.val
decreasing_by scalar_decr_tac

end Kopis.Neon
