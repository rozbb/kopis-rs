/-
  # Kopis/Neon/MulT.lean — the accumulate loop of `mul_transpose`, on the NEON branch.

  `NttMatrix::mul_transpose`'s innermost loop is `mul`'s with the outer index of `self` playing
  the role of the inner one: entry `(j,k)` of `Aᵀ·s` accumulates over `ii`, reading `A[ii][j]`
  against `s[ii][k]`.  It walks a *shared-name* loop that calls the dispatching
  `arithmetic.ntt_arith.pointwise_mul_acc`, so it needs the dispatch theorem first — and on this
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
    (lhs rhs : arithmetic.ntt_arith.NttElem) (Bl Br Ba : ℤ) (h0 : 0 ≤ Bl) (_h1 : 0 ≤ Br)
    (hl : ∀ t < 512, |(lhs.val[t]!).val| ≤ Bl)
    (hr : ∀ t < 512, |(rhs.val[t]!).val| ≤ Br)
    (ha : ∀ t < 512, |(acc.val[t]!).val| ≤ Ba)
    (hfit : Ba + Bl * Br < 2 ^ 31) :
    arithmetic.ntt_arith.pointwise_mul_acc acc lhs rhs
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
  unfold arithmetic.ntt_arith.pointwise_mul_acc
  rw [show backend.neon.cpu.available = ok true from rfl, bind_tc_ok, if_pos rfl]
  apply WP.spec_mono (pointwise_acc_int acc lhs rhs (Ba + Bl * Br) hstep (by omega))
  intro r hr' t ht
  exact ⟨hr' t ht, by rw [hr' t ht]; exact hstep t ht⟩

/-! ## The accumulate loop -/

private theorem sumT_Ico_peel {M : Type*} [AddCommMonoid M] (f : ℕ → M) {a b : ℕ} (h : a < b) :
    ∑ j ∈ Finset.Ico a b, f j = f a + ∑ j ∈ Finset.Ico (a + 1) b, f j := by
  rw [show a + 1 = a.succ from rfl, Nat.Ico_succ_left_eq_erase_Ico,
    Finset.add_sum_erase _ f (Finset.mem_Ico.mpr ⟨le_refl a, h⟩)]
end Kopis.Neon
