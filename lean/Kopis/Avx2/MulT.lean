/-
  # Kopis/Avx2/MulT.lean — the accumulate loop of `mul_transpose`, on the AVX2 branch.

  `NttMatrix::mul_transpose`'s innermost loop is `mul`'s with the outer index of `self` playing
  the role of the inner one: entry `(j,k)` of `Aᵀ·s` accumulates over `ii`, reading `A[ii][j]`
  against `s[ii][k]`.  Because the two are *different extracted constants*, the loop walk has to
  be done twice; the argument is `Kopis/Avx2/Reduce.lean`'s `mul_inner_avx` verbatim with the
  indices moved, and it consumes the same `pointwise_mul_acc_avx`.
-/
import Kopis.Avx2.Reduce

open Aeneas Aeneas.Std Result
open RustKopisAvx2
open scoped BigOperators

namespace Kopis.Avx2

set_option maxHeartbeats 1000000

private theorem sumT_Ico_peel {M : Type*} [AddCommMonoid M] (f : ℕ → M) {a b : ℕ} (h : a < b) :
    ∑ j ∈ Finset.Ico a b, f j = f a + ∑ j ∈ Finset.Ico (a + 1) b, f j := by
  rw [show a + 1 = a.succ from rfl, Nat.Ico_succ_left_eq_erase_Ico,
    Finset.add_sum_erase _ f (Finset.mem_Ico.mpr ⟨le_refl a, h⟩)]

/-- **The accumulate loop of `mul_transpose`.**  `B` is the common lane bound of both operand
families; after `n` terms the accumulator is inside `n·B²`. -/
theorem mulT_inner_avx {X Y Z : Usize} (hb : backend.avx2.cpu.available = ok true)
    (iter : core.ops.range.Range Usize)
    (self : arithmetic.ntt.NttMatrix X Y) (other : arithmetic.ntt.NttMatrix X Z)
    (j k : Usize) (acc : Array I32 512#usize) (B : ℤ) (h0 : 0 ≤ B) (hB : 4 * (B * B) < 2 ^ 31)
    (hj : j.val < Y.val) (hk : k.val < Z.val)
    (hstart : iter.start.val ≤ X.val) (hend : iter.«end».val = X.val) (hX : X.val ≤ 4)
    (hself : ∀ ii t, ii < X.val → t < 512 →
      |(i16View ((self.val[ii]!).val[j.val]!) t).toInt| ≤ B)
    (hother : ∀ ii t, ii < X.val → t < 512 →
      |(i16View ((other.val[ii]!).val[k.val]!) t).toInt| ≤ B)
    (hacc : ∀ t < 512, |(i32View acc t).toInt| ≤ (iter.start.val : ℤ) * (B * B)) :
    arithmetic.ntt.NttMatrix.mul_transpose_loop0_loop0_loop0 iter self other j k acc
      ⦃ (p : (arithmetic.ntt.NttMatrix X Y) × (arithmetic.ntt.NttMatrix X Z) ×
             (Array I32 512#usize)) =>
          p.1 = self ∧ p.2.1 = other ∧
          (∀ t < 512, (i32View p.2.2 t).toInt = (i32View acc t).toInt
            + ∑ ii ∈ Finset.Ico iter.start.val X.val,
                (i16View ((self.val[ii]!).val[j.val]!) t).toInt
                  * (i16View ((other.val[ii]!).val[k.val]!) t).toInt) ∧
          (∀ t < 512, |(i32View p.2.2 t).toInt| ≤ (X.val : ℤ) * (B * B)) ⦄ := by
  unfold arithmetic.ntt.NttMatrix.mul_transpose_loop0_loop0_loop0
  by_cases hlt : iter.start.val < iter.«end».val
  · let* ⟨o, iter1, ho, hstart', hend'⟩ ← core.iter.range.IteratorRange.next_Usize_some_spec
    rw [ho]; simp only
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
    apply WP.spec_bind (pointwise_mul_acc_avx hb acc ne ne1 B B
      ((iter.start.val : ℤ) * (B * B)) h0 h0
      (by rw [hne']; exact fun t ht => hself iter.start.val t hi_lt ht)
      (by rw [hne1']; exact fun t ht => hother iter.start.val t hi_lt ht) hacc
      (by nlinarith))
    intro acc1 hacc1
    apply WP.spec_mono (mulT_inner_avx hb iter1 self other j k acc1 B h0 hB hj hk
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
    rw [hnone]; simp only [WP.spec_ok]
    refine ⟨trivial, trivial, fun t ht => ?_, fun t ht => ?_⟩
    · rw [Finset.Ico_eq_empty (by omega), Finset.sum_empty, add_zero]
    · refine le_trans (hacc t ht) ?_
      have : ((iter.start.val : ℤ)) ≤ (X.val : ℤ) := by
        exact_mod_cast (by omega : iter.start.val ≤ X.val)
      nlinarith [mul_nonneg h0 h0]
termination_by iter.«end».val - iter.start.val
decreasing_by scalar_decr_tac

/-- The `i32` view of a zero-filled accumulator. -/
theorem i32View_zero (t : ℕ) (ht : t < 512) :
    (i32View (Array.repeat 512#usize (0#i32)) t).toInt = 0 := by
  unfold i32View
  rw [Array.repeat_val, getElem!_pos _ t
      (by rw [List.length_replicate]; show t < 512; omega),
    List.getElem_replicate]
  rfl

/-- Both halves of an `NttOK` block are inside 5376, which is the common operand bound the
accumulate loop wants. -/
theorem NttOK_lane_bound {g : ℕ → ℤ} {ne : Array I16 512#usize} (h : NttOK g ne)
    (t : ℕ) (ht : t < 512) : |(i16View ne t).toInt| ≤ 5376 := by
  obtain ⟨h1, h2, _, _⟩ := h
  by_cases hlow : t < 256
  · exact le_trans (h1 t hlow) (by norm_num)
  · have := h2 (t - 256) (by omega)
    rwa [show 256 + (t - 256) = t from by omega] at this

end Kopis.Avx2
