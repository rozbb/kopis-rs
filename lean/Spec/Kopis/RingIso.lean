import Mathlib.RingTheory.AdjoinRoot
import Spec.Kopis.Lemmas

/-! # `Poly m` is the negacyclic ring

The spec says `R13` is `(ℤ/2¹³ℤ)[X]/(X²⁵⁶ + 1)`, but `Spec.lean` represents it as a vector of 256
coefficients with a schoolbook `Poly.mul`. Here we prove that representation is faithful:
`Poly.toQuot` is a bijection onto Mathlib's `(ZMod m)[X] ⧸ (X²⁵⁶ + 1)` that preserves `+`, `-`
and `*`. -/

namespace Spec.Kopis

open Polynomial

/-- `(ZMod m)[X] ⧸ (X²⁵⁶ + 1)`. `AdjoinRoot f` is defined as `(ZMod m)[X] ⧸ (f)`. -/
abbrev NegacyclicRing (m : ℕ) := AdjoinRoot (X ^ 256 + 1 : (ZMod m)[X])

variable {m : ℕ}

/-- Interprets the coefficient vector `a` as `a₀ + a₁X + ⋯ + a₂₅₅X²⁵⁵` in the quotient. -/
noncomputable def Poly.toQuot (a : Poly m) : NegacyclicRing m :=
  ∑ i : Fin 256, a[i] • AdjoinRoot.root _ ^ i.val

/-- `toQuot a` is the class of the polynomial `∑ aᵢXⁱ`. -/
theorem Poly.toQuot_eq_mk (a : Poly m) :
    a.toQuot = AdjoinRoot.mk _ (∑ i : Fin 256, C a[i] * X ^ i.val) := by
  simp [Poly.toQuot, map_sum, Algebra.smul_def, AdjoinRoot.algebraMap_eq]

private theorem root_pow_256 :
    (AdjoinRoot.root (X ^ 256 + 1 : (ZMod m)[X])) ^ 256 = -1 := by
  have h := AdjoinRoot.eval₂_root (X ^ 256 + 1 : (ZMod m)[X])
  simp only [eval₂_add, eval₂_X_pow, eval₂_one] at h
  exact eq_neg_of_add_eq_zero_left h

theorem Poly.toQuot_add (a b : Poly m) : (a + b).toQuot = a.toQuot + b.toQuot := by
  simp only [Poly.toQuot, ← Finset.sum_add_distrib, ← add_smul]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [Poly.add_def, Poly.add]

theorem Poly.toQuot_sub (a b : Poly m) : (a - b).toQuot = a.toQuot - b.toQuot := by
  simp only [Poly.toQuot, ← Finset.sum_sub_distrib, ← sub_smul]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [HSub.hSub, Sub.sub, Poly.sub]

/-- `toQuot` as a sum over `range 256`, which is how `convCoeff` is indexed. -/
private theorem toQuot_range (a : Poly m) :
    a.toQuot = ∑ i ∈ Finset.range 256, a[i]! • AdjoinRoot.root _ ^ i := by
  rw [Poly.toQuot, ← Fin.sum_univ_eq_sum_range (fun i => a[i]! • AdjoinRoot.root _ ^ i)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [getElem!_pos a i.val i.isLt, Fin.getElem_fin]

/-- The only term of output coefficient `p` that `aᵢ·bⱼ` contributes to is `p = (i+j) mod 256`,
and `Xⁱ⁺ʲ` is `±X^((i+j) mod 256)`. -/
private theorem sum_convContrib (a b : Poly m) {i j : ℕ} (hi : i < 256) (hj : j < 256) :
    ∑ p ∈ Finset.range 256, convContrib a b i j p • AdjoinRoot.root (X ^ 256 + 1 : (ZMod m)[X]) ^ p
      = (a[i]! * b[j]!) • AdjoinRoot.root _ ^ (i + j) := by
  have hlt : (i + j) % 256 < 256 := Nat.mod_lt _ (by decide)
  simp only [convContrib, ite_smul, zero_smul]
  rw [Finset.sum_ite_eq _ _ (fun p => if i + j < 256 then _ else _), if_pos (Finset.mem_range.mpr hlt)]
  conv_rhs => rw [← Nat.mod_add_div (i + j) 256, pow_add, pow_mul, root_pow_256]
  split_ifs with h
  · rw [Nat.div_eq_of_lt h]; simp
  · have : (i + j) / 256 = 1 := by omega
    rw [this]; simp [neg_smul]

theorem Poly.toQuot_mul (a b : Poly m) : (a * b).toQuot = a.toQuot * b.toQuot := by
  rw [toQuot_range, toQuot_range a, toQuot_range b, Finset.sum_mul_sum]
  have hcoeff : ∀ p ∈ Finset.range 256, (a * b)[p]! • AdjoinRoot.root _ ^ p
      = ∑ i ∈ Finset.range 256, ∑ j ∈ Finset.range 256,
          convContrib a b i j p • AdjoinRoot.root (X ^ 256 + 1 : (ZMod m)[X]) ^ p := by
    intro p hp
    have hp : p < 256 := Finset.mem_range.mp hp
    rw [getElem!_pos _ p hp, show a * b = Poly.mul a b from rfl, mul_get a b p hp, convCoeff,
      Finset.sum_smul]
    simp only [Finset.sum_smul]
  rw [Finset.sum_congr rfl hcoeff, Finset.sum_comm]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [sum_convContrib a b (Finset.mem_range.mp hi) (Finset.mem_range.mp hj), pow_add,
    smul_mul_smul_comm]

set_option maxRecDepth 8000 in
theorem Poly.toQuot_bijective (hm : 1 < m) : Function.Bijective (Poly.toQuot (m := m)) := by
  haveI : Fact (1 < m) := ⟨hm⟩
  have hmonic : (X ^ 256 + 1 : (ZMod m)[X]).Monic := by
    rw [← C_1]; exact monic_X_pow_add_C _ (by omega)
  let pb := AdjoinRoot.powerBasis' hmonic
  have hdim : pb.dim = 256 := by
    simp only [pb, AdjoinRoot.powerBasis'_dim]
    exact natDegree_X_pow_add_C
  let e : Poly m ≃ (Fin pb.dim → ZMod m) :=
    { toFun := fun a i => a[Fin.cast hdim i]
      invFun := fun f => Vector.ofFn fun i => f (Fin.cast hdim.symm i)
      left_inv := fun a => by ext i hi; simp
      right_inv := fun f => by funext i; simp }
  have h : Poly.toQuot (m := m) = pb.basis.equivFun.symm ∘ e := by
    funext a
    simp only [Function.comp_apply, Module.Basis.equivFun_symm_apply, PowerBasis.coe_basis, e,
      Equiv.coe_fn_mk, Poly.toQuot, pb, AdjoinRoot.powerBasis'_gen]
    exact (Fintype.sum_equiv (finCongr hdim) _ _ fun i => rfl).symm
  rw [h]
  exact pb.basis.equivFun.symm.bijective.comp e.bijective

/-- The spec's `R n` is `(ℤ/2ⁿℤ)[X]/(X²⁵⁶ + 1)`: `toQuot` is a bijection that preserves the ring
operations. -/
theorem R_equiv_quotient (n : ℕ) (hn : 0 < n) :
    Function.Bijective (Poly.toQuot (m := 2 ^ n)) ∧
    (∀ a b : R n, (a + b).toQuot = a.toQuot + b.toQuot) ∧
    (∀ a b : R n, (a - b).toQuot = a.toQuot - b.toQuot) ∧
    (∀ a b : R n, (a * b).toQuot = a.toQuot * b.toQuot) :=
  ⟨Poly.toQuot_bijective (Nat.one_lt_two_pow_iff.mpr (Nat.pos_iff_ne_zero.mp hn)),
    Poly.toQuot_add, Poly.toQuot_sub, Poly.toQuot_mul⟩

end Spec.Kopis
