import Kopis.Properties.CoerceBridge10
import Kopis.Properties.MatrixSerialize
import Kopis.Properties.GenSecretTop
open Aeneas Aeneas.Std Result RustKopis
open scoped BigOperators
namespace Kopis.Properties

open arithmetic.ring_arith (RingElem)

set_option maxHeartbeats 1000000
set_option maxRecDepth 4000

/-- Spec-side evaluation of `innerProduct`'s `Id.run` loop. -/
theorem innerProduct_get {m ℓ : ℕ} (v w : Spec.Kopis.PolyVector m ℓ) :
    Spec.Kopis.innerProduct v w = ∑ i : Fin ℓ, v[i.val]'i.isLt * w[i.val]'i.isLt := by
  set g : ℕ → Spec.Kopis.Polynomial m :=
    fun j => if hj : j < ℓ then v[j]'hj * w[j]'hj else 0 with hg
  have hFS : (∑ i : Fin ℓ, v[i.val]'i.isLt * w[i.val]'i.isLt) = ∑ j ∈ Finset.range ℓ, g j := by
    rw [← Fin.sum_univ_eq_sum_range g ℓ]
    exact Finset.sum_congr rfl fun j _ => by simp only [hg, j.isLt, dif_pos]
  rw [hFS]
  unfold Spec.Kopis.innerProduct
  simp only [Aeneas.SRRange.forIn'_eq_forIn'_range', Aeneas.SRRange.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, bind_pure]
  refine forIn'_inv' (List.range' 0 ℓ) _ _
    (fun s (a : Spec.Kopis.Polynomial m) => a = ∑ j ∈ Finset.range s, g j)
    ℓ (by simp) ?hInit ?hStep
  case hInit => show Spec.Kopis.Polynomial.zero m = _; rw [Finset.range_zero, Finset.sum_empty]; rfl
  case hStep =>
    intro k hk b hb a ha ha_eq
    have ha_val : a = k := by rw [ha_eq]; simp [List.getElem_range']
    subst ha_val
    have ha_lt : a < ℓ := by simpa using hk
    have hterm : v[a]'ha_lt * w[a]'ha_lt = g a := by simp only [hg, ha_lt, dif_pos]
    refine ⟨_, rfl, ?_⟩
    rw [Finset.sum_range_succ, ← hb]
    exact congrArg (b + ·) hterm

/-- `toPolyN 10 re` is exactly the physical polynomial reduced mod `2¹⁰`. -/
theorem toPolyN10_eq_coerce (re : RingElem) :
    toPolyN 10 re = (toRingElem re).coerce (2 ^ 10) := by
  apply Vector.ext; intro k hk
  simp only [toPolyN, Spec.Kopis.Polynomial.coerce, toRingElem, Vector.getElem_map,
    Vector.getElem_ofFn, ZMod.val_natCast]
  have hlt : (re.val[k]'(by have := re.property; grind)).val < 2 ^ 16 := by
    have h := (re.val[k]'(by have := re.property; grind)).hBounds; simpa [UScalarTy.numBits] using h
  rw [Nat.mod_eq_of_lt hlt]

/-- Casting `a mod 2¹³` into `ZMod 2¹⁰` is the same as casting `a` directly. -/
theorem natCast_mod13_10 (a : ℕ) : ((a % 2 ^ 13 : ℕ) : ZMod (2 ^ 10)) = (a : ZMod (2 ^ 10)) := by
  conv_rhs => rw [← Nat.mod_add_div a (2 ^ 13)]
  rw [show (2:ℕ) ^ 13 = 2 ^ 10 * 2 ^ 3 from by norm_num]
  push_cast; ring_nf

/-- The two column-vector abstractions agree after reduction to `R10`. -/
theorem toRingElem13_coerce10 (re : RingElem) :
    (toRingElem13 re).coerce (2 ^ 10) = (toRingElem re).coerce (2 ^ 10) := by
  apply Vector.ext; intro k hk
  simp only [Spec.Kopis.Polynomial.coerce, toRingElem13, toRingElem, Vector.getElem_map,
    Vector.getElem_ofFn, ZMod.val_natCast]
  have hlt : (re.val[k]'(by have := re.property; grind)).val < 2 ^ 16 := by
    have h := (re.val[k]'(by have := re.property; grind)).hBounds; simpa [UScalarTy.numBits] using h
  rw [Nat.mod_eq_of_lt hlt, natCast_mod13_10]

/-- **Inner-product correspondence at `R10`.**  The Rust `vprime = Σᵢ b[i]·s'[i]` (physical
`2¹⁶`), reduced to `R10`, equals the spec's `innerProduct b (s'.coerce R10)`. -/
theorem innerProduct_coerce_bridge {L : Usize}
    (pkvec vecs : arithmetic.matrix_arith.Matrix L 1#usize) (vprime1 : RingElem)
    (hip : toRingElem vprime1 = ∑ ii ∈ Finset.range L.val,
        toRingElem ((pkvec.val[ii]!).val[0]!) * toRingElem ((vecs.val[ii]!).val[0]!)) :
    (toRingElem vprime1).coerce (2 ^ 10)
      = Spec.Kopis.innerProduct (toVecN 10 pkvec) ((toVector13 vecs).coerce (2 ^ 10)) := by
  rw [hip, coerce_sum10, innerProduct_get, ← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro i _
  rw [coerce_mul10]
  congr 1
  · -- (toVecN 10 pkvec)[i] = coerce (toRingElem pkvec[i][0]) 2^10
    simp only [toVecN, Vector.getElem_ofFn]
    rw [toPolyN10_eq_coerce]
  · -- ((toVector13 vecs).coerce 2^10)[i] = coerce (toRingElem vecs[i][0]) 2^10
    simp only [Spec.Kopis.PolyVector.coerce, Vector.getElem_map, toVector13, Vector.getElem_ofFn]
    rw [toRingElem13_coerce10]

/-- `innerProduct` is stable under a length cast on both arguments. -/
theorem innerProduct_cast {m ℓ ℓ' : ℕ} (h : ℓ = ℓ') (v w : Spec.Kopis.PolyVector m ℓ) :
    Spec.Kopis.innerProduct (h ▸ v) (h ▸ w) = Spec.Kopis.innerProduct v w := by cases h; rfl

/-- `PolyVector.coerce` commutes with a length cast. -/
theorem coerceVec_cast {m ℓ ℓ' : ℕ} (h : ℓ = ℓ') (v : Spec.Kopis.PolyVector m ℓ) (m' : ℕ) :
    (h ▸ v).coerce m' = h ▸ (v.coerce m') := by cases h; rfl

end Kopis.Properties
