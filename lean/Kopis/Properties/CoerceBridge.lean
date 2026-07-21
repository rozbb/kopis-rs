import Kopis.Properties.RingArith
import Kopis.Properties.Serialize
open Aeneas Aeneas.Std Result kopis
open scoped BigOperators
namespace Kopis.Properties

open arithmetic.ring_arith (RingElem)

/-! # Modulus bridge: `Polynomial.coerce` (2¹⁶ → 2¹³) is a ring homomorphism.

The Rust pipeline computes `mul_transpose` at the physical modulus `2¹⁶`, but the spec
`matVecMul` works at `2¹³`.  These lemmas let us push the `2¹⁶ → 2¹³` reduction through
`+` and `*`, matching the two computations. -/

/-- The coefficient reduction `x ↦ x.val` is exactly the ring hom `ZMod.castHom`. -/
theorem castHom_eq_val (x : ZMod (2 ^ 16)) :
    (ZMod.castHom (show (2 ^ 13 : ℕ) ∣ 2 ^ 16 by norm_num) (ZMod (2 ^ 13))) x
      = (x.val : ZMod (2 ^ 13)) := by
  rw [ZMod.castHom_apply, ZMod.natCast_val]

theorem coerce_getElem (a : Spec.Kopis.Polynomial (2 ^ 16)) (i : ℕ) (hi : i < 256) :
    (Spec.Kopis.Polynomial.coerce a (2 ^ 13))[i]'hi = ((a[i]'hi).val : ZMod (2 ^ 13)) := by
  simp only [Spec.Kopis.Polynomial.coerce, Vector.getElem_map]

theorem coerce_getElem! (a : Spec.Kopis.Polynomial (2 ^ 16)) (i : ℕ) (hi : i < 256) :
    (Spec.Kopis.Polynomial.coerce a (2 ^ 13))[i]! = ((a[i]!).val : ZMod (2 ^ 13)) := by
  rw [getElem!_pos _ i hi, getElem!_pos a i hi, coerce_getElem]

/-- `coerce` distributes over polynomial addition. -/
theorem coerce_add (a b : Spec.Kopis.Polynomial (2 ^ 16)) :
    Spec.Kopis.Polynomial.coerce (a + b) (2 ^ 13)
      = Spec.Kopis.Polynomial.coerce a (2 ^ 13) + Spec.Kopis.Polynomial.coerce b (2 ^ 13) := by
  apply Vector.ext; intro p hp
  rw [coerce_getElem _ p hp,
    show (Spec.Kopis.Polynomial.coerce a (2 ^ 13) + Spec.Kopis.Polynomial.coerce b (2 ^ 13))
        = Spec.Kopis.Polynomial.add (Spec.Kopis.Polynomial.coerce a (2 ^ 13))
            (Spec.Kopis.Polynomial.coerce b (2 ^ 13)) from rfl,
    show (a + b) = Spec.Kopis.Polynomial.add a b from rfl]
  simp only [Spec.Kopis.Polynomial.add, Vector.getElem_zipWith]
  rw [← castHom_eq_val, map_add, castHom_eq_val, castHom_eq_val, coerce_getElem a p hp,
    coerce_getElem b p hp]

set_option maxHeartbeats 1000000 in
/-- `coerce` distributes over the negacyclic polynomial product. -/
theorem coerce_mul (a b : Spec.Kopis.Polynomial (2 ^ 16)) :
    Spec.Kopis.Polynomial.coerce (a * b) (2 ^ 13)
      = Spec.Kopis.Polynomial.coerce a (2 ^ 13) * Spec.Kopis.Polynomial.coerce b (2 ^ 13) := by
  apply Vector.ext; intro p hp
  set f := ZMod.castHom (show (2 ^ 13 : ℕ) ∣ 2 ^ 16 by norm_num) (ZMod (2 ^ 13)) with hf
  rw [coerce_getElem _ p hp, show (a * b) = Spec.Kopis.Polynomial.mul a b from rfl, mul_get a b p hp,
    show (Spec.Kopis.Polynomial.coerce a (2 ^ 13) * Spec.Kopis.Polynomial.coerce b (2 ^ 13))
        = Spec.Kopis.Polynomial.mul (Spec.Kopis.Polynomial.coerce a (2 ^ 13))
            (Spec.Kopis.Polynomial.coerce b (2 ^ 13)) from rfl,
    mul_get _ _ p hp, ← castHom_eq_val]
  simp only [convCoeff, map_sum]
  refine Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl fun j hj => ?_
  have hi256 : i < 256 := Finset.mem_range.mp hi
  have hj256 : j < 256 := Finset.mem_range.mp hj
  have hfa : f (a[i]!) = (Spec.Kopis.Polynomial.coerce a (2 ^ 13))[i]! := by
    rw [castHom_eq_val, coerce_getElem! a i hi256]
  have hfb : f (b[j]!) = (Spec.Kopis.Polynomial.coerce b (2 ^ 13))[j]! := by
    rw [castHom_eq_val, coerce_getElem! b j hj256]
  simp only [convContrib]
  by_cases hij : (i + j) % 256 = p
  · rw [if_pos hij, if_pos hij]
    by_cases hlt : i + j < 256
    · rw [if_pos hlt, if_pos hlt, map_mul, hfa, hfb]
    · rw [if_neg hlt, if_neg hlt, map_neg, map_mul, hfa, hfb]
  · rw [if_neg hij, if_neg hij, map_zero]

/-- `coerce` sends `0` to `0`. -/
theorem coerce_zero : Spec.Kopis.Polynomial.coerce (0 : Spec.Kopis.Polynomial (2 ^ 16)) (2 ^ 13)
    = (0 : Spec.Kopis.Polynomial (2 ^ 13)) := by
  apply Vector.ext; intro p hp
  rw [coerce_getElem _ p hp]
  show (((Spec.Kopis.Polynomial.zero (2 ^ 16))[p]'hp).val : ZMod (2 ^ 13))
      = (Spec.Kopis.Polynomial.zero (2 ^ 13))[p]'hp
  simp only [Spec.Kopis.Polynomial.zero, Vector.getElem_replicate, ZMod.val_zero, Nat.cast_zero]

/-- `coerce` as a bundled additive homomorphism `Polynomial 2¹⁶ →+ Polynomial 2¹³`. -/
def coerceHom : Spec.Kopis.Polynomial (2 ^ 16) →+ Spec.Kopis.Polynomial (2 ^ 13) where
  toFun r := Spec.Kopis.Polynomial.coerce r (2 ^ 13)
  map_zero' := coerce_zero
  map_add' := coerce_add

/-- `coerce` distributes over a finite sum. -/
theorem coerce_sum {ι : Type*} (s : Finset ι) (f : ι → Spec.Kopis.Polynomial (2 ^ 16)) :
    Spec.Kopis.Polynomial.coerce (∑ i ∈ s, f i) (2 ^ 13)
      = ∑ i ∈ s, Spec.Kopis.Polynomial.coerce (f i) (2 ^ 13) :=
  map_sum coerceHom f s

/-- The physical-`2¹⁶` interpretation coerced to `2¹³` is the direct `2¹³` interpretation. -/
theorem coerce_toRingElem (re : RingElem) :
    Spec.Kopis.Polynomial.coerce (toRingElem re) (2 ^ 13) = toRingElem13 re := by
  apply Vector.ext; intro p hp
  rw [coerce_getElem _ p hp]
  simp only [toRingElem, toRingElem13, Vector.getElem_ofFn]
  have hlt : (re.val[p]'(by have := re.property; grind)).val < 2 ^ 16 := by
    have h := (re.val[p]'(by have := re.property; grind)).hBounds
    simpa only [UScalarTy.numBits] using h
  rw [ZMod.val_natCast, Nat.mod_eq_of_lt hlt]

end Kopis.Properties
