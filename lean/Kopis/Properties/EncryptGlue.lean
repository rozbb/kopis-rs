import Kopis.Properties.InnerProduct
open Aeneas Aeneas.Std Result kopis
namespace Kopis.Properties

open arithmetic.ring_arith (RingElem)

set_option maxHeartbeats 1000000

/-- `coerce` (2¹⁶ → 2¹⁰) distributes over polynomial subtraction. -/
theorem coerce_sub10 (a b : Spec.Kopis.Polynomial (2 ^ 16)) :
    Spec.Kopis.Polynomial.coerce (Spec.Kopis.Polynomial.sub a b) (2 ^ 10)
      = Spec.Kopis.Polynomial.sub (Spec.Kopis.Polynomial.coerce a (2 ^ 10))
          (Spec.Kopis.Polynomial.coerce b (2 ^ 10)) := by
  apply Vector.ext; intro p hp
  simp only [Spec.Kopis.Polynomial.sub, Vector.getElem_zipWith, coerce_getElem10 _ p hp]
  rw [← castHom_eq_val10, map_sub, castHom_eq_val10, castHom_eq_val10]

/-- **Message-shift bridge.**  The Rust `shift_left(m, 9)` at physical `2¹⁶`, reduced to
`R10`, equals the spec's `(m.coerce R10).shiftLeft 9` (the message bit lands at position 9). -/
theorem msg_shift_bridge (a1 : RingElem) :
    (Spec.Kopis.Polynomial.shiftLeft (toRingElem a1) 9).coerce (2 ^ 10)
      = ((toPolyN 1 a1).coerce (2 ^ 10)).shiftLeft 9 := by
  apply Vector.ext; intro k hk
  simp only [Spec.Kopis.Polynomial.coerce, Spec.Kopis.Polynomial.shiftLeft, toPolyN, toRingElem,
    Vector.getElem_map, Vector.getElem_ofFn, ZMod.val_natCast]
  have hlt : (a1.val[k]'(by have := a1.property; grind)).val < 2 ^ 16 := by
    have h := (a1.val[k]'(by have := a1.property; grind)).hBounds; simpa [UScalarTy.numBits] using h
  rw [Nat.mod_eq_of_lt hlt]
  apply (ZMod.natCast_eq_natCast_iff _ _ _).mpr
  show ((a1.val[k]'_).val <<< 9 % 2 ^ 16) % 2 ^ 10
      = ((a1.val[k]'_).val % 2 ^ 1 % 2 ^ 10) <<< 9 % 2 ^ 10
  rw [Nat.mod_mod_of_dvd _ (by norm_num : (2:ℕ)^10 ∣ 2^16),
    Nat.mod_eq_of_lt (lt_of_lt_of_le (Nat.mod_lt _ (by norm_num)) (by norm_num : (2:ℕ)^1 ≤ 2^10))]
  simp only [Nat.shiftLeft_eq, show (2:ℕ)^1 = 2 from rfl]
  rw [show (2:ℕ)^10 = 2 * 2^9 from by norm_num, Nat.mul_mod_mul_right, Nat.mul_mod_mul_right,
    Nat.mod_mod_of_dvd _ (dvd_refl 2)]

end Kopis.Properties
