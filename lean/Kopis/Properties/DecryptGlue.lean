import Kopis.Properties.InnerProduct
open Aeneas Aeneas.Std Result kopis_kem
namespace Kopis.Properties

open arithmetic.ring_arith (RingElem)

set_option maxHeartbeats 1000000

/-- **Shift-left / coerce bridge.**  The Rust `shift_left(c, 10-n)` at physical `2¹⁶`,
reduced to `R10`, equals the spec's `(c.coerce R10).shiftLeft (10-n)` (the low `n` bits of
`c` land in the top; used for `cm₁₀` in decryption).  Generalises `msg_shift_bridge`. -/
theorem shiftLeft_coerce_bridge (c : RingElem) (n : ℕ) (hn : n ≤ 10) :
    (Spec.Kopis.Polynomial.shiftLeft (toRingElem c) (10 - n)).coerce (2 ^ 10)
      = ((toPolyN n c).coerce (2 ^ 10)).shiftLeft (10 - n) := by
  apply Vector.ext; intro k hk
  simp only [Spec.Kopis.Polynomial.coerce, Spec.Kopis.Polynomial.shiftLeft, toPolyN, toRingElem,
    Vector.getElem_map, Vector.getElem_ofFn, ZMod.val_natCast]
  have hlt : (c.val[k]'(by have := c.property; grind)).val < 2 ^ 16 := by
    have h := (c.val[k]'(by have := c.property; grind)).hBounds; simpa [UScalarTy.numBits] using h
  rw [Nat.mod_eq_of_lt hlt]
  apply (ZMod.natCast_eq_natCast_iff _ _ _).mpr
  set x := (c.val[k]'(by have := c.property; grind)).val with hx
  show (x <<< (10 - n) % 2 ^ 16) % 2 ^ 10 = (x % 2 ^ n % 2 ^ 10) <<< (10 - n) % 2 ^ 10
  rw [Nat.mod_mod_of_dvd _ (by norm_num : (2:ℕ) ^ 10 ∣ 2 ^ 16),
    Nat.mod_eq_of_lt (lt_of_lt_of_le (Nat.mod_lt _ (by positivity))
      (Nat.pow_le_pow_right (by norm_num) hn))]
  simp only [Nat.shiftLeft_eq]
  rw [show (2:ℕ) ^ 10 = 2 ^ (10 - n) * 2 ^ n from by rw [← pow_add]; congr 1; omega,
    Nat.mul_comm x (2 ^ (10 - n)), Nat.mul_comm (x % 2 ^ n) (2 ^ (10 - n)),
    Nat.mul_mod_mul_left, Nat.mul_mod_mul_left, Nat.mod_mod_of_dvd _ (dvd_refl (2 ^ n))]

end Kopis.Properties
