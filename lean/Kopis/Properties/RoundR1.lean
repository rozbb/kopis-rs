import Kopis.Properties.RoundTop
open Aeneas Aeneas.Std Result kopis
namespace Kopis.Properties

open arithmetic.ring_arith (RingElem)

set_option maxHeartbeats 1000000

/-- **Spec-side `RoundToR1` coefficient.**  Coefficient `k` of `RoundToR1 t r` is
`(((r[k].val + h₂) mod 2¹⁰) >>> 9)` where `h₂ = 2⁸ - 2⁹⁻ᵗ + 4` (valid for `1 ≤ t ≤ 10`). -/
theorem roundR1_coeff (t : ℕ) (ht : 1 ≤ t ∧ t ≤ 10) (r : Spec.Kopis.Polynomial (2 ^ 10))
    (k : ℕ) (hk : k < 256) :
    (((Spec.Kopis.RoundToR1 t r)[k]'hk).val)
      = (((r[k]'hk).val + (2 ^ 8 - 2 ^ (9 - t) + 4)) % 2 ^ 10) >>> 9 := by
  haveI : NeZero ((2:ℕ)^1) := ⟨by positivity⟩
  set C : ℕ := 2 ^ 8 - 2 ^ (9 - t) + 4 with hC
  have hClt : C < 2 ^ 10 := by
    rw [hC]
    have h1 : 2 ^ (9 - t) ≤ 2 ^ 8 := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h4 : (1:ℕ) ≤ 2 ^ (9 - t) := Nat.one_le_two_pow
    have h2 : (2:ℕ) ^ 8 = 256 := by norm_num
    have h3 : (2:ℕ) ^ 10 = 1024 := by norm_num
    omega
  have hlt : (((r[k]'hk).val + C) % 2 ^ 10) >>> 9 < 2 ^ 1 := by
    have h1 : ((r[k]'hk).val + C) % 2 ^ 10 < 2 ^ 10 := Nat.mod_lt _ (by positivity)
    rw [Nat.shiftRight_eq_div_pow, Nat.div_lt_iff_lt_mul (by positivity),
      show 2 ^ 1 * 2 ^ 9 = 2 ^ 10 from by norm_num]
    exact h1
  have hcv : (((C : ℕ) : ZMod (2 ^ 10))).val = C := by
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt hClt]
  have hcoeff : ((r + Spec.Kopis.Polynomial.const (2 ^ 10) ((C : ℕ) : ZMod (2 ^ 10)))[k]'hk).val
      = ((r[k]'hk).val + C) % 2 ^ 10 := by
    show (((Spec.Kopis.Polynomial.add r (Spec.Kopis.Polynomial.const (2 ^ 10) ((C:ℕ):ZMod (2^10))))[k]'hk).val : ℕ) = _
    simp only [Spec.Kopis.Polynomial.add, Vector.getElem_zipWith, Spec.Kopis.Polynomial.const,
      Vector.getElem_replicate, ZMod.val_add, hcv]
  unfold Spec.Kopis.RoundToR1
  simp only [Spec.Kopis.Polynomial.coerce, Spec.Kopis.Polynomial.shiftRight, Vector.getElem_map,
    hcoeff, ZMod.val_natCast, ← hC]
  rw [Nat.mod_eq_of_lt (lt_of_lt_of_le hlt (by norm_num : (2:ℕ)^1 ≤ 2^10)), Nat.mod_eq_of_lt hlt]

/-- **`RoundToR1` physical bridge.**  The 16-bit physical rounding
`((((c+C) mod 2¹⁶) >>> 9) mod 2¹)` depends only on the low 10 bits of `c`. -/
theorem roundR1_bridge (c C : ℕ) :
    (((c + C) % 2 ^ 16) >>> 9) % 2 ^ 1 = (((c % 2 ^ 10) + C) % 2 ^ 10) >>> 9 := by
  simp only [Nat.shiftRight_eq_div_pow]
  have hpos : 0 < (2:ℕ) ^ 9 := by positivity
  have lhs : (((c + C) % 2 ^ 16) / 2 ^ 9) % 2 ^ 1 = (c + C) / 2 ^ 9 % 2 ^ 1 := by
    rw [show (2:ℕ) ^ 16 = 2 ^ 9 * 2 ^ 7 from by norm_num, Nat.mod_mul_right_div_self,
      Nat.mod_mod_of_dvd _ (by norm_num : (2:ℕ) ^ 1 ∣ 2 ^ 7)]
  have rhs : (((c % 2 ^ 10) + C) % 2 ^ 10) / 2 ^ 9 = ((c % 2 ^ 10) + C) / 2 ^ 9 % 2 ^ 1 := by
    generalize c % 2 ^ 10 = y
    rw [show (2:ℕ) ^ 10 = 2 ^ 9 * 2 ^ 1 from by norm_num, Nat.mod_mul_right_div_self]
  rw [lhs, rhs]
  have hsplit : c + C = (c % 2 ^ 10 + C) + 2 ^ 9 * (2 ^ 1 * (c / 2 ^ 10)) := by
    have h := Nat.div_add_mod c (2 ^ 10)
    have h2 : 2 ^ 9 * (2 ^ 1 * (c / 2 ^ 10)) = 2 ^ 10 * (c / 2 ^ 10) := by rw [← mul_assoc]; norm_num
    omega
  rw [hsplit, Nat.add_mul_div_left _ _ hpos, Nat.add_mul_mod_self_left]

/-- **Per-`RingElem` `RoundToR1` correspondence (Rust side).**  The Rust pipeline
`mp₂ = (mp + h₂) >>> 9` on a `u16` ring element computes the spec's
`RoundToR1 t ((coerce to R10) mp)`. -/
theorem roundR1_ring_bridge (mp mp1 mp2 : RingElem) (t : ℕ) (ht : 1 ≤ t ∧ t ≤ 10)
    (hw : toRingElem mp1 = Spec.Kopis.Polynomial.add (toRingElem mp)
      (Spec.Kopis.Polynomial.const (2 ^ 16) (((2 ^ 8 - 2 ^ (9 - t) + 4 : ℕ) : ZMod (2 ^ 16)))))
    (hs : toRingElem mp2 = Spec.Kopis.Polynomial.shiftRight (toRingElem mp1) 9) :
    toPolyN 1 mp2 = Spec.Kopis.RoundToR1 t ((toRingElem mp).coerce (2 ^ 10)) := by
  haveI : NeZero ((2:ℕ)^1) := ⟨by positivity⟩
  set C : ℕ := 2 ^ 8 - 2 ^ (9 - t) + 4 with hC
  have hClt16 : C < 2 ^ 16 := by
    rw [hC]; have h1 : 2 ^ (9 - t) ≤ 2 ^ 8 := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h4 : (1:ℕ) ≤ 2 ^ (9 - t) := Nat.one_le_two_pow
    have : (2:ℕ) ^ 8 = 256 := by norm_num
    have : (2:ℕ) ^ 16 = 65536 := by norm_num
    omega
  apply Vector.ext; intro k hk
  apply ZMod.val_injective
  rw [roundR1_coeff t ht ((toRingElem mp).coerce (2 ^ 10)) k hk,
    ← getElem!_pos (toPolyN 1 mp2) k hk, toPolyN_val 1 mp2 k hk,
    ← toRingElem_coeff_val mp2 k hk, getElem!_pos _ k hk, hs]
  simp only [Spec.Kopis.Polynomial.shiftRight, Vector.getElem_map, ZMod.val_natCast]
  have hCv : ((C : ℕ) : ZMod (2 ^ 16)).val = C := by rw [ZMod.val_natCast, Nat.mod_eq_of_lt hClt16]
  have hp1 : (((toRingElem mp1)[k]'hk).val) = (((toRingElem mp)[k]'hk).val + C) % 2 ^ 16 := by
    rw [hw]
    show (((Spec.Kopis.Polynomial.add (toRingElem mp)
        (Spec.Kopis.Polynomial.const (2 ^ 16) ((C:ℕ):ZMod (2^16))))[k]'hk).val : ℕ) = _
    simp only [Spec.Kopis.Polynomial.add, Vector.getElem_zipWith, Spec.Kopis.Polynomial.const,
      Vector.getElem_replicate, ZMod.val_add, hCv]
  rw [hp1]
  set d := ((toRingElem mp)[k]'hk).val with hd
  have hcoe : (((toRingElem mp).coerce (2 ^ 10))[k]'hk).val = d % 2 ^ 10 := by
    simp only [Spec.Kopis.Polynomial.coerce, Vector.getElem_map, ZMod.val_natCast, hd]
  rw [hcoe, Nat.mod_mod_of_dvd _ (show (2:ℕ) ^ 1 ∣ 2 ^ 16 from by norm_num), roundR1_bridge d C]

end Kopis.Properties
