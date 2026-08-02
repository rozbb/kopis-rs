import Kopis.Properties.RoundTop
open Aeneas Aeneas.Std Result RustKopisSerial
namespace Kopis.Properties

open arithmetic.ring_arith (RingElem)

set_option maxHeartbeats 1000000

/-- **Spec-side `RoundToRt` coefficient.**  Coefficient `k` of `RoundToRt t r` is
`(((r[k].val + 4) mod 2¹⁰) >>> (10 - t))` (valid for `t ≤ 10`). -/
theorem roundRt_coeff (t : ℕ) (ht : t ≤ 10) (r : Spec.Kopis.Polynomial (2 ^ 10))
    (k : ℕ) (hk : k < 256) :
    (((Spec.Kopis.RoundToRt t r)[k]'hk).val)
      = (((r[k]'hk).val + 4) % 2 ^ 10) >>> (10 - t) := by
  haveI : NeZero ((2:ℕ)^t) := ⟨by positivity⟩
  have hlt : (((r[k]'hk).val + 4) % 2 ^ 10) >>> (10 - t) < 2 ^ t := by
    have h1 : ((r[k]'hk).val + 4) % 2 ^ 10 < 2 ^ 10 := Nat.mod_lt _ (by positivity)
    rw [Nat.shiftRight_eq_div_pow, Nat.div_lt_iff_lt_mul (by positivity),
      show 2 ^ t * 2 ^ (10 - t) = 2 ^ 10 from by rw [← pow_add]; congr 1; omega]
    exact h1
  have h4 : (4 : ZMod (2 ^ 10)).val = 4 := by decide
  have hcoeff : ((r + Spec.Kopis.Polynomial.const (2 ^ 10) 4)[k]'hk).val
      = ((r[k]'hk).val + 4) % 2 ^ 10 := by
    show (((Spec.Kopis.Polynomial.add r (Spec.Kopis.Polynomial.const (2 ^ 10) 4))[k]'hk).val : ℕ) = _
    simp only [Spec.Kopis.Polynomial.add, Vector.getElem_zipWith, Spec.Kopis.Polynomial.const,
      Vector.getElem_replicate, ZMod.val_add, h4]
  unfold Spec.Kopis.RoundToRt
  simp only [Spec.Kopis.Polynomial.coerce, Spec.Kopis.Polynomial.shiftRight, Vector.getElem_map,
    hcoeff, ZMod.val_natCast]
  rw [Nat.mod_eq_of_lt (lt_of_lt_of_le hlt (Nat.pow_le_pow_right (by norm_num) ht)),
    Nat.mod_eq_of_lt hlt]

/-- **`RoundToRt` physical bridge.**  The 16-bit physical rounding
`((((c+4) mod 2¹⁶) >>> (10-t)) mod 2ᵗ)` depends only on the low 10 bits of `c`, matching
the spec's `R10` rounding `(((c mod 2¹⁰)+4) mod 2¹⁰) >>> (10-t)`. -/
theorem roundRt_bridge (c t : ℕ) (ht : t ≤ 10) :
    (((c + 4) % 2 ^ 16) >>> (10 - t)) % 2 ^ t = (((c % 2 ^ 10) + 4) % 2 ^ 10) >>> (10 - t) := by
  simp only [Nat.shiftRight_eq_div_pow]
  have hAB : (2:ℕ) ^ (10 - t) * 2 ^ t = 2 ^ 10 := by rw [← pow_add]; congr 1; omega
  have hpos : 0 < (2:ℕ) ^ (10 - t) := by positivity
  have lhs : (((c + 4) % 2 ^ 16) / 2 ^ (10 - t)) % 2 ^ t = (c + 4) / 2 ^ (10 - t) % 2 ^ t := by
    rw [show (2:ℕ) ^ 16 = 2 ^ (10 - t) * 2 ^ (6 + t) from by rw [← pow_add]; congr 1; omega,
      Nat.mod_mul_right_div_self,
      Nat.mod_mod_of_dvd _ (by rw [show 6 + t = t + 6 from by omega, pow_add]; exact Dvd.intro _ rfl)]
  have rhs : (((c % 2 ^ 10) + 4) % 2 ^ 10) / 2 ^ (10 - t) = ((c % 2 ^ 10) + 4) / 2 ^ (10 - t) % 2 ^ t := by
    generalize c % 2 ^ 10 = y
    rw [show (2:ℕ) ^ 10 = 2 ^ (10 - t) * 2 ^ t from hAB.symm, Nat.mod_mul_right_div_self]
  rw [lhs, rhs]
  have hsplit : c + 4 = (c % 2 ^ 10 + 4) + 2 ^ (10 - t) * (2 ^ t * (c / 2 ^ 10)) := by
    have h := Nat.div_add_mod c (2 ^ 10)
    have h2 : 2 ^ (10 - t) * (2 ^ t * (c / 2 ^ 10)) = 2 ^ 10 * (c / 2 ^ 10) := by rw [← mul_assoc, hAB]
    omega
  rw [hsplit, Nat.add_mul_div_left _ _ hpos, Nat.add_mul_mod_self_left]

/-- **Per-`RingElem` `RoundToRt` correspondence (Rust side).**  The Rust pipeline
`c₂ = (c + 4) >>> (10 - t)` on a `u16` ring element computes the spec's
`RoundToRt t ((coerce to R10) c)`. -/
theorem roundRt_ring_bridge (c c1 c2 : RingElem) (t : ℕ) (ht : t ≤ 10)
    (hw : toRingElem c1
      = Spec.Kopis.Polynomial.add (toRingElem c) (Spec.Kopis.Polynomial.const (2 ^ 16) 4))
    (hs : toRingElem c2 = Spec.Kopis.Polynomial.shiftRight (toRingElem c1) (10 - t)) :
    toPolyN t c2 = Spec.Kopis.RoundToRt t ((toRingElem c).coerce (2 ^ 10)) := by
  haveI : NeZero ((2:ℕ)^t) := ⟨by positivity⟩
  apply Vector.ext
  intro k hk
  apply ZMod.val_injective
  rw [roundRt_coeff t ht ((toRingElem c).coerce (2 ^ 10)) k hk,
    ← getElem!_pos (toPolyN t c2) k hk, toPolyN_val t c2 k hk,
    ← toRingElem_coeff_val c2 k hk, getElem!_pos _ k hk, hs]
  simp only [Spec.Kopis.Polynomial.shiftRight, Vector.getElem_map, ZMod.val_natCast]
  -- c1 coeff = c coeff + 4 (mod 2^16)
  have h4 : (4 : ZMod (2 ^ 16)).val = 4 := by decide
  have hp1 : (((toRingElem c1)[k]'hk).val) = (((toRingElem c)[k]'hk).val + 4) % 2 ^ 16 := by
    rw [hw]
    show (((Spec.Kopis.Polynomial.add (toRingElem c)
        (Spec.Kopis.Polynomial.const (2 ^ 16) 4))[k]'hk).val : ℕ) = _
    simp only [Spec.Kopis.Polynomial.add, Vector.getElem_zipWith, Spec.Kopis.Polynomial.const,
      Vector.getElem_replicate, ZMod.val_add, h4]
  rw [hp1]
  set d := ((toRingElem c)[k]'hk).val with hd
  -- RHS coerce coeff: (coerce c 2^10)[k].val = d % 2^10
  have hcoe : (((toRingElem c).coerce (2 ^ 10))[k]'hk).val = d % 2 ^ 10 := by
    simp only [Spec.Kopis.Polynomial.coerce, Vector.getElem_map, ZMod.val_natCast, hd]
  rw [hcoe]
  -- LHS: ((((d+4)%2^16) >>> (10-t)) % 2^16) % 2^t ; the inner %2^16 is absorbable
  rw [Nat.mod_mod_of_dvd _ (show (2:ℕ) ^ t ∣ 2 ^ 16 from by
    rw [show (16:ℕ) = t + (16 - t) from by omega, pow_add]; exact Dvd.intro _ rfl),
    roundRt_bridge d t ht]

end Kopis.Properties
