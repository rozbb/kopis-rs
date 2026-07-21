import Kopis.Properties.SerializeTop
open Aeneas Aeneas.Std Result
namespace Kopis.Properties

/-- **RoundToR10 per-coefficient bridge.**  The 16-bit physical rounding
`(((c+4) mod 2¹⁶) >>> 3) mod 2¹⁰` depends only on the low 13 bits of `c`, matching the
spec's 13-bit rounding `(((c mod 2¹³)+4) mod 2¹³) >>> 3`.  This is why the Rust pipeline
(which keeps `u16` coefficients) computes the same `R10` value as the spec (which reduces
to `R13` after `matVecMul`). -/
theorem round10_bridge (c : ℕ) :
    (((c + 4) % 2 ^ 16) >>> 3) % 2 ^ 10 = (((c % 2 ^ 13) + 4) % 2 ^ 13) >>> 3 := by
  simp only [Nat.shiftRight_eq_div_pow]
  have lhs : (((c + 4) % 2 ^ 16) / 2 ^ 3) % 2 ^ 10 = (c + 4) / 2 ^ 3 % 2 ^ 10 := by
    rw [show (2 : ℕ) ^ 16 = 2 ^ 3 * 2 ^ 13 from by norm_num, Nat.mod_mul_right_div_self,
      Nat.mod_mod_of_dvd _ (by norm_num : (2 : ℕ) ^ 10 ∣ 2 ^ 13)]
  have rhs : (((c % 2 ^ 13) + 4) % 2 ^ 13) / 2 ^ 3 = ((c % 2 ^ 13) + 4) / 2 ^ 3 % 2 ^ 10 := by
    rw [show (2 : ℕ) ^ 13 = 2 ^ 3 * 2 ^ 10 from by norm_num, Nat.mod_mul_right_div_self]
  rw [lhs, rhs]
  conv_lhs => rw [show c + 4 = (c % 2 ^ 13 + 4) + 2 ^ 3 * (c / 2 ^ 13 * 2 ^ 10) from by omega]
  rw [Nat.add_mul_div_left _ _ (by norm_num : 0 < 2 ^ 3), Nat.add_mul_mod_self_right]

/-- **Spec-side `RoundToR10` coefficient.**  Coefficient `k` of row `i` of `RoundToR10 ℓ vv`
is `(((vv[i][k].val + 4) mod 2¹³) >>> 3)`. -/
theorem roundR10_coeff {ℓ : ℕ} (vv : Spec.Kopis.PolyVector (2 ^ 13) ℓ) (i : ℕ) (hi : i < ℓ)
    (k : ℕ) (hk : k < 256) :
    (((Spec.Kopis.RoundToR10 ℓ vv)[i]'hi)[k]'hk).val
      = ((((vv[i]'hi)[k]'hk).val + 4) % 2 ^ 13) >>> 3 := by
  have hlt : ((((vv[i]'hi)[k]'hk).val + 4) % 2 ^ 13) >>> 3 < 2 ^ 10 := by
    have h1 : (((vv[i]'hi)[k]'hk).val + 4) % 2 ^ 13 < 2 ^ 13 := Nat.mod_lt _ (by positivity)
    rw [Nat.shiftRight_eq_div_pow]; omega
  -- coefficient `k` of the pointwise-add `vv[i] + const 4`
  have h4 : (4 : ZMod (2 ^ 13)).val = 4 := by decide
  have hcoeff : ((vv[i]'hi + Spec.Kopis.Polynomial.const (2 ^ 13) 4)[k]'hk).val
      = (((vv[i]'hi)[k]'hk).val + 4) % 2 ^ 13 := by
    show (((Spec.Kopis.Polynomial.add (vv[i]'hi) (Spec.Kopis.Polynomial.const (2 ^ 13) 4))[k]'hk).val
        : ℕ) = (((vv[i]'hi)[k]'hk).val + 4) % 2 ^ 13
    simp only [Spec.Kopis.Polynomial.add, Vector.getElem_zipWith, Spec.Kopis.Polynomial.const,
      Vector.getElem_replicate, ZMod.val_add, h4]
  -- coefficient `i` of the pointwise vector-add
  have hveci : ((vv + Vector.replicate ℓ (Spec.Kopis.Polynomial.const (2 ^ 13) 4))[i]'hi)
      = vv[i]'hi + Spec.Kopis.Polynomial.const (2 ^ 13) 4 := by
    show (Vector.ofFn fun j => vv[j] + (Vector.replicate ℓ (Spec.Kopis.Polynomial.const (2 ^ 13) 4))[j])[i]'hi
        = vv[i]'hi + Spec.Kopis.Polynomial.const (2 ^ 13) 4
    simp [Vector.getElem_ofFn, Vector.getElem_replicate]
  unfold Spec.Kopis.RoundToR10
  simp only [Spec.Kopis.PolyVector.coerce, Spec.Kopis.PolyVector.shiftRight, Vector.getElem_map,
    Spec.Kopis.Polynomial.coerce, Spec.Kopis.Polynomial.shiftRight, hveci,
    ZMod.val_natCast, hcoeff]
  rw [Nat.mod_eq_of_lt (lt_trans hlt (by norm_num : (2 : ℕ) ^ 10 < 2 ^ 13)), Nat.mod_eq_of_lt hlt]

end Kopis.Properties
