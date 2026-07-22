import Kopis.Properties.ProdBridge
import Kopis.Properties.RoundBridge
import Kopis.Properties.MatrixArith
import Kopis.Properties.RoundTop
open Aeneas Aeneas.Std Result RustKopis
open scoped BigOperators
namespace Kopis.Properties

open arithmetic.matrix_arith (Matrix)
open arithmetic.ring_arith (RingElem)

set_option maxHeartbeats 1000000
set_option maxRecDepth 4000

/-- **Product correspondence (no transpose).**  The Rust product output (physical `2¹⁶`),
reduced to `2¹³`, is exactly the spec `matVecMul Aˢᵖᵉᶜ sˢᵖᵉᶜ` using the plain matrix
product `A·s'` (no transpose). -/
theorem prod_matVecMul_bridge_nt {L : Usize} (mat_a : Matrix L L) (vec_s : Matrix L 1#usize)
    (prod : Matrix L 1#usize) (i : ℕ) (hi : i < L.val)
    (hp : ∀ i₀ : ℕ, i₀ < L.val → toRingElem ((prod.val[i₀]!).val[0]!)
        = ∑ ii ∈ Finset.range L.val,
            toRingElem ((mat_a.val[i₀]!).val[ii]!) * toRingElem ((vec_s.val[ii]!).val[0]!)) :
    Spec.Kopis.Polynomial.coerce (toRingElem ((prod.val[i]!).val[0]!)) (2 ^ 13)
      = (Spec.Kopis.matVecMul (toMatrix13 mat_a) (toVector13 vec_s))[i]'hi := by
  rw [matVecMul_get, hp i hi, coerce_sum,
    ← Fin.sum_univ_eq_sum_range
      (fun ii => Spec.Kopis.Polynomial.coerce (toRingElem ((mat_a.val[i]!).val[ii]!)
        * toRingElem ((vec_s.val[ii]!).val[0]!)) (2 ^ 13)) L.val]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [coerce_mul, coerce_toRingElem, coerce_toRingElem]
  simp only [toMatrix13, Matrix.of_apply, toVector13, Vector.getElem_ofFn]

/-- **Full RoundToR10 correspondence (Rust side, no transpose).** -/
theorem prod2_roundR10_bridge_nt {L : Usize} (mat_a : Matrix L L) (vec_s : Matrix L 1#usize)
    (prod prod1 prod2 : Matrix L 1#usize) (i : ℕ) (hi : i < L.val)
    (hmt : ∀ i₀ : ℕ, i₀ < L.val → toRingElem ((prod.val[i₀]!).val[0]!)
        = ∑ ii ∈ Finset.range L.val,
            toRingElem ((mat_a.val[i₀]!).val[ii]!) * toRingElem ((vec_s.val[ii]!).val[0]!))
    (hw : toRingElem ((prod1.val[i]!).val[0]!)
        = addC 4#u16 (toRingElem ((prod.val[i]!).val[0]!)))
    (hs : toRingElem ((prod2.val[i]!).val[0]!)
        = Spec.Kopis.Polynomial.shiftRight (toRingElem ((prod1.val[i]!).val[0]!)) 3) :
    toPolyN 10 ((prod2.val[i]!).val[0]!)
      = (Spec.Kopis.RoundToR10 L.val
          (Spec.Kopis.matVecMul (toMatrix13 mat_a) (toVector13 vec_s)))[i]'hi := by
  haveI : NeZero ((2 : ℕ) ^ 10) := ⟨by positivity⟩
  apply Vector.ext
  intro k hk
  apply ZMod.val_injective
  set vv := Spec.Kopis.matVecMul (toMatrix13 mat_a) (toVector13 vec_s) with hvv
  rw [roundR10_coeff vv i hi k hk,
    ← getElem!_pos (toPolyN 10 ((prod2.val[i]!).val[0]!)) k hk, toPolyN_val 10 _ k hk,
    ← toRingElem_coeff_val _ k hk, getElem!_pos _ k hk, hs]
  simp only [Spec.Kopis.Polynomial.shiftRight, Vector.getElem_map, ZMod.val_natCast]
  -- prod1 coeff = prod coeff + 4 (mod 2^16)
  have h4 : (4 : ZMod (2 ^ 16)).val = 4 := by decide
  have hp1 : ((toRingElem ((prod1.val[i]!).val[0]!))[k]'hk).val
      = (((toRingElem ((prod.val[i]!).val[0]!))[k]'hk).val + 4) % 2 ^ 16 := by
    rw [hw]
    show (((Spec.Kopis.Polynomial.add (toRingElem ((prod.val[i]!).val[0]!))
        (Spec.Kopis.Polynomial.const (2 ^ 16) ((4#u16).val : ZMod (2 ^ 16))))[k]'hk).val : ℕ) = _
    have hc4 : ((4#u16).val : ZMod (2 ^ 16)) = 4 := by decide
    simp only [Spec.Kopis.Polynomial.add, Vector.getElem_zipWith, Spec.Kopis.Polynomial.const,
      Vector.getElem_replicate, hc4, ZMod.val_add, h4]
  rw [hp1]
  set c := ((toRingElem ((prod.val[i]!).val[0]!))[k]'hk).val with hc
  rw [Nat.mod_mod_of_dvd _ (show (2 : ℕ) ^ 10 ∣ 2 ^ 16 from by norm_num), round10_bridge c]
  -- vv[i][k].val = c % 2^13
  have hvvc : ((vv[i]'hi)[k]'hk).val = c % 2 ^ 13 := by
    have hb := prod_matVecMul_bridge_nt mat_a vec_s prod i hi hmt
    rw [hvv, ← hb, coerce_getElem _ k hk, ZMod.val_natCast, ← hc]
  rw [hvvc]

end Kopis.Properties
