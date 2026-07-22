import Kopis.Properties.MatVecMul
import Kopis.Properties.CoerceBridge
import Kopis.Properties.MulTranspose
import Kopis.Properties.GenSecretTop
open Aeneas Aeneas.Std Result RustKopis
open scoped BigOperators
namespace Kopis.Properties

open arithmetic.matrix_arith (Matrix)

set_option maxHeartbeats 1000000

/-- **Product correspondence.**  The Rust `mul_transpose` output (physical `2¹⁶`),
reduced to `2¹³`, is exactly the spec `matVecMul (transpose Aˢᵖᵉᶜ) sˢᵖᵉᶜ`. -/
theorem prod_matVecMul_bridge {L : Usize} (mat_a : Matrix L L) (vec_s : Matrix L 1#usize)
    (prod : Matrix L 1#usize) (i : ℕ) (hi : i < L.val)
    (hp : ∀ i₀ : ℕ, i₀ < L.val → toRingElem ((prod.val[i₀]!).val[0]!)
        = ∑ ii ∈ Finset.range L.val,
            toRingElem ((mat_a.val[ii]!).val[i₀]!) * toRingElem ((vec_s.val[ii]!).val[0]!)) :
    Spec.Kopis.Polynomial.coerce (toRingElem ((prod.val[i]!).val[0]!)) (2 ^ 13)
      = (Spec.Kopis.matVecMul (Matrix.transpose (toMatrix13 mat_a)) (toVector13 vec_s))[i]'hi := by
  rw [matVecMul_get, hp i hi, coerce_sum,
    ← Fin.sum_univ_eq_sum_range
      (fun ii => Spec.Kopis.Polynomial.coerce (toRingElem ((mat_a.val[ii]!).val[i]!)
        * toRingElem ((vec_s.val[ii]!).val[0]!)) (2 ^ 13)) L.val]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [coerce_mul, coerce_toRingElem, coerce_toRingElem, Matrix.transpose_apply]
  simp only [toMatrix13, Matrix.of_apply, toVector13, Vector.getElem_ofFn]

end Kopis.Properties
