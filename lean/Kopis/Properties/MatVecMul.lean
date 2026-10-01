import Kopis.Properties.GenMatrix
open Aeneas Aeneas.Std Result RustKopisSerial
open scoped BigOperators
namespace Kopis.Properties

set_option maxHeartbeats 1000000

/-- Row `i₀` of `A * v`. -/
theorem matVecMul_get {m ℓ : ℕ} (A : Spec.Kopis.PolyMatrix m ℓ) (v : Spec.Kopis.PolyVector m ℓ)
    (i₀ : ℕ) (hi₀ : i₀ < ℓ) :
    ((A * v))[i₀]'hi₀
      = ∑ j : Fin ℓ, A ⟨i₀, hi₀⟩ j * v[j.val]'j.isLt := by
  simp only [HMul.hMul, Vector.getElem_ofFn]; rfl

end Kopis.Properties
