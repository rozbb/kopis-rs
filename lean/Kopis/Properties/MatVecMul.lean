import Kopis.Properties.GenMatrix
open Aeneas Aeneas.Std Result RustKopisSerial
open scoped BigOperators
namespace Kopis.Properties

set_option maxHeartbeats 1000000

/-- Spec-side evaluation of `matVecMul`'s nested `Id.run` loop: row `i₀` of `A·v`. -/
theorem matVecMul_get {m ℓ : ℕ} (A : Spec.Kopis.PolyMatrix m ℓ) (v : Spec.Kopis.PolyVector m ℓ)
    (i₀ : ℕ) (hi₀ : i₀ < ℓ) :
    (Spec.Kopis.matVecMul A v)[i₀]'hi₀
      = ∑ j : Fin ℓ, A ⟨i₀, hi₀⟩ j * v[j.val]'j.isLt := by
  set g : ℕ → Spec.Kopis.Polynomial m :=
    fun j => if hj : j < ℓ then A ⟨i₀, hi₀⟩ ⟨j, hj⟩ * v[j]'hj else 0 with hg
  have hFS : (∑ j : Fin ℓ, A ⟨i₀, hi₀⟩ j * v[j.val]'j.isLt) = ∑ j ∈ Finset.range ℓ, g j := by
    rw [← Fin.sum_univ_eq_sum_range g ℓ]
    exact Finset.sum_congr rfl fun j _ => by simp only [hg, j.isLt, dif_pos]
  rw [hFS]
  unfold Spec.Kopis.matVecMul
  simp only [Aeneas.SRRange.forIn'_eq_forIn'_range', Aeneas.SRRange.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, bind_pure]
  rw [show (∑ j ∈ Finset.range ℓ, g j)
      = if i₀ < ℓ then (∑ j ∈ Finset.range ℓ, g j) else (0 : Spec.Kopis.Polynomial m)
      from (if_pos hi₀).symm]
  refine forIn'_inv' (List.range' 0 ℓ) _ _
    (fun s (w : Spec.Kopis.PolyVector m ℓ) => w[i₀]'hi₀
      = if i₀ < s then (∑ j ∈ Finset.range ℓ, g j) else (0 : Spec.Kopis.Polynomial m))
    ℓ (by simp) ?hInit ?hStep
  case hInit =>
    show (Spec.Kopis.PolyVector.zero m ℓ)[i₀]'hi₀ = _
    rw [Spec.Kopis.PolyVector.zero, Vector.getElem_replicate, if_neg (Nat.not_lt_zero i₀)]
    rfl
  case hStep =>
    intro k hk b hb a ha ha_eq
    have ha_val : a = k := by rw [ha_eq]; simp [List.getElem_range']
    subst ha_val
    have ha_lt : a < ℓ := by simpa using hk
    refine ⟨_, rfl, ?_⟩
    have bridge : (if i₀ < a + 1 then (∑ j ∈ Finset.range ℓ, g j) else (0 : Spec.Kopis.Polynomial m))
        = if a = i₀ then (b[i₀]'hi₀ + ∑ j ∈ Finset.range ℓ, g j) else b[i₀]'hi₀ := by
      rw [hb]
      by_cases hai2 : a = i₀
      · rw [if_pos hai2, if_neg (by omega : ¬ i₀ < a), if_pos (by omega : i₀ < a + 1)]; abel
      · rw [if_neg hai2]
        by_cases hlt : i₀ < a
        · rw [if_pos (by omega : i₀ < a + 1), if_pos hlt]
        · rw [if_neg (by omega : ¬ i₀ < a + 1), if_neg hlt]
    rw [bridge]
    refine forIn'_inv' (List.range' 0 ℓ) b _
      (fun s (w : Spec.Kopis.PolyVector m ℓ) => w[i₀]'hi₀
        = if a = i₀ then (b[i₀]'hi₀ + ∑ j ∈ Finset.range s, g j) else b[i₀]'hi₀)
      ℓ (by simp) ?hInitIn ?hStepIn
    case hInitIn =>
      rw [Finset.range_zero, Finset.sum_empty]; split_ifs <;> abel
    case hStepIn =>
      intro t ht w hw jj hjj hjj_eq
      have hjj_val : jj = t := by rw [hjj_eq]; simp [List.getElem_range']
      subst hjj_val
      have hjj_lt : jj < ℓ := by simpa using ht
      refine ⟨_, rfl, ?_⟩
      simp only [Spec.Kopis.PolyVector.set, Vector.getElem_set]
      by_cases hai : a = i₀
      · subst hai
        rw [if_pos rfl, if_pos rfl, hw, if_pos rfl, Finset.sum_range_succ]
        have hterm : A ⟨a, ha_lt⟩ ⟨jj, hjj_lt⟩ * v[jj]'hjj_lt = g jj := by
          simp only [hg, hjj_lt, dif_pos]
        rw [hterm]; abel
      · rw [if_neg hai, if_neg hai, hw, if_neg hai]

end Kopis.Properties
