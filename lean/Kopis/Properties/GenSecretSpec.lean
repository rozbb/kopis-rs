import Kopis.Properties.GenSecretLoops
open Aeneas Aeneas.Std Result RustKopis
open scoped BigOperators
open Spec (𝔹 bytesToBits)
open scoped Spec.Notations
open Spec.TurboSHAKE (turboSHAKE256)
open Spec.Kopis (DOMSEP_GENSEC)
namespace Kopis.Properties

set_option maxHeartbeats 2000000
set_option maxRecDepth 4000

/-- Index bound for the CBD bit stream (local copy of the spec's private `gensec_idx_lt`). -/
theorem gensec_idx_lt' {μ k j : Nat} (hk : k < 256) (hj : j < μ / 2) :
    μ * k + μ / 2 + j < 8 * (32 * μ) := by
  calc μ * k + μ / 2 + j < μ * k + μ := by omega
    _ = μ * (k + 1) := by rw [Nat.mul_succ]
    _ ≤ μ * 256 := Nat.mul_le_mul_left μ (by omega)
    _ = 8 * (32 * μ) := by ring

/-- The spec's centered-binomial coefficient `k` for row `i`. -/
noncomputable def gsCoeff (μ : ℕ) (seed : 𝔹 32) (k : ℕ) (hk : k < 256) (i : ℕ) : ZMod (2 ^ 13) :=
  ((∑ j : Fin (μ / 2),
      ((bytesToBits (turboSHAKE256 (seed ‖ #v[(i : Byte)]) DOMSEP_GENSEC (32 * μ)))[μ * k + j.val]'(by
        have := gensec_idx_lt' hk j.isLt; omega)).toNat : ℕ) : ZMod (2 ^ 13))
    - ((∑ j : Fin (μ / 2),
      ((bytesToBits (turboSHAKE256 (seed ‖ #v[(i : Byte)]) DOMSEP_GENSEC (32 * μ)))[μ * k + μ / 2 + j.val]'(
        gensec_idx_lt' hk j.isLt)).toNat : ℕ) : ZMod (2 ^ 13))

/-- `(v.set i x)[j] = if j = i then x else v[j]` (both bounded). -/
theorem vget_set {n : ℕ} {α : Type*} (v : Vector α n) (i : ℕ) (x : α) (hi : i < n)
    (j : ℕ) (hj : j < n) : (v.set i x)[j]'hj = if j = i then x else v[j]'hj := by
  rw [Vector.getElem_set]
  split_ifs with h1 h2 h2 <;> first | rfl | omega

/-- Evaluation of the spec `GenSecret` at row `i₀`, coefficient `k`. -/
theorem GenSecret_get (ℓ μ : ℕ) (seed : 𝔹 32) (i₀ : Fin ℓ) (k : ℕ) (hk : k < 256) :
    ((Spec.Kopis.GenSecret ℓ μ seed)[i₀.val]'(i₀.isLt))[k]'(hk)
      = gsCoeff μ seed k hk i₀.val := by
  unfold Spec.Kopis.GenSecret
  simp only [Aeneas.SRRange.forIn'_eq_forIn'_range', Aeneas.SRRange.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, bind_pure]
  rw [show gsCoeff μ seed k hk i₀.val
      = (if i₀.val < ℓ then gsCoeff μ seed k hk i₀.val
        else (0 : ZMod (2 ^ 13))) from (if_pos i₀.isLt).symm]
  refine forIn'_inv' (List.range' 0 ℓ) _ _
    (fun s (S : Spec.Kopis.PolyVector (2 ^ 13) ℓ) =>
      (S[i₀.val]'i₀.isLt)[k]'hk
        = if i₀.val < s then gsCoeff μ seed k hk i₀.val else (0 : ZMod (2 ^ 13)))
    ℓ (by simp) ?hInit ?hStep
  case hInit =>
    simp only [Nat.not_lt_zero, if_false]
    simp [Spec.Kopis.PolyVector.zero, Spec.Kopis.Polynomial.zero]
  case hStep =>
    intro cnt hcnt b hb x hx hx_eq
    have hx_val : x = cnt := by rw [hx_eq]; simp [List.getElem_range']
    subst hx_val
    refine ⟨_, rfl, ?_⟩
    have hxℓ : x < ℓ := by simpa using hcnt
    simp only [Spec.Kopis.PolyVector.set]
    by_cases hix : i₀.val = x
    · -- the row we care about is written this iteration
      have HR : ∀ (R : Spec.Kopis.Polynomial (2 ^ 13)),
          ((Vector.set b x R)[i₀.val]'i₀.isLt)[k]'hk = R[k]'hk := fun R => by
        rw [Vector.getElem_set, if_pos hix.symm]
      rw [HR, if_pos (show i₀.val < x + 1 by omega),
        show gsCoeff μ seed k hk i₀.val
          = if k < 256 then gsCoeff μ seed k hk i₀.val else (0 : ZMod (2 ^ 13)) from (if_pos hk).symm]
      refine forIn'_inv' (List.range' 0 256) _ _
        (fun cnt2 (r : Spec.Kopis.Polynomial (2 ^ 13)) =>
          r[k]'hk = if k < cnt2 then gsCoeff μ seed k hk i₀.val else (0 : ZMod (2 ^ 13)))
        256 (by simp) ?inInit ?inStep
      case inInit => simp [Spec.Kopis.Polynomial.zero]
      case inStep =>
        intro c2 hc2 r hr c hc hc_eq
        have hc_val : c = c2 := by rw [hc_eq]; simp [List.getElem_range']
        subst hc_val
        refine ⟨_, rfl, ?_⟩
        rw [Vector.getElem_set]
        by_cases hkc : k = c
        · rw [if_pos hkc.symm, if_pos (by omega : k < c + 1)]
          subst hkc; rw [hix]; rfl
        · rw [if_neg (fun h => hkc h.symm), hr]
          by_cases hkc2 : k < c
          · rw [if_pos hkc2, if_pos (by omega)]
          · rw [if_neg hkc2, if_neg (by omega)]
    · -- a different row: value carried from `hb`
      have HR : ∀ (R : Spec.Kopis.Polynomial (2 ^ 13)),
          ((Vector.set b x R)[i₀.val]'i₀.isLt)[k]'hk = (b[i₀.val]'i₀.isLt)[k]'hk := fun R => by
        rw [Vector.getElem_set, if_neg (fun h => hix h.symm)]
      rw [HR, hb]
      by_cases hlt : i₀.val < x
      · rw [if_pos hlt, if_pos (by omega)]
      · rw [if_neg hlt, if_neg (by omega)]

/-- **Row correspondence.**  If the read buffer's bytes are the row's TurboSHAKE256
stream and each Rust coefficient is `cbdVal`, then the decoded ring element equals the
spec's `GenSecret` row. -/
theorem cbd_row_eq_genSecret (L : Usize) (μ : ℕ) (seed : 𝔹 32) (buf1 : Slice U8)
    (re1 : RingElem) (i : ℕ) (hi : i < L.val) (hbuf : buf1.length = 32 * μ)
    (hbridge : sliceToBytes buf1 (32 * μ) hbuf
        = turboSHAKE256 (seed ‖ #v[(i : Byte)]) DOMSEP_GENSEC (32 * μ))
    (hcbd : ∀ k, k < 256 → ((re1.val[k]!).val : ZMod (2 ^ 13)) = cbdVal buf1 μ (μ / 2) k) :
    toRingElem13 re1 = (Spec.Kopis.GenSecret L.val μ seed)[i]'hi := by
  apply Vector.ext
  intro k hk
  have hbuf' : buf1.val.length = 32 * μ := by rw [← Slice.length]; exact hbuf
  have hkb : k < re1.val.length := by have := re1.property; grind
  rw [toRingElem13, Vector.getElem_ofFn, ← getElem!_pos re1.val k hkb, hcbd k hk,
    cbdVal_eq_specCoeff buf1 μ k hbuf' hk, hbridge,
    GenSecret_get L.val μ seed ⟨i, hi⟩ k hk, gsCoeff]

end Kopis.Properties
