/-
  # Kopis/Avx2/NttValue.lean — what one AVX2 butterfly does to the residues (plan phase F4).

  `Kopis/Avx2/NttGrowth.lean` proves `ct_butterfly` keeps its lanes inside an `i16`.  This file
  says what it *computes*: modulo `q`, the pair `(lo + ψ·hi, lo − ψ·hi)` with `ψ` the plain
  twiddle — the stored Montgomery entry times `2⁻¹⁶`, since `mont_mul` divides by the radix on
  the way through.

  That is exactly the shape `NttAlgebra.State_ct` asks of a Cooley-Tukey layer, so a level of the
  transform refines the CRT invariant by one step.  The bound hypotheses are the same ones
  `ct_butterfly_bnd` needs, and for the same reason: they are what makes the wrapping `vpaddw`
  and `vpsubw` exact, so that the integer identity survives the cast into `ZMod q`.
-/
import Kopis.Avx2.NttZeta

open Aeneas Aeneas.Std Result
open RustKopisAvx2
open RustKopisAvx2.backend.avx2.intrinsics

namespace Kopis.Avx2

set_option maxHeartbeats 1000000

/-- Lane `i` of a vector, as a residue. -/
noncomputable def laneZ (q : ℕ) (v : Vec256) (i : ℕ) : ZMod q := (((lane16 v i).toInt : ℤ) : ZMod q)

/-- **One Cooley-Tukey butterfly, as residues.**  `mont_mul` contributes the `2⁻¹⁶`, which is why
the twiddle that appears is `z · R⁻¹` and not `z`. -/
theorem ct_butterfly_val (lo hi z zq qv : Vec256) (q : ℕ) (Zb A T : ℤ) (Rinv : ZMod q)
    (hq0 : 0 < (q : ℤ)) (hqlt : (q : ℤ) ≤ 2 ^ 15)
    (hR : ((2 ^ 16 : ℤ) : ZMod q) * Rinv = 1)
    (hQ : ∀ i < 16, (lane16 qv i).toInt = (q : ℤ))
    (hzq : ∀ i < 16, (2 ^ 16 : ℤ) ∣ ((lane16 zq i).toInt * (q : ℤ) - (lane16 z i).toInt))
    (hlo : VecBnd lo A) (hhi : VecBnd hi A) (hz : VecBnd z Zb)
    (hA0 : 0 ≤ A)
    (hAZ : A * Zb < 2 ^ 15 * (q : ℤ)) (hT : A * Zb + 2 ^ 15 * (q : ℤ) ≤ 2 ^ 16 * T)
    (hfit : A + T ≤ 2 ^ 15 - 1) :
    backend.avx2.ntt.ct_butterfly lo hi z zq qv
      ⦃ (r : Vec256 × Vec256) => ∀ i < 16,
          laneZ q r.1 i = laneZ q lo i + (laneZ q z i * Rinv) * laneZ q hi i ∧
          laneZ q r.2 i = laneZ q lo i - (laneZ q z i * Rinv) * laneZ q hi i ⦄ := by
  unfold backend.avx2.ntt.ct_butterfly
  have hbnd : ∀ i < 16, |(lane16 hi i).toInt * (lane16 z i).toInt| < 2 ^ 15 * (q : ℤ) := by
    intro i hi'
    rw [abs_mul]
    calc |(lane16 hi i).toInt| * |(lane16 z i).toInt| ≤ A * Zb :=
          mul_le_mul (hhi i hi') (hz i hi') (abs_nonneg _) hA0
      _ < 2 ^ 15 * (q : ℤ) := hAZ
  apply WP.spec_bind (mont_mul_lane_spec hi z zq qv (q : ℤ) hQ hq0 hqlt hzq hbnd)
  intro t ht
  have hTb : VecBnd t T := by
    intro i hi'
    have hsharp := (ht i hi').2.2.2
    have hle : |(lane16 hi i).toInt| * |(lane16 z i).toInt| ≤ A * Zb :=
      mul_le_mul (hhi i hi') (hz i hi') (abs_nonneg _) hA0
    have : (2:ℤ) ^ 16 * |(lane16 t i).toInt| ≤ 2 ^ 16 * T := by linarith
    exact le_of_mul_le_mul_left this (by norm_num)
  obtain ⟨hi1, hhi1, hhi1b⟩ := sub_epi16_model lo t
  rw [hhi1, bind_tc_ok]
  obtain ⟨lo1, hlo1, hlo1b⟩ := add_epi16_model lo t
  rw [hlo1, bind_tc_ok]
  simp only [WP.spec_ok]
  intro i hi'
  -- the Montgomery output, as a residue
  have htz : laneZ q t i = laneZ q z i * Rinv * laneZ q hi i := by
    obtain ⟨c, hc⟩ := (ht i hi').1
    have hcast : (((lane16 t i).toInt * 2 ^ 16 - (lane16 hi i).toInt * (lane16 z i).toInt : ℤ)
        : ZMod q) = 0 := by
      rw [(ZMod.intCast_zmod_eq_zero_iff_dvd _ q)]
      exact ⟨c, hc⟩
    push_cast at hcast
    have hmul : laneZ q t i * ((2 ^ 16 : ℤ) : ZMod q) = laneZ q hi i * laneZ q z i := by
      unfold laneZ
      push_cast
      linear_combination hcast
    calc laneZ q t i = laneZ q t i * (((2 ^ 16 : ℤ) : ZMod q) * Rinv) := by rw [hR]; ring
      _ = (laneZ q t i * ((2 ^ 16 : ℤ) : ZMod q)) * Rinv := by ring
      _ = (laneZ q hi i * laneZ q z i) * Rinv := by rw [hmul]
      _ = laneZ q z i * Rinv * laneZ q hi i := by ring
  -- the two wrapping additions are exact, so the integer identity casts
  have hex1 : (lane16 lo1 i).toInt = (lane16 lo i).toInt + (lane16 t i).toInt := by
    rw [add_lane_toInt lo t lo1 hlo1b i hi']
    exact bmod16_eq_self (by have := hlo i hi'; have := hTb i hi'; rw [abs_le] at *; omega)
      (by have := hlo i hi'; have := hTb i hi'; rw [abs_le] at *; omega)
  have hex2 : (lane16 hi1 i).toInt = (lane16 lo i).toInt - (lane16 t i).toInt := by
    rw [sub_lane_toInt lo t hi1 hhi1b i hi']
    exact bmod16_eq_self (by have := hlo i hi'; have := hTb i hi'; rw [abs_le] at *; omega)
      (by have := hlo i hi'; have := hTb i hi'; rw [abs_le] at *; omega)
  refine ⟨?_, ?_⟩
  · show laneZ q lo1 i = _
    unfold laneZ
    rw [hex1]
    push_cast
    rw [show (((lane16 t i).toInt : ℤ) : ZMod q) = laneZ q t i from rfl, htz]
    unfold laneZ
    ring
  · show laneZ q hi1 i = _
    unfold laneZ
    rw [hex2]
    push_cast
    rw [show (((lane16 t i).toInt : ℤ) : ZMod q) = laneZ q t i from rfl, htz]
    unfold laneZ
    ring

/-! ## The Gentleman-Sande butterfly

`(lo, hi) ↦ (lo + hi, ψ·(lo − hi))`, with ψ again the plain twiddle.  The tables feeding `z` on
the inverse side already carry the negation `State_gs` expects, so the ψ that appears here is
`−ζ(2nb−1−b)` and no sign has to be inserted by hand. -/

theorem gs_butterfly_bnd (lo hi z zq qv : Vec256) (Q Zb A T : ℤ)
    (hQ : ∀ i < 16, (lane16 qv i).toInt = Q) (hQpos : 0 < Q) (hQlt : Q ≤ 2 ^ 15)
    (hzq : ∀ i < 16, (2 ^ 16 : ℤ) ∣ ((lane16 zq i).toInt * Q - (lane16 z i).toInt))
    (hlo : VecBnd lo A) (hhi : VecBnd hi A) (hz : VecBnd z Zb)
    (hA0 : 0 ≤ A) (_hZ0 : 0 ≤ Zb)
    (hsum : 2 * A ≤ 2 ^ 15 - 1)
    (hAZ : 2 * A * Zb < 2 ^ 15 * Q) (hT : 2 * A * Zb + 2 ^ 15 * Q ≤ 2 ^ 16 * T) :
    backend.avx2.ntt.gs_butterfly lo hi z zq qv
      ⦃ (r : Vec256 × Vec256) => VecBnd r.1 (2 * A) ∧ VecBnd r.2 T ⦄ := by
  unfold backend.avx2.ntt.gs_butterfly
  obtain ⟨d, hd, hdb⟩ := sub_epi16_model lo hi
  rw [hd, bind_tc_ok]
  obtain ⟨lo1, hlo1, hlo1b⟩ := add_epi16_model lo hi
  rw [hlo1, bind_tc_ok]
  have hdbnd : VecBnd d (2 * A) := by
    intro i hi'
    rw [sub_lane_toInt lo hi d hdb i hi',
      bmod16_eq_self (by have := hlo i hi'; have := hhi i hi'; rw [abs_le] at *; omega)
        (by have := hlo i hi'; have := hhi i hi'; rw [abs_le] at *; omega)]
    have := hlo i hi'; have := hhi i hi'
    rw [abs_le] at *
    omega
  have hbnd : ∀ i < 16, |(lane16 d i).toInt * (lane16 z i).toInt| < 2 ^ 15 * Q := by
    intro i hi'
    rw [abs_mul]
    calc |(lane16 d i).toInt| * |(lane16 z i).toInt| ≤ 2 * A * Zb :=
          mul_le_mul (hdbnd i hi') (hz i hi') (abs_nonneg _) (by omega)
      _ < 2 ^ 15 * Q := hAZ
  apply WP.spec_bind (mont_mul_lane_spec d z zq qv Q hQ hQpos hQlt hzq hbnd)
  intro c hc
  simp only [WP.spec_ok]
  refine ⟨?_, ?_⟩
  · intro i hi'
    rw [add_lane_toInt lo hi lo1 hlo1b i hi',
      bmod16_eq_self (by have := hlo i hi'; have := hhi i hi'; rw [abs_le] at *; omega)
        (by have := hlo i hi'; have := hhi i hi'; rw [abs_le] at *; omega)]
    have := hlo i hi'; have := hhi i hi'
    rw [abs_le] at *
    omega
  · intro i hi'
    have hsharp := (hc i hi').2.2.2
    have hle : |(lane16 d i).toInt| * |(lane16 z i).toInt| ≤ 2 * A * Zb :=
      mul_le_mul (hdbnd i hi') (hz i hi') (abs_nonneg _) (by omega)
    have : (2:ℤ) ^ 16 * |(lane16 c i).toInt| ≤ 2 ^ 16 * T := by linarith
    exact le_of_mul_le_mul_left this (by norm_num)

theorem gs_butterfly_val (lo hi z zq qv : Vec256) (q : ℕ) (Zb A _T : ℤ) (Rinv : ZMod q)
    (hq0 : 0 < (q : ℤ)) (hqlt : (q : ℤ) ≤ 2 ^ 15)
    (hR : ((2 ^ 16 : ℤ) : ZMod q) * Rinv = 1)
    (hQ : ∀ i < 16, (lane16 qv i).toInt = (q : ℤ))
    (hzq : ∀ i < 16, (2 ^ 16 : ℤ) ∣ ((lane16 zq i).toInt * (q : ℤ) - (lane16 z i).toInt))
    (hlo : VecBnd lo A) (hhi : VecBnd hi A) (hz : VecBnd z Zb)
    (hA0 : 0 ≤ A) (_hZ0 : 0 ≤ Zb)
    (hsum : 2 * A ≤ 2 ^ 15 - 1)
    (hAZ : 2 * A * Zb < 2 ^ 15 * (q : ℤ)) :
    backend.avx2.ntt.gs_butterfly lo hi z zq qv
      ⦃ (r : Vec256 × Vec256) => ∀ i < 16,
          laneZ q r.1 i = laneZ q lo i + laneZ q hi i ∧
          laneZ q r.2 i = (laneZ q z i * Rinv) * (laneZ q lo i - laneZ q hi i) ⦄ := by
  unfold backend.avx2.ntt.gs_butterfly
  obtain ⟨d, hd, hdb⟩ := sub_epi16_model lo hi
  rw [hd, bind_tc_ok]
  obtain ⟨lo1, hlo1, hlo1b⟩ := add_epi16_model lo hi
  rw [hlo1, bind_tc_ok]
  have hdex : ∀ i < 16, (lane16 d i).toInt = (lane16 lo i).toInt - (lane16 hi i).toInt := by
    intro i hi'
    rw [sub_lane_toInt lo hi d hdb i hi',
      bmod16_eq_self (by have := hlo i hi'; have := hhi i hi'; rw [abs_le] at *; omega)
        (by have := hlo i hi'; have := hhi i hi'; rw [abs_le] at *; omega)]
  have hdbnd : VecBnd d (2 * A) := by
    intro i hi'
    rw [hdex i hi']
    have := hlo i hi'; have := hhi i hi'
    rw [abs_le] at *
    omega
  have hbnd : ∀ i < 16, |(lane16 d i).toInt * (lane16 z i).toInt| < 2 ^ 15 * (q : ℤ) := by
    intro i hi'
    rw [abs_mul]
    calc |(lane16 d i).toInt| * |(lane16 z i).toInt| ≤ 2 * A * Zb :=
          mul_le_mul (hdbnd i hi') (hz i hi') (abs_nonneg _) (by omega)
      _ < 2 ^ 15 * (q : ℤ) := hAZ
  apply WP.spec_bind (mont_mul_lane_spec d z zq qv (q : ℤ) hQ hq0 hqlt hzq hbnd)
  intro c hc
  simp only [WP.spec_ok]
  intro i hi'
  refine ⟨?_, ?_⟩
  · show laneZ q lo1 i = _
    unfold laneZ
    rw [add_lane_toInt lo hi lo1 hlo1b i hi',
      bmod16_eq_self (by have := hlo i hi'; have := hhi i hi'; rw [abs_le] at *; omega)
        (by have := hlo i hi'; have := hhi i hi'; rw [abs_le] at *; omega)]
    push_cast
    rfl
  · show laneZ q c i = _
    obtain ⟨w, hw⟩ := (hc i hi').1
    have hcast : (((lane16 c i).toInt * 2 ^ 16 - (lane16 d i).toInt * (lane16 z i).toInt : ℤ)
        : ZMod q) = 0 := by
      rw [(ZMod.intCast_zmod_eq_zero_iff_dvd _ q)]
      exact ⟨w, hw⟩
    push_cast at hcast
    have hmul : laneZ q c i * ((2 ^ 16 : ℤ) : ZMod q)
        = (laneZ q lo i - laneZ q hi i) * laneZ q z i := by
      unfold laneZ
      rw [show (((lane16 lo i).toInt : ℤ) : ZMod q) - (((lane16 hi i).toInt : ℤ) : ZMod q)
        = (((lane16 d i).toInt : ℤ) : ZMod q) from by rw [hdex i hi']; push_cast; ring]
      push_cast
      linear_combination hcast
    calc laneZ q c i = laneZ q c i * (((2 ^ 16 : ℤ) : ZMod q) * Rinv) := by rw [hR]; ring
      _ = (laneZ q c i * ((2 ^ 16 : ℤ) : ZMod q)) * Rinv := by ring
      _ = ((laneZ q lo i - laneZ q hi i) * laneZ q z i) * Rinv := by rw [hmul]
      _ = (laneZ q z i * Rinv) * (laneZ q lo i - laneZ q hi i) := by ring

end Kopis.Avx2
