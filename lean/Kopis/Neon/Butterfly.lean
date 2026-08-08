/-
  # Kopis/Neon/Butterfly.lean — one butterfly, value and bound together.

  `Kopis/Neon/NttGrowth.lean` gives the two butterflies' *magnitude* behaviour, which is what the
  reduction schedule is checked against.  This file gives the other half: what they compute.

  The statements are deliberately existential in the Montgomery product `t`.  A Cooley-Tukey
  butterfly is

      (lo, hi) ↦ (lo + t, lo − t)   where  t ≡ hi·ψ·2⁻¹⁶  (mod q)

  and the transform's algebra only ever uses `t` through that congruence and through `|t| ≤ Bt`.
  Naming it, rather than writing `mont_mul`'s value out, is what keeps the walk's induction
  readable — and it is the same shape `Kopis/Properties/NttWalk.lean` uses on the portable side,
  so the two are comparable at the point where they have to be.

  Both lemmas subsume their `NttGrowth.lean` counterparts: the bound is one of the conjuncts.
  The `hfit` hypothesis is where the schedule enters — the additions must not wrap an `i16`, and
  that is exactly what a Barrett pass every three levels buys.
-/
import Kopis.Neon.Tables

open Aeneas Aeneas.Std Result
open RustKopisNeon
open RustKopisNeon.backend.neon.intrinsics

namespace Kopis.Neon

set_option maxHeartbeats 1000000

/-- **The Cooley-Tukey butterfly.**  `(lo, hi) ↦ (lo + t, lo − t)` with `t` the Montgomery
product, exactly — no wrapping, given the fit hypothesis. -/
theorem ct_butterfly_spec (lo hi z zq qv : Vec128) (Q Zb B Bt : ℤ)
    (hQ : ∀ i < 8, (lane16 qv i).toInt = Q) (hQpos : 0 < Q) (hQlt : Q ≤ 2 ^ 14)
    (hz : ∀ i < 8, |(lane16 z i).toInt| ≤ Zb) (hZb : Zb ≤ 2 ^ 14)
    (hzq : ∀ i < 8, (2 ^ 16 : ℤ) ∣ ((lane16 zq i).toInt * Q - (lane16 z i).toInt))
    (hlo : VecBnd lo B) (hhi : VecBnd hi B) (hB0 : 0 ≤ B)
    (hBZ : B * Zb < 2 ^ 15 * Q) (hBt : B * Zb + 2 ^ 15 * Q ≤ 2 ^ 16 * Bt)
    (hfit : B + Bt ≤ 32767) :
    backend.neon.ntt.ct_butterfly lo hi z zq qv
      ⦃ (r : Vec128 × Vec128) =>
          VecBnd r.1 (B + Bt) ∧ VecBnd r.2 (B + Bt) ∧
          ∀ i < 8, ∃ t : ℤ,
            Q ∣ (t * 2 ^ 16 - (lane16 hi i).toInt * (lane16 z i).toInt) ∧
            |t| ≤ Bt ∧
            (lane16 r.1 i).toInt = (lane16 lo i).toInt + t ∧
            (lane16 r.2 i).toInt = (lane16 lo i).toInt - t ⦄ := by
  unfold backend.neon.ntt.ct_butterfly
  apply WP.spec_bind (mont_mul_bnd hi z zq qv Q Zb B Bt hQ hQpos hQlt hz hZb hzq hhi hB0 hBZ hBt)
  rintro t ⟨htb, htd⟩
  obtain ⟨hi1, hhi1, hhi1b⟩ := sub_16_model lo t
  rw [hhi1, bind_tc_ok]
  obtain ⟨lo1, hlo1, hlo1b⟩ := add_16_model lo t
  rw [hlo1, bind_tc_ok]
  -- both sums stay inside a lane, so `bmod` is the identity on them
  have hadd : ∀ i < 8, (lane16 lo1 i).toInt = (lane16 lo i).toInt + (lane16 t i).toInt := by
    intro i hi'
    have hl := abs_le.mp (hlo i hi')
    have ht := abs_le.mp (htb i hi')
    rw [add_lane_toInt lo t lo1 hlo1b i hi', bmod16_eq_self (by omega) (by omega)]
  have hsub : ∀ i < 8, (lane16 hi1 i).toInt = (lane16 lo i).toInt - (lane16 t i).toInt := by
    intro i hi'
    have hl := abs_le.mp (hlo i hi')
    have ht := abs_le.mp (htb i hi')
    rw [sub_lane_toInt lo t hi1 hhi1b i hi', bmod16_eq_self (by omega) (by omega)]
  refine (WP.spec_ok _).mpr ⟨fun i hi' => ?_, fun i hi' => ?_, fun i hi' => ?_⟩
  · have hl := abs_le.mp (hlo i hi')
    have ht := abs_le.mp (htb i hi')
    rw [hadd i hi', abs_le]
    omega
  · have hl := abs_le.mp (hlo i hi')
    have ht := abs_le.mp (htb i hi')
    rw [hsub i hi', abs_le]
    omega
  · exact ⟨(lane16 t i).toInt, htd i hi', htb i hi', hadd i hi', hsub i hi'⟩

/-- **The Gentleman-Sande butterfly.**  `(lo, hi) ↦ (lo + hi, (lo − hi)·ψ·2⁻¹⁶)`, with the ψ the
inverse tables already carry negated. -/
theorem gs_butterfly_spec (lo hi z zq qv : Vec128) (Q Zb B Bt : ℤ)
    (hQ : ∀ i < 8, (lane16 qv i).toInt = Q) (hQpos : 0 < Q) (hQlt : Q ≤ 2 ^ 14)
    (hz : ∀ i < 8, |(lane16 z i).toInt| ≤ Zb) (hZb : Zb ≤ 2 ^ 14)
    (hzq : ∀ i < 8, (2 ^ 16 : ℤ) ∣ ((lane16 zq i).toInt * Q - (lane16 z i).toInt))
    (hlo : VecBnd lo B) (hhi : VecBnd hi B) (hB0 : 0 ≤ B)
    (hBZ : 2 * B * Zb < 2 ^ 15 * Q) (hBt : 2 * B * Zb + 2 ^ 15 * Q ≤ 2 ^ 16 * Bt)
    (hfit : 2 * B ≤ 32767) :
    backend.neon.ntt.gs_butterfly lo hi z zq qv
      ⦃ (r : Vec128 × Vec128) =>
          VecBnd r.1 (2 * B) ∧ VecBnd r.2 Bt ∧
          ∀ i < 8,
            (lane16 r.1 i).toInt = (lane16 lo i).toInt + (lane16 hi i).toInt ∧
            Q ∣ ((lane16 r.2 i).toInt * 2 ^ 16
                  - ((lane16 lo i).toInt - (lane16 hi i).toInt) * (lane16 z i).toInt) ⦄ := by
  unfold backend.neon.ntt.gs_butterfly
  obtain ⟨diff, hdiff, hdiffb⟩ := sub_16_model lo hi
  rw [hdiff, bind_tc_ok]
  obtain ⟨lo1, hlo1, hlo1b⟩ := add_16_model lo hi
  rw [hlo1, bind_tc_ok]
  have hdv : ∀ i < 8, (lane16 diff i).toInt
      = (lane16 lo i).toInt - (lane16 hi i).toInt := by
    intro i hi'
    have hl := abs_le.mp (hlo i hi')
    have hh := abs_le.mp (hhi i hi')
    rw [sub_lane_toInt lo hi diff hdiffb i hi', bmod16_eq_self (by omega) (by omega)]
  have hlv : ∀ i < 8, (lane16 lo1 i).toInt
      = (lane16 lo i).toInt + (lane16 hi i).toInt := by
    intro i hi'
    have hl := abs_le.mp (hlo i hi')
    have hh := abs_le.mp (hhi i hi')
    rw [add_lane_toInt lo hi lo1 hlo1b i hi', bmod16_eq_self (by omega) (by omega)]
  have hdb : VecBnd diff (2 * B) := by
    intro i hi'
    have hl := abs_le.mp (hlo i hi')
    have hh := abs_le.mp (hhi i hi')
    rw [hdv i hi', abs_le]
    omega
  have hlb : VecBnd lo1 (2 * B) := by
    intro i hi'
    have hl := abs_le.mp (hlo i hi')
    have hh := abs_le.mp (hhi i hi')
    rw [hlv i hi', abs_le]
    omega
  apply WP.spec_bind (mont_mul_bnd diff z zq qv Q Zb (2 * B) Bt hQ hQpos hQlt hz hZb hzq hdb
    (by omega) hBZ hBt)
  rintro t ⟨htb, htd⟩
  refine (WP.spec_ok _).mpr ⟨hlb, htb, fun i hi' => ⟨hlv i hi', ?_⟩⟩
  rw [← hdv i hi']
  exact htd i hi'

end Kopis.Neon
