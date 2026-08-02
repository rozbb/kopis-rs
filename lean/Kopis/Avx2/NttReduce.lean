/-
  # Kopis/Avx2/NttReduce.lean — the lane-level Montgomery multiply the AVX2 NTT is built from.

  `mont_mul` is four instructions, and every butterfly in `src/backend/avx2/ntt.rs` is made of
  it.  Its specification is the same shape as the serial `mont_reduce_spec` in
  `Kopis/Properties/NttReduceMont.lean` — a congruence and a magnitude bound — but at 16-bit
  lane width, so it is stated through `Kopis/Avx2/LaneArith.lean`'s signed reading of the lanes.

  The subtlety, and the reason the input bound is a hypothesis rather than a side condition
  discharged in passing: the intermediate products *do* overflow 16 bits and wrap, and only the
  final result is small.  `mullo_epi16` is a wrapping multiplication and `sub_epi16` a wrapping
  subtraction; what makes the answer right is that `2¹⁶` divides the quantity whose high half is
  taken, so the two truncated quotients differ by the exact one and the wrapping cancels.  That
  is `shift_sub_of_dvd`, and it is the step where a model treating `vpmulhw` as *unsigned* would
  give a wrong answer with no bit-level disagreement to show for it.
-/
import Kopis.Avx2.LaneArith

open Aeneas Aeneas.Std Result
open RustKopisAvx2

namespace Kopis.Avx2

open RustKopisAvx2.backend.avx2.intrinsics

set_option maxHeartbeats 1000000

/-! ## Integer facts -/

/-- `bmod` by `2¹⁶` is the identity on the signed 16-bit range. -/
private theorem bmod16_eq_self {z : ℤ} (h1 : -(2 ^ 15 : ℤ) ≤ z) (h2 : z < 2 ^ 15) :
    z.bmod (2 ^ 16) = z := by
  unfold Int.bmod
  norm_num
  split <;> omega

/-- `bmod` changes a value by a multiple of the modulus. -/
private theorem bmod_sub_dvd (x : ℤ) (n : ℕ) : (n : ℤ) ∣ (x.bmod n - x) := by
  have h : Int.ModEq (n : ℤ) (x.bmod n) x := Int.bmod_emod
  exact Int.ModEq.dvd h.symm

/-- **The cancellation that makes Montgomery reduction work.**  When `2¹⁶` divides `X - Y`, the
difference of the two high halves is the exact quotient — no rounding error survives. -/
private theorem shift_sub_of_dvd {X Y : ℤ} (h : (2 ^ 16 : ℤ) ∣ (X - Y)) :
    (X >>> (16 : ℕ)) - (Y >>> (16 : ℕ)) = (X - Y) / 2 ^ 16 := by
  obtain ⟨k, hk⟩ := h
  have hX : X = Y + 2 ^ 16 * k := by omega
  rw [Int.shiftRight_eq_div_pow, Int.shiftRight_eq_div_pow, hX]
  push_cast
  omega

/-! ## `mont_mul`

`t = a·zq` (wrapping), then `⌊a·z / 2¹⁶⌋ − ⌊t·q / 2¹⁶⌋`.  The table entry `zq` satisfies
`zq·q ≡ z (mod 2¹⁶)`, which is exactly what makes `2¹⁶ ∣ (a·z − t·q)`.

The hypotheses are the ones `src/backend/crt.rs` establishes for its tables: `q` is broadcast,
positive and below `2¹⁵`; `zq` is the Montgomery-transformed twiddle; and the input is small
enough that `a·z` stays under `2¹⁵·q`, which is what the growth schedule maintains. -/

theorem mont_mul_lane_spec (a z zq qv : Vec256) (Q : ℤ)
    (hQ : ∀ i < 16, (lane16 qv i).toInt = Q) (hQpos : 0 < Q) (hQlt : Q ≤ 2 ^ 15)
    (hzq : ∀ i < 16, (2 ^ 16 : ℤ) ∣ ((lane16 zq i).toInt * Q - (lane16 z i).toInt))
    (hbnd : ∀ i < 16, |(lane16 a i).toInt * (lane16 z i).toInt| < 2 ^ 15 * Q) :
    backend.avx2.ntt.mont_mul a z zq qv
      ⦃ (c : Vec256) => ∀ i < 16,
          (Q ∣ ((lane16 c i).toInt * 2 ^ 16 - (lane16 a i).toInt * (lane16 z i).toInt)) ∧
          -Q < (lane16 c i).toInt ∧ (lane16 c i).toInt < Q ⦄ := by
  unfold backend.avx2.ntt.mont_mul
  obtain ⟨t, ht, htb⟩ := mullo_epi16_model a zq
  rw [ht, bind_tc_ok]
  obtain ⟨v, hv, hvb⟩ := mulhi_epi16_model a z
  rw [hv, bind_tc_ok]
  obtain ⟨v1, hv1, hv1b⟩ := mulhi_epi16_model t qv
  rw [hv1, bind_tc_ok]
  obtain ⟨c, hc, hcb⟩ := sub_epi16_model v v1
  rw [hc]
  simp only [WP.spec_ok]
  intro i hi
  have hTv := mullo_lane_toInt a zq t htb i hi
  have hVv := mulhi_lane_toInt a z v hvb i hi
  have hV1v := mulhi_lane_toInt t qv v1 hv1b i hi
  have hCv := sub_lane_toInt v v1 c hcb i hi
  rw [hQ i hi] at hV1v
  obtain ⟨k2, hk2⟩ := hzq i hi
  have hAZ := abs_lt.mp (hbnd i hi)
  set A := (lane16 a i).toInt with hA
  set Z := (lane16 z i).toInt with hZ
  set ZQ := (lane16 zq i).toInt with hZQ
  set T := (lane16 t i).toInt with hT
  -- the divisibility the whole scheme turns on
  have hdvd : (2 ^ 16 : ℤ) ∣ (A * Z - T * Q) := by
    obtain ⟨k1, hk1⟩ : (2 ^ 16 : ℤ) ∣ (T - A * ZQ) := by
      rw [hTv]; exact bmod_sub_dvd _ _
    refine ⟨-(A * k2) - k1 * Q, ?_⟩
    have hTeq : T = A * ZQ + 2 ^ 16 * k1 := by omega
    have hZQeq : ZQ * Q = Z + 2 ^ 16 * k2 := by omega
    calc A * Z - T * Q
        = A * Z - (A * ZQ + 2 ^ 16 * k1) * Q := by rw [hTeq]
      _ = A * Z - A * (ZQ * Q) - 2 ^ 16 * (k1 * Q) := by ring
      _ = A * Z - A * (Z + 2 ^ 16 * k2) - 2 ^ 16 * (k1 * Q) := by rw [hZQeq]
      _ = 2 ^ 16 * (-(A * k2) - k1 * Q) := by ring
  -- so the two truncated quotients differ by the exact one
  have hsub : (lane16 v i).toInt - (lane16 v1 i).toInt = (A * Z - T * Q) / 2 ^ 16 := by
    rw [hVv, hV1v]; exact shift_sub_of_dvd hdvd
  have hRmul : ((A * Z - T * Q) / 2 ^ 16) * 2 ^ 16 = A * Z - T * Q :=
    Int.ediv_mul_cancel hdvd
  -- the result is small, so the final wrapping subtraction is exact
  obtain ⟨hTlo, hThi⟩ := toInt_bounds (lane16 t i)
  have hTQ : -(2 ^ 15 * Q) ≤ T * Q ∧ T * Q ≤ 2 ^ 15 * Q := by
    constructor <;> nlinarith [hTlo, hThi, hQpos]
  have hRbnd : -Q < (A * Z - T * Q) / 2 ^ 16 ∧ (A * Z - T * Q) / 2 ^ 16 < Q := by
    constructor <;> nlinarith [hRmul, hAZ.1, hAZ.2, hTQ.1, hTQ.2]
  have hC : (lane16 c i).toInt = (A * Z - T * Q) / 2 ^ 16 := by
    rw [hCv, hsub]
    exact bmod16_eq_self (by omega) (by omega)
  refine ⟨?_, ?_, ?_⟩
  · exact ⟨-T, by rw [hC, hRmul]; ring⟩
  · rw [hC]; exact hRbnd.1
  · rw [hC]; exact hRbnd.2

end Kopis.Avx2
