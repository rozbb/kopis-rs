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

/-- `bmod` by `2¹⁶` is the identity on the signed 16-bit range — the exactness condition every
wrapping lane operation is discharged with. -/
theorem bmod16_eq_self {z : ℤ} (h1 : -(2 ^ 15 : ℤ) ≤ z) (h2 : z < 2 ^ 15) :
    z.bmod (2 ^ 16) = z := by
  unfold Int.bmod
  norm_num
  split <;> omega

/-- `bmod` changes a value by a multiple of the modulus. -/
theorem bmod_sub_dvd (x : ℤ) (n : ℕ) : (n : ℤ) ∣ (x.bmod n - x) := by
  have h : Int.ModEq (n : ℤ) (x.bmod n) x := Int.bmod_emod
  exact Int.ModEq.dvd h.symm

/-- **The cancellation that makes Montgomery reduction work.**  When `2¹⁶` divides `X - Y`, the
difference of the two high halves is the exact quotient — no rounding error survives. -/
theorem shift_sub_of_dvd {X Y : ℤ} (h : (2 ^ 16 : ℤ) ∣ (X - Y)) :
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
          -Q < (lane16 c i).toInt ∧ (lane16 c i).toInt < Q ∧
          2 ^ 16 * |(lane16 c i).toInt|
            ≤ |(lane16 a i).toInt| * |(lane16 z i).toInt| + 2 ^ 15 * Q ⦄ := by
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
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact ⟨-T, by rw [hC, hRmul]; ring⟩
  · rw [hC]; exact hRbnd.1
  · rw [hC]; exact hRbnd.2
  · -- the *sharp* bound: `c·2¹⁶ = a·z − T·q` exactly, and `|T| ≤ 2¹⁵`.  This, not `|c| < q`,
    -- is what makes a four-level Cooley-Tukey run fit an `i16` lane — see `NttGrowth.lean`.
    rw [hC]
    rcases abs_cases ((A * Z - T * Q) / 2 ^ 16) with ⟨hb, _⟩ | ⟨hb, _⟩ <;> rw [hb]
    · rw [show (2:ℤ) ^ 16 * ((A * Z - T * Q) / 2 ^ 16) = A * Z - T * Q from by linarith [hRmul]]
      have hAZ' : A * Z ≤ |A| * |Z| := by rw [← abs_mul]; exact le_abs_self _
      linarith [hTQ.1]
    · rw [show (2:ℤ) ^ 16 * -((A * Z - T * Q) / 2 ^ 16) = -(A * Z - T * Q) from by
        linarith [hRmul]]
      have hAZ' : -(A * Z) ≤ |A| * |Z| := by rw [← abs_mul]; exact neg_le_abs _
      linarith [hTQ.2]


/-! ## Montgomery reduction of a general `i32`

`mont_mul` reduces the *product* of two `i16`.  The inverse NTT's `reduce_block` reduces an `i32`
that came out of the accumulator, so it has no product structure to lean on — but the cancellation
is the same one, and so is the bound argument. -/

/-- `bmod` by `2¹⁶` lands in the signed 16-bit range. -/
theorem bmod16_bounds (x : ℤ) :
    -(2 ^ 15 : ℤ) ≤ x.bmod (2 ^ 16) ∧ x.bmod (2 ^ 16) < 2 ^ 15 := by
  have h1 : (0 : ℤ) ≤ x % ((2 : ℤ) ^ 16) := Int.emod_nonneg x (by norm_num)
  have h2 : x % ((2 : ℤ) ^ 16) < 2 ^ 16 := Int.emod_lt_of_pos x (by norm_num)
  unfold Int.bmod
  norm_num
  norm_num at h1 h2
  split <;> omega

/-- **Signed Montgomery reduction of an `i32`.**  `lo` is the low half taken signed, `hi` the
arithmetic-shifted high half, and `T = lo·q⁻¹ (wrapping)`; then `hi − ⌊T·q / 2¹⁶⌋` is the exact
quotient `(X − T·q)/2¹⁶`, which is `X·2⁻¹⁶ mod q` and smaller than `q`. -/
theorem mont_reduce32 {X Q QINV : ℤ} (hQpos : 0 < Q) (_hQlt : Q ≤ 2 ^ 15)
    (hu : (2 ^ 16 : ℤ) ∣ (QINV * Q - 1)) (hX : |X| < 2 ^ 15 * Q) :
    ∃ R : ℤ,
      (X >>> (16 : ℕ)) - ((((X.bmod (2 ^ 16)) * QINV).bmod (2 ^ 16)) * Q) >>> (16 : ℕ) = R ∧
      -Q < R ∧ R < Q ∧ Q ∣ (R * 2 ^ 16 - X) ∧
      2 ^ 16 * |R| ≤ |X| + 2 ^ 15 * Q := by
  set L := X.bmod (2 ^ 16) with hL
  set T := (L * QINV).bmod (2 ^ 16) with hT
  obtain ⟨k2, hk2⟩ := hu
  -- `T·q ≡ L·q⁻¹·q ≡ L ≡ X (mod 2¹⁶)`
  have hdvd : (2 ^ 16 : ℤ) ∣ (X - T * Q) := by
    obtain ⟨k1, hk1⟩ : (2 ^ 16 : ℤ) ∣ (T - L * QINV) := by rw [hT]; exact bmod_sub_dvd _ _
    obtain ⟨k0, hk0⟩ : (2 ^ 16 : ℤ) ∣ (L - X) := by rw [hL]; exact bmod_sub_dvd _ _
    refine ⟨-k0 - L * k2 - k1 * Q, ?_⟩
    have hTeq : T = L * QINV + 2 ^ 16 * k1 := by omega
    have hQeq : QINV * Q = 1 + 2 ^ 16 * k2 := by omega
    have hXeq : X = L - 2 ^ 16 * k0 := by omega
    calc X - T * Q
        = (L - 2 ^ 16 * k0) - (L * QINV + 2 ^ 16 * k1) * Q := by rw [← hTeq, ← hXeq]
      _ = L - 2 ^ 16 * k0 - L * (QINV * Q) - 2 ^ 16 * (k1 * Q) := by ring
      _ = L - 2 ^ 16 * k0 - L * (1 + 2 ^ 16 * k2) - 2 ^ 16 * (k1 * Q) := by rw [hQeq]
      _ = 2 ^ 16 * (-k0 - L * k2 - k1 * Q) := by ring
  have hTb := bmod16_bounds (L * QINV)
  rw [← hT] at hTb
  have hR : ((X - T * Q) / 2 ^ 16) * 2 ^ 16 = X - T * Q := Int.ediv_mul_cancel hdvd
  have hXb := abs_lt.mp hX
  refine ⟨(X - T * Q) / 2 ^ 16, shift_sub_of_dvd hdvd, ?_, ?_, ⟨-T, by rw [hR]; ring⟩, ?_⟩
  · nlinarith [hR, hXb.1, hXb.2, hTb.1, hTb.2, hQpos]
  · nlinarith [hR, hXb.1, hXb.2, hTb.1, hTb.2, hQpos]
  · -- the *sharp* bound: `R·2¹⁶ = X − T·q` exactly, and `|T| ≤ 2¹⁵`
    have hTQ : -(2 ^ 15 * Q) ≤ T * Q ∧ T * Q ≤ 2 ^ 15 * Q := by
      constructor <;> nlinarith [hTb.1, hTb.2, hQpos]
    rcases abs_cases ((X - T * Q) / 2 ^ 16) with ⟨hbv, _⟩ | ⟨hbv, _⟩ <;> rw [hbv]
    · rw [show (2:ℤ) ^ 16 * ((X - T * Q) / 2 ^ 16) = X - T * Q from by linarith [hR]]
      linarith [hTQ.1, le_abs_self X]
    · rw [show (2:ℤ) ^ 16 * -((X - T * Q) / 2 ^ 16) = -(X - T * Q) from by linarith [hR]]
      linarith [hTQ.2, neg_le_abs X]

/-! ## `barrett`

`t ≈ round(x/q)` formed as `(hi(x·M) + 2^(SH−1)) >> SH`, then `r = x − t·q`.  The rounding addend
is what makes the result *centered*, and the bound is tight: the crude interval argument leaves
about `q/2048` of slack, which is exactly what the low bits of `x·M` can eat.  So the proof keeps
`a = x·M mod 2¹⁶` and `b = (hi + 2¹⁰) mod 2¹¹` as real quantities instead of bounding each
rounding step on its own — the identity `2²⁷·r = x·(2²⁷ − qM) + q·a + q·2¹⁶·(b − 2¹⁰)` is exact,
and every bound comes from it.

`hD` is the accuracy of the Barrett multiplier: `M = ⌊(2²⁷ + q/2)/q⌋` gives `|2²⁷ − qM| = 66` for
`q₁ = 7681` and `1218` for `q₂ = 10753`, both well inside the `2047` assumed here. -/

private theorem bmod_congr {a b : ℤ} {n : ℕ} (h : a ≡ b [ZMOD (n : ℤ)]) : a.bmod n = b.bmod n := by
  simp only [Int.bmod]
  rw [show a % (n : ℤ) = b % (n : ℤ) from h]

theorem barrett_lane_spec (x m round q : Vec256) (Q M : ℤ)
    (hQ : ∀ i < 16, (lane16 q i).toInt = Q) (hM : ∀ i < 16, (lane16 m i).toInt = M)
    (hRnd : ∀ i < 16, (lane16 round i).toInt = 2 ^ 10)
    (hQpos : 0 < Q) (hQlt : Q < 2 ^ 14) (hQodd : ¬ (2 ∣ Q))
    (hMpos : 0 < M) (hMlt : M < 2 ^ 15)
    (hD : |2 ^ 27 - Q * M| ≤ 2047) :
    backend.avx2.ntt.barrett x m round q
      ⦃ (c : Vec256) => ∀ i < 16,
          Q ∣ ((lane16 c i).toInt - (lane16 x i).toInt) ∧ 2 * |(lane16 c i).toInt| < Q ⦄ := by
  unfold backend.avx2.ntt.barrett
  obtain ⟨v, hv, hvb⟩ := mulhi_epi16_model x m
  rw [hv, bind_tc_ok]
  obtain ⟨t0, ht0, ht0b⟩ := add_epi16_model v round
  rw [ht0, bind_tc_ok]
  obtain ⟨t, ht, htb⟩ := srai_epi16_model 11#i32 t0 (by decide)
  rw [ht, bind_tc_ok]
  obtain ⟨w, hw, hwb⟩ := mullo_epi16_model t q
  rw [hw, bind_tc_ok]
  obtain ⟨c, hc, hcb⟩ := sub_epi16_model x w
  rw [hc]
  simp only [WP.spec_ok]
  intro i hi
  have hVv := mulhi_lane_toInt x m v hvb i hi
  have hT0v := add_lane_toInt v round t0 ht0b i hi
  have hTv := srai_lane_toInt _ t0 t htb i hi
  have hWv := mullo_lane_toInt t q w hwb i hi
  have hCv := sub_lane_toInt x w c hcb i hi
  rw [hM i hi] at hVv
  rw [hRnd i hi] at hT0v
  rw [hQ i hi] at hWv
  rw [Int.shiftRight_eq_div_pow] at hVv
  norm_num at hVv
  obtain ⟨hXlo, hXhi⟩ := toInt_bounds (lane16 x i)
  set X := (lane16 x i).toInt with hX
  set V := (lane16 v i).toInt with hVdef
  -- `v` is the exact floor of `X·M / 2¹⁶`, so it fits and the rounding addend cannot overflow
  have hXM : -(2 ^ 30 : ℤ) ≤ X * M ∧ X * M < 2 ^ 30 := by
    constructor <;> nlinarith [hXlo, hXhi, hMpos, hMlt]
  have hAlo : 0 ≤ X * M % 65536 := Int.emod_nonneg _ (by norm_num)
  have hAhi : X * M % 65536 < 65536 := Int.emod_lt_of_pos _ (by norm_num)
  have hVbnd : -(2 ^ 14 : ℤ) ≤ V ∧ V ≤ 2 ^ 14 := by rw [hVv]; omega
  have hT0 : (lane16 t0 i).toInt = V + 2 ^ 10 := by
    rw [hT0v]; exact bmod16_eq_self (by omega) (by omega)
  rw [hT0, show ((11#i32).val.toNat) = 11 from rfl, Int.shiftRight_eq_div_pow] at hTv
  norm_num at hTv
  set T := (lane16 t i).toInt with hTdef
  have hBlo : 0 ≤ (V + 1024) % 2048 := Int.emod_nonneg _ (by norm_num)
  have hBhi : (V + 1024) % 2048 < 2048 := Int.emod_lt_of_pos _ (by norm_num)
  set A := X * M % 65536 with hAdef
  set B := (V + 1024) % 2048 - 1024 with hBdef
  set R := X - T * Q with hR
  -- the exact identity the bounds all come from
  have e1 : 65536 * V = X * M - A := by rw [hVv, hAdef]; omega
  have e2 : 2048 * T = V - B := by rw [hTv, hBdef]; omega
  have hkey : 2 ^ 27 * R = X * (2 ^ 27 - Q * M) + Q * A + Q * 65536 * B := by
    rw [hR]
    have h1 : (2:ℤ) ^ 27 * (X - T * Q) = 2 ^ 27 * X - Q * (65536 * (2048 * T)) := by ring
    rw [h1, e2]
    have h2 : Q * (65536 * (V - B)) = Q * (65536 * V) - Q * 65536 * B := by ring
    rw [h2, e1]
    ring
  have hXD : -(2 ^ 26 : ℤ) < X * (2 ^ 27 - Q * M) ∧ X * (2 ^ 27 - Q * M) < 2 ^ 26 := by
    rw [abs_le] at hD
    constructor <;> nlinarith [hXlo, hXhi, hD.1, hD.2]
  have hQA : 0 ≤ Q * A ∧ Q * A ≤ Q * 65535 := by
    constructor <;> nlinarith [hQpos, hAlo, hAhi]
  have hQB : -(Q * 65536 * 1024) ≤ Q * 65536 * B ∧ Q * 65536 * B ≤ Q * 65536 * 1023 := by
    constructor <;> nlinarith [hQpos, hBlo, hBhi]
  -- hence `2R` is strictly inside `±Q`
  have hup : (2 : ℤ) ^ 26 * (2 * R) < 2 ^ 26 * (1 + Q) := by
    have : (2:ℤ) ^ 26 * (2 * R) = 2 ^ 27 * R := by ring
    rw [this, hkey]; linarith [hXD.2, hQA.2, hQB.2]
  have hdn : (2 : ℤ) ^ 26 * (-(1 + Q)) < 2 ^ 26 * (2 * R) := by
    have : (2:ℤ) ^ 26 * (2 * R) = 2 ^ 27 * R := by ring
    rw [this, hkey]; linarith [hXD.1, hQA.1, hQB.1]
  have hup' : 2 * R < 1 + Q := lt_of_mul_lt_mul_left hup (by norm_num)
  have hdn' : -(1 + Q) < 2 * R := lt_of_mul_lt_mul_left hdn (by norm_num)
  have hRbnd : 2 * |R| < Q := by
    rcases abs_cases R with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h] <;> omega
  -- so the final wrapping subtraction is exact
  have hCR : (lane16 c i).toInt = R := by
    rw [hCv, hWv]
    have hcong : (X - (T * Q).bmod (2 ^ 16)) ≡ (X - T * Q) [ZMOD (((2 ^ 16 : ℕ)) : ℤ)] :=
      Int.ModEq.sub (Int.ModEq.refl X) Int.bmod_emod
    calc (X - (T * Q).bmod (2 ^ 16)).bmod (2 ^ 16)
        = (X - T * Q).bmod (2 ^ 16) := bmod_congr hcong
      _ = R := by rw [← hR]; exact bmod16_eq_self (by omega) (by omega)
  exact ⟨⟨-T, by rw [hCR, hR]; ring⟩, by rw [hCR]; exact hRbnd⟩

end Kopis.Avx2