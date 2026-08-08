/-
  # Kopis/Neon/NttReduce.lean — the two lane-level reductions the NEON NTT is built from.

  Every butterfly in `src/backend/neon/ntt.rs` is a `mont_mul`, and every re-centring pass is a
  `barrett`.  Both are specified here in the same shape as the serial `mont_reduce_spec` and
  `barrett_reduce_spec` — a congruence and a magnitude bound — at 16-bit lane width, through
  `Kopis/Neon/LaneArith.lean`'s signed reading of the lanes.

  ## `mont_mul`

  `Kopis/Neon/LaneArith.lean` already did the hard half: `mont_mul_lane` says

      c · 2¹⁶  =  a·z − t·q

  *exactly*, with `t = a·zq` truncated to 16 bits.  That is a stronger statement than its AVX2
  counterpart arrives at, and it arrives differently — AVX2 takes two truncated high halves whose
  difference happens to be exact because `2¹⁶ ∣ (a·z − t·q)`, while here the two `sqdmulh` results
  carry the same doubling carry and `shsub` cancels it.  Given that identity, everything below is
  ordinary interval arithmetic, and it is the *same* interval arithmetic as AVX2's: `|t| ≤ 2¹⁵`
  bounds the correction, and the sharp form `2¹⁶·|c| ≤ |a|·|z| + 2¹⁵·q` is what makes a run of
  Cooley-Tukey levels fit an `i16` lane.

  The extra hypotheses over AVX2's are the two saturation side conditions — `z` and `q` are not
  `−2¹⁵`.  Both are constants of `src/backend/crt.rs`; neither is anywhere near.

  ## `barrett`

  `t ≈ round(x/q)` formed as `(mulhi(x, M) + 2^(SH−1)) >> SH`, then `r = x − t·q`.  The rounding
  addend is what makes the result *centered*, and the bound is tight: the crude interval argument
  leaves about `q/2048` of slack, which is exactly what the low bits of `x·M` can eat.  So the
  proof keeps `A = x·M mod 2¹⁶` and `B = (hi + 2¹⁰) mod 2¹¹` as real quantities instead of
  bounding each rounding step on its own — the identity

      2²⁷·r  =  x·(2²⁷ − qM) + q·A + q·2¹⁶·(B − 2¹⁰)

  is exact, and every bound comes from it.  This is `Kopis/Avx2/NttReduce.lean`'s argument
  unchanged; the only difference on this backend is that `mulhi` is two instructions rather than
  one, which `Kopis/Neon/LaneArith.lean` has already absorbed.

  `hD` is the accuracy of the Barrett multiplier: `M = ⌊(2²⁷ + q/2)/q⌋` gives `|2²⁷ − qM| = 66`
  for `q₁ = 7681` and `1218` for `q₂ = 10753`, both well inside the `2047` assumed here.
-/
import Kopis.Neon.LaneArith
import Kopis.CrtArith

open Aeneas Aeneas.Std Result
open RustKopisNeon

namespace Kopis.Neon

open RustKopisNeon.backend.neon.intrinsics
open Kopis.CrtArith

export Kopis.CrtArith (bmod16_eq_self bmod_sub_dvd shift_sub_of_dvd bmod16_bounds mont_reduce32
  bmod_congr)

set_option maxHeartbeats 1000000

/-! ## `mulhi`, as the extraction writes it

Two instructions on this backend: `sqdmulh` then `sshr #1`.  Stated as a spec so `barrett` can
consume it without repeating the saturation side condition. -/

theorem mulhi_spec (a b : Vec128) (hb : ∀ i < 8, -32767 ≤ (lane16 b i).toInt) :
    backend.neon.ntt.mulhi a b
      ⦃ (c : Vec128) => ∀ i < 8,
          (lane16 c i).toInt = (lane16 a i).toInt * (lane16 b i).toInt / 65536 ⦄ := by
  unfold backend.neon.ntt.mulhi
  obtain ⟨s, hs, hsb⟩ := sqdmulh_s16_model a b
  rw [hs, bind_tc_ok]
  obtain ⟨c, hc, hcb⟩ := sshr_n_s16_model 1#i32 s (by decide) (by decide)
  rw [hc]
  simp only [WP.spec_ok]
  intro i hi
  exact mulhi_lane_toInt a b s c hsb (by simpa using hcb) i hi (hb i hi)

/-! ## `mont_mul` -/

/-- **The Montgomery multiply, with its congruence and both bounds.**  The last conjunct is the
sharp one: `2¹⁶·|c| ≤ |a|·|z| + 2¹⁵·q` says the growth of a butterfly is proportional to the
bound already reached, which is what the growth schedule is checked against. -/
theorem mont_mul_lane_spec (a z zq qv : Vec128) (Q : ℤ)
    (hQ : ∀ i < 8, (lane16 qv i).toInt = Q) (hQpos : 0 < Q) (hQlt : Q ≤ 2 ^ 15)
    (hZsat : ∀ i < 8, -32767 ≤ (lane16 z i).toInt)
    (hzq : ∀ i < 8, (2 ^ 16 : ℤ) ∣ ((lane16 zq i).toInt * Q - (lane16 z i).toInt))
    (hbnd : ∀ i < 8, |(lane16 a i).toInt * (lane16 z i).toInt| < 2 ^ 15 * Q) :
    backend.neon.ntt.mont_mul a z zq qv
      ⦃ (c : Vec128) => ∀ i < 8,
          (Q ∣ ((lane16 c i).toInt * 2 ^ 16 - (lane16 a i).toInt * (lane16 z i).toInt)) ∧
          -Q < (lane16 c i).toInt ∧ (lane16 c i).toInt < Q ∧
          2 ^ 16 * |(lane16 c i).toInt|
            ≤ |(lane16 a i).toInt| * |(lane16 z i).toInt| + 2 ^ 15 * Q ⦄ := by
  unfold backend.neon.ntt.mont_mul
  obtain ⟨t, ht, htb⟩ := mul_16_model a zq
  rw [ht, bind_tc_ok]
  obtain ⟨s1, hs1, hs1b⟩ := sqdmulh_s16_model a z
  rw [hs1, bind_tc_ok]
  obtain ⟨s2, hs2, hs2b⟩ := sqdmulh_s16_model t qv
  rw [hs2, bind_tc_ok]
  obtain ⟨c, hc, hcb⟩ := shsub_s16_model s1 s2
  rw [hc]
  simp only [WP.spec_ok]
  intro i hi
  -- the table condition, in the residue form `mont_mul_lane` wants
  have hQsat : -32767 ≤ (lane16 qv i).toInt := by rw [hQ i hi]; omega
  have hres : (lane16 zq i).toInt * (lane16 qv i).toInt % 65536
      = (lane16 z i).toInt % 65536 := by
    rw [hQ i hi]
    have hd : (65536 : ℤ) ∣ ((lane16 z i).toInt - (lane16 zq i).toInt * Q) := by
      have h := hzq i hi
      norm_num at h
      exact dvd_sub_comm.mp h
    exact Int.modEq_iff_dvd.mpr hd
  -- the exactness, from `LaneArith.lean`
  have hmont := mont_mul_lane a z zq qv t s1 s2 c htb hs1b hs2b hcb i hi
    (hZsat i hi) hQsat hres
  rw [hQ i hi] at hmont
  obtain ⟨hTlo, hThi⟩ := toInt_bounds (lane16 t i)
  have hAZ := abs_lt.mp (hbnd i hi)
  set A := (lane16 a i).toInt with hA
  set Z := (lane16 z i).toInt with hZ
  set T := (lane16 t i).toInt with hT
  set C := (lane16 c i).toInt with hC
  have hTQ : -(2 ^ 15 * Q) ≤ T * Q ∧ T * Q ≤ 2 ^ 15 * Q := by
    constructor <;> nlinarith [hTlo, hThi, hQpos]
  have hkey : C * 2 ^ 16 = A * Z - T * Q := by norm_num at hmont ⊢; linarith [hmont]
  refine ⟨⟨-T, by linarith [hkey]⟩, ?_, ?_, ?_⟩
  · nlinarith [hkey, hAZ.1, hTQ.2]
  · nlinarith [hkey, hAZ.2, hTQ.1]
  · rcases abs_cases C with ⟨hb, _⟩ | ⟨hb, _⟩ <;> rw [hb]
    · have hAZ' : A * Z ≤ |A| * |Z| := by rw [← abs_mul]; exact le_abs_self _
      nlinarith [hkey, hTQ.1]
    · have hAZ' : -(A * Z) ≤ |A| * |Z| := by rw [← abs_mul]; exact neg_le_abs _
      nlinarith [hkey, hTQ.2]

/-! ## `barrett` -/

/-- **The centred Barrett reduction.**  `r ≡ x (mod q)` with `2·|r| < q`. -/
theorem barrett_lane_spec (x m round qv : Vec128) (Q M : ℤ)
    (hQ : ∀ i < 8, (lane16 qv i).toInt = Q) (hM : ∀ i < 8, (lane16 m i).toInt = M)
    (hRnd : ∀ i < 8, (lane16 round i).toInt = 2 ^ 10)
    (hQpos : 0 < Q) (hQlt : Q < 2 ^ 14) (hQodd : ¬ (2 ∣ Q))
    (hMpos : 0 < M) (hMlt : M < 2 ^ 15)
    (hD : |2 ^ 27 - Q * M| ≤ 2047) :
    backend.neon.ntt.barrett x m round qv
      ⦃ (c : Vec128) => ∀ i < 8,
          Q ∣ ((lane16 c i).toInt - (lane16 x i).toInt) ∧ 2 * |(lane16 c i).toInt| < Q ⦄ := by
  unfold backend.neon.ntt.barrett
  apply WP.spec_bind (mulhi_spec x m (fun i hi => by rw [hM i hi]; omega))
  intro v hVall
  obtain ⟨t0, ht0, ht0b⟩ := add_16_model v round
  rw [ht0, bind_tc_ok]
  obtain ⟨t, ht, htb⟩ := sshr_n_s16_model 11#i32 t0 (by decide) (by decide)
  rw [ht, bind_tc_ok]
  obtain ⟨w, hw, hwb⟩ := mul_16_model t qv
  rw [hw, bind_tc_ok]
  obtain ⟨c, hc, hcb⟩ := sub_16_model x w
  rw [hc]
  simp only [WP.spec_ok]
  intro i hi
  have hVv := hVall i hi
  have hT0v := add_lane_toInt v round t0 ht0b i hi
  have hTv := sshr_lane_toInt _ t0 t (by simpa using htb) i hi
  have hWv := mul_lane_toInt t qv w hwb i hi
  have hCv := sub_lane_toInt x w c hcb i hi
  rw [hM i hi] at hVv
  rw [hRnd i hi] at hT0v
  rw [hQ i hi] at hWv
  obtain ⟨hXlo, hXhi⟩ := toInt_bounds (lane16 x i)
  set X := (lane16 x i).toInt with hX
  set V := (lane16 v i).toInt with hVdef
  have hXM : -(2 ^ 30 : ℤ) ≤ X * M ∧ X * M < 2 ^ 30 := by
    constructor <;> nlinarith [hXlo, hXhi, hMpos, hMlt]
  have hAlo : 0 ≤ X * M % 65536 := Int.emod_nonneg _ (by norm_num)
  have hAhi : X * M % 65536 < 65536 := Int.emod_lt_of_pos _ (by norm_num)
  have hVbnd : -(2 ^ 14 : ℤ) ≤ V ∧ V ≤ 2 ^ 14 := by rw [hVv]; omega
  have hT0 : (lane16 t0 i).toInt = V + 2 ^ 10 := by
    rw [hT0v]; exact bmod16_eq_self (by omega) (by omega)
  rw [hT0, Int.shiftRight_eq_div_pow] at hTv
  norm_num at hTv
  set T := (lane16 t i).toInt with hTdef
  have hBlo : 0 ≤ (V + 1024) % 2048 := Int.emod_nonneg _ (by norm_num)
  have hBhi : (V + 1024) % 2048 < 2048 := Int.emod_lt_of_pos _ (by norm_num)
  set A := X * M % 65536 with hAdef
  set B := (V + 1024) % 2048 - 1024 with hBdef
  set R := X - T * Q with hR
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
  have hCR : (lane16 c i).toInt = R := by
    rw [hCv, hWv]
    have hcong : (X - (T * Q).bmod (2 ^ 16)) ≡ (X - T * Q) [ZMOD (((2 ^ 16 : ℕ)) : ℤ)] :=
      Int.ModEq.sub (Int.ModEq.refl X) Int.bmod_emod
    calc (X - (T * Q).bmod (2 ^ 16)).bmod (2 ^ 16)
        = (X - T * Q).bmod (2 ^ 16) := bmod_congr hcong
      _ = R := by rw [← hR]; exact bmod16_eq_self (by omega) (by omega)
  exact ⟨⟨-T, by rw [hCR, hR]; ring⟩, by rw [hCR]; exact hRbnd⟩

end Kopis.Neon
