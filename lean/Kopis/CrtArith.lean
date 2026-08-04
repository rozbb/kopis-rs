/-
  # Kopis/CrtArith.lean — the integer arithmetic the two-prime NTT is built from.

  Signed Montgomery reduction and the exactness of a wrapping 16-bit lane are facts about ℤ, not
  about any backend: the portable transform in `src/arithmetic/ntt_crt.rs` and the vector ones do
  the same arithmetic, one lane at a time against sixteen at a time.  This file is that
  arithmetic, with no register, no array and no extraction in sight — the two code walks supply
  the values and consume the conclusions.

  The load-bearing step is `shift_sub_of_dvd`: when `2¹⁶` divides `X − Y`, the *difference of the
  truncated high halves* is the exact quotient.  That is what makes a Montgomery reduction right
  despite both halves having been rounded, and it is the step where reading `vpmulhw` (or the
  portable `>> 16`) as unsigned would give a wrong answer with no bit-level disagreement to show
  for it.
-/
import Mathlib.Data.Int.GCD
import Mathlib.Data.Int.ModEq
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Zify
import Mathlib.Tactic.Push

namespace Kopis.CrtArith

/-! ## Integer facts -/

/-- `bmod` by `2¹⁶` is the identity on the signed 16-bit range — the exactness condition every
wrapping lane operation is discharged with. -/
theorem bmod16_eq_self {z : ℤ} (h1 : -(2 ^ 15 : ℤ) ≤ z) (h2 : z < 2 ^ 15) :
    z.bmod (2 ^ 16) = z := by
  unfold Int.bmod
  norm_num
  split <;> omega

/-- `bmod` by `2³²` is the identity on the signed 32-bit range — the same exactness condition one
width up, for the two 32-bit products inside `mont_mul`. -/
theorem bmod32_eq_self {z : ℤ} (h1 : -(2 ^ 31 : ℤ) ≤ z) (h2 : z < 2 ^ 31) :
    z.bmod (2 ^ 32) = z := by
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

theorem bmod_congr {a b : ℤ} {n : ℕ} (h : a ≡ b [ZMOD (n : ℤ)]) : a.bmod n = b.bmod n := by
  simp only [Int.bmod]
  rw [show a % (n : ℤ) = b % (n : ℤ) from h]

/-! ## `mont_mul`, as integers

`t = a·zq` (wrapping), then `⌊a·z / 2¹⁶⌋ − ⌊t·q / 2¹⁶⌋`.  The table entry `zq` satisfies
`zq·q ≡ z (mod 2¹⁶)`, which is exactly what makes `2¹⁶ ∣ (a·z − t·q)`, so the two truncated
quotients differ by the *exact* one.

The last conclusion is the sharp bound, and it is the one that matters: `|R| < Q` is what a crude
per-level budget would use, and it is too weak — the growth of a Cooley-Tukey level has to be
proportional to the bound already reached, not a flat `+q`. -/

theorem mont_mul_core {A Z ZQ Q : ℤ} (hQpos : 0 < Q) (_hQlt : Q ≤ 2 ^ 15)
    (hzq : (2 ^ 16 : ℤ) ∣ (ZQ * Q - Z)) (hbnd : |A * Z| < 2 ^ 15 * Q) :
    ∃ R : ℤ,
      ((A * Z) >>> (16 : ℕ)) - (((A * ZQ).bmod (2 ^ 16)) * Q) >>> (16 : ℕ) = R ∧
      -Q < R ∧ R < Q ∧ Q ∣ (R * 2 ^ 16 - A * Z) ∧
      2 ^ 16 * |R| ≤ |A| * |Z| + 2 ^ 15 * Q := by
  set T := (A * ZQ).bmod (2 ^ 16) with hT
  obtain ⟨k2, hk2⟩ := hzq
  have hAZ := abs_lt.mp hbnd
  -- the divisibility the whole scheme turns on
  have hdvd : (2 ^ 16 : ℤ) ∣ (A * Z - T * Q) := by
    obtain ⟨k1, hk1⟩ : (2 ^ 16 : ℤ) ∣ (T - A * ZQ) := by rw [hT]; exact bmod_sub_dvd _ _
    refine ⟨-(A * k2) - k1 * Q, ?_⟩
    have hTeq : T = A * ZQ + 2 ^ 16 * k1 := by omega
    have hZQeq : ZQ * Q = Z + 2 ^ 16 * k2 := by omega
    calc A * Z - T * Q
        = A * Z - (A * ZQ + 2 ^ 16 * k1) * Q := by rw [hTeq]
      _ = A * Z - A * (ZQ * Q) - 2 ^ 16 * (k1 * Q) := by ring
      _ = A * Z - A * (Z + 2 ^ 16 * k2) - 2 ^ 16 * (k1 * Q) := by rw [hZQeq]
      _ = 2 ^ 16 * (-(A * k2) - k1 * Q) := by ring
  have hRmul : ((A * Z - T * Q) / 2 ^ 16) * 2 ^ 16 = A * Z - T * Q :=
    Int.ediv_mul_cancel hdvd
  have hTb := bmod16_bounds (A * ZQ)
  rw [← hT] at hTb
  have hTQ : -(2 ^ 15 * Q) ≤ T * Q ∧ T * Q ≤ 2 ^ 15 * Q := by
    constructor <;> nlinarith [hTb.1, hTb.2, hQpos]
  refine ⟨(A * Z - T * Q) / 2 ^ 16, shift_sub_of_dvd hdvd, ?_, ?_,
    ⟨-T, by rw [hRmul]; ring⟩, ?_⟩
  · nlinarith [hRmul, hAZ.1, hAZ.2, hTQ.1, hTQ.2]
  · nlinarith [hRmul, hAZ.1, hAZ.2, hTQ.1, hTQ.2]
  · rcases abs_cases ((A * Z - T * Q) / 2 ^ 16) with ⟨hb, _⟩ | ⟨hb, _⟩ <;> rw [hb]
    · rw [show (2:ℤ) ^ 16 * ((A * Z - T * Q) / 2 ^ 16) = A * Z - T * Q from by linarith [hRmul]]
      have hAZ' : A * Z ≤ |A| * |Z| := by rw [← abs_mul]; exact le_abs_self _
      linarith [hTQ.1]
    · rw [show (2:ℤ) ^ 16 * -((A * Z - T * Q) / 2 ^ 16) = -(A * Z - T * Q) from by
        linarith [hRmul]]
      have hAZ' : -(A * Z) ≤ |A| * |Z| := by rw [← abs_mul]; exact neg_le_abs _
      linarith [hTQ.2]

/-! ## `barrett`, as integers

`t ≈ round(x/q)` formed as `(hi(x·M) + 2^(SH−1)) >> SH`, then `r = x − t·q`.  The rounding addend
is what makes the result *centered*, and the bound is tight: the crude interval argument leaves
about `q/2048` of slack, which is exactly what the low bits of `x·M` can eat.  So the proof keeps
`a = x·M mod 2¹⁶` and `b = (hi + 2¹⁰) mod 2¹¹` as real quantities instead of bounding each
rounding step on its own — the identity `2²⁷·r = x·(2²⁷ − qM) + q·a + q·2¹⁶·(b − 2¹⁰)` is exact,
and every bound comes from it.

`hD` is the accuracy of the Barrett multiplier: `M = ⌊(2²⁷ + q/2)/q⌋` gives `|2²⁷ − qM| = 66` for
`q₁ = 7681` and `1218` for `q₂ = 10753`, both well inside the `2047` assumed here. -/

/-- `⌊x·M / 2¹⁶⌋` fits well inside an `i16`, so the rounding addend cannot overflow the lane. -/
theorem barrett_hi_bound {X M V : ℤ}
    (hXlo : -(2 ^ 15 : ℤ) ≤ X) (hXhi : X < 2 ^ 15) (hMpos : 0 < M) (hMlt : M < 2 ^ 15)
    (hV : V = (X * M) >>> (16 : ℕ)) : -(2 ^ 14 : ℤ) ≤ V ∧ V ≤ 2 ^ 14 := by
  have hXM : -(2 ^ 30 : ℤ) ≤ X * M ∧ X * M < 2 ^ 30 := by
    constructor <;> nlinarith [hXlo, hXhi, hMpos, hMlt]
  rw [hV, Int.shiftRight_eq_div_pow]
  push_cast
  norm_num at hXM ⊢
  omega

theorem barrett_core {X M Q V T : ℤ}
    (hXlo : -(2 ^ 15 : ℤ) ≤ X) (hXhi : X < 2 ^ 15)
    (hQpos : 0 < Q) (_hQlt : Q < 2 ^ 14) (hQodd : ¬ (2 ∣ Q))
    (_hMpos : 0 < M) (_hMlt : M < 2 ^ 15)
    (hD : |2 ^ 27 - Q * M| ≤ 2047)
    (hV : V = (X * M) >>> (16 : ℕ)) (hT : T = (V + 2 ^ 10) >>> (11 : ℕ)) :
    2 * |X - T * Q| < Q := by
  have hVv : V = X * M / 65536 := by
    rw [hV, Int.shiftRight_eq_div_pow]; push_cast; norm_num
  have hTv : T = (V + 1024) / 2048 := by
    rw [hT, Int.shiftRight_eq_div_pow]; push_cast; norm_num
  have hAlo : 0 ≤ X * M % 65536 := Int.emod_nonneg _ (by norm_num)
  have hAhi : X * M % 65536 < 65536 := Int.emod_lt_of_pos _ (by norm_num)
  have hBlo : 0 ≤ (V + 1024) % 2048 := Int.emod_nonneg _ (by norm_num)
  have hBhi : (V + 1024) % 2048 < 2048 := Int.emod_lt_of_pos _ (by norm_num)
  -- the exact identity the bounds all come from
  have e1 : 65536 * V = X * M - X * M % 65536 := by rw [hVv]; omega
  have e2 : 2048 * T = V - ((V + 1024) % 2048 - 1024) := by rw [hTv]; omega
  set A := X * M % 65536 with hAdef
  set B := (V + 1024) % 2048 - 1024 with hBdef
  clear_value A B
  have hkey : 2 ^ 27 * (X - T * Q) = X * (2 ^ 27 - Q * M) + Q * A + Q * 65536 * B := by
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
  have hup : (2 : ℤ) ^ 26 * (2 * (X - T * Q)) < 2 ^ 26 * (1 + Q) := by
    have h : (2:ℤ) ^ 26 * (2 * (X - T * Q)) = 2 ^ 27 * (X - T * Q) := by ring
    rw [h, hkey]; linarith [hXD.2, hQA.2, hQB.2]
  have hdn : (2 : ℤ) ^ 26 * (-(1 + Q)) < 2 ^ 26 * (2 * (X - T * Q)) := by
    have h : (2:ℤ) ^ 26 * (2 * (X - T * Q)) = 2 ^ 27 * (X - T * Q) := by ring
    rw [h, hkey]; linarith [hXD.1, hQA.1, hQB.1]
  have hup' : 2 * (X - T * Q) < 1 + Q := lt_of_mul_lt_mul_left hup (by norm_num)
  have hdn' : -(1 + Q) < 2 * (X - T * Q) := lt_of_mul_lt_mul_left hdn (by norm_num)
  rcases abs_cases (X - T * Q) with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h] <;> omega

end Kopis.CrtArith
