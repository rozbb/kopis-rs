/-
  # Kopis/Avx2/Crt.lean — why the two backends agree at the endpoints (plan phase F4).

  The AVX2 NTT does not compute the same intermediate values as the portable one: it carries two
  16-bit residues per coefficient, mod `q₁ = 7681` and `q₂ = 10753`, where the portable code
  carries one residue mod `p = 50330113`.  `Kopis/Avx2/NttMulLane.lean` makes that concrete —
  `pointwise_mul_acc` multiplies the two halves of each `i32` independently, which is a different
  function of the same bits from the portable `i32 × i32 → i64`.

  So there is no stage-by-stage correspondence to lean on.  What makes the endpoints agree is
  this file: the residue *pair* determines the coefficient, because `q₁q₂ = 82593793` and the
  exactness bound the pipeline maintains is `ℓ·256·(2¹³−1)·(μ/2) ≤ 25162752`, comfortably inside
  the centred range `±41296896`.  Everything the vector code does between the endpoints only has
  to preserve the two residues.

  Two theorems: the Garner step the backend actually runs produces a representative of the right
  class, and a class has at most one member in the centred range.
-/
import Mathlib.Tactic
import Mathlib.Data.Int.GCD

namespace Kopis.Avx2

/-! ## The two primes -/

/-- `q₁`, the first NTT prime. -/
def q1 : ℤ := 7681
/-- `q₂`, the second NTT prime. -/
def q2 : ℤ := 10753
/-- `q₁·q₂`, the CRT modulus (`CRT_Q` in `src/backend/crt.rs`). -/
def crtQ : ℤ := 82593793

theorem crtQ_eq : crtQ = q1 * q2 := by norm_num [crtQ, q1, q2]

theorem q1_pos : 0 < q1 := by norm_num [q1]
theorem q2_pos : 0 < q2 := by norm_num [q2]

/-- The two primes are coprime — `IsCoprime` over `ℤ`, which is what the CRT step needs. -/
theorem q1_q2_coprime : IsCoprime q1 q2 := by
  rw [Int.isCoprime_iff_gcd_eq_one]
  norm_num [q1, q2]

/-! ## Garner's step

The backend computes `t ≡ (a₂ − a₁)·q₁⁻¹ (mod q₂)` and then `y = a₁ + q₁·t`.  Nothing here needs
`t` to be reduced or `q₁` to be prime: only that `q₁·t ≡ a₂ − a₁` mod `q₂`, which is what the
Montgomery multiply by `CRT_Q1_INV_MONT` establishes. -/

/-- **Garner's step lands in the right class.**  If `a₁` and `a₂` are the two residues of `x` and
`t` solves `q₁·t ≡ a₂ − a₁ (mod q₂)`, then `a₁ + q₁·t ≡ x (mod q₁q₂)`. -/
theorem garner_congr {a1 a2 t x : ℤ}
    (h1 : x ≡ a1 [ZMOD q1]) (h2 : x ≡ a2 [ZMOD q2])
    (ht : q1 * t ≡ a2 - a1 [ZMOD q2]) :
    a1 + q1 * t ≡ x [ZMOD q1 * q2] := by
  -- `q₁ ∣ y − x` because `q₁·t` vanishes mod `q₁` and `a₁ ≡ x`
  have d1 : q1 ∣ (a1 + q1 * t - x) := by
    have : q1 ∣ (a1 - x) := Int.ModEq.dvd h1
    obtain ⟨c, hc⟩ := this
    exact ⟨c + t, by linarith [hc]⟩
  -- `q₂ ∣ y − x` because `a₁ + q₁·t ≡ a₁ + (a₂ − a₁) = a₂ ≡ x`
  have d2 : q2 ∣ (a1 + q1 * t - x) := by
    have e1 : q2 ∣ (q1 * t - (a2 - a1)) := Int.ModEq.dvd ht.symm
    have e2 : q2 ∣ (a2 - x) := Int.ModEq.dvd h2
    obtain ⟨c1, hc1⟩ := e1
    obtain ⟨c2, hc2⟩ := e2
    exact ⟨c1 + c2, by linarith [hc1, hc2]⟩
  exact Int.ModEq.symm (Int.modEq_iff_dvd.mpr (by
    have := (IsCoprime.mul_dvd q1_q2_coprime d1 d2)
    simpa using this))

/-! ## …and the class has one centred member

`q₁q₂ = 82593793`, so the centred range is `±41296896`.  The exactness bound the pipeline
maintains — `crt.rs` records `ℓ·256·(2¹³−1)·(μ/2) ≤ 25162752` — is well inside it, which is the
whole reason two 16-bit transforms can replace one 26-bit one. -/

/-- **Uniqueness.**  Two integers in the centred range of `q₁q₂` that agree modulo `q₁q₂` are
equal.  This is the step where "the vector code kept both residues" becomes "the vector code
computed the same coefficient". -/
theorem crt_unique {x y : ℤ} (hxy : x ≡ y [ZMOD q1 * q2])
    (hx : 2 * |x| < q1 * q2) (hy : 2 * |y| < q1 * q2) : x = y := by
  have hq : (0 : ℤ) < q1 * q2 := by norm_num [q1, q2]
  obtain ⟨c, hc⟩ : (q1 * q2) ∣ (x - y) := Int.ModEq.dvd hxy.symm
  have hxr : -(q1 * q2) < 2 * x ∧ 2 * x < q1 * q2 :=
    ⟨by linarith [neg_abs_le x], by linarith [le_abs_self x]⟩
  have hyr : -(q1 * q2) < 2 * y ∧ 2 * y < q1 * q2 :=
    ⟨by linarith [neg_abs_le y], by linarith [le_abs_self y]⟩
  rcases (show c = 0 ∨ 1 ≤ c ∨ c ≤ -1 from by omega) with rfl | hcp | hcn
  · omega
  · exfalso
    have : q1 * q2 * 1 ≤ q1 * q2 * c := mul_le_mul_of_nonneg_left hcp (le_of_lt hq)
    omega
  · exfalso
    have : q1 * q2 * c ≤ q1 * q2 * (-1) := mul_le_mul_of_nonneg_left hcn (le_of_lt hq)
    omega

/-- **The exactness bound fits.**  `crt.rs` records `ℓ·256·(2¹³−1)·(μ/2) ≤ 25162752` for the
shipped parameter sets; the centred range of `q₁q₂` is `±41296896`, leaving 16134144 to spare. -/
theorem exactness_bound_fits : 2 * 25162752 < q1 * q2 := by norm_num [q1, q2]

/-- **The endpoint theorem, in the form the pipeline uses.**  A coefficient inside the exactness
bound is determined by its two residues: run Garner on them and centre the result. -/
theorem crt_endpoint {a1 a2 t x y : ℤ}
    (h1 : x ≡ a1 [ZMOD q1]) (h2 : x ≡ a2 [ZMOD q2])
    (ht : q1 * t ≡ a2 - a1 [ZMOD q2])
    (hy : y ≡ a1 + q1 * t [ZMOD q1 * q2])
    (hxb : 2 * |x| ≤ 2 * 25162752) (hyb : 2 * |y| < q1 * q2) : y = x := by
  refine crt_unique (hy.trans (garner_congr h1 h2 ht)) hyb ?_
  have := exactness_bound_fits
  omega

/-! ## The Garner combine, as integers

`reduce_invntt`'s second half reconstructs each coefficient from its two residues.  This is the
arithmetic it performs, with the vectors stripped away: canonicalise both residues, solve for the
multiplier `t`, form `a₁ + q₁·t`, and centre it by subtracting `q₁q₂` above the midpoint.

The centring is what makes the truncation to 16 bits right afterwards: the true product lies in
`(−q₁q₂/2, q₁q₂/2]`, so the centred value *is* the coefficient, and its low 16 bits are the
wrapping `u16` the caller wants. -/

/-- **Garner reconstruction is exact.**  `41296896 = ⌊q₁q₂/2⌋` is the code's `CRT_Q_HALF`. -/
theorem garner_value {x r1 r2 a1 a2 t : ℤ}
    (h1 : x ≡ r1 [ZMOD q1]) (h2 : x ≡ r2 [ZMOD q2])
    (ha1 : a1 ≡ r1 [ZMOD q1]) (ha1r : 0 ≤ a1 ∧ a1 < q1)
    (ha2 : a2 ≡ r2 [ZMOD q2]) (ha2r : 0 ≤ a2 ∧ a2 < q2)
    (ht : q1 * t ≡ a2 - a1 [ZMOD q2]) (htr : 0 ≤ t ∧ t < q2)
    (hxb : 2 * |x| < 82593793) :
    (if 41296896 < a1 + q1 * t then a1 + q1 * t - 82593793 else a1 + q1 * t) = x := by
  have hqq : q1 * q2 = 82593793 := by norm_num [q1, q2]
  -- `a₁ + q₁·t` lies in `[0, q₁q₂)`, so the conditional subtraction centres it
  have hlo : 0 ≤ a1 + q1 * t := by
    have : (0 : ℤ) ≤ q1 * t := mul_nonneg (by norm_num [q1]) htr.1
    omega
  have hhi : a1 + q1 * t < 82593793 := by
    have hq1 : (0 : ℤ) < q1 := by norm_num [q1]
    have : q1 * t ≤ q1 * (q2 - 1) := by
      exact mul_le_mul_of_nonneg_left (by omega) (by omega)
    have hq1q2 : q1 * (q2 - 1) = 82593793 - q1 := by norm_num [q1, q2]
    omega
  set y : ℤ := if 41296896 < a1 + q1 * t then a1 + q1 * t - 82593793 else a1 + q1 * t with hy
  have hyb : 2 * |y| < q1 * q2 := by
    rw [hqq, hy]
    split
    · rw [abs_of_nonpos (by omega)]; omega
    · rw [abs_of_nonneg (by omega)]; omega
  refine crt_unique (Int.ModEq.trans ?_ (garner_congr (h1.trans ha1.symm) (h2.trans ha2.symm) ht))
    hyb (by rw [hqq]; exact hxb)
  -- `y` differs from `a₁ + q₁·t` by a multiple of `q₁q₂`
  rw [hy, hqq, Int.modEq_iff_dvd]
  split
  · exact ⟨1, by ring⟩
  · exact ⟨0, by ring⟩

/-! ## Solving for Garner's multiplier

`t = mont_mul(a₂ − a₁, CRT_Q1_INV_MONT, …)` divides by `2¹⁶` on the way through, so the constant
in the table is `q₁⁻¹·2¹⁶ mod q₂` and the `2¹⁶` cancels.  What comes out is `q₁·t ≡ a₂ − a₁`,
which is exactly Garner's condition. -/

/-- The one numeric fact behind `CRT_Q1_INV_MONT`: it is `q₁⁻¹` in Montgomery form. -/
theorem crt_q1_inv_mont_ok : (10753 : ℤ) ∣ (7681 * 3563 - 2 ^ 16) := by decide

/-- **Garner's condition, from the Montgomery multiply.**  `hmm` is what `mont_mul_lane_spec`
hands back. -/
theorem garner_mult {d t : ℤ} (hmm : (10753 : ℤ) ∣ (t * 2 ^ 16 - d * 3563)) :
    (7681 : ℤ) * t ≡ d [ZMOD 10753] := by
  obtain ⟨k, hk⟩ := hmm
  obtain ⟨j, hj⟩ := crt_q1_inv_mont_ok
  -- `2¹⁶·(q₁·t − d) = q₁·(t·2¹⁶ − d·3563) + d·(q₁·3563 − 2¹⁶)`, and `q₂` divides both terms
  have hdvd : (10753 : ℤ) ∣ (2 ^ 16 * (7681 * t - d)) := by
    refine ⟨7681 * k + d * j, ?_⟩
    have e1 : t * 2 ^ 16 - d * 3563 = 10753 * k := hk
    have e2 : (7681 : ℤ) * 3563 - 2 ^ 16 = 10753 * j := hj
    calc (2 : ℤ) ^ 16 * (7681 * t - d)
        = 7681 * (t * 2 ^ 16 - d * 3563) + d * (7681 * 3563 - 2 ^ 16) := by ring
      _ = 7681 * (10753 * k) + d * (10753 * j) := by rw [e1, e2]
      _ = 10753 * (7681 * k + d * j) := by ring
  -- `q₂` is odd, so it can be cancelled from the `2¹⁶`
  have hcop : IsCoprime (10753 : ℤ) (2 ^ 16) := by
    rw [Int.isCoprime_iff_gcd_eq_one]
    decide
  have := (hcop.dvd_of_dvd_mul_left hdvd)
  rw [Int.modEq_iff_dvd, show d - 7681 * t = -(7681 * t - d) from by ring]
  exact dvd_neg.mpr this

end Kopis.Avx2
