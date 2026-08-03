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

end Kopis.Avx2
