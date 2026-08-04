/-
  # Kopis/CrtConv.lean — the negacyclic convolution as a single sum.

  `Kopis/Avx2/NttAlgebra.lean`'s `nconv` is a double sum, which is the shape the evaluation
  homomorphism produces.  For everything downstream — the exactness bound over ℤ, and reading the
  same convolution in `ZMod q₁`, `ZMod q₂` and `ZMod 2¹⁶` — the *single* sum below is what is
  wanted: the partner index is forced, so one of the two loops collapses.

  `nconvR` is stated over an arbitrary commutative ring on purpose.  The proof has to compare the
  same convolution in four different rings, and doing that through one definition plus a transport
  lemma is what keeps it from being four separate derivations.  Nothing here mentions a modulus.
-/
import Kopis.Avx2.NttAlgebra

namespace Kopis.CrtConv

open Kopis.Avx2.NttAlg
open scoped BigOperators

/-- The negacyclic convolution, as a single 256-term sum. -/
def nconvR {R : Type*} [CommRing R] (F G : ℕ → R) (n : ℕ) : R :=
  ∑ i ∈ Finset.range 256, F i * (if i ≤ n then G (n - i) else -(G (n + 256 - i)))

/-- The double sum of `nconv` collapses to the single sum of `nconvR`. -/
theorem nconv_eq_nconvR {K : Type*} [CommRing K] (f g : ℕ → K) (n : ℕ) (hn : n < 256) :
    nconv f g n = nconvR f g n := by
  unfold nconv nconvR
  refine Finset.sum_congr rfl (fun i hi => ?_)
  have hi' : i < 256 := Finset.mem_range.mp hi
  by_cases hle : i ≤ n
  · rw [if_pos hle, Finset.sum_eq_single (n - i)]
    · rw [if_pos (by omega)]
    · intro j hj hne
      have hj' : j < 256 := Finset.mem_range.mp hj
      rw [if_neg (by omega), if_neg (by omega)]
    · intro h; exact absurd (Finset.mem_range.mpr (by omega : n - i < 256)) h
  · rw [if_neg hle, Finset.sum_eq_single (n + 256 - i)]
    · rw [if_neg (by omega), if_pos (by omega)]; ring
    · intro j hj hne
      have hj' : j < 256 := Finset.mem_range.mp hj
      rw [if_neg (by omega), if_neg (by omega)]
    · intro h; exact absurd (Finset.mem_range.mpr (by omega : n + 256 - i < 256)) h

/-- `nconvR` at `n < 256` reads its arguments only at indices below 256. -/
theorem nconvR_congr {R : Type*} [CommRing R] {F F' G G' : ℕ → R} {n : ℕ} (hn : n < 256)
    (hF : ∀ i, i < 256 → F i = F' i) (hG : ∀ j, j < 256 → G j = G' j) :
    nconvR F G n = nconvR F' G' n := by
  unfold nconvR
  refine Finset.sum_congr rfl (fun i hi => ?_)
  have hi' : i < 256 := Finset.mem_range.mp hi
  rw [hF i hi']
  congr 1
  split_ifs with hle
  · exact hG _ (by omega)
  · rw [hG _ (by omega)]

/-- The integer convolution casts into any commutative ring coefficientwise.  This is the bridge
between the exactness bound (over `ℤ`) and the three quotients the proof works in. -/
theorem nconvR_intCast {R : Type*} [CommRing R] (F G : ℕ → ℤ) (n : ℕ) :
    ((nconvR F G n : ℤ) : R)
      = nconvR (fun i => ((F i : ℤ) : R)) (fun j => ((G j : ℤ) : R)) n := by
  unfold nconvR
  rw [Int.cast_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Int.cast_mul]
  congr 1
  split_ifs
  · rfl
  · rw [Int.cast_neg]

/-- **The exactness bound.**  With both operands bounded, the convolution is bounded by
`256·bF·bG` — which `fitsExactly` keeps inside the centred range of `q₁q₂`. -/
theorem abs_nconvR_le {F G : ℕ → ℤ} {bF bG : ℤ} {n : ℕ} (hn : n < 256)
    (hF : ∀ i, i < 256 → |F i| ≤ bF) (hG : ∀ j, j < 256 → |G j| ≤ bG) :
    |nconvR F G n| ≤ 256 * bF * bG := by
  have hbF : 0 ≤ bF := le_trans (abs_nonneg _) (hF 0 (by omega))
  have hterm : ∀ i ∈ Finset.range 256,
      |F i * (if i ≤ n then G (n - i) else -(G (n + 256 - i)))| ≤ bF * bG := by
    intro i hi
    have hi' : i < 256 := Finset.mem_range.mp hi
    rw [abs_mul]
    refine mul_le_mul (hF i hi') ?_ (abs_nonneg _) hbF
    split_ifs with h
    · exact hG _ (by omega)
    · rw [abs_neg]; exact hG _ (by omega)
  calc |nconvR F G n| ≤ ∑ i ∈ Finset.range 256,
        |F i * (if i ≤ n then G (n - i) else -(G (n + 256 - i)))| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i ∈ Finset.range 256, bF * bG := Finset.sum_le_sum hterm
    _ = 256 * bF * bG := by rw [Finset.sum_const, Finset.card_range]; ring

end Kopis.CrtConv
