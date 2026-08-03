/-
  # Kopis/Avx2/NttZeta.lean — the two ψ tables satisfy the transform algebra (plan phase F4).

  `Kopis/Avx2/NttAlgebra.lean` asks one thing of a twiddle table: `ζ k ² = cst ζ k`, every
  twiddle squaring to its parent's CRT-tree node constant.  This file checks that for
  `ZETAS_Q1` and `ZETAS_Q2`, so the algebra can be instantiated at `q₁ = 7681` and `q₂ = 10753`.

  The stored entries are in Montgomery form — `ZETAS[k] = ψ^brv(k) · 2¹⁶ mod q`, centred — so the
  plain twiddle is the entry times `2⁻¹⁶`, and the check on the raw table is

      ZETAS[2j]²  ≡  ZETAS[j]·R      and      ZETAS[2j+1]²  ≡  −ZETAS[j]·R     (mod q)

  with `R = 2¹⁶ mod q`, plus `ZETAS[1]² ≡ −R²` at the root.  Those are `decide`d over the two
  literal arrays; everything else is the algebraic consequence, and holds for any table that
  passes.
-/
import Kopis.Avx2.NttAlgebra
import Kopis.Avx2.Tables

open Aeneas Aeneas.Std Result
open RustKopisAvx2

namespace Kopis.Avx2

open Kopis.Avx2.NttAlg

set_option maxRecDepth 40000

/-- Table entry `k`, as an integer. -/
def zint (T : Array I16 256#usize) (k : ℕ) : ℤ := (T.val[k]!).val

/-- The plain twiddle: the stored Montgomery entry times `2⁻¹⁶`. -/
def zetaQ {q : ℕ} (T : Array I16 256#usize) (Rinv : ZMod q) (k : ℕ) : ZMod q :=
  ((zint T k : ℤ) : ZMod q) * Rinv

/-! ## The two finite checks -/

/-- The root split: `ζ₁² = −1`, i.e. `ZETAS[1]² ≡ −R²`. -/
def rootOKq (T : Array I16 256#usize) (q R : ℤ) : Bool :=
  (zint T 1 * zint T 1 + R * R) % q == 0

/-- Child twiddles square to their parent's node constant. -/
def treeOKq (T : Array I16 256#usize) (q R : ℤ) : Bool :=
  (List.range 128).all fun j =>
    j == 0 ||
      (((zint T (2 * j) * zint T (2 * j) - zint T j * R) % q == 0) &&
       ((zint T (2 * j + 1) * zint T (2 * j + 1) + zint T j * R) % q == 0))

unseal backend.crt.ZETAS_Q1 in
theorem rootOK_q1 : rootOKq backend.crt.ZETAS_Q1 7681 4088 = true := by decide

unseal backend.crt.ZETAS_Q1 in
theorem treeOK_q1 : treeOKq backend.crt.ZETAS_Q1 7681 4088 = true := by decide

unseal backend.crt.ZETAS_Q2 in
theorem rootOK_q2 : rootOKq backend.crt.ZETAS_Q2 10753 1018 = true := by decide

unseal backend.crt.ZETAS_Q2 in
theorem treeOK_q2 : treeOKq backend.crt.ZETAS_Q2 10753 1018 = true := by decide

/-- The Gentleman-Sande pairing: `ζ_{nb+b} · ζ_{2nb−1−b} = −1`, i.e. `Z_a·Z_b ≡ −R²`. -/
def pairOKq (T : Array I16 256#usize) (q R : ℤ) : Bool :=
  (List.range 8).all fun j =>
    (List.range (2 ^ j)).all fun b =>
      (zint T (2 ^ j + b) * zint T (3 * 2 ^ j - 1 - (2 ^ j + b)) + R * R) % q == 0

unseal backend.crt.ZETAS_Q1 in
theorem pairOK_q1 : pairOKq backend.crt.ZETAS_Q1 7681 4088 = true := by decide

unseal backend.crt.ZETAS_Q2 in
theorem pairOK_q2 : pairOKq backend.crt.ZETAS_Q2 10753 1018 = true := by decide

/-! ## …give the algebra's hypothesis

Everything below is generic: any table passing the two checks satisfies `ζ k ² = cst ζ k`. -/

private theorem cast_zero_of_emod {q : ℕ} {a : ℤ} (h : a % (q : ℤ) = 0) : ((a : ℤ) : ZMod q) = 0 :=
  (ZMod.intCast_zmod_eq_zero_iff_dvd a q).mpr (Int.dvd_of_emod_eq_zero h)

/-- **The table hypothesis of `State_ct`, from the two finite checks.** -/
theorem zetaQ_sq {q : ℕ} (T : Array I16 256#usize) (R : ℤ) (Rinv : ZMod q)
    (hR : ((R : ℤ) : ZMod q) * Rinv = 1)
    (hroot : rootOKq T (q : ℤ) R = true) (htree : treeOKq T (q : ℤ) R = true) :
    ∀ k, 1 ≤ k → k < 256 → zetaQ T Rinv k ^ 2 = cst (zetaQ T Rinv) k := by
  -- the two checks, as equations in `ZMod q`
  have hrootZ : ((zint T 1 : ℤ) : ZMod q) * ((zint T 1 : ℤ) : ZMod q)
      = -(((R : ℤ) : ZMod q) * ((R : ℤ) : ZMod q)) := by
    have := cast_zero_of_emod (q := q) (by simpa [rootOKq] using hroot)
    push_cast at this
    linear_combination this
  have htreeZ : ∀ j, 1 ≤ j → j < 128 →
      ((zint T (2 * j) : ℤ) : ZMod q) * ((zint T (2 * j) : ℤ) : ZMod q)
          = ((zint T j : ℤ) : ZMod q) * ((R : ℤ) : ZMod q) ∧
      ((zint T (2 * j + 1) : ℤ) : ZMod q) * ((zint T (2 * j + 1) : ℤ) : ZMod q)
          = -(((zint T j : ℤ) : ZMod q) * ((R : ℤ) : ZMod q)) := by
    intro j hj1 hj
    have hall := List.all_eq_true.mp htree j (List.mem_range.mpr hj)
    rw [show (j == 0) = false from by simp; omega, Bool.false_or, Bool.and_eq_true] at hall
    constructor
    · have := cast_zero_of_emod (q := q) (by simpa using beq_iff_eq.mp hall.1)
      push_cast at this
      linear_combination this
    · have := cast_zero_of_emod (q := q) (by simpa using beq_iff_eq.mp hall.2)
      push_cast at this
      linear_combination this
  -- and the algebra
  intro k hk1 hk
  rcases (show k = 1 ∨ (∃ j, 1 ≤ j ∧ k = 2 * j) ∨ (∃ j, 1 ≤ j ∧ k = 2 * j + 1) from by
    rcases Nat.even_or_odd k with ⟨j, hj⟩ | ⟨j, hj⟩
    · exact Or.inr (Or.inl ⟨j, by omega, by omega⟩)
    · rcases Nat.eq_or_lt_of_le hk1 with h | h
      · exact Or.inl h.symm
      · exact Or.inr (Or.inr ⟨j, by omega, by omega⟩))
    with rfl | ⟨j, hj1, rfl⟩ | ⟨j, hj1, rfl⟩
  · rw [cst_one, zetaQ]
    calc (((zint T 1 : ℤ) : ZMod q) * Rinv) ^ 2
        = (((zint T 1 : ℤ) : ZMod q) * ((zint T 1 : ℤ) : ZMod q)) * (Rinv * Rinv) := by ring
      _ = -((((R : ℤ) : ZMod q) * Rinv) * (((R : ℤ) : ZMod q) * Rinv)) := by
          rw [hrootZ]; ring
      _ = -1 := by rw [hR]; ring
  · rw [cst_even _ hj1, zetaQ, zetaQ]
    calc (((zint T (2 * j) : ℤ) : ZMod q) * Rinv) ^ 2
        = (((zint T (2 * j) : ℤ) : ZMod q) * ((zint T (2 * j) : ℤ) : ZMod q)) * (Rinv * Rinv) := by
          ring
      _ = (((zint T j : ℤ) : ZMod q) * ((R : ℤ) : ZMod q)) * (Rinv * Rinv) := by
          rw [(htreeZ j hj1 (by omega)).1]
      _ = ((zint T j : ℤ) : ZMod q) * Rinv * ((((R : ℤ) : ZMod q)) * Rinv) := by ring
      _ = ((zint T j : ℤ) : ZMod q) * Rinv := by rw [hR]; ring
  · rw [cst_odd _ hj1, zetaQ, zetaQ]
    calc (((zint T (2 * j + 1) : ℤ) : ZMod q) * Rinv) ^ 2
        = (((zint T (2 * j + 1) : ℤ) : ZMod q) * ((zint T (2 * j + 1) : ℤ) : ZMod q))
            * (Rinv * Rinv) := by ring
      _ = -(((zint T j : ℤ) : ZMod q) * ((R : ℤ) : ZMod q)) * (Rinv * Rinv) := by
          rw [(htreeZ j hj1 (by omega)).2]
      _ = -(((zint T j : ℤ) : ZMod q) * Rinv * ((((R : ℤ) : ZMod q)) * Rinv)) := by ring
      _ = -(((zint T j : ℤ) : ZMod q) * Rinv) := by rw [hR]; ring

/-- **The Gentleman-Sande hypothesis, from the finite check.** -/
theorem zetaQ_pair {q : ℕ} (T : Array I16 256#usize) (R : ℤ) (Rinv : ZMod q)
    (hR : ((R : ℤ) : ZMod q) * Rinv = 1) (hpair : pairOKq T (q : ℤ) R = true) :
    ∀ nb b : ℕ, (∃ j, j < 8 ∧ nb = 2 ^ j) → b < nb →
      zetaQ T Rinv (nb + b) * zetaQ T Rinv (2 * nb - 1 - b) = -1 := by
  rintro nb b ⟨j, hj, rfl⟩ hb
  have hall := List.all_eq_true.mp hpair j (List.mem_range.mpr hj)
  have hb' := List.all_eq_true.mp hall b (List.mem_range.mpr hb)
  have hz := cast_zero_of_emod (q := q) (by simpa using beq_iff_eq.mp hb')
  push_cast at hz
  rw [show 3 * 2 ^ j - 1 - (2 ^ j + b) = 2 * 2 ^ j - 1 - b from by omega] at hz
  have hmul : ((zint T (2 ^ j + b) : ℤ) : ZMod q) * ((zint T (2 * 2 ^ j - 1 - b) : ℤ) : ZMod q)
      = -(((R : ℤ) : ZMod q) * ((R : ℤ) : ZMod q)) := by linear_combination hz
  unfold zetaQ
  calc (((zint T (2 ^ j + b) : ℤ) : ZMod q) * Rinv)
        * (((zint T (2 * 2 ^ j - 1 - b) : ℤ) : ZMod q) * Rinv)
      = (((zint T (2 ^ j + b) : ℤ) : ZMod q) * ((zint T (2 * 2 ^ j - 1 - b) : ℤ) : ZMod q))
          * (Rinv * Rinv) := by ring
    _ = -((((R : ℤ) : ZMod q) * Rinv) * (((R : ℤ) : ZMod q) * Rinv)) := by rw [hmul]; ring
    _ = -1 := by rw [hR]; ring

/-! ## …instantiated at the two primes -/

/-- The plain `q₁` twiddles. -/
def zeta1 : ℕ → ZMod 7681 := zetaQ backend.crt.ZETAS_Q1 (900 : ZMod 7681)
/-- The plain `q₂` twiddles. -/
def zeta2 : ℕ → ZMod 10753 := zetaQ backend.crt.ZETAS_Q2 (1764 : ZMod 10753)

theorem zeta1_sq : ∀ k, 1 ≤ k → k < 256 → zeta1 k ^ 2 = cst zeta1 k :=
  zetaQ_sq backend.crt.ZETAS_Q1 4088 (900 : ZMod 7681) (by decide) rootOK_q1 treeOK_q1

theorem zeta2_sq : ∀ k, 1 ≤ k → k < 256 → zeta2 k ^ 2 = cst zeta2 k :=
  zetaQ_sq backend.crt.ZETAS_Q2 1018 (1764 : ZMod 10753) (by decide) rootOK_q2 treeOK_q2

/-! ## …so the transform algebra applies at both primes

`State_ct` refines the CRT invariant by one Cooley-Tukey layer, and `State_leaf_mul` says that
once the leaf state is reached, multiplying lanewise multiplies the polynomials.  Those are the
two facts phase F4 needs about each prime; everything else is about the code. -/

theorem zeta1_pair : ∀ nb b : ℕ, (∃ j, j < 8 ∧ nb = 2 ^ j) → b < nb →
    zeta1 (nb + b) * zeta1 (2 * nb - 1 - b) = -1 :=
  zetaQ_pair backend.crt.ZETAS_Q1 4088 (900 : ZMod 7681) (by decide) pairOK_q1

theorem zeta2_pair : ∀ nb b : ℕ, (∃ j, j < 8 ∧ nb = 2 ^ j) → b < nb →
    zeta2 (nb + b) * zeta2 (2 * nb - 1 - b) = -1 :=
  zetaQ_pair backend.crt.ZETAS_Q2 1018 (1764 : ZMod 10753) (by decide) pairOK_q2

/-- One GS layer, at `q₁`. -/
theorem State_gs_q1 {nb m' : ℕ} (hnb1 : 1 ≤ nb) (hnb : 2 * nb ≤ 256)
    (hpow : ∃ j, j < 8 ∧ nb = 2 ^ j) {c : ZMod 7681} {f a a' : ℕ → ZMod 7681}
    (hst : State zeta1 (2 * nb) m' c f a)
    (hbut : ∀ b < nb, ∀ r < m',
      a' (b * (2 * m') + r) = a (b * (2 * m') + r) + a (b * (2 * m') + m' + r) ∧
      a' (b * (2 * m') + m' + r)
        = (-(zeta1 (2 * nb - 1 - b))) * (a (b * (2 * m') + r) - a (b * (2 * m') + m' + r))) :
    State zeta1 nb (2 * m') (2 * c) f a' :=
  State_gs zeta1_sq zeta1_pair hnb1 hnb hpow hst hbut

/-- One GS layer, at `q₂`. -/
theorem State_gs_q2 {nb m' : ℕ} (hnb1 : 1 ≤ nb) (hnb : 2 * nb ≤ 256)
    (hpow : ∃ j, j < 8 ∧ nb = 2 ^ j) {c : ZMod 10753} {f a a' : ℕ → ZMod 10753}
    (hst : State zeta2 (2 * nb) m' c f a)
    (hbut : ∀ b < nb, ∀ r < m',
      a' (b * (2 * m') + r) = a (b * (2 * m') + r) + a (b * (2 * m') + m' + r) ∧
      a' (b * (2 * m') + m' + r)
        = (-(zeta2 (2 * nb - 1 - b))) * (a (b * (2 * m') + r) - a (b * (2 * m') + m' + r))) :
    State zeta2 nb (2 * m') (2 * c) f a' :=
  State_gs zeta2_sq zeta2_pair hnb1 hnb hpow hst hbut

/-- One CT layer, at `q₁`. -/
theorem State_ct_q1 {nb m' : ℕ} (hnb1 : 1 ≤ nb) (hnb : 2 * nb ≤ 256)
    {c : ZMod 7681} {f a a' : ℕ → ZMod 7681}
    (hst : State zeta1 nb (2 * m') c f a)
    (hbut : ∀ b < nb, ∀ r < m',
      a' (b * (2 * m') + r) = a (b * (2 * m') + r) + zeta1 (nb + b) * a (b * (2 * m') + m' + r) ∧
      a' (b * (2 * m') + m' + r)
        = a (b * (2 * m') + r) - zeta1 (nb + b) * a (b * (2 * m') + m' + r)) :
    State zeta1 (2 * nb) m' c f a' :=
  State_ct zeta1_sq hnb1 hnb hst hbut

/-- One CT layer, at `q₂`. -/
theorem State_ct_q2 {nb m' : ℕ} (hnb1 : 1 ≤ nb) (hnb : 2 * nb ≤ 256)
    {c : ZMod 10753} {f a a' : ℕ → ZMod 10753}
    (hst : State zeta2 nb (2 * m') c f a)
    (hbut : ∀ b < nb, ∀ r < m',
      a' (b * (2 * m') + r) = a (b * (2 * m') + r) + zeta2 (nb + b) * a (b * (2 * m') + m' + r) ∧
      a' (b * (2 * m') + m' + r)
        = a (b * (2 * m') + r) - zeta2 (nb + b) * a (b * (2 * m') + m' + r)) :
    State zeta2 (2 * nb) m' c f a' :=
  State_ct zeta2_sq hnb1 hnb hst hbut

/-- **Lanewise product = negacyclic product, at `q₁`.** -/
theorem State_leaf_mul_q1 {f g a b : ℕ → ZMod 7681}
    (ha : State zeta1 256 1 1 f a) (hb : State zeta1 256 1 1 g b) :
    State zeta1 256 1 1 (nconv f g) (fun n => a n * b n) :=
  State_leaf_mul zeta1_sq ha hb

/-- **Lanewise product = negacyclic product, at `q₂`.** -/
theorem State_leaf_mul_q2 {f g a b : ℕ → ZMod 10753}
    (ha : State zeta2 256 1 1 f a) (hb : State zeta2 256 1 1 g b) :
    State zeta2 256 1 1 (nconv f g) (fun n => a n * b n) :=
  State_leaf_mul zeta2_sq ha hb

end Kopis.Avx2
