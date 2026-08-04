/-
  # Kopis/CrtZeta.lean — a ψ table satisfies the transform algebra, for any table.

  `Kopis/Avx2/NttAlgebra.lean` asks one thing of a twiddle table: `ζ k ² = cst ζ k`, every twiddle
  squaring to its parent's CRT-tree node constant, plus the pairing `ζ_{nb+b}·ζ_{2nb−1−b} = −1`
  that the Gentleman-Sande direction needs.  This file reduces both to *finite checks on the raw
  table*, which each backend then discharges by `decide` on its own extracted arrays.

  The stored entries are in Montgomery form — `ZETAS[k] = ψ^brv(k) · 2¹⁶ mod q`, centred — so the
  plain twiddle is the entry times `2⁻¹⁶`, and the check on the raw table is

      ZETAS[2j]²  ≡  ZETAS[j]·R      and      ZETAS[2j+1]²  ≡  −ZETAS[j]·R     (mod q)

  with `R = 2¹⁶ mod q`, plus `ZETAS[1]² ≡ −R²` at the root.  Everything here is the algebraic
  consequence, and holds for any table that passes.

  Nothing in this file mentions either extraction: `Array I16 256#usize` is an aeneas type, not a
  backend one, so the same lemmas serve `RustKopisSerial.backend.crt.ZETAS_Q1` and its AVX2 twin.
  That is the point — since the portable transform moved to two primes the two backends run the
  *same* tables, and only the `decide`s that pin them down have to be done once per extraction.
-/
import Kopis.Avx2.NttAlgebra
import Aeneas

open Aeneas Aeneas.Std Result

namespace Kopis.CrtZeta

open Kopis.Avx2.NttAlg

set_option maxRecDepth 40000

/-- Table entry `k`, as an integer. -/
def zint (T : Array I16 256#usize) (k : ℕ) : ℤ := (T.val[k]!).val

/-- The plain twiddle: the stored Montgomery entry times `2⁻¹⁶`. -/
def zetaQ {q : ℕ} (T : Array I16 256#usize) (Rinv : ZMod q) (k : ℕ) : ZMod q :=
  ((zint T k : ℤ) : ZMod q) * Rinv

/-! ## The finite checks -/

/-- The root split: `ζ₁² = −1`, i.e. `ZETAS[1]² ≡ −R²`. -/
def rootOKq (T : Array I16 256#usize) (q R : ℤ) : Bool :=
  (zint T 1 * zint T 1 + R * R) % q == 0

/-- Child twiddles square to their parent's node constant. -/
def treeOKq (T : Array I16 256#usize) (q R : ℤ) : Bool :=
  (List.range 128).all fun j =>
    j == 0 ||
      (((zint T (2 * j) * zint T (2 * j) - zint T j * R) % q == 0) &&
       ((zint T (2 * j + 1) * zint T (2 * j + 1) + zint T j * R) % q == 0))

/-- The Gentleman-Sande pairing: `ζ_{nb+b} · ζ_{2nb−1−b} = −1`, i.e. `Z_a·Z_b ≡ −R²`. -/
def pairOKq (T : Array I16 256#usize) (q R : ℤ) : Bool :=
  (List.range 8).all fun j =>
    (List.range (2 ^ j)).all fun b =>
      (zint T (2 ^ j + b) * zint T (3 * 2 ^ j - 1 - (2 ^ j + b)) + R * R) % q == 0

/-! ## …give the algebra's hypotheses

Everything below is generic: any table passing the checks satisfies them. -/

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

end Kopis.CrtZeta
