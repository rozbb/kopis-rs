/-
  # Kopis/Avx2/NttZeta.lean — the two ψ tables satisfy the transform algebra (plan phase F4).

  `Kopis/CrtZeta.lean` reduces the algebra's hypothesis on a twiddle table — `ζ k ² = cst ζ k`,
  plus the Gentleman-Sande pairing — to finite checks on the raw table.  This file discharges
  those checks by `decide` over `ZETAS_Q1` and `ZETAS_Q2` as the AVX2 extraction holds them, and
  instantiates the algebra at `q₁ = 7681` and `q₂ = 10753`.

  The portable backend does exactly the same over its own extraction of the same two arrays; see
  `Kopis/Properties/NttCrtZeta.lean`.  Only the `decide`s are repeated — the algebra is shared.
-/
import Kopis.Avx2.NttAlgebra
import Kopis.Avx2.Tables
import Kopis.CrtZeta

open Aeneas Aeneas.Std Result
open RustKopisAvx2

namespace Kopis.Avx2

open Kopis.Avx2.NttAlg Kopis.CrtZeta

set_option maxRecDepth 40000

/-! ## The finite checks, on this extraction's tables -/

unseal backend.crt.ZETAS_Q1 in
theorem rootOK_q1 : rootOKq backend.crt.ZETAS_Q1 7681 4088 = true := by decide

unseal backend.crt.ZETAS_Q1 in
theorem treeOK_q1 : treeOKq backend.crt.ZETAS_Q1 7681 4088 = true := by decide

unseal backend.crt.ZETAS_Q2 in
theorem rootOK_q2 : rootOKq backend.crt.ZETAS_Q2 10753 1018 = true := by decide

unseal backend.crt.ZETAS_Q2 in
theorem treeOK_q2 : treeOKq backend.crt.ZETAS_Q2 10753 1018 = true := by decide

unseal backend.crt.ZETAS_Q1 in
theorem pairOK_q1 : pairOKq backend.crt.ZETAS_Q1 7681 4088 = true := by decide

unseal backend.crt.ZETAS_Q2 in
theorem pairOK_q2 : pairOKq backend.crt.ZETAS_Q2 10753 1018 = true := by decide

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
