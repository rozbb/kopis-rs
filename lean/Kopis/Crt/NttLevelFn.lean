/-
  # Kopis/Crt/NttLevelFn.lean — one transform layer, written as a function of the view.

  `Kopis/Crt/NttAlgebra.lean`'s `State_ct` and `State_gs` each take an `hbut` hypothesis: a
  description of what the layer does to *every* index pair.  A loop's postcondition, though, wants
  to name the layer's result at a single index `c`, without knowing which pair `c` belongs to.
  `ctLvl` and `gsLvl` are that naming, and `ctLvl_hbut` / `gsLvl_hbut` are the bridge back.

  Nothing here mentions a register width, an extraction or an instruction — it is `ZMod q`
  arithmetic and `Nat` division — so it is shared, on the same test `Kopis/Crt/Scheme.lean` and
  `Kopis/Crt/NttAlgebra.lean` already pass.

  `Kopis/Avx2/NttWalk.lean` still carries its own copies of these four declarations, from before
  this file existed; they are character-for-character the same and should be replaced by an
  `export` the next time that file is touched.
-/
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Ring
import Kopis.Crt.NttAlgebra

namespace Kopis.CrtScheme.LevelFn

/-! ## One Cooley-Tukey layer -/

/-- The result of one Cooley-Tukey layer at `nb` blocks of size `2m'`. -/
noncomputable def ctLvl (q : ℕ) (ψ : ℕ → ZMod q) (nb m' : ℕ) (a : ℕ → ZMod q) (c : ℕ) : ZMod q :=
  if c % (2 * m') < m' then a c + ψ (nb + c / (2 * m')) * a (c + m')
  else a (c - m') - ψ (nb + c / (2 * m')) * a c

theorem ctLvl_hbut (q : ℕ) (ψ : ℕ → ZMod q) (nb m' : ℕ) (a : ℕ → ZMod q) (hm' : 0 < m') :
    ∀ b < nb, ∀ r < m',
      ctLvl q ψ nb m' a (b * (2 * m') + r)
          = a (b * (2 * m') + r) + ψ (nb + b) * a (b * (2 * m') + m' + r) ∧
      ctLvl q ψ nb m' a (b * (2 * m') + m' + r)
          = a (b * (2 * m') + r) - ψ (nb + b) * a (b * (2 * m') + m' + r) := by
  intro b hb r hr
  have hre : ∀ t, t < 2 * m' → (b * (2 * m') + t) % (2 * m') = t ∧
      (b * (2 * m') + t) / (2 * m') = b := by
    intro t ht
    constructor
    · rw [show b * (2 * m') + t = t + (2 * m') * b from by ring, Nat.add_mul_mod_self_left,
        Nat.mod_eq_of_lt ht]
    · rw [show b * (2 * m') + t = t + (2 * m') * b from by ring,
        Nat.add_mul_div_left _ _ (by omega), Nat.div_eq_of_lt ht, Nat.zero_add]
  obtain ⟨hm1, hd1⟩ := hre r (by omega)
  obtain ⟨hm2, hd2⟩ := hre (m' + r) (by omega)
  constructor
  · rw [ctLvl, hm1, if_pos hr, hd1,
      show b * (2 * m') + r + m' = b * (2 * m') + m' + r from by ring]
  · rw [ctLvl, show b * (2 * m') + m' + r = b * (2 * m') + (m' + r) from by ring, hm2,
      if_neg (by omega), hd2,
      show b * (2 * m') + (m' + r) - m' = b * (2 * m') + r from by omega]

/-! ## One Gentleman-Sande layer

The mirror of `ctLvl`.  The negation `State_gs` asks for is written into the definition, because
the inverse side's tables carry it: the code's `z` at the paired index *is* `−ζ`. -/

/-- The result of one Gentleman-Sande layer merging `2·nb` blocks of size `m'` into `nb`. -/
noncomputable def gsLvl (q : ℕ) (ζ : ℕ → ZMod q) (nb m' : ℕ) (a : ℕ → ZMod q) (c : ℕ) : ZMod q :=
  if c % (2 * m') < m' then a c + a (c + m')
  else (-(ζ (2 * nb - 1 - c / (2 * m')))) * (a (c - m') - a c)

theorem gsLvl_hbut (q : ℕ) (ζ : ℕ → ZMod q) (nb m' : ℕ) (a : ℕ → ZMod q) (hm' : 0 < m') :
    ∀ b < nb, ∀ r < m',
      gsLvl q ζ nb m' a (b * (2 * m') + r)
          = a (b * (2 * m') + r) + a (b * (2 * m') + m' + r) ∧
      gsLvl q ζ nb m' a (b * (2 * m') + m' + r)
          = (-(ζ (2 * nb - 1 - b)))
              * (a (b * (2 * m') + r) - a (b * (2 * m') + m' + r)) := by
  intro b hb r hr
  have hre : ∀ t, t < 2 * m' → (b * (2 * m') + t) % (2 * m') = t ∧
      (b * (2 * m') + t) / (2 * m') = b := by
    intro t ht
    constructor
    · rw [show b * (2 * m') + t = t + (2 * m') * b from by ring, Nat.add_mul_mod_self_left,
        Nat.mod_eq_of_lt ht]
    · rw [show b * (2 * m') + t = t + (2 * m') * b from by ring,
        Nat.add_mul_div_left _ _ (by omega), Nat.div_eq_of_lt ht, Nat.zero_add]
  obtain ⟨hm1, hd1⟩ := hre r (by omega)
  obtain ⟨hm2, hd2⟩ := hre (m' + r) (by omega)
  constructor
  · rw [gsLvl, hm1, if_pos hr,
      show b * (2 * m') + r + m' = b * (2 * m') + m' + r from by ring]
  · rw [gsLvl, show b * (2 * m') + m' + r = b * (2 * m') + (m' + r) from by ring, hm2,
      if_neg (by omega), hd2,
      show b * (2 * m') + (m' + r) - m' = b * (2 * m') + r from by omega]

/-! ## Leaf states compose

`State` at `nb = 256, m = 1` says `a b = c · Σ f(q)·cst(256+b)^q`, which is linear in `(f, a)`
jointly and scales in `c`.  Both facts are needed to turn a *sum of pointwise products* into a
single leaf state: `State_leaf_mul` handles one product, these three handle the sum and the
Montgomery factor the reduction introduces.

Nothing here mentions an extraction, so it is shared.  `Kopis/Avx2/Reduce.lean` still carries its
own copies from before this file existed. -/

open Kopis.CrtScheme.NttAlg in
theorem State_add {q : ℕ} {ζ : ℕ → ZMod q} {c : ZMod q} {f g a b : ℕ → ZMod q}
    (hf : State ζ 256 1 c f a) (hg : State ζ 256 1 c g b) :
    State ζ 256 1 c (fun n => f n + g n) (fun n => a n + b n) := by
  intro n hn r hr
  show a (n * 1 + r) + b (n * 1 + r)
    = c * ∑ i ∈ Finset.range 256, (f (i * 1 + r) + g (i * 1 + r)) * cst ζ (256 + n) ^ i
  rw [hf n hn r hr, hg n hn r hr, ← mul_add, ← Finset.sum_add_distrib]
  congr 1
  exact Finset.sum_congr rfl fun i _ => by ring

open Kopis.CrtScheme.NttAlg in
theorem State_scale {q : ℕ} {ζ : ℕ → ZMod q} {c k : ZMod q} {f a : ℕ → ZMod q}
    (h : State ζ 256 1 c f a) :
    State ζ 256 1 (k * c) f (fun n => k * a n) := by
  intro n hn r hr
  show k * a (n * 1 + r) = _
  rw [h n hn r hr, mul_assoc]

open Kopis.CrtScheme.NttAlg in
/-- A finite sum of leaf states is a leaf state. -/
theorem State_sum {q : ℕ} {ζ : ℕ → ZMod q} {N : ℕ} {F A : ℕ → ℕ → ZMod q}
    (h : ∀ jj < N, State ζ 256 1 1 (F jj) (A jj)) :
    State ζ 256 1 1 (fun n => ∑ jj ∈ Finset.range N, F jj n)
      (fun n => ∑ jj ∈ Finset.range N, A jj n) := by
  intro n hn r hr
  show (∑ jj ∈ Finset.range N, A jj (n * 1 + r))
    = 1 * ∑ i ∈ Finset.range 256,
        (∑ jj ∈ Finset.range N, F jj (i * 1 + r)) * cst ζ (256 + n) ^ i
  have hj : ∀ jj ∈ Finset.range N, A jj (n * 1 + r)
      = 1 * ∑ i ∈ Finset.range 256, F jj (i * 1 + r) * cst ζ (256 + n) ^ i :=
    fun jj hjj => h jj (Finset.mem_range.mp hjj) n hn r hr
  rw [Finset.sum_congr rfl hj]
  simp only [one_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => (Finset.sum_mul _ _ _).symm

end Kopis.CrtScheme.LevelFn
