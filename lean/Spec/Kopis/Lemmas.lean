import Spec.Kopis.Spec

/-! # Facts about the Kopis spec's helpers

`Spec.lean` defines `serialize_elem`, `deserialize_elem`, `bit_slices` and `hamming` in the
markdown's terms. The lemmas here restate them in terms of `bytesToBits` and single bits, which
is the form the correspondence proofs use. -/

namespace Spec.Kopis

open scoped BigOperators

/-- The constant polynomial `c`, i.e. `make_rn([c; 256])`, but at any modulus. -/
def Poly.const (m : ℕ) (c : ZMod m) : Poly m := Vector.replicate 256 c

theorem make_rn_replicate (n : ℕ) (c : ZMod (2 ^ n)) :
    make_rn n (Vector.replicate 256 c) = Poly.const (2 ^ n) c := rfl

/-- Bit `j` of `∑ᵢ bᵢ·2ⁱ` is `bⱼ`. -/
theorem testBit_bitSum : ∀ (k : ℕ) (b : Fin k → Bool) (j : ℕ) (hj : j < k),
    (∑ i : Fin k, (b i).toNat * 2 ^ i.val).testBit j = b ⟨j, hj⟩
  | 0, _, _, hj => absurd hj (Nat.not_lt_zero _)
  | k + 1, b, j, hj => by
    rw [Fin.sum_univ_succ]
    have hs : ∑ i : Fin k, (b i.succ).toNat * 2 ^ (i.succ : ℕ)
        = 2 * ∑ i : Fin k, (b i.succ).toNat * 2 ^ i.val := by
      rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun i _ => ?_
      simp only [Fin.val_succ, pow_succ]; ring
    rw [hs]
    rcases j with _ | j
    · cases h : b 0 <;> simp [h, Nat.testBit_zero, Nat.add_mul_mod_self_left]
    · rw [Nat.testBit_add_one, show ((b 0).toNat * 2 ^ (0 : Fin (k + 1)).val
          + 2 * ∑ i : Fin k, (b i.succ).toNat * 2 ^ i.val) / 2
          = ∑ i : Fin k, (b i.succ).toNat * 2 ^ i.val by
        have : (b 0).toNat < 2 := by cases b 0 <;> decide
        simp only [Fin.val_zero, pow_zero, mul_one]; omega]
      exact testBit_bitSum k _ j (by omega)

theorem testBit_from_bits_le (k : ℕ) (v : Vector Bool k) (j : ℕ) (hj : j < k) :
    (from_bits_le k v).testBit j = v[j] :=
  testBit_bitSum k (fun i => v[i]) j hj

/-- The spec's byte-to-bit loop is `bytesToBits`. -/
theorem flatten_to_bits_le {k : ℕ} (B : 𝔹 k) :
    (Vector.ofFn fun i : Fin k => to_bits_le 8 B[i].toNat).flatten
      = (bytesToBits B).cast (Nat.mul_comm 8 k) := by
  apply Vector.ext; intro p hp
  simp [to_bits_le, bytesToBits]

/-- Bit `j` of byte `p` of `serialize_elem n r` is bit `(8p+j) mod n` of coefficient
`(8p+j)/n`. -/
theorem serialize_elem_testBit (n : ℕ) (r : R n) (p j : ℕ)
    (hp : p < 32 * n) (hj : j < 8) (hn : 0 < n) :
    ((serialize_elem n r)[p]'hp).toNat.testBit j
      = (r[(8 * p + j) / n]'(by rw [Nat.div_lt_iff_lt_mul hn]; omega)).val.testBit
          ((8 * p + j) % n) := by
  simp only [serialize_elem, Vector.getElem_ofFn]
  rw [BitVec.natCast_eq_ofNat, BitVec.toNat_ofNat, Nat.testBit_mod_two_pow, decide_eq_true hj, Bool.true_and,
    testBit_from_bits_le _ _ j hj]
  simp [slice, canonical_coeffs, to_bits_le]

/-- Coefficient `i` of `deserialize_elem n B` is bits `n·i .. n·i+n` of `B`. -/
theorem deserialize_elem_getElem (n : ℕ) (B : 𝔹 (32 * n)) (i : ℕ) (hi : i < 256) :
    (deserialize_elem n B)[i]
      = ((∑ j : Fin n, ((bytesToBits B)[n * i + j.val]'(by
          have := chunk_bound (n := n) hi; have := j.isLt; omega)).toNat * 2 ^ j.val : ℕ)
          : ZMod (2 ^ n)) := by
  simp [deserialize_elem, make_rn, from_bits_le, slice, to_bits_le, bytesToBits]

theorem bit_slices_getElem (μ : ℕ) (B : 𝔹 (32 * μ)) (i : ℕ) (hi : i < 512) (j : ℕ)
    (hj : j < μ / 2) :
    (bit_slices μ B)[i][j] = (bytesToBits B)[i * μ / 2 + j]'(by
      have := Nat.mul_le_mul_right μ (Nat.succ_le_of_lt hi); rw [Nat.succ_mul] at this; omega) := by
  simp only [bit_slices, Vector.getElem_ofFn, slice, flatten_to_bits_le, Vector.getElem_cast]

/-- `hamming(vals[2*k])` in `GenSecret` counts bits `μ·k .. μ·k + μ/2`. -/
theorem hamming_bit_slices_even (μ : ℕ) (B : 𝔹 (32 * μ)) (k : ℕ) (hk : k < 256) :
    hamming (bit_slices μ B)[2 * k] = ∑ j : Fin (μ / 2), ((bytesToBits B)[μ * k + j.val]'(by
      have := chunk_bound (n := μ) hk; have := j.isLt; omega)).toNat := by
  have h : 2 * k * μ / 2 = μ * k := by
    rw [Nat.mul_assoc, Nat.mul_div_cancel_left _ (by decide), Nat.mul_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Fin.getElem_fin, bit_slices_getElem _ _ _ (by omega) _ j.isLt]
  simp only [h]

/-- `hamming(vals[2*k+1])` in `GenSecret` counts bits `μ·k + μ/2 .. μ·k + 2·(μ/2)`. -/
theorem hamming_bit_slices_odd (μ : ℕ) (B : 𝔹 (32 * μ)) (k : ℕ) (hk : k < 256) :
    hamming (bit_slices μ B)[2 * k + 1] = ∑ j : Fin (μ / 2),
      ((bytesToBits B)[μ * k + μ / 2 + j.val]'(by
        have := chunk_bound (n := μ) hk; have := j.isLt; omega)).toNat := by
  have h : (2 * k + 1) * μ / 2 = μ * k + μ / 2 := by
    rw [show (2 * k + 1) * μ = 2 * (μ * k) + μ by ring]; omega
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Fin.getElem_fin, bit_slices_getElem _ _ _ (by omega) _ j.isLt]
  simp only [h]

/-! ## Coefficients of `Poly.mul` -/

/-- Indexed-invariant evaluator for an `Id.run` `forIn'` loop over a `List` (replicated
locally from the `Serialize` module). -/
private theorem forIn'_getElem_indexed {α : Type} {β : Type} {m : Nat} :
    ∀ (xs : List α) (init : Vector β m)
    (body : (a : α) → a ∈ xs → Vector β m → Id (ForInStep (Vector β m)))
    (i : Nat) (hi : i < m) (val : β)
    (P : Nat → Vector β m → Prop)
    (hInit : P 0 init)
    (hFinal : ∀ dw, P xs.length dw → dw[i] = val)
    (_hStep : ∀ (k : Nat) (hk : k < xs.length) b, P k b →
      ∀ a (ha : a ∈ xs), a = xs[k]'hk →
      ∃ b', body a ha b = pure (ForInStep.yield b') ∧ P (k + 1) b'),
    (Id.run (forIn' xs init body))[i] = val := by
  intro xs; induction xs with
  | nil => intro init body i hi val P hInit hFinal _hStep; exact hFinal init hInit
  | cons x xs ih =>
    intro init body i hi val P hInit hFinal hStep
    simp only [List.forIn'_cons, Id.run, Bind.bind]
    obtain ⟨b', hb'_eq, hb'_P⟩ := hStep 0 (Nat.zero_lt_succ _) init hInit x (.head _) rfl
    conv_lhs => arg 1; rw [hb'_eq]
    exact ih b' (fun a' mm b => body a' (.tail _ mm) b) i hi val (fun k => P (k + 1))
      hb'_P
      (fun dw hP => hFinal dw (by rwa [List.length_cons]))
      (fun k hk b hPk a ha heq => by
        have hk' : k + 1 < (x :: xs).length := by simp; omega
        exact hStep (k + 1) hk' b hPk a (.tail _ ha) (by simp [heq]))

variable {m : ℕ}

/-- Contribution of the term `aᵢ·bⱼ` to output coefficient `p` in the negacyclic product. -/
def convContrib (a b : Poly m) (i j p : ℕ) : ZMod m :=
  if (i + j) % 256 = p then (if i + j < 256 then a[i]! * b[j]! else -(a[i]! * b[j]!)) else 0

/-- Closed form of coefficient `p` of the negacyclic product. -/
def convCoeff (a b : Poly m) (p : ℕ) : ZMod m :=
  ∑ i ∈ Finset.range 256, ∑ j ∈ Finset.range 256, convContrib a b i j p

set_option maxRecDepth 8000 in
theorem mul_get (a b : Poly m) (p : ℕ) (hp : p < 256) :
    (Poly.mul a b)[p]'hp = convCoeff a b p := by
  unfold Poly.mul
  simp only [Aeneas.SRRange.forIn'_eq_forIn'_range', Aeneas.SRRange.size, Nat.sub_zero,
    Nat.add_sub_cancel, Nat.div_one]
  refine forIn'_getElem_indexed (List.range' 0 256) _ _ p hp _
    (P := fun I c => c[p]'hp = ∑ i ∈ Finset.range I, ∑ j ∈ Finset.range 256, convContrib a b i j p)
    ?hInit ?hFinal ?hStep
  case hInit =>
    show (Poly.zero m)[p] = _
    simp [Poly.zero, Vector.getElem_replicate]
  case hFinal =>
    intro dw hP
    rw [show (List.range' 0 256).length = 256 from by simp] at hP
    exact hP
  case hStep =>
    intro k hk c hPc a' ha' ha'eq
    have ha'k : a' = k := by rw [ha'eq]; simp [List.getElem_range']
    have ha'256 : a' < 256 := by rw [ha'k]; simpa using hk
    refine ⟨_, rfl, ?_⟩
    -- evaluate the inner loop over `j` via a second application of the indexed evaluator
    refine forIn'_getElem_indexed (List.range' 0 256) c _ p hp _
      (P := fun J cc => cc[p]'hp = (∑ i ∈ Finset.range k, ∑ j ∈ Finset.range 256, convContrib a b i j p)
        + ∑ j ∈ Finset.range J, convContrib a b a' j p)
      ?hI ?hF ?hS
    · rw [hPc]; simp
    · intro dw hP
      rw [show (List.range' 0 256).length = 256 from by simp] at hP
      rw [hP, ha'k]; exact (Finset.sum_range_succ _ k).symm
    · intro j hjk cc hPcc aa haa haaeq
      have haaj : aa = j := by rw [haaeq]; simp [List.getElem_range']
      subst haaj
      have haa256 : aa < 256 := by simpa using hjk
      rw [Finset.sum_range_succ]
      by_cases hC : a' + aa < 256
      · refine ⟨_, by rw [if_pos hC]; rfl, ?_⟩
        rw [Vector.getElem_set]
        by_cases hpk : (a' + aa) % 256 = p
        · rw [if_pos hpk, ← getElem!_pos cc ((a' + aa) % 256) (by rw [hpk]; exact hp), hpk,
            getElem!_pos cc p hp, hPcc, convContrib, if_pos hpk, if_pos hC,
            getElem!_pos a a' ha'256, getElem!_pos b aa haa256]
          ring
        · rw [if_neg hpk, hPcc, convContrib, if_neg hpk, add_zero]
      · refine ⟨_, by rw [if_neg hC]; rfl, ?_⟩
        rw [Vector.getElem_set]
        by_cases hpk : (a' + aa) % 256 = p
        · rw [if_pos hpk, ← getElem!_pos cc ((a' + aa) % 256) (by rw [hpk]; exact hp), hpk,
            getElem!_pos cc p hp, hPcc, convContrib, if_pos hpk, if_neg hC,
            getElem!_pos a a' ha'256, getElem!_pos b aa haa256]
          ring
        · rw [if_neg hpk, hPcc, convContrib, if_neg hpk, add_zero]

end Spec.Kopis
