import Spec.Kopis.Lemmas

/-! # `Spec.lean` agrees with `Explicit.lean`

The correspondence proofs are stated against `Explicit.lean`. This file proves that each function
of `Spec.lean` computes the same thing as its `Explicit` counterpart, so that the top-level theorems
can be stated against `Spec.lean`. -/

namespace Spec.Kopis.Equiv

open Spec.Kopis

/-! ## Loops -/

/-- An invariant of an `Id` loop whose body always continues. -/
theorem forIn'_inv {α β : Type} : ∀ (xs : List α) (init : β)
    (body : (a : α) → a ∈ xs → β → Id (ForInStep β)) (P : ℕ → β → Prop), P 0 init →
    (∀ (k : ℕ) (hk : k < xs.length) b, P k b →
      ∃ b', body (xs[k]'hk) (List.getElem_mem hk) b = pure (ForInStep.yield b') ∧ P (k + 1) b') →
    P xs.length (Id.run (forIn' xs init body)) := by
  intro xs; induction xs with
  | nil => intro init body P hInit _; exact hInit
  | cons x xs ih =>
    intro init body P hInit hStep
    obtain ⟨b', hb', hP⟩ := hStep 0 (by simp) init hInit
    simp only [List.forIn'_cons, Id.run, Bind.bind]
    rw [show body x (List.mem_cons_self ..) init = pure (ForInStep.yield b') from hb']
    exact ih b' (fun a m b => body a (.tail _ m) b) (fun k => P (k + 1)) hP
      (fun k hk b hb => hStep (k + 1) (by simp; omega) b hb)

/-- Two `Id` loops over the same list, whose bodies always continue, preserve a relation between
their states. -/
theorem forIn'_sim {α β γ : Type} : ∀ (xs : List α) (i1 : β) (i2 : γ)
    (b1 : (a : α) → a ∈ xs → β → Id (ForInStep β)) (b2 : (a : α) → a ∈ xs → γ → Id (ForInStep γ))
    (R : β → γ → Prop), R i1 i2 →
    (∀ a (m : a ∈ xs) x y, R x y → ∃ x' y', b1 a m x = pure (ForInStep.yield x') ∧
      b2 a m y = pure (ForInStep.yield y') ∧ R x' y') →
    R (Id.run (forIn' xs i1 b1)) (Id.run (forIn' xs i2 b2)) := by
  intro xs; induction xs with
  | nil => intro i1 i2 _ _ R h0 _; exact h0
  | cons x xs ih =>
    intro i1 i2 b1 b2 R h0 hs
    obtain ⟨x', y', h1, h2, hR⟩ := hs x (List.mem_cons_self ..) i1 i2 h0
    simp only [List.forIn'_cons, Id.run, Bind.bind]
    rw [show b1 x (List.mem_cons_self ..) i1 = pure (ForInStep.yield x') from h1,
      show b2 x (List.mem_cons_self ..) i2 = pure (ForInStep.yield y') from h2]
    exact ih x' y' (fun a m b => b1 a (.tail _ m) b) (fun a m b => b2 a (.tail _ m) b) R hR
      (fun a m x y h => hs a (.tail _ m) x y h)

theorem mem_range'_of_lt {a k : ℕ} (h : a < k) : a ∈ List.range' 0 k :=
  List.mem_range'_1.mpr ⟨Nat.zero_le _, by omega⟩

/-- A loop that sets element `i` to `f i`, for `i < k`. -/
theorem loop_set {α : Type} {n k : ℕ} (init : Vector α n)
    (f : (a : ℕ) → a ∈ List.range' 0 k → α) (H : ∀ a ∈ List.range' 0 k, a < n) :
    (forIn' (m := Id) (List.range' 0 k) init fun a m b => do
        pure PUnit.unit
        pure (ForInStep.yield (b.set a (f a m) (H a m))))
      = pure (Vector.ofFn fun j =>
          if h : j.val < k then f j (mem_range'_of_lt h) else init[j]) := by
  have := forIn'_inv (List.range' 0 k) init (fun a m b => do
        pure PUnit.unit
        pure (ForInStep.yield (b.set a (f a m) (H a m))))
    (fun c (b : Vector α n) => ∀ j (hj : j < n), b[j] =
      if h : j < c ∧ j < k then f j (mem_range'_of_lt h.2) else init[j])
    (fun j hj => by simp)
    (fun c hc b hb => ⟨_, rfl, fun j hj => by
      have hck : c < k := by simpa using hc
      simp only [Vector.getElem_set, List.getElem_range', Nat.zero_add, Nat.one_mul]
      by_cases hjc : c = j
      · subst hjc; simp [hck]
      · rw [if_neg hjc, hb j hj]
        by_cases hlt : j < c
        · rw [dif_pos ⟨hlt, by omega⟩, dif_pos ⟨by omega, by omega⟩]
        · rw [dif_neg (by omega), dif_neg (by omega)]⟩)
  simp only [List.length_range'] at this
  show Id.run _ = _
  congr 1; ext j hj; rw [this j hj]; simp only [Id.run_pure, Vector.getElem_ofFn]
  by_cases h : j < k
  · rw [dif_pos ⟨h, h⟩, dif_pos h]
  · rw [dif_neg (by omega), dif_neg h]; rfl

private theorem div_mod_chunk {c a j : ℕ} (h1 : c * a ≤ j) (h2 : j < c * a + c) :
    j / c = a ∧ j % c = j - c * a := by
  have hc : 0 < c := by omega
  have hd : j / c = a := by
    apply Nat.div_eq_of_lt_le
    · rw [Nat.mul_comm]; exact h1
    · rw [Nat.succ_mul, Nat.mul_comm]; exact h2
  refine ⟨hd, ?_⟩
  have := Nat.div_add_mod j c
  rw [hd] at this; omega

/-- A loop that overwrites the `c` elements from `c·i` with `g i`, for `i < k`. -/
theorem loop_setSlice {α : Type} {n k c o : ℕ} (init : Vector α n)
    (g : (a : ℕ) → a ∈ List.range' 0 k → Vector α c) (ho : o = c) :
    (forIn' (m := Id) (List.range' 0 k) init fun a m b => do
        pure PUnit.unit
        pure (ForInStep.yield (b.setSlice (o * a) (g a m))))
      = pure (Vector.ofFn fun j =>
          if h : j.val < c * k then
            (g (j / c) (mem_range'_of_lt (Nat.div_lt_of_lt_mul h)))[j % c]'(Nat.mod_lt _ (by
              rcases Nat.eq_zero_or_pos c with hc | hc
              · subst hc; simp at h
              · exact hc))
          else init[j]) := by
  subst ho
  have := forIn'_inv (List.range' 0 k) init (fun a m b => do
        pure PUnit.unit
        pure (ForInStep.yield (b.setSlice (o * a) (g a m))))
    (fun cnt (b : Vector α n) => ∀ j (hj : j < n), b[j] =
      if h : j < o * cnt ∧ j < o * k then
        (g (j / o) (mem_range'_of_lt (Nat.div_lt_of_lt_mul h.2)))[j % o]'(Nat.mod_lt _ (by
            rcases Nat.eq_zero_or_pos o with hc | hc
            · subst hc; simp at h
            · exact hc)) else init[j])
    (fun j hj => by simp)
    (fun cnt hc b hb => ⟨_, rfl, fun j hj => by
      have hck : cnt < k := by simpa using hc
      have hck' : o * (cnt + 1) ≤ o * k := Nat.mul_le_mul_left _ hck
      simp only [List.getElem_range', Nat.zero_add, Nat.one_mul, Vector.setSlice,
        Vector.getElem_ofFn, Fin.getElem_fin]
      by_cases hin : o * cnt ≤ j ∧ j - o * cnt < o
      · obtain ⟨hd, hm⟩ := div_mod_chunk hin.1 (by omega)
        rw [dif_pos hin, dif_pos ⟨by rw [Nat.mul_succ]; omega, by rw [Nat.mul_succ] at hck'; omega⟩]
        congr 1 <;> simp [hd, hm]
      · rw [dif_neg hin, hb j hj]
        by_cases hlt : j < o * cnt
        · rw [dif_pos ⟨hlt, by rw [Nat.mul_succ] at hck'; omega⟩,
            dif_pos ⟨by rw [Nat.mul_succ]; omega, by rw [Nat.mul_succ] at hck'; omega⟩]
        · rw [dif_neg (by omega), dif_neg (by rw [Nat.mul_succ]; omega)]⟩)
  simp only [List.length_range'] at this
  show Id.run _ = _
  congr 1; ext j hj; rw [this j hj]; simp only [Id.run_pure, Vector.getElem_ofFn]
  by_cases h : j < o * k
  · rw [dif_pos ⟨h, h⟩, dif_pos h]
  · rw [dif_neg (by omega), dif_neg h]; rfl

theorem slice_getElem {α : Type} [Inhabited α] {n : ℕ} (s : Vector α n) (a len j : ℕ)
    (hj : j < len) (h : a + j < n) : (slice s a len)[j] = s[a + j] := by
  simp only [slice, Vector.getElem_ofFn]; exact getElem!_pos s _ h

theorem turboSHAKE256_cast {m L L' : ℕ} (M : 𝔹 m) (D : Byte) (h : L = L') :
    (TurboSHAKE.turboSHAKE256 M D L).cast h = TurboSHAKE.turboSHAKE256 M D L' := by
  subst h; rfl

theorem turboSHAKE128_cast {m L L' : ℕ} (M : 𝔹 m) (D : Byte) (h : L = L') :
    (TurboSHAKE.turboSHAKE128 M D L).cast h = TurboSHAKE.turboSHAKE128 M D L' := by
  subst h; rfl

/-- The `Id`-loop preamble every spec loop unfolds to. -/
macro "unfold_loops" : tactic => `(tactic|
  simp only [Aeneas.SRRange.forIn'_eq_forIn'_range', Aeneas.SRRange.size, Nat.sub_zero,
    Nat.add_sub_cancel, Nat.div_one, bind_pure])

/-! ## Serialization -/

theorem serialize_elem_eq (n : ℕ) (r : R n) :
    serialize_elem n r = (Explicit.serialize_elem n r).cast (by omega) := by
  unfold serialize_elem
  unfold_loops
  have e1 := loop_setSlice (Vector.replicate (n * 256) false)
    (fun a m => to_bits_le n ((canonical_coeffs r)[a]'(by simp at m; omega))) rfl
  rw [e1, pure_bind]
  have e2 := fun (all : Vector Bool (n * 256)) => loop_set (k := 32 * n) (Vector.replicate (n * 256 / 8) 0)
    (fun a _ => (from_bits_le 8 (slice all (8 * a) 8) : Byte)) (fun a m => by simp at m; omega)
  rw [e2]
  apply Vector.ext; intro p hp
  simp only [Id.run_pure, Vector.getElem_ofFn, Vector.getElem_cast, Explicit.serialize_elem,
    dif_pos (show p < 32 * n by omega)]
  refine congrArg (fun v : Vector Bool 8 => ((from_bits_le 8 v : ℕ) : Byte)) ?_
  apply Vector.ext; intro q hq
  simp only [slice, Spec.slice, Vector.getElem_ofFn, Vector.getElem_flatten]
  rw [getElem!_pos _ _ (by omega), Vector.getElem_ofFn, dif_pos (by omega)]
  rfl

theorem deserialize_elem_eq (n : ℕ) (bytes : 𝔹 (n * 256 / 8)) :
    deserialize_elem n bytes = Explicit.deserialize_elem n (bytes.cast (by omega)) := by
  unfold deserialize_elem
  unfold_loops
  have e1 := loop_setSlice (k := n * 32) (Vector.replicate (n * 256) false)
    (fun a m => to_bits_le 8 (bytes[a]'(by simp at m; omega)).toNat) rfl
  rw [e1, pure_bind]
  have e2 := fun (all : Vector Bool (n * 256)) => loop_set (k := 256) (Vector.replicate 256 (0 : ℤ))
    (fun a _ => ((from_bits_le n (slice all (n * a) n) : ℕ) : ℤ)) (fun a m => by simp at m; omega)
  rw [e2]
  apply Vector.ext; intro i hi
  simp only [pure_bind, Id.run_pure, make_rn, Explicit.make_rn, Explicit.deserialize_elem, Vector.getElem_map,
    Vector.getElem_ofFn, dif_pos hi, Int.cast_natCast]
  refine congrArg (fun v : Vector Bool n => ((from_bits_le n v : ℕ) : ZMod (2 ^ n))) ?_
  apply Vector.ext; intro q hq
  have hb : n * i + q < n * 256 := by
    have := Explicit.chunk_bound (n := n) hi; omega
  simp only [slice, Spec.slice, Vector.getElem_ofFn, Vector.getElem_flatten]
  rw [getElem!_pos _ _ (by omega), Vector.getElem_ofFn, dif_pos (by omega)]
  rfl

theorem hamming_eq {k : ℕ} (b : Vector Bool k) : hamming b = Explicit.hamming b := by
  unfold hamming
  unfold_loops
  have := forIn'_inv (List.range' 0 k) 0 (fun a m w =>
      if b[a]'(by simp at m; omega) = true then do
        pure PUnit.unit
        pure (ForInStep.yield (w + 1))
      else do
        pure PUnit.unit
        pure (ForInStep.yield w))
    (fun c w => c ≤ k → w = ∑ i : Fin c, (b[i.val]!).toNat)
    (fun _ => by simp)
    (fun c hc w hw => by
      have hck : c < k := by simpa using hc
      simp only [List.getElem_range', Nat.zero_add, Nat.one_mul]
      refine ⟨if b[c] then w + 1 else w, by split <;> rfl, fun _ => ?_⟩
      rw [Fin.sum_univ_castSucc]
      simp only [Fin.val_castSucc, Fin.val_last]
      rw [← hw (by omega), getElem!_pos b c hck]
      cases b[c] <;> simp)
  rw [List.length_range'] at this
  refine (this le_rfl).trans ?_
  unfold Explicit.hamming
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [getElem!_pos b i.val i.isLt]; rfl

theorem GenMat_eq (P : ParameterSet) (seed : 𝔹 32) : GenMat P seed = Explicit.GenMat P.ℓ seed := by
  unfold GenMat Explicit.GenMat
  unfold_loops
  show make_matn 13 (Id.run (forIn' _ _ _)) = Id.run (forIn' _ _ _)
  refine forIn'_sim _ _ _ _ _ (fun A M => make_matn 13 A = M) ?_ ?_
  · funext i j; simp [make_matn, Explicit.PolyMatrix.zero]; rfl
  intro a m A M hAM
  refine ⟨_, _, rfl, rfl, ?_⟩
  refine forIn'_sim _ _ _ _ _ (fun A M => make_matn 13 A = M) hAM ?_
  intro b m2 A' M' h'
  refine ⟨_, _, rfl, rfl, ?_⟩
  subst h'
  have ha : a < P.ℓ := by simp at m; omega
  have hb : b < P.ℓ := by simp at m2; omega
  funext i j
  simp only [make_matn, Explicit.PolyMatrix.update, Matrix.of_apply, Matrix.updateRow_apply]
  by_cases hi : i = ⟨a, ha⟩
  · subst hi
    simp only [if_true, Fin.getElem_fin, Vector.getElem_set_self, Vector.getElem_set]
    by_cases hj : j.val = b
    · simp only [hj, if_true]
      rw [deserialize_elem_eq]; rfl
    · simp only [Ne.symm hj, hj, if_false]
  · have hi' : a ≠ i.val := fun h => hi (Fin.ext h.symm)
    simp [hi, hi']

theorem bit_slices_eq (P : ParameterSet) (bytes : 𝔹 (P.μ * 256 / 8)) :
    bit_slices P bytes = Explicit.bit_slices P.μ (bytes.cast (by omega)) := by
  unfold bit_slices
  unfold_loops
  have e1 := loop_setSlice (k := P.μ * 32) (Vector.replicate (P.μ * 256) false)
    (fun a m => to_bits_le 8 (bytes[a]'(by simp at m; omega)).toNat) rfl
  rw [e1, pure_bind]
  have e2 := fun (all : Vector Bool (P.μ * 256)) => loop_set (k := 512)
    (Vector.replicate 512 (Vector.replicate (P.μ / 2) false))
    (fun a _ => slice all (a * P.μ / 2) (P.μ / 2)) (fun a m => by simp at m; omega)
  rw [e2]
  apply Vector.ext; intro i hi
  apply Vector.ext; intro q hq
  have hb : i * P.μ / 2 + q < P.μ * 256 := by
    have := Nat.mul_le_mul_right P.μ (Nat.succ_le_of_lt hi); rw [Nat.succ_mul] at this; omega
  simp only [Id.run_pure, Explicit.bit_slices, Vector.getElem_ofFn, dif_pos hi]
  rw [slice_getElem _ _ _ _ hq hb]
  simp only [Spec.slice, Vector.getElem_ofFn, Vector.getElem_flatten, dif_pos (show i * P.μ / 2 + q < 8 * (P.μ * 32) by omega)]
  rfl

theorem GenSecret_eq (P : ParameterSet) (seed : 𝔹 32) :
    GenSecret P seed = Explicit.GenSecret P.ℓ P.μ seed := by
  unfold GenSecret Explicit.GenSecret
  unfold_loops
  show make_vecn 13 (Id.run (forIn' (List.range' 0 P.ℓ) _ _)) = Id.run (forIn' (List.range' 0 P.ℓ) _ _)
  refine forIn'_sim _ _ _ _ _ (fun s s' => s = s') rfl ?_
  intro a m s s' hss
  subst hss
  refine ⟨_, _, rfl, rfl, ?_⟩
  unfold Explicit.PolyVector.set
  refine congrArg (fun x => s.set a x (by simp at m; omega)) ?_
  have hV : bit_slices P (TurboSHAKE256 (Vector.append seed #v[(a : Byte)]) (P.μ * 256 / 8)
        DOMSEP_GENSEC)
      = Explicit.bit_slices P.μ (TurboSHAKE.turboSHAKE256 (Vector.append seed #v[(a : Byte)])
        DOMSEP_GENSEC (32 * P.μ)) := by
    rw [bit_slices_eq]; unfold TurboSHAKE256; rw [turboSHAKE256_cast]
  refine forIn'_sim _ _ _ _ _ (fun r r' => make_rn 13 r = Explicit.make_rn 13 r') ?_ ?_
  · apply Vector.ext; intro j hj; simp [make_rn, Explicit.make_rn]
  intro k mk r r' hr
  refine ⟨_, _, rfl, rfl, ?_⟩
  simp only [make_rn, Explicit.make_rn] at hr ⊢
  rw [Vector.map_set, hr, hV, hamming_eq, hamming_eq]
  refine congrArg (fun x => r'.set k x (by simp at mk; omega)) ?_
  rw [show ((2 : ℤ) ^ 13) = ((2 ^ 13 : ℕ) : ℤ) by norm_num, ZMod.intCast_mod]
  push_cast; rfl

theorem serialize_vec_eq (P : ParameterSet) (n : ℕ) (v : VecR n P.ℓ) :
    serialize_vec P n v = (Explicit.serialize_vec n v).cast (by
      rw [show 256 * P.ℓ * n = P.ℓ * (32 * n) * 8 by ring]; omega) := by
  unfold serialize_vec
  unfold_loops
  have hc : n * 256 / 8 = 32 * n := by omega
  have e1 := loop_setSlice (k := P.ℓ) (o := n * 32) (Vector.replicate (256 * P.ℓ * n / 8) (0 : Byte))
    (fun a m => serialize_elem n (v[a]'(by simp at m; omega))) (by omega)
  rw [e1]
  apply Vector.ext; intro j hj
  have hj' : j < 32 * n * P.ℓ := by
    rw [show 256 * P.ℓ * n = P.ℓ * (32 * n) * 8 by ring] at hj; rw [Nat.mul_comm]; omega
  simp only [Id.run_pure, Vector.getElem_ofFn, Vector.getElem_cast, Explicit.serialize_vec,
    Vector.getElem_flatten, Vector.getElem_map, serialize_elem_eq]
  simp only [hc, dif_pos hj']

theorem deserialize_vec_eq (P : ParameterSet) (n : ℕ) (bytes : 𝔹 (256 * P.ℓ * n / 8)) :
    deserialize_vec P n bytes = Explicit.deserialize_vec (ℓ := P.ℓ) n (bytes.cast (by
      rw [show 256 * P.ℓ * n = 32 * n * P.ℓ * 8 by ring]; omega)) := by
  unfold deserialize_vec
  unfold_loops
  have e1 := loop_set (k := P.ℓ) (Vector.replicate P.ℓ (0 : R n))
    (fun a _ => deserialize_elem n (slice bytes (n * 32 * a) (n * 256 / 8)))
    (fun a m => by simp at m; omega)
  rw [e1]
  apply Vector.ext; intro i hi
  simp only [pure_bind, Id.run_pure, make_vecn, Vector.getElem_ofFn, dif_pos hi,
    Explicit.deserialize_vec, deserialize_elem_eq]
  refine congrArg (Explicit.deserialize_elem n) ?_
  apply Vector.ext; intro q hq
  have hb := Explicit.chunk_bound (n := 32 * n) hi
  rw [Vector.getElem_cast, slice_getElem _ _ _ _ (by omega)
    (by rw [show 256 * P.ℓ * n = 32 * n * P.ℓ * 8 by ring]; rw [Nat.mul_comm n 32]; omega)]
  simp only [Spec.slice, Vector.getElem_ofFn, Vector.getElem_cast]
  congr 1; ring

/-! ## Compression -/

theorem make_rn_replicate (n : ℕ) (c : ℕ) :
    make_rn n (Vector.replicate 256 (c : ℤ)) = Explicit.make_rn n (Vector.replicate 256 (c : ZMod (2 ^ n))) := by
  simp [make_rn, Explicit.make_rn]

theorem CompressToR10_eq (P : ParameterSet) (v : VecR 13 P.ℓ) :
    CompressToR10 P v = Explicit.CompressToR10 P.ℓ v := by
  unfold CompressToR10 Explicit.CompressToR10
  simp only [Id.run_pure, make_vecn, PolyVector.as_vecn]
  rw [show (4 : ℤ) = ((4 : ℕ) : ℤ) from rfl, make_rn_replicate]; rfl

theorem CompressToRt_eq (P : ParameterSet) (r : R 10) : CompressToRt P r = Explicit.CompressToRt P.t r := by
  unfold CompressToRt Explicit.CompressToRt
  simp only [Id.run_pure, Poly.as_rn]
  rw [show (4 : ℤ) = ((4 : ℕ) : ℤ) from rfl, make_rn_replicate]; rfl

theorem DecodeMsg_eq (P : ParameterSet) (ht : 1 ≤ P.t) (r : R 10) :
    DecodeMsg P r = Explicit.DecodeMsg P.t r := by
  unfold DecodeMsg Explicit.DecodeMsg
  simp only [Id.run_pure, Poly.as_rn]
  have h : (2 : ℤ) ^ 8 - 2 ^ (10 - P.t - 1) + 4 = ((2 ^ 8 - 2 ^ (10 - P.t - 1) + 4 : ℕ) : ℤ) := by
    have : 2 ^ (10 - P.t - 1) ≤ 2 ^ 8 := Nat.pow_le_pow_right (by decide) (by omega)
    rw [Nat.cast_add, Nat.cast_sub this]; push_cast; ring
  rw [h, make_rn_replicate]

/-! ## Top-level functions, per parameter set -/

theorem slice_eq {α : Type} [Inhabited α] {n : ℕ} (s : Vector α n) (a len : ℕ) (h : a + len ≤ n) :
    slice s a len = Spec.slice s a len h := by
  apply Vector.ext; intro j hj
  rw [slice_getElem _ _ _ _ hj (by omega)]; simp [Spec.slice]

theorem append_cast {α : Type} {n n' m m' k : ℕ} (a : Vector α n) (b : Vector α m) (h1 : n = n')
    (h2 : m = m') (h3 : n' + m' = k) (h4 : n + m = k) :
    ((a.cast h1).append (b.cast h2)).cast h3 = (a.append b).cast h4 := by
  subst h1 h2; rfl

/-- Removes the casts and coercion wrappers that `Spec.lean` and `Explicit.lean` differ by. -/
macro "uncast" : tactic => `(tactic|
  ((try simp only [Vector.cast_rfl, PolyVector.as_vecn, Poly.as_rn, append_cast]) <;> rfl))

/-- Evaluates the parameters and the byte lengths they determine. -/
macro "norm_params" : tactic => `(tactic|
  simp only [ParameterSet.Kopis_512, ParameterSet.Kopis_768, ParameterSet.Kopis_1024,
    Explicit.ℓ, Explicit.t, Explicit.μ, Nat.reduceMul, Nat.reduceDiv, Nat.reduceAdd])

theorem ExpandSecretKey_eq_512 (sk : 𝔹 32) :
    ExpandSecretKey .Kopis_512 sk = Explicit.ExpandSecretKey .Kopis_512 sk := by
  unfold ExpandSecretKey Explicit.ExpandSecretKey
  simp only [Id.run_pure, TurboSHAKE256, GenMat_eq, GenSecret_eq, CompressToR10_eq,
    serialize_vec_eq]
  norm_params
  simp (disch := decide) only [slice_eq]
  uncast

theorem PkeEncrypt_eq_512 (randomness : 𝔹 32) (pk : 𝔹 672) (msg : 𝔹 32) :
    PkeEncrypt .Kopis_512 randomness pk msg = Explicit.PkeEncrypt .Kopis_512 randomness pk msg := by
  unfold PkeEncrypt Explicit.PkeEncrypt
  simp only [Id.run_pure, deserialize_vec_eq, deserialize_elem_eq, GenMat_eq,
    GenSecret_eq, CompressToR10_eq, CompressToRt_eq, serialize_vec_eq, serialize_elem_eq]
  norm_params
  simp (disch := decide) only [slice_eq]
  uncast

theorem PkeDecrypt_eq_512 (sk : 𝔹 32) (ct : 𝔹 736) :
    PkeDecrypt .Kopis_512 sk ct = Explicit.PkeDecrypt .Kopis_512 sk ct := by
  unfold PkeDecrypt Explicit.PkeDecrypt
  simp only [Id.run_pure, ExpandSecretKey_eq_512, deserialize_vec_eq,
    deserialize_elem_eq, DecodeMsg_eq _ (by decide : 1 ≤ ParameterSet.Kopis_512.t),
    serialize_elem_eq]
  norm_params
  simp (disch := decide) only [slice_eq]
  uncast

theorem KemEncap_eq_512 (randomness : 𝔹 32) (pk : 𝔹 672) :
    KemEncap .Kopis_512 randomness pk = Explicit.KemEncap .Kopis_512 randomness pk := by
  unfold KemEncap Explicit.KemEncap
  simp only [Id.run_pure, TurboSHAKE256, PkeEncrypt_eq_512]
  simp (disch := decide) only [slice_eq]
  uncast

theorem KemDecap_eq_512 (sk : 𝔹 32) (ct : 𝔹 736) :
    KemDecap .Kopis_512 sk ct = Explicit.KemDecap .Kopis_512 sk ct := by
  unfold KemDecap Explicit.KemDecap
  simp only [TurboSHAKE256, ExpandSecretKey_eq_512, PkeDecrypt_eq_512,
    PkeEncrypt_eq_512]
  simp (disch := decide) only [slice_eq]
  split_ifs with h1 h2 h2 <;> simp only [beq_iff_eq] at h1
  · rfl
  · exact absurd h1 h2
  · exact absurd h2 h1
  · rfl

theorem SkToPk_eq_512 (sk : 𝔹 32) :
    SkToPk .Kopis_512 sk = Explicit.SkToPk .Kopis_512 sk := by
  unfold SkToPk Explicit.SkToPk
  simp only [Id.run_pure, ExpandSecretKey_eq_512]

theorem ExpandSecretKey_eq_768 (sk : 𝔹 32) :
    ExpandSecretKey .Kopis_768 sk = Explicit.ExpandSecretKey .Kopis_768 sk := by
  unfold ExpandSecretKey Explicit.ExpandSecretKey
  simp only [Id.run_pure, TurboSHAKE256, GenMat_eq, GenSecret_eq, CompressToR10_eq,
    serialize_vec_eq]
  norm_params
  simp (disch := decide) only [slice_eq]
  uncast

theorem PkeEncrypt_eq_768 (randomness : 𝔹 32) (pk : 𝔹 992) (msg : 𝔹 32) :
    PkeEncrypt .Kopis_768 randomness pk msg = Explicit.PkeEncrypt .Kopis_768 randomness pk msg := by
  unfold PkeEncrypt Explicit.PkeEncrypt
  simp only [Id.run_pure, deserialize_vec_eq, deserialize_elem_eq, GenMat_eq,
    GenSecret_eq, CompressToR10_eq, CompressToRt_eq, serialize_vec_eq, serialize_elem_eq]
  norm_params
  simp (disch := decide) only [slice_eq]
  uncast

theorem PkeDecrypt_eq_768 (sk : 𝔹 32) (ct : 𝔹 1088) :
    PkeDecrypt .Kopis_768 sk ct = Explicit.PkeDecrypt .Kopis_768 sk ct := by
  unfold PkeDecrypt Explicit.PkeDecrypt
  simp only [Id.run_pure, ExpandSecretKey_eq_768, deserialize_vec_eq,
    deserialize_elem_eq, DecodeMsg_eq _ (by decide : 1 ≤ ParameterSet.Kopis_768.t),
    serialize_elem_eq]
  norm_params
  simp (disch := decide) only [slice_eq]
  uncast

theorem KemEncap_eq_768 (randomness : 𝔹 32) (pk : 𝔹 992) :
    KemEncap .Kopis_768 randomness pk = Explicit.KemEncap .Kopis_768 randomness pk := by
  unfold KemEncap Explicit.KemEncap
  simp only [Id.run_pure, TurboSHAKE256, PkeEncrypt_eq_768]
  simp (disch := decide) only [slice_eq]
  uncast

theorem KemDecap_eq_768 (sk : 𝔹 32) (ct : 𝔹 1088) :
    KemDecap .Kopis_768 sk ct = Explicit.KemDecap .Kopis_768 sk ct := by
  unfold KemDecap Explicit.KemDecap
  simp only [TurboSHAKE256, ExpandSecretKey_eq_768, PkeDecrypt_eq_768,
    PkeEncrypt_eq_768]
  simp (disch := decide) only [slice_eq]
  split_ifs with h1 h2 h2 <;> simp only [beq_iff_eq] at h1
  · rfl
  · exact absurd h1 h2
  · exact absurd h2 h1
  · rfl

theorem SkToPk_eq_768 (sk : 𝔹 32) :
    SkToPk .Kopis_768 sk = Explicit.SkToPk .Kopis_768 sk := by
  unfold SkToPk Explicit.SkToPk
  simp only [Id.run_pure, ExpandSecretKey_eq_768]

theorem ExpandSecretKey_eq_1024 (sk : 𝔹 32) :
    ExpandSecretKey .Kopis_1024 sk = Explicit.ExpandSecretKey .Kopis_1024 sk := by
  unfold ExpandSecretKey Explicit.ExpandSecretKey
  simp only [Id.run_pure, TurboSHAKE256, GenMat_eq, GenSecret_eq, CompressToR10_eq,
    serialize_vec_eq]
  norm_params
  simp (disch := decide) only [slice_eq]
  uncast

theorem PkeEncrypt_eq_1024 (randomness : 𝔹 32) (pk : 𝔹 1312) (msg : 𝔹 32) :
    PkeEncrypt .Kopis_1024 randomness pk msg = Explicit.PkeEncrypt .Kopis_1024 randomness pk msg := by
  unfold PkeEncrypt Explicit.PkeEncrypt
  simp only [Id.run_pure, deserialize_vec_eq, deserialize_elem_eq, GenMat_eq,
    GenSecret_eq, CompressToR10_eq, CompressToRt_eq, serialize_vec_eq, serialize_elem_eq]
  norm_params
  simp (disch := decide) only [slice_eq]
  uncast

theorem PkeDecrypt_eq_1024 (sk : 𝔹 32) (ct : 𝔹 1472) :
    PkeDecrypt .Kopis_1024 sk ct = Explicit.PkeDecrypt .Kopis_1024 sk ct := by
  unfold PkeDecrypt Explicit.PkeDecrypt
  simp only [Id.run_pure, ExpandSecretKey_eq_1024, deserialize_vec_eq,
    deserialize_elem_eq, DecodeMsg_eq _ (by decide : 1 ≤ ParameterSet.Kopis_1024.t),
    serialize_elem_eq]
  norm_params
  simp (disch := decide) only [slice_eq]
  uncast

theorem KemEncap_eq_1024 (randomness : 𝔹 32) (pk : 𝔹 1312) :
    KemEncap .Kopis_1024 randomness pk = Explicit.KemEncap .Kopis_1024 randomness pk := by
  unfold KemEncap Explicit.KemEncap
  simp only [Id.run_pure, TurboSHAKE256, PkeEncrypt_eq_1024]
  simp (disch := decide) only [slice_eq]
  uncast

theorem KemDecap_eq_1024 (sk : 𝔹 32) (ct : 𝔹 1472) :
    KemDecap .Kopis_1024 sk ct = Explicit.KemDecap .Kopis_1024 sk ct := by
  unfold KemDecap Explicit.KemDecap
  simp only [TurboSHAKE256, ExpandSecretKey_eq_1024, PkeDecrypt_eq_1024,
    PkeEncrypt_eq_1024]
  simp (disch := decide) only [slice_eq]
  split_ifs with h1 h2 h2 <;> simp only [beq_iff_eq] at h1
  · rfl
  · exact absurd h1 h2
  · exact absurd h2 h1
  · rfl

theorem SkToPk_eq_1024 (sk : 𝔹 32) :
    SkToPk .Kopis_1024 sk = Explicit.SkToPk .Kopis_1024 sk := by
  unfold SkToPk Explicit.SkToPk
  simp only [Id.run_pure, ExpandSecretKey_eq_1024]

end Spec.Kopis.Equiv

