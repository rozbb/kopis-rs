/-
  # Kopis/Keccak/Bits.lean — the word view of a Keccak state.

  `Spec/SHA3/Spec.lean` is FIPS 202 read literally: a state is `Vector (Vector Lane 5) 5` with
  `Lane = Vector Bool 64`, and the step mappings are written bit by bit.  `src/backend/avx2/
  keccak.rs` holds the same state as 25 `Vec256` registers, each carrying one lane of all four
  sponges as a 64-bit field, and computes with whole-word `vpxor` / `vpandn` / `vpsllq`.

  This file is the bridge between those two pictures, and nothing in it mentions an intrinsic or
  an extracted constant — it is entirely about the spec.  `ofLane` reads a spec lane as a
  `BitVec 64`; the homomorphism lemmas below say that the spec's pointwise `⊕`, `&&&`, `~~~` and
  `Vector.rotateLeft` become `BitVec`'s, so a bit-by-bit spec step becomes a word equation.
  `Kopis/Avx2/Keccak/Round.lean` then states θ, ρ, π, χ and ι in that form.

  Bit order is the one place this could silently go wrong, and it does not: FIPS 202 §3.1.1
  numbers the bits of a lane LSB-first in `z`, which is exactly `BitVec.getLsbD`, so `ofLane` is
  a relabelling rather than a reversal.  `getElem_ofLane` is that statement, and every lemma here
  is a consequence of it.
-/
import Spec.SHA3.Spec
import Kopis.Bits.Lanes

namespace Kopis.Keccak
set_option maxHeartbeats 1000000

open Spec.SHA3
open scoped Spec.Notations

/-! ## A spec lane as a 64-bit word -/

/-- The 64-bit word of a spec lane: bit `z` of the word is `L[z]`. -/
def ofLane (L : Lane) : BitVec 64 := BitVec.ofFn fun z => L[z]

@[simp] theorem getElem_ofLane (L : Lane) (z : Nat) (h : z < 64) : (ofLane L)[z] = L[z] :=
  BitVec.getElem_ofFn _ _ _

theorem getLsbD_ofLane (L : Lane) (z : Nat) (h : z < 64) : (ofLane L).getLsbD z = L[z] := by
  rw [BitVec.getLsbD_eq_getElem h, getElem_ofLane L z h]

/-- Two lanes with the same word are the same lane: `ofLane` loses nothing. -/
theorem ofLane_inj {L M : Lane} (h : ofLane L = ofLane M) : L = M := by
  apply Vector.ext
  intro i hi
  have := congrArg (fun v => v[i]'(by simpa using hi)) h
  simpa only [getElem_ofLane _ i hi] using this

/-- Word equality is bitwise equality — the shape every proof below closes with. -/
theorem ofLane_eq_iff {L : Lane} {x : BitVec 64} :
    ofLane L = x ↔ ∀ z, (h : z < 64) → L[z] = x[z] := by
  constructor
  · rintro rfl z hz; rw [getElem_ofLane L z hz]
  · intro h
    apply BitVec.eq_of_getLsbD_eq
    intro z hz
    rw [getLsbD_ofLane L z hz, BitVec.getLsbD_eq_getElem hz]
    exact h z hz

/-! ## The pointwise operations are the word operations

The spec's `⊕`, `&&&`, `|||` and `~~~` on `Vector Bool n` are `Vector.zipWith`/`Vector.map`
(see `Spec/Defs.lean`); `BitVec`'s are bitwise.  On a lane they agree. -/

theorem getElem_vxor (L M : Lane) (z : Nat) (h : z < 64) : (L ^^^ M)[z] = (L[z] ^^ M[z]) :=
  Vector.getElem_zipWith h

theorem getElem_vand (L M : Lane) (z : Nat) (h : z < 64) : (L &&& M)[z] = (L[z] && M[z]) :=
  Vector.getElem_zipWith h

theorem getElem_vor (L M : Lane) (z : Nat) (h : z < 64) : (L ||| M)[z] = (L[z] || M[z]) :=
  Vector.getElem_zipWith h

theorem getElem_vnot (L : Lane) (z : Nat) (h : z < 64) : (~~~L)[z] = !L[z] :=
  Vector.getElem_map _ h

@[simp] theorem ofLane_xor (L M : Lane) : ofLane (L ^^^ M) = ofLane L ^^^ ofLane M := by
  apply BitVec.eq_of_getLsbD_eq
  intro z hz
  simp only [getLsbD_ofLane _ z hz, BitVec.getLsbD_xor, getElem_vxor L M z hz]

@[simp] theorem ofLane_and (L M : Lane) : ofLane (L &&& M) = ofLane L &&& ofLane M := by
  apply BitVec.eq_of_getLsbD_eq
  intro z hz
  simp only [getLsbD_ofLane _ z hz, BitVec.getLsbD_and, getElem_vand L M z hz]

@[simp] theorem ofLane_or (L M : Lane) : ofLane (L ||| M) = ofLane L ||| ofLane M := by
  apply BitVec.eq_of_getLsbD_eq
  intro z hz
  simp only [getLsbD_ofLane _ z hz, BitVec.getLsbD_or, getElem_vor L M z hz]

@[simp] theorem ofLane_not (L : Lane) : ofLane (~~~L) = ~~~(ofLane L) := by
  apply BitVec.eq_of_getLsbD_eq
  intro z hz
  simp only [getLsbD_ofLane _ z hz, BitVec.getLsbD_not, getElem_vnot L z hz,
    hz, decide_true, Bool.true_and]

/-- χ's `(¬a) ∧ b` — the shape `vpandn` computes directly. -/
theorem ofLane_andnot (L M : Lane) : ofLane (~~~L &&& M) = (~~~ofLane L) &&& ofLane M := by
  rw [ofLane_and, ofLane_not]

/-! ## Rotation

`Vector.rotateLeft v k` is `v[(i + n - k % n) % n]` and `BitVec.rotateLeft` splits at `k % w`.
The two agree on both sides of that split; the arithmetic is `omega`'s. -/

/-- `BitVec.rotateLeft` reads the source at `(z + w - k % w) % w`, which is the index
`Vector.rotateLeft` reads at.  Stated separately so the two representations meet on a single
arithmetic form rather than inside a case split. -/
private theorem getLsbD_rotateLeft_mod (x : BitVec 64) (k z : Nat) (hz : z < 64) :
    (x.rotateLeft k).getLsbD z = x.getLsbD ((z + 64 - k % 64) % 64) := by
  have hmod : k % 64 < 64 := Nat.mod_lt _ (by norm_num)
  rw [BitVec.getLsbD_rotateLeft]
  by_cases hlt : z < k % 64
  · rw [Bool.cond_eq_ite, if_pos (by simpa using hlt)]
    congr 1
    omega
  · rw [Bool.cond_eq_ite, if_neg (by simpa using hlt), decide_eq_true hz, Bool.true_and]
    congr 1
    omega

@[simp] theorem ofLane_rotateLeft (L : Lane) (k : Nat) :
    ofLane (L.rotateLeft k) = (ofLane L).rotateLeft k := by
  apply BitVec.eq_of_getLsbD_eq
  intro z hz
  have hmod : (z + 64 - k % 64) % 64 < 64 := Nat.mod_lt _ (by norm_num)
  rw [getLsbD_rotateLeft_mod _ k z hz, getLsbD_ofLane L _ hmod, getLsbD_ofLane _ z hz]
  simp only [Vector.rotateLeft, dif_neg (show ¬(64 = 0) by norm_num), Vector.getElem_ofFn]


/-! ## A `getElem!` reader for `List.set`

Used wherever a proof has to read back an array the extracted code has just written at a literal
index.  Lean has `List.getElem_set_self` / `List.getElem_set_of_ne` but no `getElem!` form, and
the `getElem!` form is what avoids a dependent rewrite on the index. -/

theorem getElem!_list_set {α : Type _} [Inhabited α] (l : List α) (j : ℕ)
    (v : α) (k : ℕ) (hj : j < l.length) :
    (l.set j v)[k]! = if k = j then v else l[k]! := by
  by_cases h : k = j
  · subst h
    rw [getElem!_pos _ k (by rw [List.length_set]; exact hj), List.getElem_set_self, if_pos rfl]
  · by_cases hk : k < l.length
    · rw [getElem!_pos _ k (by rw [List.length_set]; exact hk),
        List.getElem_set_of_ne (Ne.symm h), ← getElem!_pos _ k hk, if_neg h]
    · rw [getElem!_neg _ k (by rw [List.length_set]; exact hk), getElem!_neg _ k hk, if_neg h]

/-! ## The state as 25 words

`A[x][y]` is the lane at word index `5y + x`, which is the index `keccak.rs` stores it at
(`state[5 * y + x]`) and the index FIPS 202 §3.1.2 places it at in the 1600-bit string. -/

/-- Lane `(x, y)` of a spec state, as a word. -/
def stWord (A : State) (x y : Fin 5) : BitVec 64 := ofLane A[x][y]

/-- The flat word index FIPS 202 §3.1.2 and `keccak.rs` both use. -/
@[reducible] def idx (x y : Fin 5) : Nat := 5 * y.val + x.val

theorem idx_lt (x y : Fin 5) : idx x y < 25 := by
  have := x.isLt; have := y.isLt; simp only [idx]; omega

/-- The coordinates a flat word index came from. -/
def coordX (k : ℕ) : Fin 5 := ⟨k % 5, Nat.mod_lt _ (by norm_num)⟩

def coordY (k : ℕ) : Fin 5 := ⟨k / 5 % 5, Nat.mod_lt _ (by norm_num)⟩

theorem idx_coord (k : ℕ) (h : k < 25) : idx (coordX k) (coordY k) = k := by
  simp only [idx, coordX, coordY]; omega

/-- The flat index determines the coordinates. -/
theorem idx_inj {x y x' y' : Fin 5} (h : idx x y = idx x' y') : x = x' ∧ y = y' := by
  have hx := x.isLt; have hy := y.isLt; have hx' := x'.isLt; have hy' := y'.isLt
  simp only [idx] at h
  constructor <;> (apply Fin.ext; omega)

end Kopis.Keccak
