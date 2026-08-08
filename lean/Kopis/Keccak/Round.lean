/-
  # Kopis/Keccak/Round.lean — the Keccak round in word form.

  `Spec/SHA3/Spec.lean` writes θ, ρ, π, χ and ι bit by bit over `Vector Bool 64` lanes, which is
  FIPS 202 read literally and is the right shape for an auditor.  It is the wrong shape for
  relating to `each backend's `keccak.rs``, which computes on whole 64-bit words with `vpxor`,
  `vpandn`, `vpsllq` and `vpsrlq`.

  This file restates each step mapping on `Words = Fin 5 → Fin 5 → BitVec 64` and proves it is
  the spec's, transported along `wordsOf`.  Everything is a consequence of the homomorphism
  lemmas in `Bits.lean`; no intrinsic and no extracted constant appears here.

  After this, `Rnd` is `RndW` and the remaining gap to the AVX2 code is scheduling — the fused
  ρ-π-χ of `keccak.rs`'s `chi_row!` and the deferred θ xor — which is what
  `Kopis/Avx2/Keccak/Fused.lean` addresses.
-/
import Kopis.Keccak.Bits

namespace Kopis.Keccak

open Spec.SHA3
open scoped Spec.Notations

set_option maxHeartbeats 1000000

/-! ## The word view of a state -/

/-- A Keccak state as 25 words, indexed by the FIPS coordinates. -/
abbrev Words := Fin 5 → Fin 5 → BitVec 64

/-- The word view of a spec state. -/
def wordsOf (A : State) : Words := fun x y => ofLane A[x][y]

@[simp] theorem wordsOf_apply (A : State) (x y : Fin 5) : wordsOf A x y = ofLane A[x][y] := rfl

/-- Two states with the same words are the same state. -/
theorem state_ext {A B : State} (h : wordsOf A = wordsOf B) : A = B := by
  apply Vector.ext
  intro x hx
  apply Vector.ext
  intro y hy
  exact ofLane_inj (congrFun (congrFun h ⟨x, hx⟩) ⟨y, hy⟩)

/-! ## θ (§3.2.1)

The column parity `C x` and the mixing term `D x = C (x-1) ⊕ rotl 1 (C (x+1))`.  `keccak.rs`
computes exactly these five `d` vectors up front and then defers the per-lane xor into
`chi_row!`; that deferral is a rearrangement of `θW` and is handled downstream. -/

/-- Column parity: the xor of a column's five lanes. -/
def parity (W : Words) (x : Fin 5) : BitVec 64 :=
  W x 0 ^^^ W x 1 ^^^ W x 2 ^^^ W x 3 ^^^ W x 4

/-- θ's mixing term. -/
def dTerm (W : Words) (x : Fin 5) : BitVec 64 :=
  parity W (x - 1) ^^^ (parity W (x + 1)).rotateLeft 1

def θW (W : Words) : Words := fun x y => W x y ^^^ dTerm W x

theorem wordsOf_θ (A : State) : wordsOf (θ A) = θW (wordsOf A) := by
  funext x y
  simp only [wordsOf_apply, θ, θW, dTerm, parity, Fin.getElem_fin, Vector.getElem_ofFn,
    Fin.eta, ofLane_xor, ofLane_rotateLeft, BitVec.xor_assoc]
  rfl

/-! ## ρ (§3.2.2) — rotate each lane by its offset -/

def ρW (W : Words) : Words := fun x y => (W x y).rotateLeft (ρ.Offsets[x][y] % 64)

theorem wordsOf_ρ (A : State) : wordsOf (ρ A) = ρW (wordsOf A) := by
  funext x y
  simp only [wordsOf_apply, ρ, ρW, Fin.getElem_fin, Vector.getElem_ofFn, ofLane_rotateLeft]

/-! ## π (§3.2.3) — the lane permutation -/

def πW (W : Words) : Words := fun x y => W (x + 3 * y) x

theorem wordsOf_π (A : State) : wordsOf (π A) = πW (wordsOf A) := by
  funext x y
  simp only [wordsOf_apply, π, πW, Fin.getElem_fin, Vector.getElem_ofFn, Fin.eta]

/-! ## χ (§3.2.4) — the only nonlinear step

`(¬a) ∧ b` is one `vpandn`, which is why `keccak.rs` writes it in that order. -/

def χW (W : Words) : Words := fun x y => W x y ^^^ ((~~~W (x + 1) y) &&& W (x + 2) y)

theorem wordsOf_χ (A : State) : wordsOf (χ A) = χW (wordsOf A) := by
  funext x y
  simp only [wordsOf_apply, χ, χW, Fin.getElem_fin, Vector.getElem_ofFn, Fin.eta, ofLane_xor,
    ofLane_and, ofLane_not]

/-! ## ι (§3.2.5) — the round constant, added to lane (0, 0) only -/

/-- The round constant as a word.  `keccak::round_const` broadcasts `RC[24 - ROUNDS + round]`
across the four sponges; that it is *this* word is `Const.lean`'s business. -/
def rcWord (iᵣ : Nat) : BitVec 64 := ofLane (ι.RC iᵣ)

def ιW (W : Words) (iᵣ : Nat) : Words :=
  fun x y => if x = 0 ∧ y = 0 then W x y ^^^ rcWord iᵣ else W x y

theorem wordsOf_ι (A : State) (iᵣ : Nat) : wordsOf (ι A iᵣ) = ιW (wordsOf A) iᵣ := by
  funext x y
  simp only [wordsOf_apply, ι, ιW, rcWord, Fin.getElem_fin, Vector.getElem_ofFn, Fin.eta]
  split
  · exact ofLane_xor _ _
  · rfl

/-! ## The round -/

def RndW (W : Words) (iᵣ : Nat) : Words := ιW (χW (πW (ρW (θW W)))) iᵣ

/-- **The spec round is the word round.**  Everything above, composed. -/
theorem wordsOf_Rnd (A : State) (iᵣ : Nat) : wordsOf (Rnd A iᵣ) = RndW (wordsOf A) iᵣ := by
  simp only [Rnd, RndW, wordsOf_ι, wordsOf_χ, wordsOf_π, wordsOf_ρ, wordsOf_θ]

/-! ## Iterated rounds

`KECCAK_p nr` runs `Rnd` at spec round indices `12 + 2ℓ - nr … 12 + 2ℓ`.  `keccak.rs::permute`
runs the same sequence two rounds at a time, ping-ponging between two register arrays, so what
its loop invariant needs is "`n` rounds starting at `start`" as a function of the state. -/

/-- `n` rounds of `RndW`, starting from spec round index `start`. -/
def rounds (W : Words) (start : ℕ) : ℕ → Words
  | 0 => W
  | n + 1 => rounds (RndW W start) (start + 1) n

@[simp] theorem rounds_zero (W : Words) (start : ℕ) : rounds W start 0 = W := rfl

theorem rounds_succ (W : Words) (start n : ℕ) :
    rounds W start (n + 1) = rounds (RndW W start) (start + 1) n := rfl

/-- Two rounds at a time — the step `permute`'s loop body takes. -/
theorem rounds_two (W : Words) (start n : ℕ) :
    rounds W start (n + 2) = rounds (RndW (RndW W start) (start + 1)) (start + 2) n := rfl

end Kopis.Keccak
