/-
  # Kopis/Keccak/KPBridge.lean — the spec's permutation is the twelve register rounds.

  `SpecState.lean` says the two *states* are the same object.  This file says the two *maps* on
  them are the same: one `Spec.TurboSHAKE.KP_bytes` is twelve `RndW` rounds at spec indices
  12 … 23, which is what `Permute.lean` proves `keccak::permute` computes.

  Three steps, each of which could hide a mistake and none of which does:

  * `KECCAK_p 12` is written as a `for` loop inside `Id.run`.  `simp [Id.run]` turns that into a
    `List.foldl` over `List.range' 12 12` — do *not* try to `rfl` it, which unfolds `Rnd` itself
    and does not terminate.
  * §3.1.2 and §3.1.3 (`stringToState` / `stateToString`) are inverse, so the round-trip inside
    `KECCAK_p` is the identity.
  * `bytesToBits` and `bitsToBytes` are inverse, which `Spec/Defs.lean` already proves.

  Note this is deeper than the serial stack goes: there, the `turboshake` crate's conformance is
  assumed.  Here the permutation itself is proved.
-/
import Kopis.Keccak.SpecState
import Spec.TurboSHAKE.Spec

open Aeneas Aeneas.Std
open Spec.SHA3
open Spec (𝔹 bytesToBits bitsToBytes)
open scoped Spec.Notations

namespace Kopis.Keccak

set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

noncomputable section

/-- `n` rounds of `Rnd` from spec index `start` — the `State`-level twin of `rounds`. -/
def RndIter (A : State) (start : ℕ) : ℕ → State
  | 0 => A
  | n + 1 => RndIter (Rnd A start) (start + 1) n

theorem wordsOf_RndIter (A : State) (start n : ℕ) :
    wordsOf (RndIter A start n) = rounds (wordsOf A) start n := by
  induction n generalizing A start with
  | zero => rfl
  | succ m ih => rw [RndIter, rounds_succ, ih, wordsOf_Rnd]

/-- Iterating `Rnd` is the fold the spec's `for` loop reduces to. -/
theorem RndIter_eq_foldl (A : State) (start n : ℕ) :
    RndIter A start n = List.foldl (fun B i => Rnd B i) A (List.range' start n) := by
  induction n generalizing A start with
  | zero => rfl
  | succ m ih => rw [RndIter, List.range'_succ, List.foldl_cons, ih]

/-- **`KECCAK_p 12` is twelve rounds at spec indices 12 … 23**, sandwiched between the two
string/state conversions.  The spec writes the rounds as a `for` loop inside `Id.run`; `simp`
turns that into a `List.foldl` over `List.range'`, which is what `RndIter` unrolls to. -/
theorem KECCAK_p_12_eq (S : Vector Bool b) :
    KECCAK_p 12 S = stateToString (RndIter (stringToState S) 12 12) := by
  rw [RndIter_eq_foldl]
  simp [KECCAK_p, Id.run, ℓ]
  rfl

/-- §3.1.2 and §3.1.3 are inverse. -/
theorem stringToState_stateToString (A : State) : stringToState (stateToString A) = A := by
  apply Vector.ext; intro x hx
  apply Vector.ext; intro y hy
  apply Vector.ext; intro z hz
  have hz64 : z < 64 := hz
  have hx5 : x < 5 := hx
  have hy5 : y < 5 := hy
  have hd : (64 * (5 * y + x) + z) / 64 = 5 * y + x := by omega
  have e1 : (64 * (5 * y + x) + z) / 64 % 5 = x := by rw [hd]; omega
  have e2 : (64 * (5 * y + x) + z) / 64 / 5 = y := by rw [hd]; omega
  have e3 : (64 * (5 * y + x) + z) % 64 = z := by omega
  simp only [stringToState, stateToString, Vector.getElem_ofFn, w, e1, e2, e3]

/-- **One `KP_bytes` is twelve `RndW` rounds on the word view.**  This is the last link: the
spec's byte-level permutation and `keccak.rs`'s twelve register rounds are the same map. -/
theorem wordsOf_KP_bytes (B : 𝔹 200) :
    wordsOf (stringToState (bytesToBits (Spec.TurboSHAKE.KP_bytes B)))
      = rounds (wordsOf (stringToState (bytesToBits B))) 12 12 := by
  rw [Spec.TurboSHAKE.KP_bytes, Spec.TurboSHAKE.KP, Spec.bytesToBits_bitsToBytes,
    KECCAK_p_12_eq, stringToState_stateToString, wordsOf_RndIter]

/-- …and in the byte view the register array uses: `leWordB` of the permuted state is `rounds`
applied to `leWordB` of the original. -/
theorem leWordB_KP_bytes (B : 𝔹 200) (x y : Fin 5) :
    leWordB (Spec.TurboSHAKE.KP_bytes B) (8 * idx x y)
      = rounds (fun x' y' => leWordB B (8 * idx x' y')) 12 12 x y := by
  rw [← ofLane_stringToState, ← wordsOf_stringToState, ← wordsOf_apply, wordsOf_KP_bytes]

end
end Kopis.Keccak
