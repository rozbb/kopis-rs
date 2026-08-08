/-
  # Kopis/Keccak/Squeeze.lean — the squeeze stream, as a function of the `Words` state.

  Both backends read their register array out the same way: byte `k` of the state is byte `k % 8`
  of lane `k / 8`, and the stream emits `RATE` bytes per permutation.  Neither notion mentions a
  register width, so both live here, and each backend only has to say that its own register array
  reads as these `Words`.
-/
import Kopis.Keccak.Round

open Aeneas Aeneas.Std
open Kopis.Bits
open Spec.SHA3

namespace Kopis.Keccak

noncomputable section

/-- Byte `k` of a `Words` state: byte `k % 8` of lane `k / 8`, with the flat index read back to
coordinates by `coordX`/`coordY`.  The `Words`-level twin of `stateByte`. -/
def wordByte (W : Words) (k : ℕ) : BitVec 8 :=
  laneOf 8 (W (coordX (k / 8)) (coordY (k / 8))) (k % 8)

/-- The sponge state after `n` squeeze permutations. -/
def sqState (W : Words) : ℕ → Words
  | 0 => W
  | n + 1 => rounds (sqState W n) 12 12

@[simp] theorem sqState_zero (W : Words) : sqState W 0 = W := rfl

theorem sqState_succ (W : Words) (n : ℕ) :
    sqState W (n + 1) = rounds (sqState W n) 12 12 := rfl

/-- Squeezing `n+1` times from `W` is squeezing `n` times from the once-permuted state — the
form the outer loop's induction needs, since it permutes and then recurses. -/
theorem sqState_succ' (W : Words) (n : ℕ) :
    sqState W (n + 1) = sqState (rounds W 12 12) n := by
  induction n with
  | zero => rfl
  | succ m ih => rw [sqState_succ, ih, sqState_succ]

/-- **Byte `k` of the squeeze stream.**  Block `k / RATE` comes from the state permuted
`k / RATE + 1` times — the Rust permutes at the top of each output block, and the spec's `absorb`
ends with a permutation before `squeeze` emits, so the two agree on the first block too. -/
def squeezeByte (W : Words) (RATE k : ℕ) : BitVec 8 :=
  wordByte (sqState W (k / RATE + 1)) (k % RATE)

end

end Kopis.Keccak
