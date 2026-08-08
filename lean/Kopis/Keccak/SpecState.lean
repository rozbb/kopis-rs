/-
  # Kopis/Keccak/SpecState.lean — the register state and the sponge state are the same state.

  `Spec/TurboSHAKE/Spec.lean` keeps the sponge state as 200 bytes and reaches the permutation
  through `bytesToBits` / `stringToState`.  `keccak.rs` keeps it as 25 registers, each holding one
  64-bit lane of four sponges.  This file is the one lemma that says those are the same object,
  and it is the place an endianness error would have to hide, so it is worth stating exactly what
  makes it true:

  * FIPS 202 §B.1 (`bytesToBits`) lays byte `i` out at bit positions `8i … 8i+7`, **LSB first**;
  * §3.1.2 (`stringToState`) puts bit `z` of lane `(x, y)` at position `64·(5y + x) + z`.

  Composing them, lane `(x, y)` is the little-endian 64-bit word at byte offset `8·(5y + x)` —
  which is `leWordB` at `8 * idx x y`, and `idx` is the same flat index `keccak.rs` stores the
  lane at.  There is no byte reversal at any step, and `Bytes.lean`'s `leWord64` is the same
  reading of the input blocks, so absorb, permute and squeeze all agree.
-/
import Kopis.Keccak.Bytes
import Spec.TurboSHAKE.Spec

open Aeneas Aeneas.Std
open Spec.SHA3
open Spec (𝔹 bytesToBits)
open scoped Spec.Notations

namespace Kopis.Keccak

set_option maxHeartbeats 1000000

noncomputable section

/-- The little-endian 64-bit word at byte offset `off` of a spec byte vector. -/
def leWordB {n : ℕ} (B : 𝔹 n) (off : ℕ) : BitVec 64 :=
  BitVec.ofFn fun z => (B[off + z.val / 8]!).getLsbD (z.val % 8)

theorem getLsbD_leWordB {n : ℕ} (B : 𝔹 n) (off z : ℕ) (hz : z < 64) :
    (leWordB B off).getLsbD z = (B[off + z / 8]!).getLsbD (z % 8) := by
  rw [BitVec.getLsbD_eq_getElem hz, leWordB, BitVec.getElem_ofFn]

/-- **The spec's byte state, read as words, is the register view.**  FIPS 202 §B.1 lays bytes out
LSB-first and §3.1.2 puts bit `z` of lane `(x, y)` at position `64·(5y+x) + z` of the 1600-bit
string, so lane `(x, y)` is the little-endian 64-bit word at byte offset `8·(5y+x)`.  No byte
reversal anywhere — this is the step where an endianness error would hide. -/
theorem ofLane_stringToState (B : 𝔹 200) (x y : Fin 5) :
    ofLane ((stringToState (bytesToBits B))[x][y]) = leWordB B (8 * idx x y) := by
  apply BitVec.eq_of_getLsbD_eq
  intro z hz
  rw [getLsbD_leWordB _ _ _ hz, getLsbD_ofLane _ z hz]
  have hx := x.isLt; have hy := y.isLt
  have hlt2 : (64 * (5 * y.val + x.val) + z) / 8 < 200 := by omega
  simp only [stringToState, bytesToBits, Vector.getElem_ofFn, Fin.getElem_fin, w]
  -- to `getElem!` first: the `getElem` form carries its bound proof, so rewriting the index
  -- under it hits a dependent motive
  rw [← getElem!_pos B ((64 * (5 * y.val + x.val) + z) / 8) hlt2,
      show (64 * (5 * y.val + x.val) + z) / 8 = 8 * idx x y + z / 8 from by
        simp only [idx]; omega,
      show (64 * (5 * y.val + x.val) + z) % 8 = z % 8 from by omega]
  simp only [BitVec.getLsbD]

/-- The same statement in `Words` form, which is what `RndW` and `rounds` are stated over. -/
theorem wordsOf_stringToState (B : 𝔹 200) :
    wordsOf (stringToState (bytesToBits B)) = fun x y => leWordB B (8 * idx x y) := by
  funext x y; exact ofLane_stringToState B x y

end
end Kopis.Keccak
