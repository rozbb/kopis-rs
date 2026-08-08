/-
  # Kopis/Keccak/Bytes.lean — bytes, little-endian words, and the padded block.

  FIPS 202 §B.1's byte-to-bit-string convention, the one-block `pad10*1` RFC 9861 uses, and the
  state a padded block absorbs to.  None of it mentions a register width, so it is shared.

  `Kopis/Avx2/Keccak/Absorb.lean` still carries its own copies from before this file existed.
-/
import Kopis.Keccak.Round

open Aeneas Aeneas.Std

namespace Kopis.Keccak

open Spec.SHA3

noncomputable section

/-- The little-endian 64-bit word at byte offset `off` of a byte list.  Byte `i` contributes bits
`8i … 8i+7`, LSB first. -/
def leWord64 (bs : List Std.U8) (off : ℕ) : BitVec 64 :=
  BitVec.ofFn fun z => ((bs[off + z.val / 8]!).bv).getLsbD (z.val % 8)

theorem getLsbD_leWord64 (bs : List Std.U8) (off z : ℕ) (hz : z < 64) :
    (leWord64 bs off).getLsbD z = ((bs[off + z / 8]!).bv).getLsbD (z % 8) := by
  rw [BitVec.getLsbD_eq_getElem hz, leWord64, BitVec.getElem_ofFn]

/-- Byte `j` of the padded block: the 32-byte prefix, the suffix, the domain separator, zeros,
and `0x80` in the last byte. -/
def padByte (RATE : ℕ) (DS : Std.U8) (pre suf : List Std.U8) (j : ℕ) : Std.U8 :=
  if j < 32 then pre[j]!
  else if j < 32 + suf.length then suf[j - 32]!
  else if j = 32 + suf.length then DS
  else if j = RATE - 1 then 128#u8
  else 0#u8

/-- The little-endian 64-bit word at byte offset `off` of a byte *function* — the same reading as
`leWord64`, but of something described pointwise rather than stored in a list. -/
def leWordOf (f : ℕ → Std.U8) (off : ℕ) : BitVec 64 :=
  BitVec.ofFn fun z => ((f (off + z.val / 8)).bv).getLsbD (z.val % 8)

theorem leWord64_eq_leWordOf (bs : List Std.U8) (f : ℕ → Std.U8) (off : ℕ)
    (h : ∀ m < 8, bs[off + m]! = f (off + m)) :
    leWord64 bs off = leWordOf f off := by
  apply BitVec.eq_of_getLsbD_eq
  intro z hz
  rw [getLsbD_leWord64 _ _ _ hz, leWordOf, BitVec.getLsbD_eq_getElem hz, BitVec.getElem_ofFn,
    h (z / 8) (by omega)]

/-- **The state after absorbing one padded block.**  Register `k` is the little-endian word at
byte offset `8k` of the block for `8k < RATE`, and zero above that — the capacity, which the
sponge never touches on absorb. -/
def absorbed (RATE : ℕ) (DS : Std.U8) (pre suf : List Std.U8) : Words :=
  fun x y => if 8 * idx x y < RATE then leWordOf (padByte RATE DS pre suf) (8 * idx x y) else 0

end

end Kopis.Keccak
