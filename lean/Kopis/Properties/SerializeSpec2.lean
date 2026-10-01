import Kopis.Properties.SerializeSpec
open Aeneas Aeneas.Std Result
open scoped BigOperators
namespace Kopis.Properties

set_option maxHeartbeats 2000000
set_option maxRecDepth 4000

/-- **The serialize bit-correspondence.**  Bit `j` of byte `p` of `serialize_elem n r` is bit
`(8p+j) mod n` of coefficient `(8p+j)/n`. -/
theorem serialize_byte_bit (n : ℕ) (r : Spec.Kopis.Poly (2 ^ n)) (p j : ℕ)
    (hp : p < 32 * n) (hj : j < 8) (hn : 0 < n) :
    ((Spec.Kopis.Explicit.serialize_elem n r)[p]'hp).toNat.testBit j
      = (r[(8 * p + j) / n]'(by rw [Nat.div_lt_iff_lt_mul hn]; omega)).val.testBit
          ((8 * p + j) % n) :=
  Spec.Kopis.Explicit.serialize_elem_testBit n r p j hp hj hn

/-- Spec-side byte value: byte `p` of `serialize_elem n r` is byte `p` of the packed bit-stream
`∑ᵢ r[i].val · 2^(n·i)`. -/
theorem serialize_byteVal (n : ℕ) (r : Spec.Kopis.Poly (2 ^ n)) (p : ℕ)
    (hp : p < 32 * n) (hn : 0 < n) :
    ((Spec.Kopis.Explicit.serialize_elem n r)[p]'hp).toNat
      = (∑ i ∈ Finset.range 256, (r[i]!).val * 2 ^ (n * i)) / 256 ^ p % 256 := by
  haveI : NeZero (2 ^ n) := ⟨by positivity⟩
  apply byte_eq
  · exact ((Spec.Kopis.Explicit.serialize_elem n r)[p]'hp).isLt
  · exact Nat.mod_lt _ (by norm_num)
  · intro j hj
    rw [serialize_byte_bit n r p j hp hj hn, byte_testBit _ p j hj]
    set q := (8 * p + j) / n with hqdef
    set s := (8 * p + j) % n with hsdef
    have hq_lt : q < 256 := by rw [hqdef, Nat.div_lt_iff_lt_mul hn]; omega
    have hs_lt : s < n := by rw [hsdef]; exact Nat.mod_lt _ hn
    have hqs : n * q + s = 8 * p + j := by rw [hqdef, hsdef]; exact Nat.div_add_mod _ _
    have hpk := packed_testBit (fun i => (r[i]!).val) n 256
      (fun i => by simpa using ZMod.val_lt (r[i]!)) q s hs_lt hq_lt
    rw [hqs] at hpk
    rw [hpk]
    exact (congrArg (fun z => z.val.testBit s) (getElem!_pos r q hq_lt)).symm
