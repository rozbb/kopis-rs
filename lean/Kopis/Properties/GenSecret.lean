import Kopis.Properties.RingArith
import Kopis.Properties.GenMatrix
import Spec.Kopis.Spec
import Kopis.Properties.Serialize
open Aeneas Aeneas.Std Result RustKopisSerial
open scoped BigOperators
namespace Kopis.Properties

set_option maxHeartbeats 1000000

/-! ## `count_ones` (popcount) — opaque compiler intrinsics, axiomatized as the
number of set bits (= sum of the bit values). -/

@[step] axiom U16.count_ones_spec (x : U16) :
    core.num.U16.count_ones x
      ⦃ (r : U32) => r.val = ∑ i ∈ Finset.range 16, (x.bv.getLsbD i).toNat ⦄

@[step] axiom U8.count_ones_spec (x : U8) :
    core.num.U8.count_ones x
      ⦃ (r : U32) => r.val = ∑ i ∈ Finset.range 8, (x.bv.getLsbD i).toNat ⦄

/-- Popcount of `w` masked to its low `h` bits (`mask = 2^h - 1`) is the sum of
the low `h` bits of `w`. -/
theorem popcount_low_mask (w mask : U16) (h : ℕ) (hh : h ≤ 16)
    (hmask : ∀ i, mask.bv.getLsbD i = decide (i < h)) :
    ∑ i ∈ Finset.range 16, ((w &&& mask).bv.getLsbD i).toNat
      = ∑ i ∈ Finset.range h, (w.bv.getLsbD i).toNat := by
  have hstep : ∀ i, ((w &&& mask).bv.getLsbD i).toNat
      = if i < h then (w.bv.getLsbD i).toNat else 0 := by
    intro i
    rw [show (w &&& mask).bv = w.bv &&& mask.bv from rfl, BitVec.getLsbD_and, hmask i]
    by_cases hi : i < h <;> simp [hi]
  rw [Finset.sum_congr rfl (fun i _ => hstep i), ← Finset.sum_filter]
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_range]
  omega

/-- The mask `2^half - 1` has bit `i` set iff `i < half`. -/
theorem mask_getLsbD (mask : U16) (half : ℕ) (hm : mask.val = 2 ^ half - 1) (i : ℕ) :
    mask.bv.getLsbD i = decide (i < half) := by
  have h : mask.bv.getLsbD i = mask.val.testBit i := by rw [UScalar.val, BitVec.getLsbD]
  rw [h, hm, Nat.testBit_two_pow_sub_one]

/-- `u16::wrapping_sub` cast into `ZMod (2¹³)` is the `ZMod` difference (the wrap
`% 2¹⁶` is absorbed since `2¹³ ∣ 2¹⁶`). -/
theorem wrapping_sub_toZMod13 (a b : U16) :
    (((core.num.U16.wrapping_sub a b).val : ℕ) : ZMod (2 ^ 13))
      = (a.val : ZMod (2 ^ 13)) - (b.val : ZMod (2 ^ 13)) := by
  have hsize : UScalar.size .U16 = 2 ^ 16 := by rw [UScalar.size_def]; rfl
  have hy : b.val ≤ 2 ^ 16 := by have := U16.lt_succ_max b; omega
  have h216 : ((2 ^ 16 : ℕ) : ZMod (2 ^ 13)) = 0 := by
    rw [show (2 : ℕ) ^ 16 = 2 ^ 13 * 8 from by norm_num, Nat.cast_mul, ZMod.natCast_self, zero_mul]
  have castMod : ∀ x : ℕ, ((x % 2 ^ 16 : ℕ) : ZMod (2 ^ 13)) = (x : ZMod (2 ^ 13)) := fun x => by
    conv_rhs => rw [← Nat.mod_add_div x (2 ^ 16)]
    push_cast; ring
  rw [core.num.U16.wrapping_sub_val_eq, hsize, castMod, Nat.cast_add, Nat.cast_sub hy, h216]
  ring

end Kopis.Properties
