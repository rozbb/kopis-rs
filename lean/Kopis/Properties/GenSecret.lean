import Kopis.Properties.RingArith
import Kopis.Properties.GenMatrix
import Spec.Kopis.Spec
import Kopis.Properties.Serialize
open Aeneas Aeneas.Std Result RustKopis
open scoped BigOperators
namespace Kopis.Properties

set_option maxHeartbeats 1000000

/-! ## `count_ones` (popcount) — opaque compiler intrinsics, axiomatized as the
number of set bits (= sum of the bit values). -/

@[step] axiom U32.count_ones_spec (x : U32) :
    core.num.U32.count_ones x
      ⦃ (r : U32) => r.val = ∑ i ∈ Finset.range 32, (x.bv.getLsbD i).toNat ⦄

@[step] axiom U8.count_ones_spec (x : U8) :
    core.num.U8.count_ones x
      ⦃ (r : U32) => r.val = ∑ i ∈ Finset.range 8, (x.bv.getLsbD i).toNat ⦄

/-- Popcount of `w` masked to its low `h` bits (`mask = 2^h - 1`) is the sum of
the low `h` bits of `w`. -/
theorem popcount_low_mask (w mask : U32) (h : ℕ) (hh : h ≤ 32)
    (hmask : ∀ i, mask.bv.getLsbD i = decide (i < h)) :
    ∑ i ∈ Finset.range 32, ((w &&& mask).bv.getLsbD i).toNat
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

/-- The 3-byte little-endian window `buf[bi] + 2⁸·buf[bi+1] + 2¹⁶·buf[bi+2]`
(with OOB bytes read as 0 via `!`) has bit `b` (for `b < 16`) equal to the
corresponding stream bit `buf[(8bi+b)/8][(8bi+b)%8]`. -/
theorem window_testBit (buf : Slice U8) (bi b : ℕ) (hb : b < 24) :
    (((buf.val[bi]!).val) + 2 ^ 8 * (buf.val[bi+1]!).val + 2 ^ 16 * (buf.val[bi+2]!).val).testBit b
      = (buf.val[(8*bi+b)/8]!).val.testBit ((8*bi+b)%8) := by
  have h0 : (buf.val[bi]!).val < 2 ^ 8 := by have := (buf.val[bi]!).hBounds; omega
  have h1 : (buf.val[bi+1]!).val < 2 ^ 8 := by have := (buf.val[bi+1]!).hBounds; omega
  rw [show ((buf.val[bi]!).val) + 2 ^ 8 * (buf.val[bi+1]!).val + 2 ^ 16 * (buf.val[bi+2]!).val
        = 2 ^ 8 * ((buf.val[bi+1]!).val + 2 ^ 8 * (buf.val[bi+2]!).val) + (buf.val[bi]!).val from by ring,
    Nat.testBit_two_pow_mul_add _ h0 b]
  by_cases hb8 : b < 8
  · -- bit in the low byte
    rw [if_pos hb8, show (8*bi+b)/8 = bi from by omega, show (8*bi+b)%8 = b from by omega]
  · rw [if_neg hb8, show ((buf.val[bi+1]!).val + 2 ^ 8 * (buf.val[bi+2]!).val)
          = 2 ^ 8 * (buf.val[bi+2]!).val + (buf.val[bi+1]!).val from by ring,
      Nat.testBit_two_pow_mul_add _ h1 (b - 8)]
    by_cases hb16 : b < 16
    · -- second byte
      rw [if_pos (show b - 8 < 8 by omega),
        show (8*bi+b)/8 = bi+1 from by omega, show (8*bi+b)%8 = b-8 from by omega]
    · -- third byte
      rw [if_neg (show ¬ b - 8 < 8 by omega), show b - 8 - 8 = b - 16 from by omega,
        show (8*bi+b)/8 = bi+2 from by omega, show (8*bi+b)%8 = b-16 from by omega]

/-- The mask `2^half - 1` has bit `i` set iff `i < half`. -/
theorem mask_getLsbD (mask : U32) (half : ℕ) (hm : mask.val = 2 ^ half - 1) (i : ℕ) :
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

/-- **Bit heart of CBD.**  The popcount of the low `half` bits of the shifted
window `raw4 = W >> bit_in_byte` equals the spec's `∑ streamBit` over the
corresponding `half` stream positions. -/
theorem window_popcount (buf : Slice U8) (byte_idx off half : ℕ)
    (shifted : U32) (hoff : off + half ≤ 24) (hhalf : half ≤ 8)
    (hshift : shifted.val = ((buf.val[byte_idx]!).val + 2 ^ 8 * (buf.val[byte_idx+1]!).val
        + 2 ^ 16 * (buf.val[byte_idx+2]!).val) >>> off) :
    ∑ i ∈ Finset.range half, (shifted.bv.getLsbD i).toNat
      = ∑ i ∈ Finset.range half, streamBit buf (8 * byte_idx + off + i) := by
  apply Finset.sum_congr rfl
  intro i hi
  simp only [Finset.mem_range] at hi
  have hbridge : shifted.bv.getLsbD i = shifted.val.testBit i := by rw [UScalar.val, BitVec.getLsbD]
  rw [hbridge, hshift, Nat.testBit_shiftRight,
    window_testBit buf byte_idx (off + i) (by omega),
    show 8 * byte_idx + (off + i) = 8 * byte_idx + off + i from by ring]
  rfl

end Kopis.Properties
