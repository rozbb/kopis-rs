/-
  # Kopis/Avx2/SerLane.lean — one `vpshufb`/`vpsrlvd`/`vpand` lane is one coefficient.

  This is the mathematical core of the AVX2 deserializer's correctness, isolated from the loops
  and from the construction of the constant tables so that it can be read on its own.

  `src/backend/avx2/ser.rs` extracts eight coefficients at a time.  It broadcasts the group's 16
  bytes into both 128-bit halves, uses one `vpshufb` to bring, into 32-bit lane `k`, the four
  bytes starting at that coefficient's first byte, shifts lane `k` down by the coefficient's bit
  offset within that byte, and masks to `bits` bits.  The claim proved here is that lane `k` then
  holds

      streamNat bytes (bits · (8·group + k)) bits

  — coefficient `8·group + k` of the little-endian bit stream, which is what the portable
  unpacker produces.

  Two arithmetic facts do all the work, and both are visible in `plan`:

  * coefficient `k` of a group starts at byte `⌊k·bits/8⌋` and bit `(k·bits) % 8` *of the group*,
    and `8·⌊k·bits/8⌋ + (k·bits) % 8 = k·bits` puts it back at bit `k·bits`;
  * a four-byte window always covers it, since `bits ≤ 13` and the bit offset is at most 7.

  The lane is stated over `streamByte`, which reads out of range as zero — which is what makes
  the head path and the zero-padded tail path the same argument rather than two.
-/
import Kopis.Avx2.Model
import Kopis.Bits.Stream

open Aeneas Aeneas.Std Result

namespace Kopis.Avx2

open Kopis.Properties (streamNat streamByte streamNat_of_byteWindow sum_base256)

/-! ## Lanes as numbers

The intrinsic axioms are stated on `BitVec` lanes and the bit stream on `ℕ`; these three lemmas
are the whole of the translation. -/

/-- A lane, as a number: lane `i` of width `w` is the corresponding field of `x.toNat`. -/
theorem toNat_laneOf {n : ℕ} (w : ℕ) (x : BitVec n) (i : ℕ) :
    (laneOf w x i).toNat = x.toNat >>> (w * i) % 2 ^ w := rfl

/-- A 32-bit lane is its four bytes, little-endian — the step from `vpshufb`'s byte-level
specification to `vpsrlvd`'s 32-bit-lane one. -/
theorem toNat_lane32_eq_bytes {n : ℕ} (x : BitVec n) (k : ℕ) :
    (laneOf 32 x k).toNat = ∑ b ∈ Finset.range 4, (laneOf 8 x (4 * k + b)).toNat * 256 ^ b := by
  simp only [toNat_laneOf]
  rw [show (2:ℕ) ^ 32 = 256 ^ 4 from by norm_num, ← sum_base256]
  apply Finset.sum_congr rfl
  intro b _
  congr 2
  rw [show 8 * (4 * k + b) = 32 * k + 8 * b from by ring, Nat.shiftRight_add]

/-- Masking to `w` bits is reduction mod `2 ^ w`, at the level of `BitVec.toNat`. -/
theorem toNat_and_mask {n : ℕ} (x y : BitVec n) (w : ℕ) (hy : y.toNat = 2 ^ w - 1) :
    (x &&& y).toNat = x.toNat % 2 ^ w := by
  rw [BitVec.toNat_and, hy, Nat.and_two_pow_sub_one_eq_mod]

/-! ## The plan entries

`src/backend/avx2/ser.rs` computes these in a `const fn`; `Kopis/Avx2/SerPlan.lean` proves the
extracted table holds exactly them.  They are defined here because the lane lemma below is
stated through them. -/

/-- Byte `b` of the shuffle control for lane `k` at width `w`: coefficient `k` starts at byte
`⌊k·w/8⌋` of the group, and the window is the four bytes from there. -/
def planShuffle (w k b : ℕ) : ℕ := k * w / 8 + b

/-- The `vpsrlvd` count for lane `k` at width `w`: the coefficient's bit offset within its
first byte. -/
def planShift (w k : ℕ) : ℕ := k * w % 8

/-- The two together put coefficient `k` back at bit `k·w` of the group — the identity the
whole scheme rests on. -/
theorem planShuffle_planShift (w k : ℕ) : 8 * planShuffle w k 0 + planShift w k = k * w := by
  unfold planShuffle planShift
  omega

/-- The shuffle control never leaves its own 128-bit half: `⌊7·13/8⌋ + 3 = 14`. -/
theorem planShuffle_lt (w k b : ℕ) (hw : w ≤ 13) (hk : k < 8) (hb : b < 4) :
    planShuffle w k b < 16 := by
  have : k * w ≤ 7 * 13 := Nat.mul_le_mul (by omega) hw
  unfold planShuffle
  omega

/-! ## One lane is one coefficient

The three instructions `vpshufb`, `vpsrlvd`, `vpand`, applied to a register holding a group's
bytes in both halves, put coefficient `8·group + k` of the bit stream in 32-bit lane `k`.

The hypotheses are the *model* equations, which `Kopis/Avx2/Model.lean` derives from the
intrinsic axioms — so this lemma consumes the trust base exactly once, in the form that was
differential-tested. -/

open RustKopisAvx2.backend.avx2.intrinsics in
theorem lane_chain_value
    (bytes : Slice U8) (w : ℕ) (hw13 : w ≤ 13) (group : ℕ)
    (raw shuffleV shiftV maskV windows shifted out : Vec256)
    (hraw : ∀ i < 32, (lane8 raw i).toNat = streamByte bytes (group * w + i % 16))
    (hshuf : ∀ i < 32, (lane8 shuffleV i).toNat = planShuffle w (i / 4) (i % 4))
    (hshiftV : ∀ m < 8, (lane32 shiftV m).toNat = planShift w m)
    (hmask : ∀ m < 8, (lane32 maskV m).toNat = 2 ^ w - 1)
    (hwin : bits windows = Model.shuffleEpi8 (bits raw) (bits shuffleV))
    (hsh : bits shifted = Model.srlvEpi32 (bits windows) (bits shiftV))
    (hout : bits out = Model.andSi256 (bits shifted) (bits maskV)) :
    ∀ k < 8, (lane32 out k).toNat = streamNat bytes (w * (8 * group + k)) w := by
  intro k hk
  -- `vpand`: lane `k` is lane `k` of the shifted vector, reduced mod `2 ^ w`
  have h1 : (lane32 out k).toNat = (lane32 shifted k).toNat % 2 ^ w := by
    have hl : lane32 out k = lane32 shifted k &&& lane32 maskV k := by
      show laneOf 32 (bits out) k = _
      rw [hout]
      simp only [Model.andSi256]
      exact laneOf_and 32 (bits shifted) (bits maskV) k
    rw [hl, toNat_and_mask _ _ w (hmask k hk)]
  -- `vpsrlvd`: lane `k` is lane `k` of the windows, shifted by that lane's count
  have h2 : (lane32 shifted k).toNat = (lane32 windows k).toNat >>> planShift w k := by
    have hl : lane32 shifted k = lane32 windows k >>> (lane32 shiftV k).toNat := by
      show laneOf 32 (bits shifted) k = _
      rw [hsh]
      simp only [Model.srlvEpi32]
      exact laneOf_ofLanes32 _ hk
    rw [hl, BitVec.toNat_ushiftRight, hshiftV k hk]
  -- `vpshufb`: byte `b` of lane `k` is the group's byte `⌊k·w/8⌋ + b`
  have h3 : ∀ b < 4, (lane8 windows (4 * k + b)).toNat
      = streamByte bytes (group * w + planShuffle w k b) := by
    intro b hb
    have hi : 4 * k + b < 32 := by omega
    have hctrl : (lane8 shuffleV (4 * k + b)).toNat = planShuffle w k b := by
      rw [hshuf _ hi, show (4 * k + b) / 4 = k from by omega, show (4 * k + b) % 4 = b from by omega]
    have hp16 : planShuffle w k b < 16 := planShuffle_lt w k b hw13 (by omega) hb
    have hbit7 : (lane8 shuffleV (4 * k + b)).getLsbD 7 = false := by
      show (lane8 shuffleV (4 * k + b)).toNat.testBit 7 = false
      rw [hctrl]
      exact Nat.testBit_lt_two_pow (by omega)
    have hand : ((lane8 shuffleV (4 * k + b)) &&& 0x0F#8).toNat = planShuffle w k b := by
      rw [BitVec.toNat_and, hctrl, show (0x0F#8 : BitVec 8).toNat = 2 ^ 4 - 1 from rfl,
        Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt (by omega)]
    have hl : lane8 windows (4 * k + b)
        = lane8 raw (16 * ((4 * k + b) / 16) + planShuffle w k b) := by
      show laneOf 8 (bits windows) _ = _
      rw [hwin]
      simp only [Model.shuffleEpi8]
      rw [laneOf_ofLanes8 _ hi, if_neg (by simpa using hbit7), hand]
    rw [hl, hraw _ (by omega)]
    congr 2
    omega
  -- the four bytes assemble into the lane
  have h4 : (lane32 windows k).toNat
      = ∑ b ∈ Finset.range 4, streamByte bytes (group * w + k * w / 8 + b) * 256 ^ b := by
    rw [toNat_lane32_eq_bytes]
    apply Finset.sum_congr rfl
    intro b hb
    rw [h3 b (Finset.mem_range.mp hb)]
    unfold planShuffle
    congr 2
    omega
  -- and the window is the coefficient
  rw [h1, h2, h4,
    ← streamNat_of_byteWindow bytes (group * w + k * w / 8) (planShift w k) w
      (by unfold planShift; omega)]
  congr 1
  have h8 : 8 * (k * w / 8) + k * w % 8 = k * w := Nat.div_add_mod (k * w) 8
  calc 8 * (group * w + k * w / 8) + planShift w k
      = 8 * group * w + (8 * (k * w / 8) + k * w % 8) := by unfold planShift; ring
    _ = 8 * group * w + k * w := by rw [h8]
    _ = w * (8 * group + k) := by ring

/-! ## Reassembling two groups into sixteen coefficients

`vpackusdw` narrows two vectors of eight 32-bit lanes into one of sixteen 16-bit lanes, but
interleaved by 128-bit half: the result holds `a[0..3], b[0..3], a[4..7], b[4..7]`.  The
following `vpermq` with immediate `0b11_01_10_00` swaps the middle two 64-bit lanes, which puts
it back in order — `a[0..7]` then `b[0..7]`.  That is the whole of the last two instructions in
the loop body, and it is where an off-by-one would silently transpose coefficients.

The saturation is exact because every lane is a `bits`-bit field with `bits ≤ 13`. -/

/-- Which 64-bit lane of the source `vpermq`'s immediate `0b11_01_10_00` takes for each
destination lane. -/
def permQ : ℕ → ℕ
  | 0 => 0
  | 1 => 2
  | 2 => 1
  | _ => 3

theorem permQ_eq (q : ℕ) (hq : q < 4) :
    ((216#i32).bv >>> (2 * q) &&& 3#32).toNat = permQ q := by
  rcases show q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 from by omega with rfl | rfl | rfl | rfl <;> rfl

/-- `vpackusdw` saturates to `u16`, which is exact on a value that already fits in 13 bits. -/
theorem satU_of_lt (x : BitVec 32) (h : x.toNat < 2 ^ 13) : (satU x).toNat = x.toNat := by
  have hpos : (0:ℤ) ≤ x.toInt := by
    rw [BitVec.toInt_eq_toNat_cond]
    split <;> omega
  have hsmall : ¬ (65535 < x.toInt) := by
    rw [BitVec.toInt_eq_toNat_cond]
    split <;> omega
  unfold satU
  rw [if_neg (by omega), if_neg hsmall, BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)]

open RustKopisAvx2.backend.avx2.intrinsics in
theorem pack_permute_value (wide0 wide1 packed res : Vec256)
    (hb0 : ∀ m < 8, (lane32 wide0 m).toNat < 2 ^ 13)
    (hb1 : ∀ m < 8, (lane32 wide1 m).toNat < 2 ^ 13)
    (hpack : bits packed = Model.packusEpi32 (bits wide0) (bits wide1))
    (hres : bits res = Model.permute4x64Epi64 (216#i32).bv (bits packed)) :
    ∀ j < 16, (lane16 res j).toNat
      = if j < 8 then (lane32 wide0 j).toNat else (lane32 wide1 (j - 8)).toNat := by
  intro j hj
  -- the `vpermq` moves 64-bit lane `permQ (j / 4)` of `packed` to lane `j / 4`
  have h1 : laneOf 16 (bits res) j = laneOf 16 (laneOf 64 (bits res) (j / 4)) (j % 4) :=
    laneOf_laneOf 16 4 (bits res) j (by omega)
  have h2 : laneOf 64 (bits res) (j / 4) = laneOf 64 (bits packed) (permQ (j / 4)) := by
    rw [hres]
    simp only [Model.permute4x64Epi64]
    rw [laneOf_ofLanes64 _ (by omega), permQ_eq _ (by omega)]
  have hd : (4 * permQ (j / 4) + j % 4) / 4 = permQ (j / 4) := by omega
  have hm : (4 * permQ (j / 4) + j % 4) % 4 = j % 4 := by omega
  have h3 : laneOf 16 (bits packed) (4 * permQ (j / 4) + j % 4)
      = laneOf 16 (laneOf 64 (bits packed) (permQ (j / 4))) (j % 4) := by
    rw [laneOf_laneOf 16 4 (bits packed) (4 * permQ (j / 4) + j % 4) (by omega), hd, hm]
  have hstep : lane16 res j = lane16 packed (4 * permQ (j / 4) + j % 4) := by
    show laneOf 16 (bits res) j = laneOf 16 (bits packed) _
    rw [h1, h2, h3]
  -- and `vpackusdw` puts `wide0` in the low half of each 128-bit half, `wide1` in the high half
  have hperm : permQ (j / 4) < 4 := by
    rcases show j / 4 = 0 ∨ j / 4 = 1 ∨ j / 4 = 2 ∨ j / 4 = 3 from by omega with
      h | h | h | h <;> rw [h] <;> simp [permQ]
  have hidx : 4 * permQ (j / 4) + j % 4 < 16 := by omega
  have hpk : lane16 packed (4 * permQ (j / 4) + j % 4)
      = (let i := 4 * permQ (j / 4) + j % 4
         if i % 8 < 4 then satU (laneOf 32 (bits wide0) (4 * (i / 8) + i % 8))
         else satU (laneOf 32 (bits wide1) (4 * (i / 8) + (i % 8 - 4)))) := by
    show laneOf 16 (bits packed) _ = _
    rw [hpack]
    simp only [Model.packusEpi32]
    exact laneOf_ofLanes16 _ hidx
  rw [hstep, hpk]
  -- sixteen concrete cases; in each, the two index computations agree
  clear hstep hpk h1 h2 h3 hidx hperm hpack hres
  rcases show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 ∨
      j = 10 ∨ j = 11 ∨ j = 12 ∨ j = 13 ∨ j = 14 ∨ j = 15 from by omega with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl <;>
    simp only [permQ] <;>
    norm_num <;>
    first
      | exact satU_of_lt _ (hb0 _ (by norm_num))
      | exact satU_of_lt _ (hb1 _ (by norm_num))

end Kopis.Avx2
