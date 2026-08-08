/-
  # Kopis/Neon/SerLane.lean — one `tbl`/`ushl`/`and` lane is one coefficient.

  This is the mathematical core of the NEON deserializer's correctness, isolated from the loops
  and from the construction of the constant tables so that it can be read on its own.

  `src/backend/neon/ser.rs` extracts eight coefficients at a time, in two passes of four.  It
  loads the group's 16 bytes, uses one `tbl` to bring, into 32-bit lane `j`, the four bytes
  starting at that coefficient's first byte, shifts lane `j` down by the coefficient's bit offset
  within that byte, and masks to `bits` bits.  The claim proved here is that lane `j` then holds

      streamNat bytes (bits · (8·group + base + j)) bits

  — coefficient `8·group + base + j` of the little-endian bit stream, where `base` is 0 for the
  low pass and 4 for the high one.  That is what the portable unpacker produces.

  Two arithmetic facts do all the work, and both are visible in `plan`:

  * coefficient `k` of a group starts at byte `⌊k·bits/8⌋` and bit `(k·bits) % 8` *of the group*,
    and `8·⌊k·bits/8⌋ + (k·bits) % 8 = k·bits` puts it back at bit `k·bits`;
  * a four-byte window always covers it, since `bits ≤ 13` and the bit offset is at most 7.

  The lane is stated over `streamByte`, which reads out of range as zero — which is what makes
  the head path and the zero-padded tail path the same argument rather than two.

  ## What is different from `Kopis/Avx2/SerLane.lean`

  Three things, and all three make this file shorter.

  * **No broadcast, and no half.**  A NEON register is 128 bits and `tbl` indexes all sixteen
    bytes of its table, so the group's bytes are loaded once and named directly.  AVX2 has to
    broadcast the group into both 128-bit halves and its shuffle control is read modulo 16 within
    each; the `16 * (i / 16)` that appears throughout the AVX2 lane lemma has no counterpart here.
  * **The zeroing condition is the index's value.**  `tbl` zeroes on any index ≥ 16; `vpshufb`
    zeroes on bit 7 of the index and masks the rest to `& 0x0F`.  `planShuffle_lt` discharges the
    NEON condition outright, where the AVX2 proof needs both a `testBit 7` fact and an `&&& 0x0F`
    one.
  * **The shift counts are negated.**  There is no variable *right* shift on AArch64: `ushl`
    spells one as a left shift by a negative count, taken from the low byte of the count lane,
    signed.  `shiftAmount_neg` below is the bridge from the `i32` the plan stores to the `Int`
    the axiom reads, and `ushlLane_neg` turns the negative left shift back into a right shift.
    Neither has an AVX2 counterpart — `vpsrlvd` takes an unsigned count and is a right shift.

  There is also nothing here corresponding to AVX2's `pack_permute_*`: `xtn`/`xtn2` leave the
  narrowed lanes in order, so the NEON loop has no permute to undo and the reassembly is one
  `if i < 4` in `Model.xtnPair32` rather than a sixteen-case index computation.  That reassembly
  is done in `Ser.lean`, where the loop needs it.
-/
import Kopis.Neon.Model
import Kopis.Bits.Stream

open Aeneas Aeneas.Std Result

namespace Kopis.Neon

open Kopis.Properties (streamNat streamByte streamNat_of_byteWindow sum_base256)

/-! ## Lanes as numbers

The intrinsic axioms are stated on `BitVec` lanes and the bit stream on `ℕ`; these three lemmas
are the whole of the translation. -/

/-- A lane, as a number: lane `i` of width `w` is the corresponding field of `x.toNat`. -/
theorem toNat_laneOf {n : ℕ} (w : ℕ) (x : BitVec n) (i : ℕ) :
    (laneOf w x i).toNat = x.toNat >>> (w * i) % 2 ^ w := rfl

/-- A 32-bit lane is its four bytes, little-endian — the step from `tbl`'s byte-level
specification to `ushl`'s 32-bit-lane one. -/
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

/-! ## `ushl`'s negative counts

AArch64 has no variable right shift, so the deserializer spells one as `ushl` by a negative
count.  Two small lemmas cover the round trip: what the instruction reads out of the count lane,
and what it then does with it. -/

/-- A negative left shift is a right shift.  Stated at `-(p : ℤ)` rather than at an arbitrary
negative `s` because that is the only form the plan produces, and because it has to cover
`p = 0`, where the count is not negative at all and the instruction shifts left by zero. -/
theorem ushlLane_neg {n : ℕ} (x : BitVec n) (p : ℕ) : ushlLane x (-(p : ℤ)) = x >>> p := by
  unfold ushlLane
  rcases Nat.eq_zero_or_pos p with rfl | hp
  · simp
  · rw [if_neg (by omega), neg_neg, Int.toNat_natCast]

/-- **What `ushl` reads out of a 32-bit count lane.**  The count is the lane's low *byte*, as a
signed 8-bit number, so an `i32` holding a small negative value delivers that value — the two's
complement of `p` truncated to eight bits is the two's complement of `p` in eight bits, as long
as `p` fits.  The plan's counts are in `-7 .. 0`, comfortably inside the `p ≤ 127` this needs.

Stated twice, at 32 and at 16 bits, rather than once for an arbitrary width: the proof is
`omega` over `2 ^ n`, which needs `n` to be a numeral.  `ser` shifts 32-bit lanes and `sample`
16-bit ones. -/
theorem shiftAmount32_neg (x : BitVec 32) (p : ℕ) (hp : p ≤ 127) (hx : x.toInt = -(p : ℤ)) :
    shiftAmount x = -(p : ℤ) := by
  have hlt : x.toNat < 2 ^ 32 := x.isLt
  have hcond := BitVec.toInt_eq_toNat_cond x
  rw [hx] at hcond
  have hnat : x.toNat = if p = 0 then 0 else 2 ^ 32 - p := by
    split at hcond <;> [skip; skip] <;> split <;> omega
  have hsw : (BitVec.setWidth 8 x).toNat = if p = 0 then 0 else 2 ^ 8 - p := by
    rw [BitVec.toNat_setWidth, hnat]
    split <;> [simp; omega]
  unfold shiftAmount
  have hcond8 := BitVec.toInt_eq_toNat_cond (BitVec.setWidth 8 x)
  rw [hsw] at hcond8
  split at hcond8 <;> split at hcond8 <;> omega

/-- `shiftAmount32_neg` at 16-bit lanes, which is what `sample::cbd_lanes` shifts by. -/
theorem shiftAmount16_neg (x : BitVec 16) (p : ℕ) (hp : p ≤ 127) (hx : x.toInt = -(p : ℤ)) :
    shiftAmount x = -(p : ℤ) := by
  have hlt : x.toNat < 2 ^ 16 := x.isLt
  have hcond := BitVec.toInt_eq_toNat_cond x
  rw [hx] at hcond
  have hnat : x.toNat = if p = 0 then 0 else 2 ^ 16 - p := by
    split at hcond <;> [skip; skip] <;> split <;> omega
  have hsw : (BitVec.setWidth 8 x).toNat = if p = 0 then 0 else 2 ^ 8 - p := by
    rw [BitVec.toNat_setWidth, hnat]
    split <;> [simp; omega]
  unfold shiftAmount
  have hcond8 := BitVec.toInt_eq_toNat_cond (BitVec.setWidth 8 x)
  rw [hsw] at hcond8
  split at hcond8 <;> split at hcond8 <;> omega

/-! ## The plan entries

`src/backend/neon/ser.rs` computes these in a `const fn`; `Kopis/Neon/SerPlan.lean` proves the
extracted table holds exactly them.  They are defined here because the lane lemma below is
stated through them.

`planShift` is the *magnitude* of the shift.  The Rust table stores its negation, because that
is what `ushl` wants; `SerPlan.lean` states it that way and `ushlLane_neg` puts it back. -/

/-- Byte `b` of the `tbl` control for lane `k` at width `w`: coefficient `k` starts at byte
`⌊k·w/8⌋` of the group, and the window is the four bytes from there. -/
def planShuffle (w k b : ℕ) : ℕ := k * w / 8 + b

/-- The right-shift amount for lane `k` at width `w`: the coefficient's bit offset within its
first byte.  The extracted table holds `-(planShift w k)`. -/
def planShift (w k : ℕ) : ℕ := k * w % 8

/-- The two together put coefficient `k` back at bit `k·w` of the group — the identity the
whole scheme rests on. -/
theorem planShuffle_planShift (w k : ℕ) : 8 * planShuffle w k 0 + planShift w k = k * w := by
  unfold planShuffle planShift
  omega

/-- The shift is a bit offset within a byte, so at most 7 — which is what keeps the `i32` the
plan stores inside the eight bits `ushl` reads. -/
theorem planShift_lt (w k : ℕ) : planShift w k ≤ 7 := by
  unfold planShift
  omega

/-- The `tbl` control never leaves the group's sixteen bytes: `⌊7·13/8⌋ + 3 = 14`.  On NEON this
is what makes the lookup defined at all — an index of 16 or more reads as zero. -/
theorem planShuffle_lt (w k b : ℕ) (hw : w ≤ 13) (hk : k < 8) (hb : b < 4) :
    planShuffle w k b < 16 := by
  have : k * w ≤ 7 * 13 := Nat.mul_le_mul (by omega) hw
  unfold planShuffle
  omega

/-! ## One lane is one coefficient

The three instructions `tbl`, `ushl`, `and`, applied to a register holding a group's sixteen
bytes, put coefficient `8·group + base + j` of the bit stream in 32-bit lane `j`.

The hypotheses are the *model* equations, which `Kopis/Neon/Model.lean` derives from the
intrinsic axioms — so this lemma consumes the trust base exactly once, in the form phase A2 will
differential-test. -/

open RustKopisNeon.backend.neon.intrinsics in
theorem lane_chain_value
    (bytes : Slice U8) (w : ℕ) (hw13 : w ≤ 13) (group base : ℕ) (hbase : base + 4 ≤ 8)
    (raw shufV shiftV maskV windows shifted out : Vec128)
    (hraw : ∀ i < 16, (lane8 raw i).toNat = streamByte bytes (group * w + i))
    (hshuf : ∀ i < 16, (lane8 shufV i).toNat = planShuffle w (base + i / 4) (i % 4))
    (hshiftV : ∀ m < 4, shiftAmount (lane32 shiftV m) = -(planShift w (base + m) : ℤ))
    (hmask : ∀ m < 4, (lane32 maskV m).toNat = 2 ^ w - 1)
    (hwin : bits windows = Model.tbl1U8 (bits raw) (bits shufV))
    (hsh : bits shifted = Model.ushlU32 (bits windows) (bits shiftV))
    (hout : bits out = Model.andV (bits shifted) (bits maskV)) :
    ∀ j < 4, (lane32 out j).toNat = streamNat bytes (w * (8 * group + base + j)) w := by
  intro j hj
  have hk8 : base + j < 8 := by omega
  -- `and`: lane `j` is lane `j` of the shifted vector, reduced mod `2 ^ w`
  have h1 : (lane32 out j).toNat = (lane32 shifted j).toNat % 2 ^ w := by
    have hl : lane32 out j = lane32 shifted j &&& lane32 maskV j := by
      show laneOf 32 (bits out) j = _
      rw [hout]
      simp only [Model.andV]
      exact laneOf_and 32 (bits shifted) (bits maskV) j
    rw [hl, toNat_and_mask _ _ w (hmask j hj)]
  -- `ushl`: lane `j` is lane `j` of the windows, shifted right by that lane's count
  have h2 : (lane32 shifted j).toNat = (lane32 windows j).toNat >>> planShift w (base + j) := by
    have hl : lane32 shifted j
        = ushlLane (lane32 windows j) (shiftAmount (lane32 shiftV j)) := by
      show laneOf 32 (bits shifted) j = _
      rw [hsh]
      simp only [Model.ushlU32]
      exact laneOf_ofLanes32 _ hj
    rw [hl, hshiftV j hj, ushlLane_neg, BitVec.toNat_ushiftRight]
  -- `tbl`: byte `b` of lane `j` is the group's byte `⌊(base+j)·w/8⌋ + b`
  have h3 : ∀ b < 4, (lane8 windows (4 * j + b)).toNat
      = streamByte bytes (group * w + planShuffle w (base + j) b) := by
    intro b hb
    have hi : 4 * j + b < 16 := by omega
    have hctrl : (lane8 shufV (4 * j + b)).toNat = planShuffle w (base + j) b := by
      rw [hshuf _ hi, show (4 * j + b) / 4 = j from by omega,
        show (4 * j + b) % 4 = b from by omega]
    have hp16 : planShuffle w (base + j) b < 16 := planShuffle_lt w (base + j) b hw13 hk8 hb
    have hl : lane8 windows (4 * j + b) = lane8 raw (planShuffle w (base + j) b) := by
      show laneOf 8 (bits windows) _ = _
      rw [hwin]
      simp only [Model.tbl1U8]
      rw [laneOf_ofLanes8 _ hi, hctrl, if_pos hp16]
    rw [hl, hraw _ hp16]
  -- the four bytes assemble into the lane
  have h4 : (lane32 windows j).toNat
      = ∑ b ∈ Finset.range 4,
          streamByte bytes (group * w + (base + j) * w / 8 + b) * 256 ^ b := by
    rw [toNat_lane32_eq_bytes]
    apply Finset.sum_congr rfl
    intro b hb
    rw [h3 b (Finset.mem_range.mp hb)]
    unfold planShuffle
    congr 2
    omega
  -- and the window is the coefficient
  rw [h1, h2, h4,
    ← streamNat_of_byteWindow bytes (group * w + (base + j) * w / 8) (planShift w (base + j)) w
      (by have := planShift_lt w (base + j); omega)]
  congr 1
  have h8 : 8 * ((base + j) * w / 8) + (base + j) * w % 8 = (base + j) * w :=
    Nat.div_add_mod ((base + j) * w) 8
  calc 8 * (group * w + (base + j) * w / 8) + planShift w (base + j)
      = 8 * group * w + (8 * ((base + j) * w / 8) + (base + j) * w % 8) := by
        unfold planShift; ring
    _ = 8 * group * w + (base + j) * w := by rw [h8]
    _ = w * (8 * group + base + j) := by ring

end Kopis.Neon
