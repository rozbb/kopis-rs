/-
  # Kopis/Neon/Cbd.lean — the NEON centred-binomial sampler.

  `src/backend/neon/sample.rs` is short because it reuses the deserializer: it pulls the `MU`-bit
  field for each coefficient out with `ser::deserialize` — which Phase C characterises exactly —
  and then does two small population counts per 16-bit lane.

  So the whole content here is the popcount, and on AArch64 that is *one instruction*.  `cnt.16b`
  is a real per-byte population count, where AVX2 has to look the low nibble up in a `vpshufb`
  table and add bit 4 separately.  The side condition differs accordingly: `popcount_small` is
  valid exactly while each 16-bit lane's **high byte is zero**, so that the two per-byte counts
  read as the lane's count, rather than while the lane is below 32 as on AVX2.  Both follow from
  `MU/2 ≤ 5`; neither is assumed.  The result is

      out[k] = cbdX buf (MU/2) (MU·k) − cbdX buf (MU/2) (MU·k + MU/2)   (wrapping, u16)

  and `cbdX` is the same definition the portable sampler is proved against.

  The other difference is the shift.  AVX2 monomorphises over `MU/2` by taking `vpsrlw`'s count
  from a register (`shift_right_dynamic`); NEON has no such instruction and instead splats
  `-(MU/2)` and uses `ushl`, the same negative-count idiom the deserializer uses, so
  `shiftAmount16_neg` and `ushlLane_neg` from `SerLane.lean` do that work and there is no
  counterpart to `shift_right_dynamic_spec` here.
-/
import Kopis.Neon.Ser

open Aeneas Aeneas.Std Result
open RustKopisNeon

namespace Kopis.Neon

open Kopis.Properties (streamNat streamByte streamBit streamNat_lt cbdX cbdX_le cbdX_eq_bitSum
  testBit_streamNat)

set_option maxHeartbeats 1000000
set_option maxRecDepth 4000

/-! ## `cnt.16b`, as a sum of bits

`popCount8` is written as a `BitVec` sum in `Intrinsics.lean`, because that is the shape the
axiom wants; the sampler needs it as a sum of `Nat` bits.  Eight terms, each `0` or `1`, so the
`BitVec` addition never wraps and the two agree — by exhaustion over the eight bits. -/

theorem toNat_popCount8 (x : BitVec 8) :
    (popCount8 x).toNat = ∑ j ∈ Finset.range 8, (x.getLsbD j).toNat := by
  simp only [popCount8, show (List.range 8) = [0, 1, 2, 3, 4, 5, 6, 7] from rfl, List.map_cons,
    List.map_nil, List.sum_cons, List.sum_nil, Finset.sum_range_succ, Finset.sum_range_zero]
  cases h0 : x.getLsbD 0 <;> cases h1 : x.getLsbD 1 <;> cases h2 : x.getLsbD 2 <;>
    cases h3 : x.getLsbD 3 <;> cases h4 : x.getLsbD 4 <;> cases h5 : x.getLsbD 5 <;>
    cases h6 : x.getLsbD 6 <;> cases h7 : x.getLsbD 7 <;> decide

/-! ## `popcount_small`

`cnt` counts per byte.  A lane below 32 has a zero high byte, whose count is zero, so the two
per-byte counts assemble into the lane's own popcount — and only its low five bits can be set. -/

open RustKopisNeon.backend.neon.intrinsics in
theorem popcount_small_spec (v : Vec128)
    (hv : ∀ m < 8, (lane16 v m).toNat < 32) :
    backend.neon.sample.popcount_small v
      ⦃ (c : Vec128) => ∀ m < 8,
          (lane16 c m).toNat
            = ∑ i ∈ Finset.range 5, ((lane16 v m).toNat.testBit i).toNat ⦄ := by
  unfold backend.neon.sample.popcount_small
  obtain ⟨c, hc, hcb⟩ := cnt_u8_model v
  rw [hc]
  simp only [WP.spec_ok]
  intro m hm
  have hlane : ∀ i < 16, lane8 c i = popCount8 (lane8 v i) := by
    intro i hi
    show laneOf 8 (bits c) i = _
    rw [hcb]
    simp only [Model.cntU8]
    exact laneOf_ofLanes8 _ hi
  -- the two bytes of lane `m`: the value itself, and zero
  have hsmall : (lane16 v m).toNat < 32 := hv m hm
  have hlo : lane8 v (2 * m) = BitVec.setWidth 8 (lane16 v m) := by
    show laneOf 8 (bits v) (2 * m) = _
    rw [laneOf_laneOf 8 2 (bits v) (2 * m) (by omega),
      show 2 * m / 2 = m from by omega, show 2 * m % 2 = 0 from by omega]
    show laneOf 8 (lane16 v m) 0 = _
    apply BitVec.eq_of_toNat_eq
    rw [toNat_laneOf, BitVec.toNat_setWidth]
    simp
  have hhi : lane8 v (2 * m + 1) = 0#8 := by
    show laneOf 8 (bits v) (2 * m + 1) = _
    rw [laneOf_laneOf 8 2 (bits v) (2 * m + 1) (by omega),
      show (2 * m + 1) / 2 = m from by omega, show (2 * m + 1) % 2 = 1 from by omega]
    show laneOf 8 (lane16 v m) 1 = _
    apply BitVec.eq_of_toNat_eq
    rw [toNat_laneOf, Nat.mul_one, Nat.shiftRight_eq_div_pow, Nat.div_eq_of_lt (by omega)]
    simp
  -- so the high byte of the result is zero and the low one is the whole count
  have hczero : lane8 c (2 * m + 1) = 0#8 := by
    rw [hlane _ (by omega), hhi]
    decide
  have hbytes : lane16 c m = lane8 c (2 * m + 1) ++ lane8 c (2 * m) := lane16_eq_bytes _ m
  rw [hbytes, hczero, BitVec.toNat_append]
  simp only [BitVec.toNat_ofNat, Nat.zero_mod, Nat.zero_shiftLeft, Nat.zero_or]
  rw [hlane _ (by omega), toNat_popCount8]
  -- the count of the low byte is the count of its low five bits
  have hbit : ∀ j, (BitVec.setWidth 8 (lane16 v m)).getLsbD j
      = (lane16 v m).toNat.testBit j := by
    intro j
    show ((BitVec.setWidth 8 (lane16 v m)).toNat).testBit j = _
    rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)]
  rw [hlo]
  simp only [hbit]
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    Nat.testBit_lt_two_pow (show (lane16 v m).toNat < 2 ^ 5 by omega),
    Nat.testBit_lt_two_pow (show (lane16 v m).toNat < 2 ^ 6 by omega),
    Nat.testBit_lt_two_pow (show (lane16 v m).toNat < 2 ^ 7 by omega)]
  simp

/-! ## The loop

Each iteration turns eight `MU`-bit fields into eight coefficients: mask off the low half, shift
down and mask off the high half, popcount both, subtract. -/

open RustKopisNeon.backend.neon.intrinsics in
theorem cbd_loop_spec (buf : Slice U8) (mu half : ℕ) (hmu : mu = 2 * half) (hhalf : 1 ≤ half)
    (hhalf5 : half ≤ 5)
    (fields : Array U16 256#usize)
    (hfields : ∀ j < 256, (fields.val[j]!).val = streamNat buf (mu * j) mu)
    (half_mask half_shift : Vec128)
    (hmask : ∀ m < 8, (lane16 half_mask m).toNat = 2 ^ half - 1)
    (hshift : ∀ m < 8, shiftAmount (lane16 half_shift m) = -(half : ℤ))
    (iter : core.ops.range.Range Usize) (hend : iter.«end».val = 32)
    (out : arithmetic.ring_arith.RingElem) :
    backend.neon.sample.cbd_lanes_loop iter fields half_mask half_shift out
      ⦃ (r : arithmetic.ring_arith.RingElem) => ∀ j < 256,
          (r.val[j]!).val =
            if j < 8 * iter.start.val then (out.val[j]!).val
            else Kopis.Properties.cbdU16 buf half (mu * j) ⦄ := by
  unfold backend.neon.sample.cbd_lanes_loop
  by_cases hlt : iter.start.val < iter.«end».val
  · let* ⟨ o, iter1, ho, hstart', hend' ⟩ ← core.iter.range.IteratorRange.next_Usize_some_spec
    rw [ho]
    simp only
    have hi32 : iter.start.val < 32 := by omega
    -- the eight fields of this block
    obtain ⟨field, hfield, hfieldl⟩ := load_u16_spec fields iter.start (by scalar_tac)
    rw [hfield, bind_tc_ok]
    have hfv : ∀ k < 8, (lane16 field k).toNat
        = streamNat buf (mu * (8 * iter.start.val + k)) mu := by
      intro k hk
      rw [hfieldl k hk]
      exact hfields _ (by omega)
    -- the low half
    obtain ⟨low, hlow, hlowb⟩ := and_model field half_mask
    rw [hlow, bind_tc_ok]
    have hlowv : ∀ k < 8, (lane16 low k).toNat
        = streamNat buf (mu * (8 * iter.start.val + k)) half := by
      intro k hk
      have hl : lane16 low k = lane16 field k &&& lane16 half_mask k := by
        show laneOf 16 (bits low) k = _
        rw [hlowb]
        simp only [Model.andV]
        exact laneOf_and 16 (bits field) (bits half_mask) k
      rw [hl, toNat_and_mask _ _ half (hmask k hk), hfv k hk,
        Kopis.Properties.streamNat_mod _ _ _ _ (by omega)]
    -- the high half: `ushl` by the negated count
    obtain ⟨sh, hsh, hshb⟩ := ushl_u16_model field half_shift
    rw [hsh, bind_tc_ok]
    have hshl : ∀ k < 8, lane16 sh k = lane16 field k >>> half := by
      intro k hk
      show laneOf 16 (bits sh) k = _
      rw [hshb]
      simp only [Model.ushlU16]
      rw [laneOf_ofLanes16 _ hk, hshift k hk, ushlLane_neg]
    obtain ⟨high, hhigh, hhighb⟩ := and_model sh half_mask
    rw [hhigh, bind_tc_ok]
    have hhighv : ∀ k < 8, (lane16 high k).toNat
        = streamNat buf (mu * (8 * iter.start.val + k) + half) half := by
      intro k hk
      have hl : lane16 high k = lane16 sh k &&& lane16 half_mask k := by
        show laneOf 16 (bits high) k = _
        rw [hhighb]
        simp only [Model.andV]
        exact laneOf_and 16 (bits sh) (bits half_mask) k
      rw [hl, toNat_and_mask _ _ half (hmask k hk), hshl k hk, BitVec.toNat_ushiftRight,
        hfv k hk, Kopis.Properties.streamNat_shiftRight _ _ _ _ (by omega),
        Kopis.Properties.streamNat_mod _ _ _ _ (by omega)]
    -- both halves are below 32, so the per-byte popcount is valid
    have hbound : ∀ (x : Vec128), (∀ k < 8, ∃ p, (lane16 x k).toNat = streamNat buf p half) →
        ∀ k < 8, (lane16 x k).toNat < 32 := by
      intro x hx k hk
      obtain ⟨p, hp⟩ := hx k hk
      rw [hp]
      exact lt_of_lt_of_le (Kopis.Properties.streamNat_lt _ _ _)
        (by calc (2:ℕ) ^ half ≤ 2 ^ 5 := Nat.pow_le_pow_right (by norm_num) hhalf5
              _ = 32 := by norm_num)
    apply WP.spec_bind (popcount_small_spec low (hbound low (fun k hk => ⟨_, hlowv k hk⟩)))
    intro pl hpl
    apply WP.spec_bind (popcount_small_spec high (hbound high (fun k hk => ⟨_, hhighv k hk⟩)))
    intro ph hph
    -- the difference, wrapping
    obtain ⟨coeff, hcoeff, hcoeffb⟩ := sub_16_model pl ph
    rw [hcoeff, bind_tc_ok]
    have hcv : ∀ k < 8, (lane16 coeff k).toNat
        = Kopis.Properties.cbdU16 buf half (mu * (8 * iter.start.val + k)) := by
      intro k hk
      have hl : lane16 coeff k = lane16 pl k - lane16 ph k := by
        show laneOf 16 (bits coeff) k = _
        rw [hcoeffb]
        simp only [Model.sub16]
        exact laneOf_ofLanes16 _ hk
      rw [hl, BitVec.toNat_sub, hpl k hk, hph k hk, hlowv k hk, hhighv k hk,
        Kopis.Properties.cbdX_eq_bitSum_of_le buf half _ 5 hhalf5,
        Kopis.Properties.cbdX_eq_bitSum_of_le buf half _ 5 hhalf5]
      unfold Kopis.Properties.cbdU16
      have h1 := Kopis.Properties.cbdX_le buf half (mu * (8 * iter.start.val + k))
      have h2 := Kopis.Properties.cbdX_le buf half (mu * (8 * iter.start.val + k) + half)
      have h3 : (2:ℕ) ^ 16 = 65536 := by norm_num
      congr 1
      omega
    -- store, then recurse
    obtain ⟨out1, hout1, hout1v⟩ := store_u16_spec out iter.start coeff (by scalar_tac)
    rw [hout1, bind_tc_ok]
    apply WP.spec_mono (cbd_loop_spec buf mu half hmu hhalf hhalf5 fields hfields half_mask
      half_shift hmask hshift iter1 (by rw [hend']; exact hend) out1)
    intro r hr j hj
    rw [hr j hj]
    by_cases hlow' : j < 8 * iter1.start.val
    · rw [if_pos hlow']
      have hbv : (out1.val[j]!).val = ((out1.val[j]!).bv).toNat := rfl
      rw [hbv, hout1v j hj]
      by_cases hin : 8 * iter.start.val ≤ j ∧ j < 8 * iter.start.val + 8
      · rw [if_pos hin, if_neg (by omega)]
        have hk : j - 8 * iter.start.val < 8 := by omega
        show (lane16 coeff (j - 8 * iter.start.val)).toNat = _
        rw [hcv _ hk]
        congr 2
        omega
      · rw [if_neg hin, if_pos (by omega)]
        rfl
    · rw [if_neg hlow', if_neg (by omega)]
  · let* ⟨ o, iter1, hnone, _ ⟩ ← core.iter.range.IteratorRange.next_Usize_none_spec
    rw [hnone]
    refine (WP.spec_ok _).mpr (fun j hj => ?_)
    rw [if_pos (by omega)]
termination_by iter.«end».val - iter.start.val
decreasing_by scalar_decr_tac

/-! ## The whole sampler

The two splatted constants — the `(1 << MU/2) - 1` half-mask and the `-(MU/2)` shift count — then
the loop.  The fields come from `ser::deserialize`, so Phase C supplies them. -/

open RustKopisNeon.backend.neon.intrinsics in
/-- **The NEON sampler computes the centred binomial difference.**  Coefficient `k` is the
popcount of the low `MU/2` bits of its field minus that of the high `MU/2`, as a wrapping
`u16` — exactly what `sample::cbd` documents. -/
theorem cbd_streamNat (buf : Slice U8) (mu half : ℕ) (hmu : mu = 2 * half) (hhalf : 1 ≤ half)
    (hhalf5 : half ≤ 5) (hlen : buf.length = 32 * mu) (MU : Usize) (hMU : MU.val = mu) :
    backend.neon.sample.cbd_lanes MU buf
      ⦃ (r : arithmetic.ring_arith.RingElem) => ∀ j < 256,
          (r.val[j]!).val = Kopis.Properties.cbdU16 buf half (mu * j) ⦄ := by
  have hmu13 : mu ≤ 13 := by omega
  unfold backend.neon.sample.cbd_lanes
  -- the fields: Phase C
  apply WP.spec_bind (deserialize_streamNat buf mu (by omega) hmu13 hlen MU hMU)
  intro fields hfields
  -- half = MU / 2
  let* ⟨ halfU, hhalfU ⟩ ← Std.Usize.div_spec
  have hhalfUv : halfU.val = half := by rw [hhalfU, hMU]; omega
  -- the half-mask `(1 << half) - 1`
  have h2h : 2 ^ half ≤ 32 := by
    calc (2:ℕ) ^ half ≤ 2 ^ 5 := Nat.pow_le_pow_right (by norm_num) hhalf5
      _ = 32 := by norm_num
  have hsz : Std.U16.size = 65536 := by simp [Std.U16.size, Std.U16.numBits]
  let* ⟨ i1, hi1, hi1bv ⟩ ← Std.U16.ShiftLeft_spec
  have hi1v : i1.val = 2 ^ half := by
    rw [hi1, hhalfUv, Nat.shiftLeft_eq, one_mul, hsz, Nat.mod_eq_of_lt (by omega)]
  let* ⟨ i2, hi2 ⟩ ← Std.U16.sub_spec (show (1#u16).val ≤ i1.val by
    rw [hi1v]; exact Nat.one_le_two_pow)
  have hi2v : i2.val = 2 ^ half - 1 := by rw [hi2, hi1v]
  obtain ⟨half_mask, hhm, hhml⟩ := dup_n_u16_spec i2
  rw [hhm, bind_tc_ok]
  have hmaskv : ∀ m < 8, (lane16 half_mask m).toNat = 2 ^ half - 1 := by
    intro m hm
    rw [hhml m hm]
    exact hi2v
  -- the shift count, `-(half)`, splatted
  have hi16max : IScalar.max IScalarTy.I16 = 32767 := by simp [Std.I16.max_eq]
  let* ⟨ i3, hi3 ⟩ ← UScalar.hcast_inBounds_spec .I16 halfU (by rw [hhalfUv, hi16max]; omega)
  have hi3v : i3.val = (half : ℤ) := by rw [hi3, hhalfUv]
  let* ⟨ i4, hi4 ⟩ ← Std.IScalar.neg_step i3 (by
    simp only [ne_eq]
    intro h
    rw [h] at hi3v
    simp [Std.I16.min_eq] at hi3v)
  obtain ⟨half_shift, hhs, hhsl⟩ := dup_n_s16_spec i4
  rw [hhs, bind_tc_ok]
  have hshiftv : ∀ m < 8, shiftAmount (lane16 half_shift m) = -(half : ℤ) := by
    intro m hm
    rw [hhsl m hm]
    refine shiftAmount16_neg _ _ (by omega) ?_
    show (i4 : I16).val = _
    rw [hi4, hi3v]
  -- the zero output, and the trip count
  obtain ⟨out, hout⟩ : ∃ o, arithmetic.ring_arith.RingElem.Insts.CoreDefaultDefault.default
      = ok o := ⟨Array.repeat 256#usize 0#u16, rfl⟩
  rw [hout, bind_tc_ok]
  have hrd : (consts.RING_DEG : Usize) / 8#usize = ok 32#usize := by
    simp only [consts.RING_DEG]; rfl
  rw [hrd, bind_tc_ok]
  -- and the loop
  apply WP.spec_mono (cbd_loop_spec buf mu half hmu hhalf hhalf5 fields hfields half_mask
    half_shift hmaskv hshiftv ⟨0#usize, 32#usize⟩ rfl out)
  intro r hr j hj
  rw [hr j hj, if_neg (by simp)]

end Kopis.Neon
