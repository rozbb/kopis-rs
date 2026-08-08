/-
  # Kopis/Neon/Ser.lean — the NEON deserializer computes the bit stream.

  Everything the loop needs is already proved: `SerPlan.lean` pins the constant tables,
  `SerTail.lean` gives the head and tail loads the same statement, `SerLane.lean` turns one
  `tbl`/`ushl`/`and` lane into one coefficient.  What is left is to run those over the loop and
  read the result out of the output array:

      out[j] = streamNat bytes (bits · j) bits   for every j < 256

  which is exactly what `ser::deserialize_generic` computes, and hence the statement through
  which the two are equal.

  The loop is *one* loop, over 32 groups.  AVX2's is two nested ones over 16 pairs of groups,
  because it packs two eight-lane vectors into one sixteen-lane store; NEON's `xtn`/`xtn2` pair
  narrows the two halves of a single group into one 128-bit register, so a group is a store and
  there is nothing to pair.  `xtn_pair_value` below replaces the whole of AVX2's
  `pack_permute_*` — the narrowing leaves lanes in order, so it is one `if j < 4` rather than a
  sixteen-case permute computation.
-/
import Kopis.Neon.SerTail

open Aeneas Aeneas.Std Result
open RustKopisNeon

namespace Kopis.Neon

open Kopis.Properties (streamNat streamByte streamNat_lt)

set_option maxHeartbeats 2000000

/-! ## Where a group's register comes from

The `if` in the loop body picks the direct load or the scratch-buffer one.  Both produce a
register holding the group's sixteen bytes, which is the only thing the lane lemma needs. -/

open RustKopisNeon.backend.neon.intrinsics in
/-- A group in the head: loaded straight out of `bytes`. -/
theorem head_raw (bytes : Slice U8) (w : ℕ) (hw1 : 1 ≤ w) (hlen : bytes.length = 32 * w)
    (group : ℕ) (hg : group < headGroups w) (off : Usize) (hoff : off.val = group * w) :
    load_u8x16 bytes off
      ⦃ (raw : Vec128) => ∀ i < 16,
          (lane8 raw i).toNat = streamByte bytes (group * w + i) ⦄ := by
  have hb : off.val + 16 ≤ bytes.val.length := by
    have := head_load_in_bounds w group hw1 hg
    have hl : bytes.val.length = 32 * w := by simpa [Slice.length] using hlen
    omega
  obtain ⟨v, hv, hvl⟩ := load_u8x16_spec bytes off hb
  rw [hv]
  simp only [WP.spec_ok]
  intro i hi
  rw [hvl i hi, hoff]
  rfl

open RustKopisNeon.backend.neon.intrinsics in
/-- A group in the tail: loaded from the zero-padded scratch buffer, which holds the same
bytes — including, past the end of `bytes`, the same zeros. -/
theorem tail_raw (bytes : Slice U8) (w : ℕ) (hw1 : 1 ≤ w)
    (tailArr : Array U8 32#usize)
    (htail : ∀ p < 32, (tailArr.val[p]!).val = streamByte bytes (tailStart w + p))
    (group : ℕ) (hg : headGroups w ≤ group) (hg32 : group < 32)
    (off : Usize) (hoff : off.val = group * w - tailStart w) :
    (do let s ← lift (Array.to_slice tailArr)
        load_u8x16 s off)
      ⦃ (raw : Vec128) => ∀ i < 16,
          (lane8 raw i).toNat = streamByte bytes (group * w + i) ⦄ := by
  have hlen32 : (Array.to_slice tailArr).val.length = 32 := by
    simp [Array.to_slice]
  have hb : off.val + 16 ≤ (Array.to_slice tailArr).val.length := by
    rw [hlen32, hoff]
    exact tail_load_in_bounds w group hw1 hg32
  -- the tail offset puts the group back where it belongs
  have hback : tailStart w + (group * w - tailStart w) = group * w := by
    have : tailStart w ≤ group * w := by
      unfold tailStart
      exact Nat.mul_le_mul_right w hg
    omega
  obtain ⟨v, hv, hvl⟩ := load_u8x16_spec (Array.to_slice tailArr) off hb
  simp only [lift, bind_tc_ok]
  rw [hv]
  simp only [WP.spec_ok]
  intro i hi
  have hidx : off.val + i < 32 := by
    rw [hoff]; have := tail_load_in_bounds w group hw1 hg32; omega
  have hslice : ((Array.to_slice tailArr).val[off.val + i]!) = (tailArr.val[off.val + i]!) := by
    simp [Array.to_slice]
  rw [hvl i hi, hslice]
  show ((tailArr.val[off.val + i]!) : U8).val = _
  rw [htail _ hidx, hoff]
  congr 1
  omega

/-! ## The narrowing

`xtn`/`xtn2` truncate `val_lo`'s four 32-bit lanes into 16-bit lanes 0..3 and `val_hi`'s into
lanes 4..7.  Truncation is exact on values that already fit, and every coefficient is at most
13 bits.  In order — nothing to permute afterwards. -/

open RustKopisNeon.backend.neon.intrinsics in
theorem xtn_pair_value (lo hi res : Vec128)
    (hb0 : ∀ m < 4, (lane32 lo m).toNat < 2 ^ 16)
    (hb1 : ∀ m < 4, (lane32 hi m).toNat < 2 ^ 16)
    (hres : bits res = Model.xtnPair32 (bits lo) (bits hi)) :
    ∀ j < 8, (lane16 res j).toNat
      = if j < 4 then (lane32 lo j).toNat else (lane32 hi (j - 4)).toNat := by
  intro j hj
  have hl : lane16 res j
      = if j < 4 then BitVec.setWidth 16 (lane32 lo j)
        else BitVec.setWidth 16 (lane32 hi (j - 4)) := by
    show laneOf 16 (bits res) j = _
    rw [hres]
    simp only [Model.xtnPair32]
    exact laneOf_ofLanes16 _ hj
  rw [hl]
  split
  · rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (hb0 j (by omega))]
  · rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (hb1 (j - 4) (by omega))]

/-! ## The loop: thirty-two groups

Each iteration loads one group's sixteen bytes, extracts its eight coefficients in two passes of
four, narrows them into one register and stores them.  The store covers `out[8·group ..
8·group + 8]`, so after the whole loop every one of the 256 outputs has been written exactly
once. -/

open RustKopisNeon.backend.neon.intrinsics in
theorem loop_spec (bytes : Slice U8) (w : ℕ) (hw1 : 1 ≤ w) (hw13 : w ≤ 13)
    (hlen : bytes.length = 32 * w)
    (bitsU : Usize) (hbitsU : bitsU.val = w)
    (shufLo shufHi shiftLo shiftHi maskV : Vec128)
    (hshufLo : ∀ i < 16, (lane8 shufLo i).toNat = planShuffle w (i / 4) (i % 4))
    (hshufHi : ∀ i < 16, (lane8 shufHi i).toNat = planShuffle w (4 + i / 4) (i % 4))
    (hshiftLo : ∀ m < 4, shiftAmount (lane32 shiftLo m) = -(planShift w m : ℤ))
    (hshiftHi : ∀ m < 4, shiftAmount (lane32 shiftHi m) = -(planShift w (4 + m) : ℤ))
    (hmask : ∀ m < 4, (lane32 maskV m).toNat = 2 ^ w - 1)
    (headG tailS : Usize) (hheadG : headG.val = headGroups w) (htailS : tailS.val = tailStart w)
    (tailArr : Array U8 32#usize)
    (htail : ∀ p < 32, (tailArr.val[p]!).val = streamByte bytes (tailStart w + p))
    (iter : core.ops.range.Range Usize) (hend : iter.«end».val = 32)
    (out : Array U16 256#usize) :
    backend.neon.ser.deserialize_loop iter bytes bitsU shufLo shufHi shiftLo shiftHi maskV
      headG tailS tailArr out
      ⦃ (r : Array U16 256#usize) => ∀ j < 256,
          (r.val[j]!).val =
            if j < 8 * iter.start.val then (out.val[j]!).val
            else streamNat bytes (w * j) w ⦄ := by
  unfold backend.neon.ser.deserialize_loop
  by_cases hlt : iter.start.val < iter.«end».val
  · let* ⟨ o, iter1, ho, hstart', hend' ⟩ ← core.iter.range.IteratorRange.next_Usize_some_spec
    rw [ho]
    simp only
    have hg32 : iter.start.val < 32 := by omega
    -- the head/tail split, unified
    have hraw : (if iter.start < headG
        then (do let i ← iter.start * bitsU
                 load_u8x16 bytes i)
        else (do let s ← lift (Array.to_slice tailArr)
                 let i ← iter.start * bitsU
                 let i1 ← i - tailS
                 load_u8x16 s i1))
        ⦃ (raw : Vec128) => ∀ i < 16,
            (lane8 raw i).toNat = streamByte bytes (iter.start.val * w + i) ⦄ := by
      have hmulok : iter.start.val * w ≤ Usize.max := by
        have : iter.start.val * w ≤ 31 * 13 := Nat.mul_le_mul (by omega) hw13
        scalar_tac
      by_cases hhead : iter.start < headG
      · rw [if_pos hhead]
        let* ⟨ i1, hi1 ⟩ ← Std.Usize.mul_spec
        exact head_raw bytes w hw1 hlen iter.start.val (by scalar_tac) i1 (by scalar_tac)
      · rw [if_neg hhead]
        have hge : headGroups w ≤ iter.start.val := by scalar_tac
        have hts : tailStart w ≤ iter.start.val * w := by
          unfold tailStart
          exact Nat.mul_le_mul_right w hge
        simp only [lift, bind_tc_ok]
        let* ⟨ i1, hi1 ⟩ ← Std.Usize.mul_spec
        let* ⟨ i2, hi2 ⟩ ← Std.Usize.sub_spec (x := i1) (y := tailS) (by scalar_tac)
        exact tail_raw bytes w hw1 tailArr htail iter.start.val hge hg32 i2 (by scalar_tac)
    apply WP.spec_bind hraw
    intro raw hrawb
    -- the two passes of four coefficients
    obtain ⟨winLo, hwinLo, hwinLob⟩ := tbl1_u8_model raw shufLo
    obtain ⟨winHi, hwinHi, hwinHib⟩ := tbl1_u8_model raw shufHi
    obtain ⟨shLo, hshLo, hshLob⟩ := ushl_u32_model winLo shiftLo
    obtain ⟨valLo, hvalLo, hvalLob⟩ := and_model shLo maskV
    obtain ⟨shHi, hshHi, hshHib⟩ := ushl_u32_model winHi shiftHi
    obtain ⟨valHi, hvalHi, hvalHib⟩ := and_model shHi maskV
    rw [hwinLo, bind_tc_ok, hwinHi, bind_tc_ok, hshLo, bind_tc_ok, hvalLo, bind_tc_ok,
      hshHi, bind_tc_ok, hvalHi, bind_tc_ok]
    have hlo := lane_chain_value bytes w hw13 iter.start.val 0 (by omega)
      raw shufLo shiftLo maskV winLo shLo valLo hrawb
      (by simpa using hshufLo) (by simpa using hshiftLo) hmask hwinLob hshLob hvalLob
    have hhi := lane_chain_value bytes w hw13 iter.start.val 4 (by omega)
      raw shufHi shiftHi maskV winHi shHi valHi hrawb hshufHi hshiftHi hmask
      hwinHib hshHib hvalHib
    -- the narrowing, which is exact
    have hbound : ∀ (v : Vec128) (base : ℕ),
        (∀ j < 4, (lane32 v j).toNat = streamNat bytes (w * (8 * iter.start.val + base + j)) w) →
        ∀ m < 4, (lane32 v m).toNat < 2 ^ 16 := by
      intro v base hv m hm
      rw [hv m hm]
      exact lt_of_lt_of_le (streamNat_lt _ _ _)
        (Nat.pow_le_pow_right (by norm_num) (by omega))
    obtain ⟨narrow, hnarrow, hnarrowb⟩ := xtn_pair_32_model valLo valHi
    rw [hnarrow, bind_tc_ok]
    have hlanes := xtn_pair_value valLo valHi narrow (hbound valLo 0 hlo) (hbound valHi 4 hhi)
      hnarrowb
    -- the store writes exactly this group's eight outputs
    obtain ⟨out1, hout1, hout1v⟩ := store_u16_spec out iter.start narrow (by scalar_tac)
    rw [hout1, bind_tc_ok]
    apply WP.spec_mono (loop_spec bytes w hw1 hw13 hlen bitsU hbitsU shufLo shufHi shiftLo
      shiftHi maskV hshufLo hshufHi hshiftLo hshiftHi hmask headG tailS hheadG htailS tailArr
      htail iter1 (by rw [hend']; exact hend) out1)
    intro r hr j hj
    rw [hr j hj]
    by_cases hlow : j < 8 * iter1.start.val
    · rw [if_pos hlow]
      have hj16 : (out1.val[j]!).val = ((out1.val[j]!).bv).toNat := rfl
      rw [hj16, hout1v j hj]
      by_cases hin : 8 * iter.start.val ≤ j ∧ j < 8 * iter.start.val + 8
      · rw [if_pos hin, if_neg (by omega)]
        have hi8 : j - 8 * iter.start.val < 8 := by omega
        show (lane16 narrow (j - 8 * iter.start.val)).toNat = _
        rw [hlanes (j - 8 * iter.start.val) hi8]
        by_cases hhalf : j - 8 * iter.start.val < 4
        · rw [if_pos hhalf, hlo _ hhalf]
          congr 2
          omega
        · rw [if_neg hhalf, hhi _ (by omega)]
          congr 2
          omega
      · rw [if_neg hin, if_pos (by omega)]
        rfl
    · rw [if_neg hlow, if_neg (by omega)]
  · let* ⟨ o, iter1, hnone, _ ⟩ ← core.iter.range.IteratorRange.next_Usize_none_spec
    rw [hnone]
    refine (WP.spec_ok _).mpr (fun j hj => ?_)
    rw [if_pos (by omega)]
termination_by iter.«end».val - iter.start.val
decreasing_by scalar_decr_tac

/-! ## The zero-padded scratch buffer

`tail[..len - tail_start].copy_from_slice(&bytes[tail_start..])` leaves a 32-byte buffer holding
the last few bytes of `bytes` followed by zeros — which is exactly `streamByte` past the end, so
the tail loads need no separate case. -/

theorem tail_buffer_bytes (bytes : Slice U8) (w : ℕ) (hlen : bytes.length = 32 * w)
    (tailArr : Array U8 32#usize)
    (hval : tailArr.val
      = (Array.repeat 32#usize (0#u8)).val.setSlice! 0 (bytes.val.drop (tailStart w))) :
    ∀ p < 32, (tailArr.val[p]!).val = streamByte bytes (tailStart w + p) := by
  intro p hp
  have hblen : bytes.val.length = 32 * w := by simpa [Slice.length] using hlen
  have hts : tailStart w ≤ 32 * w := by
    unfold tailStart headGroups
    have : (32 - tailGroups w) * w ≤ 32 * w := Nat.mul_le_mul_right w (by omega)
    omega
  have hdlen : (bytes.val.drop (tailStart w)).length = 32 * w - tailStart w := by
    rw [List.length_drop, hblen]
  -- `tailArr` is the replicate with the drop written over its front
  have harr : tailArr = Std.Array.setSlice! (Array.repeat 32#usize (0#u8)) 0
      (bytes.val.drop (tailStart w)) := by
    apply Subtype.ext
    rw [hval]
    rfl
  rcases Nat.lt_or_ge p (32 * w - tailStart w) with hin | hout
  · -- inside the copied region
    have hb : tailArr.val[p]! = (bytes.val.drop (tailStart w))[p]! := by
      rw [harr, ← Std.Array.getElem!_Nat_eq,
        Std.Array.setSlice!_getElem!_middle _ _ 0 p ⟨by omega, by omega, by simpa using hp⟩,
        Nat.sub_zero]
    rw [hb]
    unfold streamByte
    rw [List.getElem!_drop]
  · -- past the end: the buffer holds zero, and so does the stream
    have hb : tailArr.val[p]! = (0#u8 : U8) := by
      rw [harr, ← Std.Array.getElem!_Nat_eq,
        Std.Array.setSlice!_getElem!_suffix _ _ 0 p (by omega), Std.Array.getElem!_Nat_eq,
        Array.repeat_val, getElem!_pos _ p (by simpa using hp)]
      exact List.eq_of_mem_replicate (List.getElem_mem _)
    rw [hb]
    unfold streamByte
    rw [getElem!_neg bytes.val (tailStart w + p) (by omega)]
    rfl

/-! ## The whole routine

The constant setup, then the loop.  `GROUPS` is `RING_DEG / 8 = 32`; `tail_groups` is
`⌊15/bits⌋`; and the scratch buffer is filled by the three slice operations whose composite
effect `tail_buffer_bytes` reads off. -/

open RustKopisNeon.backend.neon.intrinsics in
/-- **`backend::neon::ser::deserialize` computes the bit stream.**  Coefficient `j` of the
result is the `bits`-bit window at bit `bits·j`, which is exactly what
`ser::deserialize_generic` produces. -/
theorem deserialize_streamNat (bytes : Slice U8) (w : ℕ) (hw1 : 1 ≤ w) (hw13 : w ≤ 13)
    (hlen : bytes.length = 32 * w) (bitsU : Usize) (hbitsU : bitsU.val = w) :
    backend.neon.ser.deserialize bytes bitsU
      ⦃ (r : Array U16 256#usize) => ∀ j < 256,
          (r.val[j]!).val = streamNat bytes (w * j) w ⦄ := by
  have hblen : bytes.val.length = 32 * w := by simpa [Slice.length] using hlen
  have h2w : 2 ^ w ≤ 8192 := by
    calc 2 ^ w ≤ 2 ^ 13 := Nat.pow_le_pow_right (by norm_num) hw13
      _ = 8192 := by norm_num
  have h2wpos : 1 ≤ 2 ^ w := Nat.one_le_two_pow
  unfold backend.neon.ser.deserialize
  -- the plan for this width
  apply WP.spec_bind PLANS_spec
  intro a hplans
  obtain ⟨hpshuf, hpshift⟩ := hplans w hw1 hw13
  have halen : a.val.length = 14 := by have := a.property; scalar_tac
  let* ⟨ plan, hplan ⟩ ← Array.index_usize_spec a bitsU (by scalar_tac)
  have hplan' : plan = a.val[w]! := by
    rw [hplan, getElem!_pos a.val w (by omega)]
    congr 1
  have hshuflen : (Array.to_slice plan.shuffle).val.length = 32 := by simp [Array.to_slice]
  have hshufval : ∀ m : ℕ,
      ((Array.to_slice plan.shuffle).val[m]! : U8) = (plan.shuffle.val[m]! : U8) := by
    intro m; simp [Array.to_slice]
  simp only [lift, bind_tc_ok]
  -- the two halves of the `tbl` control
  obtain ⟨shufLo, hshufLoE, hshufLoL⟩ :=
    load_u8x16_spec (Array.to_slice plan.shuffle) 0#usize (by rw [hshuflen]; scalar_tac)
  obtain ⟨shufHi, hshufHiE, hshufHiL⟩ :=
    load_u8x16_spec (Array.to_slice plan.shuffle) 16#usize (by rw [hshuflen]; scalar_tac)
  rw [hshufLoE, bind_tc_ok, hshufHiE, bind_tc_ok]
  have hshufLo : ∀ i < 16, (lane8 shufLo i).toNat = planShuffle w (i / 4) (i % 4) := by
    intro i hi
    rw [hshufLoL i hi, hshufval]
    show ((plan.shuffle.val[(0#usize).val + i]!) : U8).val = _
    rw [show (0#usize).val + i = i from by scalar_tac, hplan']
    exact hpshuf i (by omega)
  have hshufHi : ∀ i < 16, (lane8 shufHi i).toNat = planShuffle w (4 + i / 4) (i % 4) := by
    intro i hi
    rw [hshufHiL i hi, hshufval]
    show ((plan.shuffle.val[(16#usize).val + i]!) : U8).val = _
    rw [show (16#usize).val + i = 16 + i from by scalar_tac, hplan']
    rw [hpshuf (16 + i) (by omega)]
    congr 1
    · omega
    · omega
  -- the two halves of the shift counts, negated
  obtain ⟨shiftLo, hshiftLoE, hshiftLoL⟩ := load_i32_spec plan.shift 0#usize (by scalar_tac)
  obtain ⟨shiftHi, hshiftHiE, hshiftHiL⟩ := load_i32_spec plan.shift 1#usize (by scalar_tac)
  rw [hshiftLoE, bind_tc_ok, hshiftHiE, bind_tc_ok]
  have hshiftLo : ∀ m < 4, shiftAmount (lane32 shiftLo m) = -(planShift w m : ℤ) := by
    intro m hm
    rw [hshiftLoL m hm]
    refine shiftAmount32_neg _ _ (by have := planShift_lt w m; omega) ?_
    show ((plan.shift.val[4 * (0#usize).val + m]!) : I32).val = _
    rw [show 4 * (0#usize).val + m = m from by scalar_tac, hplan']
    exact hpshift m (by omega)
  have hshiftHi : ∀ m < 4, shiftAmount (lane32 shiftHi m) = -(planShift w (4 + m) : ℤ) := by
    intro m hm
    rw [hshiftHiL m hm]
    refine shiftAmount32_neg _ _ (by have := planShift_lt w (4 + m); omega) ?_
    show ((plan.shift.val[4 * (1#usize).val + m]!) : I32).val = _
    rw [show 4 * (1#usize).val + m = 4 + m from by scalar_tac, hplan']
    exact hpshift (4 + m) (by omega)
  -- the mask `(1 << bits) - 1`, unsigned
  let* ⟨ i, hi, hibv ⟩ ← Std.U32.ShiftLeft_spec 1#u32 bitsU (by scalar_tac)
  have hsize : (8192 : ℕ) < Std.U32.size := by
    norm_num [Std.U32.size, UScalar.size, Std.U32.numBits]
  have hiv : i.val = 2 ^ w := by
    rw [hi, hbitsU, Nat.shiftLeft_eq, one_mul, Nat.mod_eq_of_lt (lt_of_le_of_lt h2w hsize)]
  let* ⟨ i1, hi1 ⟩ ← Std.U32.sub_spec (x := i) (y := 1#u32) (by scalar_tac)
  have hi1v : i1.val = 2 ^ w - 1 := by rw [hi1, hiv]
  obtain ⟨maskV, hmaskE, hmaskL⟩ := dup_n_u32_spec i1
  rw [hmaskE, bind_tc_ok]
  have hmask : ∀ m < 4, (lane32 maskV m).toNat = 2 ^ w - 1 := by
    intro m hm
    rw [hmaskL m hm]
    exact hi1v
  -- the group geometry
  let* ⟨ tg, htg ⟩ ← Std.Usize.div_spec
  have htgv : tg.val = tailGroups w := by unfold tailGroups; rw [htg, hbitsU]
  have hgroups : backend.neon.ser.GROUPS = ok 32#usize := by
    simp only [backend.neon.ser.GROUPS, consts.RING_DEG]
    rfl
  rw [hgroups, bind_tc_ok]
  have htgle : tg.val ≤ 32 := by rw [htgv]; exact le_of_lt (tailGroups_mul w)
  let* ⟨ hg, hhg ⟩ ← Std.Usize.sub_spec (x := 32#usize) (y := tg) (by scalar_tac)
  have hhgv : hg.val = headGroups w := by unfold headGroups; rw [hhg, htgv]
  let* ⟨ ts, hts ⟩ ← Std.Usize.mul_spec (x := hg) (y := bitsU)
    (by rw [hhgv, hbitsU]; have : headGroups w * w ≤ 32 * 13 := Nat.mul_le_mul
          (by unfold headGroups; omega) hw13
        scalar_tac)
  have htsv : ts.val = tailStart w := by unfold tailStart; rw [hts, hhgv, hbitsU]
  -- the zero-padded scratch buffer
  have htsle : ts.val ≤ (Slice.len bytes).val := by
    rw [Slice.len_val, htsv]
    show tailStart w ≤ bytes.length
    rw [hlen]
    unfold tailStart headGroups
    have : (32 - tailGroups w) * w ≤ 32 * w := Nat.mul_le_mul_right w (by omega)
    omega
  let* ⟨ i4, hi4 ⟩ ← Std.Usize.sub_spec (x := Slice.len bytes) (y := ts) (by scalar_tac)
  have hi4v : i4.val = 32 * w - tailStart w := by
    rw [hi4, htsv, Slice.len_val, hlen]
  step with Std.Array.index_mut_SliceIndexRangeToUsizeSlice
    (a := Array.repeat 32#usize (0#u8)) (r := { «end» := i4 })
    (by have := copy_len_le w hw1
        simp only [UScalar.le_equiv]
        rw [hi4v]
        scalar_tac) as ⟨s, back, hs, hslen, hback⟩
  step with core.slice.index.SliceIndexRangeFromUsizeSlice.index.step_spec as ⟨s1, hs1, hs1len⟩
  step with core.slice.Slice.copy_from_slice.step_spec as ⟨s2, hs2⟩
  -- the buffer now holds the tail bytes followed by zeros
  have htailval : (back s2).val
      = (Array.repeat 32#usize (0#u8)).val.setSlice! 0 (bytes.val.drop (tailStart w)) := by
    rw [hback s2, hs2, hs1, htsv]
  have htail := tail_buffer_bytes bytes w hlen (back s2) htailval
  -- and the loop does the rest
  apply WP.spec_mono (loop_spec bytes w hw1 hw13 hlen bitsU hbitsU shufLo shufHi shiftLo shiftHi
    maskV hshufLo hshufHi hshiftLo hshiftHi hmask hg ts hhgv htsv (back s2) htail
    ⟨0#usize, 32#usize⟩ rfl (Array.repeat 256#usize 0#u16))
  intro r hr j hj
  rw [hr j hj, if_neg (by simp)]

end Kopis.Neon
