/-
  # Kopis/Avx2/Ser.lean — the AVX2 deserializer computes the bit stream.

  Everything the loops need is already proved: `SerPlan.lean` pins the constant tables,
  `SerTail.lean` makes the head and tail loads say the same thing, `SerLane.lean` turns one
  `vpshufb`/`vpsrlvd`/`vpand` lane into one coefficient and one `vpackusdw`/`vpermq` pair into
  sixteen.  What is left is to run those over the two nested loops and read the result out of
  the output array:

      out[j] = streamNat bytes (bits · j) bits   for every j < 256

  which is exactly what `ser::deserialize_generic` computes, and hence the statement through
  which the two are equal.
-/
import Kopis.Avx2.SerTail

open Aeneas Aeneas.Std Result
open RustKopisAvx2

namespace Kopis.Avx2

open Kopis.Properties (streamNat streamByte streamNat_lt)

set_option maxHeartbeats 2000000

/-! ## Signed constants as bit patterns

The shift counts and the mask arrive as `i32`s whose *values* the plan spec fixes, while the
intrinsic axioms speak of their bit patterns.  For a non-negative `i32` the two agree. -/

/-- A non-negative `i32` has the bit pattern of its value. -/
theorem i32_bv_toNat {x : I32} {v : ℕ} (hv : x.val = (v : ℤ)) : x.bv.toNat = v := by
  have hlt : (x.bv.toNat : ℤ) < 2 ^ 32 := by exact_mod_cast x.bv.isLt
  have h := BitVec.toInt_eq_toNat_cond x.bv
  rw [show x.bv.toInt = (v : ℤ) from hv] at h
  split at h <;> omega

/-! ## Where a group's register comes from

The `if` in the loop body picks the direct load or the scratch-buffer one.  Both produce a
register whose bytes are the group's, which is the only thing the lane lemma needs. -/

open RustKopisAvx2.backend.avx2.intrinsics in
/-- A group in the head: loaded straight out of `bytes`. -/
theorem head_raw (bytes : Slice U8) (w : ℕ) (hw1 : 1 ≤ w) (hlen : bytes.length = 32 * w)
    (group : ℕ) (hg : group < headGroups w) (off : Usize) (hoff : off.val = group * w) :
    (do let v ← load_u8x16 bytes off
        broadcastsi128_si256 v)
      ⦃ (raw : Vec256) => ∀ i < 32,
          (lane8 raw i).toNat = streamByte bytes (group * w + i % 16) ⦄ := by
  have hb : off.val + 16 ≤ bytes.val.length := by
    have := head_load_in_bounds w group hw1 hg
    have hl : bytes.val.length = 32 * w := by simpa [Slice.length] using hlen
    omega
  obtain ⟨v, hv, hvl⟩ := load_u8x16_spec bytes off hb
  obtain ⟨raw, hraw, hrawb⟩ := broadcastsi128_si256_model v
  rw [hv, bind_tc_ok, hraw]
  simp only [WP.spec_ok]
  refine broadcast_bytes bytes (group * w) v raw (fun m hm => ?_) hrawb
  rw [hvl m hm, hoff]
  rfl

open RustKopisAvx2.backend.avx2.intrinsics in
/-- A group in the tail: loaded from the zero-padded scratch buffer, which holds the same
bytes — including, past the end of `bytes`, the same zeros. -/
theorem tail_raw (bytes : Slice U8) (w : ℕ) (hw1 : 1 ≤ w)
    (tailArr : Array U8 32#usize)
    (htail : ∀ p < 32, (tailArr.val[p]!).val = streamByte bytes (tailStart w + p))
    (group : ℕ) (hg : headGroups w ≤ group) (hg32 : group < 32)
    (off : Usize) (hoff : off.val = group * w - tailStart w) :
    (do let s ← lift (Array.to_slice tailArr)
        let v ← load_u8x16 s off
        broadcastsi128_si256 v)
      ⦃ (raw : Vec256) => ∀ i < 32,
          (lane8 raw i).toNat = streamByte bytes (group * w + i % 16) ⦄ := by
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
  obtain ⟨raw, hraw, hrawb⟩ := broadcastsi128_si256_model v
  simp only [lift, bind_tc_ok]
  rw [hv, bind_tc_ok, hraw]
  simp only [WP.spec_ok]
  refine broadcast_bytes bytes (group * w) v raw (fun m hm => ?_) hrawb
  have hidx : off.val + m < 32 := by rw [hoff]; have := tail_load_in_bounds w group hw1 hg32; omega
  have : ((Array.to_slice tailArr).val[off.val + m]!) = (tailArr.val[off.val + m]!) := by
    simp [Array.to_slice]
  rw [hvl m hm, this]
  show ((tailArr.val[off.val + m]!) : U8).val = _
  rw [htail _ hidx, hoff]
  congr 1
  omega

/-! ## The inner loop: the two groups of a pair

`Vec256` is an opaque extracted type with no `Inhabited` instance, so the two-element scratch
array is read with a bounds proof rather than `getElem!`.  `wAt` is that read, named to keep
the statements legible. -/

/-- Entry `h` of the inner loop's two-element accumulator. -/
def wAt (r : Array RustKopisAvx2.backend.avx2.intrinsics.Vec256 2#usize) (h : ℕ) (hh : h < 2) :
    RustKopisAvx2.backend.avx2.intrinsics.Vec256 :=
  r[h]'(by have := r.property; scalar_tac)

open RustKopisAvx2.backend.avx2.intrinsics in
theorem inner_loop_spec (bytes : Slice U8) (w : ℕ) (hw1 : 1 ≤ w) (hw13 : w ≤ 13)
    (hlen : bytes.length = 32 * w)
    (bitsU : Usize) (hbitsU : bitsU.val = w)
    (shuffleV shiftV maskV : Vec256)
    (hshuf : ∀ i < 32, (lane8 shuffleV i).toNat = planShuffle w (i / 4) (i % 4))
    (hshiftV : ∀ m < 8, (lane32 shiftV m).toNat = planShift w m)
    (hmask : ∀ m < 8, (lane32 maskV m).toNat = 2 ^ w - 1)
    (headG tailS : Usize) (hheadG : headG.val = headGroups w) (htailS : tailS.val = tailStart w)
    (tailArr : Array U8 32#usize)
    (htail : ∀ p < 32, (tailArr.val[p]!).val = streamByte bytes (tailStart w + p))
    (pair : Usize) (hpair : pair.val < 16)
    (iter : core.ops.range.Range Usize) (hend : iter.«end».val = 2)
    (wide : Array Vec256 2#usize) :
    backend.avx2.ser.deserialize_loop0_loop0 iter bytes bitsU shuffleV shiftV maskV headG tailS
      tailArr pair wide
      ⦃ (r : Array Vec256 2#usize) =>
          (∀ h (hh : h < 2), h < iter.start.val → wAt r h hh = wAt wide h hh) ∧
          (∀ h (hh : h < 2), iter.start.val ≤ h → ∀ k < 8,
              (lane32 (wAt r h hh) k).toNat
                = streamNat bytes (w * (8 * (2 * pair.val + h) + k)) w) ⦄ := by
  unfold backend.avx2.ser.deserialize_loop0_loop0
  by_cases hlt : iter.start.val < iter.«end».val
  · let* ⟨ o, iter1, ho, hstart', hend' ⟩ ← core.iter.range.IteratorRange.next_Usize_some_spec
    rw [ho]
    simp only
    have hhalf : iter.start.val < 2 := by omega
    let* ⟨ i, hi ⟩ ← Std.Usize.mul_spec
    let* ⟨ group, hgroup ⟩ ← Std.Usize.add_spec
    have hgv : group.val = 2 * pair.val + iter.start.val := by scalar_tac
    have hg32 : group.val < 32 := by omega
    -- the head/tail split, unified
    have hraw : (if group < headG
        then (do let i1 ← group * bitsU
                 let v ← load_u8x16 bytes i1
                 broadcastsi128_si256 v)
        else (do let s ← lift (Array.to_slice tailArr)
                 let i1 ← group * bitsU
                 let i2 ← i1 - tailS
                 let v ← load_u8x16 s i2
                 broadcastsi128_si256 v))
        ⦃ (raw : Vec256) => ∀ i < 32,
            (lane8 raw i).toNat = streamByte bytes (group.val * w + i % 16) ⦄ := by
      have hmulok : group.val * w ≤ Usize.max := by
        have : group.val * w ≤ 31 * 13 := Nat.mul_le_mul (by omega) hw13
        scalar_tac
      by_cases hhead : group < headG
      · rw [if_pos hhead]
        let* ⟨ i1, hi1 ⟩ ← Std.Usize.mul_spec
        exact head_raw bytes w hw1 hlen group.val (by scalar_tac) i1 (by scalar_tac)
      · rw [if_neg hhead]
        simp only [lift, bind_tc_ok]
        have hge : headGroups w ≤ group.val := by scalar_tac
        have hts : tailStart w ≤ group.val * w := by
          unfold tailStart
          exact Nat.mul_le_mul_right w hge
        let* ⟨ i1, hi1 ⟩ ← Std.Usize.mul_spec
        let* ⟨ i2, hi2 ⟩ ← Std.Usize.sub_spec (x := i1) (y := tailS) (by scalar_tac)
        exact tail_raw bytes w hw1 tailArr htail group.val hge hg32 i2 (by scalar_tac)
    apply WP.spec_bind hraw
    intro raw hrawb
    obtain ⟨windows, hwin, hwinb⟩ := shuffle_epi8_model raw shuffleV
    obtain ⟨shd, hshd, hshdb⟩ := srlv_epi32_model windows shiftV
    obtain ⟨v1, hv1e, hv1b⟩ := and_si256_model shd maskV
    rw [hwin, bind_tc_ok, hshd, bind_tc_ok, hv1e, bind_tc_ok]
    have hv1 := lane_chain_value bytes w hw13 group.val raw shuffleV shiftV maskV windows shd v1
      hrawb hshuf hshiftV hmask hwinb hshdb hv1b
    let* ⟨ a, ha ⟩ ← Array.update_spec
    apply WP.spec_mono (inner_loop_spec bytes w hw1 hw13 hlen bitsU hbitsU shuffleV shiftV maskV
      hshuf hshiftV hmask headG tailS hheadG htailS tailArr htail pair hpair iter1
      (by rw [hend']; exact hend) a)
    rintro r ⟨hkeep, hprop⟩
    have hwidelen : wide.val.length = 2 := by have := wide.property; scalar_tac
    have hae : ∀ j (hj : j < 2), j ≠ iter.start.val → wAt a j hj = wAt wide j hj := by
      intro j hj hne
      unfold wAt
      simp only [ha]
      grind
    have hax : wAt a iter.start.val hhalf = v1 := by
      unfold wAt
      simp only [ha]
      grind
    refine ⟨fun h hh hlow => ?_, fun h hh hhi => ?_⟩
    · rw [hkeep h hh (by omega), hae h hh (by omega)]
    · rcases Nat.lt_or_ge h iter1.start.val with hcase | hcase
      · have hheq : h = iter.start.val := by omega
        subst hheq
        rw [hkeep _ hh (by omega), hax]
        intro k hk
        rw [hv1 k hk, hgv]
      · exact hprop h hh hcase
  · let* ⟨ o, iter1, hnone, _ ⟩ ← core.iter.range.IteratorRange.next_Usize_none_spec
    rw [hnone]
    refine (WP.spec_ok _).mpr ⟨fun j hj _ => rfl, fun j hj hhi => by omega⟩
termination_by iter.«end».val - iter.start.val
decreasing_by scalar_decr_tac

/-! ## The outer loop: sixteen pairs of groups

Each iteration runs the inner loop over one pair, packs the two resulting vectors into sixteen
16-bit lanes, repairs the interleaving `vpackusdw` introduces, and stores them.  The store
covers `out[16·pair .. 16·pair + 16]`, so after the whole loop every one of the 256 outputs has
been written exactly once. -/

open RustKopisAvx2.backend.avx2.intrinsics in
theorem outer_loop_spec (bytes : Slice U8) (w : ℕ) (hw1 : 1 ≤ w) (hw13 : w ≤ 13)
    (hlen : bytes.length = 32 * w)
    (bitsU : Usize) (hbitsU : bitsU.val = w)
    (shuffleV shiftV maskV : Vec256)
    (hshuf : ∀ i < 32, (lane8 shuffleV i).toNat = planShuffle w (i / 4) (i % 4))
    (hshiftV : ∀ m < 8, (lane32 shiftV m).toNat = planShift w m)
    (hmask : ∀ m < 8, (lane32 maskV m).toNat = 2 ^ w - 1)
    (headG tailS : Usize) (hheadG : headG.val = headGroups w) (htailS : tailS.val = tailStart w)
    (tailArr : Array U8 32#usize)
    (htail : ∀ p < 32, (tailArr.val[p]!).val = streamByte bytes (tailStart w + p))
    (iter : core.ops.range.Range Usize) (hend : iter.«end».val = 16)
    (out : Array U16 256#usize) :
    backend.avx2.ser.deserialize_loop0 iter bytes bitsU shuffleV shiftV maskV headG tailS
      tailArr out
      ⦃ (r : Array U16 256#usize) => ∀ j < 256,
          (r.val[j]!).val =
            if j < 16 * iter.start.val then (out.val[j]!).val
            else streamNat bytes (w * j) w ⦄ := by
  unfold backend.avx2.ser.deserialize_loop0
  by_cases hlt : iter.start.val < iter.«end».val
  · let* ⟨ o, iter1, ho, hstart', hend' ⟩ ← core.iter.range.IteratorRange.next_Usize_some_spec
    rw [ho]
    simp only
    have hpair : iter.start.val < 16 := by omega
    obtain ⟨z, hz, -⟩ := setzero_si256_spec
    rw [hz, bind_tc_ok]
    -- the two groups of this pair
    apply WP.spec_bind (inner_loop_spec bytes w hw1 hw13 hlen bitsU hbitsU shuffleV shiftV maskV
      hshuf hshiftV hmask headG tailS hheadG htailS tailArr htail iter.start hpair
      ⟨0#usize, 2#usize⟩ rfl (Array.repeat 2#usize z))
    rintro wide1 ⟨-, hlanes⟩
    have hl0 := hlanes 0 (by omega) (by simp)
    have hl1 := hlanes 1 (by omega) (by simp)
    let* ⟨ v1, hv1 ⟩ ← Array.index_usize_spec wide1 0#usize (by scalar_tac)
    let* ⟨ v2, hv2 ⟩ ← Array.index_usize_spec wide1 1#usize (by scalar_tac)
    have hv1e : v1 = wAt wide1 0 (by omega) := by rw [hv1]; rfl
    have hv2e : v2 = wAt wide1 1 (by omega) := by rw [hv2]; rfl
    -- the coefficients are all `< 2 ^ w`, so the unsigned pack is exact
    have hb0 : ∀ m < 8, (lane32 v1 m).toNat < 2 ^ 13 := by
      intro m hm
      rw [hv1e, hl0 m hm]
      exact lt_of_lt_of_le (streamNat_lt _ _ _) (Nat.pow_le_pow_right (by norm_num) hw13)
    have hb1 : ∀ m < 8, (lane32 v2 m).toNat < 2 ^ 13 := by
      intro m hm
      rw [hv2e, hl1 m hm]
      exact lt_of_lt_of_le (streamNat_lt _ _ _) (Nat.pow_le_pow_right (by norm_num) hw13)
    obtain ⟨packed, hpacked, hpackedb⟩ := packus_epi32_model v1 v2
    obtain ⟨v3, hv3, hv3b⟩ := permute4x64_epi64_model 216#i32 packed
    rw [hpacked, bind_tc_ok, hv3, bind_tc_ok]
    have hres := pack_permute_value v1 v2 packed v3 hb0 hb1 hpackedb hv3b
    -- the store writes exactly this pair's sixteen outputs
    obtain ⟨out1, hout1, hout1v⟩ := store_u16_spec out iter.start v3 (by scalar_tac)
    rw [hout1, bind_tc_ok]
    apply WP.spec_mono (outer_loop_spec bytes w hw1 hw13 hlen bitsU hbitsU shuffleV shiftV maskV
      hshuf hshiftV hmask headG tailS hheadG htailS tailArr htail iter1
      (by rw [hend']; exact hend) out1)
    intro r hr j hj
    rw [hr j hj]
    by_cases hlow : j < 16 * iter1.start.val
    · rw [if_pos hlow]
      have hj16 : (out1.val[j]!).val = ((out1.val[j]!).bv).toNat := rfl
      rw [hj16, hout1v j hj]
      by_cases hin : 16 * iter.start.val ≤ j ∧ j < 16 * iter.start.val + 16
      · rw [if_pos hin, if_neg (by omega)]
        -- lane `j - 16·pair` of the packed result is coefficient `j`
        have hi16 : j - 16 * iter.start.val < 16 := by omega
        have := hres (j - 16 * iter.start.val) hi16
        show (lane16 v3 (j - 16 * iter.start.val)).toNat = _
        rw [this]
        by_cases hhalf : j - 16 * iter.start.val < 8
        · rw [if_pos hhalf, hv1e, hl0 _ hhalf]
          congr 2
          omega
        · rw [if_neg hhalf, hv2e, hl1 _ (by omega)]
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

open RustKopisAvx2.backend.avx2.intrinsics in
/-- **`backend::avx2::ser::deserialize` computes the bit stream.**  Coefficient `j` of the
result is the `bits`-bit window at bit `bits·j`, which is exactly what
`ser::deserialize_generic` produces. -/
theorem deserialize_streamNat (bytes : Slice U8) (w : ℕ) (hw1 : 1 ≤ w) (hw13 : w ≤ 13)
    (hlen : bytes.length = 32 * w) (bitsU : Usize) (hbitsU : bitsU.val = w) :
    backend.avx2.ser.deserialize bytes bitsU
      ⦃ (r : Array U16 256#usize) => ∀ j < 256,
          (r.val[j]!).val = streamNat bytes (w * j) w ⦄ := by
  have hblen : bytes.val.length = 32 * w := by simpa [Slice.length] using hlen
  have h2w : 2 ^ w ≤ 8192 := by
    calc 2 ^ w ≤ 2 ^ 13 := Nat.pow_le_pow_right (by norm_num) hw13
      _ = 8192 := by norm_num
  have h2wpos : 1 ≤ 2 ^ w := Nat.one_le_two_pow
  unfold backend.avx2.ser.deserialize
  -- the plan for this width
  apply WP.spec_bind PLANS_spec
  intro a hplans
  obtain ⟨hpshuf, hpshift⟩ := hplans w hw1 hw13
  have halen : a.val.length = 14 := by have := a.property; scalar_tac
  let* ⟨ plan, hplan ⟩ ← Array.index_usize_spec a bitsU (by scalar_tac)
  have hplan' : plan = a.val[w]! := by
    rw [hplan, getElem!_pos a.val w (by omega)]
    congr 1
  -- the shuffle control and the shift counts
  obtain ⟨shuffleV, hshufe, hshufl⟩ := load_u8_spec plan.shuffle 0#usize (by scalar_tac)
  rw [hshufe, bind_tc_ok]
  obtain ⟨shiftV, hshie, hshil⟩ := load_i32_spec plan.shift 0#usize (by scalar_tac)
  rw [hshie, bind_tc_ok]
  have hshuf : ∀ i < 32, (lane8 shuffleV i).toNat = planShuffle w (i / 4) (i % 4) := by
    intro i hi
    rw [hshufl i hi]
    show ((plan.shuffle.val[32 * (0#usize).val + i]!) : U8).val = _
    rw [show 32 * (0#usize).val + i = i from by scalar_tac, hplan']
    exact hpshuf i hi
  have hshiftV : ∀ m < 8, (lane32 shiftV m).toNat = planShift w m := by
    intro m hm
    rw [hshil m hm]
    refine i32_bv_toNat ?_
    rw [show 8 * (0#usize).val + m = m from by scalar_tac, hplan']
    exact_mod_cast hpshift m hm
  -- the mask `(1 << bits) - 1`
  have hshl : ((1#i32) <<< bitsU) = ok ⟨(1#i32).bv <<< w⟩ := by
    simp only [HShiftLeft.hShiftLeft, IScalar.shiftLeft_UScalar, IScalar.shiftLeft, hbitsU]
    rw [if_pos (by simp only [IScalarTy.numBits]; omega)]
  rw [hshl, bind_tc_ok]
  have hnb : (2:ℕ) ^ IScalarTy.I32.numBits = 2 ^ 32 := rfl
  have hitoNat : ((⟨(1#i32).bv <<< w⟩ : I32)).bv.toNat = 2 ^ w := by
    show ((1#i32).bv <<< w).toNat = _
    rw [BitVec.toNat_shiftLeft]
    simp only [Nat.shiftLeft_eq]
    rw [show ((1#i32).bv).toNat = 1 from rfl, one_mul, Nat.mod_eq_of_lt (by omega)]
  have hival : ((⟨(1#i32).bv <<< w⟩ : I32)).val = ((2 ^ w : ℕ) : ℤ) := by
    show ((1#i32).bv <<< w).toInt = _
    rw [BitVec.toInt_eq_toNat_cond]
    rw [if_pos (by rw [show ((1#i32).bv <<< w).toNat = 2 ^ w from hitoNat]
                   simp only [IScalarTy.numBits]
                   omega)]
    exact_mod_cast congrArg Nat.cast hitoNat
  have hone : ((1#i32 : I32).val) = 1 := rfl
  let* ⟨ i1, hi1 ⟩ ← Std.I32.sub_spec (x := (⟨(1#i32).bv <<< w⟩ : I32)) (y := 1#i32)
    (by rw [hival]; simp only [Std.I32.min_eq]; omega)
    (by rw [hival]; simp only [Std.I32.max_eq]; omega)
  have hi1bv : i1.bv.toNat = 2 ^ w - 1 := by
    refine i32_bv_toNat ?_
    rw [hi1, hival]
    push_cast [Nat.cast_sub h2wpos]
    ring
  obtain ⟨maskV, hmaske, hmaskl⟩ := set1_epi32_spec i1
  rw [hmaske, bind_tc_ok]
  have hmask : ∀ m < 8, (lane32 maskV m).toNat = 2 ^ w - 1 := by
    intro m hm
    rw [hmaskl m hm]
    exact hi1bv
  -- the group geometry
  let* ⟨ tg, htg ⟩ ← Std.Usize.div_spec
  have htgv : tg.val = tailGroups w := by unfold tailGroups; rw [htg, hbitsU]
  have hgroups : backend.avx2.ser.GROUPS = ok 32#usize := by
    simp only [backend.avx2.ser.GROUPS, consts.RING_DEG]
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
  have hi5 : (32#usize : Usize) / 2#usize = ok 16#usize := by rfl
  rw [hi5, bind_tc_ok]
  -- the buffer now holds the tail bytes followed by zeros
  have htailval : (back s2).val
      = (Array.repeat 32#usize (0#u8)).val.setSlice! 0 (bytes.val.drop (tailStart w)) := by
    rw [hback s2, hs2, hs1, htsv]
  have htail := tail_buffer_bytes bytes w hlen (back s2) htailval
  -- and the loop does the rest
  apply WP.spec_mono (outer_loop_spec bytes w hw1 hw13 hlen bitsU hbitsU shuffleV shiftV maskV
    hshuf hshiftV hmask hg ts hhgv htsv (back s2) htail ⟨0#usize, 16#usize⟩ rfl
    (Array.repeat 256#usize 0#u16))
  intro r hr j hj
  rw [hr j hj, if_neg (by simp)]

end Kopis.Avx2
