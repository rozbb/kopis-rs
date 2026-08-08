/-
  # Kopis/Neon/Keccak/Xof2.lean — the two-way XOF, end to end.

  Everything below this file proves one piece of `keccak.rs`: `RoundSpec.lean` the round,
  `Permute.lean` the twelve of them, `Absorb.lean` getting a padded block into the registers,
  `Squeeze.lean` getting bytes back out.  This file is the assembly, and then the conformance
  statement: sponge `l` of `xof2` is `turboSHAKE RATE (prefix ‖ suffix_l) DS N`, byte for byte.

  The two sponges never interact, so the whole file is stated at a fixed sponge `l < 2`.

  One block is all `xof2` ever absorbs: the Rust `const`-asserts `32 + S < RATE`, so the prefix,
  suffix and domain separator always fit, and `pad_block` produces RFC 9861's `pad10*1` directly.
  That is why there is no absorb *loop* here — only the transpose that gets the block into the
  registers, and the capacity above `RATE` which stays zero from the initial `dup_n_u64 0`.
-/
import Kopis.Neon.Keccak.Squeeze
import Kopis.Keccak.Conform

open Aeneas Aeneas.Std Result
open RustKopisNeon
open RustKopisNeon.backend.neon.intrinsics
open Kopis.Bits
open Spec (𝔹)

namespace Kopis.Neon.Keccak

open Kopis.Keccak
open Spec.SHA3

set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

noncomputable section

/-- **`keccak::pad_block` builds TurboSHAKE's one-block padded input.**  Bytes `0..32` are the
prefix, `32..32+S` the suffix, byte `32+S` is the domain separator, the last byte of the block is
`0x80`, and everything between is zero — RFC 9861's `pad10*1` when the whole message fits in one
block, which is what `32 + S < RATE` (a `const` assertion in the Rust) guarantees.

`hS` is one stronger than the Rust's assertion: it also separates the domain-separator byte from
the final `0x80` byte.  Kopis satisfies it with room to spare (`S` is 1 or 2, `RATE` is 136 or
168); without it the two writes would land on the same byte and it would hold `DS ||| 0x80`. -/
theorem pad_block_spec (RATE : Std.Usize) (DS : Std.U8) {S : Std.Usize}
    (prefix1 : Std.Array Std.U8 32#usize) (suffix : Std.Array Std.U8 S)
    (hS : 32 + S.val + 1 < RATE.val) :
    backend.neon.keccak.pad_block RATE DS prefix1 suffix ⦃ (b : Std.Array Std.U8 RATE) => ∀ j < RATE.val,
          b.val[j]! =
            if j < 32 then prefix1.val[j]!
            else if j < 32 + S.val then suffix.val[j - 32]!
            else if j = 32 + S.val then DS
            else if j = RATE.val - 1 then 128#u8
            else 0#u8 ⦄ := by
  have hRmax : RATE.val ≤ Std.Usize.max := by scalar_tac
  have hplen : prefix1.val.length = 32 := prefix1.property
  have hsuflen : suffix.val.length = S.val := suffix.property
  unfold backend.neon.keccak.pad_block
  have h32 : (32#usize : Std.Usize) ≤ RATE := by rw [Std.UScalar.le_equiv]; simp; omega
  step with Std.Array.index_mut_SliceIndexRangeToUsizeSlice as ⟨s, back, hsval, hslen, hsback⟩
  rw [show (lift (Std.Array.to_slice prefix1) : Result (Slice Std.U8))
        = ok (Std.Array.to_slice prefix1) from rfl, bind_tc_ok]
  have hcp1 : s.length = (Std.Array.to_slice prefix1).length := by
    rw [hslen]; simp only [Slice.length, Std.Array.val_to_slice, hplen]
  step with core.slice.Slice.copy_from_slice.step_spec as ⟨s2, hs2⟩
  let* ⟨ i, hi ⟩ ← Std.Usize.add_spec (x := 32#usize) (y := S) (by scalar_tac)
  have hiv : i.val = 32 + S.val := by rw [hi]
  have hb1len : (back s2).val.length = RATE.val := (back s2).property
  have hlo : (32#usize : Std.Usize) ≤ i := by rw [Std.UScalar.le_equiv, hiv]; simp
  have hhi : i ≤ RATE := by rw [Std.UScalar.le_equiv, hiv]; omega
  step with Std.Array.index_mut_SliceIndexRangeUsizeSlice.step as ⟨s3, imb1, hs3val, hs3len, hs3back⟩
  rw [show (lift (Std.Array.to_slice suffix) : Result (Slice Std.U8))
        = ok (Std.Array.to_slice suffix) from rfl, bind_tc_ok]
  have hcp2 : s3.length = (Std.Array.to_slice suffix).length := by
    rw [hs3len]; simp only [Slice.length, Std.Array.val_to_slice, hsuflen]; omega
  step with core.slice.Slice.copy_from_slice.step_spec as ⟨s5, hs5⟩
  have hb2len : (imb1 s5).val.length = RATE.val := (imb1 s5).property
  have hbnd2 : i.val < (imb1 s5).length := by
    show i.val < (imb1 s5).val.length
    rw [hb2len, hiv]; omega
  let* ⟨ b3, hb3 ⟩ ← Array.update_spec (imb1 s5) i DS hbnd2
  let* ⟨ i1, hi1, _ ⟩ ← Std.Usize.sub_spec (x := RATE) (y := 1#usize) (by scalar_tac)
  have hi1v : i1.val = RATE.val - 1 := by rw [hi1]
  have hb3len : b3.val.length = RATE.val := b3.property
  have hbnd3 : i1.val < b3.length := by
    show i1.val < b3.val.length
    rw [hb3len, hi1v]; omega
  let* ⟨ i2, hi2 ⟩ ← Array.index_usize_spec b3 i1 hbnd3
  -- the byte layout, built up one write at a time
  have hzero : ∀ j, j < RATE.val → (Std.Array.repeat RATE 0#u8).val[j]! = 0#u8 := by
    intro j hj
    rw [Std.Array.repeat_val, getElem!_pos _ j (by rw [List.length_replicate]; exact hj)]
    simp
  have hb1 : (back s2).val = (Std.Array.repeat RATE 0#u8).val.setSlice! 0 prefix1.val := by
    rw [hsback s2, hs2, Std.Array.val_to_slice]
  have hb2 : (imb1 s5).val = (back s2).val.setSlice! 32 suffix.val := by
    rw [hs3back s5, hs5, Std.Array.val_to_slice]
  have hb3v : b3.val = ((imb1 s5).val).set i.val DS := by rw [hb3]; simp only [Std.Array.set_val_eq]
  rw [show (lift (i2 ||| 128#u8) : Result Std.U8) = ok (i2 ||| 128#u8) from rfl, bind_tc_ok]
  have hlenb2 : (imb1 s5).val.length = RATE.val := hb2len
  have hi2zero : i2 = 0#u8 := by
    rw [hi2, ← getElem!_pos b3.val i1.val (by rw [hb3len, hi1v]; omega), hb3v,
      getElem!_list_set (imb1 s5).val i.val DS i1.val (by rw [hlenb2, hiv]; omega),
      if_neg (by rw [hi1v, hiv]; omega), hb2,
      List.getElem!_setSlice!_suffix _ _ _ _ (by rw [hsuflen, hi1v]; omega), hb1,
      List.getElem!_setSlice!_suffix _ _ _ _ (by rw [hplen, hi1v]; omega)]
    exact hzero _ (by rw [hi1v]; omega)
  have hbnd4 : i1.val < b3.length := hbnd3
  let* ⟨ b4, hb4 ⟩ ← Array.update_spec b3 i1 (i2 ||| 128#u8) hbnd4
  rename_i j hj
  have hb4v' : b4.val = b3.val.set i1.val (i2 ||| 128#u8) := by
    rw [hb4]; simp only [Std.Array.set_val_eq]
  rw [hb4v', getElem!_list_set b3.val i1.val (i2 ||| 128#u8) j (by rw [hb3len, hi1v]; omega)]
  by_cases hlast : j = i1.val
  · rw [if_pos hlast, hi2zero, hlast, hi1v, if_neg (by omega), if_neg (by omega),
      if_neg (by omega), if_pos rfl]
    decide
  · rw [if_neg hlast, hb3v,
      getElem!_list_set (imb1 s5).val i.val DS j (by rw [hlenb2, hiv]; omega)]
    by_cases hds : j = i.val
    · rw [if_pos hds, hds, hiv, if_neg (by omega), if_neg (by omega), if_pos rfl]
    · rw [if_neg hds, hb2]
      have hlen1 : (back s2).val.length = RATE.val := hb1len
      have hlenrep : (Std.Array.repeat RATE 0#u8).val.length = RATE.val := by
        rw [Std.Array.repeat_val, List.length_replicate]
      by_cases hpre : j < 32
      · rw [List.getElem!_setSlice!_prefix _ _ _ _ hpre, hb1,
          List.getElem!_setSlice!_middle _ _ _ _
            ⟨(by omega), (by rw [hplen]; omega), (by rw [hlenrep]; omega)⟩,
          if_pos hpre, Nat.sub_zero]
      · by_cases hsuf : j < 32 + S.val
        · rw [List.getElem!_setSlice!_middle _ _ _ _
            ⟨(by omega), (by rw [hsuflen]; omega), (by rw [hlen1]; omega)⟩,
            if_neg hpre, if_pos hsuf]
        · rw [List.getElem!_setSlice!_suffix _ _ _ _ (by rw [hsuflen]; omega), hb1,
            List.getElem!_setSlice!_suffix _ _ _ _ (by rw [hplen]; omega), hzero j hj,
            if_neg hpre, if_neg hsuf, if_neg (by rw [hiv] at hds; omega),
            if_neg (by rw [hi1v] at hlast; omega)]

/-! ## The assembly -/

/-- **`keccak::xof2` is two independent sponges.**  Sponge `l`'s output is the squeeze stream of
the sponge that absorbed `prefix ‖ suffix_l` padded to one block. -/
theorem xof2_spec (RATE : Std.Usize) (DS : Std.U8) {S N : Std.Usize}
    (prefix1 : Std.Array Std.U8 32#usize)
    (suffixes : Std.Array (Std.Array Std.U8 S) 2#usize)
    (out : Std.Array (Std.Array Std.U8 N) 2#usize)
    (l : ℕ) (hl : l < 2)
    (hR : RATE.val = 168 ∨ RATE.val = 136)
    (hDS1 : 1 ≤ DS.val) (hDS2 : DS.val ≤ 127)
    (hS : 32 + S.val + 1 < RATE.val)
    (hNmax : N.val + 232 ≤ Std.Usize.max) :
    backend.neon.keccak.xof2 RATE DS prefix1 suffixes out
      ⦃ (o : Std.Array (Std.Array Std.U8 N) 2#usize) => ∀ j < N.val,
          ((o.val[l]!).val[j]!).bv
            = squeezeByte (absorbed RATE.val DS prefix1.val (suffixes.val[l]!).val) RATE.val j ⦄
      := by
  unfold backend.neon.keccak.xof2
  -- the four `massert`s
  rw [show (if RATE = 168#usize then ok () else massert (RATE = 136#usize)) = ok () from by
        by_cases h : RATE = 168#usize
        · rw [if_pos h]
        · rw [if_neg h]
          simp only [massert, if_pos (show RATE = 136#usize by scalar_tac)],
      bind_tc_ok,
      show massert (DS ≥ 1#u8) = ok () from by
        simp only [massert, if_pos (show DS ≥ 1#u8 by scalar_tac)],
      bind_tc_ok,
      show massert (DS ≤ 127#u8) = ok () from by
        simp only [massert, if_pos (show DS ≤ 127#u8 by scalar_tac)],
      bind_tc_ok]
  let* ⟨ i, hi ⟩ ← Std.Usize.add_spec (x := 32#usize) (y := S) (by scalar_tac)
  rw [show massert (i < RATE) = ok () from by
        simp only [massert, if_pos (show i < RATE by scalar_tac)], bind_tc_ok]
  let* ⟨ words, hwords ⟩ ← Std.Usize.div_spec
  have hwv : words.val = RATE.val / 8 := hwords
  have h8w : 8 * words.val = RATE.val := by omega
  have hw25 : words.val ≤ 25 := by omega
  -- `RATE / 8` is odd, so the paired loop always leaves exactly one word for the tail
  rw [show core.num.Usize.is_multiple_of words 2#usize = ok false from by
        simp only [core.num.Usize.is_multiple_of, Std.UScalar.is_multiple_of]
        congr 1
        simp only [beq_eq_false_iff_ne, ne_eq]
        rcases hR with h | h <;> (rw [hwv, h]; decide),
      bind_tc_ok,
      show massert (¬ false) = ok () from by simp [massert]]
  have hsl : (suffixes.val : List (Std.Array Std.U8 S)).length = 2 := suffixes.property
  let* ⟨ s0, hs0 ⟩ ← Array.index_usize_spec suffixes 0#usize (by scalar_tac)
  let* ⟨ b0, hb0 ⟩ ← pad_block_spec RATE DS prefix1 s0 hS
  let* ⟨ s1, hs1 ⟩ ← Array.index_usize_spec suffixes 1#usize (by scalar_tac)
  let* ⟨ b1, hb1 ⟩ ← pad_block_spec RATE DS prefix1 s1 hS
  obtain ⟨z, hz, hzb⟩ := dup_n_u64_spec 0#u64
  rw [hz, bind_tc_ok]
  -- the padded block of each sponge, pointwise
  have hblk : ∀ l' < 2, ∀ j < RATE.val,
      (inBlk b0 b1 l').val[j]!
        = padByte RATE.val DS prefix1.val (suffixes.val[l']!).val j := by
    intro l' hl' j hj
    have es : ∀ (u : Std.Array Std.U8 S) (k : ℕ) (hk : k < 2),
        u = suffixes.val[k]'(by rw [hsl]; exact hk) → u = suffixes.val[k]! := by
      intro u k hk hu; rw [hu, getElem!_pos]
    rcases (show l' = 0 ∨ l' = 1 by omega) with rfl | rfl
    · rw [show inBlk b0 b1 0 = b0 from rfl, hb0 j hj,
        ← es s0 0 (by omega) hs0, padByte, s0.property]
    · rw [show inBlk b0 b1 1 = b1 from rfl, hb1 j hj,
        ← es s1 1 (by omega) hs1, padByte, s1.property]
  have hrate : 8 * words.val ≤ RATE.val := by omega
  let* ⟨ st1, word, hL1, hL2, hL3, hL4, hL5 ⟩ ← xof2_loop0_spec b0 b1
    (Std.Array.repeat 25#usize z) words 0#usize l hl hw25 hrate (by simp)
  let* ⟨ st2, hM1, hM2 ⟩ ← xof2_loop1_spec b0 b1 st1 words word l hl hw25 hrate hL2
    (fun k hk => hL4 k (by simp) hk)
  -- the capacity registers never moved off zero
  have hzero : ∀ k, words.val ≤ k → k < 25 → lane64 (st2.val[k]!) l = 0 := by
    intro k hk hk25
    rw [hM2 k hk hk25, hL5 k hk25 (Or.inr (by omega))]
    have hr : (Std.Array.repeat 25#usize z).val[k]! = z := by
      rw [Std.Array.repeat_val,
        getElem!_pos _ k (by rw [List.length_replicate]; exact hk25), List.getElem_replicate]
    rw [hr, hzb l hl]
    decide
  have habs : stateWords st2 l = absorbed RATE.val DS prefix1.val (suffixes.val[l]!).val := by
    funext x y
    rw [stateWords_apply, absorbed]
    by_cases hk : 8 * idx x y < RATE.val
    · rw [if_pos hk, hM1 (idx x y) (by omega)]
      refine leWord64_eq_leWordOf _ _ _ (fun m hm => ?_)
      rw [hblk l hl (8 * idx x y + m) (by omega)]
    · rw [if_neg hk, hzero (idx x y) (by omega) (idx_lt x y)]
  step*
  let* ⟨ o0, o1, hrA, hrB ⟩ ← xof2_loop2_spec RATE st2 out0 out1 0#usize l hl (by omega)
    (by omega) (by simp) hNmax
  intro j hj
  -- the two output buffers go back where they came from
  have hslen2 : (s.val : List (Std.Array Std.U8 N)).length = 2 := by
    rw [s_post1]; exact out.property
  have hheadlen : (head.val : List (Std.Array Std.U8 N)).length = 1 := head_post1
  have htaillen : (tail.val : List (Std.Array Std.U8 N)).length = 1 := by
    have h := head_post2
    simp only [Std.Slice.length, hslen2] at h
    exact h
  obtain ⟨ha, hheadv⟩ := List.length_eq_one_iff.mp hheadlen
  obtain ⟨hb, htailv⟩ := List.length_eq_one_iff.mp htaillen
  have hb0v : (index_mut_back o0).val = [o0] := by
    rw [out0_post2]; show (head.val).set 0 o0 = [o0]; rw [hheadv]; rfl
  have hb1v : (index_mut_back1 o1).val = [o1] := by
    rw [out1_post2]; show (tail.val).set 0 o1 = [o1]; rw [htailv]; rfl
  obtain ⟨hsplit, hsplitlen⟩ := head_post5 (index_mut_back o0) (index_mut_back1 o1)
    (by simp only [Std.Slice.length, hb0v]; rfl)
    (by simp only [Std.Slice.length, hb1v, hslen2]; rfl)
  have hfin : (to_slice_mut_back (split_at_mut_back
      (index_mut_back o0, index_mut_back1 o1))).val = [o0, o1] := by
    rw [s_post2, Std.Array.from_slice_val _ _ (by rw [hsplit, hb0v, hb1v]; rfl),
      hsplit, hb0v, hb1v]
    rfl
  rw [hfin]
  have hpick : (([o0, o1] : List (Std.Array Std.U8 N))[l]!) = outOf o0 o1 l := by
    rcases (show l = 0 ∨ l = 1 from by omega) with rfl | rfl <;> simp [outOf]
  rw [hpick, hrA j hj (by simp), habs]
  simp

/-! ## The conformance statement -/

/-- **`keccak::xof2` implements TurboSHAKE, two messages at a time.**  Sponge `l` of the output is
`turboSHAKE RATE (prefix ‖ suffix_l) DS N`, byte for byte. -/
theorem xof2_turboSHAKE (RATE : Std.Usize) (DS : Std.U8) {S N : Std.Usize}
    (prefix1 : Std.Array Std.U8 32#usize)
    (suffixes : Std.Array (Std.Array Std.U8 S) 2#usize)
    (out : Std.Array (Std.Array Std.U8 N) 2#usize)
    (l : ℕ) (hl : l < 2)
    (hR : RATE.val = 168 ∨ RATE.val = 136)
    (hDS1 : 1 ≤ DS.val) (hDS2 : DS.val ≤ 127)
    (hS : 32 + S.val + 1 < RATE.val)
    (hNmax : N.val + 232 ≤ Std.Usize.max) :
    backend.neon.keccak.xof2 RATE DS prefix1 suffixes out
      ⦃ (o : Std.Array (Std.Array Std.U8 N) 2#usize) => ∀ j < N.val,
          ((o.val[l]!).val[j]!).bv
            = (Spec.TurboSHAKE.turboSHAKE RATE.val (msgOf prefix1 (suffixes.val[l]!)) DS.bv
                N.val ⟨by omega, by omega⟩)[j]! ⦄ := by
  apply WP.spec_mono (xof2_spec RATE DS prefix1 suffixes out l hl hR hDS1 hDS2 hS hNmax)
  intro o ho j hj
  have hsuflen : ((suffixes.val[l]!).val : List Std.U8).length = S.val :=
    (suffixes.val[l]!).property
  have hpad : ∀ k < 200,
      (padState RATE.val DS prefix1.val (suffixes.val[l]!).val)[k]!
        = (padByte RATE.val DS prefix1.val (suffixes.val[l]!).val k).bv :=
    fun k hk => getElem!_padState _ _ _ _ k hk
  rw [ho j hj,
    absorbed_eq RATE.val DS prefix1.val (suffixes.val[l]!).val _ (by omega)
      (by rw [hsuflen]; omega) hpad,
    squeezeByte_eq _ RATE.val j (by omega) (by omega),
    ← Spec.TurboSHAKE.turboSHAKE_oneBlock_getElem RATE.val (msgOf prefix1 (suffixes.val[l]!))
      DS.bv N.val ⟨by omega, by omega⟩ (by omega) _ ?_ j hj]
  intro k hk
  rw [hpad k hk, padByte, hsuflen]
  by_cases h1 : k < 32
  · rw [if_pos h1, if_pos (by omega), getElem!_msgOf _ _ k (by omega), if_pos h1]
  · rw [if_neg h1]
    by_cases h2 : k < 32 + S.val
    · rw [if_pos h2, if_pos h2, getElem!_msgOf _ _ k (by omega), if_neg h1]
    · rw [if_neg h2, if_neg h2]
      by_cases h3 : k = 32 + S.val
      · rw [if_pos h3, if_pos h3]
      · rw [if_neg h3, if_neg h3]
        by_cases h4 : k = RATE.val - 1
        · rw [if_pos h4, if_pos h4]; rfl
        · rw [if_neg h4, if_neg h4]; rfl

end

end Kopis.Neon.Keccak
