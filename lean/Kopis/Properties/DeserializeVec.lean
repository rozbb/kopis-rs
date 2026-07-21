/-
  # Kopis/Properties/DeserializeVec.lean — 10-bit deserialization correspondence.

  Proves the Aeneas-extracted 10-bit branchless decoder (`ser::deserialize_10`,
  `RingElem::deserialize … 10`, `Matrix::deserialize_10`) computes the audited
  `Spec.Kopis.deserialize 10` / `PolyVector.deserialize 10`.  This is the
  ciphertext-vector deserialization used in PKE decryption.

  The 10-bit fast path unpacks each aligned 5-byte group into 4 coefficients with
  fixed shifts/masks (no sliding window), analogous to the 13-bit path in
  `Serialize.lean` (8 coefficients per 13-byte group).  The matrix-level proof
  mirrors `MatrixSerialize.lean` in reverse.
-/
import Kopis.Properties.MatrixSerialize
import Spec.Kopis.Spec

open Aeneas Aeneas.Std Result
open kopis
open Spec (𝔹 bytesToBits slice)
open scoped BigOperators

namespace Kopis.Properties

open arithmetic.ring_arith (RingElem)

set_option maxHeartbeats 4000000
set_option maxRecDepth 4000

/-! ## Local re-proofs of private bridges from `Serialize.lean` / `MatrixSerialize.lean` -/

/-- Bit index bound (same as the spec's private `serialize_idx_lt`). -/
private theorem deser_idx_lt {n i j : ℕ} (hi : i < 256) (hj : j < n) :
    n * i + j < 8 * (32 * n) := by
  calc n * i + j < n * i + n := by omega
    _ = n * (i + 1) := by ring
    _ ≤ n * 256 := Nat.mul_le_mul_left n (by omega)
    _ = 8 * (32 * n) := by ring

/-- `streamNat (n·j) n` equals the spec's per-coefficient `Fin`-sum over the bridged bits. -/
private theorem streamNat_eq_sum (bytes : Slice U8) (n j : ℕ) (h : bytes.length = 32 * n) (hj : j < 256) :
    streamNat bytes (n * j) n
      = ∑ k : Fin n, ((bytesToBits (sliceToBytes bytes (32 * n) h))[n * j + k.val]'(deser_idx_lt hj k.isLt)).toNat
          * 2 ^ k.val := by
  unfold streamNat
  rw [← Fin.sum_univ_eq_sum_range (fun b => streamBit bytes (n * j + b) * 2 ^ b) n]
  apply Finset.sum_congr rfl
  intro k _
  congr 1
  exact (streamBit_eq_bit bytes n (n * j + k.val) h (deser_idx_lt hj k.isLt)).symm

/-- The `q`-th byte of `sliceToBytes s m h` is the `bv` of the `q`-th physical byte. -/
private theorem sliceToBytes_getElem! (s : Slice U8) (m : ℕ) (h : s.length = m) (q : ℕ) (hq : q < m) :
    (sliceToBytes s m h)[q]'hq = (s.val[q]!).bv := by
  simp only [sliceToBytes, Vector.getElem_ofFn]
  rw [getElem!_pos s.val q (by have hh : s.val.length = m := h; omega)]

/-! ## Bridge: `RingElem` as a spec `10`-bit ring element -/

/-! ## Three-byte window lemma (width 10) -/

/-- A 10-bit little-endian window starting at bit `8·B + r` (with `r ≤ 6`) is
`(v₀ + 2⁸·v₁ + 2¹⁶·v₂) >> r`, masked to 10 bits, where `vᵢ = bytes[B+i]`. -/
private theorem streamNat_window10 (bytes : Slice U8) (B r : ℕ) (hr : r ≤ 6) :
    streamNat bytes (8 * B + r) 10
      = ((bytes.val[B]!).val + 2 ^ 8 * (bytes.val[B+1]!).val + 2 ^ 16 * (bytes.val[B+2]!).val)
          / 2 ^ r % 2 ^ 10 := by
  have hW : streamNat bytes (8 * B) 24
      = (bytes.val[B]!).val + 2 ^ 8 * (bytes.val[B+1]!).val + 2 ^ 16 * (bytes.val[B+2]!).val := by
    rw [show (24 : ℕ) = 8 + 16 from rfl, streamNat_split, show (16 : ℕ) = 8 + 8 from rfl,
        streamNat_split, streamNat_byte, show 8 * B + 8 = 8 * (B + 1) from by ring,
        streamNat_byte, show 8 * (B + 1) + 8 = 8 * (B + 2) from by ring, streamNat_byte]
    ring
  have hsplit1 : streamNat bytes (8 * B) 24
      = streamNat bytes (8 * B) r + 2 ^ r * streamNat bytes (8 * B + r) (24 - r) := by
    have := streamNat_split bytes (8 * B) r (24 - r)
    rwa [show r + (24 - r) = 24 from by omega] at this
  have hsplit2 : streamNat bytes (8 * B + r) (24 - r)
      = streamNat bytes (8 * B + r) 10 + 2 ^ 10 * streamNat bytes (8 * B + r + 10) (24 - r - 10) := by
    have := streamNat_split bytes (8 * B + r) 10 (24 - r - 10)
    rwa [show (10 : ℕ) + (24 - r - 10) = 24 - r from by omega] at this
  set A := streamNat bytes (8 * B) r with hA_def
  set C := streamNat bytes (8 * B + r) 10 with hC_def
  set D := streamNat bytes (8 * B + r + 10) (24 - r - 10) with hD_def
  have hAlt : A < 2 ^ r := streamNat_lt _ _ _
  have hClt : C < 2 ^ 10 := streamNat_lt _ _ _
  have hWACD : (bytes.val[B]!).val + 2 ^ 8 * (bytes.val[B+1]!).val + 2 ^ 16 * (bytes.val[B+2]!).val
      = A + 2 ^ r * (C + 2 ^ 10 * D) := by rw [← hW, hsplit1, hsplit2]
  rw [hWACD, Nat.add_mul_div_left _ _ (by positivity : 0 < 2 ^ r),
      Nat.div_eq_of_lt hAlt, Nat.zero_add, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hClt]

/-! ## Per-coefficient extraction lemmas (one per output slot in a 5-byte group). -/

private theorem coef0_10 (i2 i3 i4 i5 i6 : U16) (v0 v1 v2 : ℕ)
    (e2 : i2.val = v0) (e3 : i3.val = v1) (e4 : i4.val = (i3 &&& 3#u16).val)
    (e5 : i5.val = i4.val <<< 8 % U16.size) (e6 : i6.val = (i2 ||| i5).val)
    (_b0 : v0 < 256) (_b1 : v1 < 256) (_b2 : v2 < 256) :
    i6.val = (v0 + (2 ^ 8 * v1 + 2 ^ 16 * v2)) / 2 ^ 0 % 2 ^ 10 := by
  have hu16 : (U16.size : ℕ) = 2 ^ 16 := by simp [U16.size, Std.U16.numBits]
  have h4 : i4.val = v1 % 2 ^ 2 := by
    rw [e4, UScalar.val_and, e3, show ((3#u16).val : ℕ) = 2 ^ 2 - 1 from rfl]
    exact Nat.and_two_pow_sub_one_eq_mod _ _
  have h5 : i5.val = v1 % 2 ^ 2 * 2 ^ 8 := by
    rw [e5, h4, Nat.shiftLeft_eq, hu16]; exact Nat.mod_eq_of_lt (by omega)
  rw [e6, UScalar.val_or, e2, h5, lor_mul_of_lt (show v0 < 2 ^ 8 by omega)]; omega

private theorem coef1_10 (i3 i7 i8 i9 i10 i12 : U16) (v1 v2 v3 : ℕ)
    (e3 : i3.val = v1) (h7 : i7.val = i3.val >>> 2) (e8 : i8.val = v2)
    (h9 : i9.val = (i8 &&& 15#u16).val) (h10 : i10.val = i9.val <<< 6 % U16.size)
    (h12 : i12.val = (i7 ||| i10).val)
    (_b1 : v1 < 256) (_b2 : v2 < 256) (_b3 : v3 < 256) :
    i12.val = (v1 + (2 ^ 8 * v2 + 2 ^ 16 * v3)) / 2 ^ 2 % 2 ^ 10 := by
  have hu16 : (U16.size : ℕ) = 2 ^ 16 := by simp [U16.size, Std.U16.numBits]
  have p7 : i7.val = v1 / 2 ^ 2 := by rw [h7, e3, Nat.shiftRight_eq_div_pow]
  have p9 : i9.val = v2 % 2 ^ 4 := by
    rw [h9, UScalar.val_and, e8, show ((15#u16).val : ℕ) = 2 ^ 4 - 1 from rfl]
    exact Nat.and_two_pow_sub_one_eq_mod _ _
  have p10 : i10.val = v2 % 2 ^ 4 * 2 ^ 6 := by
    rw [h10, p9, Nat.shiftLeft_eq, hu16]; exact Nat.mod_eq_of_lt (by omega)
  rw [h12, UScalar.val_or, p7, p10, lor_mul_of_lt (show v1 / 2 ^ 2 < 2 ^ 6 by omega)]; omega

private theorem coef2_10 (i8 i13 i14 i15 i16 i18 : U16) (v2 v3 v4 : ℕ)
    (e8 : i8.val = v2) (h13 : i13.val = i8.val >>> 4) (e14 : i14.val = v3)
    (h15 : i15.val = (i14 &&& 63#u16).val) (h16 : i16.val = i15.val <<< 4 % U16.size)
    (h18 : i18.val = (i13 ||| i16).val)
    (_b2 : v2 < 256) (_b3 : v3 < 256) (_b4 : v4 < 256) :
    i18.val = (v2 + (2 ^ 8 * v3 + 2 ^ 16 * v4)) / 2 ^ 4 % 2 ^ 10 := by
  have hu16 : (U16.size : ℕ) = 2 ^ 16 := by simp [U16.size, Std.U16.numBits]
  have p13 : i13.val = v2 / 2 ^ 4 := by rw [h13, e8, Nat.shiftRight_eq_div_pow]
  have p15 : i15.val = v3 % 2 ^ 6 := by
    rw [h15, UScalar.val_and, e14, show ((63#u16).val : ℕ) = 2 ^ 6 - 1 from rfl]
    exact Nat.and_two_pow_sub_one_eq_mod _ _
  have p16 : i16.val = v3 % 2 ^ 6 * 2 ^ 4 := by
    rw [h16, p15, Nat.shiftLeft_eq, hu16]; exact Nat.mod_eq_of_lt (by omega)
  rw [h18, UScalar.val_or, p13, p16, lor_mul_of_lt (show v2 / 2 ^ 4 < 2 ^ 4 by omega)]; omega

private theorem coef3_10 (i14 i19 i20 i21 i23 : U16) (v3 v4 v5 : ℕ)
    (e14 : i14.val = v3) (h19 : i19.val = i14.val >>> 6) (e20 : i20.val = v4)
    (h21 : i21.val = i20.val <<< 2 % U16.size) (h23 : i23.val = (i19 ||| i21).val)
    (_b3 : v3 < 256) (_b4 : v4 < 256) (_b5 : v5 < 256) :
    i23.val = (v3 + (2 ^ 8 * v4 + 2 ^ 16 * v5)) / 2 ^ 6 % 2 ^ 10 := by
  have hu16 : (U16.size : ℕ) = 2 ^ 16 := by simp [U16.size, Std.U16.numBits]
  have p19 : i19.val = v3 / 2 ^ 6 := by rw [h19, e14, Nat.shiftRight_eq_div_pow]
  have p21 : i21.val = v4 * 2 ^ 2 := by
    rw [h21, e20, Nat.shiftLeft_eq, hu16]; exact Nat.mod_eq_of_lt (by omega)
  rw [h23, UScalar.val_or, p19, p21, lor_mul_of_lt (show v3 / 2 ^ 6 < 2 ^ 2 by omega)]; omega

/-! ## `deserialize_10` — the branchless fixed-shift fast path -/

/-- The closure `|k| b[k] as u16` reads byte `k` of the group and widens it to `u16`. -/
private theorem deser10_closure_spec (b : Slice U8) (k : Usize) (hk : k.val < b.length) :
    ser.deserialize_10.closure.Insts.CoreOpsFunctionFnTupleUsizeU16.call b k
      ⦃ (r : U16) => r.val = (b.val[k.val]'(by simp only [Slice.length] at hk; omega)).val ⦄ := by
  unfold ser.deserialize_10.closure.Insts.CoreOpsFunctionFnTupleUsizeU16.call
  let* ⟨ i, hi ⟩ ← Slice.index_usize_spec
  rw [U8.cast_U16_val_eq, hi]

set_option maxHeartbeats 10000000 in
/-- Loop-invariant version of `deserialize_10_spec`: after processing groups
`[iter.start, 64)`, coefficient `j` in a processed group holds its 10-bit window;
untouched output slots keep their old value. -/
private theorem deserialize_10_loop_spec (bytes : Slice U8) (arr : Array U8 320#usize)
    (harr : arr.val = bytes.val) (hlen : bytes.length = 320)
    (iter : core.ops.range.Range Usize) (out : Array U16 256#usize)
    (hstart : iter.start.val ≤ 64) (hend : iter.«end».val = 64) :
    ser.deserialize_10_loop iter arr out
      ⦃ (r : Array U16 256#usize) =>
          ∀ j (hj : j < 256),
            (r.val[j]'(by have := r.property; grind)).val
              = if j < 4 * iter.start.val then (out.val[j]'(by have := out.property; grind)).val
                else streamNat bytes (10 * j) 10 ⦄ := by
  unfold ser.deserialize_10_loop
  by_cases hlt : iter.start.val < iter.«end».val
  · let* ⟨ g, iter1, ho, hstart', hend' ⟩ ← core.iter.range.IteratorRange.next_Usize_some_spec
    rw [ho]; simp only
    have hg64 : iter.start.val < 64 := by scalar_tac
    let* ⟨ i, hi ⟩ ← Std.Usize.mul_spec
    let* ⟨ i1, hi1 ⟩ ← Std.Usize.add_spec
    have hb_spec : core.slice.index.SliceIndexRangeUsizeSlice.index
          ({ start := i, «end» := i1 } : core.ops.range.Range Usize) arr.to_slice
        ⦃ (s : Slice U8) => s.val = arr.val.slice i.val i1.val ∧ s.length = i1.val - i.val ⦄ := by
      have hts : arr.to_slice.length = 320 := by simp [Array.to_slice, Slice.length]
      simp only [core.slice.index.SliceIndexRangeUsizeSlice.index, UScalar.le_equiv, Slice.length]
      split
      · simp only [WP.spec_ok, Array.to_slice]; scalar_tac
      · scalar_tac
    let* ⟨ b, hb_val, hb_len ⟩ ← hb_spec
    let* ⟨ o1, ho1 ⟩ ← Std.Usize.mul_spec
    have ho1m : o1.val + 3 ≤ Usize.max := by scalar_tac
    have harrlen : arr.val.length = 320 := by have := arr.property; scalar_tac
    have hclos : ∀ (k : Usize), k.val < 5 →
        ser.deserialize_10.closure.Insts.CoreOpsFunctionFnTupleUsizeU16.call b k
          ⦃ (r : U16) => r.val = (bytes.val[5 * iter.start.val + k.val]!).val ⦄ := by
      intro k hk
      have hkb : k.val < b.length := by rw [hb_len]; scalar_tac
      apply WP.spec_mono (deser10_closure_spec b k hkb)
      intro r hr
      rw [hr]
      have hkbl : k.val < b.val.length := by simp only [Slice.length] at hkb; omega
      rw [(getElem!_pos b.val k.val hkbl).symm, hb_val,
          List.getElem!_slice i.val i1.val k.val arr.val (by rw [harrlen]; omega), harr, hi]
    let* ⟨ i2, hi2 ⟩ ← hclos 0#usize (by scalar_tac)
    let* ⟨ i3, hi3 ⟩ ← hclos 1#usize (by scalar_tac)
    let* ⟨ i4, hi4, hi4bv ⟩ ← UScalar.and_spec
    let* ⟨ i5, hi5, hi5bv ⟩ ← Std.U16.ShiftLeft_IScalar_spec
    let* ⟨ i6, hi6, hi6bv ⟩ ← UScalar.or_spec
    let* ⟨ out1, hout1 ⟩ ← Array.update_spec
    let* ⟨ i7, hi7, hi7bv ⟩ ← Std.U16.ShiftRight_IScalar_spec
    let* ⟨ i8, hi8 ⟩ ← hclos 2#usize (by scalar_tac)
    let* ⟨ i9, hi9, hi9bv ⟩ ← UScalar.and_spec
    let* ⟨ i10, hi10, hi10bv ⟩ ← Std.U16.ShiftLeft_IScalar_spec
    let* ⟨ i11, hi11 ⟩ ← Std.Usize.add_spec
    let* ⟨ i12, hi12, hi12bv ⟩ ← UScalar.or_spec
    let* ⟨ out2, hout2 ⟩ ← Array.update_spec
    let* ⟨ i13, hi13, hi13bv ⟩ ← Std.U16.ShiftRight_IScalar_spec
    let* ⟨ i14, hi14 ⟩ ← hclos 3#usize (by scalar_tac)
    let* ⟨ i15, hi15, hi15bv ⟩ ← UScalar.and_spec
    let* ⟨ i16, hi16, hi16bv ⟩ ← Std.U16.ShiftLeft_IScalar_spec
    let* ⟨ i17, hi17 ⟩ ← Std.Usize.add_spec
    let* ⟨ i18, hi18, hi18bv ⟩ ← UScalar.or_spec
    let* ⟨ out3, hout3 ⟩ ← Array.update_spec
    let* ⟨ i19, hi19, hi19bv ⟩ ← Std.U16.ShiftRight_IScalar_spec
    let* ⟨ i20, hi20 ⟩ ← hclos 4#usize (by scalar_tac)
    let* ⟨ i21, hi21, hi21bv ⟩ ← Std.U16.ShiftLeft_IScalar_spec
    let* ⟨ i22, hi22 ⟩ ← Std.Usize.add_spec
    let* ⟨ i23, hi23, hi23bv ⟩ ← UScalar.or_spec
    let* ⟨ a, ha ⟩ ← Array.update_spec
    have hc0 : i6.val = streamNat bytes (10 * (4 * iter.start.val + 0)) 10 := by
      rw [show 10 * (4 * iter.start.val + 0) = 8 * (5 * iter.start.val + 0) + 0 from by ring,
          streamNat_window10 bytes (5 * iter.start.val + 0) 0 (by norm_num)]
      simp only [Nat.add_assoc, Nat.reduceAdd]
      exact coef0_10 i2 i3 i4 i5 i6 _ _ _ hi2 hi3 hi4 hi5 hi6
        (U8.lt_succ_max _) (U8.lt_succ_max _) (U8.lt_succ_max _)
    have hc1 : i12.val = streamNat bytes (10 * (4 * iter.start.val + 1)) 10 := by
      rw [show 10 * (4 * iter.start.val + 1) = 8 * (5 * iter.start.val + 1) + 2 from by ring,
          streamNat_window10 bytes (5 * iter.start.val + 1) 2 (by norm_num)]
      simp only [Nat.add_assoc, Nat.reduceAdd]
      exact coef1_10 i3 i7 i8 i9 i10 i12 _ _ _ hi3 hi7 hi8 hi9 hi10 hi12
        (U8.lt_succ_max _) (U8.lt_succ_max _) (U8.lt_succ_max _)
    have hc2 : i18.val = streamNat bytes (10 * (4 * iter.start.val + 2)) 10 := by
      rw [show 10 * (4 * iter.start.val + 2) = 8 * (5 * iter.start.val + 2) + 4 from by ring,
          streamNat_window10 bytes (5 * iter.start.val + 2) 4 (by norm_num)]
      simp only [Nat.add_assoc, Nat.reduceAdd]
      exact coef2_10 i8 i13 i14 i15 i16 i18 _ _ _ hi8 hi13 hi14 hi15 hi16 hi18
        (U8.lt_succ_max _) (U8.lt_succ_max _) (U8.lt_succ_max _)
    have hc3 : i23.val = streamNat bytes (10 * (4 * iter.start.val + 3)) 10 := by
      rw [show 10 * (4 * iter.start.val + 3) = 8 * (5 * iter.start.val + 3) + 6 from by ring,
          streamNat_window10 bytes (5 * iter.start.val + 3) 6 (by norm_num)]
      simp only [Nat.add_assoc, Nat.reduceAdd]
      exact coef3_10 i14 i19 i20 i21 i23 _ _ _ hi14 hi19 hi20 hi21 hi23
        (U8.lt_succ_max _) (U8.lt_succ_max _) (U8.lt_succ_max _)
    have hstartnew : iter1.start.val ≤ 64 := by rw [hstart']; omega
    have hendnew : iter1.«end».val = 64 := by rw [hend']; exact hend
    apply WP.spec_mono (deserialize_10_loop_spec bytes arr harr hlen iter1 a hstartnew hendnew)
    intro r hr j hj
    have ihj := hr j hj
    rw [hstart'] at ihj
    by_cases hjA : j < 4 * iter.start.val
    · rw [if_pos hjA, ihj, if_pos (by omega : j < 4 * (iter.start.val + 1))]
      simp only [ha, hout3, hout2, hout1, Array.set_val_eq, ho1, hi11, hi17, hi22]
      simp_lists
    · by_cases hjC : j < 4 * (iter.start.val + 1)
      · rw [if_neg hjA, ihj, if_pos hjC]
        obtain ⟨t, htlt, rfl⟩ : ∃ t, t < 4 ∧ j = 4 * iter.start.val + t :=
          ⟨j - 4 * iter.start.val, by omega, by omega⟩
        rcases (show t = 0 ∨ t = 1 ∨ t = 2 ∨ t = 3 by omega) with rfl | rfl | rfl | rfl
        all_goals
          (simp only [ha, hout3, hout2, hout1, Array.set_val_eq, ho1, hi11, hi17, hi22]
           simp_lists
           first | exact hc0 | exact hc1 | exact hc2 | exact hc3)
      · rw [if_neg hjA, ihj, if_neg hjC]
  · let* ⟨ o, iter1, hnone, _ ⟩ ← core.iter.range.IteratorRange.next_Usize_none_spec
    rw [hnone]; simp only [WP.spec_ok]
    intro j hj
    rw [if_pos (by scalar_tac)]

/-- Decoding-correctness of `deserialize_10`: every coefficient equals the 10-bit
little-endian stream window. -/
theorem deserialize_10_spec (bytes : Slice U8) (arr : Array U8 320#usize)
    (harr : arr.val = bytes.val) (hlen : bytes.length = 320) :
    ser.deserialize_10 arr
      ⦃ (r : Array U16 256#usize) =>
          ∀ j (hj : j < 256),
            (r.val[j]'(by have := r.property; grind)).val = streamNat bytes (10 * j) 10 ⦄ := by
  unfold ser.deserialize_10
  apply WP.spec_mono (deserialize_10_loop_spec bytes arr harr hlen
    { start := 0#usize, «end» := 64#usize } (Array.repeat 256#usize 0#u16) (by simp) (by simp))
  intro r hr j hj
  have h := hr j hj
  rwa [if_neg (by simp)] at h

/-- **Correctness of `RingElem::deserialize` at 10 bits.**  Decoding a 320-byte
buffer yields the spec ring element `deserialize 10`. -/
theorem ringElem_deserialize_10_spec (bytes : Slice U8) (hlen : bytes.length = 32 * 10) :
    arithmetic.ring_arith.RingElem.deserialize bytes 10#usize
      ⦃ (r : RingElem) => toPolyN 10 r = Spec.Kopis.deserialize 10 (sliceToBytes bytes (32 * 10) hlen) ⦄ := by
  unfold arithmetic.ring_arith.RingElem.deserialize
  simp only [consts.RING_DEG, consts.MODULUS_Q_BITS, consts.MODULUS_P_BITS]
  have hlen320 : bytes.length = 320 := by omega
  step*
  have hb : bytes.len = 320#usize := by scalar_tac
  simp only [core.array.TryFromSharedArraySlice.try_from, dif_pos hb, bind_tc_ok,
    core.result.Result.unwrap]
  apply WP.spec_bind (deserialize_10_spec bytes ⟨bytes.val, by scalar_tac⟩ rfl hlen320)
  intro r hr
  simp only [WP.spec_ok]
  apply Vector.ext
  intro jj hjj
  simp only [toPolyN, Vector.getElem_ofFn]
  rw [deserialize_get 10 (sliceToBytes bytes (32 * 10) hlen) jj hjj]
  have hval := hr jj hjj
  rw [hval, streamNat_eq_sum bytes 10 jj hlen hjj]

/-! ## Matrix (vector) level: `Matrix.deserialize_10` for `Y = 1` -/

/-- The `32·10`-byte block of `bytes` for output row `a`, as a spec `𝔹 (32·10)`. -/
private def chunkBytes (bytes : Slice U8) (a : ℕ) : 𝔹 (32 * 10) :=
  Vector.ofFn fun (q : Fin (32 * 10)) => (bytes.val[32 * 10 * a + q.val]!).bv

/-- `getElem!` after a `List.set` at an in-bounds index. -/
private theorem getElem!_list_set {α : Type _} [Inhabited α] (l : List α) (j : ℕ)
    (v : α) (k : ℕ) (hj : j < l.length) :
    (l.set j v)[k]! = if k = j then v else l[k]! := by
  by_cases h : k = j
  · subst h
    rw [getElem!_pos _ k (by rw [List.length_set]; exact hj), List.getElem_set_self, if_pos rfl]
  · by_cases hk : k < l.length
    · rw [getElem!_pos _ k (by rw [List.length_set]; exact hk),
        List.getElem_set_of_ne (Ne.symm h), ← getElem!_pos _ k hk, if_neg h]
    · rw [getElem!_neg _ k (by rw [List.length_set]; exact hk), getElem!_neg _ k hk, if_neg h]

set_option maxHeartbeats 8000000
set_option maxRecDepth 20000

/-- Inner loop of `Matrix.deserialize_10` for `Y = 1`: fixed row `i`, iterating over
the single column `j ∈ [start, 1)`.  On `start = 0` it deserializes the `i`-th
`320`-byte block into `result[i][0]`; otherwise it leaves the matrix untouched. -/
theorem matrix_deserialize_10_inner_spec {L : Usize}
    (iter : core.ops.range.Range Usize)
    (bytes : Slice U8) (result : arithmetic.matrix_arith.Matrix L 1#usize)
    (chunk_len : Usize) (i : Usize)
    (hchunk : chunk_len.val = 32 * 10)
    (hi : i.val < L.val) (hlen : bytes.length = L.val * (32 * 10))
    (hs0 : iter.start.val = 0) (hend : iter.«end».val = 1) :
    arithmetic.matrix_arith.Matrix.deserialize_10_loop0_loop0 (X := L) (Y := 1#usize)
        iter bytes result chunk_len i
      ⦃ (r : arithmetic.matrix_arith.Matrix L 1#usize) =>
          ∀ a (_ha : a < L.val),
            toPolyN 10 ((r.val[a]!).val[0]!)
              = if a = i.val then Spec.Kopis.deserialize 10 (chunkBytes bytes i.val)
                else toPolyN 10 ((result.val[a]!).val[0]!) ⦄ := by
  unfold arithmetic.matrix_arith.Matrix.deserialize_10_loop0_loop0
  have hm : 0 < 32 * 10 := by norm_num
  have hbufmax : L.val * (32 * 10) ≤ Usize.max := hlen ▸ bytes.property
  have hlt : iter.start.val < iter.«end».val := by omega
  let* ⟨ o, iter1, ho, hstart', hend' ⟩ ← core.iter.range.IteratorRange.next_Usize_some_spec
  rw [ho]; simp only
  let* ⟨ i1, hi1 ⟩ ← Std.Usize.mul_spec (show i.val * (1#usize).val ≤ Usize.max from by
    simpa using le_trans (le_of_lt hi) (le_trans (Nat.le_mul_of_pos_right _ hm) hbufmax))
  have hi1v : i1.val = i.val := by rw [hi1]; simp
  let* ⟨ idx, hidx ⟩ ← Std.Usize.add_spec (show i1.val + iter.start.val ≤ Usize.max from by
    rw [hi1v, hs0]
    simpa using le_trans (le_of_lt hi) (le_trans (Nat.le_mul_of_pos_right _ hm) hbufmax))
  have hidxv : idx.val = i.val := by rw [hidx, hi1v, hs0]; omega
  let* ⟨ i2, hi2 ⟩ ← Std.Usize.mul_spec (show idx.val * chunk_len.val ≤ Usize.max from by
    rw [hidxv, hchunk]; exact le_trans (Nat.mul_le_mul_right (32 * 10) (le_of_lt hi)) hbufmax)
  have hi2v : i2.val = i.val * (32 * 10) := by rw [hi2, hidxv, hchunk]
  let* ⟨ i3, hi3 ⟩ ← Std.Usize.add_spec (show idx.val + (1#usize).val ≤ Usize.max from by
    rw [hidxv]
    simpa using le_trans (le_trans (show i.val + 1 ≤ L.val by omega) (Nat.le_mul_of_pos_right _ hm)) hbufmax)
  have hi3v : i3.val = i.val + 1 := by rw [hi3, hidxv]
  let* ⟨ i4, hi4 ⟩ ← Std.Usize.mul_spec (show i3.val * chunk_len.val ≤ Usize.max from by
    rw [hi3v, hchunk]; exact le_trans (Nat.mul_le_mul_right (32 * 10) (by omega)) hbufmax)
  have hi4v : i4.val = (i.val + 1) * (32 * 10) := by rw [hi4, hi3v, hchunk]
  have hle : i2.val ≤ i4.val := by rw [hi2v, hi4v]; exact Nat.mul_le_mul_right _ (by omega)
  have hbnd : i4.val ≤ bytes.length := by rw [hi4v, hlen]; exact Nat.mul_le_mul_right _ (by omega)
  have hbndl : i4.val ≤ bytes.val.length := by have := hbnd; simp only [Slice.length] at this; exact this
  have hchunk_spec : core.slice.index.SliceIndexRangeUsizeSlice.index
        ({ start := i2, «end» := i4 } : core.ops.range.Range Usize) bytes
      ⦃ (s : Slice U8) => s.val = bytes.val.slice i2.val i4.val ∧ s.length = 32 * 10 ⦄ := by
    simp only [core.slice.index.SliceIndexRangeUsizeSlice.index, UScalar.le_equiv]
    rw [if_pos ⟨hle, hbnd⟩]
    simp only [WP.spec_ok]
    refine ⟨trivial, ?_⟩
    show (bytes.val.slice i2.val i4.val).length = 32 * 10
    rw [List.slice_length, hi2v, hi4v]
    have h1 : (i.val + 1) * (32 * 10) ≤ bytes.val.length := hi4v ▸ hbndl
    omega
  let* ⟨ chunk, hchunk_val, hchunk_len ⟩ ← hchunk_spec
  let* ⟨ re, hre ⟩ ← ringElem_deserialize_10_spec chunk hchunk_len
  have hXY : sliceToBytes chunk (32 * 10) hchunk_len = chunkBytes bytes i.val := by
    apply Vector.ext
    intro q hq
    rw [sliceToBytes_getElem! chunk (32 * 10) hchunk_len q hq]
    simp only [chunkBytes, Vector.getElem_ofFn]
    rw [hchunk_val,
        List.getElem!_slice i2.val i4.val q bytes.val ⟨hbndl, by omega⟩, hi2v,
        Nat.mul_comm i.val (32 * 10)]
  have hib : i.val < result.val.length := by have := result.property; omega
  let* ⟨ row, index_mut_back, hrow, hback ⟩ ← Array.index_mut_usize_spec result i hib
  have hrowlen : row.val.length = 1 := by have := row.property; scalar_tac
  let* ⟨ a1, ha1 ⟩ ← Array.update_spec
  unfold arithmetic.matrix_arith.Matrix.deserialize_10_loop0_loop0
  let* ⟨ o2, iter2, hnone2, _ ⟩ ← core.iter.range.IteratorRange.next_Usize_none_spec iter1
    (show iter1.start.val ≥ iter1.«end».val by rw [hstart', hend']; omega)
  rw [hnone2]; simp only [WP.spec_ok]
  intro a _ha
  rw [hback]
  simp only [Array.set_val_eq]
  by_cases hai : a = i.val
  · subst hai
    rw [getElem!_list_set result.val i.val a1 i.val hib, if_pos rfl, if_pos rfl, ha1]
    simp only [Array.set_val_eq]
    rw [hs0, getElem!_list_set row.val 0 re 0 (by rw [hrowlen]; omega), if_pos rfl, hre, hXY]
  · rw [getElem!_list_set result.val i.val a1 a hib, if_neg hai, if_neg hai]

/-- Outer loop of `Matrix.deserialize_10` for `Y = 1`: iterating over rows `i ∈ [start, L)`. -/
theorem matrix_deserialize_10_outer_spec {L : Usize}
    (iter : core.ops.range.Range Usize)
    (bytes : Slice U8) (result : arithmetic.matrix_arith.Matrix L 1#usize)
    (chunk_len : Usize)
    (hchunk : chunk_len.val = 32 * 10)
    (hlen : bytes.length = L.val * (32 * 10))
    (hstart : iter.start.val ≤ L.val) (hend : iter.«end».val = L.val) :
    arithmetic.matrix_arith.Matrix.deserialize_10_loop0 (X := L) (Y := 1#usize)
        iter bytes result chunk_len
      ⦃ (r : arithmetic.matrix_arith.Matrix L 1#usize) =>
          ∀ a (_ha : a < L.val),
            toPolyN 10 ((r.val[a]!).val[0]!)
              = if iter.start.val ≤ a
                then Spec.Kopis.deserialize 10 (chunkBytes bytes a)
                else toPolyN 10 ((result.val[a]!).val[0]!) ⦄ := by
  unfold arithmetic.matrix_arith.Matrix.deserialize_10_loop0
  by_cases hlt : iter.start.val < iter.«end».val
  · let* ⟨ o, iter1, ho, hstart', hend' ⟩ ← core.iter.range.IteratorRange.next_Usize_some_spec
    rw [ho]; simp only
    have hi_lt : iter.start.val < L.val := by scalar_tac
    let* ⟨ result1, hres1 ⟩ ←
      matrix_deserialize_10_inner_spec { start := 0#usize, «end» := 1#usize } bytes result
        chunk_len iter.start hchunk hi_lt hlen (by simp) (by simp)
    apply WP.spec_mono
      (matrix_deserialize_10_outer_spec iter1 bytes result1 chunk_len hchunk hlen
        (by rw [hstart']; scalar_tac) (by rw [hend']; exact hend))
    intro r hr a ha
    rw [hr a ha, hstart']
    by_cases hlt2 : iter.start.val + 1 ≤ a
    · rw [if_pos hlt2, if_pos (by omega : iter.start.val ≤ a)]
    · rw [if_neg hlt2, hres1 a ha]
      by_cases hle : iter.start.val ≤ a
      · have haeq : a = iter.start.val := by omega
        subst haeq
        rw [if_pos (le_refl _), if_pos rfl]
      · rw [if_neg hle, if_neg (by omega : ¬ a = iter.start.val)]
  · let* ⟨ o, iter1, hnone, _ ⟩ ← core.iter.range.IteratorRange.next_Usize_none_spec
    rw [hnone]; simp only [WP.spec_ok]
    have hge : iter.start.val = L.val := by scalar_tac
    intro a ha
    rw [if_neg (by omega : ¬ iter.start.val ≤ a)]
  termination_by iter.«end».val - iter.start.val
  decreasing_by scalar_decr_tac

/-- Spec-side: the `a`-th block of `PolyVector.deserialize 10` equals the physical
`chunkBytes` deserialization. -/
private theorem polyDeser_getElem {L : Usize} (bytes : Slice U8)
    (hlen : bytes.length = L.val * (32 * 10)) (a : ℕ) (ha : a < L.val) :
    (Spec.Kopis.PolyVector.deserialize (ℓ := L.val) 10
        ((sliceToBytes bytes (L.val * (32 * 10)) hlen).cast (by ring)))[a]'ha
      = Spec.Kopis.deserialize 10 (chunkBytes bytes a) := by
  have hXY : ∀ (h : 32 * 10 * a + 32 * 10 ≤ 32 * 10 * L.val),
      slice ((sliceToBytes bytes (L.val * (32 * 10)) hlen).cast (by ring)) (32 * 10 * a) (32 * 10) h
        = chunkBytes bytes a := by
    intro h
    apply Vector.ext
    intro q hq
    simp only [slice, Vector.getElem_ofFn, Vector.getElem_cast, chunkBytes]
    rw [sliceToBytes_getElem! bytes (L.val * (32 * 10)) hlen (32 * 10 * a + q) (by
      have hb : 32 * 10 * a + 32 * 10 ≤ 32 * 10 * L.val := by
        calc 32 * 10 * a + 32 * 10 = 32 * 10 * (a + 1) := by ring
          _ ≤ 32 * 10 * L.val := Nat.mul_le_mul_left _ (by omega)
      omega)]
  simp only [Spec.Kopis.PolyVector.deserialize, Vector.getElem_ofFn, hXY]

/-- **Correctness of `Matrix::deserialize_10` for `Y = 1` (ciphertext-vector case).**
Deserializing an `L × 1` matrix of `10`-bit coefficients from a
`L·(32·10)`-byte buffer yields `PolyVector.deserialize 10`. -/
theorem matrix_deserialize_10_spec {L : Usize} (bytes : Slice U8)
    (hlen : bytes.length = L.val * (32 * 10)) (hfit : L.val * 10 * 256 ≤ Usize.max) :
    arithmetic.matrix_arith.Matrix.deserialize_10 L 1#usize bytes
      ⦃ (r : arithmetic.matrix_arith.Matrix L 1#usize) =>
          toVecN 10 r = Spec.Kopis.PolyVector.deserialize (ℓ := L.val) 10
            ((sliceToBytes bytes (L.val * (32 * 10)) hlen).cast (by ring)) ⦄ := by
  unfold arithmetic.matrix_arith.Matrix.deserialize_10
  simp only [consts.RING_DEG]
  have hm : 0 < 32 * 10 := by norm_num
  have hbufmax : L.val * (32 * 10) ≤ Usize.max := hlen ▸ bytes.property
  have hLmax : L.val ≤ Usize.max := le_trans (Nat.le_mul_of_pos_right _ hm) hbufmax
  have hb1 : L.val * 10 ≤ Usize.max := by
    have := hfit; omega
  have hsz : ∀ x : ℕ, x ≤ Usize.max → x < UScalar.size .Usize := by
    intro x hx
    have h1 : UScalar.size .Usize = 2 ^ System.Platform.numBits := by
      simp only [UScalar.size, UScalarTy.Usize_numBits_eq]
    have h2 : (Usize.max : ℕ) = 2 ^ System.Platform.numBits - 1 := by
      simp only [Usize.max, Usize.numBits, UScalarTy.Usize_numBits_eq]
    have h3 : 0 < 2 ^ System.Platform.numBits := by positivity
    omega
  -- i = X * Y = L * 1
  let* ⟨ i, hi ⟩ ← Std.Usize.mul_spec (show L.val * (1#usize).val ≤ Usize.max from by
    simp only [show (1#usize).val = 1 from rfl, Nat.mul_one]; exact hLmax)
  have hiv : i.val = L.val := by rw [hi]; simp
  -- i1 = i * 10
  let* ⟨ i1, hi1 ⟩ ← Std.Usize.mul_spec (show i.val * (10#usize).val ≤ Usize.max from by
    rw [hiv]; simp only [show (10#usize).val = 10 from rfl]; omega)
  have hi1v : i1.val = L.val * 10 := by rw [hi1, hiv]
  -- unused checked mul i1 * 256 (needs hfit)
  let* ⟨ iu, hiu ⟩ ← Std.Usize.mul_spec (show i1.val * (256#usize).val ≤ Usize.max from by
    rw [hi1v]; simp only [show (256#usize).val = 256 from rfl]; omega)
  -- reduce the `lift (wrapping_mul …)` binds
  simp only [lift, bind_tc_ok]
  -- right_val = i4 / 8 ;  massert left = right
  let* ⟨ right_val, hrv ⟩ ← Std.Usize.div_spec
  have hrvv : right_val.val = L.val * (32 * 10) := by
    rw [hrv]
    simp only [Std.Usize.wrapping_mul_val_eq, show (1#usize).val = 1 from rfl,
      show (10#usize).val = 10 from rfl, show (256#usize).val = 256 from rfl, Nat.mul_one]
    rw [Nat.mod_eq_of_lt (hsz _ hLmax), Nat.mod_eq_of_lt (hsz _ hb1),
      Nat.mod_eq_of_lt (hsz _ hfit),
      show L.val * 10 * 256 = L.val * (32 * 10) * 8 from by ring,
      Nat.mul_div_cancel _ (by norm_num)]
  have hmeq : Slice.len bytes = right_val :=
    UScalar.eq_of_val_eq (by rw [Slice.len_val, hrvv]; exact hlen)
  rw [show massert (Slice.len bytes = right_val) = ok () from by
    simp only [massert, if_pos hmeq], bind_tc_ok]
  -- default matrix (value irrelevant: the loop overwrites every row)
  have hdef : arithmetic.matrix_arith.Matrix.Insts.CoreDefaultDefault.default L 1#usize
      = ok (Array.repeat L (Array.repeat 1#usize (Array.repeat 256#usize 0#u16))) := by
    simp only [arithmetic.matrix_arith.Matrix.Insts.CoreDefaultDefault.default,
      arithmetic.ring_arith.RingElem.Insts.CoreDefaultDefault.default, bind_tc_ok]
  rw [hdef, bind_tc_ok]
  -- chunk_len = 10 * 256 / 8 = 320
  let* ⟨ i5, hi5 ⟩ ← Std.Usize.mul_spec (show (10#usize).val * (256#usize).val ≤ Usize.max from by
    have h2560 : (10#usize).val * (256#usize).val = 2560 := rfl
    rw [h2560]
    rcases Usize.bounds_eq with h | h <;> rw [h] <;> simp only [U32.max_eq, U64.max_eq] <;> omega)
  let* ⟨ chunk_len, hcl ⟩ ← Std.Usize.div_spec
  have hcv : chunk_len.val = 32 * 10 := by rw [hcl, hi5]
  apply WP.spec_mono
    (matrix_deserialize_10_outer_spec { start := 0#usize, «end» := L } bytes _ chunk_len
      hcv hlen (by simp) rfl)
  intro r hr
  apply Vector.ext
  intro a ha
  simp only [toVecN, Vector.getElem_ofFn]
  have h0 : ({ start := 0#usize, «end» := L } : core.ops.range.Range Usize).start.val = 0 := rfl
  rw [hr a ha, h0, if_pos (Nat.zero_le a), polyDeser_getElem bytes hlen a ha]

end Kopis.Properties
