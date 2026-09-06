import Kopis.Properties.MatrixSerialize
import Kopis.Properties.GenMatrix
open Aeneas Aeneas.Std Result RustKopisSerial
open Spec (𝔹)
namespace Kopis.Properties
set_option maxHeartbeats 2000000
set_option maxRecDepth 4000

/-- The public key's already-serialized vector bytes (`vec_bytes`), flattened to a single
byte-vector.  With the pubkey refactor the struct stores these bytes verbatim rather than the
structured vector, so `serialize` merely concatenates them (followed by the matrix seed). -/
def vecBytesFlat {L : Usize} (self : pke.PkePublicKey L) : 𝔹 (L.val * 320) :=
  Vector.ofFn (fun (idx : Fin (L.val * 320)) =>
    ((self.vec_bytes.val[idx.val / 320]!).val[idx.val % 320]!).bv)

theorem vecBytesFlat_getElem! {L : Usize} (self : pke.PkePublicKey L) (pos : ℕ)
    (hpos : pos < L.val * 320) :
    (vecBytesFlat self).toList[pos]! = ((self.vec_bytes.val[pos / 320]!).val[pos % 320]!).bv := by
  rw [getElem!_pos _ pos (by simp only [Vector.toList_length]; exact hpos)]
  simp only [vecBytesFlat, Vector.getElem_toList, Vector.getElem_ofFn]

/-- `PK_VEC_ELEM_BYTES` evaluates to `320` (`= 10·256/8`). -/
theorem pk_vec_elem_bytes_spec : pke.PK_VEC_ELEM_BYTES ⦃ (r : Usize) => r.val = 320 ⦄ := by
  simp only [pke.PK_VEC_ELEM_BYTES, consts.RING_DEG]
  let* ⟨ a, ha ⟩ ← Std.Usize.mul_spec (x := 10#usize) (y := 256#usize) (by scalar_tac)
  let* ⟨ b, hb ⟩ ← Std.Usize.div_spec
  rw [hb, ha]

/-- Loop invariant of `serialize_loop`: iterating `i ∈ [start, L)` copies `vec_bytes[i]` into
`out_buf[i·320 .. i·320+320)`, leaving everything before `start·320` and the seed region
untouched.  `self` is threaded unchanged. -/
theorem serialize_loop_val_spec {L : Usize} (self : pke.PkePublicKey L)
    (iter : core.ops.range.Range Usize) (out_buf : Slice U8)
    (hlen : out_buf.val.length = L.val * 320 + 32)
    (hstart : iter.start.val ≤ L.val) (hend : iter.«end».val = L.val) :
    pke.PkePublicKey.serialize_loop iter self out_buf
      ⦃ ((self1 : pke.PkePublicKey L), (ob : Slice U8)) =>
          self1 = self ∧ ob.val.length = L.val * 320 + 32 ∧
          ∀ pos, pos < L.val * 320 + 32 →
            ob.val[pos]! =
              if iter.start.val * 320 ≤ pos ∧ pos < L.val * 320
              then ((self.vec_bytes.val[pos / 320]!).val[pos % 320]!)
              else out_buf.val[pos]! ⦄ := by
  unfold pke.PkePublicKey.serialize_loop
  have hVBmax : L.val * 320 ≤ Usize.max := by
    have : L.val * 320 ≤ L.val * 320 + 32 := by omega
    exact le_trans this (hlen ▸ out_buf.property)
  by_cases hlt : iter.start.val < iter.«end».val
  · let* ⟨ o, iter1, ho, hstart', hend' ⟩ ← core.iter.range.IteratorRange.next_Usize_some_spec
    rw [ho]; simp only
    have hi_lt : iter.start.val < L.val := by scalar_tac
    let* ⟨ eb, hebv ⟩ ← pk_vec_elem_bytes_spec
    -- start = i * 320
    let* ⟨ st, hst ⟩ ← Std.Usize.mul_spec (x := iter.start) (y := eb)
      (by rw [hebv]; exact le_trans (Nat.mul_le_mul_right 320 (le_of_lt hi_lt)) hVBmax)
    have hstv : st.val = iter.start.val * 320 := by rw [hst, hebv]
    -- i2 = start + 320
    let* ⟨ i2, hi2 ⟩ ← Std.Usize.add_spec (x := st) (y := eb)
      (by rw [hstv, hebv]
          calc iter.start.val * 320 + 320 = (iter.start.val + 1) * 320 := by ring
            _ ≤ L.val * 320 := Nat.mul_le_mul_right 320 (by omega)
            _ ≤ Usize.max := hVBmax)
    have hi2v : i2.val = iter.start.val * 320 + 320 := by rw [hi2, hstv, hebv]
    -- index_mut window [start, start+320)
    have hb0 : st ≤ i2 := by rw [UScalar.le_equiv, hstv, hi2v]; omega
    have hb1 : i2 ≤ out_buf.length := by
      have hle : (iter.start.val + 1) * 320 ≤ L.val * 320 := Nat.mul_le_mul_right 320 (by omega)
      have he : (iter.start.val + 1) * 320 = iter.start.val * 320 + 320 := by ring
      show i2.val ≤ out_buf.length
      simp only [Slice.length]; rw [hi2v, hlen]; omega
    step with core.slice.index.SliceIndexRangeUsizeSlice.index_mut.step_spec as
      ⟨ s, index_mut_back, hs_val, hs_len, hs_back ⟩
    -- vec_bytes[i]
    have hib : iter.start.val < self.vec_bytes.length := by
      have := self.vec_bytes.property; scalar_tac
    let* ⟨ vb, hvb ⟩ ← Array.index_usize_spec self.vec_bytes iter.start hib
    rw [show (lift (Array.to_slice vb) : Result (Slice U8)) = ok (Array.to_slice vb) from rfl,
      bind_tc_ok]
    set s1 := Array.to_slice vb with hs1def
    have hs1val : s1.val = vb.val := by rw [hs1def, Array.val_to_slice]
    have hvblen : vb.val.length = 320 := vb.property
    have hcplen : s.length = s1.length := by
      rw [hs_len]; show i2.val - st.val = s1.val.length
      rw [hs1val, hvblen, hi2v, hstv]; omega
    step with core.slice.Slice.copy_from_slice.step_spec as ⟨ s2, hs2 ⟩
    -- out_buf1 = out_buf.setSlice! (start·320) vec_bytes[i]
    have hob1val : (index_mut_back s2).val = out_buf.val.setSlice! (iter.start.val * 320) vb.val := by
      rw [hs_back s2, hs2, hs1val, hstv]; rfl
    have hob1len : (index_mut_back s2).val.length = L.val * 320 + 32 := by
      rw [hob1val, List.length_setSlice!, hlen]
    -- recurse; the byte at `index_mut_back s2` was `hvb`-fixed to the original vec_bytes[i]
    have hvbeq : vb.val = (self.vec_bytes.val[iter.start.val]!).val := by
      rw [hvb, getElem!_pos self.vec_bytes.val iter.start.val (by
        have := self.vec_bytes.property; simpa [Array.length] using hib)]
    apply WP.spec_mono
      (serialize_loop_val_spec self iter1 (index_mut_back s2) hob1len
        (by rw [hstart']; scalar_tac) (by rw [hend']; exact hend))
    rintro ⟨pk', ob'⟩ ⟨hpk', hlen', hpost⟩
    refine ⟨hpk', hlen', ?_⟩
    intro pos hpos
    rw [hpost pos hpos, hstart', hob1val]
    by_cases hcase1 : (iter.start.val + 1) * 320 ≤ pos ∧ pos < L.val * 320
    · have hmono : iter.start.val * 320 ≤ (iter.start.val + 1) * 320 :=
        Nat.mul_le_mul_right 320 (Nat.le_succ _)
      rw [if_pos hcase1, if_pos ⟨by omega, hcase1.2⟩]
    · rw [if_neg hcase1]
      by_cases hpc : pos < iter.start.val * 320
      · rw [List.getElem!_setSlice!_prefix _ _ _ _ hpc,
          if_neg (by omega : ¬(iter.start.val * 320 ≤ pos ∧ pos < L.val * 320))]
      · by_cases hpc2 : pos < iter.start.val * 320 + 320
        · rw [List.getElem!_setSlice!_middle _ _ _ _
            ⟨by omega, by rw [hvblen]; omega, by rw [hlen]; omega⟩, hvbeq]
          have hdiv : pos / 320 = iter.start.val := by omega
          have hmod : pos % 320 = pos - iter.start.val * 320 := by omega
          rw [if_pos ⟨by omega, by omega⟩, hdiv, hmod]
        · -- pos ≥ start·320+320; not in case1 forces pos ≥ L·320
          have hnotcase : ¬((iter.start.val + 1) * 320 ≤ pos ∧ pos < L.val * 320) := hcase1
          have he : (iter.start.val + 1) * 320 = iter.start.val * 320 + 320 := by ring
          rw [List.getElem!_setSlice!_suffix _ _ _ _ (by rw [hvblen]; omega),
            if_neg (by omega : ¬(iter.start.val * 320 ≤ pos ∧ pos < L.val * 320))]
  · let* ⟨ o, iter1, hnone, _ ⟩ ← core.iter.range.IteratorRange.next_Usize_none_spec
    rw [hnone]; simp only [WP.spec_ok]
    have hge : iter.start.val = L.val := by scalar_tac
    refine ⟨rfl, by rw [hlen], ?_⟩
    intro pos hpos
    rw [if_neg (by rw [hge]; omega : ¬(iter.start.val * 320 ≤ pos ∧ pos < L.val * 320))]
  termination_by iter.«end».val - iter.start.val
  decreasing_by scalar_decr_tac

theorem pke_serialize_spec {L : Usize} (self : pke.PkePublicKey L) (out_buf : Slice U8)
    (hlen : out_buf.val.length = L.val * 320 + 32) (hfit : L.val * 10 * 256 ≤ Usize.max) :
    pke.PkePublicKey.serialize self out_buf
      ⦃ (r : Slice U8) => r.length = L.val * (32 * 10) + 32 ∧
          r.val.map (·.bv) = (vecBytesFlat self).toList
            ++ (arrayToBytes self.matrix_seed).toList ⦄ := by
  have hmax : L.val * 320 + 32 ≤ Usize.max := by rw [← hlen]; exact out_buf.property
  have hb0 : L.val * 10 ≤ Usize.max := le_trans (Nat.le_mul_of_pos_right _ (by norm_num)) hfit
  unfold pke.PkePublicKey.serialize pke.PkePublicKey.SERIALIZED_LEN
  simp only [consts.RING_DEG]
  let* ⟨ i0, hi0 ⟩ ← Std.Usize.mul_spec (x := L) (y := 10#usize) hb0
  let* ⟨ i1, hi1 ⟩ ← Std.Usize.mul_spec (x := i0) (y := 256#usize) (by rw [hi0]; exact hfit)
  let* ⟨ i2, hi2 ⟩ ← Std.Usize.div_spec
  have hi2v : i2.val = L.val * 320 := by rw [hi2, hi1, hi0]; omega
  let* ⟨ out_size, hos ⟩ ← Std.Usize.add_spec (x := 32#usize) (y := i2) (by rw [hi2v]; scalar_tac)
  have hosv : out_size.val = L.val * 320 + 32 := by rw [hos, hi2v]; omega
  have hoblen : out_buf.length = L.val * 320 + 32 := by rw [Slice.length]; exact hlen
  rw [show massert (Slice.len out_buf = out_size) = ok () from by
    have : Slice.len out_buf = out_size := by
      apply Std.UScalar.eq_of_val_eq; rw [Slice.len_val, hoblen, hosv]
    simp only [massert, if_pos this], bind_tc_ok]
  -- the vec_bytes-copy loop
  let* ⟨ self1, out_buf1, hself1, hlr_len, hlr_val ⟩ ←
    serialize_loop_val_spec self { start := 0#usize, «end» := L } out_buf hlen (by simp) rfl
  rw [hself1]
  -- i1' = L * 320
  let* ⟨ eb, hebv ⟩ ← pk_vec_elem_bytes_spec
  let* ⟨ ii, hii ⟩ ← Std.Usize.mul_spec (x := L) (y := eb)
    (by rw [hebv]; have : L.val * 320 ≤ L.val * 320 + 32 := by omega
        exact le_trans this hmax)
  have hiiv : ii.val = L.val * 320 := by rw [hii, hebv]
  -- s2 = out_buf1[L·320 ..]
  have hbnd2 : ({ start := ii } : core.ops.range.RangeFrom Usize).start ≤ out_buf1.length := by
    show ii.val ≤ out_buf1.length; rw [Slice.length, hlr_len, hiiv]; omega
  step with core.slice.index.SliceIndexRangeFromUsizeSlice.index_mut.step_spec as
    ⟨ s2, index_mut_back1, hs2_val, hs2_len, hs2_back ⟩
  rw [show (lift self.matrix_seed.to_slice : Result (Slice U8))
      = ok (Array.to_slice self.matrix_seed) from rfl, bind_tc_ok]
  set s3 := Array.to_slice self.matrix_seed with hs3def
  have hs3 : s3.val = self.matrix_seed.val := by rw [hs3def, Array.val_to_slice]
  have hs3len : s3.length = 32 := by
    simp only [hs3def, Slice.length, Array.val_to_slice]; exact self.matrix_seed.property
  have hs2len32 : s2.length = 32 := by
    rw [hs2_len, Slice.length, hlr_len, hiiv]; omega
  have hcpbnd : s2.length = s3.length := by rw [hs2len32, hs3len]
  step with core.slice.Slice.copy_from_slice.step_spec as ⟨ s4, hs4 ⟩
  -- final reconstruction
  have hres : (index_mut_back1 s4).val
      = out_buf1.val.setSlice! (L.val * 320) self.matrix_seed.val := by
    rw [hs2_back s4, hs4, hiiv, hs3]
  have hreslen : (index_mut_back1 s4).length = L.val * (32 * 10) + 32 := by
    rw [Slice.length, hres, List.length_setSlice!, hlr_len]
  refine ⟨hreslen, ?_⟩
  have hmslen : self.matrix_seed.val.length = 32 := self.matrix_seed.property
  apply List.ext_getElem
  · rw [List.length_map, ← Slice.length, hreslen, List.length_append, Vector.toList_length,
      Vector.toList_length]; scalar_tac
  · intro pos h1 h2
    rw [← getElem!_pos _ pos h1, ← getElem!_pos _ pos h2]
    have hposlt : pos < L.val * 320 + 32 := by
      rw [List.length_map, ← Slice.length, hreslen] at h1; omega
    rw [List.getElem!_map_eq _ pos (fun (x : U8) => x.bv) (by rw [← Slice.length, hreslen]; omega),
      hres]
    by_cases hpc : pos < L.val * 320
    · rw [List.getElem!_setSlice!_prefix _ _ _ _ hpc, hlr_val pos hposlt, if_pos ⟨by omega, hpc⟩,
        List.getElem!_append_left _ _ _ (by rw [Vector.toList_length]; exact hpc),
        vecBytesFlat_getElem! self pos hpc]
    · push Not at hpc
      rw [List.getElem!_setSlice!_middle _ _ _ _
        ⟨hpc, by rw [hmslen]; omega, by rw [hlr_len]; omega⟩,
        List.getElem!_append_right _ _ _ (by rw [Vector.toList_length]; omega),
        Vector.toList_length, arrayToBytes_toList,
        List.getElem!_map_eq _ (pos - L.val * 320) (fun (x : U8) => x.bv) (by rw [hmslen]; omega)]

end Kopis.Properties
