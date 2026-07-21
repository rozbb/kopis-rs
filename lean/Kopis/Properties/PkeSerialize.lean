import Kopis.Properties.MatrixSerialize
import Kopis.Properties.GenMatrix
open Aeneas Aeneas.Std Result kopis_kem
open Spec (𝔹)
namespace Kopis.Properties
set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
theorem pke_serialize_spec {L : Usize} (self : pke.PkePublicKey L) (out_buf : Slice U8)
    (hlen : out_buf.val.length = L.val * 320 + 32) (hfit : L.val * 10 * 256 ≤ Usize.max) :
    pke.PkePublicKey.serialize self out_buf
      ⦃ (r : Slice U8) => r.length = L.val * (32 * 10) + 32 ∧
          r.val.map (·.bv) = (Spec.Kopis.PolyVector.serialize 10 (toVecN 10 self.vec)).toList
            ++ (arrayToBytes self.matrix_seed).toList ⦄ := by
  have hmax : L.val * 320 + 32 ≤ Usize.max := by rw [← hlen]; scalar_tac
  have hb0 : L.val * 10 ≤ Usize.max := le_trans (Nat.le_mul_of_pos_right _ (by norm_num)) hfit
  unfold pke.PkePublicKey.serialize pke.PkePublicKey.SERIALIZED_LEN
  simp only [consts.MODULUS_P_BITS, consts.RING_DEG]
  have e32 : (32#usize).val = 32 := rfl
  let* ⟨ i0, hi0 ⟩ ← Std.Usize.mul_spec (x := L) (y := 10#usize) hb0
  let* ⟨ i1, hi1 ⟩ ← Std.Usize.mul_spec (x := i0) (y := 256#usize) (by rw [hi0]; exact hfit)
  let* ⟨ i2, hi2 ⟩ ← Std.Usize.div_spec
  have hi2v : i2.val = L.val * 320 := by rw [hi2, hi1, hi0]; omega
  let* ⟨ out_size, hos ⟩ ← Std.Usize.add_spec (x := 32#usize) (y := i2) (by rw [hi2v]; omega)
  have hosv : out_size.val = L.val * 320 + 32 := by rw [hos, hi2v]; omega
  have hoblen : out_buf.length = L.val * 320 + 32 := by rw [Slice.length]; exact hlen
  -- massert (out_buf.len = out_size)
  rw [show massert (Slice.len out_buf = out_size) = ok () from by
    have : Slice.len out_buf = out_size := by
      apply Std.UScalar.eq_of_val_eq; rw [Slice.len_val, hoblen, hosv]
    simp only [massert, if_pos this], bind_tc_ok]
  let* ⟨ ii, hii ⟩ ← Std.Usize.sub_spec (x := out_size) (y := 32#usize)
    (by rw [hosv]; omega)
  have hiiv : ii.val = L.val * 320 := by rw [hii, hosv]; omega
  -- s = out_buf[0 .. L*320]
  have hbnd1 : ({ «end» := ii } : core.ops.range.RangeTo Usize).«end» ≤ out_buf.length := by
    show ii.val ≤ out_buf.length; rw [hoblen, hiiv]; omega
  progress with core.slice.index.SliceIndexRangeToUsizeSlice.index_mut.step_spec as
    ⟨ s, index_mut_back, hs_val, hs_len, hs_back ⟩
  have hsvlen : s.val.length = L.val * (32 * 10) := by
    rw [← Slice.length, hs_len, hiiv]
  let* ⟨ s1, hs1_len, hs1_bytes ⟩ ←
    matrix_serialize_col_spec self.vec s 10#usize 10 rfl ⟨by norm_num, by norm_num⟩ hsvlen hfit
  -- s2 = out_buf1[L*320 ..]
  have hob1len : (index_mut_back s1).length = L.val * 320 + 32 := by
    rw [Slice.length, hs_back s1, List.length_setSlice!, ← Slice.length, hoblen]
  have hbnd2 : ({ start := ii } : core.ops.range.RangeFrom Usize).start ≤ (index_mut_back s1).length := by
    show ii.val ≤ (index_mut_back s1).length; rw [hob1len, hiiv]; omega
  progress with core.slice.index.SliceIndexRangeFromUsizeSlice.index_mut.step_spec as
    ⟨ s2, index_mut_back1, hs2_val, hs2_len, hs2_back ⟩
  rw [show (lift self.matrix_seed.to_slice : Result (Slice U8))
      = ok (Array.to_slice self.matrix_seed) from rfl, bind_tc_ok]
  set s3 := Array.to_slice self.matrix_seed with hs3def
  have hs3 : s3.val = self.matrix_seed.val := by rw [hs3def, Array.val_to_slice]
  have hs3len : s3.length = 32 := by
    simp only [hs3def, Slice.length, Array.val_to_slice]; exact self.matrix_seed.property
  have hs2len32 : s2.length = 32 := by rw [hs2_len, hob1len, hiiv]; omega
  have hcpbnd : s2.length = s3.length := by rw [hs2len32, hs3len]
  progress with core.slice.Slice.copy_from_slice.step_spec as ⟨ s4, hs4 ⟩
  -- final reconstruction
  have hs1L : s1.length = L.val * 320 := by rw [hs1_len]
  have hreslen : (index_mut_back1 s4).length = L.val * (32 * 10) + 32 := by
    rw [Slice.length, hs2_back s4, List.length_setSlice!, ← Slice.length, hob1len]
  refine ⟨hreslen, ?_⟩
  have hres : (index_mut_back1 s4).val
      = (out_buf.val.setSlice! 0 s1.val).setSlice! (L.val * 320) self.matrix_seed.val := by
    rw [hs2_back s4, hs_back s1, hs4, hiiv, hs3]
  have hs1vlen : s1.val.length = L.val * 320 := by rw [← Slice.length, hs1_len]
  have hmslen : self.matrix_seed.val.length = 32 := self.matrix_seed.property
  have hoblen' : out_buf.val.length = L.val * 320 + 32 := hlen
  have hrval : (index_mut_back1 s4).val = s1.val ++ self.matrix_seed.val := by
    rw [hres]
    apply List.ext_getElem
    · rw [List.length_setSlice!, List.length_setSlice!, hoblen', List.length_append, hs1vlen, hmslen]
    · intro p h1 h2
      have hp32 : p < L.val * 320 + 32 := by rw [List.length_append, hs1vlen, hmslen] at h2; exact h2
      rw [← getElem!_pos _ p h1, ← getElem!_pos _ p h2]
      by_cases hpc : p < L.val * 320
      · rw [List.getElem!_setSlice!_prefix _ _ _ _ hpc,
          List.getElem!_setSlice!_middle _ _ _ _ ⟨Nat.zero_le _, by rw [hs1vlen]; omega,
            by rw [hoblen']; omega⟩, Nat.sub_zero,
          List.getElem!_append_left _ _ _ (by rw [hs1vlen]; exact hpc)]
      · push_neg at hpc
        rw [List.getElem!_setSlice!_middle _ _ _ _ ⟨hpc, by rw [hmslen]; omega,
            by rw [List.length_setSlice!, hoblen']; omega⟩,
          List.getElem!_append_right _ _ _ (by rw [hs1vlen]; exact hpc), hs1vlen]
  have hstb : ∀ (s : Slice U8) (k : ℕ) (h : s.length = k), (sliceToBytes s k h).toList = s.val.map (·.bv) := by
    intro s k h
    apply List.ext_getElem
    · simp only [sliceToBytes, Vector.toList_length, List.length_map, Slice.length] at h ⊢; omega
    · intro q h1 h2
      simp only [sliceToBytes, Vector.getElem_toList, Vector.getElem_ofFn, List.getElem_map]
  rw [hrval, List.map_append, ← hstb s1 _ hs1_len, hs1_bytes, ← arrayToBytes_toList]
end Kopis.Properties
