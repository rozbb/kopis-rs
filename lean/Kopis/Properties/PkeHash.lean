import Kopis.Properties.PkeSerialize
import Kopis.Properties.GenSecretTop
open Aeneas Aeneas.Std Result RustKopis
open Spec (𝔹)
open scoped Spec.Notations
open Spec.TurboSHAKE (turboSHAKE256)
open Spec.Kopis (DOMSEP_PKHASH)
namespace Kopis.Properties
set_option maxHeartbeats 2000000
set_option maxRecDepth 4000

theorem domsep_pkhash_bv : (4#u8).bv = DOMSEP_PKHASH := by decide

/-- The 32-byte matrix seed as a clean `𝔹 32` (literal-sized), matching the spec's
`mat_seed : 𝔹 32`. -/
def matSeedBytes {L : Usize} (self : pke.PkePublicKey L) : 𝔹 32 :=
  (arrayToBytes self.matrix_seed).cast rfl

theorem pke_hash_spec {L : Usize} (self : pke.PkePublicKey L)
    (hbuf : L.val * 320 + 32 ≤ 1312) (hfit : L.val * 10 * 256 ≤ Usize.max) :
    pke.PkePublicKey.hash self
      ⦃ (r : Array U8 32#usize) => arrayToBytes r
          = turboSHAKE256
              (Spec.Kopis.PolyVector.serialize 10 (toVecN 10 self.vec) ‖ matSeedBytes self)
              DOMSEP_PKHASH 32 ⦄ := by
  have hb0 : L.val * 10 ≤ Usize.max := le_trans (Nat.le_mul_of_pos_right _ (by norm_num)) hfit
  have hmax : L.val * 320 + 32 ≤ Usize.max := le_trans hbuf (by scalar_tac)
  have e32 : (32#usize).val = 32 := rfl
  unfold pke.PkePublicKey.hash pke.PkePublicKey.SERIALIZED_LEN
  simp only [consts.MODULUS_P_BITS, consts.RING_DEG]
  let* ⟨ i0, hi0 ⟩ ← Std.Usize.mul_spec (x := L) (y := 10#usize) hb0
  let* ⟨ i1, hi1 ⟩ ← Std.Usize.mul_spec (x := i0) (y := 256#usize) (by rw [hi0]; exact hfit)
  let* ⟨ i2, hi2 ⟩ ← Std.Usize.div_spec
  have hi2v : i2.val = L.val * 320 := by rw [hi2, hi1, hi0]; omega
  let* ⟨ out_size, hos ⟩ ← Std.Usize.add_spec (x := 32#usize) (y := i2) (by rw [hi2v]; omega)
  have hosv : out_size.val = L.val * 320 + 32 := by rw [hos, hi2v]; omega
  -- index_mut buf
  have hbnd : ({ «end» := out_size } : core.ops.range.RangeTo Usize).«end» ≤ (1312#usize) := by
    rw [UScalar.le_equiv, hosv]; exact hbuf
  progress with Array.index_mut_SliceIndexRangeToUsizeSlice as
    ⟨ pk_slice, back, hpk_val, hpk_len, hpk_back ⟩
  have hpkvlen : pk_slice.val.length = L.val * 320 + 32 := by
    rw [← Slice.length, hpk_len, hosv]
  let* ⟨ pk_slice1, hpk1_len, hpk1_bytes ⟩ ← pke_serialize_spec self pk_slice hpkvlen hfit
  rw [show (lift (Array.to_slice (Std.Array.empty U8)) : Result (Slice U8))
      = ok (Array.to_slice (Std.Array.empty U8)) from rfl, bind_tc_ok]
  unfold turboshake256_hash
  step*
  have habs : hasherAbsorbed hasher2 = pk_slice1.val := by
    rw [hasher2_post, hasher1_post, hasher_post]
    simp [Array.to_slice, Std.Array.empty]
  have hslen : s.length = 32 := by
    rw [Slice.length, s_post1]; simpa using (Array.repeat 32#usize 0#u8).property
  have hs1len : s1.length = 32 := by rw [__post1, hslen]
  rw [reader_post1, reader_post2] at __post2
  dsimp only at __post2
  rw [Nat.zero_add, hslen] at __post2
  rw [habs] at __post2
  have hlen1 : pk_slice1.val.length = L.val * (32 * 10) + 32 := hpk1_len
  -- the absorbed bytes (recast to the right length) equal the spec's `serialize ‖ matrix_seed`
  have hXY : (u8ListToBytes pk_slice1.val).cast hlen1
      = Spec.Kopis.PolyVector.serialize 10 (toVecN 10 self.vec) ‖ matSeedBytes self := by
    apply Vector.toList_inj.mp
    rw [Vector.toList_cast]
    have hu : (u8ListToBytes pk_slice1.val).toList = pk_slice1.val.map (·.bv) := by
      simp only [u8ListToBytes, Vector.toList_ofFn]; rw [List.ofFn_getElem_eq_map]
    rw [hu, hpk1_bytes]
    show Vector.toList (Spec.Kopis.PolyVector.serialize 10 (toVecN 10 self.vec))
        ++ Vector.toList (arrayToBytes self.matrix_seed)
      = (Spec.Kopis.PolyVector.serialize 10 (toVecN 10 self.vec) ++ matSeedBytes self).toList
    rw [Vector.toList_append]
    rfl
  have hbridge : turboSHAKE256 (u8ListToBytes pk_slice1.val) (4#u8).bv 32
      = turboSHAKE256 (Spec.Kopis.PolyVector.serialize 10 (toVecN 10 self.vec)
          ‖ matSeedBytes self) DOMSEP_PKHASH 32 := by
    rw [domsep_pkhash_bv, ← turboSHAKE256_cast hlen1 (u8ListToBytes pk_slice1.val) DOMSEP_PKHASH 32, hXY]
  rw [s_post2]
  apply Vector.toList_inj.mp
  rw [arrayToBytes_toList, Array.from_slice_val _ s1 (by rw [← Slice.length, hs1len]; exact e32.symm),
    ← hbridge]
  exact __post2

end Kopis.Properties
