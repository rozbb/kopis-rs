/-
  # Kopis/Properties/PkeFromBytes.lean — `PkePublicKey::from_bytes` correspondence.

  `from_bytes` is the parser that turns a received public-key byte string back into
  the struct the crate works with. It is the exact counterpart of
  `pke_serialize_spec` (`Kopis/Properties/PkeSerialize.lean`), and it corresponds
  to the way the audited spec reads a public key inside `PkeEncrypt`:

      vec_b    = PolyVector.deserialize 10 (slice pk 0 (32·10·ℓ))
      mat_seed = slice pk (32·10·ℓ) 32
      mat_A    = GenMat ℓ mat_seed

  The theorem below says the three fields of the parsed struct are exactly those
  three values. Note the last one is not merely copied out of the input: `from_bytes`
  *re-derives* the public matrix from the seed by running `gen_matrix_from_seed`,
  which is why the postcondition ties `mat_a` to `GenMat`.

  The hypotheses are shape side conditions only (the input has the serialized
  length, and the serialized size fits in a `usize`); nothing constrains the
  *contents* of the bytes, so this covers arbitrary — including adversarially
  chosen — public-key encodings.
-/
import Kopis.Properties.DeserializeVec
import Kopis.Properties.GenMatrix
import Kopis.Properties.KeyGenHyps
import Kopis.Properties.PkeDecryptTop
open Aeneas Aeneas.Std Result RustKopisSerial
open Spec (𝔹)
namespace Kopis.Properties
set_option maxHeartbeats 4000000
set_option maxRecDepth 4000

/-! ## Bridge

The prefix/suffix bridges (`sliceToBytes_take_eq_slice`, `sliceToBytes_drop_eq_slice`)
and `deserialize_vec_toList_cast` already exist in `Kopis/Properties/PkeDecryptTop.lean`,
where the ciphertext parser needs exactly the same reasoning.  Only the
array-to-slice step for the 32-byte matrix seed is new. -/

/-- The `𝔹 32` view of a public key's matrix seed is the byte abstraction of any
slice holding the same bytes. -/
theorem matSeed_eq_sliceToBytes {L : Usize} (pk : pke.PkePublicKey L) (t : Slice U8)
    (ht : t.length = 32) (hval : pk.matrix_seed.val = t.val) :
    matSeedBytes pk = sliceToBytes t 32 ht := by
  apply Vector.toList_inj.mp
  rw [show (matSeedBytes pk).toList = pk.matrix_seed.val.map (·.bv) from by
        unfold matSeedBytes; rw [Vector.toList_cast]; exact arrayToBytes_toList _,
      sliceToBytes_toList, hval]

/-- A Rust array and a slice holding the same bytes have the same abstraction.  Stated
at the single index `(n : ℕ)` so both sides are syntactically at the same length. -/
theorem arrayToBytes_eq_sliceToBytes {n : Usize} (a : Array U8 n) (t : Slice U8)
    (ht : t.length = (n : ℕ)) (hval : a.val = t.val) :
    arrayToBytes a = sliceToBytes t (n : ℕ) ht := by
  apply Vector.toList_inj.mp
  rw [arrayToBytes_toList, sliceToBytes_toList, hval]

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

/-- `from_bytes_loop` copies each `320`-byte chunk `vec_slice[i·320 .. i·320+320)` into
`vec_bytes[i]` verbatim, leaving rows before `start` untouched. -/
theorem from_bytes_loop_val_spec {L : Usize} (iter : core.ops.range.Range Usize)
    (vec_slice : Slice U8) (vec_bytes : Array (Array U8 320#usize) L)
    (hvslen : vec_slice.length = L.val * 320)
    (hstart : iter.start.val ≤ L.val) (hend : iter.«end».val = L.val) :
    pke.PkePublicKey.from_bytes_loop iter vec_slice vec_bytes
      ⦃ (r : Array (Array U8 320#usize) L) =>
          ∀ i, i < L.val → ∀ c, c < 320 →
            (r.val[i]!).val[c]! =
              if iter.start.val ≤ i then vec_slice.val[i * 320 + c]!
              else (vec_bytes.val[i]!).val[c]! ⦄ := by
  unfold pke.PkePublicKey.from_bytes_loop
  have hVBmax : L.val * 320 ≤ Usize.max := hvslen ▸ vec_slice.property
  have hvsl : vec_slice.val.length = L.val * 320 := by rw [Slice.length] at hvslen; exact hvslen
  by_cases hlt : iter.start.val < iter.«end».val
  · let* ⟨o, iter1, ho, hstart', hend'⟩ ← core.iter.range.IteratorRange.next_Usize_some_spec
    rw [ho]; simp only
    have hi_lt : iter.start.val < L.val := by scalar_tac
    let* ⟨eb, hebv⟩ ← pk_vec_elem_bytes_spec
    let* ⟨st, hst⟩ ← Std.Usize.mul_spec (x := iter.start) (y := eb)
      (by rw [hebv]; exact le_trans (Nat.mul_le_mul_right 320 (le_of_lt hi_lt)) hVBmax)
    have hstv : st.val = iter.start.val * 320 := by rw [hst, hebv]
    have hvbi : iter.start.val < vec_bytes.length := by have := vec_bytes.property; scalar_tac
    let* ⟨a, index_mut_back, ha, hback⟩ ← Array.index_mut_usize_spec vec_bytes iter.start hvbi
    let* ⟨s, to_slice_mut_back, hs_val, hs_back⟩ ← Array.to_slice_mut_spec a
    let* ⟨i2, hi2⟩ ← Std.Usize.add_spec (x := st) (y := eb)
      (by rw [hstv, hebv]
          calc iter.start.val * 320 + 320 = (iter.start.val + 1) * 320 := by ring
            _ ≤ L.val * 320 := Nat.mul_le_mul_right 320 (by omega)
            _ ≤ Usize.max := hVBmax)
    have hi2v : i2.val = iter.start.val * 320 + 320 := by rw [hi2, hstv, hebv]
    have hb0 : st ≤ i2 := by rw [UScalar.le_equiv, hstv, hi2v]; omega
    have hb1 : i2 ≤ vec_slice.length := by
      have hle : (iter.start.val + 1) * 320 ≤ L.val * 320 := Nat.mul_le_mul_right 320 (by omega)
      have he : (iter.start.val + 1) * 320 = iter.start.val * 320 + 320 := by ring
      show i2.val ≤ vec_slice.length
      simp only [Slice.length]; rw [hi2v]; omega
    step with core.slice.index.SliceIndexRangeUsizeSlice.index.step_spec as ⟨s1, hs1_val, hs1_len⟩
    have haslen : a.val.length = 320 := a.property
    have hcplen : s.length = s1.length := by
      rw [hs1_len, Slice.length, hs_val, haslen, hi2v, hstv]; omega
    step with core.slice.Slice.copy_from_slice.step_spec as ⟨s2, hs2⟩
    have hs2len : s2.val.length = 320 := by
      rw [hs2]
      have h : s1.val.length = i2.val - st.val := by rw [← Slice.length, hs1_len]
      rw [h, hi2v, hstv]; omega
    have hs2val : (to_slice_mut_back s2).val = vec_slice.val.slice (iter.start.val * 320) (iter.start.val * 320 + 320) := by
      rw [hs_back, Array.from_slice_val a s2 hs2len, hs2, hs1_val, hi2v, hstv]
    have hbacki : (index_mut_back (to_slice_mut_back s2)).val
        = vec_bytes.val.set iter.start.val (to_slice_mut_back s2) := by
      rw [hback]; simp only [Array.set_val_eq]
    have hvbl : iter.start.val < vec_bytes.val.length := by have := vec_bytes.property; scalar_tac
    apply WP.spec_mono
      (from_bytes_loop_val_spec iter1 vec_slice (index_mut_back (to_slice_mut_back s2)) hvslen
        (by rw [hstart']; scalar_tac) (by rw [hend']; exact hend))
    intro r hr i hi c hc
    rw [hr i hi c hc, hstart']
    by_cases hcase : iter.start.val + 1 ≤ i
    · rw [if_pos hcase, if_pos (by omega : iter.start.val ≤ i)]
    · rw [if_neg hcase, hbacki]
      by_cases hii : i = iter.start.val
      · rw [getElem!_list_set vec_bytes.val iter.start.val (to_slice_mut_back s2) i hvbl,
          if_pos hii, hs2val, if_pos (by omega : iter.start.val ≤ i), hii,
          List.getElem!_slice (iter.start.val * 320) (iter.start.val * 320 + 320) c vec_slice.val
            ⟨by rw [hvsl]; have := Nat.mul_le_mul_right 320 (show iter.start.val + 1 ≤ L.val by omega); omega, by omega⟩]
      · rw [getElem!_list_set vec_bytes.val iter.start.val (to_slice_mut_back s2) i hvbl,
          if_neg hii, if_neg (by omega : ¬ iter.start.val ≤ i)]
  · let* ⟨o, iter1, hnone, _⟩ ← core.iter.range.IteratorRange.next_Usize_none_spec
    rw [hnone]; simp only [WP.spec_ok]
    have hge : iter.start.val = L.val := by scalar_tac
    intro i hi c hc
    rw [if_neg (by omega : ¬ iter.start.val ≤ i)]
  termination_by iter.«end».val - iter.start.val
  decreasing_by scalar_decr_tac

/-! ## `PkePublicKey::from_bytes` -/

/-- **Rust public-key parsing matches the spec.**  `PkePublicKey::from_bytes`
splits its input into a `320·ℓ`-byte vector encoding and a 32-byte matrix seed,
deserializes the former with the 10-bit decoder, and regenerates the public matrix
from the latter.  Each field of the resulting struct is the corresponding value the
audited spec reads out of a public key. -/
theorem pke_from_bytes_spec {L : Usize} (bytes : Slice U8)
    (hlen : bytes.length = 320 * L.val + 32)
    (hfit : L.val * 10 * 256 ≤ Usize.max) :
    pke.PkePublicKey.from_bytes L bytes
      ⦃ (pk : pke.PkePublicKey L) =>
          (∃ V : Mat L 1#usize, pk.vec_ntt = nttFwdU V ∧
              toVecN 10 V
                = Spec.Kopis.PolyVector.deserialize (ℓ := L.val) 10
                    (Spec.slice (sliceToBytes bytes (320 * L.val + 32) hlen) 0
                      (32 * 10 * L.val) (by omega)) ∧
              UniformBounded V) ∧
          matSeedBytes pk
            = Spec.slice (sliceToBytes bytes (320 * L.val + 32) hlen)
                (32 * 10 * L.val) 32 (by omega) ∧
          (∃ Amat : Mat L L, pk.mat_a_ntt = nttFwdU Amat ∧
              toMatrix13 Amat = Spec.Kopis.GenMat L.val (arrayToBytes pk.matrix_seed) ∧
              UniformBounded Amat) ∧
          vecBytesFlat pk
            = (Spec.slice (sliceToBytes bytes (320 * L.val + 32) hlen) 0
                (32 * 10 * L.val) (by omega)).cast (by ring) ⦄ := by
  have hmax : 320 * L.val + 32 ≤ Usize.max := by
    rw [← hlen]; exact bytes.property
  have hb0 : L.val * 10 ≤ Usize.max := le_trans (Nat.le_mul_of_pos_right _ (by norm_num)) hfit
  have e32 : (32#usize).val = 32 := rfl
  unfold pke.PkePublicKey.from_bytes pke.PkePublicKey.SERIALIZED_LEN
  simp only [consts.10, consts.RING_DEG]
  -- SERIALIZED_LEN = 32 + L·10·256/8 = 32 + L·320
  let* ⟨ i0, hi0 ⟩ ← Std.Usize.mul_spec (x := L) (y := 10#usize) hb0
  let* ⟨ i1, hi1 ⟩ ← Std.Usize.mul_spec (x := i0) (y := 256#usize) (by rw [hi0]; exact hfit)
  let* ⟨ i2, hi2 ⟩ ← Std.Usize.div_spec
  have hi2v : i2.val = L.val * 320 := by rw [hi2, hi1, hi0]; omega
  let* ⟨ out_size, hos ⟩ ← Std.Usize.add_spec (x := 32#usize) (y := i2) (by rw [hi2v]; omega)
  have hosv : out_size.val = L.val * 320 + 32 := by rw [hos, hi2v]; omega
  have hblen : bytes.length = L.val * 320 + 32 := by rw [hlen]; omega
  -- the length assertion succeeds
  rw [show massert (Slice.len bytes = out_size) = ok () from by
    have : Slice.len bytes = out_size := by
      apply Std.UScalar.eq_of_val_eq; rw [Slice.len_val, hosv]; exact hblen
    simp only [massert, if_pos this], bind_tc_ok]
  -- split at L·320
  let* ⟨ ii, hii ⟩ ← Std.Usize.sub_spec (x := out_size) (y := 32#usize) (by rw [hosv]; omega)
  have hiiv : ii.val = L.val * 320 := by rw [hii, hosv]; omega
  let* ⟨ vec_slice, seed, hvs_len, hseed_len, hvs_val, hseed_val ⟩ ←
    core.slice.Slice.split_at.spec bytes ii (by rw [hblen, hiiv]; omega)
  have hvslen : vec_slice.length = L.val * (32 * 10) := by rw [hvs_len, hiiv]
  have hseedlen : seed.length = 32 := by rw [hseed_len, hblen, hiiv]; omega
  -- the 32-byte seed is copied out unchanged (this comes first in the new extraction)
  let* ⟨ r, hr ⟩ ← core.array.TryFromArrayCopySlice.try_from.step 32#usize core.marker.CopyU8 seed
  have hrok : ∃ v, r = core.result.Result.Ok v := by
    cases r with
    | Ok a => exact ⟨a, rfl⟩
    | Err e =>
      cases e
      simp only at hr
      exact absurd (by rw [hseedlen]; rfl : seed.length = (32#usize : Usize).val) hr
  let* ⟨ matrix_seed, hms ⟩ ← core.result.Result.unwrap.step_spec _ r hrok
  rw [hms] at hr
  simp only at hr
  obtain ⟨ hms_val, _hms_len ⟩ := hr
  -- the 10-bit vector decoder, then its NTT representation
  let* ⟨ vec, hvec, hvecbnd ⟩ ← spec_and (matrix_deserialize_10_spec vec_slice hvslen hfit)
    (deserialize_10_uniformBounded vec_slice hvslen hfit)
  let* ⟨ vec_ntt, hvecntt ⟩ ← from_uniform_matrix_spec vec
  -- the verbatim byte copy loop (result not otherwise needed); then regenerate the matrix
  let* ⟨ vec_bytes1, hvbchar ⟩ ← from_bytes_loop_val_spec { start := 0#usize, «end» := L } vec_slice
    (Array.repeat L (Array.repeat 320#usize 0#u8)) (by rw [hvs_len, hiiv]) (by simp) rfl
  let* ⟨ mat_a, hmat, hmatbnd ⟩ ← spec_and (gen_matrix_from_seed_spec L matrix_seed)
    (gen_matrix_uniformBounded matrix_seed)
  let* ⟨ mat_a_ntt, hmatntt ⟩ ← from_uniform_matrix_spec mat_a
  -- assemble
  have hvslen' : vec_slice.length = 32 * 10 * L.val := by rw [hvslen]; ring
  have hvsdrop : vec_slice.val = bytes.val.take (32 * 10 * L.val) := by
    rw [hvs_val, hiiv]; congr 1; ring
  have hseeddrop : seed.val = bytes.val.drop (32 * 10 * L.val) := by
    rw [hseed_val, hiiv]; congr 1; ring
  -- the matrix seed is the [32·10·ℓ, +32) window of the input
  have hseedbytes : matSeedBytes (L := L)
        ⟨matrix_seed, mat_a_ntt, vec_bytes1, vec_ntt⟩
      = Spec.slice (sliceToBytes bytes (320 * L.val + 32) hlen)
          (32 * 10 * L.val) 32 (by omega) := by
    rw [matSeed_eq_sliceToBytes _ seed hseedlen (by show matrix_seed.val = _; exact hms_val)]
    exact sliceToBytes_drop_eq_slice bytes seed (320 * L.val + 32) (32 * 10 * L.val) 32
      hlen (by ring) hseeddrop hseedlen
  -- the vector encoding is the [0, 32·10·ℓ) window of the input
  have hvbtake : sliceToBytes vec_slice (32 * 10 * L.val) hvslen'
      = Spec.slice (sliceToBytes bytes (320 * L.val + 32) hlen) 0
          (32 * 10 * L.val) (by omega) :=
    sliceToBytes_take_eq_slice bytes vec_slice (320 * L.val + 32) (32 * 10 * L.val)
      hlen (by omega) hvsdrop hvslen'
  have hab : ((sliceToBytes vec_slice (L.val * (32 * 10)) hvslen).cast (by ring)
        : 𝔹 (32 * 10 * L.val)).toList
      = (Spec.slice (sliceToBytes bytes (320 * L.val + 32) hlen) 0
          (32 * 10 * L.val) (by omega)).toList := by
    rw [Vector.toList_cast, sliceToBytes_toList, ← hvbtake, sliceToBytes_toList]
  have hbyteslen : bytes.val.length = 320 * L.val + 32 := by rw [Slice.length] at hlen; exact hlen
  refine ⟨⟨vec, hvecntt, hvec.trans (deserialize_vec_toList_cast rfl _ _ hab), hvecbnd⟩,
          hseedbytes, ⟨mat_a, hmatntt, hmat, hmatbnd⟩, ?_⟩
  · -- the stored vector bytes are exactly the input's `[0, 32·10·ℓ)` prefix
    have hvsl' : vec_slice.val.length = 32 * 10 * L.val := by rw [Slice.length] at hvslen'; exact hvslen'
    rw [← hvbtake]
    apply Vector.toList_inj.mp
    rw [Vector.toList_cast, sliceToBytes_toList]
    apply List.ext_getElem
    · rw [Vector.toList_length, List.length_map, hvsl']; ring
    · intro pos h1 h2
      have hpos : pos < L.val * 320 := by rw [Vector.toList_length] at h1; exact h1
      have hi : pos / 320 < L.val := by rw [Nat.div_lt_iff_lt_mul (by norm_num)]; omega
      have hcm : pos % 320 < 320 := Nat.mod_lt _ (by norm_num)
      have hpe : pos / 320 * 320 + pos % 320 = pos := by
        rw [Nat.mul_comm]; exact Nat.div_add_mod pos 320
      rw [← getElem!_pos _ pos h1, ← getElem!_pos _ pos h2,
        vecBytesFlat_getElem! _ pos hpos, hvbchar (pos / 320) hi (pos % 320) hcm,
        if_pos (Nat.zero_le _), hpe,
        List.getElem!_map_eq _ pos (fun (x : U8) => x.bv) (by omega)]

end Kopis.Properties
