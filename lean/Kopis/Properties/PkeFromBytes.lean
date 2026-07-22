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
open Aeneas Aeneas.Std Result RustKopis
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
          toVecN 10 pk.vec
            = Spec.Kopis.PolyVector.deserialize (ℓ := L.val) 10
                (Spec.slice (sliceToBytes bytes (320 * L.val + 32) hlen) 0
                  (32 * 10 * L.val) (by omega)) ∧
          matSeedBytes pk
            = Spec.slice (sliceToBytes bytes (320 * L.val + 32) hlen)
                (32 * 10 * L.val) 32 (by omega) ∧
          toMatrix13 pk.mat_a = Spec.Kopis.GenMat L.val (arrayToBytes pk.matrix_seed) ⦄ := by
  have hmax : 320 * L.val + 32 ≤ Usize.max := by
    rw [← hlen]; exact bytes.property
  have hb0 : L.val * 10 ≤ Usize.max := le_trans (Nat.le_mul_of_pos_right _ (by norm_num)) hfit
  have e32 : (32#usize).val = 32 := rfl
  unfold pke.PkePublicKey.from_bytes pke.PkePublicKey.SERIALIZED_LEN
  simp only [consts.MODULUS_P_BITS, consts.RING_DEG]
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
  let* ⟨ vec_bytes, seed, hvb_len, hseed_len, hvb_val, hseed_val ⟩ ←
    core.slice.Slice.split_at.spec bytes ii (by rw [hblen, hiiv]; omega)
  have hvblen : vec_bytes.length = L.val * (32 * 10) := by rw [hvb_len, hiiv]
  have hseedlen : seed.length = 32 := by rw [hseed_len, hblen, hiiv]; omega
  -- the 10-bit vector decoder
  let* ⟨ vec, hvec ⟩ ← matrix_deserialize_10_spec vec_bytes hvblen hfit
  -- the 32-byte seed is copied out unchanged
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
  -- the public matrix is regenerated from that seed
  let* ⟨ mat_a, hmat ⟩ ← gen_matrix_from_seed_spec L matrix_seed
  -- assemble
  have hvblen' : vec_bytes.length = 32 * 10 * L.val := by rw [hvblen]; ring
  have hvbdrop : vec_bytes.val = bytes.val.take (32 * 10 * L.val) := by
    rw [hvb_val, hiiv]; congr 1; ring
  have hseeddrop : seed.val = bytes.val.drop (32 * 10 * L.val) := by
    rw [hseed_val, hiiv]; congr 1; ring
  -- the matrix seed is the [32·10·ℓ, +32) window of the input
  have hseedbytes : matSeedBytes (L := L) ⟨matrix_seed, vec, mat_a⟩
      = Spec.slice (sliceToBytes bytes (320 * L.val + 32) hlen)
          (32 * 10 * L.val) 32 (by omega) := by
    rw [matSeed_eq_sliceToBytes _ seed hseedlen (by show matrix_seed.val = _; exact hms_val)]
    exact sliceToBytes_drop_eq_slice bytes seed (320 * L.val + 32) (32 * 10 * L.val) 32
      hlen (by ring) hseeddrop hseedlen
  -- the vector encoding is the [0, 32·10·ℓ) window of the input
  have hvbtake : sliceToBytes vec_bytes (32 * 10 * L.val) hvblen'
      = Spec.slice (sliceToBytes bytes (320 * L.val + 32) hlen) 0
          (32 * 10 * L.val) (by omega) :=
    sliceToBytes_take_eq_slice bytes vec_bytes (320 * L.val + 32) (32 * 10 * L.val)
      hlen (by omega) hvbdrop hvblen'
  have hab : ((sliceToBytes vec_bytes (L.val * (32 * 10)) hvblen).cast (by ring)
        : 𝔹 (32 * 10 * L.val)).toList
      = (Spec.slice (sliceToBytes bytes (320 * L.val + 32) hlen) 0
          (32 * 10 * L.val) (by omega)).toList := by
    rw [Vector.toList_cast, sliceToBytes_toList, ← hvbtake, sliceToBytes_toList]
  exact ⟨hvec.trans (deserialize_vec_toList_cast rfl _ _ hab), hseedbytes, hmat⟩

end Kopis.Properties
