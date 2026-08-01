import Kopis.Properties.KeyGen
import Kopis.Properties.EncodeRoundtrip
import Kopis.Properties.KemDecap
open Aeneas Aeneas.Std Result RustKopis
open Spec (𝔹)
open scoped Spec.Notations
open Spec.TurboSHAKE (turboSHAKE256)
open Spec.Kopis (DOMSEP_PKHASH)
namespace Kopis.Properties
set_option maxHeartbeats 2000000

/-! ## Discharging the encap/decap public-key hypotheses for a key-gen output.

Given a `PkePublicKey` whose serialized form is `pkStructBytes`, the encap/decap
`hpkvec`/`hpkmat`/`hpkh` hypotheses hold.  `hpkvec` needs only the serialize/deserialize
roundtrip (it holds for ANY public key); `hpkmat`/`hpkh` additionally need the key-gen
facts that `mat_a = GenMat(matrix_seed)` and `hash = turboSHAKE256(pk)`. -/

/-- `Spec.slice` in list form. -/
theorem slice_toList {m : ℕ} (v : 𝔹 m) (off len : ℕ) (h : off + len ≤ m) :
    (Spec.slice v off len h).toList = (v.toList.drop off).take len := by
  apply List.ext_getElem
  · simp only [Vector.toList_length, List.length_take, List.length_drop, Spec.slice]; omega
  · intro k h1 h2
    have hk : k < len := by simpa [Spec.slice] using h1
    rw [Vector.getElem_toList, slice_getElem, List.getElem_take, List.getElem_drop,
      Vector.getElem_toList]

theorem pkStructBytes_toList {L : Usize} (self : pke.PkePublicKey L)
    (p : Spec.Kopis.ParameterSet) (hℓ : Spec.Kopis.ℓ p = L.val) :
    (pkStructBytes self p hℓ).toList
      = (vecBytesFlat self).toList ++ (matSeedBytes self).toList := by
  unfold pkStructBytes; rw [Vector.toList_cast, bappend_toList]

theorem vecBytesFlat_toList_length {L : Usize} (self : pke.PkePublicKey L) :
    (vecBytesFlat self).toList.length = L.val * (32 * 10) := by
  simp only [Vector.toList_length]

/-- Prefix `[0, 32·10·ℓ)` of the serialized public key is the stored vector bytes. -/
theorem slice_pkStructBytes_left {L : Usize} (self : pke.PkePublicKey L)
    (p : Spec.Kopis.ParameterSet) (hℓ : Spec.Kopis.ℓ p = L.val)
    (h : 0 + 32 * 10 * Spec.Kopis.ℓ p ≤ Spec.Kopis.pkSize p) :
    Spec.slice (pkStructBytes self p hℓ) 0 (32 * 10 * Spec.Kopis.ℓ p) h
      = (vecBytesFlat self).cast (by rw [hℓ]; ring) := by
  apply Vector.toList_inj.mp
  rw [Vector.toList_cast, slice_toList, pkStructBytes_toList, List.drop_zero,
    show 32 * 10 * Spec.Kopis.ℓ p = (vecBytesFlat self).toList.length from by
      rw [vecBytesFlat_toList_length, hℓ]; ring,
    List.take_left]

/-- Suffix `[32·10·ℓ, +32)` of the serialized public key is the matrix seed. -/
theorem slice_pkStructBytes_right {L : Usize} (self : pke.PkePublicKey L)
    (p : Spec.Kopis.ParameterSet) (hℓ : Spec.Kopis.ℓ p = L.val)
    (h : 32 * 10 * Spec.Kopis.ℓ p + 32 ≤ Spec.Kopis.pkSize p) :
    Spec.slice (pkStructBytes self p hℓ) (32 * 10 * Spec.Kopis.ℓ p) 32 h
      = matSeedBytes self := by
  apply Vector.toList_inj.mp
  rw [slice_toList, pkStructBytes_toList,
    show 32 * 10 * Spec.Kopis.ℓ p = (vecBytesFlat self).toList.length from by
      rw [vecBytesFlat_toList_length, hℓ]; ring,
    List.drop_left]
  simp

/-- `GenMat` transported along a length cast. -/
theorem genMat_cast {ℓ ℓ' : ℕ} (h : ℓ = ℓ') (ms : 𝔹 32) :
    h ▸ Spec.Kopis.GenMat ℓ ms = Spec.Kopis.GenMat ℓ' ms := by cases h; rfl

/-- **`hpkvec` holds for a key-gen public key**: the stored vector bytes are the serialization
of what `vec_ntt` denotes (`hvb`), so deserializing them recovers it (roundtrip). -/
theorem keygen_hpkvec {L : Usize} (self : pke.PkePublicKey L) (V : Mat L 1#usize)
    (p : Spec.Kopis.ParameterSet) (hℓ : Spec.Kopis.ℓ p = L.val)
    (h : 0 + 32 * 10 * Spec.Kopis.ℓ p ≤ Spec.Kopis.pkSize p)
    (hvb : vecBytesFlat self
      = Spec.Kopis.PolyVector.serialize 10 (toVecN 10 V)) :
    toVecN 10 V
      = hℓ ▸ Spec.Kopis.PolyVector.deserialize 10
          (Spec.slice (pkStructBytes self p hℓ) 0 (32 * 10 * Spec.Kopis.ℓ p) h) := by
  rw [slice_pkStructBytes_left,
    deserialize_vec_toList_cast hℓ
      ((vecBytesFlat self).cast (by rw [hℓ]; ring))
      ((Spec.Kopis.PolyVector.serialize 10 (toVecN 10 V)).cast (by ring))
      (by rw [Vector.toList_cast, Vector.toList_cast, hvb]),
    polyVector_deserialize_serialize 10 (by omega)]

/-- **`hpkmat` holds for a key-gen public key** (`mat_a = GenMat(matrix_seed)`). -/
theorem keygen_hpkmat {L : Usize} (self : pke.PkePublicKey L) (Amat : Mat L L)
    (p : Spec.Kopis.ParameterSet) (hℓ : Spec.Kopis.ℓ p = L.val)
    (h : 32 * 10 * Spec.Kopis.ℓ p + 32 ≤ Spec.Kopis.pkSize p)
    (hmat : toMatrix13 Amat
      = Spec.Kopis.GenMat L.val (arrayToBytes self.matrix_seed)) :
    toMatrix13 Amat
      = hℓ ▸ Spec.Kopis.GenMat (Spec.Kopis.ℓ p)
          (Spec.slice (pkStructBytes self p hℓ) (32 * 10 * Spec.Kopis.ℓ p) 32 h) := by
  rw [slice_pkStructBytes_right, hmat, genMat_cast hℓ (matSeedBytes self)]
  congr 1

/-- **`hpkh` holds for a key-gen public key** (`hash = turboSHAKE256(pk)`). -/
theorem keygen_hpkh {L : Usize} (self : pke.PkePublicKey L) (hash_pke_pk : Array U8 32#usize)
    (p : Spec.Kopis.ParameterSet) (hℓ : Spec.Kopis.ℓ p = L.val) (sk_seed : 𝔹 32)
    (hh : arrayToBytes hash_pke_pk = (Spec.Kopis.ExpandDecapKey p sk_seed).2.2.2)
    (hpk : pkStructBytes self p hℓ = (Spec.Kopis.ExpandDecapKey p sk_seed).2.2.1) :
    arrayToBytes hash_pke_pk = turboSHAKE256 (pkStructBytes self p hℓ) DOMSEP_PKHASH 32 := by
  rw [hh, hpk]
  simp only [Spec.Kopis.ExpandDecapKey]

end Kopis.Properties
