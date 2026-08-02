/-
  # Kopis/Properties/KemFromBytes.lean — `KemPublicKey::from_bytes`, and parse-then-encapsulate.

  `pke_from_bytes_spec` (in `PkeFromBytes.lean`) shows the parser recovers the three
  values the spec reads out of a public key.  The public API wrapper additionally
  stores `PkePublicKey::hash` of the parsed key, and `pke_hash_spec` states that hash
  relative to the key's *own* re-serialization.  Relating it to the received bytes is
  exactly the `serialize ∘ deserialize = id` round-trip from `SerializeRoundtrip.lean`.

  With that in hand we get the theorem a user of the crate actually cares about:
  parse a public key off the wire, encapsulate to it, and the result is the spec's
  `KemEncap` applied to those very bytes.
-/
import Kopis.Properties.PkeFromBytes
import Kopis.Properties.SerializeRoundtrip
import Kopis.Properties.Impls
open Aeneas Aeneas.Std Result RustKopisSerial
open Spec (𝔹)
open scoped Spec.Notations
open Spec.TurboSHAKE (turboSHAKE256)
open Spec.Kopis (DOMSEP_PKHASH)

namespace Kopis.Properties

set_option maxHeartbeats 2000000
set_option maxRecDepth 16000

/-- **A parsed public key re-serializes to the bytes it came from.**  Given that the
struct's vector is the decoding of the input's prefix and its seed is the input's
suffix, the struct's abstract serialization `pkStructBytes` *is* the input.  This is
where the `serialize ∘ deserialize = id` round-trip is used. -/
theorem pkStructBytes_eq_of_parts {L : Usize} (pk : pke.PkePublicKey L)
    (p : Spec.Kopis.ParameterSet) (hℓ : Spec.Kopis.ℓ p = L.val)
    (pkB : 𝔹 (Spec.Kopis.pkSize p))
    (h1 : 0 + 32 * 10 * L.val ≤ Spec.Kopis.pkSize p)
    (h2 : 32 * 10 * L.val + 32 ≤ Spec.Kopis.pkSize p)
    (hvecbytes : vecBytesFlat pk = (Spec.slice pkB 0 (32 * 10 * L.val) h1).cast (by ring))
    (hseed : matSeedBytes pk = Spec.slice pkB (32 * 10 * L.val) 32 h2) :
    pkStructBytes pk p hℓ = pkB := by
  have hpk : Spec.Kopis.pkSize p = 320 * L.val + 32 := by
    simp only [Spec.Kopis.pkSize, hℓ]
  have hlenB : pkB.toList.length = 320 * L.val + 32 := by rw [Vector.toList_length, hpk]
  have hdrop : (pkB.toList.drop (32 * 10 * L.val)).take 32
      = pkB.toList.drop (32 * 10 * L.val) :=
    List.take_of_length_le (by rw [List.length_drop, hlenB]; omega)
  apply Vector.toList_inj.mp
  rw [pkStructBytes_toList, hvecbytes, hseed, Vector.toList_cast, slice_toList, slice_toList,
    List.drop_zero, hdrop]
  exact List.take_append_drop _ _

/-! ## Kopis-512 -/

/-- **Kopis-512 `KemPublicKey::from_bytes` matches the spec.**  Every field of the
parsed key is what the audited spec reads out of the received byte string — including
the cached hash, which is `turboSHAKE256` of those bytes. -/
theorem kopis512_kem_from_bytes_spec (bytes : Slice U8) (hlen : bytes.length = 672) :
    kem.KemPublicKey.from_bytes 2#usize bytes
      ⦃ (kpk : kem.KemPublicKey 2#usize) =>
          (∃ V : Mat 2#usize 1#usize, kpk.pke_pk.vec_ntt = nttFwdU V ∧
              toVecN 10 V
                = Spec.Kopis.PolyVector.deserialize 10
                    (Spec.slice (sliceToBytes bytes 672 hlen) 0
                      (32 * 10 * Spec.Kopis.ℓ .Kopis_512) (by decide)) ∧
              UniformBounded V) ∧
          (∃ Amat : Mat 2#usize 2#usize, kpk.pke_pk.mat_a_ntt = nttFwdU Amat ∧
              toMatrix13 Amat
                = Spec.Kopis.GenMat (Spec.Kopis.ℓ .Kopis_512)
                    (Spec.slice (sliceToBytes bytes 672 hlen)
                      (32 * 10 * Spec.Kopis.ℓ .Kopis_512) 32 (by decide)) ∧
              UniformBounded Amat) ∧
          arrayToBytes kpk.hash_pke_pk
            = turboSHAKE256 (sliceToBytes bytes 672 hlen) DOMSEP_PKHASH 32 ⦄ := by
  unfold kem.KemPublicKey.from_bytes
  let* ⟨ pke_pk, V, hvfwd, hvec, hvecbnd, hseed, Am, hmfwd, hmat, hmatbnd, hvecbytes ⟩ ←
    pke_from_bytes_spec (L := 2#usize) bytes
    (by rw [hlen]; rfl) (by scalar_tac)
  let* ⟨ h, hh ⟩ ← pke_hash_spec pke_pk (by scalar_tac) (by scalar_tac)
  -- the parsed key re-serializes to the input bytes
  have hpk : pkStructBytes pke_pk .Kopis_512 rfl = sliceToBytes bytes 672 hlen :=
    pkStructBytes_eq_of_parts pke_pk .Kopis_512 rfl (sliceToBytes bytes 672 hlen)
      (by decide) (by decide) hvecbytes hseed
  refine ⟨⟨V, hvfwd, hvec, hvecbnd⟩, ⟨Am, hmfwd, ?_, hmatbnd⟩, ?_⟩
  · exact hmat.trans (congrArg (Spec.Kopis.GenMat 2) hseed)
  · rw [hh]
    refine turboSHAKE256_congr _ _ _ _ ?_
    rw [← hpk, pkStructBytes_toList, bappend_toList]

/-- **Kopis-512: parse a received public key, then encapsulate to it.**  This is what a
user of the crate actually does with bytes off the wire, and the result is exactly the
spec's `KemEncap` applied to those bytes.  Nothing constrains the input, so a malformed
or adversarially chosen public key is covered too — the composite still cannot panic. -/
theorem kopis512_from_bytes_encap_spec (pk_bytes : Array U8 672#usize)
    (randomness : Array U8 32#usize) :
    (do let kpk ← impls.kopis512.Kopis512PublicKey.from_bytes pk_bytes
        impls.kopis512.Kopis512PublicKey.encapsulate_deterministic kpk randomness)
      ⦃ (r : Array U8 736#usize × impls.SharedSecret) =>
          arrayToBytes r.1 = (Spec.Kopis.KemEncap .Kopis_512 ((arrayToBytes randomness).cast rfl)
              ((arrayToBytes pk_bytes).cast rfl)).2
          ∧ arrayToBytes r.2 = (Spec.Kopis.KemEncap .Kopis_512 ((arrayToBytes randomness).cast rfl)
              ((arrayToBytes pk_bytes).cast rfl)).1 ⦄ := by
  unfold impls.kopis512.Kopis512PublicKey.from_bytes
  rw [show (lift pk_bytes.to_slice : Result (Slice U8)) = ok (Array.to_slice pk_bytes) from rfl,
    bind_tc_ok]
  set s := Array.to_slice pk_bytes with hsdef
  have hsval : s.val = pk_bytes.val := by rw [hsdef, Array.val_to_slice]
  have hslen : s.length = 672 := by
    simp only [hsdef, Slice.length, Array.val_to_slice]; exact pk_bytes.property
  clear_value s
  clear hsdef
  have hsb : sliceToBytes s 672 hslen = arrayToBytes pk_bytes :=
    (arrayToBytes_eq_sliceToBytes pk_bytes s hslen hsval.symm).symm
  let* ⟨ kpk, V, hVfwd, hpkvec, hpkvecbnd, Am, hAfwd, hpkmat, hpkmatbnd, hpkh ⟩ ←
    kopis512_kem_from_bytes_spec s hslen
  have hres := kopis512_encapsulate_deterministic_spec kpk randomness
    (sliceToBytes s 672 hslen) V Am hVfwd hAfwd hpkvec hpkvecbnd hpkmat hpkmatbnd hpkh
  rw [hsb] at hres
  exact hres

/-! ## Kopis-768 -/

/-- **Kopis-768 `KemPublicKey::from_bytes` matches the spec.**  Every field of the
parsed key is what the audited spec reads out of the received byte string — including
the cached hash, which is `turboSHAKE256` of those bytes. -/
theorem kopis768_kem_from_bytes_spec (bytes : Slice U8) (hlen : bytes.length = 992) :
    kem.KemPublicKey.from_bytes 3#usize bytes
      ⦃ (kpk : kem.KemPublicKey 3#usize) =>
          (∃ V : Mat 3#usize 1#usize, kpk.pke_pk.vec_ntt = nttFwdU V ∧
              toVecN 10 V
                = Spec.Kopis.PolyVector.deserialize 10
                    (Spec.slice (sliceToBytes bytes 992 hlen) 0
                      (32 * 10 * Spec.Kopis.ℓ .Kopis_768) (by decide)) ∧
              UniformBounded V) ∧
          (∃ Amat : Mat 3#usize 3#usize, kpk.pke_pk.mat_a_ntt = nttFwdU Amat ∧
              toMatrix13 Amat
                = Spec.Kopis.GenMat (Spec.Kopis.ℓ .Kopis_768)
                    (Spec.slice (sliceToBytes bytes 992 hlen)
                      (32 * 10 * Spec.Kopis.ℓ .Kopis_768) 32 (by decide)) ∧
              UniformBounded Amat) ∧
          arrayToBytes kpk.hash_pke_pk
            = turboSHAKE256 (sliceToBytes bytes 992 hlen) DOMSEP_PKHASH 32 ⦄ := by
  unfold kem.KemPublicKey.from_bytes
  let* ⟨ pke_pk, V, hvfwd, hvec, hvecbnd, hseed, Am, hmfwd, hmat, hmatbnd, hvecbytes ⟩ ←
    pke_from_bytes_spec (L := 3#usize) bytes
    (by rw [hlen]; rfl) (by scalar_tac)
  let* ⟨ h, hh ⟩ ← pke_hash_spec pke_pk (by scalar_tac) (by scalar_tac)
  -- the parsed key re-serializes to the input bytes
  have hpk : pkStructBytes pke_pk .Kopis_768 rfl = sliceToBytes bytes 992 hlen :=
    pkStructBytes_eq_of_parts pke_pk .Kopis_768 rfl (sliceToBytes bytes 992 hlen)
      (by decide) (by decide) hvecbytes hseed
  refine ⟨⟨V, hvfwd, hvec, hvecbnd⟩, ⟨Am, hmfwd, ?_, hmatbnd⟩, ?_⟩
  · exact hmat.trans (congrArg (Spec.Kopis.GenMat 3) hseed)
  · rw [hh]
    refine turboSHAKE256_congr _ _ _ _ ?_
    rw [← hpk, pkStructBytes_toList, bappend_toList]

/-- **Kopis-768: parse a received public key, then encapsulate to it.**  This is what a
user of the crate actually does with bytes off the wire, and the result is exactly the
spec's `KemEncap` applied to those bytes.  Nothing constrains the input, so a malformed
or adversarially chosen public key is covered too — the composite still cannot panic. -/
theorem kopis768_from_bytes_encap_spec (pk_bytes : Array U8 992#usize)
    (randomness : Array U8 32#usize) :
    (do let kpk ← impls.kopis768.Kopis768PublicKey.from_bytes pk_bytes
        impls.kopis768.Kopis768PublicKey.encapsulate_deterministic kpk randomness)
      ⦃ (r : Array U8 1088#usize × impls.SharedSecret) =>
          arrayToBytes r.1 = (Spec.Kopis.KemEncap .Kopis_768 ((arrayToBytes randomness).cast rfl)
              ((arrayToBytes pk_bytes).cast rfl)).2
          ∧ arrayToBytes r.2 = (Spec.Kopis.KemEncap .Kopis_768 ((arrayToBytes randomness).cast rfl)
              ((arrayToBytes pk_bytes).cast rfl)).1 ⦄ := by
  unfold impls.kopis768.Kopis768PublicKey.from_bytes
  rw [show (lift pk_bytes.to_slice : Result (Slice U8)) = ok (Array.to_slice pk_bytes) from rfl,
    bind_tc_ok]
  set s := Array.to_slice pk_bytes with hsdef
  have hsval : s.val = pk_bytes.val := by rw [hsdef, Array.val_to_slice]
  have hslen : s.length = 992 := by
    simp only [hsdef, Slice.length, Array.val_to_slice]; exact pk_bytes.property
  clear_value s
  clear hsdef
  have hsb : sliceToBytes s 992 hslen = arrayToBytes pk_bytes :=
    (arrayToBytes_eq_sliceToBytes pk_bytes s hslen hsval.symm).symm
  let* ⟨ kpk, V, hVfwd, hpkvec, hpkvecbnd, Am, hAfwd, hpkmat, hpkmatbnd, hpkh ⟩ ←
    kopis768_kem_from_bytes_spec s hslen
  have hres := kopis768_encapsulate_deterministic_spec kpk randomness
    (sliceToBytes s 992 hslen) V Am hVfwd hAfwd hpkvec hpkvecbnd hpkmat hpkmatbnd hpkh
  rw [hsb] at hres
  exact hres

/-! ## Kopis-1024 -/

/-- **Kopis-1024 `KemPublicKey::from_bytes` matches the spec.**  Every field of the
parsed key is what the audited spec reads out of the received byte string — including
the cached hash, which is `turboSHAKE256` of those bytes. -/
theorem kopis1024_kem_from_bytes_spec (bytes : Slice U8) (hlen : bytes.length = 1312) :
    kem.KemPublicKey.from_bytes 4#usize bytes
      ⦃ (kpk : kem.KemPublicKey 4#usize) =>
          (∃ V : Mat 4#usize 1#usize, kpk.pke_pk.vec_ntt = nttFwdU V ∧
              toVecN 10 V
                = Spec.Kopis.PolyVector.deserialize 10
                    (Spec.slice (sliceToBytes bytes 1312 hlen) 0
                      (32 * 10 * Spec.Kopis.ℓ .Kopis_1024) (by decide)) ∧
              UniformBounded V) ∧
          (∃ Amat : Mat 4#usize 4#usize, kpk.pke_pk.mat_a_ntt = nttFwdU Amat ∧
              toMatrix13 Amat
                = Spec.Kopis.GenMat (Spec.Kopis.ℓ .Kopis_1024)
                    (Spec.slice (sliceToBytes bytes 1312 hlen)
                      (32 * 10 * Spec.Kopis.ℓ .Kopis_1024) 32 (by decide)) ∧
              UniformBounded Amat) ∧
          arrayToBytes kpk.hash_pke_pk
            = turboSHAKE256 (sliceToBytes bytes 1312 hlen) DOMSEP_PKHASH 32 ⦄ := by
  unfold kem.KemPublicKey.from_bytes
  let* ⟨ pke_pk, V, hvfwd, hvec, hvecbnd, hseed, Am, hmfwd, hmat, hmatbnd, hvecbytes ⟩ ←
    pke_from_bytes_spec (L := 4#usize) bytes
    (by rw [hlen]; rfl) (by scalar_tac)
  let* ⟨ h, hh ⟩ ← pke_hash_spec pke_pk (by scalar_tac) (by scalar_tac)
  -- the parsed key re-serializes to the input bytes
  have hpk : pkStructBytes pke_pk .Kopis_1024 rfl = sliceToBytes bytes 1312 hlen :=
    pkStructBytes_eq_of_parts pke_pk .Kopis_1024 rfl (sliceToBytes bytes 1312 hlen)
      (by decide) (by decide) hvecbytes hseed
  refine ⟨⟨V, hvfwd, hvec, hvecbnd⟩, ⟨Am, hmfwd, ?_, hmatbnd⟩, ?_⟩
  · exact hmat.trans (congrArg (Spec.Kopis.GenMat 4) hseed)
  · rw [hh]
    refine turboSHAKE256_congr _ _ _ _ ?_
    rw [← hpk, pkStructBytes_toList, bappend_toList]

/-- **Kopis-1024: parse a received public key, then encapsulate to it.**  This is what a
user of the crate actually does with bytes off the wire, and the result is exactly the
spec's `KemEncap` applied to those bytes.  Nothing constrains the input, so a malformed
or adversarially chosen public key is covered too — the composite still cannot panic. -/
theorem kopis1024_from_bytes_encap_spec (pk_bytes : Array U8 1312#usize)
    (randomness : Array U8 32#usize) :
    (do let kpk ← impls.kopis1024.Kopis1024PublicKey.from_bytes pk_bytes
        impls.kopis1024.Kopis1024PublicKey.encapsulate_deterministic kpk randomness)
      ⦃ (r : Array U8 1472#usize × impls.SharedSecret) =>
          arrayToBytes r.1 = (Spec.Kopis.KemEncap .Kopis_1024 ((arrayToBytes randomness).cast rfl)
              ((arrayToBytes pk_bytes).cast rfl)).2
          ∧ arrayToBytes r.2 = (Spec.Kopis.KemEncap .Kopis_1024 ((arrayToBytes randomness).cast rfl)
              ((arrayToBytes pk_bytes).cast rfl)).1 ⦄ := by
  unfold impls.kopis1024.Kopis1024PublicKey.from_bytes
  rw [show (lift pk_bytes.to_slice : Result (Slice U8)) = ok (Array.to_slice pk_bytes) from rfl,
    bind_tc_ok]
  set s := Array.to_slice pk_bytes with hsdef
  have hsval : s.val = pk_bytes.val := by rw [hsdef, Array.val_to_slice]
  have hslen : s.length = 1312 := by
    simp only [hsdef, Slice.length, Array.val_to_slice]; exact pk_bytes.property
  clear_value s
  clear hsdef
  have hsb : sliceToBytes s 1312 hslen = arrayToBytes pk_bytes :=
    (arrayToBytes_eq_sliceToBytes pk_bytes s hslen hsval.symm).symm
  let* ⟨ kpk, V, hVfwd, hpkvec, hpkvecbnd, Am, hAfwd, hpkmat, hpkmatbnd, hpkh ⟩ ←
    kopis1024_kem_from_bytes_spec s hslen
  have hres := kopis1024_encapsulate_deterministic_spec kpk randomness
    (sliceToBytes s 1312 hslen) V Am hVfwd hAfwd hpkvec hpkvecbnd hpkmat hpkmatbnd hpkh
  rw [hsb] at hres
  exact hres

end Kopis.Properties
