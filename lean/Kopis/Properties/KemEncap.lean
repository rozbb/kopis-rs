import Kopis.Properties.PkeEncryptTop
open Aeneas Aeneas.Std Result kopis_kem
open Spec (𝔹)
open scoped Spec.Notations
open Spec.TurboSHAKE (turboSHAKE256 turboSHAKE256_getElem_prefix)
open Spec.Kopis (DOMSEP_FO DOMSEP_PKHASH)
namespace Kopis.Properties
set_option maxHeartbeats 2000000
set_option maxRecDepth 4000

/-- Generalisation of `drop_toList_eq_slice` to an arbitrary squeeze length `tot`. -/
theorem drop_toList_eq_slice_gen (off tot : ℕ) (A : 𝔹 (off + 32)) (B : 𝔹 tot)
    (h : off + 32 ≤ tot)
    (hkey : ∀ k, (hk : k < 32) → A[off + k]'(by omega) = B[off + k]'(by omega)) :
    A.toList.drop off = (Spec.slice B off 32 h).toList := by
  apply List.ext_getElem
  · simp only [List.length_drop, Vector.toList_length, Spec.slice]; omega
  · intro k h1 h2
    have hk : k < 32 := by simpa [Spec.slice] using h2
    rw [List.getElem_drop, Vector.getElem_toList, Vector.getElem_toList, slice_getElem]
    exact hkey k hk

/-- A `read` window of the XOF stream at byte-offset `off` (length 32) equals the spec's
`slice … off 32` of the length-`tot` squeeze (XOF prefix/streaming property). -/
theorem turboSHAKE256_read_window_gen {n : ℕ} (msg : 𝔹 n) (D : Byte) (off tot : ℕ)
    (h : off + 32 ≤ tot) :
    (turboSHAKE256 msg D (off + 32)).toList.drop off
      = (Spec.slice (turboSHAKE256 msg D tot) off 32 h).toList :=
  drop_toList_eq_slice_gen off tot (turboSHAKE256 msg D (off + 32)) (turboSHAKE256 msg D tot) h
    (fun k hk => turboSHAKE256_getElem_prefix msg D (off + 32) tot (off + k) (by omega) (by omega))

/-- `5#u8` bit-vector is the Fujisaki–Okamoto domain separator. -/
theorem domsep_fo_bv : (5#u8).bv = DOMSEP_FO := by decide

/-- Byte-concat bridge: the Rust absorb of two 32-byte arrays `A ++ B` interprets as the
spec's `arrayToBytes A ‖ arrayToBytes B`. -/
theorem turboSHAKE256_two_array_concat (A B : Array U8 32#usize) (D : Byte) (N : ℕ) :
    turboSHAKE256 (u8ListToBytes (A.val ++ B.val)) D N
      = turboSHAKE256 (arrayToBytes A ‖ arrayToBytes B) D N := by
  refine turboSHAKE256_congr _ _ _ _ ?_
  have e1 : (u8ListToBytes (A.val ++ B.val)).toList = (A.val ++ B.val).map (·.bv) := by
    simp only [u8ListToBytes, Vector.toList_ofFn]; rw [List.ofFn_getElem_eq_map]
  rw [e1, bappend_toList, arrayToBytes_toList, arrayToBytes_toList, List.map_append]

/-- **Rust `kem.encap_deterministic` matches the spec `KemEncap`.** -/
theorem encap_deterministic_spec {L : Usize} (MU T : Usize)
    (randomness : Array U8 32#usize) (kem_pk : kem.KemPublicKey L) (out_buf : Slice U8)
    (p : Spec.Kopis.ParameterSet) (pk_bytes : 𝔹 (Spec.Kopis.pkSize p))
    (hℓ : Spec.Kopis.ℓ p = L.val) (hμ : Spec.Kopis.μ p = MU.val) (ht : Spec.Kopis.t p = T.val)
    (hMU : MU.val = 6 ∨ MU.val = 8 ∨ MU.val = 10) (hT : 1 ≤ T.val ∧ T.val ≤ 10)
    (hfit : L.val * 10 * 256 ≤ Usize.max)
    (hlenout : out_buf.length = Spec.Kopis.ctSize p)
    (hpkvec : toVecN 10 kem_pk.pke_pk.vec
      = hℓ ▸ Spec.Kopis.PolyVector.deserialize 10
          (Spec.slice pk_bytes 0 (32 * 10 * Spec.Kopis.ℓ p) (by simp [Spec.Kopis.pkSize])))
    (hpkmat : toMatrix13 kem_pk.pke_pk.mat_a
      = hℓ ▸ Spec.Kopis.GenMat (Spec.Kopis.ℓ p)
          (Spec.slice pk_bytes (32 * 10 * Spec.Kopis.ℓ p) 32 (by simp [Spec.Kopis.pkSize])))
    (hpkh : arrayToBytes kem_pk.hash_pke_pk = turboSHAKE256 pk_bytes DOMSEP_PKHASH 32) :
    kem.encap_deterministic MU T randomness kem_pk out_buf
      ⦃ (r : Array U8 32#usize × Slice U8) =>
          arrayToBytes r.1
            = (Spec.Kopis.KemEncap p ((arrayToBytes randomness).cast rfl) pk_bytes).1
          ∧ ∃ h : r.2.length = Spec.Kopis.ctSize p,
              sliceToBytes r.2 (Spec.Kopis.ctSize p) h
                = (Spec.Kopis.KemEncap p ((arrayToBytes randomness).cast rfl) pk_bytes).2 ⦄ := by
  unfold kem.encap_deterministic
  step*
  -- absorbed message = randomness ++ hash_pke_pk
  have habs : hasherAbsorbed hasher2 = randomness.val ++ kem_pk.hash_pke_pk.val := by
    rw [hasher2_post, hasher1_post, hasher_post, s_post, s1_post]
    simp [Array.to_slice]
  have hrm0 : readerModel xof = (5#u8, randomness.val ++ kem_pk.hash_pke_pk.val) := by
    rw [xof_post1, habs]
  have hrm1 : readerModel xof1 = (5#u8, randomness.val ++ kem_pk.hash_pke_pk.val) := by
    rw [xof1_post4, hrm0]
  -- offsets
  have hs2len : s2.length = 32 := by
    rw [Slice.length, s2_post1]; simpa using (Array.repeat 32#usize 0#u8).property
  have hs4len : s4.length = 32 := by
    rw [Slice.length, s4_post1]; simpa using (Array.repeat 32#usize 0#u8).property
  have hoff1 : readerOffset xof1 = 32 := by rw [xof1_post3, xof_post2, hs2len]
  -- the 64-byte FO squeeze
  set b := turboSHAKE256 (arrayToBytes randomness ‖ arrayToBytes kem_pk.hash_pke_pk)
      DOMSEP_FO 64 with hb
  -- k window
  have hkbytes : s3.val.map (·.bv) = (Spec.slice b 0 32 (by omega)).toList := by
    rw [xof1_post2, hrm0, xof_post2, hs2len]
    dsimp only
    simp only [domsep_fo_bv]
    rw [turboSHAKE256_two_array_concat, turboSHAKE256_read_window_gen _ _ 0 64 (by omega)]
  -- r window
  have hrbytes : s5.val.map (·.bv) = (Spec.slice b 32 32 (by omega)).toList := by
    rw [__post2, hrm1, hoff1, hs4len]
    dsimp only
    simp only [domsep_fo_bv]
    rw [turboSHAKE256_two_array_concat, turboSHAKE256_read_window_gen _ _ 32 64 (by omega)]
  -- reconstructed arrays carry the k / r window bytes
  have e32 : ((32#usize : Usize).val : ℕ) = 32 := rfl
  have hs3len : s3.length = 32 := by rw [xof1_post1, hs2len]
  have hs5len : s5.length = 32 := by rw [__post1, hs4len]
  have hk1val : (to_slice_mut_back s3).val = s3.val := by
    rw [s2_post2]; exact Array.from_slice_val _ s3 (by rw [← Slice.length, hs3len]; exact e32.symm)
  have hr1val : (to_slice_mut_back1 s5).val = s5.val := by
    rw [s4_post2]; exact Array.from_slice_val _ s5 (by rw [← Slice.length, hs5len]; exact e32.symm)
  have hk1bytes : arrayToBytes (to_slice_mut_back s3) = Spec.slice b 0 32 (by omega) := by
    apply Vector.toList_inj.mp; rw [arrayToBytes_toList, hk1val]; exact hkbytes
  have hr1bytes : arrayToBytes (to_slice_mut_back1 s5) = Spec.slice b 32 32 (by omega) := by
    apply Vector.toList_inj.mp; rw [arrayToBytes_toList, hr1val]; exact hrbytes
  -- run the PKE encryption on (msg = randomness, coins = r1)
  let* ⟨out_buf1, hlen1, hct1⟩ ← encrypt_deterministic_spec MU T kem_pk.pke_pk randomness
    (to_slice_mut_back1 s5) out_buf p hℓ hμ ht hMU hT hfit hlenout pk_bytes hpkvec hpkmat
  -- the FO squeeze matches the spec's `b = turboSHAKE256 (randomness ‖ pkh)`
  have hbspec : b = turboSHAKE256 (((arrayToBytes randomness).cast rfl)
      ‖ turboSHAKE256 pk_bytes DOMSEP_PKHASH 32) DOMSEP_FO 64 := by
    rw [hb]
    refine turboSHAKE256_congr _ _ _ _ ?_
    rw [bappend_toList, bappend_toList, Vector.toList_cast]
    exact congrArg (Vector.toList (arrayToBytes randomness) ++ ·) (congrArg Vector.toList hpkh)
  -- assemble the KemEncap postcondition
  simp only [Spec.Kopis.KemEncap]
  refine ⟨?_, hlen1, ?_⟩
  · rw [hk1bytes, hbspec]; rfl
  · rw [hct1, hr1bytes, hbspec]; rfl
