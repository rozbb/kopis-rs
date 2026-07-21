import Kopis.Properties.KemEncap
import Kopis.Properties.PkeDecryptTop
import Kopis.Properties.Hash
import Kopis.Properties.SubtleModel
open Aeneas Aeneas.Std Result kopis_kem
open Spec (𝔹)
open scoped Spec.Notations
open Spec.TurboSHAKE (turboSHAKE256)
open Spec.Kopis (DOMSEP_FO DOMSEP_PKHASH DOMSEP_NOREJECT)
namespace Kopis.Properties
set_option maxHeartbeats 10000000
set_option maxRecDepth 8000

/-- `6#u8` bit-vector is the implicit-rejection domain separator. -/
theorem domsep_noreject_bv : (6#u8).bv = DOMSEP_NOREJECT := by decide

/-- Byte-concat bridge for the reject hash: an array `A` followed by a slice `b`. -/
theorem turboSHAKE256_array_slice_concat (A : Array U8 32#usize) (b : Slice U8)
    (D : Byte) (N n : ℕ) (hb : b.length = n) :
    turboSHAKE256 (u8ListToBytes (A.val ++ b.val)) D N
      = turboSHAKE256 (arrayToBytes A ‖ sliceToBytes b n hb) D N := by
  refine turboSHAKE256_congr _ _ _ _ ?_
  have e1 : (u8ListToBytes (A.val ++ b.val)).toList = (A.val ++ b.val).map (·.bv) := by
    simp only [u8ListToBytes, Vector.toList_ofFn]; rw [List.ofFn_getElem_eq_map]
  rw [e1, bappend_toList, arrayToBytes_toList, sliceToBytes_toList, List.map_append]

/-- **Rust `kem.decap` matches the spec `KemDecap`.** -/
theorem decap_spec {L : Usize} (MU T : Usize) (sk : kem.KemSecretKey L)
    (ciphertext : Slice U8) (p : Spec.Kopis.ParameterSet) (sk_seed : 𝔹 32)
    (pk_bytes : 𝔹 (Spec.Kopis.pkSize p))
    (hℓ : Spec.Kopis.ℓ p = L.val) (hμ : Spec.Kopis.μ p = MU.val) (ht : Spec.Kopis.t p = T.val)
    (hMU : MU.val = 6 ∨ MU.val = 8 ∨ MU.val = 10) (hT : 3 ≤ T.val ∧ T.val ≤ 6)
    (hfit : L.val * 10 * 256 ≤ Usize.max) (hbuf : Spec.Kopis.ctSize p ≤ 1472)
    (hlenct : ciphertext.length = Spec.Kopis.ctSize p)
    (hsk : toVector13 sk.pke_sk = hℓ ▸ (Spec.Kopis.ExpandDecapKey p sk_seed).1)
    (hz : arrayToBytes sk.z = (Spec.Kopis.ExpandDecapKey p sk_seed).2.1)
    (hpk : pk_bytes = (Spec.Kopis.ExpandDecapKey p sk_seed).2.2.1)
    (hpkvec : toVecN 10 sk.pke_pk.vec
      = hℓ ▸ Spec.Kopis.PolyVector.deserialize 10
          (Spec.slice pk_bytes 0 (32 * 10 * Spec.Kopis.ℓ p) (by simp [Spec.Kopis.pkSize])))
    (hpkmat : toMatrix13 sk.pke_pk.mat_a
      = hℓ ▸ Spec.Kopis.GenMat (Spec.Kopis.ℓ p)
          (Spec.slice pk_bytes (32 * 10 * Spec.Kopis.ℓ p) 32 (by simp [Spec.Kopis.pkSize])))
    (hpkh : arrayToBytes sk.hash_pke_pk = turboSHAKE256 pk_bytes DOMSEP_PKHASH 32) :
    kem.decap MU T sk ciphertext
      ⦃ (r : Array U8 32#usize) =>
          arrayToBytes r
            = Spec.Kopis.KemDecap p sk_seed (sliceToBytes ciphertext (Spec.Kopis.ctSize p) hlenct) ⦄ := by
  unfold kem.decap
  have hct : Spec.Kopis.ctSize p = L.val * 320 + T.val * 32 := by
    simp only [Spec.Kopis.ctSize, hℓ, ht]; ring
  simp only [pke.ciphertext_len, consts.MODULUS_P_BITS, consts.RING_DEG]
  let* ⟨n0, hn0⟩ ← Std.Usize.mul_spec (x := L) (y := 10#usize) (by scalar_tac)
  let* ⟨n1, hn1⟩ ← Std.Usize.mul_spec (x := n0) (y := 256#usize) (by rw [hn0]; scalar_tac)
  let* ⟨n2, hn2⟩ ← Std.Usize.div_spec
  let* ⟨n3, hn3⟩ ← Std.Usize.mul_spec (x := T) (y := 256#usize) (by scalar_tac)
  let* ⟨n4, hn4⟩ ← Std.Usize.div_spec
  let* ⟨right_val, hrv⟩ ← Std.Usize.add_spec (x := n2) (y := n4)
    (by rw [hn2, hn1, hn0, hn4, hn3]; rw [hct] at hlenct; scalar_tac)
  have hrvv : right_val.val = Spec.Kopis.ctSize p := by
    rw [hrv, hn2, hn1, hn0, hn4, hn3, hct]; omega
  rw [show massert (ciphertext.len = right_val) = ok () from by
    have hlv : ciphertext.len = right_val :=
      UScalar.eq_of_val_eq (by rw [Slice.len_val, hrvv]; exact hlenct)
    simp only [massert, if_pos hlv], bind_tc_ok]
  -- PkeDecrypt
  let* ⟨randomness, hrand⟩ ← decrypt_spec T sk.pke_sk ciphertext p sk_seed hℓ ht hT hfit hlenct hsk
  -- FO XOF: k / rprime windows from the 64-byte squeeze
  step*
  have habs : hasherAbsorbed hasher2 = randomness.val ++ sk.hash_pke_pk.val := by
    rw [hasher2_post, hasher1_post, hasher_post, s_post, s1_post]; simp [Array.to_slice]
  have hrm0 : readerModel xof = (5#u8, randomness.val ++ sk.hash_pke_pk.val) := by
    rw [xof_post1, habs]
  have hrm1 : readerModel xof1 = (5#u8, randomness.val ++ sk.hash_pke_pk.val) := by
    rw [xof1_post4, hrm0]
  have hs2len : s2.length = 32 := by
    rw [Slice.length, s2_post1]; simpa using (Array.repeat 32#usize 0#u8).property
  have hs4len : s4.length = 32 := by
    rw [Slice.length, s4_post1]; simpa using (Array.repeat 32#usize 0#u8).property
  have hoff1 : readerOffset xof1 = 32 := by rw [xof1_post3, xof_post2, hs2len]
  set b := turboSHAKE256 (arrayToBytes randomness ‖ arrayToBytes sk.hash_pke_pk) DOMSEP_FO 64 with hb
  have hkbytes : s3.val.map (·.bv) = (Spec.slice b 0 32 (by omega)).toList := by
    rw [xof1_post2, hrm0, xof_post2, hs2len]
    dsimp only
    simp only [domsep_fo_bv]
    rw [turboSHAKE256_two_array_concat, turboSHAKE256_read_window_gen _ _ 0 64 (by omega)]
  have hrbytes : s5.val.map (·.bv) = (Spec.slice b 32 32 (by omega)).toList := by
    rw [__post2, hrm1, hoff1, hs4len]
    dsimp only
    simp only [domsep_fo_bv]
    rw [turboSHAKE256_two_array_concat, turboSHAKE256_read_window_gen _ _ 32 64 (by omega)]
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
  -- reconstructed ciphertext buffer (handled by step*)
  have hrclen : reconstructed_ct.length = Spec.Kopis.ctSize p := by
    rw [reconstructed_ct_post2, hrvv]
  -- re-encrypt with (msg = randomness, coins = rprime)
  let* ⟨reconstructed_ct1, hrc1len, hrc1eq⟩ ← encrypt_deterministic_spec MU T sk.pke_pk randomness
    (to_slice_mut_back1 s5) reconstructed_ct p hℓ hμ ht hMU ⟨by omega, by omega⟩ hfit hrclen
    pk_bytes hpkvec hpkmat
  -- reject hash  turboSHAKE256 (z ‖ c) DOMSEP_NOREJECT 32
  rw [show (lift (Array.to_slice sk.z) : Result (Slice U8)) = ok (Array.to_slice sk.z) from rfl,
    bind_tc_ok]
  let* ⟨reject_val, hreject⟩ ← turboshake256_hash_spec 6#u8 (Array.to_slice sk.z) ciphertext
  -- constant-time compare + select
  let* ⟨matched, hmatched⟩ ← ct_eq_slice_u8_spec reconstructed_ct1 ciphertext
  let* ⟨out, hout⟩ ← conditional_select_array_u8_spec reject_val (to_slice_mut_back s3) matched
  -- === final assembly ===
  -- structural fact: `pkh` component is the hash of the `pk` component
  have hpkh_rel : (Spec.Kopis.ExpandDecapKey p sk_seed).2.2.2
      = turboSHAKE256 (Spec.Kopis.ExpandDecapKey p sk_seed).2.2.1 DOMSEP_PKHASH 32 := by
    simp only [Spec.Kopis.ExpandDecapKey]
  have hpkh2 : (Spec.Kopis.ExpandDecapKey p sk_seed).2.2.2 = arrayToBytes sk.hash_pke_pk := by
    rw [hpkh_rel, ← hpk, ← hpkh]
  -- `b` matches the spec's `turboSHAKE256 (randomness ‖ pkh)` (bridged at the list level to
  -- avoid the `𝔹 32` vs `𝔹 ↑32#usize` size-index mismatch)
  have hbspec : b = turboSHAKE256
      (Spec.Kopis.PkeDecrypt p sk_seed (sliceToBytes ciphertext (Spec.Kopis.ctSize p) hlenct)
        ‖ (Spec.Kopis.ExpandDecapKey p sk_seed).2.2.2) DOMSEP_FO 64 := by
    rw [hb]
    refine turboSHAKE256_congr _ _ _ _ ?_
    rw [bappend_toList, bappend_toList, congrArg Vector.toList hrand]
    exact congrArg (Vector.toList _ ++ ·) (congrArg Vector.toList hpkh2.symm)
  -- `cprime = sliceToBytes reconstructed_ct1`
  have hcprime : Spec.Kopis.PkeEncrypt p (Spec.slice b 32 32 (by omega)) pk_bytes
        (arrayToBytes randomness)
      = sliceToBytes reconstructed_ct1 (Spec.Kopis.ctSize p) hrc1len := by
    rw [← hr1bytes]; exact hrc1eq.symm
  -- transform the Rust result into an `ite` over a `Prop`
  rw [hout, hmatched, apply_ite (f := fun a => arrayToBytes a), hk1bytes, hreject]
  simp only [decide_eq_true_eq]
  -- reduce the spec side, then match branch-by-branch
  simp only [Spec.Kopis.KemDecap]
  refine if_congr ?_ ?_ ?_
  · -- condition
    rw [← hbspec, ← hpk, ← hrand, hcprime,
      sliceToBytes_inj ciphertext reconstructed_ct1 (Spec.Kopis.ctSize p) hlenct hrc1len]
    exact eq_comm
  · -- accept branch:  slice b 0 32
    rw [← hbspec]
  · -- reject branch
    rw [Array.val_to_slice,
      turboSHAKE256_array_slice_concat sk.z ciphertext (6#u8).bv 32 (Spec.Kopis.ctSize p) hlenct,
      domsep_noreject_bv, hz]
    rfl

end Kopis.Properties
