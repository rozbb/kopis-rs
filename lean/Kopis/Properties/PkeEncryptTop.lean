import Kopis.Properties.RoundRt
import Kopis.Properties.ProdBridgeNT
import Kopis.Properties.InnerProduct
import Kopis.Properties.EncryptGlue
import Kopis.Properties.DeserializeMsg
import Kopis.Properties.MatrixMul
import Kopis.Properties.MatrixSerialize
import Kopis.Properties.SerializeTop
import Kopis.Properties.RingArith
import Kopis.Properties.MulTranspose
import Kopis.Properties.GenSecretTop
import Kopis.Properties.ExpandDecap
open Aeneas Aeneas.Std Result RustKopis
open Spec (𝔹)
open scoped Spec.Notations
namespace Kopis.Properties
set_option maxHeartbeats 10000000
set_option maxRecDepth 8000

theorem roundR10_mvm_cast {ℓ ℓ' : ℕ} (h : ℓ = ℓ') (A : Spec.Kopis.PolyMatrix (2 ^ 13) ℓ)
    (v : Spec.Kopis.PolyVector (2 ^ 13) ℓ) :
    h ▸ Spec.Kopis.RoundToR10 ℓ (Spec.Kopis.matVecMul A v)
      = Spec.Kopis.RoundToR10 ℓ' (Spec.Kopis.matVecMul (h ▸ A) (h ▸ v)) := by cases h; rfl

theorem genSecret_cast {ℓ ℓ' : ℕ} (h : ℓ = ℓ') (μ : ℕ) (ss : 𝔹 32) :
    h ▸ Spec.Kopis.GenSecret ℓ μ ss = Spec.Kopis.GenSecret ℓ' μ ss := by cases h; rfl

/-- **Rust `encrypt_deterministic` matches the spec `PkeEncrypt`.** -/
theorem encrypt_deterministic_spec {L : Usize} (MU T : Usize)
    (pk : pke.PkePublicKey L) (msg coins : Array U8 32#usize) (out_buf : Slice U8)
    (p : Spec.Kopis.ParameterSet)
    (hℓ : Spec.Kopis.ℓ p = L.val) (hμ : Spec.Kopis.μ p = MU.val) (ht : Spec.Kopis.t p = T.val)
    (hMU : MU.val = 6 ∨ MU.val = 8 ∨ MU.val = 10)
    (hT : 1 ≤ T.val ∧ T.val ≤ 10)
    (hfit : L.val * 10 * 256 ≤ Usize.max)
    (hlenout : out_buf.length = Spec.Kopis.ctSize p)
    (pk_bytes : 𝔹 (Spec.Kopis.pkSize p))
    (hpkvec : toVecN 10 (nttInvU pk.vec_ntt)
      = hℓ ▸ Spec.Kopis.PolyVector.deserialize 10 (Spec.slice pk_bytes 0 (32 * 10 * Spec.Kopis.ℓ p) (by simp [Spec.Kopis.pkSize])))
    (hpkvecbnd : UniformBounded (nttInvU pk.vec_ntt))
    (hpkmat : toMatrix13 (nttInvU pk.mat_a_ntt)
      = hℓ ▸ Spec.Kopis.GenMat (Spec.Kopis.ℓ p) (Spec.slice pk_bytes (32 * 10 * Spec.Kopis.ℓ p) 32 (by simp [Spec.Kopis.pkSize])))
    (hpkmatbnd : UniformBounded (nttInvU pk.mat_a_ntt)) :
    pke.encrypt_deterministic MU T pk msg coins out_buf
      ⦃ (r : Slice U8) => ∃ h : r.length = Spec.Kopis.ctSize p,
          sliceToBytes r (Spec.Kopis.ctSize p) h
            = Spec.Kopis.PkeEncrypt p (arrayToBytes coins) pk_bytes
                ((arrayToBytes msg).cast rfl) ⦄ := by
  unfold pke.encrypt_deterministic
  have hct : Spec.Kopis.ctSize p = L.val * 320 + T.val * 32 := by
    simp only [Spec.Kopis.ctSize, hℓ, ht]; ring
  have hb2560 : L.val * 10 * 256 = L.val * 2560 := by ring
  have hlenmax : out_buf.length ≤ Usize.max := by have := out_buf.property; simpa [Slice.length] using this
  simp only [pke.ciphertext_len, consts.MODULUS_P_BITS, consts.RING_DEG]
  -- evaluate ciphertext_len = L*320 + T*32
  let* ⟨n0, hn0⟩ ← Std.Usize.mul_spec (x := L) (y := 10#usize) (by scalar_tac)
  let* ⟨n1, hn1⟩ ← Std.Usize.mul_spec (x := n0) (y := 256#usize) (by rw [hn0]; scalar_tac)
  let* ⟨n2, hn2⟩ ← Std.Usize.div_spec
  let* ⟨n3, hn3⟩ ← Std.Usize.mul_spec (x := T) (y := 256#usize) (by scalar_tac)
  let* ⟨n4, hn4⟩ ← Std.Usize.div_spec
  let* ⟨rv, hrv⟩ ← Std.Usize.add_spec (x := n2) (y := n4)
    (by rw [hn2, hn1, hn0, hn4, hn3]; rw [hct] at hlenout; scalar_tac)
  rw [show massert (out_buf.len = rv) = ok () from by
    have hlv : out_buf.len = rv := by
      apply Std.UScalar.eq_of_val_eq
      rw [hct] at hlenout
      rw [hrv, hn2, hn1, hn0, hn4, hn3]
      show out_buf.length = _
      omega
    simp only [massert, if_pos hlv], bind_tc_ok]
  let* ⟨vec_sprime, hvecs, hspbnd⟩ ← spec_and (gen_secret_from_seed_spec L MU coins hMU)
    (gen_secret_secretBounded coins hMU)
  let* ⟨sprime_ntt, hspntt⟩ ← from_secret_matrix_spec vec_sprime
  have hfitex : fitsExactly L.val ((MU.val / 2 : ℕ) : ℤ) := by
    have h := fitsExactly_paramSet p; rw [hℓ, hμ] at h; exact h
  let* ⟨prod, hprod0⟩ ← ntt_mul_spec pk.mat_a_ntt sprime_ntt ((MU.val / 2 : ℕ) : ℤ) hfitex hpkmatbnd
    (by rw [hspntt]; exact hspbnd)
  have hprod : ∀ (i : ℕ), i < L.val → ∀ (k : ℕ), k < 1 →
      toRingElem ((prod.val[i]!).val[k]!) = ∑ jj ∈ Finset.range L.val,
        toRingElem (((nttInvU pk.mat_a_ntt).val[i]!).val[jj]!)
          * toRingElem ((vec_sprime.val[jj]!).val[k]!) := by
    intro i hi k hk; rw [hprod0 i hi k hk, hspntt]
  -- H1_VAL = 4
  simp only [pke.H1_VAL, consts.MODULUS_Q_BITS, consts.MODULUS_P_BITS]
  let* ⟨e0, he0, _⟩ ← Std.Usize.sub_spec (x := 13#usize) (y := 10#usize) (by scalar_tac)
  have he0v : e0.val = 3 := by scalar_tac
  let* ⟨e1, he1, _⟩ ← Std.Usize.sub_spec (x := e0) (y := 1#usize) (by scalar_tac)
  have he1v : e1.val = 2 := by scalar_tac
  let* ⟨x16, hx16, _⟩ ← Std.U16.ShiftLeft_spec 1#u16 e1 (by scalar_tac)
  have hx4 : x16 = 4#u16 := by
    apply Std.UScalar.eq_of_val_eq; rw [hx16, he1v]
    simp [Nat.shiftLeft_eq, U16.size, U16.numBits]
  subst hx4
  let* ⟨prod1, hprod1⟩ ← matrix_wrapping_add_to_all_spec prod 4#u16
  let* ⟨e2, he2, _⟩ ← Std.Usize.sub_spec (x := 13#usize) (y := 10#usize) (by scalar_tac)
  have he2v : e2.val = 3 := by scalar_tac
  let* ⟨prod2, hprod2⟩ ← matrix_shift_right_spec prod1 e2 (by scalar_tac)
  -- vprime = <pk.vec, vec_sprime>  (through the NTT bridge)
  let* ⟨vprime, hvprime0⟩ ← ntt_mul_transpose_spec pk.vec_ntt sprime_ntt ((MU.val / 2 : ℕ) : ℤ)
    hfitex hpkvecbnd (by rw [hspntt]; exact hspbnd)
  have hvprime : ∀ (j : ℕ), j < 1 → ∀ (k : ℕ), k < 1 →
      toRingElem ((vprime.val[j]!).val[k]!) = ∑ ii ∈ Finset.range L.val,
        toRingElem (((nttInvU pk.vec_ntt).val[ii]!).val[j]!)
          * toRingElem ((vec_sprime.val[ii]!).val[k]!) := by
    intro j hj k hk; rw [hvprime0 j hj k hk, hspntt]
  let* ⟨arow, harow⟩ ← Array.index_usize_spec vprime 0#usize (by have := vprime.property; scalar_tac)
  let* ⟨vprime1, hvprime1⟩ ← Array.index_usize_spec arow 0#usize (by have := arow.property; scalar_tac)
  -- message decode
  rw [show (lift msg.to_slice : Result (Slice U8)) = ok msg.to_slice from rfl, bind_tc_ok]
  have hmsgslen : msg.to_slice.length = 32 := by simp [Array.to_slice, Slice.length]
  let* ⟨a1, ha1⟩ ← deserialize_msg_spec msg.to_slice hmsgslen
  -- msg_polyn = a1 << 9
  let* ⟨e3, he3, _⟩ ← Std.Usize.sub_spec (x := 10#usize) (y := 1#usize) (by scalar_tac)
  have he3v : e3.val = 9 := by scalar_tac
  let* ⟨msg_polyn, hmp⟩ ← shift_left_spec a1 e3 (by scalar_tac)
  -- c = vprime1 - msg_polyn
  let* ⟨c, hc⟩ ← sub_spec vprime1 msg_polyn
  -- c1 = c + 4
  let* ⟨c1, hc1⟩ ← wrapping_add_to_all_spec c 4#u16
  -- c2 = c1 >> (10 - T)
  let* ⟨e4, he4, _⟩ ← Std.Usize.sub_spec (x := 10#usize) (y := T) (by scalar_tac)
  have he4v : e4.val = 10 - T.val := by scalar_tac
  let* ⟨c2, hc2⟩ ← shift_right_spec c1 e4 (by scalar_tac)
  -- split point = L*320
  let* ⟨m0, hm0⟩ ← Std.Usize.mul_spec (x := L) (y := 10#usize) (by scalar_tac)
  let* ⟨m1, hm1⟩ ← Std.Usize.mul_spec (x := m0) (y := 256#usize) (by rw [hm0]; scalar_tac)
  let* ⟨m2, hm2⟩ ← Std.Usize.div_spec
  have hm2v : m2.val = L.val * 320 := by rw [hm2, hm1, hm0]; omega
  have hsple : m2.val ≤ out_buf.length := by rw [hm2v, hlenout, hct]; omega
  let* ⟨res, split_back, backfn, hres_len, hsb_len, hres_val, hsb_val, hbackfn⟩ ←
    core.slice.Slice.split_at_mut.spec out_buf m2 hsple
  let* ⟨bprime_buf1, hbp1len, hbp1eq⟩ ← matrix_serialize_col_spec prod2 res 10#usize 10 rfl
    (by norm_num) (by rw [← Slice.length, hres_len, hm2v]) hfit
  let* ⟨c_buf1, hcb1len, hcb1eq⟩ ← ring_serialize_spec c2 split_back T T.val rfl
    ⟨hT.1, by omega⟩ (by rw [← Slice.length, hsb_len, hlenout, hct, hm2v]; omega)
  -- vprime1 = Σᵢ pk.vec[i]·vec_sprime[i]  (physical 2¹⁶)
  have hvp1_pos : vprime1 = (vprime.val[0]!).val[0]! := by
    rw [hvprime1, harow,
      getElem!_pos vprime.val 0 (by have := vprime.property; simp only [Slice.length] at *; scalar_tac),
      getElem!_pos _ 0 (by have := (vprime.val[0]!).property; simp only [Slice.length] at *; scalar_tac)]
  have hip : toRingElem vprime1 = ∑ ii ∈ Finset.range L.val,
      toRingElem (((nttInvU pk.vec_ntt).val[ii]!).val[0]!) * toRingElem ((vec_sprime.val[ii]!).val[0]!) := by
    rw [hvp1_pos]; exact hvprime 0 (by norm_num) 0 (by norm_num)
  -- cm's pre-rounding value equals the spec's `vprime - m·2⁹` (at R10)
  have hcv : (toRingElem c).coerce (2 ^ 10)
      = Spec.Kopis.Polynomial.sub
          (Spec.Kopis.innerProduct (toVecN 10 (nttInvU pk.vec_ntt)) ((toVector13 vec_sprime).coerce (2 ^ 10)))
          (((toPolyN 1 a1).coerce (2 ^ 10)).shiftLeft 9) := by
    rw [hc, coerce_sub10, innerProduct_coerce_bridge (nttInvU pk.vec_ntt) vec_sprime vprime1 hip]
    congr 1
    rw [hmp, he3v, msg_shift_bridge]
  -- toPolyN T c2 = RoundToRt T (that value)
  have hccorr : toPolyN T.val c2 = Spec.Kopis.RoundToRt T.val ((toRingElem c).coerce (2 ^ 10)) := by
    apply roundRt_ring_bridge c c1 c2 T.val hT.2
    · rw [hc1]; congr 1
    · rw [hc2, he4v]
  -- b' correspondence: toVecN 10 prod2 = RoundToR10 (over L.val)
  have hbcorr : toVecN 10 prod2 = Spec.Kopis.RoundToR10 L.val
      (Spec.Kopis.matVecMul (toMatrix13 (nttInvU pk.mat_a_ntt)) (toVector13 vec_sprime)) := by
    apply Vector.ext
    intro idx hidx
    have hs := hprod2 idx hidx 0 (by norm_num); rw [he2v] at hs
    simp only [toVecN, Vector.getElem_ofFn]
    exact prod2_roundR10_bridge_nt (nttInvU pk.mat_a_ntt) vec_sprime prod prod1 prod2 idx hidx
      (fun i₀ hi₀ => hprod i₀ hi₀ 0 (by norm_num)) (hprod1 idx hidx 0 (by norm_num)) hs
  have hbprime : toVecN 10 prod2 = hℓ ▸ Spec.Kopis.RoundToR10 (Spec.Kopis.ℓ p)
      (Spec.Kopis.matVecMul
        (Spec.Kopis.GenMat (Spec.Kopis.ℓ p)
          (Spec.slice pk_bytes (32 * 10 * Spec.Kopis.ℓ p) 32 (by simp [Spec.Kopis.pkSize])))
        (Spec.Kopis.GenSecret (Spec.Kopis.ℓ p) (Spec.Kopis.μ p) (arrayToBytes coins))) := by
    rw [hbcorr, roundR10_mvm_cast, hpkmat, genSecret_cast, hvecs, ← hμ]
  have hvsc : toVector13 vec_sprime
      = hℓ ▸ Spec.Kopis.GenSecret (Spec.Kopis.ℓ p) (Spec.Kopis.μ p) (arrayToBytes coins) := by
    rw [hvecs, genSecret_cast, hμ]
  have hcmfinal : toPolyN T.val c2 = Spec.Kopis.RoundToRt T.val
      (Spec.Kopis.Polynomial.sub
        (Spec.Kopis.innerProduct
          (Spec.Kopis.PolyVector.deserialize 10
            (Spec.slice pk_bytes 0 (32 * 10 * Spec.Kopis.ℓ p) (by simp [Spec.Kopis.pkSize])))
          ((Spec.Kopis.GenSecret (Spec.Kopis.ℓ p) (Spec.Kopis.μ p) (arrayToBytes coins)).coerce (2 ^ 10)))
        (((Spec.Kopis.deserialize 1 ((arrayToBytes msg).cast rfl)).coerce (2 ^ 10)).shiftLeft 9)) := by
    have hA : Spec.Kopis.innerProduct (toVecN 10 (nttInvU pk.vec_ntt)) ((toVector13 vec_sprime).coerce (2 ^ 10))
        = Spec.Kopis.innerProduct
            (Spec.Kopis.PolyVector.deserialize 10
              (Spec.slice pk_bytes 0 (32 * 10 * Spec.Kopis.ℓ p) (by simp [Spec.Kopis.pkSize])))
            ((Spec.Kopis.GenSecret (Spec.Kopis.ℓ p) (Spec.Kopis.μ p) (arrayToBytes coins)).coerce (2 ^ 10)) := by
      rw [hpkvec, hvsc, coerceVec_cast, innerProduct_cast]
    have hmeq : toPolyN 1 a1 = Spec.Kopis.deserialize 1 ((arrayToBytes msg).cast rfl) := by
      rw [ha1]
      refine congrArg (Spec.Kopis.deserialize 1) ?_
      apply Vector.toList_inj.mp
      refine Eq.trans ?_ (Vector.toList_cast ..).symm
      refine Eq.trans ?_ (arrayToBytes_toList msg).symm
      rw [sliceToBytes_toList]
      simp [Array.to_slice]
    have hB : ((toPolyN 1 a1).coerce (2 ^ 10)).shiftLeft 9
        = ((Spec.Kopis.deserialize 1 ((arrayToBytes msg).cast rfl)).coerce (2 ^ 10)).shiftLeft 9 := by
      rw [hmeq]
    rw [hccorr, hcv, hA, hB]
  -- reconstruct the ciphertext bytes
  have hcond1 : bprime_buf1.length = m2.val := by rw [hbp1len, hm2v]
  have hcond2 : c_buf1.length = out_buf.length - m2.val := by
    rw [hcb1len, hlenout, hct, hm2v]; omega
  obtain ⟨hrval, hrlen⟩ := hbackfn bprime_buf1 c_buf1 hcond1 hcond2
  refine ⟨hrlen.trans hlenout, ?_⟩
  have hb1t : bprime_buf1.val.map (·.bv)
      = (Spec.Kopis.PolyVector.serialize 10 (toVecN 10 prod2)).toList := by
    rw [← sliceToBytes_toList hbp1len, hbp1eq]
  have hc1t : c_buf1.val.map (·.bv) = (Spec.Kopis.serialize T.val (toPolyN T.val c2)).toList := by
    rw [← sliceToBytes_toList hcb1len, hcb1eq]
  apply Vector.toList_inj.mp
  rw [sliceToBytes_toList, hrval, List.map_append, hb1t, hc1t, hbprime, serialize_eqRec_toList,
    hcmfinal]
  unfold Spec.Kopis.PkeEncrypt
  refine Eq.trans ?_ (Vector.toList_cast ..).symm
  rw [bappend_toList, ht]
  rfl

end Kopis.Properties
