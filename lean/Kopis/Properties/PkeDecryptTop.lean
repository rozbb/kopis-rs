import Kopis.Properties.RoundR1
import Kopis.Properties.DecryptGlue
import Kopis.Properties.InnerProduct
import Kopis.Properties.EncryptGlue
import Kopis.Properties.MulTranspose
import Kopis.Properties.RingArith
import Kopis.Properties.SerializeTop
import Kopis.Properties.ExpandDecap
import Kopis.Properties.DeserializeVec
import Kopis.Properties.DeserializeCm
open Aeneas Aeneas.Std Result RustKopis
open Spec (𝔹)
open scoped Spec.Notations
namespace Kopis.Properties
set_option maxHeartbeats 10000000
set_option maxRecDepth 8000

/-- Prefix slice: `sliceToBytes` of the `take k` prefix equals `Spec.slice` at offset 0. -/
theorem sliceToBytes_take_eq_slice (s t : Slice U8) (N k : ℕ) (hN : s.length = N)
    (hk : k ≤ N) (hval : t.val = s.val.take k) (ht : t.length = k) :
    sliceToBytes t k ht = Spec.slice (sliceToBytes s N hN) 0 k (by omega) := by
  apply Vector.ext; intro i hi
  rw [slice_getElem]
  simp only [sliceToBytes, Vector.getElem_ofFn, Nat.zero_add, hval, List.getElem_take]

/-- Suffix slice: `sliceToBytes` of the `drop k` suffix equals `Spec.slice` at offset `k`. -/
theorem sliceToBytes_drop_eq_slice (s t : Slice U8) (N k len : ℕ) (hN : s.length = N)
    (hkl : k + len = N) (hval : t.val = s.val.drop k) (ht : t.length = len) :
    sliceToBytes t len ht = Spec.slice (sliceToBytes s N hN) k len (by omega) := by
  apply Vector.ext; intro i hi
  rw [slice_getElem]
  simp only [sliceToBytes, Vector.getElem_ofFn, hval, List.getElem_drop]

/-- `PolyVector.deserialize` transports across a length cast when the two byte inputs
have equal underlying lists. -/
theorem deserialize_vec_toList_cast {ℓ ℓ' n : ℕ} (h : ℓ = ℓ')
    (a : 𝔹 (32 * n * ℓ)) (b : 𝔹 (32 * n * ℓ')) (hab : a.toList = b.toList) :
    h ▸ Spec.Kopis.PolyVector.deserialize (ℓ := ℓ) n a
      = Spec.Kopis.PolyVector.deserialize (ℓ := ℓ') n b := by
  cases h; exact congrArg (Spec.Kopis.PolyVector.deserialize n) (Vector.toList_inj.mp hab)

/-- The coerced `deserialize` of a `cm` slice is invariant under swapping the bit-width
`t p` for the definitionally-equal `Usize` value `↑T` (the `coerce` erases the type index,
so the propositional equality `t p = ↑T` suffices). -/
theorem deserialize_slice_coerce_cast {p : Spec.Kopis.ParameterSet} (T : Usize)
    (ht : Spec.Kopis.t p = T.val) (C : 𝔹 (Spec.Kopis.ctSize p)) (off m : ℕ)
    (hA : off + 32 * T.val ≤ Spec.Kopis.ctSize p)
    (hB : off + 32 * Spec.Kopis.t p ≤ Spec.Kopis.ctSize p) :
    (Spec.Kopis.deserialize (Spec.Kopis.t p) (Spec.slice C off (32 * Spec.Kopis.t p) hB)).coerce m
      = (Spec.Kopis.deserialize T.val (Spec.slice C off (32 * T.val) hA)).coerce m := by
  generalize hk : Spec.Kopis.t p = k at ht hB ⊢
  cases ht
  rfl

/-- **Rust `pke.decrypt` matches the spec `PkeDecrypt`.** -/
theorem decrypt_spec {L : Usize} (T : Usize) (sk : pke.PkeSecretKey L)
    (ciphertext : Slice U8) (p : Spec.Kopis.ParameterSet) (sk_seed : 𝔹 32) (sBound : ℤ)
    (hℓ : Spec.Kopis.ℓ p = L.val) (ht : Spec.Kopis.t p = T.val)
    (hT : 3 ≤ T.val ∧ T.val ≤ 6)
    (hfit : L.val * 10 * 256 ≤ Usize.max)
    (hfitex : fitsExactly L.val sBound)
    (hskbnd : SecretBounded (nttInvS sk) sBound)
    (hlenct : ciphertext.length = Spec.Kopis.ctSize p)
    (hsk : toVector13 (nttInvS sk) = hℓ ▸ (Spec.Kopis.ExpandDecapKey p sk_seed).1) :
    pke.decrypt T sk ciphertext
      ⦃ (r : Array U8 32#usize) => arrayToBytes r
          = Spec.Kopis.PkeDecrypt p sk_seed (sliceToBytes ciphertext (Spec.Kopis.ctSize p) hlenct) ⦄ := by
  unfold pke.decrypt
  have hct : Spec.Kopis.ctSize p = L.val * 320 + T.val * 32 := by
    simp only [Spec.Kopis.ctSize, hℓ, ht]; ring
  have hlenmax : ciphertext.length ≤ Usize.max := by
    have := ciphertext.property; simpa [Slice.length] using this
  simp only [pke.ciphertext_len, consts.MODULUS_P_BITS, consts.MODULUS_Q_BITS, consts.RING_DEG]
  let* ⟨n0, hn0⟩ ← Std.Usize.mul_spec (x := L) (y := 10#usize) (by scalar_tac)
  let* ⟨n1, hn1⟩ ← Std.Usize.mul_spec (x := n0) (y := 256#usize) (by rw [hn0]; scalar_tac)
  let* ⟨n2, hn2⟩ ← Std.Usize.div_spec
  let* ⟨n3, hn3⟩ ← Std.Usize.mul_spec (x := T) (y := 256#usize) (by scalar_tac)
  let* ⟨n4, hn4⟩ ← Std.Usize.div_spec
  let* ⟨rv, hrv⟩ ← Std.Usize.add_spec (x := n2) (y := n4)
    (by rw [hn2, hn1, hn0, hn4, hn3]; rw [hct] at hlenct; scalar_tac)
  rw [show massert (ciphertext.len = rv) = ok () from by
    have hlv : ciphertext.len = rv := by
      apply Std.UScalar.eq_of_val_eq
      rw [hct] at hlenct
      rw [hrv, hn2, hn1, hn0, hn4, hn3]; show ciphertext.length = _; omega
    simp only [massert, if_pos hlv], bind_tc_ok]
  let* ⟨m0, hm0⟩ ← Std.Usize.mul_spec (x := L) (y := 10#usize) (by scalar_tac)
  let* ⟨m1, hm1⟩ ← Std.Usize.mul_spec (x := m0) (y := 256#usize) (by rw [hm0]; scalar_tac)
  let* ⟨m2, hm2⟩ ← Std.Usize.div_spec
  have hm2v : m2.val = L.val * 320 := by rw [hm2, hm1, hm0]; omega
  have hsple : m2.val ≤ ciphertext.length := by rw [hm2v, hlenct, hct]; omega
  let* ⟨bprime_bytes, c_bytes, hbb_len, hcb_len, hbb_val, hcb_val⟩ ←
    core.slice.Slice.split_at.spec ciphertext m2 hsple
  -- deserialize b' and cm
  have hlen_bb : bprime_bytes.length = L.val * (32 * 10) := by rw [hbb_len, hm2v]
  let* ⟨bprime, hbprime, hbpbnd⟩ ← spec_and (matrix_deserialize_10_spec bprime_bytes hlen_bb hfit)
    (deserialize_10_uniformBounded bprime_bytes)
  let* ⟨bprime_ntt, hbpntt⟩ ← from_uniform_matrix_spec bprime
  have hlen_cb : c_bytes.length = 32 * T.val := by rw [hcb_len, hlenct, hct, hm2v]; omega
  let* ⟨cm, hcm⟩ ← ringElem_deserialize_gen_spec' c_bytes T T.val rfl
    ⟨by omega, by omega⟩ (by omega) (by omega) hlen_cb
  -- i3 = 10 - T
  let* ⟨i3, hi3, _⟩ ← Std.Usize.sub_spec (x := 10#usize) (y := T) (by scalar_tac)
  have hi3v : i3.val = 10 - T.val := by scalar_tac
  -- c1 = cm << (10 - T)
  let* ⟨c1, hc1⟩ ← shift_left_spec cm i3 (by scalar_tac)
  -- v = <bprime, sk>, v1 = v[0][0]  (through the NTT bridge)
  let* ⟨v, hv0⟩ ← ntt_mul_transpose_spec bprime_ntt sk sBound hfitex
    (by rw [hbpntt]; exact hbpbnd) hskbnd
  have hv : ∀ (j : ℕ), j < 1 → ∀ (k : ℕ), k < 1 →
      toRingElem ((v.val[j]!).val[k]!) = ∑ ii ∈ Finset.range L.val,
        toRingElem ((bprime.val[ii]!).val[j]!) * toRingElem (((nttInvS sk).val[ii]!).val[k]!) := by
    intro j hj k hk; rw [hv0 j hj k hk, hbpntt]
  let* ⟨arow, harow⟩ ← Array.index_usize_spec v 0#usize (by have := v.property; scalar_tac)
  let* ⟨v1, hv1⟩ ← Array.index_usize_spec arow 0#usize (by have := arow.property; scalar_tac)
  -- mprime = v1 - c1
  let* ⟨mprime, hmprime⟩ ← sub_spec v1 c1
  -- h2_val = 2⁸ - 2⁹⁻ᵀ + 4
  let* ⟨j4, hj4, _⟩ ← Std.Usize.sub_spec (x := 10#usize) (y := 2#usize) (by scalar_tac)
  have hj4v : j4.val = 8 := by scalar_tac
  let* ⟨j5, hj5, _⟩ ← Std.U16.ShiftLeft_spec 1#u16 j4 (by scalar_tac)
  have hj5v : j5.val = 2 ^ 8 := by
    rw [hj5, hj4v]; simp only [Nat.shiftLeft_eq, one_mul]
    rw [Nat.mod_eq_of_lt (by simp only [U16.size, U16.numBits]; norm_num)]
  let* ⟨j6, hj6, _⟩ ← Std.Usize.sub_spec (x := i3) (y := 1#usize) (by scalar_tac)
  have hj6v : j6.val = 9 - T.val := by rw [hj6, hi3v]; omega
  let* ⟨j7, hj7, _⟩ ← Std.U16.ShiftLeft_spec 1#u16 j6 (by scalar_tac)
  have hj7v : j7.val = 2 ^ (9 - T.val) := by
    rw [hj7, hj6v]; simp only [Nat.shiftLeft_eq, one_mul]
    rw [Nat.mod_eq_of_lt]
    calc 2 ^ (9 - T.val) ≤ 2 ^ 6 := Nat.pow_le_pow_right (by norm_num) (by omega)
      _ < U16.size := by simp only [U16.size, U16.numBits]; norm_num
  let* ⟨j8, hj8, _⟩ ← Std.U16.sub_spec (x := j5) (y := j7) (by
    rw [hj7v, hj5v]
    calc 2 ^ (9 - T.val) ≤ 2 ^ 6 := Nat.pow_le_pow_right (by norm_num) (by omega)
      _ ≤ 2 ^ 8 := by norm_num)
  have hj8v : j8.val = 2 ^ 8 - 2 ^ (9 - T.val) := by rw [hj8, hj5v, hj7v]
  let* ⟨j9, hj9, _⟩ ← Std.Usize.sub_spec (x := 13#usize) (y := 10#usize) (by scalar_tac)
  have hj9v : j9.val = 3 := by scalar_tac
  let* ⟨j10, hj10, _⟩ ← Std.Usize.sub_spec (x := j9) (y := 1#usize) (by scalar_tac)
  have hj10v : j10.val = 2 := by rw [hj10, hj9v]
  let* ⟨j11, hj11, _⟩ ← Std.U16.ShiftLeft_spec 1#u16 j10 (by scalar_tac)
  have hj11v : j11.val = 4 := by
    rw [hj11, hj10v]; simp only [Nat.shiftLeft_eq, one_mul]
    rw [Nat.mod_eq_of_lt (by simp only [U16.size, U16.numBits]; norm_num)]
  let* ⟨h2, hh2⟩ ← Std.U16.add_spec (x := j8) (y := j11) (by
    rw [hj8v, hj11v]
    have hb : 2 ^ (9 - T.val) ≤ 2 ^ 8 := Nat.pow_le_pow_right (by norm_num) (by omega)
    have e8 : (2 : ℕ) ^ 8 = 256 := by norm_num
    have em : U16.max = 65535 := by simp only [U16.max, U16.numBits]; norm_num
    omega)
  have hh2v : h2.val = 2 ^ 8 - 2 ^ (9 - T.val) + 4 := by rw [hh2, hj8v, hj11v]
  -- mprime1 = mprime + h2_val
  let* ⟨mprime1, hmprime1⟩ ← wrapping_add_to_all_spec mprime h2
  -- mprime2 = mprime1 >> 9
  let* ⟨i12, hi12, _⟩ ← Std.Usize.sub_spec (x := 10#usize) (y := 1#usize) (by scalar_tac)
  have hi12v : i12.val = 9 := by scalar_tac
  let* ⟨mprime2, hmprime2⟩ ← shift_right_spec mprime1 i12 (by scalar_tac)
  -- serialize mprime2 (1 bit) into a fresh 32-byte array
  let* ⟨s, to_slice_mut_back, hs_val, hto_back⟩ ← Array.to_slice_mut_spec
  have hslen : s.val.length = 32 * 1 := by
    rw [hs_val]; show (Array.repeat 32#usize 0#u8).val.length = 32 * 1
    simp [Array.repeat]
  let* ⟨s1, hs1len, hs1eq⟩ ← ring_serialize_spec mprime2 s 1#usize 1 rfl ⟨by norm_num, by norm_num⟩ hslen
  -- === algebraic correspondence ===
  -- v1 = v[0][0]
  have hv1_pos : v1 = (v.val[0]!).val[0]! := by
    rw [hv1, harow,
      getElem!_pos v.val 0 (by have := v.property; simp only [Slice.length] at *; scalar_tac),
      getElem!_pos _ 0 (by have := (v.val[0]!).property; simp only [Slice.length] at *; scalar_tac)]
  have hip : toRingElem v1 = ∑ ii ∈ Finset.range L.val,
      toRingElem ((bprime.val[ii]!).val[0]!) * toRingElem (((nttInvS sk).val[ii]!).val[0]!) := by
    rw [hv1_pos]; exact hv 0 (by norm_num) 0 (by norm_num)
  have hvcoerce := innerProduct_coerce_bridge bprime (nttInvS sk) v1 hip
  have hc1coerce : (toRingElem c1).coerce (2 ^ 10)
      = ((toPolyN T.val cm).coerce (2 ^ 10)).shiftLeft (10 - T.val) := by
    rw [hc1, hi3v]; exact shiftLeft_coerce_bridge cm T.val (by omega)
  have hmcoerce : (toRingElem mprime).coerce (2 ^ 10)
      = Spec.Kopis.Polynomial.sub
          (Spec.Kopis.innerProduct (toVecN 10 bprime) ((toVector13 (nttInvS sk)).coerce (2 ^ 10)))
          (((toPolyN T.val cm).coerce (2 ^ 10)).shiftLeft (10 - T.val)) := by
    rw [hmprime, coerce_sub10, hvcoerce, hc1coerce]
  have hround : toPolyN 1 mprime2
      = Spec.Kopis.RoundToR1 T.val ((toRingElem mprime).coerce (2 ^ 10)) := by
    apply roundR1_ring_bridge mprime mprime1 mprime2 T.val ⟨by omega, by omega⟩
    · rw [hmprime1]; congr 2; rw [hh2v]
    · rw [hmprime2, hi12v]
  -- spec-side slice/cast bridging
  have hk_eq : m2.val = 32 * 10 * Spec.Kopis.ℓ p := by rw [hm2v, hℓ]; ring
  have hbb_val' : bprime_bytes.val = ciphertext.val.take (32 * 10 * Spec.Kopis.ℓ p) := by
    rw [hbb_val, hk_eq]
  have hbb_len' : bprime_bytes.length = 32 * 10 * Spec.Kopis.ℓ p := by rw [hbb_len, hk_eq]
  have hcb_val' : c_bytes.val = ciphertext.val.drop (32 * 10 * Spec.Kopis.ℓ p) := by
    rw [hcb_val, hk_eq]
  have hbprime_spec : hℓ ▸ Spec.Kopis.PolyVector.deserialize (ℓ := Spec.Kopis.ℓ p) 10
        (Spec.slice (sliceToBytes ciphertext (Spec.Kopis.ctSize p) hlenct) 0
          (32 * 10 * Spec.Kopis.ℓ p) (by rw [hct, hℓ]; omega))
      = toVecN 10 bprime := by
    rw [hbprime]
    apply deserialize_vec_toList_cast hℓ
    rw [← sliceToBytes_take_eq_slice ciphertext bprime_bytes (Spec.Kopis.ctSize p)
          (32 * 10 * Spec.Kopis.ℓ p) hlenct (by rw [hct, hℓ]; omega) hbb_val' hbb_len',
        sliceToBytes_toList, Vector.toList_cast, sliceToBytes_toList]
  have hcm_spec : toPolyN T.val cm = Spec.Kopis.deserialize T.val
      (Spec.slice (sliceToBytes ciphertext (Spec.Kopis.ctSize p) hlenct)
        (32 * 10 * Spec.Kopis.ℓ p) (32 * T.val) (by rw [hct, hℓ]; omega)) := by
    rw [hcm, sliceToBytes_drop_eq_slice ciphertext c_bytes (Spec.Kopis.ctSize p)
        (32 * 10 * Spec.Kopis.ℓ p) (32 * T.val) hlenct (by rw [hct, hℓ]; ring) hcb_val' hlen_cb]
  have hvecs_coerce : (toVector13 (nttInvS sk)).coerce (2 ^ 10)
      = hℓ ▸ ((Spec.Kopis.ExpandDecapKey p sk_seed).1.coerce (2 ^ 10)) := by
    rw [hsk, coerceVec_cast]
  have hv_spec : Spec.Kopis.innerProduct (toVecN 10 bprime) ((toVector13 (nttInvS sk)).coerce (2 ^ 10))
      = Spec.Kopis.innerProduct
          (Spec.Kopis.PolyVector.deserialize (ℓ := Spec.Kopis.ℓ p) 10
            (Spec.slice (sliceToBytes ciphertext (Spec.Kopis.ctSize p) hlenct) 0
              (32 * 10 * Spec.Kopis.ℓ p) (by rw [hct, hℓ]; omega)))
          (((Spec.Kopis.ExpandDecapKey p sk_seed).1).coerce (2 ^ 10)) := by
    rw [← hbprime_spec, hvecs_coerce, innerProduct_cast]
  -- === assemble the output ===
  rw [hto_back]
  have hs1val32 : s1.val.length = 32 := by
    have := hs1len; simp only [Slice.length] at this; omega
  have houtval : (Array.from_slice (Array.repeat 32#usize 0#u8) s1).val = s1.val :=
    Array.from_slice_val _ s1 (by show s1.val.length = 32; rw [hs1val32])
  apply Vector.toList_inj.mp
  rw [arrayToBytes_toList, houtval, ← sliceToBytes_toList hs1len, hs1eq, hround, hmcoerce, hv_spec,
    hcm_spec]
  -- reduce the spec side: destructure `ExpandDecapKey` to collapse the `match`, align `t p = ↑T`
  unfold Spec.Kopis.PkeDecrypt
  generalize Spec.Kopis.ExpandDecapKey p sk_seed = E
  obtain ⟨vec_s, _, _, _⟩ := E
  simp only [ht]
  rw [deserialize_slice_coerce_cast T ht (sliceToBytes ciphertext (Spec.Kopis.ctSize p) hlenct)
    (32 * 10 * Spec.Kopis.ℓ p) (2 ^ 10) (by rw [hct, hℓ]; omega) (by rw [hct, hℓ, ht]; omega)]
  rfl

end Kopis.Properties
