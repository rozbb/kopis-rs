import Kopis.Properties.PkeHash
import Kopis.Properties.RoundTop
import Kopis.Properties.MulTranspose
open Aeneas Aeneas.Std Result kopis_kem
open Spec (𝔹)
open scoped Spec.Notations
open Spec.TurboSHAKE (turboSHAKE256 turboSHAKE256_getElem_prefix)
open Spec.Kopis (DOMSEP_KGEXPAND DOMSEP_PKHASH)
namespace Kopis.Properties
set_option maxHeartbeats 2000000
set_option maxRecDepth 4000

/-- `slice`'s coefficient is a shifted index of the underlying vector. -/
theorem slice_getElem {m : ℕ} (v : 𝔹 m) (off len : ℕ) (h : off + len ≤ m) (k : ℕ) (hk : k < len) :
    (Spec.slice v off len h)[k]'hk = v[off + k]'(by omega) := by
  unfold Spec.slice; rw [Vector.getElem_ofFn]

/-- Abstract: dropping the first `off` bytes of a length-`off+32` vector `A` equals the
`[off, off+32)` slice of a length-96 vector `B`, when they agree pointwise on that window. -/
theorem drop_toList_eq_slice (off : ℕ) (A : 𝔹 (off + 32)) (B : 𝔹 96) (h : off + 32 ≤ 96)
    (hkey : ∀ k, (hk : k < 32) → A[off + k]'(by omega) = B[off + k]'(by omega)) :
    A.toList.drop off = (Spec.slice B off 32 h).toList := by
  apply List.ext_getElem
  · simp only [List.length_drop, Vector.toList_length, Spec.slice]; omega
  · intro k h1 h2
    have hk : k < 32 := by simpa [Spec.slice] using h2
    rw [List.getElem_drop]
    rw [Vector.getElem_toList, Vector.getElem_toList, slice_getElem]
    exact hkey k hk

/-- A `read` window of the XOF stream at byte-offset `off` (length 32) equals the spec's
`slice … off 32` of the length-96 squeeze (XOF prefix/streaming property). -/
theorem turboSHAKE256_read_window {n : ℕ} (msg : 𝔹 n) (D : Byte) (off : ℕ)
    (h : off + 32 ≤ 96) :
    (turboSHAKE256 msg D (off + 32)).toList.drop off
      = (Spec.slice (turboSHAKE256 msg D 96) off 32 h).toList :=
  drop_toList_eq_slice off (turboSHAKE256 msg D (off + 32)) (turboSHAKE256 msg D 96) h
    (fun k hk => turboSHAKE256_getElem_prefix msg D (off + 32) 96 (off + k) (by omega) (by omega))

/-- `sk` as a clean literal-32 byte vector, matching the spec's `sk : 𝔹 32`. -/
def skBytes (sk : Array U8 32#usize) : 𝔹 32 := (arrayToBytes sk).cast rfl

/-- The serialized public-key bytes of a `PkePublicKey` struct — the abstraction that
corresponds to the spec's `pk : 𝔹 (pkSize p)`. -/
def pkStructBytes {L : Usize} (self : pke.PkePublicKey L) (p : Spec.Kopis.ParameterSet)
    (hℓ : Spec.Kopis.ℓ p = L.val) : 𝔹 (Spec.Kopis.pkSize p) :=
  (Spec.Kopis.PolyVector.serialize 10 (toVecN 10 self.vec) ‖ matSeedBytes self).cast (by
    simp only [Spec.Kopis.pkSize, hℓ]; ring)

/-- `1#u8` bit-vector is the KG-expand domain separator. -/
theorem domsep_kgexpand_bv : (1#u8).bv = DOMSEP_KGEXPAND := by decide

/-- Byte-concat bridge for the KG-expand absorb: the Rust message `sk ++ [i]` interprets
as the spec's `skBytes sk ‖ #v[i.bv]`. -/
theorem turboSHAKE256_sk_concat (sk : Array U8 32#usize) (i : U8) (D : Byte) (N : ℕ) :
    turboSHAKE256 (u8ListToBytes (sk.val ++ [i])) D N
      = turboSHAKE256 (skBytes sk ‖ #v[i.bv]) D N := by
  have h32 : sk.val.length = 32 := sk.property
  have hlen : (sk.val ++ [i]).length = 33 := by simp [h32]
  have htl : (u8ListToBytes (sk.val ++ [i])).toList = (skBytes sk ‖ #v[i.bv]).toList := by
    have e2 : (skBytes sk).toList = sk.val.map (·.bv) := by
      simp only [skBytes, Vector.toList_cast]; exact arrayToBytes_toList sk
    have e1 : (u8ListToBytes (sk.val ++ [i])).toList = (sk.val ++ [i]).map (·.bv) := by
      simp only [u8ListToBytes, Vector.toList_ofFn]; rw [List.ofFn_getElem_eq_map]
    rw [e1]
    show (sk.val ++ [i]).map (·.bv) = (skBytes sk ++ #v[i.bv]).toList
    simp [Vector.toList_push, e2, List.map_append]
  have hmsg : u8ListToBytes (sk.val ++ [i]) = (skBytes sk ‖ #v[i.bv]).cast (by rw [hlen]) := by
    apply Vector.toList_inj.mp; rw [Vector.toList_cast]; exact htl
  rw [hmsg]; exact turboSHAKE256_cast (by rw [hlen]) _ D N

/-- Transporting a vector along an index equality leaves its underlying list unchanged. -/
theorem eqRec_toList {α : Type*} {n m : ℕ} (h : n = m) (v : Vector α n) :
    (h ▸ v).toList = v.toList := by cases h; rfl

/-- `serialize` commutes with index transport at the list level. -/
theorem serialize_eqRec_toList {N ℓ ℓ' : ℕ} (h : ℓ = ℓ')
    (v : Spec.Kopis.PolyVector (2 ^ N) ℓ) :
    (Spec.Kopis.PolyVector.serialize N (h ▸ v)).toList
      = (Spec.Kopis.PolyVector.serialize N v).toList := by cases h; rfl

/-- The rounded-product expression transports cleanly across the matrix dimension. -/
theorem roundExpr_cast {ℓ ℓ' : ℕ} (h : ℓ = ℓ') (μ : ℕ) (ms ss : 𝔹 32) :
    h ▸ (Spec.Kopis.RoundToR10 ℓ (Spec.Kopis.matVecMul
          (Matrix.transpose (Spec.Kopis.GenMat ℓ ms)) (Spec.Kopis.GenSecret ℓ μ ss)))
      = Spec.Kopis.RoundToR10 ℓ' (Spec.Kopis.matVecMul
          (Matrix.transpose (Spec.Kopis.GenMat ℓ' ms)) (Spec.Kopis.GenSecret ℓ' μ ss)) := by
  cases h; rfl

/-- `toList` of a byte-vector append (`‖`) splits as list append. -/
theorem bappend_toList {a b : ℕ} (X : 𝔹 a) (Y : 𝔹 b) :
    (X ‖ Y).toList = X.toList ++ Y.toList := by
  show (X ++ Y).toList = X.toList ++ Y.toList
  rw [Vector.toList_append]

/-- `turboSHAKE256` depends only on the list of input bytes. -/
theorem turboSHAKE256_congr {a b : ℕ} (X : 𝔹 a) (Y : 𝔹 b) (D : Byte) (N : ℕ)
    (h : X.toList = Y.toList) : turboSHAKE256 X D N = turboSHAKE256 Y D N := by
  have hab : a = b := by
    have h2 := congrArg List.length h; simp only [Vector.toList_length] at h2; exact h2
  subst hab; rw [Vector.toList_inj.mp h]

/-- **Rust `expand_decap_key` matches the spec `ExpandDecapKey`.** -/
theorem expand_decap_key_spec (L MU : Usize) (sk : Array U8 32#usize)
    (p : Spec.Kopis.ParameterSet)
    (hℓ : Spec.Kopis.ℓ p = L.val) (hμ : Spec.Kopis.μ p = MU.val)
    (hMU : MU.val = 6 ∨ MU.val = 8 ∨ MU.val = 10)
    (hbuf : L.val * 320 + 32 ≤ 1312) (hfit : L.val * 10 * 256 ≤ Usize.max)
    (hL : L.val < 256) :
    pke.expand_decap_key L MU sk
      ⦃ (r : pke.PkeSecretKey L × Array U8 32#usize × pke.PkePublicKey L × Array U8 32#usize) =>
          toVector13 r.1 = hℓ ▸ (Spec.Kopis.ExpandDecapKey p (skBytes sk)).1 ∧
          arrayToBytes r.2.1 = (Spec.Kopis.ExpandDecapKey p (skBytes sk)).2.1 ∧
          pkStructBytes r.2.2.1 p hℓ = (Spec.Kopis.ExpandDecapKey p (skBytes sk)).2.2.1 ∧
          arrayToBytes r.2.2.2 = (Spec.Kopis.ExpandDecapKey p (skBytes sk)).2.2.2 ∧
          toMatrix13 r.2.2.1.mat_a
            = Spec.Kopis.GenMat L.val (arrayToBytes r.2.2.1.matrix_seed) ⦄ := by
  unfold pke.expand_decap_key
  step*
  -- domain separator + injected byte
  have hi_bv : (#v[i.bv] : 𝔹 1) = #v[((Spec.Kopis.ℓ p : ℕ) : Byte)] := by
    simp only [i_post, cast_u8_bv, hℓ]
  -- absorbed message  sk ++ [i]
  have habs : hasherAbsorbed hasher2 = sk.val ++ [i] := by
    rw [hasher2_post, hasher1_post, hasher_post, s_post, s1_post]
    simp [Array.to_slice, Array.make]
  have hrm0 : readerModel xof = (1#u8, sk.val ++ [i]) := by rw [xof_post1, habs]
  have hrm1 : readerModel xof1 = (1#u8, sk.val ++ [i]) := by rw [xof1_post4, hrm0]
  have hrm2 : readerModel xof2 = (1#u8, sk.val ++ [i]) := by rw [xof2_post4, hrm1]
  -- offsets
  have hs2len : s2.length = 32 := by
    rw [Slice.length, s2_post1]; simpa using (Array.repeat 32#usize 0#u8).property
  have hs4len : s4.length = 32 := by
    rw [Slice.length, s4_post1]; simpa using (Array.repeat 32#usize 0#u8).property
  have hs6len : s6.length = 32 := by
    rw [Slice.length, s6_post1]; simpa using (Array.repeat 32#usize 0#u8).property
  have hoff1 : readerOffset xof1 = 32 := by rw [xof1_post3, xof_post2, hs2len]
  have hoff2 : readerOffset xof2 = 64 := by rw [xof2_post3, hoff1, hs4len]
  -- the three seed windows equal the spec's slices of the length-96 squeeze
  have hs3bytes : s3.val.map (·.bv)
      = (Spec.slice (turboSHAKE256 (skBytes sk ‖ #v[((Spec.Kopis.ℓ p : ℕ) : Byte)])
          DOMSEP_KGEXPAND 96) 0 32 (by omega)).toList := by
    rw [xof1_post2, hrm0, xof_post2, hs2len]
    dsimp only
    rw [turboSHAKE256_sk_concat]
    simp only [domsep_kgexpand_bv, hi_bv]
    rw [turboSHAKE256_read_window _ _ 0 (by omega)]
  have hs5bytes : s5.val.map (·.bv)
      = (Spec.slice (turboSHAKE256 (skBytes sk ‖ #v[((Spec.Kopis.ℓ p : ℕ) : Byte)])
          DOMSEP_KGEXPAND 96) 32 32 (by omega)).toList := by
    rw [xof2_post2, hrm1, hoff1, hs4len]
    dsimp only
    rw [turboSHAKE256_sk_concat]
    simp only [domsep_kgexpand_bv, hi_bv]
    rw [turboSHAKE256_read_window _ _ 32 (by omega)]
  have hs7bytes : s7.val.map (·.bv)
      = (Spec.slice (turboSHAKE256 (skBytes sk ‖ #v[((Spec.Kopis.ℓ p : ℕ) : Byte)])
          DOMSEP_KGEXPAND 96) 64 32 (by omega)).toList := by
    rw [__post2, hrm2, hoff2, hs6len]
    dsimp only
    rw [turboSHAKE256_sk_concat]
    simp only [domsep_kgexpand_bv, hi_bv]
    rw [turboSHAKE256_read_window _ _ 64 (by omega)]
  -- reconstructed seed arrays carry the read bytes
  have e32 : ((32#usize : Usize).val : ℕ) = 32 := rfl
  have hs3len : s3.length = 32 := by rw [xof1_post1, hs2len]
  have hs5len : s5.length = 32 := by rw [xof2_post1, hs4len]
  have hs7len : s7.length = 32 := by rw [__post1, hs6len]
  have hms3 : (to_slice_mut_back s3).val = s3.val := by
    rw [s2_post2]; exact Array.from_slice_val _ s3 (by rw [← Slice.length, hs3len]; exact e32.symm)
  have hms5 : (to_slice_mut_back1 s5).val = s5.val := by
    rw [s4_post2]; exact Array.from_slice_val _ s5 (by rw [← Slice.length, hs5len]; exact e32.symm)
  have hms7 : (to_slice_mut_back2 s7).val = s7.val := by
    rw [s6_post2]; exact Array.from_slice_val _ s7 (by rw [← Slice.length, hs7len]; exact e32.symm)
  -- seed byte-vectors equal the spec's slices of the length-96 squeeze
  have hmatseed : arrayToBytes (to_slice_mut_back s3)
      = Spec.slice (turboSHAKE256 (skBytes sk ‖ #v[((Spec.Kopis.ℓ p : ℕ) : Byte)])
          DOMSEP_KGEXPAND 96) 0 32 (by omega) := by
    apply Vector.toList_inj.mp; rw [arrayToBytes_toList, hms3]; exact hs3bytes
  have hsecseed : arrayToBytes (to_slice_mut_back1 s5)
      = Spec.slice (turboSHAKE256 (skBytes sk ‖ #v[((Spec.Kopis.ℓ p : ℕ) : Byte)])
          DOMSEP_KGEXPAND 96) 32 32 (by omega) := by
    apply Vector.toList_inj.mp; rw [arrayToBytes_toList, hms5]; exact hs5bytes
  have hzseed : arrayToBytes (to_slice_mut_back2 s7)
      = Spec.slice (turboSHAKE256 (skBytes sk ‖ #v[((Spec.Kopis.ℓ p : ℕ) : Byte)])
          DOMSEP_KGEXPAND 96) 64 32 (by omega) := by
    apply Vector.toList_inj.mp; rw [arrayToBytes_toList, hms7]; exact hs7bytes
  -- run the algebraic pipeline
  let* ⟨mat_a, hmata⟩ ← gen_matrix_from_seed_spec L (to_slice_mut_back s3)
  let* ⟨vec_s, hvecs⟩ ← gen_secret_from_seed_spec L MU (to_slice_mut_back1 s5) hMU
  let* ⟨prod, hprod⟩ ← matrix_mul_transpose_spec mat_a vec_s
  -- H1_VAL = 4, Q_BITS - P_BITS = 3, computed via the scalar step specs
  simp only [pke.H1_VAL, consts.MODULUS_Q_BITS, consts.MODULUS_P_BITS]
  let* ⟨j0, hj0, _⟩ ← Std.Usize.sub_spec (x := 13#usize) (y := 10#usize) (by scalar_tac)
  have hj0v : j0.val = 3 := by scalar_tac
  let* ⟨j1, hj1, _⟩ ← Std.Usize.sub_spec (x := j0) (y := 1#usize) (by scalar_tac)
  have hj1v : j1.val = 2 := by scalar_tac
  let* ⟨x16, hx16, _⟩ ← Std.U16.ShiftLeft_spec 1#u16 j1 (by scalar_tac)
  have hx4 : x16 = 4#u16 := by
    apply UScalar.eq_of_val_eq; rw [hx16, hj1v]
    simp [Nat.shiftLeft_eq, U16.size, U16.numBits]
  subst hx4
  let* ⟨prod1, hprod1⟩ ← matrix_wrapping_add_to_all_spec prod 4#u16
  let* ⟨j2, hj2, _⟩ ← Std.Usize.sub_spec (x := 13#usize) (y := 10#usize) (by scalar_tac)
  have hj2v : j2.val = 3 := by scalar_tac
  let* ⟨prod2, hprod2⟩ ← matrix_shift_right_spec prod1 j2 (by scalar_tac)
  let* ⟨pkh, hpkh⟩ ← pke_hash_spec
    { matrix_seed := to_slice_mut_back s3, vec := prod2, mat_a := mat_a } hbuf hfit
  -- matrix seed bytes correspond to the spec's `mat_seed`
  have hmsb : matSeedBytes { matrix_seed := to_slice_mut_back s3, vec := prod2, mat_a := mat_a }
      = Spec.slice (turboSHAKE256 (skBytes sk ‖ #v[((Spec.Kopis.ℓ p : ℕ) : Byte)])
          DOMSEP_KGEXPAND 96) 0 32 (by omega) := by
    apply Vector.toList_inj.mp
    unfold matSeedBytes
    rw [Vector.toList_cast, hmatseed]
  -- the rounded vector corresponds to the spec's `vec_b` (over `L.val`)
  have hvecb : toVecN 10 prod2 = Spec.Kopis.RoundToR10 L.val
      (Spec.Kopis.matVecMul (Matrix.transpose (toMatrix13 mat_a)) (toVector13 vec_s)) := by
    apply Vector.ext
    intro idx hidx
    have hs := hprod2 idx hidx 0 (by omega)
    rw [hj2v] at hs
    simp only [toVecN, Vector.getElem_ofFn]
    exact prod2_roundR10_bridge mat_a vec_s prod prod1 prod2 idx hidx
      (fun i₀ hi₀ => hprod i₀ hi₀ 0 (by omega)) (hprod1 idx hidx 0 (by omega)) hs
  -- the rounded vector, transported to the spec's `ℓ p` index, is the spec's `vec_b`
  have hvecbcast : toVecN 10 prod2 = hℓ ▸ Spec.Kopis.RoundToR10 (Spec.Kopis.ℓ p)
      (Spec.Kopis.matVecMul (Matrix.transpose (Spec.Kopis.GenMat (Spec.Kopis.ℓ p)
          (Spec.slice (turboSHAKE256 (skBytes sk ‖ #v[((Spec.Kopis.ℓ p : ℕ) : Byte)])
            DOMSEP_KGEXPAND 96) 0 32 (by omega))))
        (Spec.Kopis.GenSecret (Spec.Kopis.ℓ p) (Spec.Kopis.μ p)
          (Spec.slice (turboSHAKE256 (skBytes sk ‖ #v[((Spec.Kopis.ℓ p : ℕ) : Byte)])
            DOMSEP_KGEXPAND 96) 32 32 (by omega)))) := by
    rw [hvecb, hmata, hmatseed, hvecs, hsecseed, roundExpr_cast hℓ, hμ]
  simp only [Spec.Kopis.ExpandDecapKey]
  refine ⟨?_, ?_, ?_, ?_, hmata⟩
  · -- secret key
    apply Vector.toList_inj.mp
    rw [eqRec_toList, hvecs, hsecseed, hℓ, hμ]
  · exact hzseed
  · -- public key (serialized bytes)
    unfold pkStructBytes
    apply Vector.toList_inj.mp
    rw [Vector.toList_cast, Vector.toList_cast, bappend_toList, bappend_toList,
      hvecbcast, serialize_eqRec_toList, hmsb]
  · -- public-key hash
    rw [hpkh]
    refine turboSHAKE256_congr _ _ _ _ ?_
    rw [Vector.toList_cast, bappend_toList, bappend_toList,
      hvecbcast, serialize_eqRec_toList, hmsb]

end Kopis.Properties
