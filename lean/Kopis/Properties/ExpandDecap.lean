import Kopis.Properties.PkeHash
import Kopis.Properties.RoundTop
import Kopis.Properties.MulTranspose
import Kopis.Properties.NttBridge
open Aeneas Aeneas.Std Result RustKopisSerial
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
corresponds to the spec's `pk : 𝔹 (pkSize p)`.  With the pubkey refactor the struct stores the
serialized vector bytes verbatim, so this is `vecBytesFlat ‖ matSeedBytes` (byte-level) rather
than a re-serialization of a structured vector. -/
def pkStructBytes {L : Usize} (self : pke.PkePublicKey L) (p : Spec.Kopis.ParameterSet)
    (hℓ : Spec.Kopis.ℓ p = L.val) : 𝔹 (Spec.Kopis.pkSize p) :=
  (vecBytesFlat self ‖ matSeedBytes self).cast (by
    simp only [Spec.Kopis.pkSize, hℓ]; ring)

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

private theorem sliceToBytes_getElem! (s : Slice U8) (m : ℕ) (h : s.length = m) (q : ℕ) (hq : q < m) :
    (sliceToBytes s m h)[q]'hq = (s.val[q]!).bv := by
  simp only [sliceToBytes, Vector.getElem_ofFn]
  rw [getElem!_pos s.val q (by have hh : s.val.length = m := h; omega)]

/-- Loop invariant of `expand_decap_key_loop`: iterating `i ∈ [start, L)` serializes row
`b[i][0]` (10-bit coefficients) into `vec_bytes[i]`, leaving rows before `start` untouched. -/
theorem expand_decap_key_loop_spec {L : Usize}
    (iter : core.ops.range.Range Usize) (b : arithmetic.matrix_arith.Matrix L 1#usize)
    (vec_bytes : Array (Array U8 320#usize) L)
    (hstart : iter.start.val ≤ L.val) (hend : iter.«end».val = L.val)
    (hfit : L.val * 10 * 256 ≤ Usize.max) :
    pke.expand_decap_key_loop iter b vec_bytes
      ⦃ (r : Array (Array U8 320#usize) L) =>
          ∀ i, i < L.val → ∀ c, c < 320 →
            ((r.val[i]!).val[c]!).bv
              = if iter.start.val ≤ i
                then (Spec.Kopis.serialize 10 (toPolyN 10 ((b.val[i]!).val[0]!)))[c]!
                else ((vec_bytes.val[i]!).val[c]!).bv ⦄ := by
  unfold pke.expand_decap_key_loop
  by_cases hlt : iter.start.val < iter.«end».val
  · let* ⟨ o, iter1, ho, hstart', hend' ⟩ ← core.iter.range.IteratorRange.next_Usize_some_spec
    rw [ho]; simp only
    have hi_lt : iter.start.val < L.val := by scalar_tac
    have hbi : iter.start.val < b.val.length := by have := b.property; scalar_tac
    let* ⟨ a, ha ⟩ ← Array.index_usize_spec b iter.start hbi
    have ha0 : (0#usize).val < a.val.length := by have := a.property; scalar_tac
    let* ⟨ re, hre ⟩ ← Array.index_usize_spec a 0#usize ha0
    have hvbi : iter.start.val < vec_bytes.length := by have := vec_bytes.property; scalar_tac
    let* ⟨ a1, index_mut_back, ha1, hback ⟩ ← Array.index_mut_usize_spec vec_bytes iter.start hvbi
    let* ⟨ s, to_slice_mut_back, hs_val, hs_back ⟩ ← Array.to_slice_mut_spec a1
    have hslen : s.val.length = 32 * 10 := by
      have h : a1.val.length = 320 := a1.property; rw [hs_val]; omega
    let* ⟨ s1, hs1len, hs1eq ⟩ ← ring_serialize_spec re s 10#usize 10 rfl ⟨by norm_num, by norm_num⟩ hslen
    have hs1val : s1.val.length = 320 := by have := hs1len; simp only [Slice.length] at this; omega
    have ha2val : (to_slice_mut_back s1).val = s1.val := by
      rw [hs_back]; exact Array.from_slice_val a1 s1 (by rw [hs1val]; rfl)
    -- byte-level serialize characterization of s1
    have hs1byte : ∀ c, (hc : c < 320) → (s1.val[c]!).bv
        = (Spec.Kopis.serialize 10 (toPolyN 10 re))[c]! := by
      intro c hc
      have hcc : c < 32 * 10 := by omega
      rw [← sliceToBytes_getElem! s1 (32 * 10) hs1len c hcc, hs1eq,
        getElem!_pos (Spec.Kopis.serialize 10 (toPolyN 10 re)) c hcc]
    apply WP.spec_mono
      (expand_decap_key_loop_spec iter1 b (index_mut_back (to_slice_mut_back s1))
        (by rw [hstart']; scalar_tac) (by rw [hend']; exact hend) hfit)
    intro r hr i hi c hc
    rw [hr i hi c hc, hstart']
    have hbacki : (index_mut_back (to_slice_mut_back s1)).val
        = vec_bytes.val.set iter.start.val (to_slice_mut_back s1) := by
      rw [hback]; simp only [Array.set_val_eq]
    have hvbl : iter.start.val < vec_bytes.val.length := by
      have := vec_bytes.property; scalar_tac
    by_cases hcase : iter.start.val + 1 ≤ i
    · rw [if_pos hcase, if_pos (by omega : iter.start.val ≤ i)]
    · rw [if_neg hcase, hbacki]
      by_cases hii : i = iter.start.val
      · rw [getElem!_list_set vec_bytes.val iter.start.val (to_slice_mut_back s1) i hvbl,
          if_pos hii, ha2val, hs1byte c hc, if_pos (by omega : iter.start.val ≤ i)]
        have hree : re = (b.val[i]!).val[0]! := by
          have ea : b.val[i]! = a := by
            rw [hii]; exact (getElem!_pos b.val iter.start.val hbi).trans ha.symm
          rw [ea, hre, ← getElem!_pos a.val 0 ha0]
        rw [hree]
      · rw [getElem!_list_set vec_bytes.val iter.start.val (to_slice_mut_back s1) i hvbl,
          if_neg hii, if_neg (by omega : ¬ iter.start.val ≤ i)]
  · let* ⟨ o, iter1, hnone, _ ⟩ ← core.iter.range.IteratorRange.next_Usize_none_spec
    rw [hnone]; simp only [WP.spec_ok]
    have hge : iter.start.val = L.val := by scalar_tac
    intro i hi c hc
    rw [if_neg (by omega : ¬ iter.start.val ≤ i)]
  termination_by iter.«end».val - iter.start.val
  decreasing_by scalar_decr_tac

/-- The flattened `vec_bytes` produced by `expand_decap_key_loop` (from `start = 0`) is exactly
the spec's `PolyVector.serialize 10` of the rounded vector. -/
theorem vecBytesFlat_of_loop {L : Usize} (self : pke.PkePublicKey L)
    (b : arithmetic.matrix_arith.Matrix L 1#usize)
    (hbytes : ∀ i, i < L.val → ∀ c, c < 320 →
      ((self.vec_bytes.val[i]!).val[c]!).bv
        = (Spec.Kopis.serialize 10 (toPolyN 10 ((b.val[i]!).val[0]!)))[c]!) :
    vecBytesFlat self = Spec.Kopis.PolyVector.serialize 10 (toVecN 10 b) := by
  apply Vector.ext
  intro pos hpos
  have hc : pos % 320 < 320 := Nat.mod_lt _ (by norm_num)
  have hi : pos / 320 < L.val := by
    rw [Nat.div_lt_iff_lt_mul (by norm_num)]; omega
  simp only [vecBytesFlat, Vector.getElem_ofFn]
  rw [hbytes (pos / 320) hi (pos % 320) hc,
    getElem!_pos _ (pos % 320) (by omega)]
  simp only [Spec.Kopis.PolyVector.serialize]
  rw [Vector.getElem_flatten (by omega : pos < L.val * (32 * 10)), Vector.getElem_map]
  simp only [toVecN, Vector.getElem_ofFn]

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
    h ▸ (Spec.Kopis.CompressToR10 ℓ (Spec.Kopis.matVecMul
          (Matrix.transpose (Spec.Kopis.GenMat ℓ ms)) (Spec.Kopis.GenSecret ℓ μ ss)))
      = Spec.Kopis.CompressToR10 ℓ' (Spec.Kopis.matVecMul
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

/-- **Rust `expand_decap_key` matches the spec `ExpandSecretKey`.** -/
theorem expand_decap_key_spec (L MU : Usize) (sk : Array U8 32#usize)
    (p : Spec.Kopis.ParameterSet)
    (hℓ : Spec.Kopis.ℓ p = L.val) (hμ : Spec.Kopis.μ p = MU.val)
    (hMU : MU.val = 6 ∨ MU.val = 8 ∨ MU.val = 10)
    (_hbuf : L.val * 320 + 32 ≤ 1312) (hfit : L.val * 10 * 256 ≤ Usize.max)
    (_hL : L.val < 256) :
    pke.expand_decap_key L MU sk
      ⦃ (r : pke.PkeSecretKey L × Array U8 32#usize × pke.PkePublicKey L × Array U8 32#usize) =>
          -- the secret vector `s`: `pke_sk` is its NTT-domain image, it is the spec's secret,
          -- and its coefficients are within the secret bound
          (∃ S : Mat L 1#usize, r.1 = nttFwdS S ∧
              toVector13 S = hℓ ▸ (Spec.Kopis.ExpandSecretKey p (skBytes sk)).1 ∧
              SecretBounded S ((MU.val / 2 : ℕ) : ℤ)) ∧
          arrayToBytes r.2.1 = (Spec.Kopis.ExpandSecretKey p (skBytes sk)).2.1 ∧
          pkStructBytes r.2.2.1 p hℓ = (Spec.Kopis.ExpandSecretKey p (skBytes sk)).2.2.1 ∧
          arrayToBytes r.2.2.2 = (Spec.Kopis.ExpandSecretKey p (skBytes sk)).2.2.2 ∧
          -- the public matrix `A`: `mat_a_ntt` is its NTT-domain image, and it is `GenMat`
          (∃ Amat : Mat L L, r.2.2.1.mat_a_ntt = nttFwdU Amat ∧
              toMatrix13 Amat = Spec.Kopis.GenMat L.val (arrayToBytes r.2.2.1.matrix_seed) ∧
              UniformBounded Amat) ∧
          -- the public vector `b`: `vec_ntt` is its NTT-domain image, and `vec_bytes` is its
          -- serialization
          (∃ V : Mat L 1#usize, r.2.2.1.vec_ntt = nttFwdU V ∧
              UniformBounded V ∧
              vecBytesFlat r.2.2.1 = Spec.Kopis.PolyVector.serialize 10 (toVecN 10 V)) ⦄ := by
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
    rw [Slice.length, s2_post1]; simp
  have hs4len : s4.length = 32 := by
    rw [Slice.length, s4_post1]; simp
  have hs6len : s6.length = 32 := by
    rw [Slice.length, s6_post1]; simp
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
  let* ⟨mat_a, hmata, hmatbnd⟩ ← spec_and (gen_matrix_from_seed_spec L (to_slice_mut_back s3))
    (gen_matrix_uniformBounded (to_slice_mut_back s3))
  let* ⟨vec_s, hvecs, hvecbnd⟩ ← spec_and (gen_secret_from_seed_spec L MU (to_slice_mut_back1 s5) hMU)
    (gen_secret_secretBounded (to_slice_mut_back1 s5) hMU)
  let* ⟨mat_a_ntt, hmata_ntt⟩ ← from_uniform_matrix_spec mat_a
  have hsb : ((MU.val / 2 : ℕ) : ℤ) ≤ 3840 := by
    rcases hMU with h | h | h <;> rw [h] <;> norm_num
  have hsm : SecretSmall vec_s := secretSmall_of_bounded hvecbnd hsb
  let* ⟨vec_s_ntt, hvecs_ntt⟩ ← from_secret_matrix_spec vec_s hsm
  -- the NTT `mul_transpose` computes the schoolbook product `mat_aᵀ · vec_s`
  have hfitex : fitsExactly L.val ((MU.val / 2 : ℕ) : ℤ) := by
    have h := fitsExactly_paramSet p; rw [hℓ, hμ] at h; exact h
  -- The multiplier spec is stated over the *coefficient* matrices; the stored NTT matrices are
  -- their forward images, so rewrite the spec (not the goal — rewriting the goal would perturb
  -- the program term and break the `let*` matching that follows).
  have hL4 : L.val ≤ 4 := by rw [← hℓ]; cases p <;> decide
  have hmt := ntt_mul_transpose_spec mat_a vec_s ((MU.val / 2 : ℕ) : ℤ) hfitex hmatbnd hvecbnd hL4 hsb
  rw [← hmata_ntt, ← hvecs_ntt] at hmt
  let* ⟨prod, hprod0⟩ ← hmt
  have hprod : ∀ (j : ℕ), j < L.val → ∀ (k : ℕ), k < 1 →
      toRingElem ((prod.val[j]!).val[k]!) = ∑ ii ∈ Finset.range L.val,
        toRingElem ((mat_a.val[ii]!).val[j]!) * toRingElem ((vec_s.val[ii]!).val[k]!) := by
    intro j hj k hk; exact hprod0 j hj k hk
  -- `H1_VAL = 1 << (13 - 10 - 1)` is a closed term (the shift amount is now `i32` arithmetic
  -- on literals), so evaluate it rather than stepping it.
  have hH1 : pke.H1_VAL = ok 4#u16 := by unfold pke.H1_VAL; rfl
  simp only [hH1, bind_tc_ok]
  let* ⟨prod1, hprod1⟩ ← matrix_wrapping_add_to_all_spec prod 4#u16
  let* ⟨j2, hj2, _⟩ ← Std.Usize.sub_spec (x := 13#usize) (y := 10#usize) (by scalar_tac)
  have hj2v : j2.val = 3 := by scalar_tac
  let* ⟨prod2, hprod2, hprod2bnd⟩ ← spec_and (matrix_shift_right_spec prod1 j2 (by scalar_tac))
    (shift_right_uniformBounded prod1 j2 hj2v)
  -- from_uniform of the rounded vector, then serialize each row into `vec_bytes`
  let* ⟨vec_ntt, hvecntt⟩ ← from_uniform_matrix_spec prod2
  let* ⟨vec_bytes1, hvb⟩ ← expand_decap_key_loop_spec { start := 0#usize, «end» := L } prod2
    (Array.repeat L (Array.repeat 320#usize 0#u8)) (by simp) rfl hfit
  let* ⟨pkh, hpkh⟩ ← pke_hash_spec
    { matrix_seed := to_slice_mut_back s3, mat_a_ntt := mat_a_ntt, vec_bytes := vec_bytes1,
      vec_ntt := vec_ntt }
  -- the serialized rows equal the spec `serialize` of the rounded vector
  have hbytes : ∀ i, i < L.val → ∀ c, c < 320 →
      ((vec_bytes1.val[i]!).val[c]!).bv
        = (Spec.Kopis.serialize 10 (toPolyN 10 ((prod2.val[i]!).val[0]!)))[c]! := by
    intro i hi c hc
    have h := hvb i hi c hc
    rwa [if_pos (by scalar_tac)] at h
  -- matrix seed bytes correspond to the spec's `mat_seed`
  have hmsb : matSeedBytes ({ matrix_seed := to_slice_mut_back s3, mat_a_ntt := mat_a_ntt, vec_bytes := vec_bytes1, vec_ntt := vec_ntt } : pke.PkePublicKey L)
      = Spec.slice (turboSHAKE256 (skBytes sk ‖ #v[((Spec.Kopis.ℓ p : ℕ) : Byte)])
          DOMSEP_KGEXPAND 96) 0 32 (by omega) := by
    apply Vector.toList_inj.mp
    unfold matSeedBytes
    rw [Vector.toList_cast, hmatseed]
  -- the rounded vector corresponds to the spec's `vec_b` (over `L.val`)
  have hvecb : toVecN 10 prod2 = Spec.Kopis.CompressToR10 L.val
      (Spec.Kopis.matVecMul (Matrix.transpose (toMatrix13 mat_a)) (toVector13 vec_s)) := by
    apply Vector.ext
    intro idx hidx
    have hs := hprod2 idx hidx 0 (by omega)
    rw [hj2v] at hs
    simp only [toVecN, Vector.getElem_ofFn]
    exact prod2_roundR10_bridge mat_a vec_s prod prod1 prod2 idx hidx
      (fun i₀ hi₀ => hprod i₀ hi₀ 0 (by omega)) (hprod1 idx hidx 0 (by omega)) hs
  -- the rounded vector, transported to the spec's `ℓ p` index, is the spec's `vec_b`
  have hvecbcast : toVecN 10 prod2 = hℓ ▸ Spec.Kopis.CompressToR10 (Spec.Kopis.ℓ p)
      (Spec.Kopis.matVecMul (Matrix.transpose (Spec.Kopis.GenMat (Spec.Kopis.ℓ p)
          (Spec.slice (turboSHAKE256 (skBytes sk ‖ #v[((Spec.Kopis.ℓ p : ℕ) : Byte)])
            DOMSEP_KGEXPAND 96) 0 32 (by omega))))
        (Spec.Kopis.GenSecret (Spec.Kopis.ℓ p) (Spec.Kopis.μ p)
          (Spec.slice (turboSHAKE256 (skBytes sk ‖ #v[((Spec.Kopis.ℓ p : ℕ) : Byte)])
            DOMSEP_KGEXPAND 96) 32 32 (by omega)))) := by
    rw [hvecb, hmata, hmatseed, hvecs, hsecseed, roundExpr_cast hℓ, hμ]
  simp only [Spec.Kopis.ExpandSecretKey]
  refine ⟨⟨vec_s, hvecs_ntt, ?_, hvecbnd⟩, hzseed, ?_, ?_,
          ⟨mat_a, hmata_ntt, hmata, hmatbnd⟩, ⟨prod2, hvecntt, hprod2bnd, ?_⟩⟩
  · -- the secret vector is the spec's secret
    apply Vector.toList_inj.mp
    rw [eqRec_toList, hvecs, hsecseed, hℓ, hμ]
  · -- public key (serialized bytes)
    unfold pkStructBytes
    apply Vector.toList_inj.mp
    rw [vecBytesFlat_of_loop _ prod2 hbytes, hvecbcast]
    simp only [Vector.toList_cast, bappend_toList]
    rw [serialize_eqRec_toList, hmsb]
  · -- public-key hash
    rw [hpkh]
    refine turboSHAKE256_congr _ _ _ _ ?_
    rw [vecBytesFlat_of_loop _ prod2 hbytes, hvecbcast]
    simp only [Vector.toList_cast, bappend_toList]
    rw [serialize_eqRec_toList, hmsb]
  · -- vec_bytes are the serialization of the public vector
    rw [vecBytesFlat_of_loop _ prod2 hbytes]

end Kopis.Properties
