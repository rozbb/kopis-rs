import Kopis.Properties.GenSecretSpec
open Aeneas Aeneas.Std Result RustKopisSerial
open scoped BigOperators
open Spec (𝔹 bytesToBits)
open scoped Spec.Notations
open Spec.TurboSHAKE (turboSHAKE256)
open Spec.Kopis (DOMSEP_GENSEC)
namespace Kopis.Properties

set_option maxHeartbeats 2000000
set_option maxRecDepth 4000

private theorem getElem!_list_set {α : Type _} [Inhabited α] (l : List α) (j : ℕ)
    (v : α) (k : ℕ) (hj : j < l.length) : (l.set j v)[k]! = if k = j then v else l[k]! := by
  by_cases h : k = j
  · subst h
    rw [getElem!_pos _ k (by rw [List.length_set]; exact hj), List.getElem_set_self, if_pos rfl]
  · by_cases hk : k < l.length
    · rw [getElem!_pos _ k (by rw [List.length_set]; exact hk),
        List.getElem_set_of_ne (Ne.symm h), ← getElem!_pos _ k hk, if_neg h]
    · rw [getElem!_neg _ k (by rw [List.length_set]; exact hk), getElem!_neg _ k hk, if_neg h]

theorem domsep_gensec_bv : (3#u8).bv = DOMSEP_GENSEC := by decide

theorem turboSHAKE256_cast {n m : ℕ} (h : n = m) (v : 𝔹 n) (D : Byte) (outLen : ℕ) :
    turboSHAKE256 (v.cast h) D outLen = turboSHAKE256 v D outLen := by
  subst h; rw [Vector.cast_rfl]

/-- Byte-concat bridge (single index byte): `seed ++ [ci]` is `arrayToBytes seed ‖ #v[ci]`. -/
theorem turboSHAKE256_u8concat (seed : Array U8 32#usize) (ci : U8) (outLen : ℕ) (D : Byte) :
    turboSHAKE256 (u8ListToBytes (seed.val ++ [ci])) D outLen
      = turboSHAKE256 (arrayToBytes seed ‖ #v[ci.bv]) D outLen := by
  have h32 : seed.val.length = 32 := seed.property
  have hlen : (seed.val ++ [ci]).length = 33 := by
    simp only [List.length_append, List.length_cons, List.length_nil]; omega
  have htl : (u8ListToBytes (seed.val ++ [ci])).toList = (arrayToBytes seed ‖ #v[ci.bv]).toList := by
    have e2 : (arrayToBytes seed).toList = seed.val.map (·.bv) := by
      apply List.ext_getElem
      · simp [arrayToBytes, h32]
      · intro k h1 h2; simp [arrayToBytes, List.getElem_map]
    have e1 : (u8ListToBytes (seed.val ++ [ci])).toList = (seed.val ++ [ci]).map (·.bv) := by
      simp only [u8ListToBytes, Vector.toList_ofFn]; rw [List.ofFn_getElem_eq_map]
    rw [e1]
    show (seed.val ++ [ci]).map (·.bv) = (arrayToBytes seed ++ #v[ci.bv]).toList
    simp [Vector.toList_push, e2, List.map_append]
  have hmsg : u8ListToBytes (seed.val ++ [ci]) = (arrayToBytes seed ‖ #v[ci.bv]).cast hlen.symm := by
    apply Vector.toList_inj.mp; rw [Vector.toList_cast]; exact htl
  rw [hmsg]; exact turboSHAKE256_cast hlen.symm _ D outLen

/-- Interpret the Rust column matrix `Matrix L 1` as a spec `PolyVector (2¹³) L`. -/
def toVector13 {L : Usize} (secret : arithmetic.matrix_arith.Matrix L 1#usize) :
    Spec.Kopis.PolyVector (2 ^ 13) (L : ℕ) :=
  Vector.ofFn fun (a : Fin (L : ℕ)) => toRingElem13 ((secret.val[a.val]!).val[0]!)

/-- **Outer loop spec.**  Fills rows `[iter.start, L)` of the secret column with their
CBD samples. -/
theorem gen_secret_from_seed_loop_spec {L : Usize} (MU : Usize)
    (iter : core.ops.range.Range Usize) (seed : Array U8 32#usize)
    (secret : arithmetic.matrix_arith.Matrix L 1#usize) (buf : Slice U8)
    (hMU : MU.val = 6 ∨ MU.val = 8 ∨ MU.val = 10)
    (hbuflen : buf.val.length = 32 * MU.val)
    (hstart : iter.start.val ≤ L.val) (hend : iter.«end».val = L.val) :
    sample.gen_secret_from_seed_loop MU iter seed secret buf
      ⦃ (result : arithmetic.matrix_arith.Matrix L 1#usize) =>
          ∀ (a : ℕ) (_ : a < L.val),
            toRingElem13 ((result.val[a]!).val[0]!)
              = if iter.start.val ≤ a
                then (Spec.Kopis.GenSecret L.val MU.val (arrayToBytes seed))[a]!
                else toRingElem13 ((secret.val[a]!).val[0]!) ⦄ := by
  unfold sample.gen_secret_from_seed_loop
  by_cases hlt : iter.start.val < iter.«end».val
  · let* ⟨ o, iter1, ho, hstart', hend' ⟩ ← core.iter.range.IteratorRange.next_Usize_some_spec
    rw [ho]; simp only
    have hi_lt : iter.start.val < L.val := by scalar_tac
    step*
    have habs : hasherAbsorbed hasher2 = seed.val ++ [UScalar.cast .U8 iter.start] := by
      rw [hasher2_post, hasher1_post, hasher_post, s_post, s1_post, i1_post]; rfl
    have hbuf1_len : buf1.val.length = 32 * MU.val := by
      rw [← Slice.length, __post1, Slice.length, hbuflen]
    have hbridge : sliceToBytes buf1 (32 * MU.val) hbuf1_len
        = turboSHAKE256 (arrayToBytes seed ‖ #v[((iter.start.val : ℕ) : Byte)])
            DOMSEP_GENSEC (32 * MU.val) := by
      apply Vector.toList_inj.mp
      rw [reader_post1] at __post2
      dsimp only at __post2
      rw [reader_post2, Nat.zero_add, List.drop_zero] at __post2
      rw [habs] at __post2
      have hbuflen' : buf.length = 32 * MU.val := by rw [Slice.length]; exact hbuflen
      have hsl : (sliceToBytes buf1 (32 * MU.val) hbuf1_len).toList = buf1.val.map (·.bv) := by
        apply List.ext_getElem
        · simp only [sliceToBytes, Vector.toList_length, List.length_map, hbuf1_len]
        · intro q h1 h2
          simp only [sliceToBytes, Vector.getElem_toList, Vector.getElem_ofFn, List.getElem_map]
      rw [hsl, __post2, hbuflen', turboSHAKE256_u8concat]
      simp only [cast_u8_bv, domsep_gensec_bv]
    let* ⟨ re1, hre1 ⟩ ← cbd_spec MU buf1 re hMU hbuf1_len
    have hrow_eq : toRingElem13 re1
        = (Spec.Kopis.GenSecret L.val MU.val (arrayToBytes seed))[iter.start.val]'hi_lt :=
      cbd_row_eq_genSecret L MU.val (arrayToBytes seed) buf1 re1 iter.start.val hi_lt
        hbuf1_len hbridge hre1
    have h_start_new : iter1.start.val ≤ L.val := by rw [hstart']; scalar_tac
    have h_end_new : iter1.«end».val = L.val := by rw [hend']; exact hend
    apply WP.spec_mono
      (gen_secret_from_seed_loop_spec MU iter1 seed (index_mut_back (index_mut_back1 re1)) buf1
        hMU hbuf1_len h_start_new h_end_new)
    rintro r hr a ha
    rw [hr a ha, hstart']
    have harr0 : ∀ (arr : Std.Array arithmetic.ring_arith.RingElem 1#usize)
        (v : arithmetic.ring_arith.RingElem), (arr.set 0#usize v).val[0]! = v := fun arr v => by
      rw [Std.Array.set_val_eq]
      show (arr.val.set 0 v)[0]! = v
      rw [getElem!_list_set _ 0 v 0 (by rw [arr.property]; decide), if_pos rfl]
    have hml : iter.start.val < secret.val.length := by have := secret.property; omega
    have hM : (index_mut_back (index_mut_back1 re1)).val[a]!
        = if a = iter.start.val then (index_mut_back1 re1) else secret.val[a]! := by
      rw [a_post2, Std.Array.set_val_eq, getElem!_list_set _ _ _ _ hml]
    by_cases h1 : iter.start.val + 1 ≤ a
    · rw [if_pos h1, if_pos (by omega)]
    · rw [if_neg h1]
      by_cases h2 : iter.start.val ≤ a
      · have ha_eq : a = iter.start.val := by omega
        rw [if_pos h2, hM, if_pos ha_eq, re_post2, harr0, hrow_eq, ha_eq,
          getElem!_pos _ iter.start.val hi_lt]
      · rw [if_neg h2, hM, if_neg (by omega : ¬ a = iter.start.val)]
  · let* ⟨ o, iter1, hnone, _ ⟩ ← core.iter.range.IteratorRange.next_Usize_none_spec
    rw [hnone]; simp only [WP.spec_ok]
    intro a ha
    rw [if_neg (by scalar_tac)]

/-- **`gen_secret_from_seed` correctness.**  The Rust secret-key sampler produces exactly
the spec's `GenSecret` vector (mod `2¹³`). -/
theorem gen_secret_from_seed_spec (L MU : Usize) (seed : Array U8 32#usize)
    (hMU : MU.val = 6 ∨ MU.val = 8 ∨ MU.val = 10) :
    sample.gen_secret_from_seed L MU seed
      ⦃ (r : arithmetic.matrix_arith.Matrix L 1#usize) =>
          toVector13 r = Spec.Kopis.GenSecret L.val MU.val (arrayToBytes seed) ⦄ := by
  unfold sample.gen_secret_from_seed
  simp only [arithmetic.matrix_arith.Matrix.Insts.CoreDefaultDefault.default,
    arithmetic.ring_arith.RingElem.Insts.CoreDefaultDefault.default, bind_tc_ok, consts.RING_DEG]
  have hMUle : MU.val ≤ 10 := by omega
  let* ⟨ i, hi ⟩ ← Std.Usize.mul_spec (show (256#usize).val * MU.val ≤ Usize.max by
    rw [show (256#usize).val = 256 from rfl]
    calc 256 * MU.val ≤ 256 * 10 := by omega
      _ ≤ Usize.max := by scalar_tac)
  let* ⟨ i1, hi1 ⟩ ← Std.Usize.div_spec
  have hiv : i.val = 256 * MU.val := by rw [hi]
  have hi1v : i1.val = 32 * MU.val := by rw [hi1, hiv]; omega
  simp only [core.array.Array.index_mut, core.ops.index.IndexMutSlice,
    core.slice.index.Slice.index_mut, core.slice.index.SliceIndexRangeToUsizeSlice.index_mut]
  have h320 : (Array.repeat 320#usize 0#u8).to_slice.length = 320 := by
    simp [Array.to_slice, Slice.length, Array.repeat]
  rw [if_pos (show i1.val ≤ (Array.repeat 320#usize 0#u8).to_slice.length by rw [h320, hi1v]; omega)]
  simp only [bind_tc_ok]
  apply WP.spec_mono
    (gen_secret_from_seed_loop_spec MU { start := 0#usize, «end» := L } seed _ _ hMU ?buflen
      (by simp) rfl)
  case buflen =>
    show (List.slice 0 i1.val (Array.repeat 320#usize 0#u8).to_slice.val).length = 32 * MU.val
    rw [List.slice_length]
    have : (Array.repeat 320#usize 0#u8).to_slice.val.length = 320 := by rw [← Slice.length, h320]
    rw [this, hi1v]; omega
  intro r hr
  apply Vector.ext
  intro a ha
  rw [toVector13, Vector.getElem_ofFn]
  have key := hr a ha
  rw [show (({ start := 0#usize, «end» := L } : core.ops.range.Range Usize).start.val) = 0 from rfl,
    if_pos (Nat.zero_le _)] at key
  rw [key, getElem!_pos _ a ha]

/-! ## Signed-magnitude bound (centered-binomial `|coeff| ≤ μ/2`) -/

/-- **Outer loop, magnitude version.**  Every coefficient of every row of the secret column,
as a small-signed `u16`, has magnitude `≤ μ/2`.  Same skeleton as `gen_secret_from_seed_loop_spec`
with the SHAKE/`cbdVal` value reasoning stripped, using `cbd_bd`. -/
theorem gen_secret_from_seed_loop_bd {L : Usize} (MU : Usize)
    (iter : core.ops.range.Range Usize) (seed : Array U8 32#usize)
    (secret : arithmetic.matrix_arith.Matrix L 1#usize) (buf : Slice U8)
    (hMU : MU.val = 6 ∨ MU.val = 8 ∨ MU.val = 10)
    (hbuflen : buf.val.length = 32 * MU.val) (hend : iter.«end».val = L.val)
    (hsec : ∀ a (_ha : a < L.val) c (_hc : c < 256),
        smallSignedU16 (((secret.val[a]!).val[0]!).val[c]!) (MU.val / 2)) :
    sample.gen_secret_from_seed_loop MU iter seed secret buf
      ⦃ (r : arithmetic.matrix_arith.Matrix L 1#usize) =>
          ∀ a (_ha : a < L.val) c (_hc : c < 256),
            smallSignedU16 (((r.val[a]!).val[0]!).val[c]!) (MU.val / 2) ⦄ := by
  unfold sample.gen_secret_from_seed_loop
  by_cases hlt : iter.start.val < iter.«end».val
  · let* ⟨ o, iter1, ho, hstart', hend' ⟩ ← core.iter.range.IteratorRange.next_Usize_some_spec
    rw [ho]; simp only
    have hi_lt : iter.start.val < L.val := by scalar_tac
    step*
    have hbuf1_len : buf1.val.length = 32 * MU.val := by
      rw [← Slice.length, __post1, Slice.length, hbuflen]
    let* ⟨ re1, hre1 ⟩ ← cbd_bd MU buf1 re hMU hbuf1_len
    have h_end_new : iter1.«end».val = L.val := by rw [hend']; exact hend
    have harr0 : ∀ (arr : Std.Array arithmetic.ring_arith.RingElem 1#usize)
        (v : arithmetic.ring_arith.RingElem), (arr.set 0#usize v).val[0]! = v := fun arr v => by
      rw [Std.Array.set_val_eq]
      show (arr.val.set 0 v)[0]! = v
      rw [getElem!_list_set _ 0 v 0 (by rw [arr.property]; decide), if_pos rfl]
    have hml : iter.start.val < secret.val.length := by have := secret.property; omega
    apply WP.spec_mono
      (gen_secret_from_seed_loop_bd MU iter1 seed (index_mut_back (index_mut_back1 re1)) buf1
        hMU hbuf1_len h_end_new ?sec')
    · rintro r hr a ha c hc; exact hr a ha c hc
    · intro a ha c hc
      have hM : (index_mut_back (index_mut_back1 re1)).val[a]!
          = if a = iter.start.val then (index_mut_back1 re1) else secret.val[a]! := by
        rw [a_post2, Std.Array.set_val_eq, getElem!_list_set _ _ _ _ hml]
      rw [hM]
      by_cases hai : a = iter.start.val
      · rw [if_pos hai, re_post2, harr0]
        exact hre1 c hc
      · rw [if_neg hai]
        exact hsec a ha c hc
  · let* ⟨ o, iter1, hnone, _ ⟩ ← core.iter.range.IteratorRange.next_Usize_none_spec
    rw [hnone]; simp only [WP.spec_ok]
    exact hsec

/-- **`gen_secret_from_seed` signed-magnitude bound.**  Every coefficient, read as a small-signed
`u16`, has magnitude `≤ μ/2` (for the shipped `μ ∈ {6, 8, 10}`). -/
theorem gen_secret_from_seed_bd (L MU : Usize) (seed : Array U8 32#usize)
    (hMU : MU.val = 6 ∨ MU.val = 8 ∨ MU.val = 10) :
    sample.gen_secret_from_seed L MU seed
      ⦃ (r : arithmetic.matrix_arith.Matrix L 1#usize) =>
          ∀ a (_ha : a < L.val) c (_hc : c < 256),
            smallSignedU16 (((r.val[a]!).val[0]!).val[c]!) (MU.val / 2) ⦄ := by
  unfold sample.gen_secret_from_seed
  simp only [arithmetic.matrix_arith.Matrix.Insts.CoreDefaultDefault.default,
    arithmetic.ring_arith.RingElem.Insts.CoreDefaultDefault.default, bind_tc_ok, consts.RING_DEG]
  have hMUle : MU.val ≤ 10 := by omega
  let* ⟨ i, hi ⟩ ← Std.Usize.mul_spec (show (256#usize).val * MU.val ≤ Usize.max by
    rw [show (256#usize).val = 256 from rfl]
    calc 256 * MU.val ≤ 256 * 10 := by omega
      _ ≤ Usize.max := by scalar_tac)
  let* ⟨ i1, hi1 ⟩ ← Std.Usize.div_spec
  have hiv : i.val = 256 * MU.val := by rw [hi]
  have hi1v : i1.val = 32 * MU.val := by rw [hi1, hiv]; omega
  simp only [core.array.Array.index_mut, core.ops.index.IndexMutSlice,
    core.slice.index.Slice.index_mut, core.slice.index.SliceIndexRangeToUsizeSlice.index_mut]
  have h320 : (Array.repeat 320#usize 0#u8).to_slice.length = 320 := by
    simp [Array.to_slice, Slice.length, Array.repeat]
  rw [if_pos (show i1.val ≤ (Array.repeat 320#usize 0#u8).to_slice.length by rw [h320, hi1v]; omega)]
  simp only [bind_tc_ok]
  apply WP.spec_mono
    (gen_secret_from_seed_loop_bd MU { start := 0#usize, «end» := L } seed _ _ hMU ?buflen rfl ?sec)
  · intro r hr; exact hr
  case buflen =>
    show (List.slice 0 i1.val (Array.repeat 320#usize 0#u8).to_slice.val).length = 32 * MU.val
    rw [List.slice_length]
    have : (Array.repeat 320#usize 0#u8).to_slice.val.length = 320 := by rw [← Slice.length, h320]
    rw [this, hi1v]; omega
  case sec =>
    intro a _ha c hc
    rw [Array.repeat_val, getElem!_pos _ a (by rw [List.length_replicate]; exact _ha),
      List.getElem_replicate, Array.repeat_val,
      getElem!_pos _ 0 (by rw [List.length_replicate]; norm_num), List.getElem_replicate,
      Array.repeat_val, getElem!_pos _ c (by rw [List.length_replicate]; exact hc),
      List.getElem_replicate]
    exact Or.inl (Nat.zero_le _)

end Kopis.Properties
