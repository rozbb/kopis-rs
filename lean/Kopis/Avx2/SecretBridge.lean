/-
  # Kopis/Avx2/SecretBridge.lean — the AVX2 secret sampler against the spec.

  The same shape as `SampleBridge.lean`'s matrix path, one dimension lower: one lane per row, a
  one-byte suffix, `cbd` instead of `deserialize`, and `xof4` at rate 136 (TurboSHAKE256) rather
  than 168.

  Split from `SampleBridge.lean` only to break an import cycle: this needs `GenSecretSpec`, which
  transitively imports the `GenMatrix` twin, which imports `SampleBridge` for the matrix dispatch.
-/
import Kopis.Avx2.SampleBridge
import Kopis.Avx2.CbdEq
import Kopis.Avx2.Properties.GenSecretSpec

open Aeneas Aeneas.Std Result
open RustKopisAvx2
open Kopis.Avx2
open Kopis.Avx2.Keccak (min_usize_eq getElem!_list_set bytesOf msgOf getElem!_bytesOf
  getElem!_msgOf xof4_turboSHAKE)
open Kopis.Properties (streamNat)
open Spec (𝔹)
open scoped Spec.Notations
open Spec.TurboSHAKE (turboSHAKE256)
open arithmetic.ring_arith (RingElem)

namespace Kopis.Avx2.Properties

set_option maxHeartbeats 4000000
set_option maxRecDepth 2000000

noncomputable section

/-! ## The secret sampler

Same shape as the matrix sampler, one dimension lower: one lane per row, a one-byte suffix, and
`cbd` instead of `deserialize`.  `xof4` runs at rate 136 (TurboSHAKE256) rather than 168. -/

/-- **The secret sampler's index loop.**  Lane `lane` carries the row it will sample, clamped to
the last row so the trailing lanes of a short vector hash something harmless. -/
theorem secret_loop0_spec (L : Std.Usize) (iter : core.ops.range.Range Std.Usize)
    (indices : Std.Array (Std.Array Std.U8 1#usize) 4#usize)
    (hL : 0 < L.val) (hend : iter.«end».val = 4) (hstart : iter.start.val ≤ 4)
    (hpre : ∀ lane < iter.start.val,
      ((indices.val[lane]!).val[0]!).bv = ((min lane (L.val - 1) : ℕ) : Byte)) :
    backend.avx2.sample.secret_loop0 L iter indices
      ⦃ (r : Std.Array (Std.Array Std.U8 1#usize) 4#usize) => ∀ lane < 4,
          ((r.val[lane]!).val[0]!).bv = ((min lane (L.val - 1) : ℕ) : Byte) ⦄ := by
  unfold backend.avx2.sample.secret_loop0
  by_cases hlt : iter.start.val < iter.«end».val
  · let* ⟨ o, iter1, ho, hstart', hend' ⟩ ← core.iter.range.IteratorRange.next_Usize_some_spec
    rw [ho]; simp only
    have hl4 : iter.start.val < 4 := by scalar_tac
    let* ⟨ i, hi ⟩ ← Std.Usize.sub_spec (x := L) (y := 1#usize) (by scalar_tac)
    rw [min_usize_eq, bind_tc_ok]
    have hiv : i.val = L.val - 1 := hi
    have hmv : ((if iter.start.val < i.val then iter.start else i) : Std.Usize).val
        = min iter.start.val (L.val - 1) := by
      split <;> omega
    have hilen : (indices.val : List (Std.Array Std.U8 1#usize)).length = 4 := indices.property
    have hlen1 : ∀ (r : Std.Array Std.U8 1#usize), (r.val : List Std.U8).length = 1 :=
      fun r => r.property
    let* ⟨ row, back, hrow, hback ⟩ ← Array.index_mut_usize_spec indices iter.start (by scalar_tac)
    rw [show (lift (Std.UScalar.cast .U8 (if iter.start.val < i.val then iter.start else i))
        : Result Std.U8)
      = ok (Std.UScalar.cast .U8 (if iter.start.val < i.val then iter.start else i)) from rfl,
      bind_tc_ok]
    let* ⟨ row1, hrow1 ⟩ ← Array.update_spec
    have u0 : ((0#usize : Std.Usize) : ℕ) = 0 := rfl
    have hpre' : ∀ lane < iter1.start.val,
        (((back row1).val[lane]!).val[0]!).bv = ((min lane (L.val - 1) : ℕ) : Byte) := by
      intro lane hlane
      rw [hstart'] at hlane
      rw [hback, Std.Array.set_val_eq,
        getElem!_list_set indices.val iter.start.val row1 lane (by rw [hilen]; exact hl4)]
      by_cases h : lane = iter.start.val
      · rw [if_pos h, h, hrow1, Std.Array.set_val_eq, u0,
          getElem!_list_set row.val 0 _ 0 (by rw [hlen1]; omega), if_pos rfl,
          show Std.U8.bv (Std.UScalar.cast .U8
              (if iter.start.val < i.val then iter.start else i))
            = (((if iter.start.val < i.val then iter.start else i) : Std.Usize).val : Byte)
            from usize_cast_u8_bv _, hmv]
      · rw [if_neg h]; exact hpre lane (by omega)
    apply WP.spec_mono
      (secret_loop0_spec L iter1 (back row1) hL (by rw [hend']; exact hend)
        (by rw [hstart']; omega) hpre')
    intro r hr
    exact hr
  · let* ⟨ o, iter1, hnone, _ ⟩ ← core.iter.range.IteratorRange.next_Usize_none_spec
    rw [hnone]; simp only [WP.spec_ok]
    intro lane hlane
    exact hpre lane (by omega)
  termination_by iter.«end».val - iter.start.val
  decreasing_by simp only [hend']; omega

/-- `sliceToBytes` depends only on the underlying bytes, not on which slice carries them. -/
theorem sliceToBytes_congr (s1 s2 : Slice Std.U8) (n : ℕ)
    (h1 : s1.length = n) (h2 : s2.length = n) (h : s1.val = s2.val) :
    sliceToBytes s1 n h1 = sliceToBytes s2 n h2 := by
  apply Vector.ext
  intro j hj
  simp only [sliceToBytes, Vector.getElem_ofFn, h]

/-- **The secret sampler's CBD loop.**  One row per lane: unpack that lane's buffer through the
vector `cbd` and store it.  `avx2_cbd_eq` makes the vector sampler the portable one, so the
serial `cbd_spec` and `cbd_row_eq_genSecret` carry the rest. -/
theorem secret_loop1_spec {L : Std.Usize} (MU : Std.Usize) {N : Std.Usize}
    (iter : core.ops.range.Range Std.Usize)
    (bufs : Std.Array (Std.Array Std.U8 N) 4#usize)
    (secret : arithmetic.matrix_arith.Matrix L 1#usize) (seed : Std.Array Std.U8 32#usize)
    (hMU : MU.val = 6 ∨ MU.val = 8 ∨ MU.val = 10)
    (hL4 : L.val ≤ 4) (hend : iter.«end».val = L.val) (hstart : iter.start.val ≤ L.val)
    (hN : N.val = 32 * MU.val)
    (hbridge : ∀ (i : ℕ) (_hi : i < L.val)
        (hs : (Std.Array.to_slice (bufs.val[i]!)).length = 32 * MU.val),
      sliceToBytes (Std.Array.to_slice (bufs.val[i]!)) (32 * MU.val) hs
        = turboSHAKE256 (arrayToBytes seed ‖ #v[(i : Byte)])
            Spec.Kopis.DOMSEP_GENSEC (32 * MU.val)) :
    backend.avx2.sample.secret_loop1 MU iter bufs secret
      ⦃ (r : arithmetic.matrix_arith.Matrix L 1#usize) => ∀ a < L.val,
          toRingElem13 ((r.val[a]!).val[0]!)
            = if iter.start.val ≤ a
              then (Spec.Kopis.GenSecret L.val MU.val (arrayToBytes seed))[a]!
              else toRingElem13 ((secret.val[a]!).val[0]!) ⦄ := by
  unfold backend.avx2.sample.secret_loop1
  by_cases hlt : iter.start.val < iter.«end».val
  · let* ⟨ o, iter1, ho, hstart', hend' ⟩ ← core.iter.range.IteratorRange.next_Usize_some_spec
    rw [ho]; simp only
    have hi_lt : iter.start.val < L.val := by scalar_tac
    let* ⟨ buf, hbuf ⟩ ← Array.index_usize_spec bufs iter.start (by scalar_tac)
    have hbufv : buf = bufs.val[iter.start.val]! :=
      hbuf.trans (getElem!_pos bufs.val iter.start.val (by scalar_tac)).symm
    have hblen : (buf.val : List Std.U8).length = N.val := buf.property
    simp only [consts.RING_DEG]
    let* ⟨ i1, hi1 ⟩ ← Std.Usize.mul_spec (x := 256#usize) (y := MU) (by scalar_tac)
    let* ⟨ i2, hi2 ⟩ ← Std.Usize.div_spec
    have hi2v : i2.val = 32 * MU.val := by rw [hi2, hi1]; omega
    have hslice : core.slice.index.SliceIndexRangeToUsizeSlice.index
        ({ «end» := i2 } : core.ops.range.RangeTo Std.Usize) (Std.Array.to_slice buf)
      ⦃ (sl : Slice Std.U8) => sl.val = buf.val ⦄ := by
      unfold core.slice.index.SliceIndexRangeToUsizeSlice.index
      rw [if_pos (by simp only [Std.Array.to_slice, Slice.length]; scalar_tac)]
      simp only [WP.spec_ok, Std.Array.to_slice]
      apply List.ext_getElem (by rw [List.slice_length]; omega)
      intro k hk1 hk2
      rw [← getElem!_pos _ k hk1, ← getElem!_pos _ k hk2,
        List.getElem!_slice 0 i2.val k buf.val (by simp at hk2 ⊢; omega)]
      simp
    let* ⟨ sl, hsl ⟩ ← hslice
    have hsllen : (sl : Slice Std.U8).val.length = 32 * MU.val := by rw [hsl]; omega
    have hsllen' : (sl : Slice Std.U8).length = 32 * MU.val := by
      rw [← Slice.length] at hsllen; exact hsllen
    rw [Kopis.Avx2.avx2_cbd_eq sl MU (Std.Array.repeat 256#usize 0#u16) hMU hsllen]
    let* ⟨ re, hre ⟩ ← cbd_spec MU sl (Std.Array.repeat 256#usize 0#u16) hMU hsllen
    have hrow : toRingElem13 re
        = (Spec.Kopis.GenSecret L.val MU.val (arrayToBytes seed))[iter.start.val]'hi_lt := by
      refine cbd_row_eq_genSecret L MU.val (arrayToBytes seed) sl re iter.start.val hi_lt
        hsllen' ?_ hre
      refine Eq.trans ?_ (hbridge iter.start.val hi_lt (by
        simp only [Slice.length, Std.Array.to_slice, ← hbufv]; omega))
      exact sliceToBytes_congr _ _ _ _ _ (by
        simp only [Std.Array.to_slice, ← hbufv]; exact hsl)
    have hslen : (secret.val : List (Std.Array RingElem 1#usize)).length = L.val :=
      secret.property
    have harr0 : ∀ (arr : Std.Array RingElem 1#usize) (v : RingElem),
        (arr.set 0#usize v).val[0]! = v := fun arr v => by
      rw [Std.Array.set_val_eq]
      show (arr.val.set 0 v)[0]! = v
      rw [getElem!_list_set _ 0 v 0 (by rw [arr.property]; decide), if_pos rfl]
    let* ⟨ row, back, hrow2, hback ⟩ ← Array.index_mut_usize_spec secret iter.start (by scalar_tac)
    let* ⟨ row1, hrow1 ⟩ ← Array.update_spec
    apply WP.spec_mono
      (secret_loop1_spec MU iter1 bufs (back row1) seed hMU hL4
        (by rw [hend']; exact hend) (by rw [hstart']; scalar_tac) hN hbridge)
    intro r hr a ha
    rw [hr a ha, hstart']
    by_cases h1 : iter.start.val + 1 ≤ a
    · rw [if_pos h1, if_pos (by omega)]
    · rw [if_neg h1, hback, Std.Array.set_val_eq,
        getElem!_list_set secret.val iter.start.val row1 a (by rw [hslen]; exact hi_lt)]
      by_cases h2 : a = iter.start.val
      · rw [if_pos h2, hrow1, harr0, if_pos (by omega), h2, hrow,
          getElem!_pos _ iter.start.val (by simpa using hi_lt)]
      · rw [if_neg h2, if_neg (by omega)]
  · let* ⟨ o, iter1, hnone, _ ⟩ ← core.iter.range.IteratorRange.next_Usize_none_spec
    rw [hnone]; simp only [WP.spec_ok]
    intro a ha
    rw [if_neg (by scalar_tac)]

/-- The one-byte-suffix message: `seed ‖ i`. -/
theorem msgOf_eq1 (seed : Std.Array Std.U8 32#usize) (suf : Std.Array Std.U8 1#usize) (a : ℕ)
    (ha : (suf.val[0]!).bv = ((a : ℕ) : Byte)) :
    msgOf seed suf = (seedBytes seed ‖ #v[(a : Byte)]).cast (by simp) := by
  apply Vector.ext
  intro j hj
  have h1u : ((1#usize : Std.Usize) : ℕ) = 1 := rfl
  have hj33 : j < 33 := by simp at hj; omega
  rw [← getElem!_pos _ j hj, getElem!_msgOf seed suf j (by simpa using hj)]
  simp only [Vector.getElem_cast, vappend_eq, Vector.getElem_append]
  by_cases h32 : j < 32
  · rw [if_pos h32, dif_pos (by omega),
      ← getElem!_pos _ j (by simpa using h32), getElem!_seedBytes seed j h32]
  · rw [if_neg h32, dif_neg (by omega)]
    simp only [show j - 32 = 0 from by omega]
    rw [ha]
    simp

/-- A lane's `xof4` buffer at rate 136 is the spec's `turboSHAKE256 (seed ‖ i)`. -/
theorem bufBytes_eq1 {N : Std.Usize} (seed : Std.Array Std.U8 32#usize)
    (suf : Std.Array Std.U8 1#usize) (buf : Std.Array Std.U8 N) (a μ : ℕ)
    (ha : (suf.val[0]!).bv = ((a : ℕ) : Byte)) (hN : N.val = 32 * μ)
    (hbuf : ∀ j < N.val,
      ((buf.val[j]!).bv) = (turboSHAKE256 (msgOf seed suf) (3#u8).bv N.val)[j]!)
    (hlen : (Std.Array.to_slice buf).length = 32 * μ) :
    sliceToBytes (Std.Array.to_slice buf) (32 * μ) hlen
      = turboSHAKE256 (seedBytes seed ‖ #v[(a : Byte)]) Spec.Kopis.DOMSEP_GENSEC (32 * μ) := by
  have hdom : (3#u8 : Std.U8).bv = Spec.Kopis.DOMSEP_GENSEC := by decide
  have hcast : ∀ {m n : ℕ} (v : 𝔹 m) (h : m = n) (D : Byte) (o : ℕ),
      turboSHAKE256 (v.cast h) D o = turboSHAKE256 v D o := by
    intro m n v h D o; subst h; rfl
  apply Vector.ext
  intro j hj
  have hjN : j < N.val := by omega
  simp only [sliceToBytes, Vector.getElem_ofFn, Std.Array.to_slice]
  rw [← getElem!_pos (turboSHAKE256 (seedBytes seed ‖ #v[(a : Byte)])
        Spec.Kopis.DOMSEP_GENSEC (32 * μ)) j (by omega),
    ← getElem!_pos buf.val j (by rw [buf.property]; exact hjN), hbuf j hjN,
    msgOf_eq1 seed suf a ha, hdom, hcast, hN]

/-- **`backend::avx2::sample::secret` matches the spec.**  Every row is the spec's CBD sample for
that row index.

`0 < L` is a real precondition: the index loop computes `L - 1` unconditionally, before any guard,
so the vector path underflows at `L = 0` where the portable path is simply empty. -/
theorem avx2_secret_spec (L MU N : Std.Usize) (seed : Std.Array Std.U8 32#usize)
    (hMU : MU.val = 6 ∨ MU.val = 8 ∨ MU.val = 10)
    (hL : 0 < L.val) (hL4 : L.val ≤ 4) (hN : N.val = 32 * MU.val) :
    backend.avx2.sample.secret L MU N seed
      ⦃ (r : arithmetic.matrix_arith.Matrix L 1#usize) => ∀ a < L.val,
          toRingElem13 ((r.val[a]!).val[0]!)
            = (Spec.Kopis.GenSecret L.val MU.val (arrayToBytes seed))[a]! ⦄ := by
  unfold backend.avx2.sample.secret
  rw [show massert (L ≤ 4#usize) = ok () from by
      simp only [massert, if_pos (show L ≤ 4#usize by scalar_tac)], bind_tc_ok]
  let* ⟨ indices1, hidx ⟩ ← secret_loop0_spec L { start := 0#usize, «end» := 4#usize }
    (Std.Array.repeat 4#usize (Std.Array.repeat 1#usize 0#u8)) hL rfl (by simp)
    (by intro lane hlane; simp at hlane)
  obtain ⟨bufs1, hb1, hp0⟩ := WP.spec_imp_exists
    (xof4_turboSHAKE 136#usize 3#u8 seed indices1
      (Std.Array.repeat 4#usize (Std.Array.repeat N 0#u8)) 0 (by omega)
      (Or.inr rfl) (by decide) (by decide) (by decide) (by scalar_tac))
  rw [hb1, bind_tc_ok]
  have hlane : ∀ l, l < 4 → ∀ j < N.val,
      ((bufs1.val[l]!).val[j]!).bv
        = (turboSHAKE256 (msgOf seed (indices1.val[l]!)) (3#u8).bv N.val)[j]! := by
    intro l hl
    have h := xof4_turboSHAKE 136#usize 3#u8 seed indices1
      (Std.Array.repeat 4#usize (Std.Array.repeat N 0#u8)) l hl
      (Or.inr rfl) (by decide) (by decide) (by decide) (by scalar_tac)
    rw [hb1] at h
    simp only [WP.spec_ok] at h
    exact h
  simp only [arithmetic.matrix_arith.Matrix.Insts.CoreDefaultDefault.default,
    arithmetic.ring_arith.RingElem.Insts.CoreDefaultDefault.default, bind_tc_ok]
  apply WP.spec_mono
    (secret_loop1_spec MU { start := 0#usize, «end» := L } bufs1 _ seed hMU hL4 rfl (by simp) hN
      (fun i hi hs => bufBytes_eq1 seed (indices1.val[i]!) (bufs1.val[i]!) i MU.val
        (by rw [hidx i (by omega)]; congr 1; omega) hN (hlane i (by omega)) hs))
  intro r hr a ha
  rw [hr a ha, if_pos (by simp)]

/-- **`backend::avx2::sample::gen_secret_from_seed` matches the spec.**  The `MU` match picks the
buffer length; every arm is `secret` at `N = 32·MU`. -/
theorem avx2_gen_secret_from_seed_spec (L MU : Std.Usize) (seed : Std.Array Std.U8 32#usize)
    (hMU : MU.val = 6 ∨ MU.val = 8 ∨ MU.val = 10) (hL : 0 < L.val) (hL4 : L.val ≤ 4) :
    backend.avx2.sample.gen_secret_from_seed L MU seed
      ⦃ (r : arithmetic.matrix_arith.Matrix L 1#usize) => ∀ a < L.val,
          toRingElem13 ((r.val[a]!).val[0]!)
            = (Spec.Kopis.GenSecret L.val MU.val (arrayToBytes seed))[a]! ⦄ := by
  have harm : ∀ (n : Std.Usize), MU.val = 6 ∧ n = 192#usize ∨ MU.val = 8 ∧ n = 256#usize
      ∨ MU.val = 10 ∧ n = 320#usize →
      backend.avx2.sample.gen_secret_from_seed L MU seed
        = backend.avx2.sample.secret L MU n seed := by
    rintro n (⟨h, rfl⟩ | ⟨h, rfl⟩ | ⟨h, rfl⟩) <;>
      · unfold backend.avx2.sample.gen_secret_from_seed
        rw [h]
        rfl
  rcases hMU with h | h | h
  · rw [harm 192#usize (Or.inl ⟨h, rfl⟩)]
    exact avx2_secret_spec L MU 192#usize seed (Or.inl h) hL hL4 (by rw [h]; decide)
  · rw [harm 256#usize (Or.inr (Or.inl ⟨h, rfl⟩))]
    exact avx2_secret_spec L MU 256#usize seed (Or.inr (Or.inl h)) hL hL4 (by rw [h]; decide)
  · rw [harm 320#usize (Or.inr (Or.inr ⟨h, rfl⟩))]
    exact avx2_secret_spec L MU 320#usize seed (Or.inr (Or.inr h)) hL hL4 (by rw [h]; decide)

/-! ## The coefficient bound -/

/-- **The CBD loop's coefficient bound.**  Same walk as `secret_loop1_spec` with the value
reasoning stripped, using `cbd_bd`. -/
theorem secret_loop1_bd {L : Std.Usize} (MU : Std.Usize) {N : Std.Usize}
    (iter : core.ops.range.Range Std.Usize)
    (bufs : Std.Array (Std.Array Std.U8 N) 4#usize)
    (secret : arithmetic.matrix_arith.Matrix L 1#usize)
    (hMU : MU.val = 6 ∨ MU.val = 8 ∨ MU.val = 10)
    (hL4 : L.val ≤ 4) (hend : iter.«end».val = L.val) (hstart : iter.start.val ≤ L.val)
    (hN : N.val = 32 * MU.val)
    (hpre : ∀ a, a < L.val → a < iter.start.val → ∀ c, c < 256 →
      smallSignedU16 (((secret.val[a]!).val[0]!).val[c]!) (MU.val / 2)) :
    backend.avx2.sample.secret_loop1 MU iter bufs secret
      ⦃ (r : arithmetic.matrix_arith.Matrix L 1#usize) => ∀ a, a < L.val → ∀ c, c < 256 →
          smallSignedU16 (((r.val[a]!).val[0]!).val[c]!) (MU.val / 2) ⦄ := by
  unfold backend.avx2.sample.secret_loop1
  by_cases hlt : iter.start.val < iter.«end».val
  · let* ⟨ o, iter1, ho, hstart', hend' ⟩ ← core.iter.range.IteratorRange.next_Usize_some_spec
    rw [ho]; simp only
    have hi_lt : iter.start.val < L.val := by scalar_tac
    let* ⟨ buf, hbuf ⟩ ← Array.index_usize_spec bufs iter.start (by scalar_tac)
    have hblen : (buf.val : List Std.U8).length = N.val := buf.property
    simp only [consts.RING_DEG]
    let* ⟨ i1, hi1 ⟩ ← Std.Usize.mul_spec (x := 256#usize) (y := MU) (by scalar_tac)
    let* ⟨ i2, hi2 ⟩ ← Std.Usize.div_spec
    have hi2v : i2.val = 32 * MU.val := by rw [hi2, hi1]; omega
    have hslice : core.slice.index.SliceIndexRangeToUsizeSlice.index
        ({ «end» := i2 } : core.ops.range.RangeTo Std.Usize) (Std.Array.to_slice buf)
      ⦃ (sl : Slice Std.U8) => sl.val = buf.val ⦄ := by
      unfold core.slice.index.SliceIndexRangeToUsizeSlice.index
      rw [if_pos (by simp only [Std.Array.to_slice, Slice.length]; scalar_tac)]
      simp only [WP.spec_ok, Std.Array.to_slice]
      apply List.ext_getElem (by rw [List.slice_length]; omega)
      intro k hk1 hk2
      rw [← getElem!_pos _ k hk1, ← getElem!_pos _ k hk2,
        List.getElem!_slice 0 i2.val k buf.val (by simp at hk2 ⊢; omega)]
      simp
    let* ⟨ sl, hsl ⟩ ← hslice
    have hsllen : (sl : Slice Std.U8).val.length = 32 * MU.val := by rw [hsl]; omega
    rw [Kopis.Avx2.avx2_cbd_eq sl MU (Std.Array.repeat 256#usize 0#u16) hMU hsllen]
    let* ⟨ re, hre ⟩ ← CbdGeneric.cbd_bd MU sl (Std.Array.repeat 256#usize 0#u16) hMU hsllen
    have hslen : (secret.val : List (Std.Array RingElem 1#usize)).length = L.val :=
      secret.property
    have harr0 : ∀ (arr : Std.Array RingElem 1#usize) (v : RingElem),
        (arr.set 0#usize v).val[0]! = v := fun arr v => by
      rw [Std.Array.set_val_eq]
      show (arr.val.set 0 v)[0]! = v
      rw [getElem!_list_set _ 0 v 0 (by rw [arr.property]; decide), if_pos rfl]
    let* ⟨ row, back, hrow2, hback ⟩ ← Array.index_mut_usize_spec secret iter.start (by scalar_tac)
    let* ⟨ row1, hrow1 ⟩ ← Array.update_spec
    apply WP.spec_mono
      (secret_loop1_bd MU iter1 bufs (back row1) hMU hL4
        (by rw [hend']; exact hend) (by rw [hstart']; scalar_tac) hN ?_)
    · intro r hr
      exact hr
    · intro a ha ha2 c hc
      rw [hstart'] at ha2
      rw [hback, Std.Array.set_val_eq,
        getElem!_list_set secret.val iter.start.val row1 a (by rw [hslen]; exact hi_lt)]
      by_cases h2 : a = iter.start.val
      · rw [if_pos h2, hrow1, harr0]
        exact hre c hc
      · rw [if_neg h2]
        exact hpre a ha (by omega) c hc
  · let* ⟨ o, iter1, hnone, _ ⟩ ← core.iter.range.IteratorRange.next_Usize_none_spec
    rw [hnone]; simp only [WP.spec_ok]
    intro a ha c hc
    exact hpre a ha (by scalar_tac) c hc

/-- **`backend::avx2::sample::secret`'s coefficient bound.** -/
theorem avx2_secret_bd (L MU N : Std.Usize) (seed : Std.Array Std.U8 32#usize)
    (hMU : MU.val = 6 ∨ MU.val = 8 ∨ MU.val = 10)
    (hL : 0 < L.val) (hL4 : L.val ≤ 4) (hN : N.val = 32 * MU.val) :
    backend.avx2.sample.secret L MU N seed
      ⦃ (r : arithmetic.matrix_arith.Matrix L 1#usize) => ∀ a, a < L.val → ∀ c, c < 256 →
          smallSignedU16 (((r.val[a]!).val[0]!).val[c]!) (MU.val / 2) ⦄ := by
  unfold backend.avx2.sample.secret
  rw [show massert (L ≤ 4#usize) = ok () from by
      simp only [massert, if_pos (show L ≤ 4#usize by scalar_tac)], bind_tc_ok]
  let* ⟨ indices1, hidx ⟩ ← secret_loop0_spec L { start := 0#usize, «end» := 4#usize }
    (Std.Array.repeat 4#usize (Std.Array.repeat 1#usize 0#u8)) hL rfl (by simp)
    (by intro lane hlane; simp at hlane)
  obtain ⟨bufs1, hb1, hp0⟩ := WP.spec_imp_exists
    (Kopis.Avx2.Keccak.xof4_turboSHAKE 136#usize 3#u8 seed indices1
      (Std.Array.repeat 4#usize (Std.Array.repeat N 0#u8)) 0 (by omega)
      (Or.inr rfl) (by decide) (by decide) (by decide) (by scalar_tac))
  rw [hb1, bind_tc_ok]
  simp only [arithmetic.matrix_arith.Matrix.Insts.CoreDefaultDefault.default,
    arithmetic.ring_arith.RingElem.Insts.CoreDefaultDefault.default, bind_tc_ok]
  apply WP.spec_mono
    (secret_loop1_bd MU { start := 0#usize, «end» := L } bufs1 _ hMU hL4 rfl (by simp) hN
      (by intro a ha ha2 c hc; simp at ha2))
  intro r hr
  exact hr

/-- **`backend::avx2::sample::gen_secret_from_seed`'s coefficient bound.** -/
theorem avx2_gen_secret_from_seed_bd (L MU : Std.Usize) (seed : Std.Array Std.U8 32#usize)
    (hMU : MU.val = 6 ∨ MU.val = 8 ∨ MU.val = 10) (hL : 0 < L.val) (hL4 : L.val ≤ 4) :
    backend.avx2.sample.gen_secret_from_seed L MU seed
      ⦃ (r : arithmetic.matrix_arith.Matrix L 1#usize) => ∀ a, a < L.val → ∀ c, c < 256 →
          smallSignedU16 (((r.val[a]!).val[0]!).val[c]!) (MU.val / 2) ⦄ := by
  have harm : ∀ (n : Std.Usize), MU.val = 6 ∧ n = 192#usize ∨ MU.val = 8 ∧ n = 256#usize
      ∨ MU.val = 10 ∧ n = 320#usize →
      backend.avx2.sample.gen_secret_from_seed L MU seed
        = backend.avx2.sample.secret L MU n seed := by
    rintro n (⟨h, rfl⟩ | ⟨h, rfl⟩ | ⟨h, rfl⟩) <;>
      · unfold backend.avx2.sample.gen_secret_from_seed
        rw [h]
        rfl
  rcases hMU with h | h | h
  · rw [harm 192#usize (Or.inl ⟨h, rfl⟩)]
    exact avx2_secret_bd L MU 192#usize seed (Or.inl h) hL hL4 (by rw [h]; decide)
  · rw [harm 256#usize (Or.inr (Or.inl ⟨h, rfl⟩))]
    exact avx2_secret_bd L MU 256#usize seed (Or.inr (Or.inl h)) hL hL4 (by rw [h]; decide)
  · rw [harm 320#usize (Or.inr (Or.inr ⟨h, rfl⟩))]
    exact avx2_secret_bd L MU 320#usize seed (Or.inr (Or.inr h)) hL hL4 (by rw [h]; decide)

end
end Kopis.Avx2.Properties
