/-
  # Kopis/Neon/SecretBridge.lean — the NEON secret sampler against the spec.

  `SampleBridge.lean`'s matrix path, one dimension lower: one sponge per row, a one-byte suffix,
  `cbd` instead of `deserialize`, and `xof2` at rate 136 (TurboSHAKE256) rather than 168.

  Two differences from `Kopis/Avx2/SecretBridge.lean`, both from the extracted code rather than
  from the proof.  The NEON sampler *batches*, exactly as its matrix sampler does — two rows per
  `xof2` call, looping on `first` — where AVX2 asserts `L ≤ 4` and covers every row in one call.
  And its inner loop carries a second guard, `MU % 8 == 0`, choosing between the portable `cbd`
  and `cbd_lanes`; `Kopis/Neon/CbdDispatch.lean` collapses that to the portable body, so
  everything below the guard is the serial argument.

  Split from `SampleBridge.lean` only to break an import cycle: this needs `GenSecretSpec`, which
  transitively imports the `GenMatrix` twin, which imports `SampleBridge` for the matrix dispatch.
-/
import Kopis.Neon.SampleBridge
import Kopis.Neon.CbdDispatch
import Kopis.Neon.Properties.GenSecretSpec

open Aeneas Aeneas.Std Result
open RustKopisNeon
open Kopis.Neon
open Kopis.Neon.Keccak (min_usize_eq xof2_turboSHAKE)
open Kopis.Keccak (getElem!_list_set bytesOf msgOf getElem!_bytesOf getElem!_msgOf)
open Kopis.Properties (streamNat)
open Spec (𝔹)
open scoped Spec.Notations
open Spec.TurboSHAKE (turboSHAKE256)
open arithmetic.ring_arith (RingElem)

namespace Kopis.Neon.Properties

set_option maxHeartbeats 8000000
set_option maxRecDepth 2000000

noncomputable section

/-! ## The secret sampler

Same shape as the matrix sampler, one dimension lower: one sponge per row, a one-byte suffix, and
`cbd` instead of `deserialize`.  `xof2` runs at rate 136 (TurboSHAKE256) rather than 168. -/

/-- The row a given lane of a two-wide batch samples: `first + lane`, clamped to the last row so
the trailing lane of a short batch hashes something harmless. -/
def batchRow (L first lane : ℕ) : ℕ := min (first + lane) (L - 1)

/-- **The secret sampler's index loop.**  Lane `lane` carries the row it will sample. -/
theorem secret_loop0_loop0_spec (L : Std.Usize) (iter : core.ops.range.Range Std.Usize)
    (first : Std.Usize) (indices : Std.Array (Std.Array Std.U8 1#usize) 2#usize)
    (hL : 0 < L.val) (hend : iter.«end».val = 2) (hstart : iter.start.val ≤ 2)
    (hmax : first.val + 2 ≤ Std.Usize.max)
    (hpre : ∀ lane < iter.start.val,
      ((indices.val[lane]!).val[0]!).bv = ((batchRow L.val first.val lane : ℕ) : Byte)) :
    backend.neon.sample.secret_loop0_loop0 L iter first indices
      ⦃ (r : Std.Array (Std.Array Std.U8 1#usize) 2#usize) => ∀ lane < 2,
          ((r.val[lane]!).val[0]!).bv = ((batchRow L.val first.val lane : ℕ) : Byte) ⦄ := by
  unfold backend.neon.sample.secret_loop0_loop0
  by_cases hlt : iter.start.val < iter.«end».val
  · let* ⟨ o, iter1, ho, hstart', hend' ⟩ ← core.iter.range.IteratorRange.next_Usize_some_spec
    rw [ho]; simp only
    have hl2 : iter.start.val < 2 := by scalar_tac
    let* ⟨ i, hi ⟩ ← Std.Usize.add_spec (x := first) (y := iter.start) (by scalar_tac)
    let* ⟨ i1, hi1 ⟩ ← Std.Usize.sub_spec (x := L) (y := 1#usize) (by scalar_tac)
    rw [min_usize_eq, bind_tc_ok]
    have hbv : ((if i.val < i1.val then i else i1) : Std.Usize).val
        = batchRow L.val first.val iter.start.val := by
      simp only [batchRow]; split <;> omega
    have hilen : (indices.val : List (Std.Array Std.U8 1#usize)).length = 2 := indices.property
    let* ⟨ row, back, hrow, hback ⟩ ← Array.index_mut_usize_spec indices iter.start (by scalar_tac)
    rw [show (lift (Std.UScalar.cast .U8 (if i.val < i1.val then i else i1)) : Result Std.U8)
      = ok (Std.UScalar.cast .U8 (if i.val < i1.val then i else i1)) from rfl, bind_tc_ok]
    have hlen1 : ∀ (r : Std.Array Std.U8 1#usize), (r.val : List Std.U8).length = 1 :=
      fun r => r.property
    let* ⟨ row1, hrow1 ⟩ ← Array.update_spec
    have hpre' : ∀ lane < iter1.start.val,
        (((back row1).val[lane]!).val[0]!).bv
          = ((batchRow L.val first.val lane : ℕ) : Byte) := by
      intro lane hlane
      rw [hstart'] at hlane
      have u0 : ((0#usize : Std.Usize) : ℕ) = 0 := rfl
      rw [hback, Std.Array.set_val_eq,
        getElem!_list_set indices.val iter.start.val row1 lane (by rw [hilen]; exact hl2)]
      by_cases h : lane = iter.start.val
      · rw [if_pos h, h, hrow1, Std.Array.set_val_eq, u0,
          getElem!_list_set row.val 0 _ 0 (by rw [hlen1]; omega), if_pos rfl,
          show Std.U8.bv (Std.UScalar.cast .U8 (if i.val < i1.val then i else i1))
            = (((if i.val < i1.val then i else i1) : Std.Usize).val : Byte) from
            usize_cast_u8_bv _, hbv]
      · rw [if_neg h]
        exact hpre lane (by omega)
    apply WP.spec_mono
      (secret_loop0_loop0_spec L iter1 first (back row1) hL
        (by rw [hend']; exact hend) (by rw [hstart']; omega) hmax hpre')
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

/-- **The secret sampler's CBD loop.**  One row per lane, for the lanes whose row is in range.
`CbdDispatch.lean` collapses the `MU % 8` guard to the portable sampler, so the serial `cbd_spec`
and `cbd_row_eq_genSecret` carry the rest. -/
theorem secret_loop0_loop1_spec {L : Std.Usize} (MU : Std.Usize) {N : Std.Usize}
    (iter : core.ops.range.Range Std.Usize)
    (secret : arithmetic.matrix_arith.Matrix L 1#usize) (first : Std.Usize)
    (bufs : Std.Array (Std.Array Std.U8 N) 2#usize) (seed : Std.Array Std.U8 32#usize)
    (hMU : MU.val = 6 ∨ MU.val = 8 ∨ MU.val = 10)
    (hend : iter.«end».val = 2) (hstart : iter.start.val ≤ 2)
    (hN : N.val = 32 * MU.val) (hmax : first.val + 2 ≤ Std.Usize.max)
    (hbridge : ∀ lane < 2, first.val + lane < L.val →
      ∀ (hs : (Std.Array.to_slice (bufs.val[lane]!)).length = 32 * MU.val),
      sliceToBytes (Std.Array.to_slice (bufs.val[lane]!)) (32 * MU.val) hs
        = turboSHAKE256 (arrayToBytes seed ‖ #v[((first.val + lane : ℕ) : Byte)])
            Spec.Kopis.DOMSEP_GENSEC (32 * MU.val)) :
    backend.neon.sample.secret_loop0_loop1 MU iter secret first bufs
      ⦃ (r : arithmetic.matrix_arith.Matrix L 1#usize) => ∀ a < L.val,
          toRingElem13 ((r.val[a]!).val[0]!)
            = if first.val + iter.start.val ≤ a ∧ a < first.val + 2
              then (Spec.Kopis.GenSecret L.val MU.val (arrayToBytes seed))[a]!
              else toRingElem13 ((secret.val[a]!).val[0]!) ⦄ := by
  unfold backend.neon.sample.secret_loop0_loop1
  by_cases hlt : iter.start.val < iter.«end».val
  · let* ⟨ o, iter1, ho, hstart', hend' ⟩ ← core.iter.range.IteratorRange.next_Usize_some_spec
    rw [ho]; simp only
    have hl2 : iter.start.val < 2 := by scalar_tac
    let* ⟨ i, hi ⟩ ← Std.Usize.add_spec (x := first) (y := iter.start) (by scalar_tac)
    have hiv : i.val = first.val + iter.start.val := hi
    by_cases hin : i < L
    · rw [if_pos hin]
      have hi_lt : i.val < L.val := by scalar_tac
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
      have hslen : (secret.val : List (Std.Array RingElem 1#usize)).length = L.val :=
        secret.property
      have hia : i.val < secret.length := by
        show i.val < (secret.val : List (Std.Array RingElem 1#usize)).length
        rw [hslen]; exact hi_lt
      have hbufslen : (Std.Array.to_slice (bufs.val[iter.start.val]!)).length = 32 * MU.val := by
        rw [← hbufv]
        show (buf.val : List Std.U8).length = 32 * MU.val
        rw [hblen, hN]
      have hbufvals : (sl : Slice Std.U8).val
          = (Std.Array.to_slice (bufs.val[iter.start.val]!)).val := by
        rw [← hbufv]; exact hsl
      have hspec : sliceToBytes sl (32 * MU.val) hsllen'
          = turboSHAKE256 (arrayToBytes seed ‖ #v[((i.val : ℕ) : Byte)])
              Spec.Kopis.DOMSEP_GENSEC (32 * MU.val) := by
        refine Eq.trans (sliceToBytes_congr _ _ _ _ hbufslen hbufvals) ?_
        refine Eq.trans (hbridge iter.start.val hl2 (by omega) hbufslen) ?_
        rw [hiv]
      -- the recursion, taking the post-store matrix and its row `i`
      have hcomb : ∀ (m : arithmetic.matrix_arith.Matrix L 1#usize),
          (∀ a < L.val, toRingElem13 ((m.val[a]!).val[0]!)
            = if a = i.val
              then (Spec.Kopis.GenSecret L.val MU.val (arrayToBytes seed))[i.val]'hi_lt
              else toRingElem13 ((secret.val[a]!).val[0]!)) →
          backend.neon.sample.secret_loop0_loop1 MU iter1 m first bufs
            ⦃ (r : arithmetic.matrix_arith.Matrix L 1#usize) => ∀ a < L.val,
                toRingElem13 ((r.val[a]!).val[0]!)
                  = if first.val + iter.start.val ≤ a ∧ a < first.val + 2
                    then (Spec.Kopis.GenSecret L.val MU.val (arrayToBytes seed))[a]!
                    else toRingElem13 ((secret.val[a]!).val[0]!) ⦄ := by
        intro m hm
        apply WP.spec_mono
          (secret_loop0_loop1_spec MU iter1 m first bufs seed hMU
            (by rw [hend']; exact hend) (by rw [hstart']; omega) hN hmax hbridge)
        intro r hr a ha
        rw [hr a ha, hstart']
        by_cases h1 : first.val + (iter.start.val + 1) ≤ a ∧ a < first.val + 2
        · rw [if_pos h1, if_pos ⟨by omega, h1.2⟩]
        · rw [if_neg h1, hm a ha]
          by_cases h2 : a = i.val
          · rw [if_pos h2, if_pos ⟨by omega, by omega⟩, h2,
              getElem!_pos _ i.val (by simpa using hi_lt)]
          · rw [if_neg h2, if_neg (by omega)]
      -- the `MU % 8` guard: byte-aligned takes the portable sampler, otherwise `cbd_lanes`,
      -- which `neon_cbd_eq` says *is* the portable sampler.  Only the write-back differs.
      rw [show core.num.Usize.is_multiple_of MU 8#usize
        = ok (MU.val % ((8#usize : Std.Usize) : ℕ) == 0) from rfl, bind_tc_ok]
      by_cases hb8 : (MU.val % ((8#usize : Std.Usize) : ℕ) == 0) = true
      · rw [if_pos hb8]
        let* ⟨ row, back, hrow2, hback ⟩ ← Array.index_mut_usize_spec secret i hia
        let* ⟨ re0, back1, hre0, hback1 ⟩ ← Array.index_mut_usize_spec row 0#usize (by
          show ((0#usize : Std.Usize) : ℕ) < (row.val : List RingElem).length
          rw [row.property]; decide)
        let* ⟨ re, hre ⟩ ← cbd_spec MU sl re0 hMU hsllen
        refine hcomb _ (fun a ha => ?_)
        rw [hback, Std.Array.set_val_eq,
          getElem!_list_set secret.val i.val (back1 re) a (by rw [hslen]; exact hi_lt)]
        by_cases h2 : a = i.val
        · rw [if_pos h2, if_pos h2, hback1, Std.Array.set_val_eq,
            show ((row.val : List RingElem).set ((0#usize : Std.Usize) : ℕ) re)[0]! = re from by
              rw [getElem!_list_set row.val ((0#usize : Std.Usize) : ℕ) re 0
                (by rw [row.property]; decide),
                if_pos (show (0 : ℕ) = ((0#usize : Std.Usize) : ℕ) from rfl)]]
          exact cbd_row_eq_genSecret L MU.val (arrayToBytes seed) sl re i.val hi_lt hsllen'
            hspec hre
        · rw [if_neg h2, if_neg h2]
      · rw [if_neg hb8, Kopis.Neon.neon_cbd_eq sl MU (Std.Array.repeat 256#usize 0#u16) hMU hsllen]
        let* ⟨ re, hre ⟩ ← cbd_spec MU sl (Std.Array.repeat 256#usize 0#u16) hMU hsllen
        let* ⟨ row, back, hrow2, hback ⟩ ← Array.index_mut_usize_spec secret i hia
        let* ⟨ row1, hrow1 ⟩ ← Array.update_spec
        refine hcomb _ (fun a ha => ?_)
        rw [hback, Std.Array.set_val_eq,
          getElem!_list_set secret.val i.val row1 a (by rw [hslen]; exact hi_lt)]
        by_cases h2 : a = i.val
        · rw [if_pos h2, if_pos h2, hrow1, Std.Array.set_val_eq,
            show ((row.val : List RingElem).set ((0#usize : Std.Usize) : ℕ) re)[0]! = re from by
              rw [getElem!_list_set row.val ((0#usize : Std.Usize) : ℕ) re 0
                (by rw [row.property]; decide),
                if_pos (show (0 : ℕ) = ((0#usize : Std.Usize) : ℕ) from rfl)]]
          exact cbd_row_eq_genSecret L MU.val (arrayToBytes seed) sl re i.val hi_lt hsllen'
            hspec hre
        · rw [if_neg h2, if_neg h2]
    · rw [if_neg hin]
      have hge : L.val ≤ first.val + iter.start.val := by scalar_tac
      apply WP.spec_mono
        (secret_loop0_loop1_spec MU iter1 secret first bufs seed hMU
          (by rw [hend']; exact hend) (by rw [hstart']; omega) hN hmax hbridge)
      intro r hr a ha
      rw [hr a ha, hstart', if_neg (by omega), if_neg (by omega)]
  · let* ⟨ o, iter1, hnone, _ ⟩ ← core.iter.range.IteratorRange.next_Usize_none_spec
    rw [hnone]; simp only [WP.spec_ok]
    intro a ha
    rw [if_neg (by scalar_tac)]
  termination_by iter.«end».val - iter.start.val
  decreasing_by all_goals (simp only [hend']; omega)

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

/-- A lane's `xof2` buffer at rate 136 is the spec's `turboSHAKE256 (seed ‖ i)`. -/
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


/-! ## The batching loop -/

unseal backend.neon.keccak.WAYS in
/-- **The batching loop.**  Two rows per `xof2` call; every row from `first` on ends up holding
the spec's CBD sample for its index. -/
theorem secret_loop0_spec {L : Std.Usize} (MU N : Std.Usize) (seed : Std.Array Std.U8 32#usize)
    (secret : arithmetic.matrix_arith.Matrix L 1#usize) (first : Std.Usize)
    (hMU : MU.val = 6 ∨ MU.val = 8 ∨ MU.val = 10) (hN : N.val = 32 * MU.val)
    (hmax : L.val + 2 ≤ Std.Usize.max) :
    backend.neon.sample.secret_loop0 MU N seed secret first
      ⦃ (r : arithmetic.matrix_arith.Matrix L 1#usize) => ∀ a < L.val,
          toRingElem13 ((r.val[a]!).val[0]!)
            = if first.val ≤ a
              then (Spec.Kopis.GenSecret L.val MU.val (arrayToBytes seed))[a]!
              else toRingElem13 ((secret.val[a]!).val[0]!) ⦄ := by
  unfold backend.neon.sample.secret_loop0
  simp only [show backend.neon.keccak.WAYS = 2#usize from by decide]
  by_cases hlt : first < L
  · rw [if_pos hlt]
    have hfv : first.val < L.val := by scalar_tac
    have hL : 0 < L.val := by omega
    let* ⟨ indices1, hidx ⟩ ← secret_loop0_loop0_spec L { start := 0#usize, «end» := 2#usize }
      first (Std.Array.repeat 2#usize (Std.Array.repeat 1#usize 0#u8)) hL (by decide) (by simp)
      (by omega) (by intro lane hlane; simp at hlane)
    obtain ⟨bufs1, hb1, hp0⟩ := WP.spec_imp_exists
      (xof2_turboSHAKE 136#usize 3#u8 seed indices1
        (Std.Array.repeat 2#usize (Std.Array.repeat N 0#u8)) 0 (by omega)
        (Or.inr rfl) (by decide) (by decide) (by decide) (by scalar_tac))
    rw [hb1, bind_tc_ok]
    have hbufl : ∀ l, l < 2 → ∀ j < N.val,
        ((bufs1.val[l]!).val[j]!).bv
          = (turboSHAKE256 (msgOf seed (indices1.val[l]!)) (3#u8).bv N.val)[j]! := by
      intro l hl
      have h := xof2_turboSHAKE 136#usize 3#u8 seed indices1
        (Std.Array.repeat 2#usize (Std.Array.repeat N 0#u8)) l hl
        (Or.inr rfl) (by decide) (by decide) (by decide) (by scalar_tac)
      rw [hb1] at h
      simp only [WP.spec_ok] at h
      exact h
    let* ⟨ secret1, hs1 ⟩ ← secret_loop0_loop1_spec MU { start := 0#usize, «end» := 2#usize }
      secret first bufs1 seed hMU (by decide) (by simp) hN (by omega)
      (fun lane hln hrow hs => bufBytes_eq1 seed (indices1.val[lane]!) (bufs1.val[lane]!)
        (first.val + lane) MU.val
        (by rw [hidx lane hln]; congr 1; simp only [batchRow]; omega) hN
        (hbufl lane hln) hs)
    let* ⟨ first1, hf1 ⟩ ← Std.Usize.add_spec (x := first) (y := 2#usize) (by scalar_tac)
    apply WP.spec_mono (secret_loop0_spec MU N seed secret1 first1 hMU hN hmax)
    intro r hr a ha
    rw [hr a ha, hf1]
    by_cases h2 : first.val + 2 ≤ a
    · rw [if_pos h2, if_pos (by omega)]
    · rw [if_neg h2, hs1 a ha]
      simp only [Nat.add_zero]
      by_cases h0 : first.val ≤ a
      · rw [if_pos ⟨h0, by omega⟩, if_pos h0]
      · rw [if_neg (by omega), if_neg h0]
  · rw [if_neg hlt]
    simp only [WP.spec_ok]
    intro a ha
    rw [if_neg (by scalar_tac)]
  termination_by L.val - first.val
  decreasing_by scalar_decr_tac

/-! ## The entry points -/

/-- **`backend::neon::sample::secret` matches the spec.**  Every row is the spec's CBD sample for
that row index. -/
theorem neon_secret_spec (L MU N : Std.Usize) (seed : Std.Array Std.U8 32#usize)
    (hMU : MU.val = 6 ∨ MU.val = 8 ∨ MU.val = 10) (hN : N.val = 32 * MU.val)
    (hmax : L.val + 2 ≤ Std.Usize.max) :
    backend.neon.sample.secret L MU N seed
      ⦃ (r : arithmetic.matrix_arith.Matrix L 1#usize) => ∀ a < L.val,
          toRingElem13 ((r.val[a]!).val[0]!)
            = (Spec.Kopis.GenSecret L.val MU.val (arrayToBytes seed))[a]! ⦄ := by
  unfold backend.neon.sample.secret
  simp only [arithmetic.matrix_arith.Matrix.Insts.CoreDefaultDefault.default,
    arithmetic.ring_arith.RingElem.Insts.CoreDefaultDefault.default, bind_tc_ok]
  apply WP.spec_mono (secret_loop0_spec MU N seed _ 0#usize hMU hN hmax)
  intro r hr a ha
  rw [hr a ha, if_pos (by simp)]

/-- **`backend::neon::sample::gen_secret_from_seed` matches the spec.**  The `MU` match picks the
buffer length; every arm is `secret` at `N = 32·MU`. -/
theorem neon_gen_secret_from_seed_spec (L MU : Std.Usize) (seed : Std.Array Std.U8 32#usize)
    (hMU : MU.val = 6 ∨ MU.val = 8 ∨ MU.val = 10) (hmax : L.val + 2 ≤ Std.Usize.max) :
    backend.neon.sample.gen_secret_from_seed L MU seed
      ⦃ (r : arithmetic.matrix_arith.Matrix L 1#usize) => ∀ a < L.val,
          toRingElem13 ((r.val[a]!).val[0]!)
            = (Spec.Kopis.GenSecret L.val MU.val (arrayToBytes seed))[a]! ⦄ := by
  have harm : ∀ (n : Std.Usize), MU.val = 6 ∧ n = 192#usize ∨ MU.val = 8 ∧ n = 256#usize
      ∨ MU.val = 10 ∧ n = 320#usize →
      backend.neon.sample.gen_secret_from_seed L MU seed
        = backend.neon.sample.secret L MU n seed := by
    rintro n (⟨h, rfl⟩ | ⟨h, rfl⟩ | ⟨h, rfl⟩) <;>
      · unfold backend.neon.sample.gen_secret_from_seed
        rw [h]
        rfl
  rcases hMU with h | h | h
  · rw [harm 192#usize (Or.inl ⟨h, rfl⟩)]
    exact neon_secret_spec L MU 192#usize seed (Or.inl h) (by rw [h]; decide) hmax
  · rw [harm 256#usize (Or.inr (Or.inl ⟨h, rfl⟩))]
    exact neon_secret_spec L MU 256#usize seed (Or.inr (Or.inl h)) (by rw [h]; decide) hmax
  · rw [harm 320#usize (Or.inr (Or.inr ⟨h, rfl⟩))]
    exact neon_secret_spec L MU 320#usize seed (Or.inr (Or.inr h)) (by rw [h]; decide) hmax

/-! ## The coefficient bound -/

/-- **The CBD loop's coefficient bound.**  The same walk as `secret_loop0_loop1_spec` with the
value reasoning stripped, using `cbd_bd`. -/
theorem secret_loop0_loop1_bd {L : Std.Usize} (MU : Std.Usize) {N : Std.Usize}
    (iter : core.ops.range.Range Std.Usize)
    (secret : arithmetic.matrix_arith.Matrix L 1#usize) (first : Std.Usize)
    (bufs : Std.Array (Std.Array Std.U8 N) 2#usize)
    (hMU : MU.val = 6 ∨ MU.val = 8 ∨ MU.val = 10)
    (hend : iter.«end».val = 2) (hstart : iter.start.val ≤ 2)
    (hN : N.val = 32 * MU.val) (hmax : first.val + 2 ≤ Std.Usize.max)
    (hpre : ∀ a, a < L.val → a < first.val + iter.start.val →
      ∀ c, c < 256 → smallSignedU16 (((secret.val[a]!).val[0]!).val[c]!) (MU.val / 2)) :
    backend.neon.sample.secret_loop0_loop1 MU iter secret first bufs
      ⦃ (r : arithmetic.matrix_arith.Matrix L 1#usize) => ∀ a, a < L.val → a < first.val + 2 →
          ∀ c, c < 256 → smallSignedU16 (((r.val[a]!).val[0]!).val[c]!) (MU.val / 2) ⦄ := by
  unfold backend.neon.sample.secret_loop0_loop1
  by_cases hlt : iter.start.val < iter.«end».val
  · let* ⟨ o, iter1, ho, hstart', hend' ⟩ ← core.iter.range.IteratorRange.next_Usize_some_spec
    rw [ho]; simp only
    have hl2 : iter.start.val < 2 := by scalar_tac
    let* ⟨ i, hi ⟩ ← Std.Usize.add_spec (x := first) (y := iter.start) (by scalar_tac)
    have hiv : i.val = first.val + iter.start.val := hi
    by_cases hin : i < L
    · rw [if_pos hin]
      have hi_lt : i.val < L.val := by scalar_tac
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
      have hslen : (secret.val : List (Std.Array RingElem 1#usize)).length = L.val :=
        secret.property
      have hia : i.val < secret.length := by
        show i.val < (secret.val : List (Std.Array RingElem 1#usize)).length
        rw [hslen]; exact hi_lt
      have hcomb : ∀ (m : arithmetic.matrix_arith.Matrix L 1#usize),
          (∀ a, a < L.val → a < first.val + (iter.start.val + 1) →
            ∀ c, c < 256 → smallSignedU16 (((m.val[a]!).val[0]!).val[c]!) (MU.val / 2)) →
          backend.neon.sample.secret_loop0_loop1 MU iter1 m first bufs
            ⦃ (r : arithmetic.matrix_arith.Matrix L 1#usize) => ∀ a, a < L.val →
                a < first.val + 2 → ∀ c, c < 256 →
                smallSignedU16 (((r.val[a]!).val[0]!).val[c]!) (MU.val / 2) ⦄ := by
        intro m hm
        apply WP.spec_mono
          (secret_loop0_loop1_bd MU iter1 m first bufs hMU
            (by rw [hend']; exact hend) (by rw [hstart']; omega) hN hmax
            (fun a ha hout c hc => hm a ha (by rw [hstart'] at hout; exact hout) c hc))
        intro r hr
        exact hr
      have hstore : ∀ (v : RingElem) (row : Std.Array RingElem 1#usize)
          (back : Std.Array RingElem 1#usize → arithmetic.matrix_arith.Matrix L 1#usize),
          (∀ s, (back s).val = secret.val.set i.val s) →
          (∀ c, c < 256 → smallSignedU16 (v.val[c]!) (MU.val / 2)) →
          ∀ a, a < L.val → a < first.val + (iter.start.val + 1) → ∀ c, c < 256 →
            smallSignedU16 ((((back (row.set 0#usize v)).val[a]!).val[0]!).val[c]!)
              (MU.val / 2) := by
        intro v row back hback hv a ha hout c hc
        rw [hback, getElem!_list_set secret.val i.val (row.set 0#usize v) a
          (by rw [hslen]; exact hi_lt)]
        by_cases h2 : a = i.val
        · rw [if_pos h2, Std.Array.set_val_eq,
            getElem!_list_set row.val ((0#usize : Std.Usize) : ℕ) v 0
              (by rw [row.property]; decide),
            if_pos (show (0 : ℕ) = ((0#usize : Std.Usize) : ℕ) from rfl)]
          exact hv c hc
        · rw [if_neg h2]
          exact hpre a ha (by omega) c hc
      rw [show core.num.Usize.is_multiple_of MU 8#usize
        = ok (MU.val % ((8#usize : Std.Usize) : ℕ) == 0) from rfl, bind_tc_ok]
      by_cases hb8 : (MU.val % ((8#usize : Std.Usize) : ℕ) == 0) = true
      · rw [if_pos hb8]
        let* ⟨ row, back, hrow2, hback ⟩ ← Array.index_mut_usize_spec secret i hia
        let* ⟨ re0, back1, hre0, hback1 ⟩ ← Array.index_mut_usize_spec row 0#usize (by
          show ((0#usize : Std.Usize) : ℕ) < (row.val : List RingElem).length
          rw [row.property]; decide)
        let* ⟨ re, hre ⟩ ← CbdGeneric.cbd_bd MU sl re0 hMU hsllen
        refine hcomb _ ?_
        rw [hback1]
        exact hstore re row back (fun s => by rw [hback, Std.Array.set_val_eq]) hre
      · rw [if_neg hb8, Kopis.Neon.neon_cbd_eq sl MU (Std.Array.repeat 256#usize 0#u16) hMU hsllen]
        let* ⟨ re, hre ⟩ ← CbdGeneric.cbd_bd MU sl (Std.Array.repeat 256#usize 0#u16) hMU hsllen
        let* ⟨ row, back, hrow2, hback ⟩ ← Array.index_mut_usize_spec secret i hia
        let* ⟨ row1, hrow1 ⟩ ← Array.update_spec
        refine hcomb _ ?_
        rw [hrow1]
        exact hstore re row back (fun s => by rw [hback, Std.Array.set_val_eq]) hre
    · rw [if_neg hin]
      have hge : L.val ≤ first.val + iter.start.val := by scalar_tac
      apply WP.spec_mono
        (secret_loop0_loop1_bd MU iter1 secret first bufs hMU
          (by rw [hend']; exact hend) (by rw [hstart']; omega) hN hmax
          (fun a ha ha2 c hc => hpre a ha (by rw [hstart'] at ha2; omega) c hc))
      intro r hr
      exact hr
  · let* ⟨ o, iter1, hnone, _ ⟩ ← core.iter.range.IteratorRange.next_Usize_none_spec
    rw [hnone]; simp only [WP.spec_ok]
    intro a ha ha2 c hc
    exact hpre a ha (by scalar_tac) c hc
  termination_by iter.«end».val - iter.start.val
  decreasing_by all_goals (simp only [hend']; omega)

unseal backend.neon.keccak.WAYS in
/-- **The batching loop's coefficient bound.** -/
theorem secret_loop0_bd {L : Std.Usize} (MU N : Std.Usize) (seed : Std.Array Std.U8 32#usize)
    (secret : arithmetic.matrix_arith.Matrix L 1#usize) (first : Std.Usize)
    (hMU : MU.val = 6 ∨ MU.val = 8 ∨ MU.val = 10) (hN : N.val = 32 * MU.val)
    (hmax : L.val + 2 ≤ Std.Usize.max)
    (hpre : ∀ a, a < L.val → a < first.val → ∀ c, c < 256 →
      smallSignedU16 (((secret.val[a]!).val[0]!).val[c]!) (MU.val / 2)) :
    backend.neon.sample.secret_loop0 MU N seed secret first
      ⦃ (r : arithmetic.matrix_arith.Matrix L 1#usize) => ∀ a, a < L.val → ∀ c, c < 256 →
          smallSignedU16 (((r.val[a]!).val[0]!).val[c]!) (MU.val / 2) ⦄ := by
  unfold backend.neon.sample.secret_loop0
  simp only [show backend.neon.keccak.WAYS = 2#usize from by decide]
  by_cases hlt : first < L
  · rw [if_pos hlt]
    have hfv : first.val < L.val := by scalar_tac
    have hL : 0 < L.val := by omega
    let* ⟨ indices1, hidx ⟩ ← secret_loop0_loop0_spec L { start := 0#usize, «end» := 2#usize }
      first (Std.Array.repeat 2#usize (Std.Array.repeat 1#usize 0#u8)) hL (by decide) (by simp)
      (by omega) (by intro lane hlane; simp at hlane)
    obtain ⟨bufs1, hb1, hp0⟩ := WP.spec_imp_exists
      (xof2_turboSHAKE 136#usize 3#u8 seed indices1
        (Std.Array.repeat 2#usize (Std.Array.repeat N 0#u8)) 0 (by omega)
        (Or.inr rfl) (by decide) (by decide) (by decide) (by scalar_tac))
    rw [hb1, bind_tc_ok]
    let* ⟨ secret1, hs1 ⟩ ← secret_loop0_loop1_bd MU { start := 0#usize, «end» := 2#usize }
      secret first bufs1 hMU (by decide) (by simp) hN (by omega)
      (fun a ha ha2 c hc => hpre a ha (by simpa using ha2) c hc)
    let* ⟨ first1, hf1 ⟩ ← Std.Usize.add_spec (x := first) (y := 2#usize) (by scalar_tac)
    apply WP.spec_mono
      (secret_loop0_bd MU N seed secret1 first1 hMU hN hmax
        (fun a ha ha2 c hc => hs1 a ha (by rw [hf1] at ha2; omega) c hc))
    intro r hr
    exact hr
  · rw [if_neg hlt]
    simp only [WP.spec_ok]
    intro a ha c hc
    exact hpre a ha (by scalar_tac) c hc
  termination_by L.val - first.val
  decreasing_by scalar_decr_tac

/-- **`backend::neon::sample::secret`'s coefficient bound.** -/
theorem neon_secret_bd (L MU N : Std.Usize) (seed : Std.Array Std.U8 32#usize)
    (hMU : MU.val = 6 ∨ MU.val = 8 ∨ MU.val = 10) (hN : N.val = 32 * MU.val)
    (hmax : L.val + 2 ≤ Std.Usize.max) :
    backend.neon.sample.secret L MU N seed
      ⦃ (r : arithmetic.matrix_arith.Matrix L 1#usize) => ∀ a, a < L.val → ∀ c, c < 256 →
          smallSignedU16 (((r.val[a]!).val[0]!).val[c]!) (MU.val / 2) ⦄ := by
  unfold backend.neon.sample.secret
  simp only [arithmetic.matrix_arith.Matrix.Insts.CoreDefaultDefault.default,
    arithmetic.ring_arith.RingElem.Insts.CoreDefaultDefault.default, bind_tc_ok]
  apply WP.spec_mono
    (secret_loop0_bd MU N seed _ 0#usize hMU hN hmax (by intro a ha ha2 c hc; simp at ha2))
  intro r hr
  exact hr

/-- **`backend::neon::sample::gen_secret_from_seed`'s coefficient bound.** -/
theorem neon_gen_secret_from_seed_bd (L MU : Std.Usize) (seed : Std.Array Std.U8 32#usize)
    (hMU : MU.val = 6 ∨ MU.val = 8 ∨ MU.val = 10) (hmax : L.val + 2 ≤ Std.Usize.max) :
    backend.neon.sample.gen_secret_from_seed L MU seed
      ⦃ (r : arithmetic.matrix_arith.Matrix L 1#usize) => ∀ a, a < L.val → ∀ c, c < 256 →
          smallSignedU16 (((r.val[a]!).val[0]!).val[c]!) (MU.val / 2) ⦄ := by
  have harm : ∀ (n : Std.Usize), MU.val = 6 ∧ n = 192#usize ∨ MU.val = 8 ∧ n = 256#usize
      ∨ MU.val = 10 ∧ n = 320#usize →
      backend.neon.sample.gen_secret_from_seed L MU seed
        = backend.neon.sample.secret L MU n seed := by
    rintro n (⟨h, rfl⟩ | ⟨h, rfl⟩ | ⟨h, rfl⟩) <;>
      · unfold backend.neon.sample.gen_secret_from_seed
        rw [h]
        rfl
  rcases hMU with h | h | h
  · rw [harm 192#usize (Or.inl ⟨h, rfl⟩)]
    exact neon_secret_bd L MU 192#usize seed (Or.inl h) (by rw [h]; decide) hmax
  · rw [harm 256#usize (Or.inr (Or.inl ⟨h, rfl⟩))]
    exact neon_secret_bd L MU 256#usize seed (Or.inr (Or.inl h)) (by rw [h]; decide) hmax
  · rw [harm 320#usize (Or.inr (Or.inr ⟨h, rfl⟩))]
    exact neon_secret_bd L MU 320#usize seed (Or.inr (Or.inr h)) (by rw [h]; decide) hmax

end
end Kopis.Neon.Properties
