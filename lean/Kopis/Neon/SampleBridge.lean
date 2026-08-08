/-
  # Kopis/Neon/SampleBridge.lean — the NEON sampling loops against the spec.

  `Keccak/Conform.lean` proves `keccak::xof2` is TurboSHAKE.  This file is what sits on top: the
  NEON `sample` module hashes two matrix entries at a time through `xof2`, and the twins in
  `Kopis/Neon/Properties/` need to know that produces the same matrix the portable path does.

  The batching is where the two paths differ.  The portable path hashes one entry per call; the
  NEON path fills two lanes and clamps the trailing ones of a short batch to the last entry, so
  they hash something harmless rather than running off the end.  `batchEntry` is that clamp, and
  the loop below establishes that lane `l` really does carry the row and column of the entry it
  will sample.
-/
import Kopis.Neon.Keccak.Xof2
import Kopis.Neon.Ser
import Spec.Kopis.Spec
import Kopis.Neon.Properties.Serialize

open Aeneas Aeneas.Std Result
open RustKopisNeon
open Kopis.Neon
open Kopis.Neon.Keccak (min_usize_eq xof2_turboSHAKE)
open Kopis.Keccak (getElem!_list_set bytesOf msgOf getElem!_bytesOf getElem!_msgOf)
open Kopis.Properties (streamNat streamNat_lt)
open Spec (𝔹)
open scoped Spec.Notations
open Spec.TurboSHAKE (turboSHAKE128)
open arithmetic.ring_arith (RingElem)

namespace Kopis.Neon.Properties

set_option maxHeartbeats 4000000
set_option maxRecDepth 2000000

noncomputable section

/-- A `Usize` truncated to a byte is that value mod 256, which is exactly how the spec reads a
row or column index (`(i : Byte)`).  Stating the index loop at this level rather than at
`.val` level is what lets the NEON sampler be proved correct for *every* `L` — including
`L > 255`, where both the Rust and the spec alias, and agree in doing so. -/
theorem usize_cast_u8_bv (x : Std.Usize) : (Std.UScalar.cast .U8 x).bv = ((x.val : ℕ) : Byte) := by
  apply BitVec.eq_of_toNat_eq
  simp only [Std.UScalar.cast, BitVec.toNat_setWidth]
  rfl

/-- The entry a given lane of a two-wide batch samples: the batch's `first + lane`, clamped to
the last entry so the trailing lanes of a short batch hash something harmless rather than running
off the end. -/
def batchEntry (entries first lane : ℕ) : ℕ := min (first + lane) (entries - 1)

/-- **The index-pair loop.**  Lane `lane`'s two suffix bytes are the row and column of the entry
that lane will sample. -/
theorem gen_matrix_from_seed_loop0_loop0_spec (L : Std.Usize)
    (iter : core.ops.range.Range Std.Usize) (entries first : Std.Usize)
    (indices : Std.Array (Std.Array Std.U8 2#usize) 2#usize)
    (hL : 0 < L.val) (hmaxe : entries.val + 2 ≤ Std.Usize.max) (hend : iter.«end».val = 2)
    (hstart : iter.start.val ≤ 2) (hent : 0 < entries.val) (hentL : entries.val = L.val * L.val)
    (hfirst : first.val < entries.val)
    (hpre : ∀ lane < iter.start.val,
      ((indices.val[lane]!).val[0]!).bv
        = ((batchEntry entries.val first.val lane / L.val : ℕ) : Byte) ∧
      ((indices.val[lane]!).val[1]!).bv
        = ((batchEntry entries.val first.val lane % L.val : ℕ) : Byte)) :
    backend.neon.sample.gen_matrix_from_seed_loop0_loop0 L iter entries first indices
      ⦃ (r : Std.Array (Std.Array Std.U8 2#usize) 2#usize) => ∀ lane < 2,
          ((r.val[lane]!).val[0]!).bv
            = ((batchEntry entries.val first.val lane / L.val : ℕ) : Byte) ∧
          ((r.val[lane]!).val[1]!).bv
            = ((batchEntry entries.val first.val lane % L.val : ℕ) : Byte) ⦄ := by
  unfold backend.neon.sample.gen_matrix_from_seed_loop0_loop0
  by_cases hlt : iter.start.val < iter.«end».val
  · let* ⟨ o, iter1, ho, hstart', hend' ⟩ ← core.iter.range.IteratorRange.next_Usize_some_spec
    rw [ho]; simp only
    have hl4 : iter.start.val < 2 := by scalar_tac
    let* ⟨ i, hi ⟩ ← Std.Usize.add_spec (x := first) (y := iter.start) (by scalar_tac)
    let* ⟨ i1, hi1 ⟩ ← Std.Usize.sub_spec (x := entries) (y := 1#usize) (by scalar_tac)
    rw [min_usize_eq, bind_tc_ok]
    have hbv : ((if i.val < i1.val then i else i1) : Std.Usize).val
        = batchEntry entries.val first.val iter.start.val := by
      simp only [batchEntry]; split <;> omega
    have hblt : batchEntry entries.val first.val iter.start.val < entries.val := by
      simp only [batchEntry]; omega
    let* ⟨ q, hq ⟩ ← Std.Usize.div_spec
    have hqv : q.val = batchEntry entries.val first.val iter.start.val / L.val := by
      rw [hq, hbv]
    have hqlt : q.val < L.val := by
      rw [hqv]; exact Nat.div_lt_of_lt_mul (by omega)
    have hilen : (indices.val : List (Std.Array Std.U8 2#usize)).length = 2 := indices.property
    let* ⟨ row, back, hrow, hback ⟩ ← Array.index_mut_usize_spec indices iter.start (by scalar_tac)
    rw [show (lift (Std.UScalar.cast .U8 q) : Result Std.U8) = ok (Std.UScalar.cast .U8 q)
      from rfl, bind_tc_ok]
    let* ⟨ row1, hrow1 ⟩ ← Array.update_spec
    let* ⟨ m, hm ⟩ ← Std.Usize.rem_spec
    have hmv : m.val = batchEntry entries.val first.val iter.start.val % L.val := by
      rw [hm, hbv]
    let* ⟨ row2, back2, hrow2, hback2 ⟩ ←
      Array.index_mut_usize_spec (back row1) iter.start (by scalar_tac)
    rw [show (lift (Std.UScalar.cast .U8 m) : Result Std.U8) = ok (Std.UScalar.cast .U8 m)
      from rfl, bind_tc_ok]
    have hlen2 : ∀ (r : Std.Array Std.U8 2#usize), (r.val : List Std.U8).length = 2 :=
      fun r => r.property
    let* ⟨ row3, hrow3 ⟩ ← Array.update_spec
    have hr2v : row2 = row1 := by
      have h := hrow2.trans (getElem!_pos (back row1).val iter.start.val (by scalar_tac)).symm
      rw [h, hback, Std.Array.set_val_eq,
        getElem!_list_set indices.val iter.start.val row1 iter.start.val
          (by rw [hilen]; exact hl4), if_pos rfl]
    have hpre' : ∀ lane < iter1.start.val,
        (((back2 row3).val[lane]!).val[0]!).bv
          = ((batchEntry entries.val first.val lane / L.val : ℕ) : Byte) ∧
        (((back2 row3).val[lane]!).val[1]!).bv
          = ((batchEntry entries.val first.val lane % L.val : ℕ) : Byte) := by
      intro lane hlane
      rw [hstart'] at hlane
      have u0 : ((0#usize : Std.Usize) : ℕ) = 0 := rfl
      have u1 : ((1#usize : Std.Usize) : ℕ) = 1 := rfl
      rw [hback2, Std.Array.set_val_eq,
        getElem!_list_set (back row1).val iter.start.val row3 lane
          (by rw [(back row1).property]; exact hl4)]
      by_cases h : lane = iter.start.val
      · rw [if_pos h, h, hrow3, hr2v, Std.Array.set_val_eq, u1,
          getElem!_list_set row1.val 1 (Std.UScalar.cast .U8 m) 0 (by rw [hlen2]; omega),
          if_neg (by omega),
          getElem!_list_set row1.val 1 (Std.UScalar.cast .U8 m) 1 (by rw [hlen2]; omega),
          if_pos rfl, hrow1, Std.Array.set_val_eq, u0,
          getElem!_list_set row.val 0 (Std.UScalar.cast .U8 q) 0 (by rw [hlen2]; omega),
          if_pos rfl]
        refine ⟨?_, ?_⟩
        · rw [show Std.U8.bv (Std.UScalar.cast .U8 q) = ((q.val : ℕ) : Byte) from usize_cast_u8_bv q,
            hqv]
        · rw [show Std.U8.bv (Std.UScalar.cast .U8 m) = ((m.val : ℕ) : Byte) from usize_cast_u8_bv m,
            hmv]
      · rw [if_neg h, hback, Std.Array.set_val_eq,
          getElem!_list_set indices.val iter.start.val row1 lane (by rw [hilen]; exact hl4),
          if_neg h]
        exact hpre lane (by omega)
    apply WP.spec_mono
      (gen_matrix_from_seed_loop0_loop0_spec L iter1 entries first (back2 row3) hL hmaxe
        (by rw [hend']; exact hend) (by rw [hstart']; omega) hent hentL hfirst hpre')
    intro r hr
    exact hr
  · let* ⟨ o, iter1, hnone, _ ⟩ ← core.iter.range.IteratorRange.next_Usize_none_spec
    rw [hnone]; simp only [WP.spec_ok]
    intro lane hlane
    have hge : 2 ≤ iter.start.val := by omega
    exact hpre lane (by omega)
  termination_by iter.«end».val - iter.start.val
  decreasing_by simp only [hend']; omega

/-- **The deserialize loop.**  Each lane whose entry is in range is unpacked out of that lane's
`xof2` buffer into its matrix slot; lanes past the end of the matrix are skipped, and every other
slot is left alone. -/
theorem gen_matrix_from_seed_loop0_loop1_spec {L : Std.Usize}
    (iter : core.ops.range.Range Std.Usize)
    (mat : arithmetic.matrix_arith.Matrix L L) (entries first : Std.Usize)
    (bufs : Std.Array (Std.Array Std.U8 416#usize) 2#usize)
    (hL : 0 < L.val) (hend : iter.«end».val = 2) (hstart : iter.start.val ≤ 2)
    (hentL : entries.val = L.val * L.val) (hfirst : first.val < entries.val)
    (hmax : first.val + 2 ≤ Std.Usize.max) :
    backend.neon.sample.gen_matrix_from_seed_loop0_loop1 iter mat entries bufs first
      ⦃ (r : arithmetic.matrix_arith.Matrix L L) => ∀ a < L.val, ∀ b < L.val, ∀ j < 256,
          (((r.val[a]!).val[b]!).val[j]!).val =
            if first.val + iter.start.val ≤ a * L.val + b ∧ a * L.val + b < first.val + 2
                ∧ a * L.val + b < entries.val
            then streamNat (Std.Array.to_slice (bufs.val[a * L.val + b - first.val]!))
                   (13 * j) 13
            else (((mat.val[a]!).val[b]!).val[j]!).val ⦄ := by
  unfold backend.neon.sample.gen_matrix_from_seed_loop0_loop1
  by_cases hlt : iter.start.val < iter.«end».val
  · let* ⟨ o, iter1, ho, hstart', hend' ⟩ ← core.iter.range.IteratorRange.next_Usize_some_spec
    rw [ho]; simp only
    have hl4 : iter.start.val < 2 := by scalar_tac
    let* ⟨ entry, hentry ⟩ ← Std.Usize.add_spec (x := first) (y := iter.start) (by scalar_tac)
    by_cases hin : entry < entries
    · rw [if_pos hin]
      let* ⟨ buf, hbuf ⟩ ← Array.index_usize_spec bufs iter.start (by scalar_tac)
      have hblen : (buf.val : List Std.U8).length = 416 := buf.property
      rw [show (lift (Std.Array.to_slice buf) : Result (Slice Std.U8))
        = ok (Std.Array.to_slice buf) from rfl, bind_tc_ok]
      have hsllen : (Std.Array.to_slice buf).length = 32 * 13 := by
        simp only [Slice.length, Std.Array.to_slice, hblen]
      let* ⟨ re, hre ⟩ ← Kopis.Neon.deserialize_streamNat (Std.Array.to_slice buf) 13
        (by omega) (by omega) hsllen consts.MODULUS_Q_BITS (by simp [consts.MODULUS_Q_BITS])
      let* ⟨ q, hq ⟩ ← Std.Usize.div_spec
      let* ⟨ m, hm ⟩ ← Std.Usize.rem_spec
      have hentv : entry.val = first.val + iter.start.val := hentry
      have hinv : entry.val < entries.val := by scalar_tac
      have hqlt : q.val < L.val := by rw [hq]; exact Nat.div_lt_of_lt_mul (by omega)
      have hmlt : m.val < L.val := by rw [hm]; exact Nat.mod_lt _ hL
      let* ⟨ row, back, hrow, hback ⟩ ← Array.index_mut_usize_spec mat q (by scalar_tac)
      let* ⟨ row1, hrow1 ⟩ ← Array.update_spec
      have hmatlen : (mat.val : List (Std.Array arithmetic.ring_arith.RingElem L)).length = L.val :=
        mat.property
      have hrowlen : ∀ (r : Std.Array arithmetic.ring_arith.RingElem L),
          (r.val : List arithmetic.ring_arith.RingElem).length = L.val := fun r => r.property
      have hqm : q.val * L.val + m.val = entry.val := by
        rw [hq, hm, Nat.mul_comm]; exact Nat.div_add_mod _ _
      have hrowv : row = mat.val[q.val]! :=
        hrow.trans (getElem!_pos mat.val q.val (by rw [hmatlen]; exact hqlt)).symm
      have hread : ∀ a < L.val, ∀ b < L.val,
          ((back row1).val[a]!).val[b]! =
            if a = q.val ∧ b = m.val then re else (mat.val[a]!).val[b]! := by
        intro a ha b hb
        rw [hback, Std.Array.set_val_eq,
          getElem!_list_set mat.val q.val row1 a (by rw [hmatlen]; exact hqlt)]
        by_cases hqa : a = q.val
        · rw [if_pos hqa, hrow1, Std.Array.set_val_eq,
            getElem!_list_set row.val m.val re b (by rw [hrowlen]; exact hmlt), hrowv, hqa]
          by_cases hmb : b = m.val
          · rw [if_pos hmb, if_pos ⟨rfl, hmb⟩]
          · rw [if_neg hmb, if_neg (by tauto)]
        · rw [if_neg hqa, if_neg (by tauto)]
      have hbufv : bufs.val[iter.start.val]! = buf :=
        (getElem!_pos bufs.val iter.start.val (by scalar_tac)).trans hbuf.symm
      apply WP.spec_mono
        (gen_matrix_from_seed_loop0_loop1_spec iter1 (back row1) entries first bufs hL
          (by rw [hend']; exact hend) (by rw [hstart']; omega) hentL hfirst hmax)
      intro r hr a ha b hb j hj
      have hadiv : (a * L.val + b) / L.val = a := by
        rw [Nat.mul_comm, Nat.add_comm, Nat.add_mul_div_left _ _ hL, Nat.div_eq_of_lt hb]
        omega
      have hamod : (a * L.val + b) % L.val = b := by
        rw [Nat.mul_comm, Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hb]
      rw [hr a ha b hb j hj, hstart']
      by_cases h1 : first.val + (iter.start.val + 1) ≤ a * L.val + b
          ∧ a * L.val + b < first.val + 2 ∧ a * L.val + b < entries.val
      · rw [if_pos h1, if_pos ⟨by omega, h1.2.1, h1.2.2⟩]
      · rw [if_neg h1, hread a ha b hb]
        by_cases h2 : a = q.val ∧ b = m.val
        · have habe : a * L.val + b = entry.val := by rw [h2.1, h2.2]; exact hqm
          rw [if_pos h2, if_pos ⟨by omega, by omega, by omega⟩, hre j hj,
            show a * L.val + b - first.val = iter.start.val from by omega, hbufv]
        · have hne : ¬(first.val + iter.start.val ≤ a * L.val + b
              ∧ a * L.val + b < first.val + 2 ∧ a * L.val + b < entries.val) := by
            rintro ⟨hc1, hc2, hc3⟩
            have habe : a * L.val + b = entry.val := by omega
            exact h2 ⟨by rw [← hadiv, habe, hq], by rw [← hamod, habe, hm]⟩
          rw [if_neg h2, if_neg hne]
    · rw [if_neg hin]
      have hgeq : entries.val ≤ first.val + iter.start.val := by scalar_tac
      apply WP.spec_mono
        (gen_matrix_from_seed_loop0_loop1_spec iter1 mat entries first bufs hL
          (by rw [hend']; exact hend) (by rw [hstart']; omega) hentL hfirst hmax)
      intro r hr a ha b hb j hj
      rw [hr a ha b hb j hj, hstart', if_neg (by omega), if_neg (by omega)]
  · let* ⟨ o, iter1, hnone, _ ⟩ ← core.iter.range.IteratorRange.next_Usize_none_spec
    rw [hnone]; simp only [WP.spec_ok]
    intro a ha b hb j hj
    have hge : 2 ≤ iter.start.val := by omega
    rw [if_neg (by omega)]
  termination_by iter.«end».val - iter.start.val
  decreasing_by all_goals (simp only [hend']; omega)

/-! ## Matching the spec's message -/

/-- `Spec.Notations`' `‖` is the bare `Vector.append`, while the `getElem` lemmas are stated for
`++` (`HAppend.hAppend`).  The two are defeq but not syntactically equal, so rewriting with
`Vector.getElem_append` silently matches nothing against a `‖`.  This turns one into the other. -/
theorem vappend_eq {α : Type _} {m n : ℕ} (u : Vector α m) (v : Vector α n) :
    Vector.append u v = u ++ v := rfl

/-- The seed as a spec byte vector at the literal length 32 — `bytesOf` gives `𝔹 ↑32#usize`,
whose size index is not syntactically `32`, which stops `Vector.getElem_append` firing. -/
def seedBytes (seed : Std.Array Std.U8 32#usize) : 𝔹 32 := (bytesOf seed).cast (by simp)

theorem getElem!_seedBytes (seed : Std.Array Std.U8 32#usize) (j : ℕ) (hj : j < 32) :
    (seedBytes seed)[j]! = (seed.val[j]!).bv := by
  rw [getElem!_pos _ j (by simpa using hj), seedBytes, Vector.getElem_cast,
    ← getElem!_pos _ j (by simpa using hj), getElem!_bytesOf seed j (by simpa using hj)]

/-- The spec value of matrix entry `(a, b)`. -/
def entryOf (seed : Std.Array Std.U8 32#usize) (a b : ℕ) : Spec.Kopis.Polynomial (2 ^ 13) :=
  Spec.Kopis.deserialize 13
    (turboSHAKE128 (seedBytes seed ‖ #v[(a : Byte)] ‖ #v[(b : Byte)])
      Spec.Kopis.DOMSEP_GENMAT (32 * 13))

/-- The message `xof2` hashes for entry `(a, b)` is the spec's `seed ‖ a ‖ b`. -/
theorem msgOf_eq (seed : Std.Array Std.U8 32#usize) (suf : Std.Array Std.U8 2#usize) (a b : ℕ)
    (ha : (suf.val[0]!).bv = ((a : ℕ) : Byte)) (hb : (suf.val[1]!).bv = ((b : ℕ) : Byte)) :
    msgOf seed suf = (seedBytes seed ‖ #v[(a : Byte)] ‖ #v[(b : Byte)]).cast (by simp) := by
  apply Vector.ext
  intro j hj
  have h2u : ((2#usize : Std.Usize) : ℕ) = 2 := rfl
  have hj34 : j < 34 := by simp at hj; omega
  have hbv : ∀ (x : Std.U8), x.bv = ((x.val : ℕ) : Byte) := by
    intro x
    apply BitVec.eq_of_toNat_eq
    simp only [Std.UScalar.val]
    exact (Nat.mod_eq_of_lt x.bv.isLt).symm
  rw [← getElem!_pos _ j hj, getElem!_msgOf seed suf j (by simpa using hj)]
  simp only [Vector.getElem_cast, vappend_eq, Vector.getElem_append]
  by_cases h32 : j < 32
  · rw [if_pos h32, dif_pos (by omega), dif_pos (by omega),
      ← getElem!_pos _ j (by simpa using h32), getElem!_seedBytes seed j h32]
  · rw [if_neg h32]
    by_cases h33 : j < 33
    · rw [dif_pos (by omega), dif_neg (by omega)]
      simp only [show j - 32 = 0 from by omega]
      rw [ha]
      simp
    · rw [dif_neg (by omega)]
      simp only [show j - (32 + 1) = 0 from by omega, show j - 32 = 1 from by omega]
      rw [hb]
      simp

/-- **A lane's `xof2` buffer is the spec's hash for that entry.**  Reading the buffer as a spec
byte vector gives `turboSHAKE128 (seed ‖ a ‖ b) DOMSEP_GENMAT 416` exactly. -/
theorem bufBytes_eq (seed : Std.Array Std.U8 32#usize) (suf : Std.Array Std.U8 2#usize)
    (buf : Std.Array Std.U8 416#usize) (a b : ℕ)
    (ha : (suf.val[0]!).bv = ((a : ℕ) : Byte)) (hb : (suf.val[1]!).bv = ((b : ℕ) : Byte))
    (hbuf : ∀ j < 416,
      ((buf.val[j]!).bv) = (turboSHAKE128 (msgOf seed suf) (2#u8).bv 416)[j]!)
    (hlen : (Std.Array.to_slice buf).length = 32 * 13) :
    sliceToBytes (Std.Array.to_slice buf) (32 * 13) hlen
      = turboSHAKE128 (seedBytes seed ‖ #v[(a : Byte)] ‖ #v[(b : Byte)])
          Spec.Kopis.DOMSEP_GENMAT (32 * 13) := by
  have hdom : (2#u8 : Std.U8).bv = Spec.Kopis.DOMSEP_GENMAT := by decide
  have hcast : ∀ {m n : ℕ} (v : 𝔹 m) (h : m = n) (D : Byte) (o : ℕ),
      turboSHAKE128 (v.cast h) D o = turboSHAKE128 v D o := by
    intro m n v h D o; subst h; rfl
  apply Vector.ext
  intro j hj
  have hj416 : j < 416 := by omega
  simp only [sliceToBytes, Vector.getElem_ofFn, Std.Array.to_slice]
  rw [← getElem!_pos buf.val j (by rw [buf.property]; exact hj416), hbuf j hj416,
    msgOf_eq seed suf a b ha hb, hdom, hcast,
    ← getElem!_pos (turboSHAKE128 (seedBytes seed ‖ #v[(a : Byte)] ‖ #v[(b : Byte)])
      Spec.Kopis.DOMSEP_GENMAT (32 * 13)) j hj]

/-! ## The batching loop -/

/-- Two `RingElem`s with the same coefficient values give the same spec polynomial. -/
theorem toRingElem13_congr (x y : arithmetic.ring_arith.RingElem)
    (h : ∀ j < 256, (x.val[j]!).val = (y.val[j]!).val) : toRingElem13 x = toRingElem13 y := by
  have hx : (x.val : List Std.U16).length = 256 := by have := x.property; scalar_tac
  have hy : (y.val : List Std.U16).length = 256 := by have := y.property; scalar_tac
  apply Vector.ext
  intro j hj
  simp only [toRingElem13, Vector.getElem_ofFn]
  rw [← getElem!_pos x.val j (by rw [hx]; exact hj), ← getElem!_pos y.val j (by rw [hy]; exact hj),
    h j hj]

unseal backend.neon.keccak.WAYS in
/-- **The batching loop.**  Two entries per `xof2` call; every entry from `first` on ends up
holding the spec's value for its coordinates. -/
theorem gen_matrix_from_seed_loop0_spec {L : Std.Usize} (seed : Std.Array Std.U8 32#usize)
    (mat : arithmetic.matrix_arith.Matrix L L) (entries : Std.Usize)
    (bufs : Std.Array (Std.Array Std.U8 416#usize) 2#usize) (first : Std.Usize)
    (hentL : entries.val = L.val * L.val) (hmax : entries.val + 2 ≤ Std.Usize.max) :
    backend.neon.sample.gen_matrix_from_seed_loop0 seed mat entries bufs first
      ⦃ (r : arithmetic.matrix_arith.Matrix L L) => ∀ a < L.val, ∀ b < L.val,
          toRingElem13 ((r.val[a]!).val[b]!) =
            if first.val ≤ a * L.val + b then entryOf seed a b
            else toRingElem13 ((mat.val[a]!).val[b]!) ⦄ := by
  unfold backend.neon.sample.gen_matrix_from_seed_loop0
  simp only [show backend.neon.keccak.WAYS = 2#usize from by decide]
  by_cases hlt : first < entries
  · rw [if_pos hlt]
    have hfv : first.val < entries.val := by scalar_tac
    -- `L = 0` would make `entries = 0`, so this branch already witnesses `0 < L`
    have hL : 0 < L.val := by
      rcases Nat.eq_zero_or_pos L.val with h | h
      · rw [hentL, h] at hfv; omega
      · exact h
    let* ⟨ indices1, hidx ⟩ ← gen_matrix_from_seed_loop0_loop0_spec L
      { start := 0#usize, «end» := 2#usize }
      entries first (Std.Array.repeat 2#usize (Std.Array.repeat 2#usize 0#u8))
      hL hmax (by decide) (by simp) (by omega) hentL hfv (by intro lane hlane; simp at hlane)
    obtain ⟨bufs1, hb1, hp0⟩ := WP.spec_imp_exists
      (xof2_turboSHAKE 168#usize 2#u8 seed indices1
        bufs 0 (by omega)
        (Or.inl rfl) (by decide) (by decide) (by decide) (by scalar_tac))
    rw [hb1, bind_tc_ok]
    have hlane : ∀ l, l < 2 → ∀ j < 416,
        ((bufs1.val[l]!).val[j]!).bv
          = (turboSHAKE128 (msgOf seed (indices1.val[l]!)) (2#u8).bv 416)[j]! := by
      intro l hl
      have h := xof2_turboSHAKE 168#usize 2#u8 seed indices1
        bufs l hl
        (Or.inl rfl) (by decide) (by decide) (by decide) (by scalar_tac)
      rw [hb1] at h
      simp only [WP.spec_ok] at h
      exact h
    let* ⟨ mat1, hm1 ⟩ ← gen_matrix_from_seed_loop0_loop1_spec
      { start := 0#usize, «end» := 2#usize } mat entries first bufs1
      hL (by decide) (by simp) hentL hfv (by omega)
    let* ⟨ first1, hf1 ⟩ ← Std.Usize.add_spec (x := first) (y := 2#usize) (by scalar_tac)
    apply WP.spec_mono
      (gen_matrix_from_seed_loop0_spec seed mat1 entries bufs1 first1 hentL hmax)
    intro r hr a ha b hb
    have habe : a * L.val + b < entries.val := by
      rw [hentL]; calc a * L.val + b < a * L.val + L.val := by omega
        _ = (a + 1) * L.val := by ring
        _ ≤ L.val * L.val := by
            rw [Nat.mul_comm]; exact Nat.mul_le_mul_left _ (by omega)
    rw [hr a ha b hb, hf1]
    by_cases h4 : first.val + 2 ≤ a * L.val + b
    · rw [if_pos h4, if_pos (by omega)]
    · rw [if_neg h4]
      by_cases h0 : first.val ≤ a * L.val + b
      · rw [if_pos h0]
        have hadiv : (a * L.val + b) / L.val = a := by
          rw [Nat.mul_comm, Nat.add_comm, Nat.add_mul_div_left _ _ hL, Nat.div_eq_of_lt hb]
          omega
        have hamod : (a * L.val + b) % L.val = b := by
          rw [Nat.mul_comm, Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hb]
        have hlane4 : a * L.val + b - first.val < 2 := by omega
        have hbe : batchEntry entries.val first.val (a * L.val + b - first.val)
            = a * L.val + b := by simp only [batchEntry]; omega
        have hi0 : ((indices1.val[a * L.val + b - first.val]!).val[0]!).bv
            = ((a : ℕ) : Byte) := by rw [(hidx _ hlane4).1, hbe, hadiv]
        have hi1 : ((indices1.val[a * L.val + b - first.val]!).val[1]!).bv
            = ((b : ℕ) : Byte) := by rw [(hidx _ hlane4).2, hbe, hamod]
        have hslen : (Std.Array.to_slice (bufs1.val[a * L.val + b - first.val]!)).length
            = 32 * 13 := by
          simp only [Slice.length, Std.Array.to_slice,
            (bufs1.val[a * L.val + b - first.val]!).property]
          decide
        rw [toRingElem13_of_streamNat _ hslen _
              (fun j hj => by rw [hm1 a ha b hb j hj, if_pos ⟨h0, by omega, habe⟩]),
          bufBytes_eq seed _ _ a b hi0 hi1 (hlane _ hlane4) hslen]
        rfl
      · rw [if_neg h0]
        exact toRingElem13_congr _ _ (fun j hj => by
          rw [hm1 a ha b hb j hj, if_neg (by omega)])
  · rw [if_neg hlt]
    simp only [WP.spec_ok]
    intro a ha b hb
    have habe : a * L.val + b < entries.val := by
      rw [hentL]; calc a * L.val + b < a * L.val + L.val := by omega
        _ = (a + 1) * L.val := by ring
        _ ≤ L.val * L.val := by
            rw [Nat.mul_comm]; exact Nat.mul_le_mul_left _ (by omega)
    rw [if_neg (by scalar_tac)]
  termination_by entries.val - first.val
  decreasing_by scalar_decr_tac

/-! ## The entry point -/

/-- **`backend::neon::sample::gen_matrix_from_seed` matches the spec.**  Every entry is the
spec's hash-derived polynomial for its coordinates. -/
theorem neon_gen_matrix_from_seed_spec (L : Std.Usize) (seed : Std.Array Std.U8 32#usize)
    (hmax : L.val * L.val + 2 ≤ Std.Usize.max) :
    backend.neon.sample.gen_matrix_from_seed L seed
      ⦃ (r : arithmetic.matrix_arith.Matrix L L) => ∀ a < L.val, ∀ b < L.val,
          toRingElem13 ((r.val[a]!).val[b]!) = entryOf seed a b ⦄ := by
  unfold backend.neon.sample.gen_matrix_from_seed
  simp only [arithmetic.matrix_arith.Matrix.Insts.CoreDefaultDefault.default,
    arithmetic.ring_arith.RingElem.Insts.CoreDefaultDefault.default, bind_tc_ok]
  let* ⟨ entries, hent ⟩ ← Std.Usize.mul_spec (x := L) (y := L) (by scalar_tac)
  apply WP.spec_mono (gen_matrix_from_seed_loop0_spec seed _ entries _ 0#usize
    (by rw [hent]) (by rw [hent]; omega))
  intro r hr a ha b hb
  rw [hr a ha b hb, if_pos (by simp)]


/-! ## The coefficient bound -/

unseal backend.neon.keccak.WAYS in
/-- **The batching loop's coefficient bound.**  Every entry the loop writes is a 13-bit window,
hence below `2¹³`; entries it does not touch keep whatever bound they had. -/
theorem gen_matrix_from_seed_loop0_bd {L : Std.Usize} (seed : Std.Array Std.U8 32#usize)
    (mat : arithmetic.matrix_arith.Matrix L L) (entries : Std.Usize)
    (bufs : Std.Array (Std.Array Std.U8 416#usize) 2#usize) (first : Std.Usize)
    (hentL : entries.val = L.val * L.val) (hmax : entries.val + 2 ≤ Std.Usize.max)
    (hpre : ∀ a b c, a < L.val → b < L.val → c < 256 → a * L.val + b < first.val →
      (((mat.val[a]!).val[b]!).val[c]!).val < 2 ^ 13) :
    backend.neon.sample.gen_matrix_from_seed_loop0 seed mat entries bufs first
      ⦃ (r : arithmetic.matrix_arith.Matrix L L) => ∀ a b c, a < L.val → b < L.val → c < 256 →
          (((r.val[a]!).val[b]!).val[c]!).val < 2 ^ 13 ⦄ := by
  unfold backend.neon.sample.gen_matrix_from_seed_loop0
  simp only [show backend.neon.keccak.WAYS = 2#usize from by decide]
  by_cases hlt : first < entries
  · rw [if_pos hlt]
    have hfv : first.val < entries.val := by scalar_tac
    have hL : 0 < L.val := by
      rcases Nat.eq_zero_or_pos L.val with h | h
      · rw [hentL, h] at hfv; omega
      · exact h
    let* ⟨ indices1, hidx ⟩ ← gen_matrix_from_seed_loop0_loop0_spec L
      { start := 0#usize, «end» := 2#usize }
      entries first (Std.Array.repeat 2#usize (Std.Array.repeat 2#usize 0#u8))
      hL hmax (by decide) (by simp) (by omega) hentL hfv (by intro lane hlane; simp at hlane)
    obtain ⟨bufs1, hb1, hp0⟩ := WP.spec_imp_exists
      (Kopis.Neon.Keccak.xof2_turboSHAKE 168#usize 2#u8 seed indices1
        bufs 0 (by omega)
        (Or.inl rfl) (by decide) (by decide) (by decide) (by scalar_tac))
    rw [hb1, bind_tc_ok]
    let* ⟨ mat1, hm1 ⟩ ← gen_matrix_from_seed_loop0_loop1_spec
      { start := 0#usize, «end» := 2#usize } mat entries first bufs1
      hL (by decide) (by simp) hentL hfv (by omega)
    let* ⟨ first1, hf1 ⟩ ← Std.Usize.add_spec (x := first) (y := 2#usize) (by scalar_tac)
    apply WP.spec_mono
      (gen_matrix_from_seed_loop0_bd seed mat1 entries bufs1 first1 hentL hmax ?_)
    · intro r hr
      exact hr
    · intro a b c ha hb hc hlt2
      have habe : a * L.val + b < entries.val := by
        rw [hentL]; calc a * L.val + b < a * L.val + L.val := by omega
          _ = (a + 1) * L.val := by ring
          _ ≤ L.val * L.val := by
              rw [Nat.mul_comm]; exact Nat.mul_le_mul_left _ (by omega)
      rw [hm1 a ha b hb c hc]
      by_cases hw : first.val + 0 ≤ a * L.val + b ∧ a * L.val + b < first.val + 2
          ∧ a * L.val + b < entries.val
      · rw [if_pos hw]
        exact streamNat_lt _ _ _
      · rw [if_neg hw]
        exact hpre a b c ha hb hc (by rw [hf1] at hlt2; omega)
  · rw [if_neg hlt]
    simp only [WP.spec_ok]
    intro a b c ha hb hc
    have habe : a * L.val + b < entries.val := by
      rw [hentL]; calc a * L.val + b < a * L.val + L.val := by omega
        _ = (a + 1) * L.val := by ring
        _ ≤ L.val * L.val := by
            rw [Nat.mul_comm]; exact Nat.mul_le_mul_left _ (by omega)
    exact hpre a b c ha hb hc (by scalar_tac)
  termination_by entries.val - first.val
  decreasing_by scalar_decr_tac

/-- **`backend::neon::sample::gen_matrix_from_seed`'s coefficient bound.** -/
theorem neon_gen_matrix_from_seed_bd (L : Std.Usize) (seed : Std.Array Std.U8 32#usize)
    (hmax : L.val * L.val + 2 ≤ Std.Usize.max) :
    backend.neon.sample.gen_matrix_from_seed L seed
      ⦃ (r : arithmetic.matrix_arith.Matrix L L) => ∀ a b c, a < L.val → b < L.val → c < 256 →
          (((r.val[a]!).val[b]!).val[c]!).val < 2 ^ 13 ⦄ := by
  unfold backend.neon.sample.gen_matrix_from_seed
  simp only [arithmetic.matrix_arith.Matrix.Insts.CoreDefaultDefault.default,
    arithmetic.ring_arith.RingElem.Insts.CoreDefaultDefault.default, bind_tc_ok]
  let* ⟨ entries, hent ⟩ ← Std.Usize.mul_spec (x := L) (y := L) (by scalar_tac)
  apply WP.spec_mono
    (gen_matrix_from_seed_loop0_bd seed _ entries _ 0#usize (by rw [hent]) (by rw [hent]; omega)
      (by intro a b c ha hb hc h0; simp at h0))
  intro r hr
  exact hr

end
end Kopis.Neon.Properties
