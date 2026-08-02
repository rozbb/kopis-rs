/-
  # Kopis/Properties/GenMatrix.lean — Correspondence proof for `gen_matrix_from_seed`.

  Relates the Aeneas-extracted `RustKopisSerial.sample.gen_matrix_from_seed` to the audited
  spec `Spec.Kopis.GenMat`.  The procedure decomposes into three layers:

  * **(A) TurboSHAKE — trust boundary.**  The `turboshake` crate is an external
    crates.io dependency, so Aeneas axiomatizes its entire stateful API
    (`default`/`update`/`finalize_xof`/`read`) as opaque constants.  We model that
    API abstractly (`hasherAbsorbed` / `readerModel`) and state its RFC-9861
    contract as `@[step]` axioms — the single assumed correspondence to
    `Spec.TurboSHAKE.turboSHAKE128`.  This is what a separate verification of the
    `turboshake` crate would eventually discharge.
  * **(B) `deserialize` / `from_bytes`** — proved elsewhere; imported here.
  * **(C) the nested matrix-assembly loop** — proved here.
-/
import ExtractedRust
import Spec.Kopis.Spec
import Kopis.Properties.Serialize

open Aeneas Aeneas.Std Result
open RustKopisSerial
open arithmetic.ring_arith (RingElem)
open Spec (𝔹)
open scoped Spec.Notations
open Spec.TurboSHAKE (turboSHAKE128)

namespace Kopis.Properties

/-! ## Byte bridges (local copies to keep Kopis independent of the MLKEM modules) -/

/-- Interpret a `List U8` as a spec byte vector. -/
def u8ListToBytes (l : List U8) : 𝔹 l.length :=
  Vector.ofFn fun (i : Fin l.length) => (l[i.val]).bv

/-- Interpret a Rust `Array U8 n` as a spec `𝔹 n`. -/
def arrayToBytes {n : Usize} (a : Array U8 n) : 𝔹 (n : ℕ) :=
  Vector.ofFn fun (i : Fin (n : ℕ)) => (a.val[i.val]'(by have := a.property; grind)).bv

/-- `arrayToBytes` unfolds to the byte-list mapped through `.bv`. -/
theorem arrayToBytes_toList {n : Usize} (a : Array U8 n) :
    (arrayToBytes a).toList = a.val.map (·.bv) := by
  apply List.ext_getElem
  · have := a.property; simp only [arrayToBytes, Vector.toList_length, List.length_map]; omega
  · intro k h1 h2
    simp only [arrayToBytes, Vector.getElem_toList, Vector.getElem_ofFn, List.getElem_map]

/-! ## (A) TurboSHAKE stateful hasher — abstract model + trust-boundary axioms

`turboshake::TurboShake<RATE, DS>` and `TurboShakeReader<RATE>` are opaque Aeneas
externals.  We give them an abstract model: `hasherAbsorbed h` is the byte string
absorbed into `h` so far, and `readerModel r = (DS, absorbed)` records the domain
separator and absorbed message captured at `finalize_xof`.  The axioms below are
the RFC-9861 contract of the `turboshake` crate — the effort's trust boundary. -/

/-- Abstract state: the bytes absorbed into a hasher so far. -/
opaque hasherAbsorbed {RATE : Usize} {DS : U8} : turboshake.TurboShake RATE DS → List U8

/-- Abstract state of a finalized reader: `(domain separator, absorbed message)`. -/
opaque readerModel {RATE : Usize} : turboshake.TurboShakeReader RATE → U8 × List U8

/-- Abstract consumed-byte offset of a reader: how many XOF bytes have already been
squeezed.  A freshly-finalized reader has offset `0`; each `read` advances it. -/
opaque readerOffset {RATE : Usize} : turboshake.TurboShakeReader RATE → ℕ

/-- `default` yields a hasher with nothing absorbed. -/
@[step] axiom hasher_default_spec (RATE : Usize) (DS : U8) :
    turboshake.TurboShake.Insts.CoreDefaultDefault.default RATE DS
      ⦃ (h : turboshake.TurboShake RATE DS) => hasherAbsorbed h = [] ⦄

/-- `update h s` appends `s` to the absorbed bytes. -/
@[step] axiom hasher_update_spec {RATE : Usize} {DS : U8}
    (h : turboshake.TurboShake RATE DS) (s : Slice U8) :
    turboshake.TurboShake.Insts.DigestUpdate.update h s
      ⦃ (h' : turboshake.TurboShake RATE DS) => hasherAbsorbed h' = hasherAbsorbed h ++ s.val ⦄

/-- `finalize_xof` freezes the domain separator and absorbed message into the reader,
which starts at consumed-offset `0`. -/
@[step] axiom hasher_finalize_spec {RATE : Usize} {DS : U8}
    (h : turboshake.TurboShake RATE DS) :
    turboshake.TurboShake.Insts.DigestExtendableOutputTurboShakeReader.finalize_xof h
      ⦃ (r : turboshake.TurboShakeReader RATE) =>
          readerModel r = (DS, hasherAbsorbed h) ∧ readerOffset r = 0 ⦄

/-- `read` (RATE = 168 ⇒ TurboSHAKE128) fills `out` with the next `out.length` bytes of
the XOF stream, starting at the reader's consumed offset, and advances that offset.  The
output is the `[offset, offset+len)` window of the squeeze, i.e. the length-`offset+len`
squeeze with its first `offset` bytes dropped (XOF prefix/streaming property, RFC-9861). -/
@[step] axiom reader_read168_spec
    (r : turboshake.TurboShakeReader 168#usize) (out : Slice U8) :
    turboshake.TurboShakeReader.Insts.DigestXofReader.read r out
      ⦃ (r' : turboshake.TurboShakeReader 168#usize) (out' : Slice U8) =>
          out'.length = out.length ∧
          out'.val.map (·.bv)
            = (turboSHAKE128 (u8ListToBytes (readerModel r).2) (readerModel r).1.bv
                (readerOffset r + out.length)).toList.drop (readerOffset r) ∧
          readerOffset r' = readerOffset r + out.length ∧
          readerModel r' = readerModel r ⦄

/-- `read` (RATE = 136 ⇒ TurboSHAKE256) fills `out` with the XOF output determined
by the reader's domain separator and absorbed message.  A `read` advances the consumed
offset but leaves the absorbed message and domain separator (`readerModel`) unchanged, so
several reads stream successive windows of the same squeeze (used by `expand_decap_key`). -/
@[step] axiom reader_read136_spec
    (r : turboshake.TurboShakeReader 136#usize) (out : Slice U8) :
    turboshake.TurboShakeReader.Insts.DigestXofReader.read r out
      ⦃ (r' : turboshake.TurboShakeReader 136#usize) (out' : Slice U8) =>
          out'.length = out.length ∧
          out'.val.map (·.bv)
            = (Spec.TurboSHAKE.turboSHAKE256 (u8ListToBytes (readerModel r).2)
                (readerModel r).1.bv (readerOffset r + out.length)).toList.drop (readerOffset r) ∧
          readerOffset r' = readerOffset r + out.length ∧
          readerModel r' = readerModel r ⦄

/-! ### Smoke test: `step` flows through the opaque absorb → finalize → read chain,
mirroring the hash block of `gen_matrix_from_seed_loop0_loop0`. -/

set_option maxHeartbeats 1000000

example (seed : Array U8 32#usize) (i j : U8) (buf : Array U8 416#usize) :
    (do
      let hasher ← turboshake.TurboShake.Insts.CoreDefaultDefault.default 168#usize 2#u8
      let s ← lift (Array.to_slice seed)
      let hasher1 ← turboshake.TurboShake.Insts.DigestUpdate.update hasher s
      let s1 ← lift (Array.to_slice (Array.make 1#usize [i]))
      let hasher2 ← turboshake.TurboShake.Insts.DigestUpdate.update hasher1 s1
      let s2 ← lift (Array.to_slice (Array.make 1#usize [j]))
      let hasher3 ← turboshake.TurboShake.Insts.DigestUpdate.update hasher2 s2
      let reader ←
        turboshake.TurboShake.Insts.DigestExtendableOutputTurboShakeReader.finalize_xof hasher3
      let (s3, back) ← lift (Array.to_slice_mut buf)
      let (_rd, s4) ← turboshake.TurboShakeReader.Insts.DigestXofReader.read reader s3
      ok (back s4))
      ⦃ (buf1 : Array U8 416#usize) =>
          buf1.val.map (·.bv)
            = (turboSHAKE128 (u8ListToBytes (seed.val ++ [i] ++ [j])) (2#u8).bv 416).toList ⦄ := by
  step*
  have habs : hasherAbsorbed hasher3 = seed.val ++ [i] ++ [j] := by
    rw [hasher3_post, hasher2_post, hasher1_post, hasher_post, s_post, s1_post, s2_post]; rfl
  have hs3 : s3.length = 416 := by rw [Slice.length, s3_post1]; exact buf.property
  have hs4 : s4.val.length = 416 := by rw [← Slice.length, _rd_post1, hs3]
  rw [reader_post1, reader_post2] at _rd_post2
  dsimp only at _rd_post2
  simp only [List.drop_zero] at _rd_post2
  rw [habs, hs3] at _rd_post2
  rw [s3_post2, Array.from_slice_val buf s4 hs4]
  exact _rd_post2

/-! ## (C) The nested matrix-assembly loop -/

set_option maxRecDepth 4000

/-- Generic invariant-threading for an `Id.run` `forIn'` loop (any state type). -/
theorem forIn'_inv {α : Type} {β : Type} :
    ∀ (xs : List α) (init : β)
    (body : (a : α) → a ∈ xs → β → Id (ForInStep β))
    (P : Nat → β → Prop)
    (_hInit : P 0 init)
    (_hStep : ∀ (k : Nat) (hk : k < xs.length) b, P k b →
      ∀ a (ha : a ∈ xs), a = xs[k]'hk →
      ∃ b', body a ha b = pure (ForInStep.yield b') ∧ P (k + 1) b'),
    P xs.length (Id.run (forIn' xs init body)) := by
  intro xs; induction xs with
  | nil => intro init body P hInit _; exact hInit
  | cons x xs ih =>
    intro init body P hInit hStep
    obtain ⟨b', hb'_eq, hb'_P⟩ := hStep 0 (Nat.zero_lt_succ _) init hInit x (.head _) rfl
    have hrun : Id.run (forIn' (x :: xs) init body)
        = Id.run (forIn' xs b' (fun a' mm b => body a' (.tail _ mm) b)) := by
      simp only [List.forIn'_cons, Id.run, Bind.bind, hb'_eq]; rfl
    rw [show (x :: xs).length = xs.length + 1 from rfl, hrun]
    exact ih b' (fun a' mm b => body a' (.tail _ mm) b) (fun k => P (k + 1)) hb'_P
      (fun k hk b hPk a ha heq => by
        have hk' : k + 1 < (x :: xs).length := by simp; omega
        exact hStep (k + 1) hk' b hPk a (.tail _ ha) (by simp [heq]))

/-- `forIn'_inv` with an explicit iteration count. -/
theorem forIn'_inv' {α : Type} {β : Type} (xs : List α) (init : β)
    (body : (a : α) → a ∈ xs → β → Id (ForInStep β)) (P : Nat → β → Prop) (n : Nat)
    (hn : xs.length = n) (hInit : P 0 init)
    (hStep : ∀ (k : Nat) (hk : k < xs.length) b, P k b →
      ∀ a (ha : a ∈ xs), a = xs[k]'hk →
      ∃ b', body a ha b = pure (ForInStep.yield b') ∧ P (k + 1) b') :
    P n (Id.run (forIn' xs init body)) :=
  hn ▸ forIn'_inv xs init body P hInit hStep

/-- Matrix bridge: interpret the Rust `Matrix L L` as a spec `PolyMatrix (2¹³) L`. -/
def toMatrix13 {L : Usize} (mat : arithmetic.matrix_arith.Matrix L L) :
    Spec.Kopis.PolyMatrix (2 ^ 13) (L : ℕ) :=
  Matrix.of fun (a b : Fin (L : ℕ)) => toRingElem13 ((mat.val[a.val]!).val[b.val]!)

/-- Entry formula for `PolyMatrix.update`. -/
theorem polyMatrix_update_entry {m ℓ : ℕ} (M : Spec.Kopis.PolyMatrix m ℓ) (i j : ℕ)
    (val : Spec.Kopis.Polynomial m) (hi : i < ℓ) (hj : j < ℓ) (i₀ j₀ : Fin ℓ) :
    (M.update i j val hi hj) i₀ j₀ = if i₀.val = i ∧ j₀.val = j then val else M i₀ j₀ := by
  unfold Spec.Kopis.PolyMatrix.update
  rw [Matrix.updateRow_apply]
  by_cases h1 : i₀ = ⟨i, hi⟩
  · subst h1; simp
  · have hne : (i₀ : Fin ℓ).val ≠ i := fun h => h1 (Fin.ext h)
    simp [h1, hne]

theorem turboSHAKE128_cast {n m : ℕ} (h : n = m) (v : 𝔹 n) (D : Byte) (outLen : ℕ) :
    turboSHAKE128 (v.cast h) D outLen = turboSHAKE128 v D outLen := by
  subst h; rw [Vector.cast_rfl]

/-- Byte-concat bridge: the Rust-absorbed message `seed ++ [i] ++ [j]` interprets as
the spec's concatenation `arrayToBytes seed ‖ #v[i] ‖ #v[j]`. -/
theorem turboSHAKE_u8concat (seed : Array U8 32#usize) (ci cj : U8) (outLen : ℕ) (D : Byte) :
    turboSHAKE128 (u8ListToBytes (seed.val ++ [ci] ++ [cj])) D outLen
      = turboSHAKE128 (arrayToBytes seed ‖ #v[ci.bv] ‖ #v[cj.bv]) D outLen := by
  have h32 : seed.val.length = 32 := seed.property
  have hlen : (seed.val ++ [ci] ++ [cj]).length = 34 := by
    simp only [List.length_append, List.length_cons, List.length_nil]; omega
  -- Trivial byte-reindexing: both sides list the same 34 bytes.
  have htl : (u8ListToBytes (seed.val ++ [ci] ++ [cj])).toList
      = (arrayToBytes seed ‖ #v[ci.bv] ‖ #v[cj.bv]).toList := by
    have e2 : (arrayToBytes seed).toList = seed.val.map (·.bv) := by
      apply List.ext_getElem
      · simp [arrayToBytes, h32]
      · intro k h1 h2
        simp [arrayToBytes, List.getElem_map]
    have e1 : (u8ListToBytes (seed.val ++ [ci] ++ [cj])).toList
        = (seed.val ++ [ci] ++ [cj]).map (·.bv) := by
      simp only [u8ListToBytes, Vector.toList_ofFn]; rw [List.ofFn_getElem_eq_map]
    rw [e1]
    show (seed.val ++ [ci] ++ [cj]).map (·.bv)
      = (arrayToBytes seed ++ #v[ci.bv] ++ #v[cj.bv]).toList
    simp [Vector.toList_push, e2, List.map_append]
  have hmsg : u8ListToBytes (seed.val ++ [ci] ++ [cj])
      = (arrayToBytes seed ‖ #v[ci.bv] ‖ #v[cj.bv]).cast hlen.symm := by
    apply Vector.toList_inj.mp
    rw [Vector.toList_cast]; exact htl
  rw [hmsg]
  exact turboSHAKE128_cast hlen.symm _ D outLen

/-- Spec-side: evaluate `GenMat`'s nested `Id.run` loop at entry `(i₀, j₀)`. -/
theorem GenMat_get (ℓ : ℕ) (seed : 𝔹 32) (i₀ j₀ : Fin ℓ) :
    Spec.Kopis.GenMat ℓ seed i₀ j₀
      = Spec.Kopis.deserialize 13
          (turboSHAKE128 (seed ‖ #v[(i₀.val : Byte)] ‖ #v[(j₀.val : Byte)])
            Spec.Kopis.DOMSEP_GENMAT (32 * 13)) := by
  unfold Spec.Kopis.GenMat
  simp only [Aeneas.SRRange.forIn'_eq_forIn'_range', Aeneas.SRRange.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, bind_pure]
  rw [show Spec.Kopis.deserialize 13 (turboSHAKE128 (seed ‖ #v[(i₀.val : Byte)] ‖ #v[(j₀.val : Byte)])
        Spec.Kopis.DOMSEP_GENMAT (32 * 13))
      = (if i₀.val < ℓ then Spec.Kopis.deserialize 13
          (turboSHAKE128 (seed ‖ #v[(i₀.val : Byte)] ‖ #v[(j₀.val : Byte)])
            Spec.Kopis.DOMSEP_GENMAT (32 * 13))
        else Spec.Kopis.Polynomial.zero (2 ^ 13)) from (if_pos i₀.isLt).symm]
  refine forIn'_inv' (List.range' 0 ℓ) _ _
    (fun s (A : Spec.Kopis.PolyMatrix (2 ^ 13) ℓ) => A i₀ j₀
      = if i₀.val < s then Spec.Kopis.deserialize 13
          (turboSHAKE128 (seed ‖ #v[(i₀.val : Byte)] ‖ #v[(j₀.val : Byte)])
            Spec.Kopis.DOMSEP_GENMAT (32 * 13))
        else Spec.Kopis.Polynomial.zero (2 ^ 13)) ℓ (by simp) ?hInit ?hStep
  case hInit => simp [Spec.Kopis.PolyMatrix.zero]
  case hStep =>
    intro k hk b hb a ha ha_eq
    have ha_val : a = k := by rw [ha_eq]; simp [List.getElem_range']
    subst ha_val
    refine ⟨_, rfl, ?_⟩
    rw [show (if i₀.val < a + 1 then Spec.Kopis.deserialize 13
            (turboSHAKE128 (seed ‖ #v[(i₀.val : Byte)] ‖ #v[(j₀.val : Byte)])
              Spec.Kopis.DOMSEP_GENMAT (32 * 13)) else Spec.Kopis.Polynomial.zero (2 ^ 13))
          = (if a = i₀.val ∧ j₀.val < ℓ then Spec.Kopis.deserialize 13
              (turboSHAKE128 (seed ‖ #v[(i₀.val : Byte)] ‖ #v[(j₀.val : Byte)])
                Spec.Kopis.DOMSEP_GENMAT (32 * 13)) else b i₀ j₀) from ?_]
    · -- inner loop
      refine forIn'_inv' (List.range' 0 ℓ) b _
        (fun s (A : Spec.Kopis.PolyMatrix (2 ^ 13) ℓ) => A i₀ j₀
          = if a = i₀.val ∧ j₀.val < s then Spec.Kopis.deserialize 13
              (turboSHAKE128 (seed ‖ #v[(i₀.val : Byte)] ‖ #v[(j₀.val : Byte)])
                Spec.Kopis.DOMSEP_GENMAT (32 * 13)) else b i₀ j₀) ℓ (by simp) ?hInitIn ?hStepIn
      case hInitIn => simp
      case hStepIn =>
        intro t ht A hA a_2 ha_2 ha_2_eq
        have ha_2_val : a_2 = t := by rw [ha_2_eq]; simp [List.getElem_range']
        subst ha_2_val
        refine ⟨_, rfl, ?_⟩
        rw [polyMatrix_update_entry, hA]
        by_cases hc : i₀.val = a ∧ j₀.val = a_2
        · obtain ⟨e1, e2⟩ := hc
          rw [if_pos ⟨e1, e2⟩, if_pos (show a = i₀.val ∧ j₀.val < a_2 + 1 from ⟨e1.symm, by omega⟩),
            ← e1, ← e2]
        · rw [if_neg hc]
          by_cases hai : a = i₀.val
          · by_cases hjt : j₀.val < a_2
            · rw [if_pos ⟨hai, hjt⟩, if_pos ⟨hai, by omega⟩]
            · rw [if_neg (fun h => hjt h.2), if_neg (fun h => hc ⟨hai.symm, by omega⟩)]
          · rw [if_neg (fun h => hai h.1), if_neg (fun h => hai h.1)]
    · -- the if-shape equality
      rw [hb]
      simp only [j₀.isLt, and_true]
      generalize Spec.Kopis.deserialize 13 (turboSHAKE128 (seed ‖ #v[(i₀.val : Byte)] ‖ #v[(j₀.val : Byte)])
        Spec.Kopis.DOMSEP_GENMAT (32 * 13)) = E
      split_ifs <;> first | rfl | omega

/-- `sliceToBytes` of an array's slice is `arrayToBytes` of the array. -/
theorem sliceToBytes_to_slice {n : Usize} (a : Array U8 n) (h : (Array.to_slice a).length = (n : ℕ)) :
    sliceToBytes (Array.to_slice a) (n : ℕ) h = arrayToBytes a := rfl

/-- Casting a `Usize` to `U8` gives the spec byte `(x.val : Byte)`. -/
theorem cast_u8_bv (x : Usize) : (UScalar.cast .U8 x).bv = ((x.val : ℕ) : Byte) := by
  apply BitVec.eq_of_toNat_eq
  simp only [UScalar.cast, BitVec.toNat_setWidth]
  rfl

/-- `DOMSEP_GENMAT` as a byte is `(2#u8).bv`. -/
theorem domsep_genmat_bv : (2#u8).bv = Spec.Kopis.DOMSEP_GENMAT := by decide

/-- **Hash-block spec (A).**  The `default → update×3 → finalize → read` chain fills
`buf` with `turboSHAKE128 (seed ‖ i ‖ j) DOMSEP_GENMAT 416`. -/
theorem hash_block_spec (seed : Array U8 32#usize) (i j : Usize) (buf : Array U8 416#usize) :
    (do
      let hasher ← turboshake.TurboShake.Insts.CoreDefaultDefault.default 168#usize 2#u8
      let s ← lift (Array.to_slice seed)
      let hasher1 ← turboshake.TurboShake.Insts.DigestUpdate.update hasher s
      let i1 ← lift (UScalar.cast .U8 i)
      let s1 ← lift (Array.to_slice (Array.make 1#usize [i1]))
      let hasher2 ← turboshake.TurboShake.Insts.DigestUpdate.update hasher1 s1
      let i2 ← lift (UScalar.cast .U8 j)
      let s2 ← lift (Array.to_slice (Array.make 1#usize [i2]))
      let hasher3 ← turboshake.TurboShake.Insts.DigestUpdate.update hasher2 s2
      let reader ←
        turboshake.TurboShake.Insts.DigestExtendableOutputTurboShakeReader.finalize_xof hasher3
      let (s3, to_slice_mut_back) ← lift (Array.to_slice_mut buf)
      let (_rd, s4) ← turboshake.TurboShakeReader.Insts.DigestXofReader.read reader s3
      ok (to_slice_mut_back s4))
      ⦃ (buf1 : Array U8 416#usize) =>
          arrayToBytes buf1 = turboSHAKE128
            (arrayToBytes seed ‖ #v[((i.val : ℕ) : Byte)] ‖ #v[((j.val : ℕ) : Byte)])
            Spec.Kopis.DOMSEP_GENMAT (32 * 13) ⦄ := by
  step*
  have habs : hasherAbsorbed hasher3 = seed.val ++ [UScalar.cast .U8 i] ++ [UScalar.cast .U8 j] := by
    rw [hasher3_post, hasher2_post, hasher1_post, hasher_post, s_post, s1_post, s2_post,
      i1_post, i2_post]; rfl
  have hs3 : s3.length = 416 := by rw [Slice.length, s3_post1]; exact buf.property
  have hs4 : s4.val.length = 416 := by rw [← Slice.length, _rd_post1, hs3]
  rw [reader_post1, reader_post2] at _rd_post2
  dsimp only at _rd_post2
  simp only [List.drop_zero] at _rd_post2
  rw [habs, hs3] at _rd_post2
  rw [s3_post2]
  have harr : arrayToBytes (buf.from_slice s4)
      = turboSHAKE128 (u8ListToBytes (seed.val ++ [UScalar.cast .U8 i] ++ [UScalar.cast .U8 j]))
          (2#u8).bv 416 := by
    apply Vector.toList_inj.mp
    rw [arrayToBytes_toList, Array.from_slice_val buf s4 hs4]
    exact _rd_post2
  rw [harr, turboSHAKE_u8concat]
  simp only [cast_u8_bv, domsep_genmat_bv]

/-- The deserialized hash entry for row `a`, column `b`. -/
private def HDEntry (seed : Array U8 32#usize) (a b : ℕ) : Spec.Kopis.Polynomial (2 ^ 13) :=
  Spec.Kopis.deserialize 13 (turboSHAKE128
    (arrayToBytes seed ‖ #v[((a : ℕ) : Byte)] ‖ #v[((b : ℕ) : Byte)])
    Spec.Kopis.DOMSEP_GENMAT (32 * 13))

/-- `getElem!` after a `List.set` at an in-bounds index: reduces to a conditional. -/
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

/-- **Inner loop spec.**  Fills row `i`, columns `[iter.start, L)`, of the matrix. -/
theorem gen_matrix_loop0_loop0_spec {L : Usize} (iter : core.ops.range.Range Usize)
    (seed : Array U8 32#usize) (mat : arithmetic.matrix_arith.Matrix L L)
    (buf : Array U8 416#usize) (i : Usize)
    (hi : i.val < L.val) (hstart : iter.start.val ≤ L.val) (hend : iter.«end».val = L.val) :
    sample.gen_matrix_from_seed_loop0_loop0 iter seed mat buf i
      ⦃ (result : arithmetic.matrix_arith.Matrix L L × Array U8 416#usize) =>
          ∀ (a b : ℕ) (_ : a < L.val) (_ : b < L.val),
            toRingElem13 ((result.1.val[a]!).val[b]!)
              = if a = i.val ∧ iter.start.val ≤ b then HDEntry seed i.val b
                else toRingElem13 ((mat.val[a]!).val[b]!) ⦄ := by
  unfold sample.gen_matrix_from_seed_loop0_loop0
  by_cases hlt : iter.start.val < iter.«end».val
  · let* ⟨ o, iter1, ho, hstart', hend' ⟩ ← core.iter.range.IteratorRange.next_Usize_some_spec
    rw [ho]; simp only
    have hj_lt : iter.start.val < L.val := by scalar_tac
    simp only [consts.MODULUS_Q_BITS]
    step*
    have habs : hasherAbsorbed hasher3
        = seed.val ++ [UScalar.cast .U8 i] ++ [UScalar.cast .U8 iter.start] := by
      rw [hasher3_post, hasher2_post, hasher1_post, hasher_post, s_post, s1_post, s2_post,
        i1_post, i2_post]; rfl
    have hs3 : s3.length = 416 := by rw [Slice.length, s3_post1]; exact buf.property
    have hs4 : s4.val.length = 416 := by rw [← Slice.length, __post1, hs3]
    rw [reader_post1, reader_post2] at __post2
    dsimp only at __post2
    simp only [List.drop_zero] at __post2
    rw [habs, hs3] at __post2
    simp only [s5_post, s3_post2]
    have hs5len : ((buf.from_slice s4).to_slice).length = 32 * 13 := by
      simp only [Slice.length, Array.to_slice, Array.from_slice_val buf s4 hs4]; omega
    let* ⟨ re, hre ⟩ ← from_bytes_spec
    have hre' : toRingElem13 re = HDEntry seed i.val iter.start.val := by
      rw [hre, show sliceToBytes ((buf.from_slice s4).to_slice) (32 * 13) hs5len
            = arrayToBytes (buf.from_slice s4) from rfl]
      have harr : arrayToBytes (buf.from_slice s4)
          = turboSHAKE128 (u8ListToBytes (seed.val ++ [UScalar.cast .U8 i] ++ [UScalar.cast .U8 iter.start]))
              (2#u8).bv 416 := by
        apply Vector.toList_inj.mp
        rw [arrayToBytes_toList, Array.from_slice_val buf s4 hs4]; exact __post2
      rw [harr, turboSHAKE_u8concat]; simp only [cast_u8_bv, domsep_genmat_bv]; rfl
    let* ⟨ row, index_mut_back, hrow, hback ⟩ ← Array.index_mut_usize_spec
    let* ⟨ a1, ha1 ⟩ ← Array.update_spec
    have h_start_new : iter1.start.val ≤ L.val := by rw [hstart']; scalar_tac
    have h_end_new : iter1.«end».val = L.val := by rw [hend']; exact hend
    apply WP.spec_mono
      (gen_matrix_loop0_loop0_spec iter1 seed (index_mut_back a1) (buf.from_slice s4) i hi
        h_start_new h_end_new)
    rintro r hr a b ha hb
    rw [hr a b ha hb, hstart', hback, ha1, hrow]
    have hml : i.val < mat.val.length := by have := mat.property; omega
    rw [Std.Array.set_val_eq]
    by_cases hai : a = i.val
    · subst hai
      have hrl2 : iter.start.val < ((mat.val[i.val]'hml).val).length := by
        rw [(mat.val[i.val]'hml).property]; exact hj_lt
      rw [getElem!_list_set _ _ _ _ hml, if_pos rfl, Std.Array.set_val_eq,
        getElem!_list_set _ _ _ _ hrl2]
      by_cases hb1 : iter.start.val < b
      · rw [if_pos ⟨rfl, by omega⟩, if_pos ⟨rfl, by omega⟩]
      · by_cases hbs : b = iter.start.val
        · subst hbs
          rw [if_neg (by omega), if_pos rfl, if_pos ⟨rfl, le_refl _⟩, hre']
        · rw [if_neg hbs, if_neg (by omega), if_neg (by omega), getElem!_pos _ i.val hml]
    · rw [if_neg (fun h => hai h.1), if_neg (fun h => hai h.1),
        getElem!_list_set _ _ _ _ hml, if_neg hai]
  · let* ⟨ o, iter1, hnone, _ ⟩ ← core.iter.range.IteratorRange.next_Usize_none_spec
    rw [hnone]; simp only [WP.spec_ok]
    intro a b ha hb
    rw [if_neg (by scalar_tac)]

/-- **Outer loop spec.**  Fills rows `[iter.start, L)` (all columns) of the matrix. -/
theorem gen_matrix_loop0_spec {L : Usize} (iter : core.ops.range.Range Usize)
    (seed : Array U8 32#usize) (mat : arithmetic.matrix_arith.Matrix L L)
    (buf : Array U8 416#usize)
    (hstart : iter.start.val ≤ L.val) (hend : iter.«end».val = L.val) :
    sample.gen_matrix_from_seed_loop0 iter seed mat buf
      ⦃ (result : arithmetic.matrix_arith.Matrix L L) =>
          ∀ (a b : ℕ) (_ : a < L.val) (_ : b < L.val),
            toRingElem13 ((result.val[a]!).val[b]!)
              = if iter.start.val ≤ a then HDEntry seed a b
                else toRingElem13 ((mat.val[a]!).val[b]!) ⦄ := by
  unfold sample.gen_matrix_from_seed_loop0
  by_cases hlt : iter.start.val < iter.«end».val
  · let* ⟨ o, iter1, ho, hstart', hend' ⟩ ← core.iter.range.IteratorRange.next_Usize_some_spec
    rw [ho]; simp only
    have hj_lt : iter.start.val < L.val := by scalar_tac
    let* ⟨ mat1, buf1, hpr ⟩ ← gen_matrix_loop0_loop0_spec { start := 0#usize, «end» := L } seed mat buf
      iter.start hj_lt (by simp) rfl
    have h_start_new : iter1.start.val ≤ L.val := by rw [hstart']; scalar_tac
    have h_end_new : iter1.«end».val = L.val := by rw [hend']; exact hend
    apply WP.spec_mono (gen_matrix_loop0_spec iter1 seed mat1 buf1 h_start_new h_end_new)
    rintro r hr a b ha hb
    rw [hr a b ha hb, hstart']
    have hib := hpr a b ha hb
    simp only [Nat.zero_le, and_true] at hib
    by_cases hca : iter.start.val + 1 ≤ a
    · rw [if_pos (by omega), if_pos (by omega)]
    · rw [if_neg (by omega), hib]
      by_cases hca2 : a = iter.start.val
      · subst hca2
        rw [if_pos rfl, if_pos (le_refl _)]
      · rw [if_neg hca2, if_neg (by omega)]
  · let* ⟨ o, iter1, hnone, _ ⟩ ← core.iter.range.IteratorRange.next_Usize_none_spec
    rw [hnone]; simp only [WP.spec_ok]
    intro a b ha hb
    rw [if_neg (by scalar_tac)]

/-- **`gen_matrix_from_seed` correctness.**  The Rust matrix generator produces exactly the
spec's `GenMat` matrix (interpreted mod `2¹³`). -/
theorem gen_matrix_from_seed_spec (L : Usize) (seed : Array U8 32#usize) :
    sample.gen_matrix_from_seed L seed
      ⦃ (r : arithmetic.matrix_arith.Matrix L L) =>
          toMatrix13 r = Spec.Kopis.GenMat (L : ℕ) (arrayToBytes seed) ⦄ := by
  unfold sample.gen_matrix_from_seed
  simp only [arithmetic.matrix_arith.Matrix.Insts.CoreDefaultDefault.default,
    arithmetic.ring_arith.RingElem.Insts.CoreDefaultDefault.default, bind_tc_ok]
  apply WP.spec_mono
    (gen_matrix_loop0_spec { start := 0#usize, «end» := L } seed _ _ (by simp) rfl)
  intro r hr
  apply Matrix.ext
  intro a b
  have key := hr a.val b.val a.isLt b.isLt
  rw [show (({ start := 0#usize, «end» := L } : core.ops.range.Range Usize).start : ℕ) = 0 from rfl,
    if_pos (Nat.zero_le _)] at key
  rw [toMatrix13, Matrix.of_apply, key, GenMat_get]
  rfl

end Kopis.Properties
