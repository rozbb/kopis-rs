/-
  # Kopis/Avx2/SerDispatch.lean — the `RingElem::deserialize` dispatch point.

  This is the first of the six runtime-dispatch points of `AVX2_VERIFICATION_PLAN.md` §E3.  The
  AVX2 extraction guards the vector path with

      if (1..=13).contains(&bits) && avx2_available() { … } else { …portable… }

  and *both* guards are opaque — `cpu::available` for the obvious reason, and `contains` because
  charon does not lower it either.  Nothing is assumed about what either returns: all three
  reachable paths are shown to compute the same bit stream, so the result holds whatever the
  CPU says.

  ## Why this lives in its own module

  The obvious home for this argument is the generated twin of `Kopis/Properties/Serialize.lean`,
  next to `from_bytes_spec`.  It cannot go there: unfolding `RingElem::deserialize` (whose AVX2
  body nests three copies of the portable path) and case-splitting it takes that file from 106 s
  to over thirty minutes, which makes the proof impossible to iterate on.  Here the width-13
  spec is a *hypothesis*, so the expensive work happens in a module that builds in seconds and
  the twin needs only to supply `deserialize_13_spec` and apply this.
-/
import Kopis.Avx2.Ser

open Aeneas Aeneas.Std Result
open RustKopisAvx2

namespace Kopis.Avx2

open Kopis.Properties (streamNat)
open arithmetic.ring_arith (RingElem)

set_option maxHeartbeats 1000000


/-! ## The dispatch, once, for any postcondition

`RingElem::deserialize` has the same shape at every width, so the case analysis is done once
here and the three call sites (widths 13, 10, and the generic path) differ only in what they
supply for the two branches. -/

/-- The portable else-branch of `RingElem::deserialize`, exactly as the extraction writes it. -/
def portableDeserialize (bytes : Slice U8) (bits : Usize) : Result RingElem :=
  if bits = consts.MODULUS_Q_BITS then
    (do let r ← core.array.TryFromSharedArraySlice.try_from 416#usize bytes
        let arr ← core.result.Result.unwrap core.fmt.DebugTryFromSliceError r
        let a ← ser.deserialize_13 arr
        ok a)
  else if bits = consts.MODULUS_P_BITS then
    (do let r ← core.array.TryFromSharedArraySlice.try_from 320#usize bytes
        let arr ← core.result.Result.unwrap core.fmt.DebugTryFromSliceError r
        let a ← ser.deserialize_10 arr
        ok a)
  else
    (do let a ← ser.deserialize_generic 256#usize bytes bits
        ok a)

/-- **The dispatch.**  Both guards are opaque and neither's value is assumed: if the portable
path and the vector path both satisfy `P`, so does `RingElem::deserialize`. -/
theorem ringElem_deserialize_dispatch (bytes : Slice U8) (bits : Usize)
    (hbits : bits.val ≤ 13) (hlen : bytes.length = 32 * bits.val) {P : RingElem → Prop}
    (hport : portableDeserialize bytes bits ⦃ P ⦄)
    (havx : backend.avx2.ser.deserialize bytes bits ⦃ P ⦄) :
    arithmetic.ring_arith.RingElem.deserialize bytes bits ⦃ P ⦄ := by
  unfold arithmetic.ring_arith.RingElem.deserialize
  simp only [consts.RING_DEG]
  let* ⟨ i, hi ⟩ ← Std.Usize.mul_spec
  let* ⟨ rv, hrv ⟩ ← Std.Usize.div_spec
  have hmeq : Slice.len bytes = rv :=
    UScalar.eq_of_val_eq (by rw [Slice.len_val, hrv, hi]; omega)
  rw [show massert (Slice.len bytes = rv) = ok () from by
    simp only [massert, if_pos hmeq], bind_tc_ok]
  let* ⟨ ri, hri ⟩ ← core.ops.range.RangeInclusive.new_spec
  obtain ⟨bw, hbw⟩ := rangeInclusive_contains_ok _ _ _ _ _
  rw [hbw, bind_tc_ok]
  cases bw
  · simpa only [Bool.false_eq_true, reduceIte, portableDeserialize] using hport
  · simp only [reduceIte]
    obtain ⟨b1, hb1⟩ := available_ok
    rw [hb1, bind_tc_ok]
    cases b1
    · simpa only [Bool.false_eq_true, reduceIte, portableDeserialize] using hport
    · simp only [reduceIte]
      apply WP.spec_bind havx
      intro r hr
      simp only [WP.spec_ok]
      exact hr


/-- **Dispatch point at width 10.** -/
theorem ringElem_deserialize_10_streamNat (bytes : Slice U8) (hlen : bytes.length = 32 * 10)
    (h10 : ∀ (arr : Array U8 320#usize), arr.val = bytes.val →
        ser.deserialize_10 arr
          ⦃ (r : Array U16 256#usize) => ∀ j < 256,
              (r.val[j]!).val = streamNat bytes (10 * j) 10 ⦄) :
    arithmetic.ring_arith.RingElem.deserialize bytes 10#usize
      ⦃ (r : RingElem) => ∀ j < 256,
          (r.val[j]!).val = streamNat bytes (10 * j) 10 ⦄ := by
  refine ringElem_deserialize_dispatch bytes 10#usize (by simp) (by simpa using hlen) ?_ ?_
  · unfold portableDeserialize
    rw [if_neg (by simp only [consts.MODULUS_Q_BITS]; decide),
      if_pos (by simp only [consts.MODULUS_P_BITS])]
    have hb : bytes.len = 320#usize := by scalar_tac
    simp only [core.array.TryFromSharedArraySlice.try_from, dif_pos hb, bind_tc_ok,
      core.result.Result.unwrap]
    apply WP.spec_bind (h10 _ rfl)
    intro r hr
    simp only [WP.spec_ok]
    exact hr
  · exact deserialize_streamNat bytes 10 (by omega) (by omega) (by simpa using hlen) 10#usize
      (by simp)

/-- **Dispatch point at the generic widths** (`1 ≤ n ≤ 12`, `n ≠ 10`). -/
theorem ringElem_deserialize_gen_streamNat (bytes : Slice U8) (n : ℕ) (hn1 : 1 ≤ n) (hn12 : n ≤ 12)
    (hne10 : n ≠ 10) (hlen : bytes.length = 32 * n)
    (hgen : ser.deserialize_generic 256#usize bytes n#usize
        ⦃ (r : Array U16 256#usize) => ∀ j < 256,
            (r.val[j]!).val = streamNat bytes (n * j) n ⦄) :
    arithmetic.ring_arith.RingElem.deserialize bytes n#usize
      ⦃ (r : RingElem) => ∀ j < 256,
          (r.val[j]!).val = streamNat bytes (n * j) n ⦄ := by
  have hnv : (n#usize).val = n := by simp
  have h13 : n#usize ≠ consts.MODULUS_Q_BITS := by
    simp only [consts.MODULUS_Q_BITS]
    intro h
    have := congrArg UScalar.val h
    simp at this
    omega
  have h10 : n#usize ≠ consts.MODULUS_P_BITS := by
    simp only [consts.MODULUS_P_BITS]
    intro h
    have := congrArg UScalar.val h
    simp at this
    omega
  refine ringElem_deserialize_dispatch bytes n#usize (by omega) (by rw [hnv]; exact hlen) ?_ ?_
  · unfold portableDeserialize
    rw [if_neg h13, if_neg h10]
    apply WP.spec_bind hgen
    intro r hr
    simp only [WP.spec_ok]
    exact hr
  · apply WP.spec_mono (deserialize_streamNat bytes n (by omega) (by omega) hlen n#usize hnv)
    intro r hr
    exact hr

/-- **Dispatch point 1.**  Whichever branch runs, `RingElem::deserialize` at width 13 produces
the 13-bit windows of the byte stream.  The portable width-13 unpacker's spec is taken as a
hypothesis so that this proof does not have to live in the file that proves it. -/
theorem ringElem_deserialize_13_streamNat (bytes : Slice U8) (hlen : bytes.length = 32 * 13)
    (h13 : ∀ (arr : Array U8 416#usize), arr.val = bytes.val →
        ser.deserialize_13 arr
          ⦃ (r : Array U16 256#usize) => ∀ j < 256,
              (r.val[j]!).val = streamNat bytes (13 * j) 13 ⦄) :
    arithmetic.ring_arith.RingElem.deserialize bytes 13#usize
      ⦃ (r : RingElem) => ∀ j < 256,
          (r.val[j]!).val = streamNat bytes (13 * j) 13 ⦄ := by
  have hlen416 : bytes.length = 416 := by omega
  have hportable : ∀ (arr : Array U8 416#usize), arr.val = bytes.val →
      (do let a ← ser.deserialize_13 arr; ok a)
        ⦃ (r : RingElem) => ∀ j < 256,
            (r.val[j]!).val = streamNat bytes (13 * j) 13 ⦄ := by
    intro arr harr
    apply WP.spec_bind (h13 arr harr)
    intro r hr
    simp only [WP.spec_ok]
    exact hr
  unfold arithmetic.ring_arith.RingElem.deserialize
  simp only [consts.RING_DEG, consts.MODULUS_Q_BITS]
  -- the length assertion, by hand: `step*` walks the whole nested dispatch
  let* ⟨ i, hi ⟩ ← Std.Usize.mul_spec
  let* ⟨ rv, hrv ⟩ ← Std.Usize.div_spec
  have hmeq : Slice.len bytes = rv :=
    UScalar.eq_of_val_eq (by rw [Slice.len_val, hrv, hi]; omega)
  rw [show massert (Slice.len bytes = rv) = ok () from by
    simp only [massert, if_pos hmeq], bind_tc_ok]
  let* ⟨ ri, hri ⟩ ← core.ops.range.RangeInclusive.new_spec
  obtain ⟨bw, hbw⟩ := rangeInclusive_contains_ok _ _ _ _ _
  rw [hbw, bind_tc_ok]
  have hb : bytes.len = 416#usize := by scalar_tac
  cases bw
  · -- width guard false: the portable width-13 unpacker
    simp only [Bool.false_eq_true, reduceIte,
      core.array.TryFromSharedArraySlice.try_from, dif_pos hb, bind_tc_ok,
      core.result.Result.unwrap]
    exact hportable _ rfl
  · simp only [reduceIte]
    obtain ⟨b1, hb1⟩ := available_ok
    rw [hb1, bind_tc_ok]
    cases b1
    · -- no AVX2: the same portable unpacker
      simp only [Bool.false_eq_true, reduceIte,
        core.array.TryFromSharedArraySlice.try_from, dif_pos hb, bind_tc_ok,
        core.result.Result.unwrap]
      exact hportable _ rfl
    · -- the vector path: phase C
      simp only [reduceIte]
      apply WP.spec_bind
        (deserialize_streamNat bytes 13 (by omega) (by omega) hlen 13#usize (by simp))
      intro r hr
      simp only [WP.spec_ok]
      exact hr

end Kopis.Avx2
