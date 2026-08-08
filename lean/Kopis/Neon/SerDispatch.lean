/-
  # Kopis/Neon/SerDispatch.lean — the `RingElem::deserialize` dispatch point.

  This is the first of the eight runtime-dispatch points of `NEON_VERIFICATION_PLAN.md` §3.  The
  NEON extraction guards the vector path with

      if (1..=13).contains(&bits) && neon_available() { … } else { …portable… }

  and **only the first guard is opaque.**  On AArch64 NEON is baseline, so `cpu::available()` is
  `cfg!(target_arch = "aarch64")` — a compile-time `true` — and the extraction reads

      def backend.neon.cpu.available : Result Bool := do ok true

  so the inner branch reduces rather than needing a proof.  `contains` is still uninterpreted,
  because charon does not lower it, and nothing is assumed about what it returns: *both* of the
  reachable paths are shown to compute the same bit stream.

  That is the whole of §1(a)'s promised simplification here.  Where `Kopis/Avx2/SerDispatch.lean`
  has three reachable paths and consumes `available_ok`, this file has two and consumes no
  assumption about the CPU at all.

  ## Why this lives in its own module

  The obvious home for this argument is the generated twin of `Kopis/Properties/Serialize.lean`,
  next to `from_bytes_spec`.  It cannot go there: unfolding `RingElem::deserialize` (whose body
  nests two copies of the portable path) and case-splitting it makes that file's build time
  explode — the AVX2 sibling measured 106 s to over thirty minutes.  Here the width-13 spec is a
  *hypothesis*, so the expensive work happens in a module that builds in seconds and the twin
  needs only to supply `deserialize_13_spec` and apply this.
-/
import Kopis.Neon.Ser

open Aeneas Aeneas.Std Result
open RustKopisNeon

namespace Kopis.Neon

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

/-- **The dispatch.**  The width guard is opaque and its value is not assumed: if the portable
path and the vector path both satisfy `P`, so does `RingElem::deserialize`.  The CPU probe needs
no such treatment — it is `ok true`. -/
theorem ringElem_deserialize_dispatch (bytes : Slice U8) (bits : Usize)
    (hbits : bits.val ≤ 13) (hlen : bytes.length = 32 * bits.val) {P : RingElem → Prop}
    (hport : portableDeserialize bytes bits ⦃ P ⦄)
    (hneon : backend.neon.ser.deserialize bytes bits ⦃ P ⦄) :
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
  · simp only [reduceIte, backend.neon.cpu.available, bind_tc_ok]
    apply WP.spec_bind hneon
    intro r hr
    simp only [WP.spec_ok]
    exact hr

/-- **Dispatch point at width 13**, reached from `from_bytes`.  The portable width-13 unpacker's
spec is taken as a hypothesis so that this proof does not have to live in the file that proves
it. -/
theorem ringElem_deserialize_13_streamNat (bytes : Slice U8) (hlen : bytes.length = 32 * 13)
    (h13 : ∀ (arr : Array U8 416#usize), arr.val = bytes.val →
        ser.deserialize_13 arr
          ⦃ (r : Array U16 256#usize) => ∀ j < 256,
              (r.val[j]!).val = streamNat bytes (13 * j) 13 ⦄) :
    arithmetic.ring_arith.RingElem.deserialize bytes 13#usize
      ⦃ (r : RingElem) => ∀ j < 256,
          (r.val[j]!).val = streamNat bytes (13 * j) 13 ⦄ := by
  refine ringElem_deserialize_dispatch bytes 13#usize (by simp) (by simpa using hlen) ?_ ?_
  · unfold portableDeserialize
    rw [if_pos (by simp only [consts.MODULUS_Q_BITS])]
    have hb : bytes.len = 416#usize := by scalar_tac
    simp only [core.array.TryFromSharedArraySlice.try_from, dif_pos hb, bind_tc_ok,
      core.result.Result.unwrap]
    apply WP.spec_bind (h13 _ rfl)
    intro r hr
    simp only [WP.spec_ok]
    exact hr
  · exact deserialize_streamNat bytes 13 (by omega) (by omega) (by simpa using hlen) 13#usize
      (by simp)

/-- **Dispatch point at width 10** (the ciphertext / public-key width). -/
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

end Kopis.Neon
