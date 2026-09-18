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
open arithmetic.plain_arith (RingElem)

set_option maxHeartbeats 1000000

/-! ## The dispatch, once, for any postcondition

`RingElem::deserialize` has the same shape at every width, so the case analysis is done once
here and the three call sites (widths 13, 10, and the generic path) differ only in what they
supply for the two branches. -/

/-- The portable else-branch of `RingElem::deserialize`, exactly as the extraction writes it.
(`BITS_PER_ELEM` is a const generic now, so the width dispatch is a `match` on its value rather
than the chain of `if`s it used to be.) -/
def portableDeserialize (bytes : Slice U8) (bits : Usize) : Result RingElem :=
  match bits.val with
  | 13 =>
    (do let r ← core.array.TryFromSharedArraySlice.try_from 416#usize bytes
        let arr ← core.result.Result.unwrap core.fmt.DebugTryFromSliceError r
        let a ← ser.deserialize_13 arr
        ok a)
  | 10 =>
    (do let r ← core.array.TryFromSharedArraySlice.try_from 320#usize bytes
        let arr ← core.result.Result.unwrap core.fmt.DebugTryFromSliceError r
        let a ← ser.deserialize_10 arr
        ok a)
  | _ =>
    (do let a ← ser.deserialize_generic 256#usize bits bytes
        ok a)

/-- **The dispatch.**  The CPU probe needs no treatment — on AArch64 it is `ok true` — so the
portable branch is unreachable and only the vector path is left to prove.  `hport` is kept so
that this reads the same as its AVX2 sibling. -/
theorem ringElem_deserialize_dispatch (bytes : Slice U8) (bits : Usize)
    (hbits1 : 1 ≤ bits.val) (hbits : bits.val ≤ 13) (hlen : bytes.length = 32 * bits.val)
    {P : RingElem → Prop}
    (_hport : portableDeserialize bytes bits ⦃ P ⦄)
    (hneon : backend.neon.ser.deserialize bits bytes ⦃ P ⦄) :
    arithmetic.plain_arith.RingElem.deserialize bits bytes ⦃ P ⦄ := by
  unfold arithmetic.plain_arith.RingElem.deserialize
  simp only [consts.RING_DEG]
  -- The two `debug_assert!` width comparisons now front the body as `massert`s; both are
  -- discharged from `1 ≤ bits ≤ 13`, so neither costs an assumption.
  rw [show massert (bits >= 1#usize) = ok () from by
        simp only [massert, if_pos (show bits >= 1#usize by scalar_tac)], bind_tc_ok]
  rw [show massert (bits <= 13#usize) = ok () from by
        simp only [massert, if_pos (show bits <= 13#usize by scalar_tac)], bind_tc_ok]
  -- `BITS_PER_ELEM * RING_DEG` is an overflow check whose value the body discards, then the same
  -- product recomputed as a wrapping multiply; `mul_spec` succeeding is what rules out the wrap.
  let* ⟨ chk, hchk ⟩ ← Std.Usize.mul_spec
  have h256 : (256#usize).val = 256 := by simp
  have hlt : bits.val * (256#usize).val < UScalar.size UScalarTy.Usize := by
    rw [h256, UScalar.size_def]
    have := UScalar.hBounds chk
    omega
  have hiv : (Std.Usize.wrapping_mul bits 256#usize).val = bits.val * 256 := by
    rw [Std.Usize.wrapping_mul_val_eq, Nat.mod_eq_of_lt hlt, h256]
  rw [show lift (Std.Usize.wrapping_mul bits 256#usize)
        = ok (Std.Usize.wrapping_mul bits 256#usize) from rfl, bind_tc_ok]
  let* ⟨ rv, hrv ⟩ ← Std.Usize.div_spec
  have hmeq : Slice.len bytes = rv :=
    UScalar.eq_of_val_eq (by rw [Slice.len_val, hrv, hiv]; omega)
  rw [show massert (Slice.len bytes = rv) = ok () from by
    simp only [massert, if_pos hmeq], bind_tc_ok]
  simp only [backend.neon.cpu.available, bind_tc_ok, reduceIte]
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
    arithmetic.plain_arith.RingElem.deserialize 13#usize bytes
      ⦃ (r : RingElem) => ∀ j < 256,
          (r.val[j]!).val = streamNat bytes (13 * j) 13 ⦄ := by
  refine ringElem_deserialize_dispatch bytes 13#usize (by simp) (by simp) (by simpa using hlen)
    ?_ ?_
  · rw [show portableDeserialize bytes 13#usize =
          (do let r ← core.array.TryFromSharedArraySlice.try_from 416#usize bytes
              let arr ← core.result.Result.unwrap core.fmt.DebugTryFromSliceError r
              let a ← ser.deserialize_13 arr
              ok a) from rfl]
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
    arithmetic.plain_arith.RingElem.deserialize 10#usize bytes
      ⦃ (r : RingElem) => ∀ j < 256,
          (r.val[j]!).val = streamNat bytes (10 * j) 10 ⦄ := by
  refine ringElem_deserialize_dispatch bytes 10#usize (by simp) (by simp) (by simpa using hlen)
    ?_ ?_
  · rw [show portableDeserialize bytes 10#usize =
          (do let r ← core.array.TryFromSharedArraySlice.try_from 320#usize bytes
              let arr ← core.result.Result.unwrap core.fmt.DebugTryFromSliceError r
              let a ← ser.deserialize_10 arr
              ok a) from rfl]
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
    (hgen : ser.deserialize_generic 256#usize n#usize bytes
        ⦃ (r : Array U16 256#usize) => ∀ j < 256,
            (r.val[j]!).val = streamNat bytes (n * j) n ⦄) :
    arithmetic.plain_arith.RingElem.deserialize n#usize bytes
      ⦃ (r : RingElem) => ∀ j < 256,
          (r.val[j]!).val = streamNat bytes (n * j) n ⦄ := by
  have hnv : (n#usize).val = n := by simp
  refine ringElem_deserialize_dispatch bytes n#usize (by omega) (by omega)
    (by rw [hnv]; exact hlen) ?_ ?_
  · -- `1 ≤ n ≤ 12` and `n ≠ 10`, so the width `match` lands in its default branch
    rw [show portableDeserialize bytes n#usize =
          (do let a ← ser.deserialize_generic 256#usize n#usize bytes; ok a) from by
        unfold portableDeserialize
        rw [hnv]
        have hn : n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8 ∨ n = 9
            ∨ n = 11 ∨ n = 12 := by omega
        rcases hn with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rfl]
    apply WP.spec_bind hgen
    intro r hr
    simp only [WP.spec_ok]
    exact hr
  · apply WP.spec_mono (deserialize_streamNat bytes n (by omega) (by omega) hlen n#usize hnv)
    intro r hr
    exact hr

end Kopis.Neon
