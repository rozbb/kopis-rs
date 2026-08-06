#!/usr/bin/env python3
"""Generate Kopis/Avx2/Properties/*.lean from Kopis/Properties/*.lean.

Phase E2 of AVX2_VERIFICATION_PLAN.md: the 298 declarations whose bodies are identical
between the two extractions should transfer by renaming the namespace.  The substitutions
are exactly:

    RustKopisSerial     -> RustKopisAvx2      (the extracted constants)
    ExtractedRustSerial -> ExtractedRustAvx2  (the extraction module)
    Kopis.Properties    -> Kopis.Avx2.Properties  (this stack's own namespace and imports)

plus an explicit re-open of the *shared* bit-stream vocabulary, which lives in
`Kopis.Bits.Stream` under `Kopis.Properties` and is deliberately not duplicated.
"""
import importlib.util, pathlib, re, sys

_bridge_spec = importlib.util.spec_from_file_location(
    "gen_avx2_bridge", pathlib.Path(__file__).with_name("gen_avx2_bridge.py"))
gen_avx2_bridge = importlib.util.module_from_spec(_bridge_spec)
_bridge_spec.loader.exec_module(gen_avx2_bridge)

SRC = pathlib.Path("Kopis/Properties")
DST = pathlib.Path("Kopis/Avx2/Properties")

# Names defined in Kopis/Bits/Stream.lean: backend-agnostic, shared by both stacks.
SHARED = ("streamBit streamNat streamNat_zero streamNat_succ streamBit_le_one streamNat_lt "
          "streamNat_split lor_add_of_lt lor_mul_of_lt sum_testBit_eq_mod streamNat_byte "
          "streamByte streamByte_lt sum_base256 testBit_sum_bytes streamNat_of_byteWindow "
          "cbdX cbdX_le testBit_streamNat cbdX_eq_bitSum streamNat_mod streamNat_shiftRight "
          "cbdX_eq_bitSum_of_le cbdU16")


# ---------------------------------------------------------------------------------------
# Phase E3: the runtime-dispatch points.
#
# Six extracted declarations differ between the two backends -- they are the `if available()`
# sites -- so the serial proof of any theorem that unfolds one of them does not transfer.  Those
# theorems are patched here rather than hand-edited in the generated file: a patch that stops
# applying (because the serial proof changed) makes the generator fail loudly, whereas a hand
# edit would be silently overwritten or silently stale.
#
# Each entry is (module, old, new).  `old` must occur exactly once.
# ---------------------------------------------------------------------------------------

PATCHES = [
    # Dispatch point 1 again, reached from `Ntt.lean`'s two magnitude lemmas.  Same argument as
    # `Serialize.lean` below, but the postcondition wanted here is a bound rather than the stream
    # itself, so the stream spec is weakened after the fact.
    ("Ntt.lean",
     """  unfold arithmetic.ring_arith.RingElem.deserialize
  simp only [consts.RING_DEG, consts.MODULUS_Q_BITS]
  have hlen416 : bytes.length = 416 := by omega
  step*
  have hb : bytes.len = 416#usize := by scalar_tac
  simp only [core.array.TryFromSharedArraySlice.try_from, dif_pos hb, bind_tc_ok,
    core.result.Result.unwrap]
  apply WP.spec_bind (deserialize_13_spec bytes ⟨bytes.val, by scalar_tac⟩ rfl hlen416)
  intro r hr
  simp only [WP.spec_ok]
  intro c hc
  have hb2 : c < r.val.length := by have := r.property; grind
  have heq : (r.val[c]!).val = streamNat bytes (13 * c) 13 := by
    rw [getElem!_pos r.val c hb2]; exact hr c hc
  rw [heq]; exact streamNat_lt _ _ _""",
     """  -- AVX2 only: `RingElem::deserialize` dispatches on the width and on `cpu::available`.
  -- Whichever path runs, it produces the 13-bit windows of the byte stream (SerDispatch.lean),
  -- and the bound is a consequence of that.
  have hlen416 : bytes.length = 416 := by omega
  refine WP.spec_mono (Kopis.Avx2.ringElem_deserialize_13_streamNat bytes hlen ?_) ?_
  · intro arr harr
    -- SerDispatch states the window spec with `[j]!`; this file's spec uses `[j]`.
    refine WP.spec_mono (deserialize_13_spec bytes arr harr hlen416) ?_
    intro r hr j hj
    have hb2 : j < r.val.length := by have := r.property; grind
    rw [getElem!_pos r.val j hb2]
    exact hr j hj
  · intro r hr c hc
    rw [hr c hc]
    exact streamNat_lt _ _ _"""),
    ("Ntt.lean",
     """  unfold arithmetic.ring_arith.RingElem.deserialize
  simp only [consts.RING_DEG, consts.MODULUS_Q_BITS, consts.MODULUS_P_BITS]
  have hlen320 : bytes.length = 320 := by omega
  step*
  have hb : bytes.len = 320#usize := by scalar_tac
  simp only [core.array.TryFromSharedArraySlice.try_from, dif_pos hb, bind_tc_ok,
    core.result.Result.unwrap]
  apply WP.spec_bind (deserialize_10_spec bytes ⟨bytes.val, by scalar_tac⟩ rfl hlen320)
  intro r hr
  simp only [WP.spec_ok]
  intro c hc
  have hb2 : c < r.val.length := by have := r.property; grind
  have heq : (r.val[c]!).val = streamNat bytes (10 * c) 10 := by
    rw [getElem!_pos r.val c hb2]; exact hr c hc
  rw [heq]; exact streamNat_lt _ _ _""",
     """  -- AVX2 only: the width-10 dispatch, exactly as above.
  have hlen320 : bytes.length = 320 := by omega
  refine WP.spec_mono (Kopis.Avx2.ringElem_deserialize_10_streamNat bytes hlen ?_) ?_
  · intro arr harr
    -- SerDispatch states the window spec with `[j]!`; this file's spec uses `[j]`.
    refine WP.spec_mono (deserialize_10_spec bytes arr harr hlen320) ?_
    intro r hr j hj
    have hb2 : j < r.val.length := by have := r.property; grind
    rw [getElem!_pos r.val j hb2]
    exact hr j hj
  · intro r hr c hc
    rw [hr c hc]
    exact streamNat_lt _ _ _"""),
    # Dispatch point 1: `RingElem::deserialize` at width 13, reached from `from_bytes`.
    # The argument itself lives in `Kopis/Avx2/SerDispatch.lean`, which takes the width-13
    # spec as a hypothesis; doing it here instead took this file from 106 s to over thirty
    # minutes, because unfolding the AVX2 dispatch body (three nested copies of the portable
    # path) and case-splitting it is expensive in this file's environment.
    ("Serialize.lean",
     """  unfold arithmetic.ring_arith.RingElem.deserialize
  simp only [consts.RING_DEG, consts.MODULUS_Q_BITS]
  have hlen416 : bytes.length = 416 := by omega
  step*
  -- resolve `try_from 416` (lengths match) and `unwrap`, exposing `arr.val = bytes.val`
  have hb : bytes.len = 416#usize := by scalar_tac
  simp only [core.array.TryFromSharedArraySlice.try_from, dif_pos hb, bind_tc_ok,
    core.result.Result.unwrap]
  apply WP.spec_bind (deserialize_13_spec bytes ⟨bytes.val, by scalar_tac⟩ rfl hlen416)
  intro r hr
  simp only [WP.spec_ok]
  apply Vector.ext""",
     """  have hlen416 : bytes.length = 416 := by omega
  -- Both guards of the AVX2 dispatch are opaque, and nothing is assumed about what they
  -- return: all three reachable paths compute the same bit stream.  See SerDispatch.lean.
  have hstream := Kopis.Avx2.ringElem_deserialize_13_streamNat bytes hlen
    (fun arr harr => by
      apply WP.spec_mono (deserialize_13_spec bytes arr harr hlen416)
      intro r hr j hj
      rw [getElem!_pos r.val j (by have := r.property; scalar_tac)]
      exact hr j hj)
  apply WP.spec_mono hstream
  intro r hr
  apply Vector.ext"""),
    # Dispatch point at the generic widths (`RingElem::deserialize`, n <= 12, n != 10, 13).
    # The width-13 disequality is used only by the portable-branch reasoning the patch below
    # replaces, so its binder is renamed rather than left to trip the unused-variable linter.
    ("DeserializeCm.lean",
     """    (hne13 : n ≠ 13) (hne10 : n ≠ 10) (hlen : bytes.length = 32 * n) :""",
     """    (_hne13 : n ≠ 13) (hne10 : n ≠ 10) (hlen : bytes.length = 32 * n) :"""),
    ("DeserializeCm.lean",
     """  unfold arithmetic.ring_arith.RingElem.deserialize
  simp only [consts.RING_DEG]
  -- i = n * 256, right_val = 32·n, discharge the length massert
  let* ⟨ i, hi ⟩ ← Std.Usize.mul_spec
  have hiv : i.val = n * 256 := hi
  let* ⟨ rv, hrv ⟩ ← Std.Usize.div_spec
  have hrvv : rv.val = 32 * n := by rw [hrv, hiv]; omega
  have hmeq : Slice.len bytes = rv := UScalar.eq_of_val_eq (by rw [Slice.len_val, hrvv]; exact hlen)
  rw [show massert (Slice.len bytes = rv) = ok () from by
    simp only [massert, if_pos hmeq], bind_tc_ok]
  -- neither the 13-bit nor the 10-bit fast path: take the generic else-branch
  have hne13' : n#usize ≠ consts.MODULUS_Q_BITS := by
    simp only [consts.MODULUS_Q_BITS]
    intro h; exact hne13 (by have := congrArg UScalar.val h; simpa using this)
  have hne10' : n#usize ≠ consts.MODULUS_P_BITS := by
    simp only [consts.MODULUS_P_BITS]
    intro h; exact hne10 (by have := congrArg UScalar.val h; simpa using this)
  rw [if_neg hne13', if_neg hne10']
  -- delegate to the generic decoder and thread the postcondition through `ok a`
  let* ⟨ a, ha ⟩ ← deserialize_generic_gen_spec bytes n ⟨hn1, hn2⟩ hlen
  exact ha""",
     """  -- The dispatch is proved once in `Kopis/Avx2/SerDispatch.lean`; here it is instantiated at
  -- the generic widths, with the portable branch supplied by the twin's own generic decoder.
  have hstream := Kopis.Avx2.ringElem_deserialize_gen_streamNat bytes n hn1 hn2 hne10 hlen
    (Kopis.Avx2.Generic.generic_streamNat bytes n hn1 (by omega) hlen)
  apply WP.spec_mono hstream
  intro r hr
  apply Vector.ext
  intro jj hjj
  simp only [toPolyN, Vector.getElem_ofFn]
  rw [deserialize_get n (sliceToBytes bytes (32 * n) hlen) jj hjj,
    ← getElem!_pos r.val jj (by have := r.property; scalar_tac), hr jj hjj,
    streamNat_eq_sum' bytes n jj hlen hjj]"""),
    # Dispatch point at width 10 (`RingElem::deserialize`, the ciphertext/public-key width).
    ("DeserializeVec.lean",
     """  unfold arithmetic.ring_arith.RingElem.deserialize
  simp only [consts.RING_DEG, consts.MODULUS_Q_BITS, consts.MODULUS_P_BITS]
  have hlen320 : bytes.length = 320 := by omega
  step*
  have hb : bytes.len = 320#usize := by scalar_tac
  simp only [core.array.TryFromSharedArraySlice.try_from, dif_pos hb, bind_tc_ok,
    core.result.Result.unwrap]
  apply WP.spec_bind (deserialize_10_spec bytes ⟨bytes.val, by scalar_tac⟩ rfl hlen320)
  intro r hr
  simp only [WP.spec_ok]
  apply Vector.ext
  intro jj hjj
  simp only [toPolyN, Vector.getElem_ofFn]
  rw [deserialize_get 10 (sliceToBytes bytes (32 * 10) hlen) jj hjj]
  have hval := hr jj hjj
  rw [hval, streamNat_eq_sum bytes 10 jj hlen hjj]""",
     """  have hlen320 : bytes.length = 320 := by omega
  -- dispatch at width 10, proved in `Kopis/Avx2/SerDispatch.lean`
  have hstream := Kopis.Avx2.ringElem_deserialize_10_streamNat bytes hlen
    (fun arr harr => by
      apply WP.spec_mono (deserialize_10_spec bytes arr harr hlen320)
      intro r hr j hj
      rw [getElem!_pos r.val j (by have := r.property; scalar_tac)]
      exact hr j hj)
  apply WP.spec_mono hstream
  intro r hr
  apply Vector.ext
  intro jj hjj
  simp only [toPolyN, Vector.getElem_ofFn]
  rw [deserialize_get 10 (sliceToBytes bytes (32 * 10) hlen) jj hjj,
    ← getElem!_pos r.val jj (by have := r.property; scalar_tac), hr jj hjj,
    streamNat_eq_sum bytes 10 jj hlen hjj]"""),
    # `hr` now gives the `getElem!` form, so convert before rewriting with it.
    ("Serialize.lean",
     """  rw [deserialize_get 13 (sliceToBytes bytes (32 * 13) hlen) jj hjj]
  have hval := hr jj hjj
  rw [hval, streamNat_eq_sum bytes 13 jj hlen hjj]""",
     """  rw [deserialize_get 13 (sliceToBytes bytes (32 * 13) hlen) jj hjj]
  have hval := hr jj hjj
  rw [← getElem!_pos r.val jj (by have := r.property; scalar_tac), hval,
    streamNat_eq_sum bytes 13 jj hlen hjj]"""),

    # Dispatch point 3: `pointwise_mul_acc`, and dispatch point 4:
    # `reduce_invntt_to_ring_elem`.  Both statements are about `aZ`/`accZ` — the integer *value*
    # of an `i32` lane — which on this backend is two 16-bit residues rather than one mod-`p`
    # residue, so they are false on the vector branch, not merely unproved.  They are therefore
    # restricted to the portable branch; `Kopis/Avx2/Reduce.lean` proves the vector branch, and
    # `NttBridge.lean`'s `ntt_inner_entry_spec` joins the two.
    ("NttMul.lean",
     """/-- **`pointwise_mul_acc` adds the pointwise product into the accumulator, exactly.** -/
theorem pointwise_mul_acc_spec
    (acc : Array I64 256#usize) (lhs rhs : arithmetic.ntt.NttElem) (Bacc : ℤ)""",
     """/-- **`pointwise_mul_acc` adds the pointwise product into the accumulator, exactly.**
AVX2 only: stated on the portable branch.  The vector branch computes a different function of
the same bits — see `Kopis/Avx2/NttMulLane.lean` — so it is proved separately, and
`available_ok` fixes one boolean for every call site. -/
theorem pointwise_mul_acc_spec (hb : backend.avx2.cpu.available = ok false)
    (acc : Array I64 256#usize) (lhs rhs : arithmetic.ntt.NttElem) (Bacc : ℤ)"""),
    ("NttMul.lean",
     """  unfold arithmetic.ntt.pointwise_mul_acc
  apply WP.spec_mono""",
     """  unfold arithmetic.ntt.pointwise_mul_acc
  rw [hb, bind_tc_ok]
  simp only [Bool.false_eq_true, if_false]
  apply WP.spec_mono"""),
    ("NttMul.lean",
     """theorem reduce_invntt_to_ring_elem_spec (acc : Array I64 256#usize) (h : ℕ → Zp) (H : ℕ → ℤ)""",
     """theorem reduce_invntt_to_ring_elem_spec (hb : backend.avx2.cpu.available = ok false)
    (acc : Array I64 256#usize) (h : ℕ → Zp) (H : ℕ → ℤ)"""),
    ("NttMul.lean",
     """  unfold arithmetic.ntt.reduce_invntt_to_ring_elem
  let* ⟨v1, hv1a, hv1b⟩ ← reduce_loop0_spec""",
     """  unfold arithmetic.ntt.reduce_invntt_to_ring_elem
  rw [hb, bind_tc_ok]
  simp only [Bool.false_eq_true, if_false]
  let* ⟨v1, hv1a, hv1b⟩ ← reduce_loop0_spec"""),
    # The two `from_secret_matrix_spec` call sites: the vector `from_secret` needs its input
    # already centred (see `scripts/gen_avx2_bridge.py`), and both callers already carry the
    # `SecretBounded` fact that gives it.
    # Dispatch point 5: `gen_matrix_from_seed`.  Unlike the NTT dispatch points, both branches
    # satisfy the *same* statement here — `Kopis/Avx2/SampleBridge.lean` proves the vector path
    # against `GenMat` on top of `Keccak/Conform.lean`'s `xof4_turboSHAKE` — so the two are
    # joined rather than one being restricted away.  The vector path computes `L * L`, which the
    # portable path does not, so it carries an overflow hypothesis the portable path lacks.
    ("GenMatrix.lean",
     """import Kopis.Avx2.Properties.Serialize""",
     """import Kopis.Avx2.Properties.Serialize
import Kopis.Avx2.SampleBridge"""),
    ("GenMatrix.lean",
     """theorem gen_matrix_from_seed_spec (L : Usize) (seed : Array U8 32#usize) :
    sample.gen_matrix_from_seed L seed
      ⦃ (r : arithmetic.matrix_arith.Matrix L L) =>
          toMatrix13 r = Spec.Kopis.GenMat (L : ℕ) (arrayToBytes seed) ⦄ := by
  unfold sample.gen_matrix_from_seed
  simp only [""",
     """theorem gen_matrix_from_seed_spec (L : Usize) (seed : Array U8 32#usize)
    (hLmax : L.val * L.val + 4 ≤ Usize.max) :
    sample.gen_matrix_from_seed L seed
      ⦃ (r : arithmetic.matrix_arith.Matrix L L) =>
          toMatrix13 r = Spec.Kopis.GenMat (L : ℕ) (arrayToBytes seed) ⦄ := by
  unfold sample.gen_matrix_from_seed
  obtain ⟨b1, hb1⟩ := Kopis.Avx2.available_ok
  rw [hb1, bind_tc_ok]
  have havx : backend.avx2.sample.gen_matrix_from_seed L seed
      ⦃ (r : arithmetic.matrix_arith.Matrix L L) =>
          toMatrix13 r = Spec.Kopis.GenMat (L : ℕ) (arrayToBytes seed) ⦄ := by
    apply WP.spec_mono (Kopis.Avx2.Properties.avx2_gen_matrix_from_seed_spec L seed hLmax)
    intro r hr
    apply Matrix.ext
    intro a b
    rw [toMatrix13, Matrix.of_apply, hr a.val a.isLt b.val b.isLt, GenMat_get,
      Kopis.Avx2.Properties.entryOf]
    rfl
  cases b1
  case true => simpa only [reduceIte] using havx
  all_goals simp only [Bool.false_eq_true, reduceIte]
  simp only ["""),
    # Dispatch point 6: `gen_secret_from_seed`, joined the same way as `gen_matrix_from_seed`.
    # `Kopis/Avx2/SecretBridge.lean` proves the vector path against `GenSecret`.  It carries two
    # hypotheses the portable path does not need: the vector index loop computes `L - 1` before
    # any guard (so `L = 0` underflows where the portable path is simply empty), and the Rust
    # `const`-asserts `L <= 4`.
    ("GenSecretTop.lean",
     """import Kopis.Avx2.Properties.GenSecretSpec""",
     """import Kopis.Avx2.Properties.GenSecretSpec
import Kopis.Avx2.SecretBridge"""),
    ("GenSecretTop.lean",
     """theorem gen_secret_from_seed_spec (L MU : Usize) (seed : Array U8 32#usize)
    (hMU : MU.val = 6 ∨ MU.val = 8 ∨ MU.val = 10) :
    sample.gen_secret_from_seed L MU seed
      ⦃ (r : arithmetic.matrix_arith.Matrix L 1#usize) =>
          toVector13 r = Spec.Kopis.GenSecret L.val MU.val (arrayToBytes seed) ⦄ := by
  unfold sample.gen_secret_from_seed
  simp only [""",
     """theorem gen_secret_from_seed_spec (L MU : Usize) (seed : Array U8 32#usize)
    (hMU : MU.val = 6 ∨ MU.val = 8 ∨ MU.val = 10) (hL : 0 < L.val) (hL4 : L.val ≤ 4) :
    sample.gen_secret_from_seed L MU seed
      ⦃ (r : arithmetic.matrix_arith.Matrix L 1#usize) =>
          toVector13 r = Spec.Kopis.GenSecret L.val MU.val (arrayToBytes seed) ⦄ := by
  unfold sample.gen_secret_from_seed
  obtain ⟨bAvx, hbAvx⟩ := Kopis.Avx2.available_ok
  rw [hbAvx, bind_tc_ok]
  have havx : backend.avx2.sample.gen_secret_from_seed L MU seed
      ⦃ (r : arithmetic.matrix_arith.Matrix L 1#usize) =>
          toVector13 r = Spec.Kopis.GenSecret L.val MU.val (arrayToBytes seed) ⦄ := by
    apply WP.spec_mono
      (Kopis.Avx2.Properties.avx2_gen_secret_from_seed_spec L MU seed hMU hL hL4)
    intro r hr
    apply Vector.ext
    intro a ha
    rw [toVector13, Vector.getElem_ofFn, hr a ha,
      getElem!_pos (Spec.Kopis.GenSecret L.val MU.val (arrayToBytes seed)) a (by simpa using ha)]
  cases bAvx
  case true => simpa only [reduceIte] using havx
  all_goals simp only [Bool.false_eq_true, reduceIte]
  simp only ["""),
    # …and the same theorem's coefficient bound, which has its own dispatch.
    ("GenSecretTop.lean",
     """theorem gen_secret_from_seed_bd (L MU : Usize) (seed : Array U8 32#usize)
    (hMU : MU.val = 6 ∨ MU.val = 8 ∨ MU.val = 10) :
    sample.gen_secret_from_seed L MU seed
      ⦃ (r : arithmetic.matrix_arith.Matrix L 1#usize) =>
          ∀ a (_ha : a < L.val) c (_hc : c < 256),
            smallSignedU16 (((r.val[a]!).val[0]!).val[c]!) (MU.val / 2) ⦄ := by
  unfold sample.gen_secret_from_seed
  simp only [""",
     """theorem gen_secret_from_seed_bd (L MU : Usize) (seed : Array U8 32#usize)
    (hMU : MU.val = 6 ∨ MU.val = 8 ∨ MU.val = 10) (hL : 0 < L.val) (hL4 : L.val ≤ 4) :
    sample.gen_secret_from_seed L MU seed
      ⦃ (r : arithmetic.matrix_arith.Matrix L 1#usize) =>
          ∀ a (_ha : a < L.val) c (_hc : c < 256),
            smallSignedU16 (((r.val[a]!).val[0]!).val[c]!) (MU.val / 2) ⦄ := by
  unfold sample.gen_secret_from_seed
  obtain ⟨bAvx2, hbAvx2⟩ := Kopis.Avx2.available_ok
  rw [hbAvx2, bind_tc_ok]
  have havx : backend.avx2.sample.gen_secret_from_seed L MU seed
      ⦃ (r : arithmetic.matrix_arith.Matrix L 1#usize) =>
          ∀ a (_ha : a < L.val) c (_hc : c < 256),
            smallSignedU16 (((r.val[a]!).val[0]!).val[c]!) (MU.val / 2) ⦄ := by
    apply WP.spec_mono
      (Kopis.Avx2.Properties.avx2_gen_secret_from_seed_bd L MU seed hMU hL hL4)
    intro r hr
    exact hr
  cases bAvx2
  case true => simpa only [reduceIte] using havx
  all_goals simp only [Bool.false_eq_true, reduceIte]
  simp only ["""),
    # Dispatch point 7: the matrix sampler's coefficient bound, which lives in `Ntt.lean` rather
    # than `GenMatrix.lean` because it is what the NTT's exactness argument needs.
    ("Ntt.lean",
     """import Kopis.Avx2.Properties.GenSecretTop""",
     """import Kopis.Avx2.Properties.GenSecretTop
import Kopis.Avx2.SampleBridge"""),
    ("Ntt.lean",
     """theorem gen_matrix_uniformBounded {L : Usize} (seed : Array U8 32#usize) :
    sample.gen_matrix_from_seed L seed
      ⦃ (r : arithmetic.matrix_arith.Matrix L L) => UniformBounded r ⦄ := by
  unfold sample.gen_matrix_from_seed
  simp only [""",
     """theorem gen_matrix_uniformBounded {L : Usize} (seed : Array U8 32#usize)
    (hLmax : L.val * L.val + 4 ≤ Usize.max) :
    sample.gen_matrix_from_seed L seed
      ⦃ (r : arithmetic.matrix_arith.Matrix L L) => UniformBounded r ⦄ := by
  unfold sample.gen_matrix_from_seed
  obtain ⟨bU, hbU⟩ := Kopis.Avx2.available_ok
  rw [hbU, bind_tc_ok]
  have havx : backend.avx2.sample.gen_matrix_from_seed L seed
      ⦃ (r : arithmetic.matrix_arith.Matrix L L) => UniformBounded r ⦄ := by
    apply WP.spec_mono
      (Kopis.Avx2.Properties.avx2_gen_matrix_from_seed_bd L seed hLmax)
    intro r hr i j c hi hj hc
    exact hr i j c hi hj hc
  cases bU
  case true => simpa only [reduceIte] using havx
  all_goals simp only [Bool.false_eq_true, reduceIte]
  simp only ["""),
    # …and its one caller, which has to carry the vector path's two hypotheses onward.
    ("Ntt.lean",
     """theorem gen_secret_secretBounded {L MU : Usize} (seed : Array U8 32#usize)
    (hMU : MU.val = 6 ∨ MU.val = 8 ∨ MU.val = 10) :
    sample.gen_secret_from_seed L MU seed
      ⦃ (r : arithmetic.matrix_arith.Matrix L 1#usize) =>
          SecretBounded r ((MU.val / 2 : ℕ) : ℤ) ⦄ := by
  apply WP.spec_mono (gen_secret_from_seed_bd L MU seed hMU)""",
     """theorem gen_secret_secretBounded {L MU : Usize} (seed : Array U8 32#usize)
    (hMU : MU.val = 6 ∨ MU.val = 8 ∨ MU.val = 10) (hL : 0 < L.val) (hL4 : L.val ≤ 4) :
    sample.gen_secret_from_seed L MU seed
      ⦃ (r : arithmetic.matrix_arith.Matrix L 1#usize) =>
          SecretBounded r ((MU.val / 2 : ℕ) : ℤ) ⦄ := by
  apply WP.spec_mono (gen_secret_from_seed_bd L MU seed hMU hL hL4)"""),
    # `expand_decap_key_spec` calls all four sampler specs.  `L ≤ 4` and `L*L + 4 ≤ Usize.max`
    # follow from hypotheses it already has (`_hbuf` and `_hL`); `0 < L` does not, so it is added.
    ("ExpandDecap.lean",
     """    (_hbuf : L.val * 320 + 32 ≤ 1312) (hfit : L.val * 10 * 256 ≤ Usize.max)
    (_hL : L.val < 256) :
    pke.expand_decap_key L MU sk""",
     """    (_hbuf : L.val * 320 + 32 ≤ 1312) (hfit : L.val * 10 * 256 ≤ Usize.max)
    (_hL : L.val < 256) (hL0 : 0 < L.val) :
    pke.expand_decap_key L MU sk"""),
    ("ExpandDecap.lean",
     """  let* ⟨mat_a, hmata, hmatbnd⟩ ← spec_and (gen_matrix_from_seed_spec L (to_slice_mut_back s3))
    (gen_matrix_uniformBounded (to_slice_mut_back s3))
  let* ⟨vec_s, hvecs, hvecbnd⟩ ← spec_and (gen_secret_from_seed_spec L MU (to_slice_mut_back1 s5) hMU)
    (gen_secret_secretBounded (to_slice_mut_back1 s5) hMU)""",
     """  have hLsq : L.val * L.val + 4 ≤ Usize.max := by
    have : L.val * L.val ≤ 255 * 255 := Nat.mul_le_mul (by omega) (by omega)
    scalar_tac
  have hL4 : L.val ≤ 4 := by omega
  let* ⟨mat_a, hmata, hmatbnd⟩ ←
    spec_and (gen_matrix_from_seed_spec L (to_slice_mut_back s3) hLsq)
    (gen_matrix_uniformBounded (to_slice_mut_back s3) hLsq)
  let* ⟨vec_s, hvecs, hvecbnd⟩ ←
    spec_and (gen_secret_from_seed_spec L MU (to_slice_mut_back1 s5) hMU hL0 hL4)
    (gen_secret_secretBounded (to_slice_mut_back1 s5) hMU hL0 hL4)"""),
    # The two remaining callers of the sampler specs, threading the same hypotheses onward.
    ("KeyGen.lean",
     """    expand_decap_key_spec L MU seed p hℓ hμ hMU hbuf hfit hL""",
     """    expand_decap_key_spec L MU seed p hℓ hμ hMU hbuf hfit hL hL0"""),
    ("PkeEncryptTop.lean",
     """    (hT : 1 ≤ T.val ∧ T.val ≤ 10)
    (hfit : L.val * 10 * 256 ≤ Usize.max)""",
     """    (hT : 1 ≤ T.val ∧ T.val ≤ 10) (hL0 : 0 < L.val) (hL4 : L.val ≤ 4)
    (hfit : L.val * 10 * 256 ≤ Usize.max)"""),
    ("PkeEncryptTop.lean",
     """  let* ⟨vec_sprime, hvecs, hspbnd⟩ ← spec_and (gen_secret_from_seed_spec L MU coins hMU)
    (gen_secret_secretBounded coins hMU)""",
     """  let* ⟨vec_sprime, hvecs, hspbnd⟩ ←
    spec_and (gen_secret_from_seed_spec L MU coins hMU hL0 hL4)
    (gen_secret_secretBounded coins hMU hL0 hL4)"""),
    ("KemEncap.lean",
     """    (hMU : MU.val = 6 ∨ MU.val = 8 ∨ MU.val = 10) (hT : 1 ≤ T.val ∧ T.val ≤ 10)
    (hfit : L.val * 10 * 256 ≤ Usize.max)""",
     """    (hMU : MU.val = 6 ∨ MU.val = 8 ∨ MU.val = 10) (hT : 1 ≤ T.val ∧ T.val ≤ 10)
    (hL0 : 0 < L.val) (hL4 : L.val ≤ 4)
    (hfit : L.val * 10 * 256 ≤ Usize.max)"""),
    ("KemEncap.lean",
     """    (to_slice_mut_back1 s5) out_buf p hℓ hμ ht hMU hT hfit hlenout pk_bytes V Amat""",
     """    (to_slice_mut_back1 s5) out_buf p hℓ hμ ht hMU hT hL0 hL4 hfit hlenout pk_bytes V Amat"""),
    ("KemDecap.lean",
     """    (hMU : MU.val = 6 ∨ MU.val = 8 ∨ MU.val = 10) (hT : 3 ≤ T.val ∧ T.val ≤ 6)
    (hfit : L.val * 10 * 256 ≤ Usize.max) (hbuf : Spec.Kopis.ctSize p ≤ 1472)""",
     """    (hMU : MU.val = 6 ∨ MU.val = 8 ∨ MU.val = 10) (hT : 3 ≤ T.val ∧ T.val ≤ 6)
    (hL0 : 0 < L.val) (hL4 : L.val ≤ 4)
    (hfit : L.val * 10 * 256 ≤ Usize.max) (hbuf : Spec.Kopis.ctSize p ≤ 1472)"""),
    ("KemDecap.lean",
     """    (to_slice_mut_back1 s5) reconstructed_ct p hℓ hμ ht hMU ⟨by omega, by omega⟩ hfit hrclen""",
     """    (to_slice_mut_back1 s5) reconstructed_ct p hℓ hμ ht hMU ⟨by omega, by omega⟩ hL0 hL4 hfit
    hrclen"""),
    ("PkeFromBytes.lean",
     """theorem pke_from_bytes_spec {L : Usize} (bytes : Slice U8)
    (hlen : bytes.length = 320 * L.val + 32)
    (hfit : L.val * 10 * 256 ≤ Usize.max) :""",
     """theorem pke_from_bytes_spec {L : Usize} (bytes : Slice U8)
    (hlen : bytes.length = 320 * L.val + 32)
    (hfit : L.val * 10 * 256 ≤ Usize.max) (hLsq : L.val * L.val + 4 ≤ Usize.max) :"""),
    ("PkeFromBytes.lean",
     """  let* ⟨ mat_a, hmat, hmatbnd ⟩ ← spec_and (gen_matrix_from_seed_spec L matrix_seed)
    (gen_matrix_uniformBounded matrix_seed)""",
     """  let* ⟨ mat_a, hmat, hmatbnd ⟩ ←
    spec_and (gen_matrix_from_seed_spec L matrix_seed hLsq)
    (gen_matrix_uniformBounded matrix_seed hLsq)"""),
    # The concrete parameter sets: `L` is a literal here, so the new hypotheses are `decide`.
    ("Impls.lean",
     """encap_deterministic_spec 10#usize 3#usize randomness self s
    .Kopis_512 pk_bytes rfl rfl rfl (by decide) (by decide) (by scalar_tac)""",
     """encap_deterministic_spec 10#usize 3#usize randomness self s
    .Kopis_512 pk_bytes rfl rfl rfl (by decide) (by decide) (by decide) (by decide)
    (by scalar_tac)"""),
    ("Impls.lean",
     """decap_spec 10#usize 3#usize self (Array.to_slice encapsulated_key)
    .Kopis_512 sk_seed pk_bytes rfl rfl rfl (by decide) (by decide) (by scalar_tac)""",
     """decap_spec 10#usize 3#usize self (Array.to_slice encapsulated_key)
    .Kopis_512 sk_seed pk_bytes rfl rfl rfl (by decide) (by decide) (by decide) (by decide)
    (by scalar_tac)"""),
    ("Impls.lean",
     """encap_deterministic_spec 8#usize 4#usize randomness self s
    .Kopis_768 pk_bytes rfl rfl rfl (by decide) (by decide) (by scalar_tac)""",
     """encap_deterministic_spec 8#usize 4#usize randomness self s
    .Kopis_768 pk_bytes rfl rfl rfl (by decide) (by decide) (by decide) (by decide)
    (by scalar_tac)"""),
    ("Impls.lean",
     """decap_spec 8#usize 4#usize self (Array.to_slice encapsulated_key)
    .Kopis_768 sk_seed pk_bytes rfl rfl rfl (by decide) (by decide) (by scalar_tac)""",
     """decap_spec 8#usize 4#usize self (Array.to_slice encapsulated_key)
    .Kopis_768 sk_seed pk_bytes rfl rfl rfl (by decide) (by decide) (by decide) (by decide)
    (by scalar_tac)"""),
    ("Impls.lean",
     """encap_deterministic_spec 6#usize 6#usize randomness self s
    .Kopis_1024 pk_bytes rfl rfl rfl (by decide) (by decide) (by scalar_tac)""",
     """encap_deterministic_spec 6#usize 6#usize randomness self s
    .Kopis_1024 pk_bytes rfl rfl rfl (by decide) (by decide) (by decide) (by decide)
    (by scalar_tac)"""),
    ("Impls.lean",
     """decap_spec 6#usize 6#usize self (Array.to_slice encapsulated_key)
    .Kopis_1024 sk_seed pk_bytes rfl rfl rfl (by decide) (by decide) (by scalar_tac)""",
     """decap_spec 6#usize 6#usize self (Array.to_slice encapsulated_key)
    .Kopis_1024 sk_seed pk_bytes rfl rfl rfl (by decide) (by decide) (by decide) (by decide)
    (by scalar_tac)"""),
]


# Modules that need the phase C / D results in scope for their patches.
EXTRA_IMPORTS = {
    "Serialize.lean": ["Kopis.Avx2.SerDispatch"],
    "DeserializeCm.lean": ["Kopis.Avx2.SerDispatch", "Kopis.Avx2.SerGeneric"],
    "DeserializeVec.lean": ["Kopis.Avx2.SerDispatch"],
    "Ntt.lean": ["Kopis.Avx2.SerDispatch"],
    "NttCrtElem.lean": ["Kopis.Avx2.Reduce"],
    "NttBridge.lean": ["Kopis.Avx2.Reduce"],
}

HEADER = ("-- AUTOGENERATED from Kopis/Properties/%s by `make generated`.  Do not edit.\n"
          "-- See AVX2_VERIFICATION_PLAN.md phase E: the serial proof, with the extracted\n"
          "-- constants and this stack's namespace renamed, and nothing else changed.\n")

# `_gen_secret_all_goals` used to live here.  It absorbed an AVX2-only `MU % 8 == 0` +
# `cpu::available` guard inside `sample::gen_secret_from_seed_loop`.  That guard is gone: the
# branch moved the vector path up to `gen_secret_from_seed` itself, which now dispatches once and
# calls `backend::avx2::sample::gen_secret_from_seed`.  The loop body is portable-only again, so
# the serial proof applies unchanged and the dispatch is handled by a PATCHES entry instead.

POST_TRANSFORMS = {"NttCrtElem.lean": lambda out: gen_avx2_bridge.patch_elem(out),
                   "NttCrtMul.lean": lambda out: gen_avx2_bridge.patch_mul(out),
                   "NttBridge.lean": lambda out: gen_avx2_bridge.patch(out)}


def convert(text: str, name: str) -> str:
    out = text.replace("RustKopisSerial", "RustKopisAvx2")
    out = out.replace("ExtractedRustSerial", "ExtractedRustAvx2")
    # `import Kopis.Bits.Stream` must NOT be renamed: it is shared.
    out = out.replace("import Kopis.Bits.Stream", "import Kopis.Bits.Stream@KEEP@")
    out = out.replace("Kopis.Properties", "Kopis.Avx2.Properties")
    out = out.replace("import Kopis.Bits.Stream@KEEP@", "import Kopis.Bits.Stream")
    # The shared bit-stream vocabulary lives in `Kopis.Bits.Stream` under `Kopis.Properties`
    # and is deliberately not duplicated, so every twin imports and re-opens it.  (Importing it
    # unconditionally keeps the rule uniform; it is a leaf module with no backend dependency.)
    if "import Kopis.Bits.Stream" not in out:
        out = re.sub(r"(?m)^(import [^\n]*)$", r"\1", out, count=0)
        first_import = re.search(r"(?m)^import [^\n]*$", out)
        if first_import:
            out = (out[:first_import.start()] + "import Kopis.Bits.Stream\n"
                   + out[first_import.start():])
    out = re.sub(r"(?m)^namespace Kopis\.Avx2\.Properties$",
                 "namespace Kopis.Avx2.Properties\n\nopen Kopis.Properties (" + SHARED + ")",
                 out, count=1)
    for mod, old, new in PATCHES:
        if mod != name:
            continue
        if out.count(old) != 1:
            raise SystemExit(
                f"gen_avx2_twins: patch for {mod} does not apply "
                f"({out.count(old)} matches). The serial proof changed; update PATCHES.")
        out = out.replace(old, new, 1)
    if name in POST_TRANSFORMS:
        out = POST_TRANSFORMS[name](out)
    for extra in EXTRA_IMPORTS.get(name, []):
        first_import = re.search(r"(?m)^import [^\n]*$", out)
        out = out[:first_import.start()] + f"import {extra}\n" + out[first_import.start():]
    return HEADER % name + out

def write_if_changed(path: pathlib.Path, text: str) -> bool:
    """Write `text` to `path` only when it differs from what is already there.

    Not a build-time optimisation: lake keys on content hashes, so a bumped mtime on an
    unchanged module costs a rehash and a replay, not a re-elaboration (measured — see the
    note on the audit-copy rule in the Makefile).  The reason is reporting.  The Makefile runs
    this generator on every build, and "3 written, 57 unchanged" says what a serial edit
    actually propagated to; "60 written" every time would say nothing at all.
    """
    if path.exists() and path.read_text() == text:
        return False
    path.write_text(text)
    return True


def main() -> int:
    DST.mkdir(parents=True, exist_ok=True)
    names = sorted(p.name for p in SRC.glob("*.lean"))
    written = 0
    for name in names:
        if write_if_changed(DST / name, convert((SRC / name).read_text(), name)):
            written += 1
    # aggregator, so that a generated TopLevelTheoremsAvx2 can `import Kopis.Avx2.Properties`
    if write_if_changed(pathlib.Path("Kopis/Avx2/Properties.lean"),
                        "-- AUTOGENERATED by `make twins`.  Do not edit.\n"
                        + "".join(f"import Kopis.Avx2.Properties.{n[:-5]}\n" for n in names)):
        written += 1
    # A serial module that has been deleted or renamed leaves a twin behind; it would still
    # compile and would still be picked up by the `KopisAvx2Properties` glob, so drop it.
    stale = [q for q in sorted(DST.glob("*.lean")) if q.name not in names]
    for q in stale:
        q.unlink()
    if written or stale:
        print(f"twins: {written} written, {len(names) + 1 - written} unchanged, "
              f"{len(stale)} removed")
    return 0

if __name__ == "__main__":
    sys.exit(main())
