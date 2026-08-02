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
import pathlib, re, sys

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
]

# Modules that need the phase C / D results in scope for their patches.
EXTRA_IMPORTS = {
    "Serialize.lean": ["Kopis.Avx2.SerDispatch"],
    "DeserializeCm.lean": ["Kopis.Avx2.SerDispatch", "Kopis.Avx2.SerGeneric"],
    "DeserializeVec.lean": ["Kopis.Avx2.SerDispatch"],
    "GenSecretTop.lean": ["Kopis.Avx2.CbdDispatch"],
    "Ntt.lean": ["Kopis.Avx2.SerDispatch"],
}

HEADER = ("-- AUTOGENERATED from Kopis/Properties/%s by `make generated`.  Do not edit.\n"
          "-- See AVX2_VERIFICATION_PLAN.md phase E: the serial proof, with the extracted\n"
          "-- constants and this stack's namespace renamed, and nothing else changed.\n")

def _gen_secret_all_goals(out: str) -> str:
    """`GenSecretTop.lean`: absorb the AVX2-only `MU % 8 == 0` guard.

    The AVX2 extraction of `sample::gen_secret_from_seed_loop` guards the body with
    `MU.is_multiple_of(8)` and then with `cpu::available`, so the serial proof's `step*` splits
    into two goals where the serial file has one.  Both outcomes run the portable sampler
    (`Kopis/Avx2/CbdDispatch.lean`), so collapse the vector branch, re-`step*` the branch the
    guard cut short, and run the unchanged serial argument on both goals.
    """
    collapse = [
        "    -- AVX2 only: `step*` split on the `MU % 8 == 0` guard.  Both outcomes run the",
        "    -- portable sampler, so collapse the vector branch and step into the body the guard",
        "    -- cut short; the serial argument below then applies to both goals verbatim.",
        "    all_goals (try rw [Kopis.Avx2.gen_secret_avx_branch_eq MU buf1 secret iter.start",
        "      hi_lt hMU (by rw [← Slice.length, __post1, Slice.length, hbuflen])])",
        "    all_goals (try step*)",
        "    all_goals",
    ]
    lines = out.split("\n")
    res, i, hits = [], 0, 0
    while i < len(lines):
        res.append(lines[i])
        if lines[i] == "    step*":
            hits += 1
            j = i + 1
            while j < len(lines) and (not lines[j].strip() or lines[j].startswith("    ")):
                j += 1
            res.extend(collapse)
            res.extend(("  " + l) if l.strip() else l for l in lines[i + 1:j])
            i = j
            continue
        i += 1
    if hits != 2:
        raise SystemExit(f"gen_avx2_twins: GenSecretTop transform found {hits} `step*` (want 2). "
                         "The serial proof changed; update _gen_secret_all_goals.")
    return "\n".join(res)


POST_TRANSFORMS = {"GenSecretTop.lean": _gen_secret_all_goals}


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

def main() -> int:
    DST.mkdir(parents=True, exist_ok=True)
    written = 0
    for src in sorted(SRC.glob("*.lean")):
        (DST / src.name).write_text(convert(src.read_text(), src.name))
        written += 1
    # aggregator, so that a generated TopLevelTheoremsAvx2 can `import Kopis.Avx2.Properties`
    mods = sorted(p.stem for p in SRC.glob("*.lean"))
    (pathlib.Path("Kopis/Avx2/Properties.lean")).write_text(
        "-- AUTOGENERATED by `make generated`.  Do not edit.\n"
        + "".join(f"import Kopis.Avx2.Properties.{m}\n" for m in mods))
    print(f"generated {written} twin modules + aggregator")
    return 0

if __name__ == "__main__":
    sys.exit(main())
