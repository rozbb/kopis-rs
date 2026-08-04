#!/usr/bin/env python3
"""The dispatch-point patches, applied by `scripts/gen_avx2_twins.py`.

Four extracted declarations differ between the two backends — the `if cpu::available()` sites —
so any serial theorem that unfolds one of them does not transfer:

    NttElem::from_uniform          ntt::pointwise_mul_acc
    NttElem::from_secret           ntt::reduce_invntt_to_ring_elem

This file patches the four, and that is *all* it patches.  Until 2026-08-04 it was 700 lines,
because the two backends stored different things in an `NttElem` — one residue mod
`p = 50330113` against two 16-bit residues — so the serial `ElemOK` was **false** on the vector
branch and a parallel `UOK`/`SOK` had to be threaded through every matrix loop.  The portable
transform now uses the same two-prime scheme and the same `[i16; 512]` layout, so the two
branches prove *the same postcondition* and the patch is four case splits.

Each is `obtain ⟨b, hb⟩ := available_ok; cases b`, with the portable proof unchanged on `false`
and `Kopis/Avx2/Reduce.lean`'s corresponding theorem on `true`.  `available_ok` assumes only that
the probe returns, not what it returns.

Every edit is anchored on exact serial text and asserted to apply exactly `n` times, so a change
to the serial proof fails the generator loudly rather than silently producing a stale twin.
"""

_ELEM: list = []
_MUL: list = []
_BRIDGE: list = []


def _apply(edits, t, what):
    for old, new, cnt in edits:
        got = t.count(old)
        if got != cnt:
            raise SystemExit(
                f"gen_avx2_twins: {what} patch anchor matched {got} times (want {cnt}); "
                f"the serial proof changed.  Anchor starts: {old[:90]!r}")
        t = t.replace(old, new)
    return t


# ---------------------------------------------------------------------------------------
# NttCrtElem.lean — the two element constructors
# ---------------------------------------------------------------------------------------

_ELEM.append((
    """/-! ## The two `NttElem` constructors -/""",
    r"""/-! ## The two `NttElem` constructors

AVX2 only: both are dispatch points.  `available_ok` says the probe returns; whichever way it
goes, the postcondition is the same one — which is the whole benefit of the two backends now
agreeing on the representation. -/

/-- A stored `u16` read as an `i16` is exactly its `BitVec` signed reading, which is the form the
AVX2 lemmas use. -/
theorem signedOfU16_toInt (v : U16) : (v.bv).toInt = signedOfU16 v := by
  have hn : v.bv.toNat = v.val := rfl
  have hlt : v.val < 65536 := by have := v.hBounds; scalar_tac
  simp only [BitVec.toInt, signedOfU16, hn]
  norm_num
  split <;> split <;> omega

/-- The AVX2 stack's `NttOK` and this one are the same predicate, spelled through `i16View`
rather than `eZ`.  Both read element `t` of the same `[i16; 512]`. -/
theorem nttOK_of_avx {g : ℕ → ℤ} {ne : Array I16 512#usize} (h : Kopis.Avx2.NttOK g ne) :
    NttOK g ne := h""", 1))

_ELEM.append((
    """  unfold arithmetic.ntt.NttElem.from_uniform arithmetic.ntt_crt.from_uniform
  apply WP.spec_bind (from_ring_elem_spec true elem (by simp))
  intro r hr
  simp only [WP.spec_ok]
  exact hr""",
    """  obtain ⟨b, hb⟩ := Kopis.Avx2.available_ok
  cases b
  · unfold arithmetic.ntt.NttElem.from_uniform
    rw [hb, bind_tc_ok]
    simp only [Bool.false_eq_true, if_false]
    apply WP.spec_bind (show arithmetic.ntt_crt.from_uniform elem
        ⦃ (r : Array I16 512#usize) =>
            NttOK (fun c => signedOfU16 (elem.val[c]!)) r ⦄ from by
      unfold arithmetic.ntt_crt.from_uniform
      exact from_ring_elem_spec true elem (by simp))
    intro r hr
    simp only [WP.spec_ok]
    exact hr
  · refine WP.spec_mono (Kopis.Avx2.from_uniform_NttOK hb elem
      (fun c => signedOfU16 (elem.val[c]!)) (fun c _ => signedOfU16_toInt _)) ?_
    exact fun r hr => nttOK_of_avx hr""", 1))

_ELEM.append((
    """  unfold arithmetic.ntt.NttElem.from_secret arithmetic.ntt_crt.from_secret
  apply WP.spec_bind (from_ring_elem_spec false elem (fun _ => hs))
  intro r hr
  simp only [WP.spec_ok]
  exact hr""",
    """  obtain ⟨b, hb⟩ := Kopis.Avx2.available_ok
  cases b
  · unfold arithmetic.ntt.NttElem.from_secret
    rw [hb, bind_tc_ok]
    simp only [Bool.false_eq_true, if_false]
    apply WP.spec_bind (show arithmetic.ntt_crt.from_secret elem
        ⦃ (r : Array I16 512#usize) =>
            NttOK (fun c => signedOfU16 (elem.val[c]!)) r ⦄ from by
      unfold arithmetic.ntt_crt.from_secret
      exact from_ring_elem_spec false elem (fun _ => hs))
    intro r hr
    simp only [WP.spec_ok]
    exact hr
  · refine WP.spec_mono (Kopis.Avx2.from_secret_NttOK hb elem
      (fun c => signedOfU16 (elem.val[c]!)) (fun c _ => signedOfU16_toInt _)
      (fun c hc => by have := hs c hc; omega) (fun c hc => by have := hs c hc; omega)) ?_
    exact fun r hr => nttOK_of_avx hr""", 1))


# ---------------------------------------------------------------------------------------
# NttBridge.lean — the accumulate loops and the entry point
# ---------------------------------------------------------------------------------------

_PW_OLD = """    apply WP.spec_bind (pointwise_mul_acc_spec acc ne ne1 B B
      ((iter.start.val : ℤ) * (B * B)) h0 h0 (mul_nonneg hstz hBB)
      (by rw [hne']; exact fun t ht => hself iter.start.val t %s ht)
      (by rw [hne1']; exact fun t ht => hother iter.start.val t %s ht) hacc
      (by nlinarith))
    intro acc1 hacc1"""

_PW_NEW = r"""    apply WP.spec_bind (show arithmetic.ntt.pointwise_mul_acc acc ne ne1
        ⦃ (r : Array I32 512#usize) =>
            (∀ t, t < 512 → accZ r t = accZ acc t + eZ ne t * eZ ne1 t) ∧
            (∀ t, t < 512 → |accZ r t| ≤ (iter.start.val : ℤ) * (B * B) + B * B) ⦄ from by
      obtain ⟨bb, hbb⟩ := Kopis.Avx2.available_ok
      cases bb
      · unfold arithmetic.ntt.pointwise_mul_acc
        rw [hbb, bind_tc_ok]
        simp only [Bool.false_eq_true, if_false]
        exact pointwise_mul_acc_spec acc ne ne1 B B
          ((iter.start.val : ℤ) * (B * B)) h0 h0 (mul_nonneg hstz hBB)
          (by rw [hne']; exact fun t ht => hself iter.start.val t %s ht)
          (by rw [hne1']; exact fun t ht => hother iter.start.val t %s ht) hacc
          (by nlinarith)
      · refine WP.spec_mono (Kopis.Avx2.pointwise_mul_acc_avx hbb acc ne ne1 B B
          ((iter.start.val : ℤ) * (B * B)) h0 h0
          (by rw [hne']; exact fun t ht => hself iter.start.val t %s ht)
          (by rw [hne1']; exact fun t ht => hother iter.start.val t %s ht) hacc
          (by nlinarith)) ?_
        exact fun r hr => ⟨fun t ht => (hr t ht).1, fun t ht => (hr t ht).2⟩)
    intro acc1 hacc1"""

for _g in ("hj_lt", "hi_lt"):
    _BRIDGE.append((_PW_OLD % (_g, _g), _PW_NEW % (_g, _g, _g, _g), 1))

_BRIDGE.append((
    "def nttFwdU {X Y : Usize} (A : Mat X Y) : arithmetic.ntt.NttMatrix X Y :=",
    "noncomputable def nttFwdU {X Y : Usize} (A : Mat X Y) : arithmetic.ntt.NttMatrix X Y :=", 1))

_BRIDGE.append((
    "def nttFwdS {X Y : Usize} (s : Mat X Y) : arithmetic.ntt.NttMatrix X Y :=",
    "noncomputable def nttFwdS {X Y : Usize} (s : Mat X Y) : arithmetic.ntt.NttMatrix X Y :=", 1))

_BRIDGE.append((
    """  unfold arithmetic.ntt.reduce_invntt_to_ring_elem
  refine WP.spec_bind (crt_entry_spec N hN acc nu nv (fun jj => uP (u jj)) (fun jj => sP (v jj))
    hu hv hacc (convZ u v N) hHb ?_ ?_) ?_""",
    r"""  have hres1 : ∀ c, c < 256 → ((convZ u v N c : ℤ) : ZMod 7681)
      = ∑ jj ∈ Finset.range N, nconv (fun n => ((uP (u jj) n : ℤ) : ZMod 7681))
          (fun n => ((sP (v jj) n : ℤ) : ZMod 7681)) c := by
    intro c hc
    unfold convZ
    rw [Int.cast_sum]
    refine Finset.sum_congr rfl (fun jj _ => ?_)
    rw [nconvR_intCast, ← nconv_eq_nconvR _ _ c hc]
    rfl
  have hres2 : ∀ c, c < 256 → ((convZ u v N c : ℤ) : ZMod 10753)
      = ∑ jj ∈ Finset.range N, nconv (fun n => ((uP (u jj) n : ℤ) : ZMod 10753))
          (fun n => ((sP (v jj) n : ℤ) : ZMod 10753)) c := by
    intro c hc
    unfold convZ
    rw [Int.cast_sum]
    refine Finset.sum_congr rfl (fun jj _ => ?_)
    rw [nconvR_intCast, ← nconv_eq_nconvR _ _ c hc]
    rfl
  refine WP.spec_mono (show arithmetic.ntt.reduce_invntt_to_ring_elem acc
      ⦃ (r : arithmetic.ring_arith.RingElem) =>
          ∀ c, c < 256 → ((r.val[c]!).val : ℤ) = convZ u v N c % 65536 ⦄ from by
    obtain ⟨bb, hbb⟩ := Kopis.Avx2.available_ok
    cases bb
    · unfold arithmetic.ntt.reduce_invntt_to_ring_elem
      rw [hbb, bind_tc_ok]
      simp only [Bool.false_eq_true, if_false]
      apply WP.spec_bind (crt_entry_spec N hN acc nu nv (fun jj => uP (u jj))
        (fun jj => sP (v jj)) hu hv hacc (convZ u v N) hHb hres1 hres2)
      intro r hr
      simp only [WP.spec_ok]
      exact hr
    · refine WP.spec_mono (Kopis.Avx2.reduce_invntt_to_ring_elem_avx hbb N hN acc nu nv
        (fun jj => uP (u jj)) (fun jj => sP (v jj)) hu hv hacc (convZ u v N) hHb
        hres1 hres2) ?_
      intro r hr c hc
      have hb : ((r.val[c]!).val : ℤ) < 65536 := by
        have := (r.val[c]!).hBounds; scalar_tac
      have h0 : (0 : ℤ) ≤ ((r.val[c]!).val : ℤ) := Int.natCast_nonneg _
      rw [← hr c hc, Int.emod_eq_of_lt h0 hb]) ?_""", 1))

_BRIDGE.append((
    """  · intro c hc
    unfold convZ
    rw [Int.cast_sum]
    refine Finset.sum_congr rfl (fun jj _ => ?_)
    rw [nconvR_intCast]
    rw [← nconv_eq_nconvR _ _ c hc]
    rfl
  · intro c hc
    unfold convZ
    rw [Int.cast_sum]
    refine Finset.sum_congr rfl (fun jj _ => ?_)
    rw [nconvR_intCast]
    rw [← nconv_eq_nconvR _ _ c hc]
    rfl
  · intro r hr""",
    """  · intro r hr""", 1))


# `WP.spec_mono` (rather than `spec_bind`) leaves the result already introduced, so the serial
# proof's `WP.spec_ok` step has nothing to do here.
_BRIDGE.append((
    """  · intro r hr
    simp only [WP.spec_ok]
    apply Vector.ext""",
    """  · intro r hr
    apply Vector.ext""", 1))


def patch_elem(t: str) -> str:
    return _apply(_ELEM, t, "NttCrtElem")


def patch_mul(t: str) -> str:
    return _apply(_MUL, t, "NttCrtMul")


def patch(t: str) -> str:
    return _apply(_BRIDGE, t, "NttBridge")


