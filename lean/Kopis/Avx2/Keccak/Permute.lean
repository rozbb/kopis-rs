/-
  # Kopis/Avx2/Keccak/Permute.lean — `keccak::permute` is Keccak-p[1600, 12].

  `RoundSpec.lean` gives one round; this iterates it.  `keccak.rs::permute` runs the 12 rounds
  two at a time, ping-ponging between `state` and a zeroed `scratch` so neither array is ever
  read and written in the same round — the loop body writes `state → scratch` at even round
  indices and `scratch → state` at odd ones, and returns `state`, which is why the pairing is
  what makes the register reuse safe.

  The loop invariant is `Round.lean`'s `rounds`: at loop entry with counter `p`, the array being
  returned holds `2p` rounds' worth of work starting from spec index 12.  Since `ROUNDS / 2 = 6`,
  the loop ends having applied rounds 12 … 23, which is `KECCAK_p 12` (§3.3 at `ℓ = 6`).

  Everything is stated per lane, at a fixed `l < 4`: the four sponges never interact, so the
  whole file carries one lane index and says nothing about the other three.
-/
import Kopis.Avx2.Keccak.RoundSpec

open Aeneas Aeneas.Std Result
open RustKopisAvx2
open RustKopisAvx2.backend.avx2.intrinsics
open Kopis.Avx2
open Spec.SHA3

namespace Kopis.Avx2.Keccak

set_option maxHeartbeats 2000000

noncomputable section

/-- **The loop invariant.**  With the counter at `p`, what remains is `12 - 2p` rounds starting
at spec index `12 + 2p`. -/
theorem permute_loop_spec (iter : core.ops.range.Range Std.Usize)
    (state scratch : Std.Array Vec256 25#usize) (l : ℕ) (hl : l < 4)
    (hstart : iter.start.val ≤ 6) (hend : iter.«end».val = 6) :
    backend.avx2.keccak.permute_loop iter state scratch
      ⦃ (r : Std.Array Vec256 25#usize) =>
          stateWords r l
            = rounds (stateWords state l) (12 + 2 * iter.start.val) (12 - 2 * iter.start.val) ⦄ := by
  unfold backend.avx2.keccak.permute_loop
  by_cases hlt : iter.start.val < iter.«end».val
  · let* ⟨ o, iter1, ho, hstart', hend' ⟩ ← core.iter.range.IteratorRange.next_Usize_some_spec
    rw [ho]; simp only
    have hs6 : iter.start.val < 6 := by scalar_tac
    let* ⟨ i, hi ⟩ ← Std.Usize.mul_spec (x := 2#usize) (y := iter.start) (by scalar_tac)
    have hiv : i.val = 2 * iter.start.val := by rw [hi]
    let* ⟨ v, hv ⟩ ← round_const_spec i (by rw [hiv]; omega)
    let* ⟨ scratch1, hsc1 ⟩ ← round_spec state scratch v (12 + i.val) l hl hv
    let* ⟨ i1, hi1 ⟩ ← Std.Usize.add_spec (x := i) (y := 1#usize) (by scalar_tac)
    have hi1v : i1.val = 2 * iter.start.val + 1 := by rw [hi1, hiv]
    let* ⟨ v1, hv1 ⟩ ← round_const_spec i1 (by rw [hi1v]; omega)
    let* ⟨ state1, hst1 ⟩ ← round_spec scratch1 state v1 (12 + i1.val) l hl hv1
    apply WP.spec_mono
      (permute_loop_spec iter1 state1 scratch1 l hl
        (by rw [hstart']; scalar_tac) (by rw [hend']; exact hend))
    intro r hr
    rw [hr, hstart']
    have e1 : stateWords scratch1 l = RndW (stateWords state l) (12 + i.val) := by
      funext x y; exact hsc1 x y
    have e2 : stateWords state1 l = RndW (stateWords scratch1 l) (12 + i1.val) := by
      funext x y; exact hst1 x y
    rw [e2, e1, hiv, hi1v]
    have a1 : 12 + (2 * iter.start.val + 1) = 12 + 2 * iter.start.val + 1 := by omega
    have a2 : 12 + 2 * (iter.start.val + 1) = 12 + 2 * iter.start.val + 2 := by omega
    have harith : 12 - 2 * iter.start.val = (12 - 2 * (iter.start.val + 1)) + 2 := by omega
    rw [a1, a2, harith, rounds_two]
  · let* ⟨ o, iter1, hnone, _ ⟩ ← core.iter.range.IteratorRange.next_Usize_none_spec
    rw [hnone]; simp only [WP.spec_ok]
    have hge : iter.start.val = 6 := by scalar_tac
    rw [hge]
    simp only [show 12 - 2 * 6 = 0 from rfl, rounds_zero]
  termination_by iter.«end».val - iter.start.val
  decreasing_by scalar_decr_tac

/-- **`keccak::permute` is Keccak-p[1600, 12] in each of the four lanes.**  The 12 rounds run at
spec round indices 12 … 23, which is what `KECCAK_p 12` does (§3.3 with `ℓ = 6`, `nr = 12`). -/
theorem permute_spec (state : Std.Array Vec256 25#usize) (l : ℕ) (hl : l < 4) :
    backend.avx2.keccak.permute state
      ⦃ (r : Std.Array Vec256 25#usize) =>
          stateWords r l = rounds (stateWords state l) 12 12 ⦄ := by
  unfold backend.avx2.keccak.permute
  obtain ⟨z, hz, _⟩ := setzero_si256_spec
  rw [hz, bind_tc_ok]
  simp only [backend.avx2.keccak.ROUNDS]
  let* ⟨ i, hi ⟩ ← Std.Usize.div_spec
  have hiv : i.val = 6 := by rw [hi]
  apply WP.spec_mono
    (permute_loop_spec ⟨0#usize, i⟩ state (Std.Array.repeat 25#usize z) l hl
      (by simp) (by simpa using hiv))
  intro r hr
  simpa using hr

end
end Kopis.Avx2.Keccak
