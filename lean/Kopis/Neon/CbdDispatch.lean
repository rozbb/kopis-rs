/-
  # Kopis/Neon/CbdDispatch.lean — the `gen_secret_from_seed_loop` dispatch point.

  The second of the eight runtime-dispatch points of `NEON_VERIFICATION_PLAN.md` §3, and the one
  §3 calls "the odd one": NEON keeps a *second* dispatch inside the portable loop, which AVX2 has
  no counterpart for because its batched path has already returned by then.  The extracted body
  has three reachable arms:

  * `MU` byte-aligned (`MU % 8 == 0`, i.e. `MU = 8`) — the portable sampler;
  * otherwise, the backend flag set — `backend::neon::sample::cbd_lanes`;
  * otherwise — the portable sampler again.

  The first and third are the same term, so the only work is the middle one, and phase D's
  `neon_cbd_eq` does it: the vector sampler *is* the portable one.  The two branches also differ
  in how they write the result back (`Array.update` against the `index_mut` closure), which is
  the same store written two ways.

  One shape difference from `Kopis/Avx2/CbdDispatch.lean`, and it makes this file *simpler*: the
  flag arrives as a plain `Bool` parameter `b` of the loop rather than as a monadic call to
  `cpu::available`, because aeneas hoisted the compile-time-`true` probe out of the loop.  So
  there is nothing to bind and nothing to assume — `cases b` covers it.

  As with `SerDispatch.lean`, this lives outside the generated twin: the twin only has to hand
  over its portable-branch obligation.
-/
import Kopis.Neon.CbdEq

open Aeneas Aeneas.Std Result
open RustKopisNeon

namespace Kopis.Neon

open arithmetic.ring_arith (RingElem)

set_option maxHeartbeats 1000000

/-- **Dispatch point 2, inner guard.**  Whatever the flag says, the loop body is the portable
sampler: phase D's `neon_cbd_eq` says the vector sampler *is* the portable one, and the two
branches' write-backs (`Array.update` against the `index_mut` closure) are the same store written
two ways.  Stated as an equality of terms so the generated twin needs only to rewrite. -/
theorem gen_secret_neon_branch_eq {L : Usize} {β : Type} (MU : Usize) (b : Bool)
    (buf1 : Slice U8)
    (secret : arithmetic.matrix_arith.Matrix L 1#usize) (i : Usize)
    (hi : i.val < L.val)
    (hMU : MU.val = 6 ∨ MU.val = 8 ∨ MU.val = 10)
    (hlen : buf1.val.length = 32 * MU.val)
    (k : arithmetic.matrix_arith.Matrix L 1#usize → Result β) :
    (if b then
        (do let re ← backend.neon.sample.cbd_lanes MU buf1
            let (a, index_mut_back) ← Array.index_mut_usize secret i
            let a1 ← Array.update a 0#usize re
            k (index_mut_back a1))
      else
        (do let (a, index_mut_back) ← Array.index_mut_usize secret i
            let (re, index_mut_back1) ← Array.index_mut_usize a 0#usize
            let re1 ← sample.cbd MU buf1 re
            k (index_mut_back (index_mut_back1 re1))))
      = (do let (a, index_mut_back) ← Array.index_mut_usize secret i
            let (re, index_mut_back1) ← Array.index_mut_usize a 0#usize
            let re1 ← sample.cbd MU buf1 re
            k (index_mut_back (index_mut_back1 re1))) := by
  have hia : i.val < secret.length := by simp [Array.length]; omega
  obtain ⟨⟨a, back⟩, hidx, ha, hback⟩ :=
    WP.spec_imp_exists (Array.index_mut_usize_spec secret i hia)
  have h0a : (0#usize).val < a.length := by simp [Array.length]
  obtain ⟨⟨re, back1⟩, hidx1, hre, hback1⟩ :=
    WP.spec_imp_exists (Array.index_mut_usize_spec a 0#usize h0a)
  have hupd : ∀ re1, Array.update a 0#usize re1 = ok (Std.Array.set a 0#usize re1) := by
    intro re1
    obtain ⟨x, hx, hxe⟩ := WP.spec_imp_exists (Array.update_spec a 0#usize re1 h0a)
    rw [hx, hxe]
  cases b
  · simp only [Bool.false_eq_true, reduceIte]
  · simp only [reduceIte]
    rw [Kopis.Neon.neon_cbd_eq buf1 MU re hMU hlen]
    simp only [hidx, bind_tc_ok]
    -- both sides now index the same store; `show` performs the iota reduction that `simp`
    -- leaves alone on `let (x, y) := (a, back)`
    show (do let re' ← sample.cbd MU buf1 re
             let a1 ← Array.update a 0#usize re'
             k (back a1))
        = (do let (re2, back2) ← Array.index_mut_usize a 0#usize
              let re1 ← sample.cbd MU buf1 re2
              k (back (back2 re1)))
    rw [hidx1, bind_tc_ok, hback1]
    simp only [hupd, bind_tc_ok]
    rfl

/-- **Dispatch point 2.**  The full three-way guard collapses to the portable body. -/
theorem gen_secret_body_eq {L : Usize} {β : Type} (MU : Usize) (b : Bool) (buf1 : Slice U8)
    (secret : arithmetic.matrix_arith.Matrix L 1#usize) (i : Usize)
    (hi : i.val < L.val)
    (hMU : MU.val = 6 ∨ MU.val = 8 ∨ MU.val = 10)
    (hlen : buf1.val.length = 32 * MU.val)
    (k : arithmetic.matrix_arith.Matrix L 1#usize → Result β) :
    (do let b1 ← core.num.Usize.is_multiple_of MU 8#usize
        if b1 then
          (do let (a, index_mut_back) ← Array.index_mut_usize secret i
              let (re, index_mut_back1) ← Array.index_mut_usize a 0#usize
              let re1 ← sample.cbd MU buf1 re
              k (index_mut_back (index_mut_back1 re1)))
        else
          (if b then
              (do let re ← backend.neon.sample.cbd_lanes MU buf1
                  let (a, index_mut_back) ← Array.index_mut_usize secret i
                  let a1 ← Array.update a 0#usize re
                  k (index_mut_back a1))
            else
              (do let (a, index_mut_back) ← Array.index_mut_usize secret i
                  let (re, index_mut_back1) ← Array.index_mut_usize a 0#usize
                  let re1 ← sample.cbd MU buf1 re
                  k (index_mut_back (index_mut_back1 re1)))))
      = (do let (a, index_mut_back) ← Array.index_mut_usize secret i
            let (re, index_mut_back1) ← Array.index_mut_usize a 0#usize
            let re1 ← sample.cbd MU buf1 re
            k (index_mut_back (index_mut_back1 re1))) := by
  simp only [core.num.Usize.is_multiple_of, UScalar.is_multiple_of, bind_tc_ok]
  by_cases hb : (MU.val % (8#usize).val == 0) = true
  · rw [if_pos hb]
  · rw [if_neg hb]
    exact gen_secret_neon_branch_eq MU b buf1 secret i hi hMU hlen k

end Kopis.Neon
