/-
  # Kopis/Avx2/CbdDispatch.lean — the `gen_secret_from_seed_loop` dispatch point.

  The second of the six runtime-dispatch points of `AVX2_VERIFICATION_PLAN.md` §E3.  The AVX2
  extraction of `sample::gen_secret_from_seed_loop` has three reachable bodies:

  * `MU` byte-aligned (`MU % 8 == 0`, i.e. `MU = 8`) — the portable sampler;
  * otherwise, AVX2 available — `backend::avx2::sample::cbd`;
  * otherwise — the portable sampler again.

  The first and third are the same term, so the only work is the middle one, and phase D's
  `avx2_cbd_eq` does it: the vector sampler *is* the portable one.  The two branches also differ
  in how they write the result back (`Array.update` against the `index_mut` closure), which is
  the same store written two ways.

  As with `SerDispatch.lean`, this lives outside the generated twin: the twin only has to hand
  over its portable-branch obligation.
-/
import Kopis.Avx2.CbdEq

open Aeneas Aeneas.Std Result
open RustKopisAvx2

namespace Kopis.Avx2

open arithmetic.ring_arith (RingElem)

set_option maxHeartbeats 1000000

/-- **Dispatch point 2, inner guard.**  Whatever `cpu::available` says, the loop body is the
portable sampler: phase D's `avx2_cbd_eq` says the vector sampler *is* the portable one, and the
two branches' write-backs (`Array.update` against the `index_mut` closure) are the same store
written two ways.  Stated as an equality of terms so the generated twin needs only to rewrite. -/
theorem gen_secret_avx_branch_eq {L : Usize} {β : Type} (MU : Usize) (buf1 : Slice U8)
    (secret : arithmetic.matrix_arith.Matrix L 1#usize) (i : Usize)
    (hi : i.val < L.val)
    (hMU : MU.val = 6 ∨ MU.val = 8 ∨ MU.val = 10)
    (hlen : buf1.val.length = 32 * MU.val)
    (k : arithmetic.matrix_arith.Matrix L 1#usize → Result β) :
    (do let b1 ← backend.avx2.cpu.available
        if b1 then
          (do let re ← backend.avx2.sample.cbd MU buf1
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
  obtain ⟨b1, hb1⟩ := available_ok
  rw [hb1, bind_tc_ok]
  cases b1
  · simp only [Bool.false_eq_true, reduceIte]
  · simp only [reduceIte]
    rw [Kopis.Avx2.avx2_cbd_eq buf1 MU re hMU hlen]
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
theorem gen_secret_body_eq {L : Usize} {β : Type} (MU : Usize) (buf1 : Slice U8)
    (secret : arithmetic.matrix_arith.Matrix L 1#usize) (i : Usize)
    (hi : i.val < L.val)
    (hMU : MU.val = 6 ∨ MU.val = 8 ∨ MU.val = 10)
    (hlen : buf1.val.length = 32 * MU.val)
    (k : arithmetic.matrix_arith.Matrix L 1#usize → Result β) :
    (do let b ← core.num.Usize.is_multiple_of MU 8#usize
        if b then
          (do let (a, index_mut_back) ← Array.index_mut_usize secret i
              let (re, index_mut_back1) ← Array.index_mut_usize a 0#usize
              let re1 ← sample.cbd MU buf1 re
              k (index_mut_back (index_mut_back1 re1)))
        else
          (do let b1 ← backend.avx2.cpu.available
              if b1 then
                (do let re ← backend.avx2.sample.cbd MU buf1
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
    exact gen_secret_avx_branch_eq MU buf1 secret i hi hMU hlen k

end Kopis.Avx2
