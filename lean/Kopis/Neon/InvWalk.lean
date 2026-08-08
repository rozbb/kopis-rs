/-
  # Kopis/Neon/InvWalk.lean — the inverse transform's levels, as residues (plan phase F4).

  The mirror of `Kopis/Neon/NttWalk.lean`.  Same coordinates, same loop shapes, same bound
  hypotheses; what changes is the butterfly — `gs_butterfly_val` instead of `ct_butterfly_val` —
  and with it the layer, `gsLvl` instead of `ctLvl`.

  Two differences worth stating once.  Gentleman-Sande puts the twiddle on the *second* output
  only, so the low half of every pairing is a plain sum and only the high half carries ψ.  And the
  inverse tables already hold `−ζ`, which is exactly the sign `State_gs` asks for, so no negation
  is inserted anywhere below: the ψ that appears *is* `−ζ(2·nb − 1 − b)`.
-/
import Kopis.Neon.NttWalk
import Kopis.Neon.InvNttLevel

open Aeneas Aeneas.Std Result
open RustKopisNeon
open RustKopisNeon.backend.neon.intrinsics

namespace Kopis.Neon

open Kopis.CrtScheme.LevelFn

set_option maxHeartbeats 1000000

/-! ## The transposed levels, in the inverse direction -/


/-- **`neg_zeta` broadcasts `−ζ(k)`, as a residue.**  The bound half is
`Kopis/Neon/InvNttLevel.lean`'s; what is new is the twiddle the layer sees. -/
theorem neg_zeta_val (SECOND : Bool) (q : ℕ) (Zb : ℤ) (Rinv : ZMod q) (ζ : ℕ → ZMod q)
    (kk : Usize) (zi : I16) (hzie : backend.crt.zeta SECOND kk = ok zi) (hzib : |zi.val| ≤ Zb)
    (hzv : ((zi.val : ℤ) : ZMod q) * Rinv = ζ kk.val) (hZb : Zb ≤ 2 ^ 14)
    (qic : I16) (hqinv : backend.crt.qinv SECOND = ok qic)
    (hqinvu : (2 ^ 16 : ℤ) ∣ (qic.val * (q : ℤ) - 1)) :
    ∃ z zq : Vec128, backend.neon.ntt.neg_zeta SECOND kk = ok (z, zq) ∧
      (∀ i < 8, |(lane16 z i).toInt| ≤ Zb) ∧
      (∀ i < 8, (2 ^ 16 : ℤ) ∣ ((lane16 zq i).toInt * (q : ℤ) - (lane16 z i).toInt)) ∧
      (∀ m < 8, laneZ q z m * Rinv = -(ζ kk.val)) := by
  obtain ⟨z, zq, he, hzl, hbd, hzq⟩ :=
    neg_zeta_spec SECOND (q : ℤ) Zb kk zi hzie hzib hZb qic hqinv hqinvu
  refine ⟨z, zq, he, hbd, hzq, fun m hm => ?_⟩
  unfold laneZ
  rw [hzl m hm, ← hzv]
  push_cast
  ring

/-- **The `len = 1` transposed level, as residues.**  Pairs `(2r, 2r+1)`, one fresh ψ per
iteration from `inv1` at table position `4g + r`. -/
theorem invntt_len1_val (SECOND : Bool) (qv : Vec128) (q : ℕ) (Zb B Bt : ℤ) (Rinv : ZMod q)
    (ψm : ℕ → ℕ → ZMod q) (hR : ((2 ^ 16 : ℤ) : ZMod q) * Rinv = 1)
    (hQ : ∀ i < 8, (lane16 qv i).toInt = (q : ℤ)) (hQpos : 0 < (q : ℤ)) (hQlt : (q : ℤ) ≤ 2 ^ 14)
    (hZb : Zb ≤ 2 ^ 14)
    (hB0 : 0 ≤ B) (hBZ : 2 * B * Zb < 2 ^ 15 * (q : ℤ))
    (hBt : 2 * B * Zb + 2 ^ 15 * (q : ℤ) ≤ 2 ^ 16 * Bt) (hfit : 2 * B ≤ 32767)
    (htbl : ∀ kk : Usize, kk.val < 16 → ∃ z zq : Vec128,
        backend.neon.ntt.inv1 SECOND kk = ok (z, zq) ∧
        (∀ i < 8, |(lane16 z i).toInt| ≤ Zb) ∧
        (∀ i < 8, (2 ^ 16 : ℤ) ∣ ((lane16 zq i).toInt * (q : ℤ) - (lane16 z i).toInt)) ∧
        (∀ m < 8, laneZ q z m * Rinv = ψm kk.val m))
    (g : Usize) (hg : g.val < 4) (v : Array Vec128 8#usize)
    (iter : core.ops.range.Range Usize) (hend : iter.«end».val = 4)
    (hv : ∀ j (hj : j < 8), pend1 iter.start.val j → VecBnd (vAt v j hj) B) :
    backend.neon.ntt.invntt_block_loop0_loop0 SECOND iter qv g v
      ⦃ (r : Array Vec128 8#usize) => ∀ j (hj : j < 8), ∀ m < 8,
          if 2 * iter.start.val ≤ j then
            (if j % 2 = 0 then
              laneZ q (vAt r j hj) m = laneZ q (vAt v (2 * (j / 2)) (by omega)) m
                + laneZ q (vAt v (2 * (j / 2) + 1) (by omega)) m
            else
              laneZ q (vAt r j hj) m = ψm (4 * g.val + j / 2) m
                * (laneZ q (vAt v (2 * (j / 2)) (by omega)) m
                    - laneZ q (vAt v (2 * (j / 2) + 1) (by omega)) m))
          else laneZ q (vAt r j hj) m = laneZ q (vAt v j hj) m ⦄ := by
  unfold backend.neon.ntt.invntt_block_loop0_loop0
  by_cases hlt : iter.start.val < iter.«end».val
  · let* ⟨ o, iter1, ho, hstart', hend' ⟩ ← core.iter.range.IteratorRange.next_Usize_some_spec
    rw [ho]
    simp only
    have hr4 : iter.start.val < 4 := by omega
    let* ⟨ i, hi ⟩ ← Std.Usize.mul_spec (x := 4#usize) (y := g) (by scalar_tac)
    let* ⟨ i1, hi1 ⟩ ← Std.Usize.add_spec (x := i) (y := iter.start) (by scalar_tac)
    have hi1v : i1.val = 4 * g.val + iter.start.val := by scalar_tac
    obtain ⟨z, zq, hzt, hz, hzq, hzpsi⟩ := htbl i1 (by scalar_tac)
    rw [hzt, bind_tc_ok]
    let* ⟨ i2, hi2 ⟩ ← Std.Usize.mul_spec (x := 2#usize) (y := iter.start) (by scalar_tac)
    have hi2v : i2.val = 2 * iter.start.val := by scalar_tac
    let* ⟨ lo, hlo ⟩ ← Array.index_usize_spec v i2 (by scalar_tac)
    have hloe : lo = vAt v i2.val (by omega) := by rw [hlo]; rfl
    let* ⟨ i3, hi3 ⟩ ← Std.Usize.add_spec (x := i2) (y := 1#usize) (by scalar_tac)
    have hi3v : i3.val = i2.val + 1 := by scalar_tac
    let* ⟨ hiv, hhi ⟩ ← Array.index_usize_spec v i3 (by scalar_tac)
    have hhie : hiv = vAt v i3.val (by omega) := by rw [hhi]; rfl
    apply WP.spec_bind (WP.spec_both
      (gs_butterfly_spec lo hiv z zq qv (q : ℤ) Zb B Bt hQ hQpos hQlt hz hZb hzq
        (by rw [hloe]; exact hv _ (by omega) ⟨by omega, by omega⟩)
        (by rw [hhie]; exact hv _ (by omega) ⟨by omega, by omega⟩)
        hB0 hBZ hBt hfit)
      (gs_butterfly_val lo hiv z zq qv q Zb B Bt Rinv hR hQ hQpos hQlt hz hZb hzq
        (by rw [hloe]; exact hv _ (by omega) ⟨by omega, by omega⟩)
        (by rw [hhie]; exact hv _ (by omega) ⟨by omega, by omega⟩)
        hB0 hBZ hBt hfit))
    rintro ⟨lo1, hi1'⟩ ⟨⟨hlo1b, hhi1b, -⟩, hbutval⟩
    show (do let v1 ← Array.update v i2 lo1
             let i4 ← i2 + 1#usize
             let a ← Array.update v1 i4 hi1'
             backend.neon.ntt.invntt_block_loop0_loop0 SECOND iter1 qv g a)
        ⦃ (r : Array Vec128 8#usize) => ∀ j (hj : j < 8), ∀ m < 8,
            if 2 * iter.start.val ≤ j then
              (if j % 2 = 0 then
                laneZ q (vAt r j hj) m = laneZ q (vAt v (2 * (j / 2)) (by omega)) m
                  + laneZ q (vAt v (2 * (j / 2) + 1) (by omega)) m
              else
                laneZ q (vAt r j hj) m = ψm (4 * g.val + j / 2) m
                  * (laneZ q (vAt v (2 * (j / 2)) (by omega)) m
                      - laneZ q (vAt v (2 * (j / 2) + 1) (by omega)) m))
            else laneZ q (vAt r j hj) m = laneZ q (vAt v j hj) m ⦄
    let* ⟨ v1, hv1 ⟩ ← Array.update_spec
    let* ⟨ i4, hi4 ⟩ ← Std.Usize.add_spec (x := i2) (y := 1#usize) (by scalar_tac)
    have hi4v : i4.val = i2.val + 1 := by scalar_tac
    let* ⟨ a, ha ⟩ ← Array.update_spec
    have hav : ∀ j (hj : j < 8), vAt a j hj =
        if j = i4.val then hi1' else if j = i2.val then lo1 else vAt v j hj := by
      intro j hj
      rw [ha, vAt_set, hv1, vAt_set]
    have havZ : ∀ j (hj : j < 8), ∀ m < 8, laneZ q (vAt a j hj) m =
        if j = i4.val then laneZ q hi1' m
        else if j = i2.val then laneZ q lo1 m else laneZ q (vAt v j hj) m := by
      intro j hj m hm
      rw [hav j hj]
      split
      · rfl
      · split <;> rfl
    apply WP.spec_mono (invntt_len1_val SECOND qv q Zb B Bt Rinv ψm hR hQ hQpos hQlt hZb hB0 hBZ
      hBt hfit htbl g hg a iter1 (by rw [hend']; exact hend) (by
        intro j hj hpend
        rw [hav j hj, if_neg (by unfold pend1 at hpend; omega),
          if_neg (by unfold pend1 at hpend; omega)]
        exact hv j hj (by unfold pend1 at hpend ⊢; omega)))
    intro r hr j hj m hm
    have hrj := hr j hj m hm
    have hlo1v : laneZ q lo1 m = laneZ q (vAt v i2.val (by omega)) m
        + laneZ q (vAt v i3.val (by omega)) m := by
      have hb := (hbutval m hm).1
      rw [hloe, hhie] at hb
      exact hb
    have hhi1v : laneZ q hi1' m = ψm i1.val m
        * (laneZ q (vAt v i2.val (by omega)) m - laneZ q (vAt v i3.val (by omega)) m) := by
      have hb := (hbutval m hm).2
      rw [hzpsi m hm, hloe, hhie] at hb
      exact hb
    by_cases hge : 2 * iter.start.val ≤ j
    · rw [if_pos hge]
      by_cases hnext : 2 * iter1.start.val ≤ j
      · rw [if_pos hnext] at hrj
        by_cases hpar : j % 2 = 0
        · rw [if_pos hpar] at hrj ⊢
          rw [hrj, havZ (2 * (j / 2)) (by omega) m hm, havZ (2 * (j / 2) + 1) (by omega) m hm,
            if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
        · rw [if_neg hpar] at hrj ⊢
          rw [hrj, havZ (2 * (j / 2)) (by omega) m hm, havZ (2 * (j / 2) + 1) (by omega) m hm,
            if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
      · rw [if_neg hnext] at hrj
        rw [hrj, havZ j hj m hm]
        by_cases hpar : j % 2 = 0
        · rw [if_pos hpar, if_neg (by omega), if_pos (by omega), hlo1v,
            vAt_congr v (by omega) (by omega) (show i2.val = 2 * (j / 2) from by omega),
            vAt_congr v (by omega) (by omega) (show i3.val = 2 * (j / 2) + 1 from by omega)]
        · rw [if_neg hpar, if_pos (by omega), hhi1v,
            vAt_congr v (by omega) (by omega) (show i2.val = 2 * (j / 2) from by omega),
            vAt_congr v (by omega) (by omega) (show i3.val = 2 * (j / 2) + 1 from by omega),
            show i1.val = 4 * g.val + j / 2 from by omega]
    · rw [if_neg hge]
      rw [if_neg (by omega)] at hrj
      rw [hrj, havZ j hj m hm, if_neg (by omega), if_neg (by omega)]
  · let* ⟨ o, iter1, hnone, _ ⟩ ← core.iter.range.IteratorRange.next_Usize_none_spec
    rw [hnone]
    refine (WP.spec_ok _).mpr (fun j hj m hm => ?_)
    rw [if_neg (by omega)]
termination_by iter.«end».val - iter.start.val
decreasing_by scalar_decr_tac

/-- **The `len = 2` transposed level, as residues.** -/
theorem invntt_len2_val (qv z zq : Vec128) (q : ℕ) (Zb B Bt : ℤ) (Rinv : ZMod q)
    (ψm : ℕ → ZMod q) (hR : ((2 ^ 16 : ℤ) : ZMod q) * Rinv = 1)
    (hψ : ∀ m < 8, laneZ q z m * Rinv = ψm m)
    (hQ : ∀ i < 8, (lane16 qv i).toInt = (q : ℤ)) (hQpos : 0 < (q : ℤ)) (hQlt : (q : ℤ) ≤ 2 ^ 14)
    (hz : ∀ i < 8, |(lane16 z i).toInt| ≤ Zb) (hZb : Zb ≤ 2 ^ 14)
    (hzq : ∀ i < 8, (2 ^ 16 : ℤ) ∣ ((lane16 zq i).toInt * (q : ℤ) - (lane16 z i).toInt))
    (hB0 : 0 ≤ B) (hBZ : 2 * B * Zb < 2 ^ 15 * (q : ℤ))
    (hBt : 2 * B * Zb + 2 ^ 15 * (q : ℤ) ≤ 2 ^ 16 * Bt) (hfit : 2 * B ≤ 32767)
    (v : Array Vec128 8#usize) (h : Usize) (hh : h.val < 2)
    (iter : core.ops.range.Range Usize) (hend : iter.«end».val = 2)
    (hv : ∀ j (hj : j < 8), pend2 h.val iter.start.val j → VecBnd (vAt v j hj) B) :
    backend.neon.ntt.invntt_block_loop0_loop1_loop0 iter qv v h z zq
      ⦃ (r : Array Vec128 8#usize) => ∀ j (hj : j < 8), ∀ m < 8,
          if 4 * h.val + iter.start.val ≤ j ∧ j < 4 * h.val + 2 then
            laneZ q (vAt r j hj) m = laneZ q (vAt v (4 * (j / 4) + j % 2) (by omega)) m
              + laneZ q (vAt v (4 * (j / 4) + j % 2 + 2) (by omega)) m
          else if 4 * h.val + 2 + iter.start.val ≤ j ∧ j < 4 * h.val + 4 then
            laneZ q (vAt r j hj) m = ψm m
              * (laneZ q (vAt v (4 * (j / 4) + j % 2) (by omega)) m
                  - laneZ q (vAt v (4 * (j / 4) + j % 2 + 2) (by omega)) m)
          else laneZ q (vAt r j hj) m = laneZ q (vAt v j hj) m ⦄ := by
  unfold backend.neon.ntt.invntt_block_loop0_loop1_loop0
  by_cases hlt : iter.start.val < iter.«end».val
  · let* ⟨ o, iter1, ho, hstart', hend' ⟩ ← core.iter.range.IteratorRange.next_Usize_some_spec
    rw [ho]
    simp only
    have hi2 : iter.start.val < 2 := by omega
    let* ⟨ i1, hi1 ⟩ ← Std.Usize.mul_spec (x := 4#usize) (y := h) (by scalar_tac)
    let* ⟨ base, hbase ⟩ ← Std.Usize.add_spec (x := i1) (y := iter.start) (by scalar_tac)
    have hbv : base.val = 4 * h.val + iter.start.val := by scalar_tac
    let* ⟨ lo, hlo ⟩ ← Array.index_usize_spec v base (by scalar_tac)
    have hloe : lo = vAt v base.val (by omega) := by rw [hlo]; rfl
    let* ⟨ i2, hi2v ⟩ ← Std.Usize.add_spec (x := base) (y := 2#usize) (by scalar_tac)
    have hi2vv : i2.val = base.val + 2 := by scalar_tac
    let* ⟨ hiv, hhi ⟩ ← Array.index_usize_spec v i2 (by scalar_tac)
    have hhie : hiv = vAt v i2.val (by omega) := by rw [hhi]; rfl
    apply WP.spec_bind (WP.spec_both
      (gs_butterfly_spec lo hiv z zq qv (q : ℤ) Zb B Bt hQ hQpos hQlt hz hZb hzq
        (by rw [hloe]; exact hv _ (by omega) (Or.inl ⟨by omega, by omega⟩))
        (by rw [hhie]; exact hv _ (by omega) (Or.inr ⟨by omega, by omega⟩))
        hB0 hBZ hBt hfit)
      (gs_butterfly_val lo hiv z zq qv q Zb B Bt Rinv hR hQ hQpos hQlt hz hZb hzq
        (by rw [hloe]; exact hv _ (by omega) (Or.inl ⟨by omega, by omega⟩))
        (by rw [hhie]; exact hv _ (by omega) (Or.inr ⟨by omega, by omega⟩))
        hB0 hBZ hBt hfit))
    rintro ⟨lo1, hi1'⟩ ⟨⟨hlo1b, hhi1b, -⟩, hbutval⟩
    show (do let v1 ← Array.update v base lo1
             let a ← Array.update v1 i2 hi1'
             backend.neon.ntt.invntt_block_loop0_loop1_loop0 iter1 qv a h z zq)
        ⦃ (r : Array Vec128 8#usize) => ∀ j (hj : j < 8), ∀ m < 8,
            if 4 * h.val + iter.start.val ≤ j ∧ j < 4 * h.val + 2 then
              laneZ q (vAt r j hj) m = laneZ q (vAt v (4 * (j / 4) + j % 2) (by omega)) m
                + laneZ q (vAt v (4 * (j / 4) + j % 2 + 2) (by omega)) m
            else if 4 * h.val + 2 + iter.start.val ≤ j ∧ j < 4 * h.val + 4 then
              laneZ q (vAt r j hj) m = ψm m
                * (laneZ q (vAt v (4 * (j / 4) + j % 2) (by omega)) m
                    - laneZ q (vAt v (4 * (j / 4) + j % 2 + 2) (by omega)) m)
            else laneZ q (vAt r j hj) m = laneZ q (vAt v j hj) m ⦄
    let* ⟨ v1, hv1 ⟩ ← Array.update_spec
    let* ⟨ a, ha ⟩ ← Array.update_spec
    have hav : ∀ j (hj : j < 8), vAt a j hj =
        if j = i2.val then hi1' else if j = base.val then lo1 else vAt v j hj := by
      intro j hj
      rw [ha, vAt_set, hv1, vAt_set]
    have havZ : ∀ j (hj : j < 8), ∀ m < 8, laneZ q (vAt a j hj) m =
        if j = i2.val then laneZ q hi1' m
        else if j = base.val then laneZ q lo1 m else laneZ q (vAt v j hj) m := by
      intro j hj m hm
      rw [hav j hj]
      split
      · rfl
      · split <;> rfl
    apply WP.spec_mono (invntt_len2_val qv z zq q Zb B Bt Rinv ψm hR hψ hQ hQpos hQlt hz hZb hzq
      hB0 hBZ hBt hfit a h hh iter1 (by rw [hend']; exact hend) (by
        intro j hj hpend
        rw [hav j hj, if_neg (by unfold pend2 at hpend; omega),
          if_neg (by unfold pend2 at hpend; omega)]
        exact hv j hj (by unfold pend2 at hpend ⊢; omega)))
    intro r hr j hj m hm
    have hrj := hr j hj m hm
    have hlo1v : laneZ q lo1 m = laneZ q (vAt v (4 * (base.val / 4) + base.val % 2) (by omega)) m
        + laneZ q (vAt v (4 * (base.val / 4) + base.val % 2 + 2) (by omega)) m := by
      have hb := (hbutval m hm).1
      rw [hloe, hhie] at hb
      rw [hb, vAt_congr v (by omega) (by omega)
          (show base.val = 4 * (base.val / 4) + base.val % 2 from by omega),
        vAt_congr v (by omega) (by omega)
          (show i2.val = 4 * (base.val / 4) + base.val % 2 + 2 from by omega)]
    have hhi1v : laneZ q hi1' m = ψm m
        * (laneZ q (vAt v (4 * (base.val / 4) + base.val % 2) (by omega)) m
            - laneZ q (vAt v (4 * (base.val / 4) + base.val % 2 + 2) (by omega)) m) := by
      have hb := (hbutval m hm).2
      rw [hψ m hm, hloe, hhie] at hb
      rw [hb, vAt_congr v (by omega) (by omega)
          (show base.val = 4 * (base.val / 4) + base.val % 2 from by omega),
        vAt_congr v (by omega) (by omega)
          (show i2.val = 4 * (base.val / 4) + base.val % 2 + 2 from by omega)]
    by_cases hL : 4 * h.val + iter.start.val ≤ j ∧ j < 4 * h.val + 2
    · rw [if_pos hL]
      by_cases hJ : j = base.val
      · rw [if_neg (by omega), if_neg (by omega)] at hrj
        rw [hrj, havZ j hj m hm, if_neg (by omega), if_pos hJ, hlo1v,
          vAt_congr v (by omega) (by omega)
            (show 4 * (base.val / 4) + base.val % 2 = 4 * (j / 4) + j % 2 from by omega),
          vAt_congr v (by omega) (by omega)
            (show 4 * (base.val / 4) + base.val % 2 + 2 = 4 * (j / 4) + j % 2 + 2 from by omega)]
      · rw [if_pos (by omega : 4 * h.val + iter1.start.val ≤ j ∧ j < 4 * h.val + 2)] at hrj
        rw [hrj, havZ (4 * (j / 4) + j % 2) (by omega) m hm,
          havZ (4 * (j / 4) + j % 2 + 2) (by omega) m hm,
          if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
    · rw [if_neg hL]
      by_cases hH : 4 * h.val + 2 + iter.start.val ≤ j ∧ j < 4 * h.val + 4
      · rw [if_pos hH]
        by_cases hJ : j = i2.val
        · rw [if_neg (by omega), if_neg (by omega)] at hrj
          rw [hrj, havZ j hj m hm, if_pos hJ, hhi1v,
            vAt_congr v (by omega) (by omega)
              (show 4 * (base.val / 4) + base.val % 2 = 4 * (j / 4) + j % 2 from by omega),
            vAt_congr v (by omega) (by omega)
              (show 4 * (base.val / 4) + base.val % 2 + 2 = 4 * (j / 4) + j % 2 + 2
                from by omega)]
        · rw [if_neg (by omega),
            if_pos (by omega : 4 * h.val + 2 + iter1.start.val ≤ j ∧ j < 4 * h.val + 4)] at hrj
          rw [hrj, havZ (4 * (j / 4) + j % 2) (by omega) m hm,
            havZ (4 * (j / 4) + j % 2 + 2) (by omega) m hm,
            if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
      · rw [if_neg hH]
        rw [if_neg (by omega), if_neg (by omega)] at hrj
        rw [hrj, havZ j hj m hm, if_neg (by omega), if_neg (by omega)]
  · let* ⟨ o, iter1, hnone, _ ⟩ ← core.iter.range.IteratorRange.next_Usize_none_spec
    rw [hnone]
    refine (WP.spec_ok _).mpr (fun j hj m hm => ?_)
    rw [if_neg (by omega), if_neg (by omega)]
termination_by iter.«end».val - iter.start.val
decreasing_by scalar_decr_tac

/-- **The `len = 4` transposed level, as residues.** -/
theorem invntt_len4_val (qv z zq : Vec128) (q : ℕ) (Zb B Bt : ℤ) (Rinv : ZMod q)
    (ψm : ℕ → ZMod q) (hR : ((2 ^ 16 : ℤ) : ZMod q) * Rinv = 1)
    (hψ : ∀ m < 8, laneZ q z m * Rinv = ψm m)
    (hQ : ∀ i < 8, (lane16 qv i).toInt = (q : ℤ)) (hQpos : 0 < (q : ℤ)) (hQlt : (q : ℤ) ≤ 2 ^ 14)
    (hz : ∀ i < 8, |(lane16 z i).toInt| ≤ Zb) (hZb : Zb ≤ 2 ^ 14)
    (hzq : ∀ i < 8, (2 ^ 16 : ℤ) ∣ ((lane16 zq i).toInt * (q : ℤ) - (lane16 z i).toInt))
    (hB0 : 0 ≤ B) (hBZ : 2 * B * Zb < 2 ^ 15 * (q : ℤ))
    (hBt : 2 * B * Zb + 2 ^ 15 * (q : ℤ) ≤ 2 ^ 16 * Bt) (hfit : 2 * B ≤ 32767)
    (v : Array Vec128 8#usize) (iter : core.ops.range.Range Usize) (hend : iter.«end».val = 4)
    (hv : ∀ j (hj : j < 8), pend4 iter.start.val j → VecBnd (vAt v j hj) B) :
    backend.neon.ntt.invntt_block_loop0_loop3 iter qv v z zq
      ⦃ (r : Array Vec128 8#usize) => ∀ j (hj : j < 8), ∀ m < 8,
          if iter.start.val ≤ j ∧ j < 4 then
            laneZ q (vAt r j hj) m = laneZ q (vAt v (j % 4) (by omega)) m
              + laneZ q (vAt v (j % 4 + 4) (by omega)) m
          else if 4 + iter.start.val ≤ j ∧ j < 8 then
            laneZ q (vAt r j hj) m = ψm m
              * (laneZ q (vAt v (j % 4) (by omega)) m - laneZ q (vAt v (j % 4 + 4) (by omega)) m)
          else laneZ q (vAt r j hj) m = laneZ q (vAt v j hj) m ⦄ := by
  unfold backend.neon.ntt.invntt_block_loop0_loop3
  by_cases hlt : iter.start.val < iter.«end».val
  · let* ⟨ o, iter1, ho, hstart', hend' ⟩ ← core.iter.range.IteratorRange.next_Usize_some_spec
    rw [ho]
    simp only
    have hi4 : iter.start.val < 4 := by omega
    let* ⟨ lo, hlo ⟩ ← Array.index_usize_spec v iter.start (by scalar_tac)
    have hloe : lo = vAt v iter.start.val (by omega) := by rw [hlo]; rfl
    let* ⟨ i1, hi1 ⟩ ← Std.Usize.add_spec (x := iter.start) (y := 4#usize) (by scalar_tac)
    have hi1v : i1.val = iter.start.val + 4 := by scalar_tac
    let* ⟨ hiv, hhi ⟩ ← Array.index_usize_spec v i1 (by scalar_tac)
    have hhie : hiv = vAt v i1.val (by omega) := by rw [hhi]; rfl
    apply WP.spec_bind (WP.spec_both
      (gs_butterfly_spec lo hiv z zq qv (q : ℤ) Zb B Bt hQ hQpos hQlt hz hZb hzq
        (by rw [hloe]; exact hv _ (by omega) (Or.inl ⟨by omega, by omega⟩))
        (by rw [hhie]; exact hv _ (by omega) (Or.inr ⟨by omega, by omega⟩))
        hB0 hBZ hBt hfit)
      (gs_butterfly_val lo hiv z zq qv q Zb B Bt Rinv hR hQ hQpos hQlt hz hZb hzq
        (by rw [hloe]; exact hv _ (by omega) (Or.inl ⟨by omega, by omega⟩))
        (by rw [hhie]; exact hv _ (by omega) (Or.inr ⟨by omega, by omega⟩))
        hB0 hBZ hBt hfit))
    rintro ⟨lo1, hi1'⟩ ⟨⟨hlo1b, hhi1b, -⟩, hbutval⟩
    show (do let v1 ← Array.update v iter.start lo1
             let a ← Array.update v1 i1 hi1'
             backend.neon.ntt.invntt_block_loop0_loop3 iter1 qv a z zq)
        ⦃ (r : Array Vec128 8#usize) => ∀ j (hj : j < 8), ∀ m < 8,
            if iter.start.val ≤ j ∧ j < 4 then
              laneZ q (vAt r j hj) m = laneZ q (vAt v (j % 4) (by omega)) m
                + laneZ q (vAt v (j % 4 + 4) (by omega)) m
            else if 4 + iter.start.val ≤ j ∧ j < 8 then
              laneZ q (vAt r j hj) m = ψm m
                * (laneZ q (vAt v (j % 4) (by omega)) m
                    - laneZ q (vAt v (j % 4 + 4) (by omega)) m)
            else laneZ q (vAt r j hj) m = laneZ q (vAt v j hj) m ⦄
    let* ⟨ v1, hv1 ⟩ ← Array.update_spec
    let* ⟨ a, ha ⟩ ← Array.update_spec
    have hav : ∀ j (hj : j < 8), vAt a j hj =
        if j = i1.val then hi1' else if j = iter.start.val then lo1 else vAt v j hj := by
      intro j hj
      rw [ha, vAt_set, hv1, vAt_set]
    have havZ : ∀ j (hj : j < 8), ∀ m < 8, laneZ q (vAt a j hj) m =
        if j = i1.val then laneZ q hi1' m
        else if j = iter.start.val then laneZ q lo1 m else laneZ q (vAt v j hj) m := by
      intro j hj m hm
      rw [hav j hj]
      split
      · rfl
      · split <;> rfl
    apply WP.spec_mono (invntt_len4_val qv z zq q Zb B Bt Rinv ψm hR hψ hQ hQpos hQlt hz hZb hzq
      hB0 hBZ hBt hfit a iter1 (by rw [hend']; exact hend) (by
        intro j hj hpend
        rw [hav j hj, if_neg (by unfold pend4 at hpend; omega),
          if_neg (by unfold pend4 at hpend; omega)]
        exact hv j hj (by unfold pend4 at hpend ⊢; omega)))
    intro r hr j hj m hm
    have hrj := hr j hj m hm
    have hlo1v : laneZ q lo1 m = laneZ q (vAt v (iter.start.val % 4) (by omega)) m
        + laneZ q (vAt v (iter.start.val % 4 + 4) (by omega)) m := by
      have hb := (hbutval m hm).1
      rw [hloe, hhie] at hb
      rw [hb, vAt_congr v (by omega) (by omega) (show iter.start.val = iter.start.val % 4 from
          by omega),
        vAt_congr v (by omega) (by omega) (show i1.val = iter.start.val % 4 + 4 from by omega)]
    have hhi1v : laneZ q hi1' m = ψm m
        * (laneZ q (vAt v (iter.start.val % 4) (by omega)) m
            - laneZ q (vAt v (iter.start.val % 4 + 4) (by omega)) m) := by
      have hb := (hbutval m hm).2
      rw [hψ m hm, hloe, hhie] at hb
      rw [hb, vAt_congr v (by omega) (by omega) (show iter.start.val = iter.start.val % 4 from
          by omega),
        vAt_congr v (by omega) (by omega) (show i1.val = iter.start.val % 4 + 4 from by omega)]
    by_cases hL : iter.start.val ≤ j ∧ j < 4
    · rw [if_pos hL]
      by_cases hJ : j = iter.start.val
      · rw [if_neg (by omega), if_neg (by omega)] at hrj
        rw [hrj, havZ j hj m hm, if_neg (by omega), if_pos hJ, hlo1v,
          vAt_congr v (by omega) (by omega) (show iter.start.val % 4 = j % 4 from by omega),
          vAt_congr v (by omega) (by omega)
            (show iter.start.val % 4 + 4 = j % 4 + 4 from by omega)]
      · rw [if_pos (by omega : iter1.start.val ≤ j ∧ j < 4)] at hrj
        rw [hrj, havZ (j % 4) (by omega) m hm, havZ (j % 4 + 4) (by omega) m hm,
          if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
    · rw [if_neg hL]
      by_cases hH : 4 + iter.start.val ≤ j ∧ j < 8
      · rw [if_pos hH]
        by_cases hJ : j = i1.val
        · rw [if_neg (by omega), if_neg (by omega)] at hrj
          rw [hrj, havZ j hj m hm, if_pos hJ, hhi1v,
            vAt_congr v (by omega) (by omega) (show iter.start.val % 4 = j % 4 from by omega),
            vAt_congr v (by omega) (by omega)
              (show iter.start.val % 4 + 4 = j % 4 + 4 from by omega)]
        · rw [if_neg (by omega),
            if_pos (by omega : 4 + iter1.start.val ≤ j ∧ j < 8)] at hrj
          rw [hrj, havZ (j % 4) (by omega) m hm, havZ (j % 4 + 4) (by omega) m hm,
            if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
      · rw [if_neg hH]
        rw [if_neg (by omega), if_neg (by omega)] at hrj
        rw [hrj, havZ j hj m hm, if_neg (by omega), if_neg (by omega)]
  · let* ⟨ o, iter1, hnone, _ ⟩ ← core.iter.range.IteratorRange.next_Usize_none_spec
    rw [hnone]
    refine (WP.spec_ok _).mpr (fun j hj m hm => ?_)
    rw [if_neg (by omega), if_neg (by omega)]
termination_by iter.«end».val - iter.start.val
decreasing_by scalar_decr_tac

/-- **The `len = 2` level's two halves, as residues.**  `h` walks the two halves of the group,
each taking its own ψ pair — `inv2` at table position `2g + h`. -/
theorem invntt_len2_outer_val (SECOND : Bool) (qv : Vec128) (q : ℕ) (Zb B Bt C : ℤ)
    (Rinv : ZMod q) (ψ2 : ℕ → ℕ → ZMod q) (hR : ((2 ^ 16 : ℤ) : ZMod q) * Rinv = 1)
    (hQ : ∀ i < 8, (lane16 qv i).toInt = (q : ℤ)) (hQpos : 0 < (q : ℤ)) (hQlt : (q : ℤ) ≤ 2 ^ 14)
    (hZb : Zb ≤ 2 ^ 14)
    (hB0 : 0 ≤ B) (hBZ : 2 * B * Zb < 2 ^ 15 * (q : ℤ))
    (hBt : 2 * B * Zb + 2 ^ 15 * (q : ℤ) ≤ 2 ^ 16 * Bt) (hfit : 2 * B ≤ 32767)
    (hC1 : 2 * B ≤ C) (hC2 : Bt ≤ C)
    (htbl : ∀ kk : Usize, kk.val < 8 → ∃ z zq : Vec128,
        backend.neon.ntt.inv2 SECOND kk = ok (z, zq) ∧
        (∀ i < 8, |(lane16 z i).toInt| ≤ Zb) ∧
        (∀ i < 8, (2 ^ 16 : ℤ) ∣ ((lane16 zq i).toInt * (q : ℤ) - (lane16 z i).toInt)) ∧
        (∀ m < 8, laneZ q z m * Rinv = ψ2 kk.val m))
    (g : Usize) (hg : g.val < 4) (v : Array Vec128 8#usize)
    (iter : core.ops.range.Range Usize) (hend : iter.«end».val = 2)
    (hv : ∀ j (hj : j < 8), 4 * iter.start.val ≤ j → VecBnd (vAt v j hj) B) :
    backend.neon.ntt.invntt_block_loop0_loop1 SECOND iter qv g v
      ⦃ (r : Array Vec128 8#usize) => ∀ j (hj : j < 8), ∀ m < 8,
          if 4 * iter.start.val ≤ j then
            (if j % 4 < 2 then
              laneZ q (vAt r j hj) m = laneZ q (vAt v (4 * (j / 4) + j % 2) (by omega)) m
                + laneZ q (vAt v (4 * (j / 4) + j % 2 + 2) (by omega)) m
            else
              laneZ q (vAt r j hj) m = ψ2 (2 * g.val + j / 4) m
                * (laneZ q (vAt v (4 * (j / 4) + j % 2) (by omega)) m
                    - laneZ q (vAt v (4 * (j / 4) + j % 2 + 2) (by omega)) m))
          else laneZ q (vAt r j hj) m = laneZ q (vAt v j hj) m ⦄ := by
  unfold backend.neon.ntt.invntt_block_loop0_loop1
  by_cases hlt : iter.start.val < iter.«end».val
  · let* ⟨ o, iter1, ho, hstart', hend' ⟩ ← core.iter.range.IteratorRange.next_Usize_some_spec
    rw [ho]
    simp only
    have hh2 : iter.start.val < 2 := by omega
    let* ⟨ i, hi ⟩ ← Std.Usize.mul_spec (x := 2#usize) (y := g) (by scalar_tac)
    let* ⟨ i1, hi1 ⟩ ← Std.Usize.add_spec (x := i) (y := iter.start) (by scalar_tac)
    have hi1v : i1.val = 2 * g.val + iter.start.val := by scalar_tac
    obtain ⟨z, zq, hzt, hz, hzq, hzpsi⟩ := htbl i1 (by scalar_tac)
    rw [hzt, bind_tc_ok]
    apply WP.spec_bind (WP.spec_both
      (invntt_len2_bnd qv z zq (q : ℤ) Zb B Bt C hQ hQpos hQlt hz hZb hzq hB0 hBZ hBt hfit
        hC1 hC2 v iter.start hh2 ⟨0#usize, 2#usize⟩ rfl (by
          intro j hj hpend
          exact hv j hj (by unfold pend2 at hpend; scalar_tac)))
      (invntt_len2_val qv z zq q Zb B Bt Rinv (ψ2 i1.val) hR (fun m hm => hzpsi m hm) hQ hQpos
        hQlt hz hZb hzq hB0 hBZ hBt hfit v iter.start hh2 ⟨0#usize, 2#usize⟩ rfl (by
          intro j hj hpend
          exact hv j hj (by unfold pend2 at hpend; scalar_tac))))
    rintro v1 ⟨hv1b, hv1v⟩
    have hz0 : ((⟨0#usize, 2#usize⟩ : core.ops.range.Range Usize)).start.val = 0 := by scalar_tac
    simp only [hz0, Nat.add_zero] at hv1v
    apply WP.spec_mono (invntt_len2_outer_val SECOND qv q Zb B Bt C Rinv ψ2 hR hQ hQpos hQlt hZb
      hB0 hBZ hBt hfit hC1 hC2 htbl g hg v1 iter1 (by rw [hend']; exact hend) (by
        intro j hj hge
        have h := hv1b j hj
        rw [if_neg (by unfold pend2; omega)] at h
        rw [h]
        exact hv j hj (by omega)))
    intro r hr j hj m hm
    have hrj := hr j hj m hm
    have hvj := hv1v j hj m hm
    by_cases hge : 4 * iter.start.val ≤ j
    · rw [if_pos hge]
      by_cases hnext : 4 * iter1.start.val ≤ j
      · rw [if_pos hnext] at hrj
        have hp1 := hv1v (4 * (j / 4) + j % 2) (by omega) m hm
        have hp2 := hv1v (4 * (j / 4) + j % 2 + 2) (by omega) m hm
        rw [if_neg (by omega), if_neg (by omega)] at hp1
        rw [if_neg (by omega), if_neg (by omega)] at hp2
        by_cases hpar : j % 4 < 2
        · rw [if_pos hpar] at hrj ⊢
          rw [hrj, hp1, hp2]
        · rw [if_neg hpar] at hrj ⊢
          rw [hrj, hp1, hp2]
      · rw [if_neg hnext] at hrj
        rw [hrj]
        have hjq : j / 4 = iter.start.val := by omega
        have hpsi : ψ2 i1.val m = ψ2 (2 * g.val + j / 4) m := by rw [hi1v, hjq]
        by_cases hpar : j % 4 < 2
        · rw [if_pos hpar]
          rw [if_pos (show 4 * iter.start.val ≤ j ∧ j < 4 * iter.start.val + 2 from
            ⟨by omega, by omega⟩)] at hvj
          rw [hvj]
        · rw [if_neg hpar]
          rw [if_neg (show ¬ (4 * iter.start.val ≤ j ∧ j < 4 * iter.start.val + 2) from
              by omega),
            if_pos (show 4 * iter.start.val + 2 ≤ j ∧ j < 4 * iter.start.val + 4 from
              ⟨by omega, by omega⟩)] at hvj
          rw [hvj, hpsi]
    · rw [if_neg hge]
      rw [if_neg (by omega)] at hrj
      rw [if_neg (by omega), if_neg (by omega)] at hvj
      rw [hrj, hvj]
  · let* ⟨ o, iter1, hnone, _ ⟩ ← core.iter.range.IteratorRange.next_Usize_none_spec
    rw [hnone]
    refine (WP.spec_ok _).mpr (fun j hj m hm => ?_)
    rw [if_neg (by omega)]
termination_by iter.«end».val - iter.start.val
decreasing_by scalar_decr_tac

/-! ## The whole-vector levels, in the inverse direction -/

/-- **One whole-vector level's Gentleman-Sande pass, as residues.** -/
theorem invntt_inner_val (b : Array I16 256#usize) (qv z zq : Vec128) (q : ℕ) (Zb B Bt : ℤ)
    (Rinv ψ : ZMod q) (hR : ((2 ^ 16 : ℤ) : ZMod q) * Rinv = 1)
    (hψ : ∀ m < 8, laneZ q z m * Rinv = ψ)
    (hQ : ∀ i < 8, (lane16 qv i).toInt = (q : ℤ)) (hQpos : 0 < (q : ℤ)) (hQlt : (q : ℤ) ≤ 2 ^ 14)
    (hz : ∀ i < 8, |(lane16 z i).toInt| ≤ Zb) (hZb : Zb ≤ 2 ^ 14)
    (hzq : ∀ i < 8, (2 ^ 16 : ℤ) ∣ ((lane16 zq i).toInt * (q : ℤ) - (lane16 z i).toInt))
    (hB0 : 0 ≤ B) (hBZ : 2 * B * Zb < 2 ^ 15 * (q : ℤ))
    (hBt : 2 * B * Zb + 2 ^ 15 * (q : ℤ) ≤ 2 ^ 16 * Bt) (hfit : 2 * B ≤ 32767)
    (half start i : Usize) (hhalf : 1 ≤ half.val)
    (hrange : start.val + 2 * half.val ≤ 32) (hstart : start.val ≤ i.val)
    (hb : ∀ p < 256, pending start.val half.val i.val p → |(b.val[p]!).val| ≤ B) :
    backend.neon.ntt.invntt_block_loop1_loop0_loop0 b qv half start z zq i
      ⦃ (r : Array I16 256#usize) => ∀ p < 256,
          if 8 * i.val ≤ p ∧ p < 8 * (start.val + half.val) then
            posZ q r p = posZ q b p + posZ q b (p + 8 * half.val)
          else if 8 * (i.val + half.val) ≤ p ∧ p < 8 * (start.val + 2 * half.val) then
            posZ q r p = ψ * (posZ q b (p - 8 * half.val) - posZ q b p)
          else posZ q r p = posZ q b p ⦄ := by
  unfold backend.neon.ntt.invntt_block_loop1_loop0_loop0
  let* ⟨ i1, hi1 ⟩ ← Std.Usize.add_spec (x := start) (y := half) (by scalar_tac)
  by_cases hlt : i < i1
  · rw [if_pos hlt]
    have hiv : i.val < start.val + half.val := by scalar_tac
    obtain ⟨lo, hlo, hlol⟩ := load_i16_val b i (by omega)
    rw [hlo, bind_tc_ok]
    let* ⟨ i2, hi2 ⟩ ← Std.Usize.add_spec (x := i) (y := half) (by scalar_tac)
    have hi2v : i2.val = i.val + half.val := by scalar_tac
    obtain ⟨hv, hhi, hhil⟩ := load_i16_val b i2 (by omega)
    rw [hhi, bind_tc_ok]
    have hlob : VecBnd lo B := by
      intro k hk
      rw [hlol k hk]
      exact hb _ (by omega) (Or.inl ⟨by omega, by omega⟩)
    have hhib : VecBnd hv B := by
      intro k hk
      rw [hhil k hk, hi2v]
      exact hb _ (by omega) (Or.inr ⟨by omega, by omega⟩)
    have hloZ : ∀ m < 8, laneZ q lo m = posZ q b (8 * i.val + m) := by
      intro m hm; unfold laneZ posZ; rw [hlol m hm]
    have hhvZ : ∀ m < 8, laneZ q hv m = posZ q b (8 * i2.val + m) := by
      intro m hm; unfold laneZ posZ; rw [hhil m hm]
    apply WP.spec_bind (gs_butterfly_val lo hv z zq qv q Zb B Bt Rinv hR hQ hQpos hQlt hz hZb
      hzq hlob hhib hB0 hBZ hBt hfit)
    rintro ⟨lo1, hi1'⟩ hval
    show (do let b1 ← backend.neon.intrinsics.store_i16 b i lo1
             let b2 ← backend.neon.intrinsics.store_i16 b1 i2 hi1'
             let i3 ← i + 1#usize
             backend.neon.ntt.invntt_block_loop1_loop0_loop0 b2 qv half start z zq i3)
        ⦃ (r : Array I16 256#usize) => ∀ p < 256,
            if 8 * i.val ≤ p ∧ p < 8 * (start.val + half.val) then
              posZ q r p = posZ q b p + posZ q b (p + 8 * half.val)
            else if 8 * (i.val + half.val) ≤ p ∧ p < 8 * (start.val + 2 * half.val) then
              posZ q r p = ψ * (posZ q b (p - 8 * half.val) - posZ q b p)
            else posZ q r p = posZ q b p ⦄
    obtain ⟨b1, hb1, hb1v⟩ := store_i16_val b i lo1 (by omega)
    rw [hb1, bind_tc_ok]
    obtain ⟨b2, hb2, hb2v⟩ := store_i16_val b1 i2 hi1' (by omega)
    rw [hb2, bind_tc_ok]
    let* ⟨ i3, hi3 ⟩ ← Std.Usize.add_spec (x := i) (y := 1#usize) (by scalar_tac)
    have hi3v : i3.val = i.val + 1 := by scalar_tac
    have hb2all : ∀ p < 256, (b2.val[p]!).val =
        if 8 * i.val ≤ p ∧ p < 8 * i.val + 8 then (lane16 lo1 (p - 8 * i.val)).toInt
        else if 8 * i2.val ≤ p ∧ p < 8 * i2.val + 8 then
          (lane16 hi1' (p - 8 * i2.val)).toInt
        else (b.val[p]!).val := by
      intro p hp
      rw [hb2v p hp, hb1v p hp]
      by_cases h2 : 8 * i2.val ≤ p ∧ p < 8 * i2.val + 8
      · rw [if_pos h2, if_neg (by scalar_tac), if_pos h2]
      · rw [if_neg h2, if_neg h2]
    have hb2Z : ∀ p < 256, posZ q b2 p =
        if 8 * i.val ≤ p ∧ p < 8 * i.val + 8 then laneZ q lo1 (p - 8 * i.val)
        else if 8 * i2.val ≤ p ∧ p < 8 * i2.val + 8 then laneZ q hi1' (p - 8 * i2.val)
        else posZ q b p := by
      intro p hp
      unfold posZ laneZ
      rw [hb2all p hp]
      split
      · rfl
      · split <;> rfl
    apply WP.spec_mono (invntt_inner_val b2 qv z zq q Zb B Bt Rinv ψ hR hψ hQ hQpos hQlt hz hZb
      hzq hB0 hBZ hBt hfit half start i3 hhalf hrange (by omega) (by
        intro p hp hpend
        rw [hb2all p hp, if_neg (by unfold pending at hpend; omega),
          if_neg (by unfold pending at hpend; omega)]
        exact hb p hp (by unfold pending at hpend ⊢; omega)))
    intro r hr p hp
    have hrp := hr p hp
    by_cases hL : 8 * i.val ≤ p ∧ p < 8 * (start.val + half.val)
    · rw [if_pos hL]
      by_cases hLv : p < 8 * i.val + 8
      · rw [if_neg (by omega), if_neg (by omega)] at hrp
        rw [hrp, hb2Z p hp, if_pos ⟨hL.1, hLv⟩, (hval (p - 8 * i.val) (by omega)).1,
          hloZ _ (by omega), hhvZ _ (by omega),
          show 8 * i.val + (p - 8 * i.val) = p from by omega,
          show 8 * i2.val + (p - 8 * i.val) = p + 8 * half.val from by omega]
      · rw [if_pos (by omega : 8 * i3.val ≤ p ∧ p < 8 * (start.val + half.val))] at hrp
        rw [hrp, hb2Z p hp, if_neg (by omega), if_neg (by omega),
          hb2Z (p + 8 * half.val) (by omega), if_neg (by omega), if_neg (by omega)]
    · rw [if_neg hL]
      by_cases hH : 8 * (i.val + half.val) ≤ p ∧ p < 8 * (start.val + 2 * half.val)
      · rw [if_pos hH]
        by_cases hHv : p < 8 * i2.val + 8
        · rw [if_neg (by omega), if_neg (by omega)] at hrp
          rw [hrp, hb2Z p hp, if_neg (by omega), if_pos ⟨by omega, hHv⟩,
            (hval (p - 8 * i2.val) (by omega)).2, hloZ _ (by omega), hhvZ _ (by omega),
            hψ _ (by omega), show 8 * i.val + (p - 8 * i2.val) = p - 8 * half.val from by omega,
            show 8 * i2.val + (p - 8 * i2.val) = p from by omega]
        · rw [if_neg (by omega), if_pos (by omega :
            8 * (i3.val + half.val) ≤ p ∧ p < 8 * (start.val + 2 * half.val))] at hrp
          rw [hrp, hb2Z p hp, if_neg (by omega), if_neg (by omega),
            hb2Z (p - 8 * half.val) (by omega), if_neg (by omega), if_neg (by omega)]
      · rw [if_neg hH]
        rw [if_neg (by omega), if_neg (by omega)] at hrp
        rw [hrp, hb2Z p hp, if_neg (by omega), if_neg (by omega)]
  · rw [if_neg hlt]
    refine (WP.spec_ok _).mpr (fun p hp => ?_)
    have : ¬ (i.val < start.val + half.val) := by scalar_tac
    rw [if_neg (by omega), if_neg (by omega)]

termination_by (start.val + half.val) - i.val
decreasing_by scalar_decr_tac

/-- **The blocks of one whole-vector inverse level, as residues.**

The `k` counter walks *downwards*: the code takes `ζ(k − 1)` at each block, and the layer wants
`−ζ(2·nb − 1 − b)`, so the invariant is `k = 2·nb − b`.  With `nb = 32 / (2·half)` blocks in the
level, that fixes the level's starting `k` at `2·nb` — `32, 16, 8, 4, 2` for
`half = 1, 2, 4, 8, 16`, which is exactly what `invntt_block` passes in and what each level
leaves for the next. -/
theorem invntt_start_val (SECOND : Bool) (b : Array I16 256#usize) (qv : Vec128)
    (q : ℕ) (Zb B Bt C : ℤ) (Rinv : ZMod q) (ζ a0 : ℕ → ZMod q) (nb bIdx : ℕ)
    (hR : ((2 ^ 16 : ℤ) : ZMod q) * Rinv = 1)
    (hQ : ∀ i < 8, (lane16 qv i).toInt = (q : ℤ)) (hQpos : 0 < (q : ℤ)) (hQlt : (q : ℤ) ≤ 2 ^ 14)
    (hZb : Zb ≤ 2 ^ 14)
    (hB0 : 0 ≤ B) (hBZ : 2 * B * Zb < 2 ^ 15 * (q : ℤ))
    (hBt : 2 * B * Zb + 2 ^ 15 * (q : ℤ) ≤ 2 ^ 16 * Bt) (hfit : 2 * B ≤ 32767)
    (hC1 : 2 * B ≤ C) (hC2 : Bt ≤ C)
    (hzeta : ∀ kk : Usize, kk.val < 256 → ∃ zi : I16,
        backend.crt.zeta SECOND kk = ok zi ∧ |zi.val| ≤ Zb ∧
        ((zi.val : ℤ) : ZMod q) * Rinv = ζ kk.val)
    (qic : I16) (hqinv : backend.crt.qinv SECOND = ok qic)
    (hqinvu : (2 ^ 16 : ℤ) ∣ (qic.val * (q : ℤ) - 1))
    (iv k half start : Usize) (hiv : iv.val = 32)
    (hhalf : 1 ≤ half.val) (hnb32 : 32 = nb * (2 * half.val))
    (hstartb : start.val = bIdx * (2 * half.val)) (hstart32 : start.val ≤ 32)
    (hkeq : k.val = 2 * nb - bIdx) (hnb1 : 1 ≤ nb) (hnb256 : 2 * nb ≤ 256)
    (hb : ∀ p < 256, 8 * start.val ≤ p → |(b.val[p]!).val| ≤ B)
    (hva : ∀ c < 256, posZ q b c =
        if c < 8 * start.val then gsLvl q ζ nb (8 * half.val) a0 c else a0 c) :
    backend.neon.ntt.invntt_block_loop1_loop0 SECOND iv b qv k half start
      ⦃ (r : Array I16 256#usize × Usize) =>
          (∀ p < 256, if 8 * start.val ≤ p then |(r.1.val[p]!).val| ≤ C
            else (r.1.val[p]!).val = (b.val[p]!).val) ∧
          (∀ c < 256, posZ q r.1 c = gsLvl q ζ nb (8 * half.val) a0 c) ∧
          r.2.val = nb ⦄ := by
  have hdvd : 2 * half.val ∣ start.val := ⟨bIdx, by rw [hstartb]; ring⟩
  have hhalfdvd : 2 * half.val ∣ 32 := ⟨nb, by rw [hnb32]; ring⟩
  have hm' : 0 < 8 * half.val := by omega
  have hbs : bIdx * (2 * (8 * half.val)) = 8 * start.val := by rw [hstartb]; ring
  unfold backend.neon.ntt.invntt_block_loop1_loop0
  by_cases hlt : start < iv
  · rw [if_pos hlt]
    have hs32 : start.val < 32 := by scalar_tac
    have hbIdx : bIdx < nb := by
      by_contra hcon
      have h1 : nb * (2 * half.val) ≤ bIdx * (2 * half.val) :=
        Nat.mul_le_mul_right _ (by omega)
      omega
    have hfits : start.val + 2 * half.val ≤ 32 := by
      have h1 : (bIdx + 1) * (2 * half.val) ≤ nb * (2 * half.val) :=
        Nat.mul_le_mul_right _ (by omega)
      have h2 : start.val + 2 * half.val = (bIdx + 1) * (2 * half.val) := by rw [hstartb]; ring
      omega
    let* ⟨ k1, hk1 ⟩ ← Std.Usize.sub_spec (x := k) (y := 1#usize) (by scalar_tac)
    have hk1v : k1.val = 2 * nb - 1 - bIdx := by scalar_tac
    obtain ⟨zi, hzi, hzib, hzpsi⟩ := hzeta k1 (by omega)
    obtain ⟨z, zq, hnz, hzlv, hzqlv, hzk'⟩ :=
      neg_zeta_val SECOND q Zb Rinv ζ k1 zi hzi hzib hzpsi hZb qic hqinv hqinvu
    rw [hnz, bind_tc_ok]
    have hzk : ∀ m < 8, laneZ q z m * Rinv = -(ζ (2 * nb - 1 - bIdx)) := by
      intro m hm
      rw [hzk' m hm, hk1v]
    apply WP.spec_bind (WP.spec_both
      (invntt_inner_bnd b qv z zq (q : ℤ) Zb B Bt C hQ hQpos hQlt hzlv hZb hzqlv hB0 hBZ hBt
        hfit hC1 hC2 half start start hhalf hfits (le_refl _) (by
          intro p hp hpend
          exact hb p hp (by unfold pending at hpend; omega)))
      (invntt_inner_val b qv z zq q Zb B Bt Rinv (-(ζ (2 * nb - 1 - bIdx))) hR hzk hQ hQpos hQlt
        hzlv hZb hzqlv hB0 hBZ hBt hfit half start start hhalf hfits (le_refl _) (by
          intro p hp hpend
          exact hb p hp (by unfold pending at hpend; omega))))
    rintro b1 ⟨hb1, hb1v⟩
    have hb1all : ∀ c < 256, posZ q b1 c =
        if c < 8 * (start.val + 2 * half.val) then gsLvl q ζ nb (8 * half.val) a0 c
        else a0 c := by
      intro c hc
      have hcv := hb1v c hc
      by_cases hLo : 8 * start.val ≤ c ∧ c < 8 * (start.val + half.val)
      · rw [if_pos hLo] at hcv
        have hr : c - 8 * start.val < 8 * half.val := by omega
        obtain ⟨hgs, -⟩ := gsLvl_hbut q ζ nb (8 * half.val) a0 hm' bIdx hbIdx
          (c - 8 * start.val) hr
        rw [show bIdx * (2 * (8 * half.val)) + (c - 8 * start.val) = c from by omega] at hgs
        rw [show bIdx * (2 * (8 * half.val)) + 8 * half.val + (c - 8 * start.val)
              = c + 8 * half.val from by omega] at hgs
        rw [if_pos (by omega), hgs, hcv, hva c hc, if_neg (by omega),
          hva (c + 8 * half.val) (by omega), if_neg (by omega)]
      · by_cases hHi : 8 * (start.val + half.val) ≤ c ∧ c < 8 * (start.val + 2 * half.val)
        · rw [if_neg hLo, if_pos hHi] at hcv
          have hr : c - 8 * (start.val + half.val) < 8 * half.val := by omega
          obtain ⟨-, hgs⟩ := gsLvl_hbut q ζ nb (8 * half.val) a0 hm' bIdx hbIdx
            (c - 8 * (start.val + half.val)) hr
          rw [show bIdx * (2 * (8 * half.val)) + (c - 8 * (start.val + half.val))
                = c - 8 * half.val from by omega] at hgs
          rw [show bIdx * (2 * (8 * half.val)) + 8 * half.val
                + (c - 8 * (start.val + half.val)) = c from by omega] at hgs
          rw [if_pos (by omega), hgs, hcv, hva c hc, if_neg (by omega),
            hva (c - 8 * half.val) (by omega), if_neg (by omega)]
        · rw [if_neg hLo, if_neg hHi] at hcv
          rw [hcv, hva c hc]
          by_cases hbelow : c < 8 * start.val
          · rw [if_pos hbelow, if_pos (by omega)]
          · rw [if_neg hbelow, if_neg (by omega)]
    let* ⟨ i4, hi4 ⟩ ← Std.Usize.mul_spec (x := 2#usize) (y := half) (by scalar_tac)
    let* ⟨ start1, hstart1 ⟩ ← Std.Usize.add_spec (x := start) (y := i4) (by scalar_tac)
    have hs1v : start1.val = start.val + 2 * half.val := by scalar_tac
    apply WP.spec_mono (invntt_start_val SECOND b1 qv q Zb B Bt C Rinv ζ a0 nb (bIdx + 1) hR hQ
      hQpos hQlt hZb hB0 hBZ hBt hfit hC1 hC2 hzeta qic hqinv hqinvu iv k1 half start1 hiv hhalf
      hnb32 (by rw [hs1v, hstartb]; ring) (by omega) (by omega) hnb1 hnb256
      (by
        intro p hp hge
        have h := hb1 p hp
        rw [if_neg (by unfold pending; omega)] at h
        rw [h]
        exact hb p hp (by omega))
      (by
        intro c hc
        rw [hb1all c hc, hs1v]))
    rintro ⟨r, kk⟩ ⟨hr1, hr2, hr3⟩
    refine ⟨fun p hp => ?_, hr2, hr3⟩
    have h1 := hr1 p hp
    have h2 := hb1 p hp
    by_cases hge : 8 * start.val ≤ p
    · rw [if_pos hge]
      by_cases hge1 : 8 * start1.val ≤ p
      · rw [if_pos hge1] at h1
        exact h1
      · rw [if_neg hge1] at h1
        rw [if_pos (by unfold pending; omega)] at h2
        rw [h1]
        exact h2
    · rw [if_neg hge]
      rw [if_neg (by omega)] at h1
      rw [if_neg (by unfold pending; omega)] at h2
      rw [h1]
      exact h2
  · rw [if_neg hlt]
    have hs32 : 32 ≤ start.val := by scalar_tac
    have hs : start.val = 32 := by omega
    have hmul : bIdx * (2 * half.val) = nb * (2 * half.val) := by
      rw [← hstartb, hs]; exact hnb32
    have hbn : bIdx = nb := Nat.eq_of_mul_eq_mul_right (by omega) hmul
    have hkk : k.val = nb := by omega
    refine (WP.spec_ok _).mpr ⟨fun p hp => ?_, fun c hc => ?_, hkk⟩
    · rw [if_neg (by omega)]
    · rw [hva c hc, if_pos (by omega)]

termination_by 32 - start.val
decreasing_by scalar_decr_tac

/-! ## Levels 3, 4 and 5, inverse direction, as residues

After the transpose back the group is in coefficient order again, and the last three levels it
carries take a broadcast `−ζ` — indices `31 − 4g − r` and `15 − 2g − h`.  Level 5 is
`invntt_len4_val` with a broadcast twiddle and needs nothing new. -/

theorem invntt_lvl3_val (SECOND : Bool) (qv : Vec128) (q : ℕ) (Zb B Bt : ℤ) (Rinv : ZMod q)
    (ζ : ℕ → ZMod q) (hR : ((2 ^ 16 : ℤ) : ZMod q) * Rinv = 1)
    (hQ : ∀ i < 8, (lane16 qv i).toInt = (q : ℤ)) (hQpos : 0 < (q : ℤ)) (hQlt : (q : ℤ) ≤ 2 ^ 14)
    (hZb : Zb ≤ 2 ^ 14)
    (hB0 : 0 ≤ B) (hBZ : 2 * B * Zb < 2 ^ 15 * (q : ℤ))
    (hBt : 2 * B * Zb + 2 ^ 15 * (q : ℤ) ≤ 2 ^ 16 * Bt) (hfit : 2 * B ≤ 32767)
    (hzeta : ∀ kk : Usize, kk.val < 256 → ∃ zi : I16,
        backend.crt.zeta SECOND kk = ok zi ∧ |zi.val| ≤ Zb ∧
        ((zi.val : ℤ) : ZMod q) * Rinv = ζ kk.val)
    (qic : I16) (hqinv : backend.crt.qinv SECOND = ok qic)
    (hqinvu : (2 ^ 16 : ℤ) ∣ (qic.val * (q : ℤ) - 1))
    (g : Usize) (hg : g.val < 4) (v : Array Vec128 8#usize)
    (iter : core.ops.range.Range Usize) (hend : iter.«end».val = 4)
    (hv : ∀ j (hj : j < 8), pend1 iter.start.val j → VecBnd (vAt v j hj) B) :
    backend.neon.ntt.invntt_block_loop0_loop4 SECOND iter qv g v
      ⦃ (r : Array Vec128 8#usize) => ∀ j (hj : j < 8), ∀ m < 8,
          if 2 * iter.start.val ≤ j then
            (if j % 2 = 0 then
              laneZ q (vAt r j hj) m = laneZ q (vAt v (2 * (j / 2)) (by omega)) m
                + laneZ q (vAt v (2 * (j / 2) + 1) (by omega)) m
            else
              laneZ q (vAt r j hj) m = -(ζ (31 - (4 * g.val + j / 2)))
                * (laneZ q (vAt v (2 * (j / 2)) (by omega)) m
                    - laneZ q (vAt v (2 * (j / 2) + 1) (by omega)) m))
          else laneZ q (vAt r j hj) m = laneZ q (vAt v j hj) m ⦄ := by
  unfold backend.neon.ntt.invntt_block_loop0_loop4
  by_cases hlt : iter.start.val < iter.«end».val
  · let* ⟨ o, iter1, ho, hstart', hend' ⟩ ← core.iter.range.IteratorRange.next_Usize_some_spec
    rw [ho]
    simp only
    have hr4 : iter.start.val < 4 := by omega
    let* ⟨ i, hi ⟩ ← Std.Usize.mul_spec (x := 4#usize) (y := g) (by scalar_tac)
    let* ⟨ i0, hi0 ⟩ ← Std.Usize.sub_spec (x := 31#usize) (y := i) (by scalar_tac)
    let* ⟨ i1, hi1 ⟩ ← Std.Usize.sub_spec (x := i0) (y := iter.start) (by scalar_tac)
    have hi1v : i1.val = 31 - (4 * g.val + iter.start.val) := by scalar_tac
    obtain ⟨zi, hzie, hzib, hzv⟩ := hzeta i1 (by scalar_tac)
    obtain ⟨z, zq, hzt, hz, hzq, hzpsi⟩ :=
      neg_zeta_val SECOND q Zb Rinv ζ i1 zi hzie hzib hzv hZb qic hqinv hqinvu
    rw [hzt, bind_tc_ok]
    let* ⟨ i2, hi2 ⟩ ← Std.Usize.mul_spec (x := 2#usize) (y := iter.start) (by scalar_tac)
    have hi2v : i2.val = 2 * iter.start.val := by scalar_tac
    let* ⟨ lo, hlo ⟩ ← Array.index_usize_spec v i2 (by scalar_tac)
    have hloe : lo = vAt v i2.val (by omega) := by rw [hlo]; rfl
    let* ⟨ i3, hi3 ⟩ ← Std.Usize.add_spec (x := i2) (y := 1#usize) (by scalar_tac)
    have hi3v : i3.val = i2.val + 1 := by scalar_tac
    let* ⟨ hiv, hhi ⟩ ← Array.index_usize_spec v i3 (by scalar_tac)
    have hhie : hiv = vAt v i3.val (by omega) := by rw [hhi]; rfl
    apply WP.spec_bind (WP.spec_both
      (gs_butterfly_spec lo hiv z zq qv (q : ℤ) Zb B Bt hQ hQpos hQlt hz hZb hzq
        (by rw [hloe]; exact hv _ (by omega) ⟨by omega, by omega⟩)
        (by rw [hhie]; exact hv _ (by omega) ⟨by omega, by omega⟩)
        hB0 hBZ hBt hfit)
      (gs_butterfly_val lo hiv z zq qv q Zb B Bt Rinv hR hQ hQpos hQlt hz hZb hzq
        (by rw [hloe]; exact hv _ (by omega) ⟨by omega, by omega⟩)
        (by rw [hhie]; exact hv _ (by omega) ⟨by omega, by omega⟩)
        hB0 hBZ hBt hfit))
    rintro ⟨lo1, hi1'⟩ ⟨⟨hlo1b, hhi1b, -⟩, hbutval⟩
    show (do let v1 ← Array.update v i2 lo1
             let i4 ← i2 + 1#usize
             let a ← Array.update v1 i4 hi1'
             backend.neon.ntt.invntt_block_loop0_loop4 SECOND iter1 qv g a)
        ⦃ (r : Array Vec128 8#usize) => ∀ j (hj : j < 8), ∀ m < 8,
            if 2 * iter.start.val ≤ j then
              (if j % 2 = 0 then
                laneZ q (vAt r j hj) m = laneZ q (vAt v (2 * (j / 2)) (by omega)) m
                  + laneZ q (vAt v (2 * (j / 2) + 1) (by omega)) m
              else
                laneZ q (vAt r j hj) m = -(ζ (31 - (4 * g.val + j / 2)))
                  * (laneZ q (vAt v (2 * (j / 2)) (by omega)) m
                      - laneZ q (vAt v (2 * (j / 2) + 1) (by omega)) m))
            else laneZ q (vAt r j hj) m = laneZ q (vAt v j hj) m ⦄
    let* ⟨ v1, hv1 ⟩ ← Array.update_spec
    let* ⟨ i4, hi4 ⟩ ← Std.Usize.add_spec (x := i2) (y := 1#usize) (by scalar_tac)
    have hi4v : i4.val = i2.val + 1 := by scalar_tac
    let* ⟨ a, ha ⟩ ← Array.update_spec
    have hav : ∀ j (hj : j < 8), vAt a j hj =
        if j = i4.val then hi1' else if j = i2.val then lo1 else vAt v j hj := by
      intro j hj
      rw [ha, vAt_set, hv1, vAt_set]
    have havZ : ∀ j (hj : j < 8), ∀ m < 8, laneZ q (vAt a j hj) m =
        if j = i4.val then laneZ q hi1' m
        else if j = i2.val then laneZ q lo1 m else laneZ q (vAt v j hj) m := by
      intro j hj m hm
      rw [hav j hj]
      split
      · rfl
      · split <;> rfl
    apply WP.spec_mono (invntt_lvl3_val SECOND qv q Zb B Bt Rinv ζ hR hQ hQpos hQlt hZb hB0 hBZ
      hBt hfit hzeta qic hqinv hqinvu g hg a iter1 (by rw [hend']; exact hend) (by
        intro j hj hpend
        rw [hav j hj, if_neg (by unfold pend1 at hpend; omega),
          if_neg (by unfold pend1 at hpend; omega)]
        exact hv j hj (by unfold pend1 at hpend ⊢; omega)))
    intro r hr j hj m hm
    have hrj := hr j hj m hm
    have hlo1v : laneZ q lo1 m = laneZ q (vAt v i2.val (by omega)) m
        + laneZ q (vAt v i3.val (by omega)) m := by
      have hb := (hbutval m hm).1
      rw [hloe, hhie] at hb
      exact hb
    have hhi1v : laneZ q hi1' m = -(ζ i1.val)
        * (laneZ q (vAt v i2.val (by omega)) m - laneZ q (vAt v i3.val (by omega)) m) := by
      have hb := (hbutval m hm).2
      rw [hzpsi m hm, hloe, hhie] at hb
      exact hb
    by_cases hge : 2 * iter.start.val ≤ j
    · rw [if_pos hge]
      by_cases hnext : 2 * iter1.start.val ≤ j
      · rw [if_pos hnext] at hrj
        by_cases hpar : j % 2 = 0
        · rw [if_pos hpar] at hrj ⊢
          rw [hrj, havZ (2 * (j / 2)) (by omega) m hm, havZ (2 * (j / 2) + 1) (by omega) m hm,
            if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
        · rw [if_neg hpar] at hrj ⊢
          rw [hrj, havZ (2 * (j / 2)) (by omega) m hm, havZ (2 * (j / 2) + 1) (by omega) m hm,
            if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
      · rw [if_neg hnext] at hrj
        rw [hrj, havZ j hj m hm]
        by_cases hpar : j % 2 = 0
        · rw [if_pos hpar, if_neg (by omega), if_pos (by omega), hlo1v,
            vAt_congr v (by omega) (by omega) (show i2.val = 2 * (j / 2) from by omega),
            vAt_congr v (by omega) (by omega) (show i3.val = 2 * (j / 2) + 1 from by omega)]
        · rw [if_neg hpar, if_pos (by omega), hhi1v,
            vAt_congr v (by omega) (by omega) (show i2.val = 2 * (j / 2) from by omega),
            vAt_congr v (by omega) (by omega) (show i3.val = 2 * (j / 2) + 1 from by omega),
            show i1.val = 31 - (4 * g.val + j / 2) from by omega]
    · rw [if_neg hge]
      rw [if_neg (by omega)] at hrj
      rw [hrj, havZ j hj m hm, if_neg (by omega), if_neg (by omega)]
  · let* ⟨ o, iter1, hnone, _ ⟩ ← core.iter.range.IteratorRange.next_Usize_none_spec
    rw [hnone]
    refine (WP.spec_ok _).mpr (fun j hj m hm => ?_)
    rw [if_neg (by omega)]
termination_by iter.«end».val - iter.start.val
decreasing_by scalar_decr_tac

theorem invntt_lvl4_val (SECOND : Bool) (qv : Vec128) (q : ℕ) (Zb B Bt C : ℤ)
    (Rinv : ZMod q) (ζ : ℕ → ZMod q) (hR : ((2 ^ 16 : ℤ) : ZMod q) * Rinv = 1)
    (hQ : ∀ i < 8, (lane16 qv i).toInt = (q : ℤ)) (hQpos : 0 < (q : ℤ)) (hQlt : (q : ℤ) ≤ 2 ^ 14)
    (hZb : Zb ≤ 2 ^ 14)
    (hB0 : 0 ≤ B) (hBZ : 2 * B * Zb < 2 ^ 15 * (q : ℤ))
    (hBt : 2 * B * Zb + 2 ^ 15 * (q : ℤ) ≤ 2 ^ 16 * Bt) (hfit : 2 * B ≤ 32767)
    (hC1 : 2 * B ≤ C) (hC2 : Bt ≤ C)
    (hzeta : ∀ kk : Usize, kk.val < 256 → ∃ zi : I16,
        backend.crt.zeta SECOND kk = ok zi ∧ |zi.val| ≤ Zb ∧
        ((zi.val : ℤ) : ZMod q) * Rinv = ζ kk.val)
    (qic : I16) (hqinv : backend.crt.qinv SECOND = ok qic)
    (hqinvu : (2 ^ 16 : ℤ) ∣ (qic.val * (q : ℤ) - 1))
    (g : Usize) (hg : g.val < 4) (v : Array Vec128 8#usize)
    (iter : core.ops.range.Range Usize) (hend : iter.«end».val = 2)
    (hv : ∀ j (hj : j < 8), 4 * iter.start.val ≤ j → VecBnd (vAt v j hj) B) :
    backend.neon.ntt.invntt_block_loop0_loop6 SECOND iter qv g v
      ⦃ (r : Array Vec128 8#usize) => ∀ j (hj : j < 8), ∀ m < 8,
          if 4 * iter.start.val ≤ j then
            (if j % 4 < 2 then
              laneZ q (vAt r j hj) m = laneZ q (vAt v (4 * (j / 4) + j % 2) (by omega)) m
                + laneZ q (vAt v (4 * (j / 4) + j % 2 + 2) (by omega)) m
            else
              laneZ q (vAt r j hj) m = -(ζ (15 - (2 * g.val + j / 4)))
                * (laneZ q (vAt v (4 * (j / 4) + j % 2) (by omega)) m
                    - laneZ q (vAt v (4 * (j / 4) + j % 2 + 2) (by omega)) m))
          else laneZ q (vAt r j hj) m = laneZ q (vAt v j hj) m ⦄ := by
  unfold backend.neon.ntt.invntt_block_loop0_loop6
  by_cases hlt : iter.start.val < iter.«end».val
  · let* ⟨ o, iter1, ho, hstart', hend' ⟩ ← core.iter.range.IteratorRange.next_Usize_some_spec
    rw [ho]
    simp only
    have hh2 : iter.start.val < 2 := by omega
    let* ⟨ i, hi ⟩ ← Std.Usize.mul_spec (x := 2#usize) (y := g) (by scalar_tac)
    let* ⟨ i0, hi0 ⟩ ← Std.Usize.sub_spec (x := 15#usize) (y := i) (by scalar_tac)
    let* ⟨ i1, hi1 ⟩ ← Std.Usize.sub_spec (x := i0) (y := iter.start) (by scalar_tac)
    have hi1v : i1.val = 15 - (2 * g.val + iter.start.val) := by scalar_tac
    obtain ⟨zi, hzie, hzib, hzv⟩ := hzeta i1 (by scalar_tac)
    obtain ⟨z, zq, hzt, hz, hzq, hzpsi⟩ :=
      neg_zeta_val SECOND q Zb Rinv ζ i1 zi hzie hzib hzv hZb qic hqinv hqinvu
    rw [hzt, bind_tc_ok, invntt_loop0_loop6_loop0_eq]
    apply WP.spec_bind (WP.spec_both
      (invntt_len2_bnd qv z zq (q : ℤ) Zb B Bt C hQ hQpos hQlt hz hZb hzq hB0 hBZ hBt hfit
        hC1 hC2 v iter.start hh2 ⟨0#usize, 2#usize⟩ rfl (by
          intro j hj hpend
          exact hv j hj (by unfold pend2 at hpend; scalar_tac)))
      (invntt_len2_val qv z zq q Zb B Bt Rinv (fun _ => -(ζ i1.val)) hR (fun m hm => hzpsi m hm) hQ hQpos
        hQlt hz hZb hzq hB0 hBZ hBt hfit v iter.start hh2 ⟨0#usize, 2#usize⟩ rfl (by
          intro j hj hpend
          exact hv j hj (by unfold pend2 at hpend; scalar_tac))))
    rintro v1 ⟨hv1b, hv1v⟩
    have hz0 : ((⟨0#usize, 2#usize⟩ : core.ops.range.Range Usize)).start.val = 0 := by scalar_tac
    simp only [hz0, Nat.add_zero] at hv1v
    apply WP.spec_mono (invntt_lvl4_val SECOND qv q Zb B Bt C Rinv ζ hR hQ hQpos hQlt hZb
      hB0 hBZ hBt hfit hC1 hC2 hzeta qic hqinv hqinvu g hg v1 iter1 (by rw [hend']; exact hend) (by
        intro j hj hge
        have h := hv1b j hj
        rw [if_neg (by unfold pend2; omega)] at h
        rw [h]
        exact hv j hj (by omega)))
    intro r hr j hj m hm
    have hrj := hr j hj m hm
    have hvj := hv1v j hj m hm
    by_cases hge : 4 * iter.start.val ≤ j
    · rw [if_pos hge]
      by_cases hnext : 4 * iter1.start.val ≤ j
      · rw [if_pos hnext] at hrj
        have hp1 := hv1v (4 * (j / 4) + j % 2) (by omega) m hm
        have hp2 := hv1v (4 * (j / 4) + j % 2 + 2) (by omega) m hm
        rw [if_neg (by omega), if_neg (by omega)] at hp1
        rw [if_neg (by omega), if_neg (by omega)] at hp2
        by_cases hpar : j % 4 < 2
        · rw [if_pos hpar] at hrj ⊢
          rw [hrj, hp1, hp2]
        · rw [if_neg hpar] at hrj ⊢
          rw [hrj, hp1, hp2]
      · rw [if_neg hnext] at hrj
        rw [hrj]
        have hjq : j / 4 = iter.start.val := by omega
        have hpsi : -(ζ i1.val) = -(ζ (15 - (2 * g.val + j / 4))) := by rw [hi1v, hjq]
        by_cases hpar : j % 4 < 2
        · rw [if_pos hpar]
          rw [if_pos (show 4 * iter.start.val ≤ j ∧ j < 4 * iter.start.val + 2 from
            ⟨by omega, by omega⟩)] at hvj
          rw [hvj]
        · rw [if_neg hpar]
          rw [if_neg (show ¬ (4 * iter.start.val ≤ j ∧ j < 4 * iter.start.val + 2) from
              by omega),
            if_pos (show 4 * iter.start.val + 2 ≤ j ∧ j < 4 * iter.start.val + 4 from
              ⟨by omega, by omega⟩)] at hvj
          rw [hvj, hpsi]
    · rw [if_neg hge]
      rw [if_neg (by omega)] at hrj
      rw [if_neg (by omega), if_neg (by omega)] at hvj
      rw [hrj, hvj]
  · let* ⟨ o, iter1, hnone, _ ⟩ ← core.iter.range.IteratorRange.next_Usize_none_spec
    rw [hnone]
    refine (WP.spec_ok _).mpr (fun j hj m hm => ?_)
    rw [if_neg (by omega)]
termination_by iter.«end».val - iter.start.val
decreasing_by scalar_decr_tac

/-! ## The two whole-vector inverse levels

`half = 8` then `half = 16`, with `m' = 8·half` and `nb = 32 / (2·half)`.  Both of the schedule's
last two reductions have already happened inside the group, so there is no re-centring pass here.
The starting `k` is `2·nb` at each level, and `invntt_start_val` reports `nb`, which is the next
level's `2·nb`. -/

/-- The two whole-vector inverse layers, as a function of the view they start from. -/
noncomputable def invH (q : ℕ) (ζ a : ℕ → ZMod q) : ℕ → ZMod q :=
  gsLvl q ζ 1 128 (gsLvl q ζ 2 64 a)

theorem invntt_horizontal_val (SECOND : Bool) (b : Array I16 256#usize) (qv : Vec128)
    (q : ℕ) (Zb B0 T6 C6 T7 C7 : ℤ) (Rinv : ZMod q) (ζ a0 : ℕ → ZMod q)
    (hR : ((2 ^ 16 : ℤ) : ZMod q) * Rinv = 1)
    (hQ : ∀ i < 8, (lane16 qv i).toInt = (q : ℤ)) (hQpos : 0 < (q : ℤ))
    (hQ14 : (q : ℤ) < 2 ^ 14) (hZb : Zb ≤ 2 ^ 14)
    (hzeta : ∀ kk : Usize, kk.val < 256 → ∃ zi : I16,
        backend.crt.zeta SECOND kk = ok zi ∧ |zi.val| ≤ Zb ∧
        ((zi.val : ℤ) : ZMod q) * Rinv = ζ kk.val)
    (qic : I16) (hqinv : backend.crt.qinv SECOND = ok qic)
    (hqinvu : (2 ^ 16 : ℤ) ∣ (qic.val * (q : ℤ) - 1))
    (hB0 : 0 ≤ B0) (hC6 : 0 ≤ C6)
    (l6 : GSLevel (q : ℤ) Zb B0 T6 C6) (l7 : GSLevel (q : ℤ) Zb C6 T7 C7)
    (hb : BlockBnd b B0) (hf : ∀ c < 256, posZ q b c = a0 c) :
    backend.neon.ntt.invntt_block_loop1 SECOND b qv 4#usize 8#usize
      ⦃ (r : Array I16 256#usize) =>
          BlockBnd r C7 ∧ ∀ c < 256, posZ q r c = invH q ζ a0 c ⦄ := by
  have hQ14' : (q : ℤ) ≤ 2 ^ 14 := by omega
  have hvecs : backend.neon.ntt.VECS = ok 32#usize := by
    simp only [backend.neon.ntt.VECS, consts.RING_DEG]; rfl

  -- level 6: half = 8, nb = 2
  unfold backend.neon.ntt.invntt_block_loop1
  rw [hvecs, bind_tc_ok, if_pos (show (8#usize : Usize) < 32#usize by decide)]
  apply WP.spec_bind (invntt_start_val SECOND b qv q Zb B0 T6 C6 Rinv ζ a0
    2 0 hR hQ hQpos hQ14' hZb (by omega) l6.bz l6.bt l6.fit l6.c1 l6.c2 hzeta qic hqinv hqinvu
    32#usize 4#usize 8#usize 0#usize rfl (by scalar_tac) (by scalar_tac) (by scalar_tac)
    (by scalar_tac) (by scalar_tac) (by omega) (by omega) (fun p hp _ => hb p hp)
    (by intro c hc; rw [hf c hc, if_neg (by scalar_tac)]))
  rintro ⟨b1, k1⟩ ⟨hsb1, hvb1, hkb1⟩
  have hvb1n : ∀ c < 256, posZ q b1 c = gsLvl q ζ 2 64 a0 c := by
    intro c hc
    have h := hvb1 c hc
    rwa [show (8 : ℕ) * (8#usize : Usize).val = 64 from by scalar_tac] at h
  show (do let half1 ← (8#usize : Usize) * 2#usize
           backend.neon.ntt.invntt_block_loop1 SECOND b1 qv k1 half1)
      ⦃ (r : Array I16 256#usize) =>
          BlockBnd r C7 ∧ ∀ c < 256, posZ q r c = invH q ζ a0 c ⦄
  rw [show (8#usize : Usize) * 2#usize = ok 16#usize from
      usize_mul_two _ _ (by scalar_tac), bind_tc_ok]
  have hb1 : BlockBnd b1 C6 := blockBnd_of_inv_start hsb1
  have hk1 : k1 = 2#usize := UScalar.eq_of_val_eq (by scalar_tac)
  subst hk1

  -- level 7: half = 16, nb = 1
  unfold backend.neon.ntt.invntt_block_loop1
  rw [hvecs, bind_tc_ok, if_pos (show (16#usize : Usize) < 32#usize by decide)]
  apply WP.spec_bind (invntt_start_val SECOND b1 qv q Zb C6 T7 C7 Rinv ζ (gsLvl q ζ 2 64 a0)
    1 0 hR hQ hQpos hQ14' hZb (by omega) l7.bz l7.bt l7.fit l7.c1 l7.c2 hzeta qic hqinv hqinvu
    32#usize 2#usize 16#usize 0#usize rfl (by scalar_tac) (by scalar_tac) (by scalar_tac)
    (by scalar_tac) (by scalar_tac) (by omega) (by omega) (fun p hp _ => hb1 p hp)
    (by intro c hc; rw [hvb1n c hc, if_neg (by scalar_tac)]))
  rintro ⟨b2, k2⟩ ⟨hsb2, hvb2, hkb2⟩
  have hvb2n : ∀ c < 256, posZ q b2 c = invH q ζ a0 c := by
    intro c hc
    have h := hvb2 c hc
    rwa [show (8 : ℕ) * (16#usize : Usize).val = 128 from by scalar_tac] at h
  show (do let half1 ← (16#usize : Usize) * 2#usize
           backend.neon.ntt.invntt_block_loop1 SECOND b2 qv k2 half1)
      ⦃ (r : Array I16 256#usize) =>
          BlockBnd r C7 ∧ ∀ c < 256, posZ q r c = invH q ζ a0 c ⦄
  rw [show (16#usize : Usize) * 2#usize = ok 32#usize from
      usize_mul_two _ _ (by scalar_tac), bind_tc_ok]
  unfold backend.neon.ntt.invntt_block_loop1
  rw [hvecs, bind_tc_ok, if_neg (by decide)]
  exact (WP.spec_ok _).mpr ⟨blockBnd_of_inv_start hsb2, hvb2n⟩

/-! ## The three inverse transposed layers, in coefficient coordinates

The mirror of `ctLvl_group4` / `_group2` / `_group1`.  The ζ index of a Gentleman-Sande layer is
`2·nb − 1 − b`, and the `inv*Idx` closed forms walk the table downwards to exactly that:

* `len = 1`: block `32g + 4m + k/2`, index `255 − b` = `inv1Idx (8·(4g + k/2) + m)`;
* `len = 2`: block `16g + 2m + k/4`, index `127 − b` = `inv2Idx (8·(2g + k/4) + m)`;
* `len = 4`: block `8g + m`,         index `63 − b`  = `inv4Idx (8g + m)`.
-/

theorem gsLvl_group4 (q : ℕ) (ζ a0 : ℕ → ZMod q) (g m k : ℕ) (_hm : m < 8) (hk : k < 8) :
    gsLvl q ζ 32 4 a0 (64 * g + 8 * m + k) =
      if k < 4 then a0 (64 * g + 8 * m + k) + a0 (64 * g + 8 * m + k + 4)
      else (-(ζ (63 - (8 * g + m))))
          * (a0 (64 * g + 8 * m + k - 4) - a0 (64 * g + 8 * m + k)) := by
  unfold gsLvl
  rw [show (64 * g + 8 * m + k) % (2 * 4) = k from by omega,
    show (64 * g + 8 * m + k) / (2 * 4) = 8 * g + m from by omega]

theorem gsLvl_group2 (q : ℕ) (ζ a0 : ℕ → ZMod q) (g m k : ℕ) (_hm : m < 8) (_hk : k < 8) :
    gsLvl q ζ 64 2 a0 (64 * g + 8 * m + k) =
      if k % 4 < 2 then a0 (64 * g + 8 * m + k) + a0 (64 * g + 8 * m + k + 2)
      else (-(ζ (127 - (16 * g + 2 * m + k / 4))))
          * (a0 (64 * g + 8 * m + k - 2) - a0 (64 * g + 8 * m + k)) := by
  unfold gsLvl
  rw [show (64 * g + 8 * m + k) % (2 * 2) = k % 4 from by omega,
    show (64 * g + 8 * m + k) / (2 * 2) = 16 * g + 2 * m + k / 4 from by omega]

theorem gsLvl_group1 (q : ℕ) (ζ a0 : ℕ → ZMod q) (g m k : ℕ) (_hm : m < 8) (_hk : k < 8) :
    gsLvl q ζ 128 1 a0 (64 * g + 8 * m + k) =
      if k % 2 = 0 then a0 (64 * g + 8 * m + k) + a0 (64 * g + 8 * m + k + 1)
      else (-(ζ (255 - (32 * g + 4 * m + k / 2))))
          * (a0 (64 * g + 8 * m + k - 1) - a0 (64 * g + 8 * m + k)) := by
  unfold gsLvl
  rw [show (64 * g + 8 * m + k) % (2 * 1) = k % 2 from by omega,
    show (64 * g + 8 * m + k) / (2 * 1) = 32 * g + 4 * m + k / 2 from by omega]
  by_cases h : k % 2 = 0
  · rw [if_pos (by omega), if_pos h]
  · rw [if_neg (by omega), if_neg h]

/-! ## The inverse tables carry the twiddles the layers want -/

open Kopis.CrtZeta in
theorem psiFull_inv4 (SECOND : Bool) (q : ℕ) (Zb : ℤ) (Rinv : ZMod q)
    (hz : ∀ k < 256, |((zetasOf SECOND).val[k]!).val| ≤ Zb)
    (hinv : (2 ^ 16 : ℤ) ∣ ((qinvOf SECOND).val * (q : ℤ) - 1))
    (kk : Usize) (hkk : kk.val < 4) :
    ∃ z zq : Vec128, backend.neon.ntt.inv4 SECOND kk = ok (z, zq) ∧ PsiOk z zq (q : ℤ) Zb ∧
      ∀ m < 8, laneZ q z m * Rinv
        = -(zetaQ (zetasOf SECOND) Rinv (63 - (8 * kk.val + m))) := by
  obtain ⟨r, hr, hp⟩ := WP.spec_imp_exists (inv4_spec SECOND kk (by scalar_tac))
  refine ⟨r.1, r.2, by rw [hr], ⟨fun i hi => ?_, fun i hi => ?_⟩, fun m hm => ?_⟩
  · rw [(hp i hi).1]
    unfold tblZ
    split
    · rw [abs_neg]; exact hz _ (by unfold inv4Idx; omega)
    · exact hz _ (by unfold inv4Idx; omega)
  · rw [(hp i hi).1, (hp i hi).2]
    exact tblZq_mont _ _ _ hinv
  · unfold laneZ zetaQ zint
    rw [(hp m hm).1]
    simp only [tblZ, if_true]
    rw [show (inv4Idx (8 * kk.val + m)).toNat = 63 - (8 * kk.val + m) from by
      unfold inv4Idx; omega]
    push_cast
    ring

open Kopis.CrtZeta in
theorem psiFull_inv2 (SECOND : Bool) (q : ℕ) (Zb : ℤ) (Rinv : ZMod q)
    (hz : ∀ k < 256, |((zetasOf SECOND).val[k]!).val| ≤ Zb)
    (hinv : (2 ^ 16 : ℤ) ∣ ((qinvOf SECOND).val * (q : ℤ) - 1))
    (kk : Usize) (hkk : kk.val < 8) :
    ∃ z zq : Vec128, backend.neon.ntt.inv2 SECOND kk = ok (z, zq) ∧ PsiOk z zq (q : ℤ) Zb ∧
      ∀ m < 8, laneZ q z m * Rinv
        = -(zetaQ (zetasOf SECOND) Rinv (127 - (16 * (kk.val / 2) + 2 * m + kk.val % 2))) := by
  obtain ⟨r, hr, hp⟩ := WP.spec_imp_exists (inv2_spec SECOND kk (by scalar_tac))
  refine ⟨r.1, r.2, by rw [hr], ⟨fun i hi => ?_, fun i hi => ?_⟩, fun m hm => ?_⟩
  · rw [(hp i hi).1]
    unfold tblZ
    split
    · rw [abs_neg]; exact hz _ (by unfold inv2Idx; omega)
    · exact hz _ (by unfold inv2Idx; omega)
  · rw [(hp i hi).1, (hp i hi).2]
    exact tblZq_mont _ _ _ hinv
  · unfold laneZ zetaQ zint
    rw [(hp m hm).1]
    simp only [tblZ, if_true]
    rw [show (inv2Idx (8 * kk.val + m)).toNat
        = 127 - (16 * (kk.val / 2) + 2 * m + kk.val % 2) from by
      have e1 : (8 * kk.val + m) / 16 = kk.val / 2 := by omega
      have e2 : (8 * kk.val + m) / 8 % 2 = kk.val % 2 := by omega
      have e3 : (8 * kk.val + m) % 8 = m := by omega
      unfold inv2Idx
      rw [e1, e2, e3]
      omega]
    push_cast
    ring

open Kopis.CrtZeta in
theorem psiFull_inv1 (SECOND : Bool) (q : ℕ) (Zb : ℤ) (Rinv : ZMod q)
    (hz : ∀ k < 256, |((zetasOf SECOND).val[k]!).val| ≤ Zb)
    (hinv : (2 ^ 16 : ℤ) ∣ ((qinvOf SECOND).val * (q : ℤ) - 1))
    (kk : Usize) (hkk : kk.val < 16) :
    ∃ z zq : Vec128, backend.neon.ntt.inv1 SECOND kk = ok (z, zq) ∧ PsiOk z zq (q : ℤ) Zb ∧
      ∀ m < 8, laneZ q z m * Rinv
        = -(zetaQ (zetasOf SECOND) Rinv (255 - (32 * (kk.val / 4) + 4 * m + kk.val % 4))) := by
  obtain ⟨r, hr, hp⟩ := WP.spec_imp_exists (inv1_spec SECOND kk (by scalar_tac))
  refine ⟨r.1, r.2, by rw [hr], ⟨fun i hi => ?_, fun i hi => ?_⟩, fun m hm => ?_⟩
  · rw [(hp i hi).1]
    unfold tblZ
    split
    · rw [abs_neg]; exact hz _ (by unfold inv1Idx; omega)
    · exact hz _ (by unfold inv1Idx; omega)
  · rw [(hp i hi).1, (hp i hi).2]
    exact tblZq_mont _ _ _ hinv
  · unfold laneZ zetaQ zint
    rw [(hp m hm).1]
    simp only [tblZ, if_true]
    rw [show (inv1Idx (8 * kk.val + m)).toNat
        = 255 - (32 * (kk.val / 4) + 4 * m + kk.val % 4) from by
      have e1 : (8 * kk.val + m) / 32 = kk.val / 4 := by omega
      have e2 : (8 * kk.val + m) / 8 % 4 = kk.val % 4 := by omega
      have e3 : (8 * kk.val + m) % 8 = m := by omega
      unfold inv1Idx
      rw [e1, e2, e3]
      omega]
    push_cast
    ring

/-! ## The re-centring pass between the inverse transposed levels

Character for character `Kopis/Neon/NttWalk.lean`'s `ntt_barrett_iter_val`, over
`invntt_block_loop0_loop2` instead of `ntt_block_loop1_loop1`.  aeneas gives the two passes
distinct names because they are distinct loops in the Rust, so the proof cannot be shared. -/

theorem invntt_barrett_iter_val (iter : core.slice.iter.IterMut Vec128)
    (back : core.slice.iter.IterMut Vec128 → core.slice.iter.IterMut Vec128)
    (bm round qv : Vec128) (q : ℕ) (M : ℤ) (val0 : ℕ → ℕ → ZMod q)
    (hQ : ∀ i < 8, (lane16 qv i).toInt = (q : ℤ)) (hM : ∀ i < 8, (lane16 bm i).toInt = M)
    (hRnd : ∀ i < 8, (lane16 round i).toInt = 2 ^ 10)
    (hQpos : 0 < (q : ℤ)) (hQlt : (q : ℤ) < 2 ^ 14) (hQodd : ¬ (2 ∣ (q : ℤ)))
    (hMpos : 0 < M) (hMlt : M < 2 ^ 15) (hD : |2 ^ 27 - (q : ℤ) * M| ≤ 2047)
    (h_len8 : iter.slice.val.length = 8) (h_iter_i : iter.i ≤ 8)
    (hval0 : ∀ (j : ℕ) (hj : j < iter.slice.val.length), ∀ m < 8,
      laneZ q (sAt iter.slice j hj) m = val0 j m)
    (hback_len : ∀ (im : core.slice.iter.IterMut Vec128),
      im.slice.val.length = 8 → (back im).slice.val.length = 8)
    (hback_writes : ∀ (im : core.slice.iter.IterMut Vec128)
      (_him : im.slice.val.length = 8) (j : ℕ) (_hj : j < iter.i)
      (hb : j < (back im).slice.val.length) (m : ℕ) (_hm : m < 8),
        laneZ q (sAt (back im).slice j hb) m = val0 j m)
    (hback_rest : ∀ (im : core.slice.iter.IterMut Vec128)
      (_him : im.slice.val.length = 8) (j : ℕ) (_hge : iter.i ≤ j)
      (hb : j < (back im).slice.val.length) (hb' : j < im.slice.val.length),
        sAt (back im).slice j hb = sAt im.slice j hb') :
    backend.neon.ntt.invntt_block_loop0_loop2 iter back qv bm round
      ⦃ (r : core.slice.iter.IterMut Vec128 ×
             (core.slice.iter.IterMut Vec128 → core.slice.iter.IterMut Vec128)) =>
          ∀ (im : core.slice.iter.IterMut Vec128), im.slice.val.length = 8 →
            ∀ (j : ℕ) (hj : j < (r.2 im).slice.val.length) (m : ℕ), m < 8 →
              laneZ q (sAt (r.2 im).slice j hj) m = val0 j m ⦄ := by
  unfold backend.neon.ntt.invntt_block_loop0_loop2
  by_cases hlt : iter.i < iter.slice.len
  · let* ⟨ o, iter1, next_back, h_all ⟩ ← CbdGeneric.iter_mut_next_spec
    obtain ⟨ho, hit2_slice, hit2_i, hnb_none, hnb_some⟩ := h_all
    rw [ho]
    simp only []
    have hii : iter.i < 8 := by
      have h := hlt
      rw [← h_len8]
      simpa [Slice.len, Slice.length] using h
    have hivl : iter.i < iter.slice.val.length := by omega
    apply WP.spec_bind (barrett_lane_spec (sAt iter.slice iter.i hivl) bm round qv (q : ℤ) M
      hQ hM hRnd hQpos hQlt hQodd hMpos hMlt hD)
    intro slot1 hslot1
    have hnbs : ∀ im : core.slice.iter.IterMut Vec128,
        (next_back im (some slot1)).slice = im.slice.setAtNat iter.i slot1 := by
      intro im
      rw [hnb_some im slot1]
    have hlen' : ∀ (im : core.slice.iter.IterMut Vec128), im.slice.val.length = 8 →
        (next_back im (some slot1)).slice.val.length = 8 := by
      intro im him
      rw [hnbs im]
      simpa [Slice.setAtNat] using him
    -- the Barrett output has the residue of the entry it replaces
    have hslotZ : ∀ m < 8, laneZ q slot1 m = val0 iter.i m := by
      intro m hm
      have hd := (hslot1 m hm).1
      rw [← hval0 iter.i hivl m hm]
      unfold laneZ
      have hcast : (((lane16 slot1 m).toInt
          - (lane16 (sAt iter.slice iter.i hivl) m).toInt : ℤ) : ZMod q) = 0 :=
        (ZMod.intCast_zmod_eq_zero_iff_dvd _ q).mpr hd
      push_cast at hcast
      linear_combination hcast
    apply WP.spec_mono (invntt_barrett_iter_val iter1
      (fun im => back (next_back im (some slot1))) bm round qv q M val0 hQ hM hRnd hQpos hQlt
      hQodd hMpos hMlt hD (by rw [hit2_slice]; exact h_len8) (by omega)
      (by
        intro j hj m hm
        simp only [hit2_slice] at hj ⊢
        exact hval0 j hj m hm)
      (fun im him => hback_len _ (hlen' im him))
      (by
        intro im him j hj hb m hm
        by_cases hje : j = iter.i
        · have hbm : j < (next_back im (some slot1)).slice.val.length := by
            rw [hlen' im him]; omega
          rw [hback_rest (next_back im (some slot1)) (hlen' im him) j (by omega) hb hbm]
          have hset : ∀ (h1 : j < (im.slice.setAtNat iter.i slot1).val.length),
              sAt (next_back im (some slot1)).slice j hbm
                = sAt (im.slice.setAtNat iter.i slot1) j h1 := by
            intro h1
            simp only [hnbs im]
          rw [hset (by rw [← hnbs im]; exact hbm),
            sAt_setAtNat im.slice iter.i slot1 j _ (by omega), if_pos hje]
          rw [hje]
          exact hslotZ m hm
        · exact hback_writes (next_back im (some slot1)) (hlen' im him) j (by omega) hb m hm)
      (by
        intro im him j hge hb hb'
        have hbm : j < (next_back im (some slot1)).slice.val.length := by
          rw [hlen' im him]; omega
        rw [hback_rest (next_back im (some slot1)) (hlen' im him) j (by omega) hb hbm]
        have hset : ∀ (h1 : j < (im.slice.setAtNat iter.i slot1).val.length),
            sAt (next_back im (some slot1)).slice j hbm
              = sAt (im.slice.setAtNat iter.i slot1) j h1 := by
          intro h1
          simp only [hnbs im]
        rw [hset (by rw [← hnbs im]; exact hbm),
          sAt_setAtNat im.slice iter.i slot1 j _ hb', if_neg (by omega)]))
    rintro ⟨r1, r2⟩ hr
    exact hr
  · let* ⟨ o, iter1, next_back, h_all ⟩ ← CbdGeneric.iter_mut_next_spec_none
    obtain ⟨ho, hit_eq, hnb⟩ := h_all
    rw [ho]
    have hi8 : iter.i = 8 := by
      have hnot : ¬ (iter.i < 8) := by
        have h := hlt
        rw [← h_len8]
        simpa [Slice.len, Slice.length] using h
      omega
    refine (WP.spec_ok _).mpr (fun im him => ?_)
    simp only [hnb]
    intro j hj m hm
    exact hback_writes im him j (by rw [hback_len im him] at hj; omega) hj m hm


/-! ## The four groups, inverse direction

Six levels per group: the three transposed ones, a transpose back, and the three vector pairings
that still fit inside eight vectors, with a re-centring pass after the second, the fourth and the
sixth. -/

/-- The three transposed inverse layers, as a function of the view they start from. -/
noncomputable def invT (q : ℕ) (ζ a0 : ℕ → ZMod q) : ℕ → ZMod q :=
  gsLvl q ζ 4 32 (gsLvl q ζ 8 16 (gsLvl q ζ 16 8
    (gsLvl q ζ 32 4 (gsLvl q ζ 64 2 (gsLvl q ζ 128 1 a0)))))

/-! ## The three inverse layers the group carries *after* the transpose back

Coefficient order again, so lane `m` of vector `j` is coefficient `64g + 8j + m`, and the ζ
index of a Gentleman-Sande layer, `2·nb − 1 − b`, comes out as `31 − 4g − j/2`, `15 − 2g − j/4`
and `7 − g` — exactly the `neg_zeta` arguments the Rust computes. -/

theorem gsLvl_lvl3 (q : ℕ) (ζ a0 : ℕ → ZMod q) (g j m : ℕ) (_hj : j < 8) (hm : m < 8) :
    gsLvl q ζ 16 8 a0 (64 * g + 8 * j + m) =
      if j % 2 = 0 then a0 (64 * g + 8 * j + m) + a0 (64 * g + 8 * j + m + 8)
      else (-(ζ (31 - (4 * g + j / 2))))
          * (a0 (64 * g + 8 * j + m - 8) - a0 (64 * g + 8 * j + m)) := by
  unfold gsLvl
  rw [show (64 * g + 8 * j + m) % (2 * 8) = (8 * j + m) % 16 from by omega,
    show 2 * 16 - 1 - (64 * g + 8 * j + m) / (2 * 8) = 31 - (4 * g + j / 2) from by omega]
  by_cases h : j % 2 = 0
  · rw [if_pos (by omega), if_pos h]
  · rw [if_neg (by omega), if_neg h]

theorem gsLvl_lvl4 (q : ℕ) (ζ a0 : ℕ → ZMod q) (g j m : ℕ) (_hj : j < 8) (hm : m < 8) :
    gsLvl q ζ 8 16 a0 (64 * g + 8 * j + m) =
      if j % 4 < 2 then a0 (64 * g + 8 * j + m) + a0 (64 * g + 8 * j + m + 16)
      else (-(ζ (15 - (2 * g + j / 4))))
          * (a0 (64 * g + 8 * j + m - 16) - a0 (64 * g + 8 * j + m)) := by
  unfold gsLvl
  rw [show (64 * g + 8 * j + m) % (2 * 16) = (8 * j + m) % 32 from by omega,
    show 2 * 8 - 1 - (64 * g + 8 * j + m) / (2 * 16) = 15 - (2 * g + j / 4) from by omega]
  by_cases h : j % 4 < 2
  · rw [if_pos (by omega), if_pos h]
  · rw [if_neg (by omega), if_neg h]

theorem gsLvl_lvl5 (q : ℕ) (ζ a0 : ℕ → ZMod q) (g j m : ℕ) (hj : j < 8) (hm : m < 8) :
    gsLvl q ζ 4 32 a0 (64 * g + 8 * j + m) =
      if j < 4 then a0 (64 * g + 8 * j + m) + a0 (64 * g + 8 * j + m + 32)
      else (-(ζ (7 - g))) * (a0 (64 * g + 8 * j + m - 32) - a0 (64 * g + 8 * j + m)) := by
  unfold gsLvl
  rw [show (64 * g + 8 * j + m) % (2 * 32) = 8 * j + m from by omega,
    show 2 * 4 - 1 - (64 * g + 8 * j + m) / (2 * 32) = 7 - g from by omega]
  by_cases h : j < 4
  · rw [if_pos (by omega), if_pos h]
  · rw [if_neg (by omega), if_neg h]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 16000000 in
theorem invntt_group_val (SECOND : Bool) (b : Array I16 256#usize) (qv bm round : Vec128)
    (q : ℕ) (Zb M Ain T0 C0 T1 C1 Ar T2 C2 T3 C3 T4 C4 T5 C5 : ℤ) (Rinv : ZMod q)
    (ζ a0 : ℕ → ZMod q)
    (hR : ((2 ^ 16 : ℤ) : ZMod q) * Rinv = 1)
    (hQ : ∀ i < 8, (lane16 qv i).toInt = (q : ℤ)) (hQpos : 0 < (q : ℤ))
    (hQ14 : (q : ℤ) < 2 ^ 14) (hQodd : ¬ (2 ∣ (q : ℤ))) (hZb : Zb ≤ 2 ^ 14)
    (hM : ∀ i < 8, (lane16 bm i).toInt = M) (hMpos : 0 < M) (hMlt : M < 2 ^ 15)
    (hD : |2 ^ 27 - (q : ℤ) * M| ≤ 2047)
    (hRnd : ∀ i < 8, (lane16 round i).toInt = 2 ^ 10)
    (hzeta : ∀ kk : Usize, kk.val < 256 → ∃ zi : I16,
        backend.crt.zeta SECOND kk = ok zi ∧ |zi.val| ≤ Zb ∧
        ((zi.val : ℤ) : ZMod q) * Rinv = ζ kk.val)
    (qic : I16) (hqinv : backend.crt.qinv SECOND = ok qic)
    (hqinvu : (2 ^ 16 : ℤ) ∣ (qic.val * (q : ℤ) - 1))
    (htbl4 : ∀ kk : Usize, kk.val < 4 → ∃ z zq : Vec128,
        backend.neon.ntt.inv4 SECOND kk = ok (z, zq) ∧ PsiOk z zq (q : ℤ) Zb ∧
        ∀ m < 8, laneZ q z m * Rinv = -(ζ (63 - (8 * kk.val + m))))
    (htbl2 : ∀ kk : Usize, kk.val < 8 → ∃ z zq : Vec128,
        backend.neon.ntt.inv2 SECOND kk = ok (z, zq) ∧ PsiOk z zq (q : ℤ) Zb ∧
        ∀ m < 8, laneZ q z m * Rinv
          = -(ζ (127 - (16 * (kk.val / 2) + 2 * m + kk.val % 2))))
    (htbl1 : ∀ kk : Usize, kk.val < 16 → ∃ z zq : Vec128,
        backend.neon.ntt.inv1 SECOND kk = ok (z, zq) ∧ PsiOk z zq (q : ℤ) Zb ∧
        ∀ m < 8, laneZ q z m * Rinv
          = -(ζ (255 - (32 * (kk.val / 4) + 4 * m + kk.val % 4))))
    (hAin : 0 ≤ Ain) (hC0 : 0 ≤ C0) (hAr : 0 ≤ Ar) (hC2 : 0 ≤ C2) (hC4 : 0 ≤ C4)
    (hreset : ((q : ℤ) - 1) / 2 ≤ Ar)
    (g0 : GSLevel (q : ℤ) Zb Ain T0 C0) (g1 : GSLevel (q : ℤ) Zb C0 T1 C1) (hCB01 : C0 ≤ C1)
    (g2 : GSLevel (q : ℤ) Zb Ar T2 C2) (g3 : GSLevel (q : ℤ) Zb C2 T3 C3)
    (g4 : GSLevel (q : ℤ) Zb Ar T4 C4) (g5 : GSLevel (q : ℤ) Zb C4 T5 C5)
    (iter : core.ops.range.Range Usize) (hend : iter.«end».val = 4)
    (hb : ∀ p < 256, 64 * iter.start.val ≤ p → |(b.val[p]!).val| ≤ Ain)
    (hva : ∀ c < 256, posZ q b c =
        if c < 64 * iter.start.val then invT q ζ a0 c else a0 c) :
    backend.neon.ntt.invntt_block_loop0 SECOND iter b qv bm round
      ⦃ (r : Array I16 256#usize) =>
          (∀ p < 256, if 64 * iter.start.val ≤ p then
              |(r.val[p]!).val| ≤ ((q : ℤ) - 1) / 2
            else (r.val[p]!).val = (b.val[p]!).val) ∧
          (∀ c < 256, posZ q r c = invT q ζ a0 c) ⦄ := by
  unfold backend.neon.ntt.invntt_block_loop0
  by_cases hlt : iter.start.val < iter.«end».val
  · let* ⟨ o, iter1, ho, hstart', hend' ⟩ ← core.iter.range.IteratorRange.next_Usize_some_spec
    rw [ho]
    simp only
    have hgi : iter.start.val < 4 := by omega
    set g := iter.start with hg_def
    apply WP.spec_bind (load_group_spec b g hgi)
    intro v hvload
    have hvb : ∀ k (hk : k < 8), VecBnd (vAt v k hk) Ain := by
      intro k hk m hm
      rw [hvload k hk m hm]
      exact hb _ (by omega) (by omega)
    have hvZ : ∀ k (hk : k < 8), ∀ m < 8,
        laneZ q (vAt v k hk) m = a0 (64 * g.val + 8 * m + k) := by
      intro k hk m hm
      unfold laneZ
      rw [hvload k hk m hm]
      have := hva (64 * g.val + 8 * m + k) (by omega)
      rw [if_neg (by omega)] at this
      exact this
    -- `len = 1`
    apply WP.spec_bind (WP.spec_both
      (invntt_len1_bnd SECOND qv (q : ℤ) Zb Ain T0 C0 hQ hQpos (by omega) hZb
        hAin g0.bz g0.bt g0.fit g0.c1 g0.c2 (fun kk hkk => by
          obtain ⟨z, zq, he, hp, -⟩ := htbl1 kk hkk
          exact ⟨z, zq, he, hp.1, hp.2⟩)
        g hgi v ⟨0#usize, 4#usize⟩ rfl (fun j hj _ => hvb j hj))
      (invntt_len1_val SECOND qv q Zb Ain T0 Rinv
        (fun kk m => -(ζ (255 - (32 * (kk / 4) + 4 * m + kk % 4)))) hR hQ hQpos (by omega) hZb
        hAin g0.bz g0.bt g0.fit (fun kk hkk => by
          obtain ⟨z, zq, he, hp, hv⟩ := htbl1 kk hkk
          exact ⟨z, zq, he, hp.1, hp.2, hv⟩)
        g hgi v ⟨0#usize, 4#usize⟩ rfl (fun j hj _ => hvb j hj)))
    rintro v0 ⟨hv0, hv0v⟩
    have hv0b : ∀ j (hj : j < 8), VecBnd (vAt v0 j hj) C0 := by
      intro j hj
      have := hv0 j hj
      rw [if_pos (by unfold pend1; scalar_tac)] at this
      exact this
    have hv0Z : ∀ k (hk : k < 8), ∀ m < 8,
        laneZ q (vAt v0 k hk) m = gsLvl q ζ 128 1 a0 (64 * g.val + 8 * m + k) := by
      intro k hk m hm
      have h := hv0v k hk m hm
      rw [if_pos (show 2 * ((⟨0#usize, 4#usize⟩ : core.ops.range.Range Usize)).start.val ≤ k
        from by scalar_tac)] at h
      rw [gsLvl_group1 q ζ a0 g.val m k hm hk]
      have hpsi : -(ζ (255 - (32 * ((4 * g.val + k / 2) / 4) + 4 * m + (4 * g.val + k / 2) % 4)))
          = -(ζ (255 - (32 * g.val + 4 * m + k / 2))) := by
        rw [show (4 * g.val + k / 2) / 4 = g.val from by omega,
          show (4 * g.val + k / 2) % 4 = k / 2 from by omega]
      by_cases hpar : k % 2 = 0
      · rw [if_pos hpar] at h
        rw [h, if_pos hpar, hvZ (2 * (k / 2)) (by omega) m hm,
          hvZ (2 * (k / 2) + 1) (by omega) m hm,
          show 64 * g.val + 8 * m + 2 * (k / 2) = 64 * g.val + 8 * m + k from by omega,
          show 64 * g.val + 8 * m + (2 * (k / 2) + 1)
            = 64 * g.val + 8 * m + k + 1 from by omega]
      · rw [if_neg hpar] at h
        rw [h, if_neg hpar, hpsi, hvZ (2 * (k / 2)) (by omega) m hm,
          hvZ (2 * (k / 2) + 1) (by omega) m hm,
          show 64 * g.val + 8 * m + 2 * (k / 2) = 64 * g.val + 8 * m + k - 1 from by omega,
          show 64 * g.val + 8 * m + (2 * (k / 2) + 1) = 64 * g.val + 8 * m + k from by omega]
    -- `len = 2`
    apply WP.spec_bind (WP.spec_both
      (invntt_len2_outer_bnd SECOND qv (q : ℤ) Zb C0 T1 C1 hQ hQpos (by omega) hZb
        hC0 g1.bz g1.bt g1.fit g1.c1 g1.c2 hCB01 (fun kk hkk => by
          obtain ⟨z, zq, he, hp, -⟩ := htbl2 kk hkk
          exact ⟨z, zq, he, hp.1, hp.2⟩)
        g hgi v0 ⟨0#usize, 2#usize⟩ rfl (fun j hj _ => hv0b j hj))
      (invntt_len2_outer_val SECOND qv q Zb C0 T1 C1 Rinv
        (fun kk m => -(ζ (127 - (16 * (kk / 2) + 2 * m + kk % 2)))) hR hQ hQpos (by omega) hZb
        hC0 g1.bz g1.bt g1.fit g1.c1 g1.c2 (fun kk hkk => by
          obtain ⟨z, zq, he, hp, hv⟩ := htbl2 kk hkk
          exact ⟨z, zq, he, hp.1, hp.2, hv⟩)
        g hgi v0 ⟨0#usize, 2#usize⟩ rfl (fun j hj _ => hv0b j hj)))
    rintro v1 ⟨hv1, hv1v⟩
    have hv1b : ∀ j (hj : j < 8), VecBnd (vAt v1 j hj) C1 := by
      intro j hj
      have := hv1 j hj
      rw [if_pos (by scalar_tac)] at this
      exact this
    have hv1Z : ∀ k (hk : k < 8), ∀ m < 8, laneZ q (vAt v1 k hk) m
        = gsLvl q ζ 64 2 (gsLvl q ζ 128 1 a0) (64 * g.val + 8 * m + k) := by
      intro k hk m hm
      have h := hv1v k hk m hm
      rw [if_pos (show 4 * ((⟨0#usize, 2#usize⟩ : core.ops.range.Range Usize)).start.val ≤ k
        from by scalar_tac)] at h
      rw [gsLvl_group2 q ζ (gsLvl q ζ 128 1 a0) g.val m k hm hk]
      have hpsi : -(ζ (127 - (16 * ((2 * g.val + k / 4) / 2) + 2 * m + (2 * g.val + k / 4) % 2)))
          = -(ζ (127 - (16 * g.val + 2 * m + k / 4))) := by
        rw [show (2 * g.val + k / 4) / 2 = g.val from by omega,
          show (2 * g.val + k / 4) % 2 = k / 4 from by omega]
      by_cases hk2 : k % 4 < 2
      · rw [if_pos hk2] at h
        rw [h, if_pos hk2, hv0Z (4 * (k / 4) + k % 2) (by omega) m hm,
          hv0Z (4 * (k / 4) + k % 2 + 2) (by omega) m hm,
          show 64 * g.val + 8 * m + (4 * (k / 4) + k % 2) = 64 * g.val + 8 * m + k from by omega,
          show 64 * g.val + 8 * m + (4 * (k / 4) + k % 2 + 2)
            = 64 * g.val + 8 * m + k + 2 from by omega]
      · rw [if_neg hk2] at h
        rw [h, if_neg hk2, hpsi, hv0Z (4 * (k / 4) + k % 2) (by omega) m hm,
          hv0Z (4 * (k / 4) + k % 2 + 2) (by omega) m hm,
          show 64 * g.val + 8 * m + (4 * (k / 4) + k % 2)
            = 64 * g.val + 8 * m + k - 2 from by omega,
          show 64 * g.val + 8 * m + (4 * (k / 4) + k % 2 + 2)
            = 64 * g.val + 8 * m + k from by omega]
    -- the slice round trip and the re-centring pass
    let* ⟨ s, to_back, hs_val, hto_back ⟩ ← Array.to_slice_mut_spec
    let* ⟨ iter2, imb, hi2_slice, hi2_zero, hi2_back ⟩ ← iter_mut_spec
    have hs_len : s.val.length = 8 := by rw [hs_val]; have := v1.property; scalar_tac
    have hi2_len : iter2.slice.val.length = 8 := by rw [hi2_slice]; exact hs_len
    have hi2Z : ∀ (j : ℕ) (hj : j < iter2.slice.val.length), ∀ m < 8,
        laneZ q (sAt iter2.slice j hj) m
          = gsLvl q ζ 64 2 (gsLvl q ζ 128 1 a0) (64 * g.val + 8 * m + j) := by
      intro j hj m hm
      have hjv : j < 8 := by omega
      have heq : sAt iter2.slice j hj = vAt v1 j hjv := by
        unfold sAt vAt
        exact List.getElem_of_eq (by rw [hi2_slice, hs_val]) _
      rw [heq]
      exact hv1Z j hjv m hm
    apply WP.spec_bind (WP.spec_both
      (invntt_barrett_iter_bnd iter2 (fun im1 => im1) bm round qv (q : ℤ) M hQ hM hRnd
        hQpos hQ14 hQodd hMpos hMlt hD hi2_len (by rw [hi2_zero]; omega)
        (fun im him => him)
        (fun im him j hj hbnd => absurd hj (by rw [hi2_zero]; omega))
        (fun im him j _ hbnd hbnd' => rfl))
      (invntt_barrett_iter_val iter2 (fun im1 => im1) bm round qv q M
        (fun j m => gsLvl q ζ 64 2 (gsLvl q ζ 128 1 a0) (64 * g.val + 8 * m + j)) hQ hM hRnd
        hQpos hQ14 hQodd hMpos hMlt hD hi2_len (by rw [hi2_zero]; omega) hi2Z
        (fun im him => him)
        (fun im him j hj hbnd m hm => absurd hj (by rw [hi2_zero]; omega))
        (fun im him j _ hbnd hbnd' => rfl)))
    rintro ⟨im, bk⟩ ⟨⟨him_len, hbk⟩, hbkv⟩
    obtain ⟨hbk_len, hbk_bnd⟩ := hbk im him_len
    obtain ⟨z4, zq4, hz4e, ⟨hz4, hzq4⟩, hz4v⟩ := htbl4 g hgi
    apply WP.spec_bind (show backend.neon.ntt.inv4 SECOND g
        ⦃ (p : Vec128 × Vec128) => p.1 = z4 ∧ p.2 = zq4 ⦄ from by
      rw [hz4e]; exact (WP.spec_ok _).mpr ⟨rfl, rfl⟩)
    rintro ⟨z, zq⟩ ⟨rfl, rfl⟩
    set a := to_back (imb (bk im)) with ha_def
    have ha_val : a.val = (bk im).slice.val := by
      rw [ha_def, hi2_back, hto_back]
      exact Std.Array.from_slice_val _ _ (by rw [hbk_len]; simp)
    have haeq : ∀ j (hj : j < 8), ∃ hjb : j < (bk im).slice.val.length,
        vAt a j hj = sAt (bk im).slice j hjb := by
      intro j hj
      refine ⟨by rw [hbk_len]; omega, ?_⟩
      unfold vAt sAt
      exact List.getElem_of_eq ha_val _
    have hab : ∀ j (hj : j < 8), VecBnd (vAt a j hj) Ar := by
      intro j hj
      obtain ⟨hjb, heq⟩ := haeq j hj
      rw [heq]
      exact (hbk_bnd j hjb).mono hreset
    have haZ : ∀ j (hj : j < 8), ∀ m < 8, laneZ q (vAt a j hj) m
        = gsLvl q ζ 64 2 (gsLvl q ζ 128 1 a0) (64 * g.val + 8 * m + j) := by
      intro j hj m hm
      obtain ⟨hjb, heq⟩ := haeq j hj
      rw [heq]
      exact hbkv im him_len j hjb m hm
    -- level 2, `len = 4`
    apply WP.spec_bind (WP.spec_both
      (invntt_len4_bnd qv z zq (q : ℤ) Zb Ar T2 C2 hQ hQpos (by omega) hz4 hZb hzq4
        hAr g2.bz g2.bt g2.fit g2.c1 g2.c2 a ⟨0#usize, 4#usize⟩ rfl (fun j hj _ => hab j hj))
      (invntt_len4_val qv z zq q Zb Ar T2 Rinv (fun m => -(ζ (63 - (8 * g.val + m)))) hR
        (fun m hm => hz4v m hm) hQ hQpos (by omega) hz4 hZb hzq4 hAr g2.bz g2.bt g2.fit
        a ⟨0#usize, 4#usize⟩ rfl (fun j hj _ => hab j hj)))
    rintro v3 ⟨hv3, hv3v⟩
    have hv3b : ∀ j (hj : j < 8), VecBnd (vAt v3 j hj) C2 := by
      intro j hj
      have := hv3 j hj
      rw [if_pos (by unfold pend4; scalar_tac)] at this
      exact this
    have hv3Z : ∀ k (hk : k < 8), ∀ m < 8, laneZ q (vAt v3 k hk) m
        = gsLvl q ζ 32 4 (gsLvl q ζ 64 2 (gsLvl q ζ 128 1 a0)) (64 * g.val + 8 * m + k) := by
      intro k hk m hm
      have h := hv3v k hk m hm
      rw [gsLvl_group4 q ζ (gsLvl q ζ 64 2 (gsLvl q ζ 128 1 a0)) g.val m k hm hk]
      by_cases hk4 : k < 4
      · rw [if_pos (show ((⟨0#usize, 4#usize⟩ : core.ops.range.Range Usize)).start.val ≤ k
              ∧ k < 4 from ⟨by scalar_tac, hk4⟩)] at h
        rw [h, if_pos hk4, haZ (k % 4) (by omega) m hm, haZ (k % 4 + 4) (by omega) m hm,
          show 64 * g.val + 8 * m + k % 4 = 64 * g.val + 8 * m + k from by omega,
          show 64 * g.val + 8 * m + (k % 4 + 4) = 64 * g.val + 8 * m + k + 4 from by omega]
      · rw [if_neg (show ¬ (((⟨0#usize, 4#usize⟩ : core.ops.range.Range Usize)).start.val ≤ k
              ∧ k < 4) from by scalar_tac),
          if_pos (show 4 + ((⟨0#usize, 4#usize⟩ : core.ops.range.Range Usize)).start.val ≤ k
              ∧ k < 8 from ⟨by scalar_tac, hk⟩)] at h
        rw [h, if_neg hk4, haZ (k % 4) (by omega) m hm, haZ (k % 4 + 4) (by omega) m hm,
          show 64 * g.val + 8 * m + k % 4 = 64 * g.val + 8 * m + k - 4 from by omega,
          show 64 * g.val + 8 * m + (k % 4 + 4) = 64 * g.val + 8 * m + k from by omega]
    -- back to coefficient order
    apply WP.spec_bind (WP.spec_both (transpose8_bnd v3 C2 hv3b)
      (transpose8_val v3 q (fun k m =>
        gsLvl q ζ 32 4 (gsLvl q ζ 64 2 (gsLvl q ζ 128 1 a0)) (64 * g.val + 8 * m + k)) hv3Z))
    rintro v4 ⟨hv4b, hv4Z⟩
    -- level 3
    apply WP.spec_bind (WP.spec_both
      (invntt_lvl3_bnd SECOND qv (q : ℤ) Zb C2 T3 C3 hQ hQpos (by omega) hZb
        hC2 g3.bz g3.bt g3.fit g3.c1 g3.c2 (fun kk hkk => by
          obtain ⟨zi, h1, h2, -⟩ := hzeta kk hkk
          exact ⟨zi, h1, h2⟩) qic hqinv hqinvu
        g hgi v4 ⟨0#usize, 4#usize⟩ rfl (fun j hj _ => hv4b j hj))
      (invntt_lvl3_val SECOND qv q Zb C2 T3 Rinv ζ hR hQ hQpos (by omega) hZb
        hC2 g3.bz g3.bt g3.fit hzeta qic hqinv hqinvu
        g hgi v4 ⟨0#usize, 4#usize⟩ rfl (fun j hj _ => hv4b j hj)))
    rintro v5 ⟨hv5, hv5v⟩
    have hv5b : ∀ j (hj : j < 8), VecBnd (vAt v5 j hj) C3 := by
      intro j hj
      have := hv5 j hj
      rw [if_pos (by unfold pend1; scalar_tac)] at this
      exact this
    have hv5Z : ∀ j (hj : j < 8), ∀ m < 8, laneZ q (vAt v5 j hj) m
        = gsLvl q ζ 16 8 (gsLvl q ζ 32 4 (gsLvl q ζ 64 2 (gsLvl q ζ 128 1 a0)))
            (64 * g.val + 8 * j + m) := by
      intro j hj m hm
      have h := hv5v j hj m hm
      rw [if_pos (show 2 * ((⟨0#usize, 4#usize⟩ : core.ops.range.Range Usize)).start.val ≤ j
        from by scalar_tac)] at h
      rw [gsLvl_lvl3 q ζ _ g.val j m hj hm]
      by_cases hpar : j % 2 = 0
      · rw [if_pos hpar] at h
        rw [h, if_pos hpar, hv4Z (2 * (j / 2)) (by omega) m hm,
          hv4Z (2 * (j / 2) + 1) (by omega) m hm,
          show 64 * g.val + 8 * (2 * (j / 2)) + m = 64 * g.val + 8 * j + m from by omega,
          show 64 * g.val + 8 * (2 * (j / 2) + 1) + m
            = 64 * g.val + 8 * j + m + 8 from by omega]
      · rw [if_neg hpar] at h
        rw [h, if_neg hpar, hv4Z (2 * (j / 2)) (by omega) m hm,
          hv4Z (2 * (j / 2) + 1) (by omega) m hm,
          show 64 * g.val + 8 * (2 * (j / 2)) + m = 64 * g.val + 8 * j + m - 8 from by omega,
          show 64 * g.val + 8 * (2 * (j / 2) + 1) + m
            = 64 * g.val + 8 * j + m from by omega]
    -- the second re-centring pass
    let* ⟨ s2, to_back2, hs2_val, hto_back2 ⟩ ← Array.to_slice_mut_spec
    let* ⟨ iter3, imb3, hi3_slice, hi3_zero, hi3_back ⟩ ← iter_mut_spec
    have hs2_len : s2.val.length = 8 := by rw [hs2_val]; have := v5.property; scalar_tac
    have hi3_len : iter3.slice.val.length = 8 := by rw [hi3_slice]; exact hs2_len
    have hi3Z : ∀ (j : ℕ) (hj : j < iter3.slice.val.length), ∀ m < 8,
        laneZ q (sAt iter3.slice j hj) m
          = gsLvl q ζ 16 8 (gsLvl q ζ 32 4 (gsLvl q ζ 64 2 (gsLvl q ζ 128 1 a0)))
              (64 * g.val + 8 * j + m) := by
      intro j hj m hm
      have hjv : j < 8 := by omega
      have heq : sAt iter3.slice j hj = vAt v5 j hjv := by
        unfold sAt vAt
        exact List.getElem_of_eq (by rw [hi3_slice, hs2_val]) _
      rw [heq]
      exact hv5Z j hjv m hm
    rw [invntt_loop0_loop5_eq]
    apply WP.spec_bind (WP.spec_both
      (invntt_barrett_iter_bnd iter3 (fun im1 => im1) bm round qv (q : ℤ) M hQ hM hRnd
        hQpos hQ14 hQodd hMpos hMlt hD hi3_len (by rw [hi3_zero]; omega)
        (fun im him => him)
        (fun im him j hj hbnd => absurd hj (by rw [hi3_zero]; omega))
        (fun im him j _ hbnd hbnd' => rfl))
      (invntt_barrett_iter_val iter3 (fun im1 => im1) bm round qv q M
        (fun j m => gsLvl q ζ 16 8 (gsLvl q ζ 32 4 (gsLvl q ζ 64 2 (gsLvl q ζ 128 1 a0)))
          (64 * g.val + 8 * j + m)) hQ hM hRnd
        hQpos hQ14 hQodd hMpos hMlt hD hi3_len (by rw [hi3_zero]; omega) hi3Z
        (fun im him => him)
        (fun im him j hj hbnd m hm => absurd hj (by rw [hi3_zero]; omega))
        (fun im him j _ hbnd hbnd' => rfl)))
    rintro ⟨im2, bk2⟩ ⟨⟨him2_len, hbk2⟩, hbk2v⟩
    obtain ⟨hbk2_len, hbk2_bnd⟩ := hbk2 im2 him2_len
    set a2 := to_back2 (imb3 (bk2 im2)) with ha2_def
    have ha2_val : a2.val = (bk2 im2).slice.val := by
      rw [ha2_def, hi3_back, hto_back2]
      exact Std.Array.from_slice_val _ _ (by rw [hbk2_len]; simp)
    have ha2eq : ∀ j (hj : j < 8), ∃ hjb : j < (bk2 im2).slice.val.length,
        vAt a2 j hj = sAt (bk2 im2).slice j hjb := by
      intro j hj
      refine ⟨by rw [hbk2_len]; omega, ?_⟩
      unfold vAt sAt
      exact List.getElem_of_eq ha2_val _
    have ha2b : ∀ j (hj : j < 8), VecBnd (vAt a2 j hj) Ar := by
      intro j hj
      obtain ⟨hjb, heq⟩ := ha2eq j hj
      rw [heq]
      exact (hbk2_bnd j hjb).mono hreset
    have ha2Z : ∀ j (hj : j < 8), ∀ m < 8, laneZ q (vAt a2 j hj) m
        = gsLvl q ζ 16 8 (gsLvl q ζ 32 4 (gsLvl q ζ 64 2 (gsLvl q ζ 128 1 a0)))
            (64 * g.val + 8 * j + m) := by
      intro j hj m hm
      obtain ⟨hjb, heq⟩ := ha2eq j hj
      rw [heq]
      exact hbk2v im2 him2_len j hjb m hm
    -- level 4
    apply WP.spec_bind (WP.spec_both
      (invntt_lvl4_bnd SECOND qv (q : ℤ) Zb Ar T4 C4 hQ hQpos (by omega) hZb
        hAr g4.bz g4.bt g4.fit g4.c1 g4.c2 (by have h := g4.c1; omega) (fun kk hkk => by
          obtain ⟨zi, h1, h2, -⟩ := hzeta kk hkk
          exact ⟨zi, h1, h2⟩) qic hqinv hqinvu
        g hgi a2 ⟨0#usize, 2#usize⟩ rfl (fun j hj _ => ha2b j hj))
      (invntt_lvl4_val SECOND qv q Zb Ar T4 C4 Rinv ζ hR hQ hQpos (by omega) hZb
        hAr g4.bz g4.bt g4.fit g4.c1 g4.c2 hzeta qic hqinv hqinvu
        g hgi a2 ⟨0#usize, 2#usize⟩ rfl (fun j hj _ => ha2b j hj)))
    rintro v6 ⟨hv6, hv6v⟩
    have hv6b : ∀ j (hj : j < 8), VecBnd (vAt v6 j hj) C4 := by
      intro j hj
      have := hv6 j hj
      rw [if_pos (by scalar_tac)] at this
      exact this
    have hv6Z : ∀ j (hj : j < 8), ∀ m < 8, laneZ q (vAt v6 j hj) m
        = gsLvl q ζ 8 16 (gsLvl q ζ 16 8 (gsLvl q ζ 32 4
            (gsLvl q ζ 64 2 (gsLvl q ζ 128 1 a0)))) (64 * g.val + 8 * j + m) := by
      intro j hj m hm
      have h := hv6v j hj m hm
      rw [if_pos (show 4 * ((⟨0#usize, 2#usize⟩ : core.ops.range.Range Usize)).start.val ≤ j
        from by scalar_tac)] at h
      rw [gsLvl_lvl4 q ζ _ g.val j m hj hm]
      by_cases hj2 : j % 4 < 2
      · rw [if_pos hj2] at h
        rw [h, if_pos hj2, ha2Z (4 * (j / 4) + j % 2) (by omega) m hm,
          ha2Z (4 * (j / 4) + j % 2 + 2) (by omega) m hm,
          show 64 * g.val + 8 * (4 * (j / 4) + j % 2) + m
            = 64 * g.val + 8 * j + m from by omega,
          show 64 * g.val + 8 * (4 * (j / 4) + j % 2 + 2) + m
            = 64 * g.val + 8 * j + m + 16 from by omega]
      · rw [if_neg hj2] at h
        rw [h, if_neg hj2, ha2Z (4 * (j / 4) + j % 2) (by omega) m hm,
          ha2Z (4 * (j / 4) + j % 2 + 2) (by omega) m hm,
          show 64 * g.val + 8 * (4 * (j / 4) + j % 2) + m
            = 64 * g.val + 8 * j + m - 16 from by omega,
          show 64 * g.val + 8 * (4 * (j / 4) + j % 2 + 2) + m
            = 64 * g.val + 8 * j + m from by omega]
    -- level 5
    let* ⟨ i7, hi7 ⟩ ← Std.Usize.sub_spec (x := 7#usize) (y := g) (by scalar_tac)
    obtain ⟨zi7, hzie7, hzib7, hzv7⟩ := hzeta i7 (by scalar_tac)
    obtain ⟨z5, zq5, hnz5, hz5b, hzq5b, hz5v⟩ :=
      neg_zeta_val SECOND q Zb Rinv ζ i7 zi7 hzie7 hzib7 hzv7 hZb qic hqinv hqinvu
    rw [hnz5, bind_tc_ok, invntt_loop0_loop7_eq]
    apply WP.spec_bind (WP.spec_both
      (invntt_len4_bnd qv z5 zq5 (q : ℤ) Zb C4 T5 C5 hQ hQpos (by omega) hz5b hZb hzq5b
        hC4 g5.bz g5.bt g5.fit g5.c1 g5.c2 v6 ⟨0#usize, 4#usize⟩ rfl (fun j hj _ => hv6b j hj))
      (invntt_len4_val qv z5 zq5 q Zb C4 T5 Rinv (fun _ => -(ζ i7.val)) hR
        (fun m hm => hz5v m hm) hQ hQpos (by omega) hz5b hZb hzq5b hC4 g5.bz g5.bt g5.fit
        v6 ⟨0#usize, 4#usize⟩ rfl (fun j hj _ => hv6b j hj)))
    rintro v7 ⟨hv7, hv7v⟩
    have hv7b : ∀ j (hj : j < 8), VecBnd (vAt v7 j hj) C5 := by
      intro j hj
      have := hv7 j hj
      rw [if_pos (by unfold pend4; scalar_tac)] at this
      exact this
    have hv7Z : ∀ j (hj : j < 8), ∀ m < 8,
        laneZ q (vAt v7 j hj) m = invT q ζ a0 (64 * g.val + 8 * j + m) := by
      intro j hj m hm
      have h := hv7v j hj m hm
      unfold invT
      rw [gsLvl_lvl5 q ζ _ g.val j m hj hm,
        show 7 - g.val = i7.val from by scalar_tac]
      by_cases hj4 : j < 4
      · rw [if_pos (show ((⟨0#usize, 4#usize⟩ : core.ops.range.Range Usize)).start.val ≤ j
              ∧ j < 4 from ⟨by scalar_tac, hj4⟩)] at h
        rw [h, if_pos hj4, hv6Z (j % 4) (by omega) m hm, hv6Z (j % 4 + 4) (by omega) m hm,
          show 64 * g.val + 8 * (j % 4) + m = 64 * g.val + 8 * j + m from by omega,
          show 64 * g.val + 8 * (j % 4 + 4) + m
            = 64 * g.val + 8 * j + m + 32 from by omega]
      · rw [if_neg (show ¬ (((⟨0#usize, 4#usize⟩ : core.ops.range.Range Usize)).start.val ≤ j
              ∧ j < 4) from by scalar_tac),
          if_pos (show 4 + ((⟨0#usize, 4#usize⟩ : core.ops.range.Range Usize)).start.val ≤ j
              ∧ j < 8 from ⟨by scalar_tac, hj⟩)] at h
        rw [h, if_neg hj4, hv6Z (j % 4) (by omega) m hm, hv6Z (j % 4 + 4) (by omega) m hm,
          show 64 * g.val + 8 * (j % 4) + m = 64 * g.val + 8 * j + m - 32 from by omega,
          show 64 * g.val + 8 * (j % 4 + 4) + m = 64 * g.val + 8 * j + m from by omega]
    -- the third re-centring pass
    let* ⟨ s3, to_back3, hs3_val, hto_back3 ⟩ ← Array.to_slice_mut_spec
    let* ⟨ iter4, imb4, hi4_slice, hi4_zero, hi4_back ⟩ ← iter_mut_spec
    have hs3_len : s3.val.length = 8 := by rw [hs3_val]; have := v7.property; scalar_tac
    have hi4_len : iter4.slice.val.length = 8 := by rw [hi4_slice]; exact hs3_len
    have hi4Z : ∀ (j : ℕ) (hj : j < iter4.slice.val.length), ∀ m < 8,
        laneZ q (sAt iter4.slice j hj) m = invT q ζ a0 (64 * g.val + 8 * j + m) := by
      intro j hj m hm
      have hjv : j < 8 := by omega
      have heq : sAt iter4.slice j hj = vAt v7 j hjv := by
        unfold sAt vAt
        exact List.getElem_of_eq (by rw [hi4_slice, hs3_val]) _
      rw [heq]
      exact hv7Z j hjv m hm
    rw [invntt_loop0_loop8_eq]
    apply WP.spec_bind (WP.spec_both
      (invntt_barrett_iter_bnd iter4 (fun im1 => im1) bm round qv (q : ℤ) M hQ hM hRnd
        hQpos hQ14 hQodd hMpos hMlt hD hi4_len (by rw [hi4_zero]; omega)
        (fun im him => him)
        (fun im him j hj hbnd => absurd hj (by rw [hi4_zero]; omega))
        (fun im him j _ hbnd hbnd' => rfl))
      (invntt_barrett_iter_val iter4 (fun im1 => im1) bm round qv q M
        (fun j m => invT q ζ a0 (64 * g.val + 8 * j + m)) hQ hM hRnd
        hQpos hQ14 hQodd hMpos hMlt hD hi4_len (by rw [hi4_zero]; omega) hi4Z
        (fun im him => him)
        (fun im him j hj hbnd m hm => absurd hj (by rw [hi4_zero]; omega))
        (fun im him j _ hbnd hbnd' => rfl)))
    rintro ⟨im3, bk3⟩ ⟨⟨him3_len, hbk3⟩, hbk3v⟩
    obtain ⟨hbk3_len, hbk3_bnd⟩ := hbk3 im3 him3_len
    -- the eight stores
    let* ⟨ i8, hi8 ⟩ ← Std.Usize.mul_spec (x := 8#usize) (y := g) (by scalar_tac)
    have hi8v : i8.val = 8 * g.val := by scalar_tac
    set a3 := to_back3 (imb4 (bk3 im3)) with ha3_def
    have ha3_val : a3.val = (bk3 im3).slice.val := by
      rw [ha3_def, hi4_back, hto_back3]
      exact Std.Array.from_slice_val _ _ (by rw [hbk3_len]; simp)
    have ha3eq : ∀ j (hj : j < 8), ∃ hjb : j < (bk3 im3).slice.val.length,
        vAt a3 j hj = sAt (bk3 im3).slice j hjb := by
      intro j hj
      refine ⟨by rw [hbk3_len]; omega, ?_⟩
      unfold vAt sAt
      exact List.getElem_of_eq ha3_val _
    have ha3b : ∀ j (hj : j < 8), VecBnd (vAt a3 j hj) (((q : ℤ) - 1) / 2) := by
      intro j hj
      obtain ⟨hjb, heq⟩ := ha3eq j hj
      rw [heq]
      exact hbk3_bnd j hjb
    have ha3Z : ∀ j (hj : j < 8), ∀ m < 8,
        laneZ q (vAt a3 j hj) m = invT q ζ a0 (64 * g.val + 8 * j + m) := by
      intro j hj m hm
      obtain ⟨hjb, heq⟩ := ha3eq j hj
      rw [heq]
      exact hbk3v im3 him3_len j hjb m hm
    have hstore : ∀ (ju : Usize) (hju : ju.val < 8) (bb : Array I16 256#usize) (idx : Usize)
        (hidx : idx.val = 8 * g.val + ju.val),
        ∃ bb', store_i16 bb idx (vAt a3 ju.val hju) = ok bb' ∧ ∀ p < 256,
          (bb'.val[p]!).val =
            if 8 * idx.val ≤ p ∧ p < 8 * idx.val + 8 then
              (lane16 (vAt a3 ju.val hju) (p - 8 * idx.val)).toInt
            else (bb.val[p]!).val := fun ju hju bb idx hidx =>
      store_i16_val bb idx (vAt a3 ju.val hju) (by omega)
    have hv0e : ∀ (j : Usize) (hj : j.val < 8),
        Array.index_usize a3 j = ok (vAt a3 j.val hj) := by
      intro j hj
      obtain ⟨w, hw⟩ := WP.spec_imp_exists (Array.index_usize_spec a3 j (by scalar_tac))
      rw [hw.1]
      congr 1
      rw [hw.2]
      rfl
    rw [hv0e 0#usize (by decide), bind_tc_ok]
    obtain ⟨b1, hb1e, hb1v⟩ := hstore 0#usize (by decide) b i8 (by scalar_tac)
    rw [hb1e, bind_tc_ok]
    let* ⟨ j1, hj1 ⟩ ← Std.Usize.add_spec (x := i8) (y := 1#usize) (by scalar_tac)
    rw [hv0e 1#usize (by decide), bind_tc_ok]
    obtain ⟨b2, hb2e, hb2v⟩ := hstore 1#usize (by decide) b1 j1 (by scalar_tac)
    rw [hb2e, bind_tc_ok]
    let* ⟨ j2, hj2 ⟩ ← Std.Usize.add_spec (x := i8) (y := 2#usize) (by scalar_tac)
    rw [hv0e 2#usize (by decide), bind_tc_ok]
    obtain ⟨b3, hb3e, hb3v⟩ := hstore 2#usize (by decide) b2 j2 (by scalar_tac)
    rw [hb3e, bind_tc_ok]
    let* ⟨ j3, hj3 ⟩ ← Std.Usize.add_spec (x := i8) (y := 3#usize) (by scalar_tac)
    rw [hv0e 3#usize (by decide), bind_tc_ok]
    obtain ⟨b4, hb4e, hb4v⟩ := hstore 3#usize (by decide) b3 j3 (by scalar_tac)
    rw [hb4e, bind_tc_ok]
    let* ⟨ j4, hj4 ⟩ ← Std.Usize.add_spec (x := i8) (y := 4#usize) (by scalar_tac)
    rw [hv0e 4#usize (by decide), bind_tc_ok]
    obtain ⟨b5, hb5e, hb5v⟩ := hstore 4#usize (by decide) b4 j4 (by scalar_tac)
    rw [hb5e, bind_tc_ok]
    let* ⟨ j5, hj5 ⟩ ← Std.Usize.add_spec (x := i8) (y := 5#usize) (by scalar_tac)
    rw [hv0e 5#usize (by decide), bind_tc_ok]
    obtain ⟨b6, hb6e, hb6v⟩ := hstore 5#usize (by decide) b5 j5 (by scalar_tac)
    rw [hb6e, bind_tc_ok]
    let* ⟨ j6, hj6 ⟩ ← Std.Usize.add_spec (x := i8) (y := 6#usize) (by scalar_tac)
    rw [hv0e 6#usize (by decide), bind_tc_ok]
    obtain ⟨b7, hb7e, hb7v⟩ := hstore 6#usize (by decide) b6 j6 (by scalar_tac)
    rw [hb7e, bind_tc_ok]
    let* ⟨ j7, hj7 ⟩ ← Std.Usize.add_spec (x := i8) (y := 7#usize) (by scalar_tac)
    rw [hv0e 7#usize (by decide), bind_tc_ok]
    obtain ⟨b8, hb8e, hb8v⟩ := hstore 7#usize (by decide) b7 j7 (by scalar_tac)
    rw [hb8e, bind_tc_ok]
    have hb8lane : ∀ p < 256, ∀ (hd : (p - 64 * g.val) / 8 < 8),
        64 * g.val ≤ p → p < 64 * g.val + 64 →
        (b8.val[p]!).val
          = (lane16 (vAt a3 ((p - 64 * g.val) / 8) hd) ((p - 64 * g.val) % 8)).toInt := by
      intro p hp hd hlo hhi
      have e8 := hb8v p hp
      have e7 := hb7v p hp
      have e6 := hb6v p hp
      have e5 := hb5v p hp
      have e4 := hb4v p hp
      have e3 := hb3v p hp
      have e2 := hb2v p hp
      have e1 := hb1v p hp
      rcases show (p - 64 * g.val) / 8 = 0 ∨ (p - 64 * g.val) / 8 = 1 ∨ (p - 64 * g.val) / 8 = 2
          ∨ (p - 64 * g.val) / 8 = 3 ∨ (p - 64 * g.val) / 8 = 4 ∨ (p - 64 * g.val) / 8 = 5
          ∨ (p - 64 * g.val) / 8 = 6 ∨ (p - 64 * g.val) / 8 = 7 from by omega with
        h | h | h | h | h | h | h | h <;>
      simp only [h] <;>
      [ (rw [e8, if_neg (by omega), e7, if_neg (by omega), e6, if_neg (by omega),
          e5, if_neg (by omega), e4, if_neg (by omega), e3, if_neg (by omega),
          e2, if_neg (by omega), e1, if_pos (by omega)]);
        (rw [e8, if_neg (by omega), e7, if_neg (by omega), e6, if_neg (by omega),
          e5, if_neg (by omega), e4, if_neg (by omega), e3, if_neg (by omega),
          e2, if_pos (by omega)]);
        (rw [e8, if_neg (by omega), e7, if_neg (by omega), e6, if_neg (by omega),
          e5, if_neg (by omega), e4, if_neg (by omega), e3, if_pos (by omega)]);
        (rw [e8, if_neg (by omega), e7, if_neg (by omega), e6, if_neg (by omega),
          e5, if_neg (by omega), e4, if_pos (by omega)]);
        (rw [e8, if_neg (by omega), e7, if_neg (by omega), e6, if_neg (by omega),
          e5, if_pos (by omega)]);
        (rw [e8, if_neg (by omega), e7, if_neg (by omega), e6, if_pos (by omega)]);
        (rw [e8, if_neg (by omega), e7, if_pos (by omega)]);
        (rw [e8, if_pos (by omega)]) ] <;>
      congr 2 <;> omega
    have hb8rest : ∀ p < 256, ¬ (64 * g.val ≤ p ∧ p < 64 * g.val + 64) →
        (b8.val[p]!).val = (b.val[p]!).val := by
      intro p hp hout
      rw [hb8v p hp, if_neg (by omega), hb7v p hp, if_neg (by omega), hb6v p hp,
        if_neg (by omega), hb5v p hp, if_neg (by omega), hb4v p hp, if_neg (by omega),
        hb3v p hp, if_neg (by omega), hb2v p hp, if_neg (by omega), hb1v p hp,
        if_neg (by omega)]
    have hb8Z : ∀ c < 256, posZ q b8 c =
        if c < 64 * g.val + 64 then invT q ζ a0 c else a0 c := by
      intro c hc
      unfold posZ
      by_cases hin : 64 * g.val ≤ c ∧ c < 64 * g.val + 64
      · rw [hb8lane c hc (by omega) hin.1 hin.2, if_pos (by omega)]
        have := ha3Z ((c - 64 * g.val) / 8) (by omega) ((c - 64 * g.val) % 8) (by omega)
        unfold laneZ at this
        rw [this, show 64 * g.val + 8 * ((c - 64 * g.val) / 8) + (c - 64 * g.val) % 8 = c
          from by omega]
      · rw [hb8rest c hc hin]
        have := hva c hc
        unfold posZ at this
        rw [this]
        by_cases hbelow : c < 64 * g.val
        · rw [if_pos hbelow, if_pos (by omega)]
        · rw [if_neg hbelow, if_neg (by omega)]
    -- and the remaining groups
    apply WP.spec_mono (invntt_group_val SECOND b8 qv bm round q Zb M Ain T0 C0 T1 C1 Ar
      T2 C2 T3 C3 T4 C4 T5 C5 Rinv ζ a0 hR hQ hQpos hQ14 hQodd hZb hM hMpos hMlt hD hRnd
      hzeta qic hqinv hqinvu htbl4 htbl2 htbl1 hAin hC0 hAr hC2 hC4 hreset g0 g1 hCB01 g2 g3
      g4 g5 iter1 (by rw [hend']; exact hend) (by
        intro p hp hge
        rw [hb8rest p hp (by omega)]
        exact hb p hp (by omega))
      (by
        intro c hc
        rw [hb8Z c hc]
        by_cases hbelow : c < 64 * g.val + 64
        · rw [if_pos hbelow, if_pos (by omega)]
        · rw [if_neg hbelow, if_neg (by omega)]))
    rintro r ⟨hr1, hr2⟩
    refine ⟨fun p hp => ?_, hr2⟩
    have hrp := hr1 p hp
    by_cases hge : 64 * g.val ≤ p
    · rw [if_pos hge]
      by_cases hge1 : 64 * iter1.start.val ≤ p
      · rw [if_pos hge1] at hrp
        exact hrp
      · rw [if_neg hge1] at hrp
        rw [hrp, hb8lane p hp (by omega) (by omega) (by omega)]
        exact ha3b _ (by omega) _ (by omega)
    · rw [if_neg hge]
      rw [if_neg (by omega)] at hrp
      rw [hrp, hb8rest p hp (by omega)]
  · let* ⟨ o, iter1, hnone, _ ⟩ ← core.iter.range.IteratorRange.next_Usize_none_spec
    rw [hnone]
    have hs4' : 4 ≤ iter.start.val := by scalar_tac
    refine (WP.spec_ok _).mpr ⟨fun p hp => ?_, fun c hc => ?_⟩
    · rw [if_neg (by omega)]
    · rw [hva c hc, if_pos (by omega)]
termination_by 4 - iter.start.val
decreasing_by scalar_decr_tac

/-! ## The final scaling

One `mont_mul` by a broadcast constant per vector.  In residues that is multiplication of the
whole block by `scale · R⁻¹` — the factor that undoes both the `1/256` the inverse transform
leaves behind and the Montgomery factor the pointwise step introduced. -/

theorem invntt_scale_val (b : Array I16 256#usize) (qv scale scaleq : Vec128) (q : ℕ)
    (Zb B Bt : ℤ) (Rinv sc : ZMod q) (hR : ((2 ^ 16 : ℤ) : ZMod q) * Rinv = 1)
    (hsc : ∀ m < 8, laneZ q scale m * Rinv = sc)
    (hQ : ∀ i < 8, (lane16 qv i).toInt = (q : ℤ)) (hQpos : 0 < (q : ℤ)) (hQlt : (q : ℤ) ≤ 2 ^ 14)
    (hz : ∀ i < 8, |(lane16 scale i).toInt| ≤ Zb) (hZb : Zb ≤ 2 ^ 14)
    (hzq : ∀ i < 8, (2 ^ 16 : ℤ) ∣ ((lane16 scaleq i).toInt * (q : ℤ) - (lane16 scale i).toInt))
    (hB0 : 0 ≤ B) (hBZ : B * Zb < 2 ^ 15 * (q : ℤ))
    (hBt : B * Zb + 2 ^ 15 * (q : ℤ) ≤ 2 ^ 16 * Bt)
    (iter : core.ops.range.Range Usize) (hend : iter.«end».val = 32)
    (hb : ∀ p < 256, 8 * iter.start.val ≤ p → |(b.val[p]!).val| ≤ B) :
    backend.neon.ntt.invntt_block_loop2 iter b qv scale scaleq
      ⦃ (r : Array I16 256#usize) => ∀ p < 256,
          if 8 * iter.start.val ≤ p then posZ q r p = sc * posZ q b p
          else posZ q r p = posZ q b p ⦄ := by
  unfold backend.neon.ntt.invntt_block_loop2
  by_cases hlt : iter.start.val < iter.«end».val
  · let* ⟨ o, iter1, ho, hstart', hend' ⟩ ← core.iter.range.IteratorRange.next_Usize_some_spec
    rw [ho]
    simp only
    have hi32 : iter.start.val < 32 := by omega
    obtain ⟨vec, hvec, hvecl⟩ := load_i16_val b iter.start hi32
    rw [hvec, bind_tc_ok]
    have hvb : VecBnd vec B := by
      intro k hk
      rw [hvecl k hk]
      exact hb _ (by omega) (by omega)
    have hvZ : ∀ m < 8, laneZ q vec m = posZ q b (8 * iter.start.val + m) := by
      intro m hm; unfold laneZ posZ; rw [hvecl m hm]
    apply WP.spec_bind (mont_mul_bnd vec scale scaleq qv (q : ℤ) Zb B Bt hQ hQpos hQlt hz hZb hzq
      hvb hB0 hBZ hBt)
    rintro v1 ⟨hv1b, hv1d⟩
    have hv1Z : ∀ m < 8, laneZ q v1 m = sc * posZ q b (8 * iter.start.val + m) := by
      intro m hm
      have h := mont_resZ q Rinv hR _ _ _ (hv1d m hm)
      rw [show laneZ q v1 m = (((lane16 v1 m).toInt : ℤ) : ZMod q) from rfl, h,
        show (((lane16 scale m).toInt : ℤ) : ZMod q) = laneZ q scale m from rfl,
        show (((lane16 vec m).toInt : ℤ) : ZMod q) = laneZ q vec m from rfl,
        hsc m hm, hvZ m hm]
    obtain ⟨b1, hb1, hb1v⟩ := store_i16_val b iter.start v1 hi32
    rw [hb1, bind_tc_ok]
    have hb1Z : ∀ p < 256, posZ q b1 p =
        if 8 * iter.start.val ≤ p ∧ p < 8 * iter.start.val + 8 then sc * posZ q b p
        else posZ q b p := by
      intro p hp
      have h := hb1v p hp
      unfold posZ
      rw [h]
      by_cases hin : 8 * iter.start.val ≤ p ∧ p < 8 * iter.start.val + 8
      · rw [if_pos hin, if_pos hin]
        have := hv1Z (p - 8 * iter.start.val) (by omega)
        unfold laneZ at this
        rw [this, show 8 * iter.start.val + (p - 8 * iter.start.val) = p from by omega]
        rfl
      · rw [if_neg hin, if_neg hin]
    apply WP.spec_mono (invntt_scale_val b1 qv scale scaleq q Zb B Bt Rinv sc hR hsc hQ hQpos
      hQlt hz hZb hzq hB0 hBZ hBt iter1 (by rw [hend']; exact hend) (by
        intro p hp hge
        rw [hb1v p hp, if_neg (by scalar_tac)]
        exact hb p hp (by omega)))
    intro r hr p hp
    have hrp := hr p hp
    by_cases hge : 8 * iter.start.val ≤ p
    · rw [if_pos hge]
      by_cases hge1 : 8 * iter1.start.val ≤ p
      · rw [if_pos hge1] at hrp
        rw [hrp, hb1Z p hp, if_neg (by omega)]
      · rw [if_neg hge1] at hrp
        rw [hrp, hb1Z p hp, if_pos (by omega)]
    · rw [if_neg hge]
      rw [if_neg (by omega)] at hrp
      rw [hrp, hb1Z p hp, if_neg (by omega)]
  · let* ⟨ o, iter1, hnone, _ ⟩ ← core.iter.range.IteratorRange.next_Usize_none_spec
    rw [hnone]
    refine (WP.spec_ok _).mpr (fun p hp => ?_)
    rw [if_neg (by scalar_tac)]
termination_by 32 - iter.start.val
decreasing_by scalar_decr_tac

/-! ## The inverse transform

The constant setup, the four transposed groups, the five whole-vector levels and the scaling —
the same composition `invntt_block_bnd` makes, with the value chain riding along. -/

/-- The eight inverse layers, before the final scaling. -/
noncomputable def invAllRaw (q : ℕ) (ζ a0 : ℕ → ZMod q) : ℕ → ZMod q := invH q ζ (invT q ζ a0)

theorem invntt_block_val (SECOND : Bool) (b : Array I16 256#usize)
    (q : ℕ) (Zb M Ain T0 C0 T1 C1 Ar Tlo Clo Thi Chi Bt : ℤ) (Rinv : ZMod q)
    (ζ a0 : ℕ → ZMod q)
    (qc mc rc sc qic : I16)
    (hR : ((2 ^ 16 : ℤ) : ZMod q) * Rinv = 1)
    (hq : backend.crt.q SECOND = ok qc) (hqv : qc.val = (q : ℤ))
    (hm : backend.crt.barrett_m SECOND = ok mc) (hmv : mc.val = M)
    (hrc : (1#i16 : I16) <<< (10#i32 : Std.I32) = ok rc) (hrcv : rc.val = 2 ^ 10)
    (hsc : backend.crt.invntt_scale SECOND = ok sc) (hscb : |sc.val| ≤ Zb)
    (hqi : backend.crt.qinv SECOND = ok qic) (hqiu : (2 ^ 16 : ℤ) ∣ (qic.val * (q : ℤ) - 1))
    (hQpos : 0 < (q : ℤ)) (hQ14 : (q : ℤ) < 2 ^ 14) (hQodd : ¬ (2 ∣ (q : ℤ)))
    (hZb : Zb ≤ 2 ^ 14)
    (hMpos : 0 < M) (hMlt : M < 2 ^ 15) (hD : |2 ^ 27 - (q : ℤ) * M| ≤ 2047)
    (hzeta : ∀ kk : Usize, kk.val < 256 → ∃ zi : I16,
        backend.crt.zeta SECOND kk = ok zi ∧ |zi.val| ≤ Zb ∧
        ((zi.val : ℤ) : ZMod q) * Rinv = ζ kk.val)
    (htbl4 : ∀ kk : Usize, kk.val < 4 → ∃ z zq : Vec128,
        backend.neon.ntt.inv4 SECOND kk = ok (z, zq) ∧ PsiOk z zq (q : ℤ) Zb ∧
        ∀ m < 8, laneZ q z m * Rinv = -(ζ (63 - (8 * kk.val + m))))
    (htbl2 : ∀ kk : Usize, kk.val < 8 → ∃ z zq : Vec128,
        backend.neon.ntt.inv2 SECOND kk = ok (z, zq) ∧ PsiOk z zq (q : ℤ) Zb ∧
        ∀ m < 8, laneZ q z m * Rinv
          = -(ζ (127 - (16 * (kk.val / 2) + 2 * m + kk.val % 2))))
    (htbl1 : ∀ kk : Usize, kk.val < 16 → ∃ z zq : Vec128,
        backend.neon.ntt.inv1 SECOND kk = ok (z, zq) ∧ PsiOk z zq (q : ℤ) Zb ∧
        ∀ m < 8, laneZ q z m * Rinv
          = -(ζ (255 - (32 * (kk.val / 4) + 4 * m + kk.val % 4))))
    (hAinz : 0 ≤ Ain) (hC0z : 0 ≤ C0)
    (hArz : 0 ≤ Ar) (hCloz : 0 ≤ Clo) (hreset : ((q : ℤ) - 1) / 2 ≤ Ar)
    (g0 : GSLevel (q : ℤ) Zb Ain T0 C0) (g1 : GSLevel (q : ℤ) Zb C0 T1 C1) (hCB01 : C0 ≤ C1)
    (glo : GSLevel (q : ℤ) Zb Ar Tlo Clo) (ghi : GSLevel (q : ℤ) Zb Clo Thi Chi)
    (hCB : Clo ≤ Chi)
    (hBZ : Chi * Zb < 2 ^ 15 * (q : ℤ)) (hBt : Chi * Zb + 2 ^ 15 * (q : ℤ) ≤ 2 ^ 16 * Bt)
    (hb : BlockBnd b Ain) (hf : ∀ c < 256, posZ q b c = a0 c) :
    backend.neon.ntt.invntt_block SECOND b
      ⦃ (r : Array I16 256#usize) => ∀ c < 256,
          posZ q r c = (((sc.val : ℤ) : ZMod q) * Rinv) * invAllRaw q ζ a0 c ⦄ := by
  unfold backend.neon.ntt.invntt_block
  rw [hq, bind_tc_ok]
  obtain ⟨qv, hqe, hql⟩ := dup_n_s16_spec qc
  rw [hqe, bind_tc_ok, hm, bind_tc_ok]
  obtain ⟨bm, hbme, hbml⟩ := dup_n_s16_spec mc
  rw [hbme, bind_tc_ok]
  have hsh : backend.crt.BARRETT_SH - (1#i32 : Std.I32) = ok (10#i32 : Std.I32) := by
    simp only [backend.crt.BARRETT_SH]
    rfl
  rw [hsh, bind_tc_ok, hrc, bind_tc_ok]
  obtain ⟨round, hre, hrl⟩ := dup_n_s16_spec rc
  rw [hre, bind_tc_ok]
  have hQv : ∀ i < 8, (lane16 qv i).toInt = (q : ℤ) := by
    intro i hi; rw [hql i hi]; exact hqv
  have hMv : ∀ i < 8, (lane16 bm i).toInt = M := by
    intro i hi; rw [hbml i hi]; exact hmv
  have hRv : ∀ i < 8, (lane16 round i).toInt = 2 ^ 10 := by
    intro i hi; rw [hrl i hi]; exact hrcv
  -- the four groups: levels 0 to 5
  apply WP.spec_bind (invntt_group_val SECOND b qv bm round q Zb M Ain T0 C0 T1 C1 Ar
    Tlo Clo Thi Chi Tlo Clo Thi Chi
    Rinv ζ a0 hR hQv hQpos hQ14 hQodd hZb hMv hMpos hMlt hD hRv hzeta qic hqi hqiu
    htbl4 htbl2 htbl1 hAinz hC0z hArz hCloz hCloz hreset g0 g1 hCB01 glo ghi glo ghi
    ⟨0#usize, 4#usize⟩ rfl (fun p hp _ => hb p hp)
    (by intro c hc; rw [hf c hc, if_neg (by scalar_tac)]))
  rintro b1 ⟨hb1, hb1v⟩
  have hb1' : BlockBnd b1 Ar := by
    intro p hp
    have h := hb1 p hp
    rw [if_pos (by scalar_tac)] at h
    exact le_trans h hreset
  -- levels 6 and 7, which cross groups
  apply WP.spec_bind (invntt_horizontal_val SECOND b1 qv q Zb Ar Tlo Clo Thi Chi
    Rinv ζ (invT q ζ a0) hR hQv hQpos hQ14 hZb hzeta qic hqi hqiu hArz hCloz glo ghi
    hb1' hb1v)
  rintro b2 ⟨hb2, hb2v⟩
  -- and the final scaling
  rw [hsc, bind_tc_ok]
  obtain ⟨scale, hse, hsl⟩ := dup_n_s16_spec sc
  rw [hse, bind_tc_ok, hqi, bind_tc_ok]
  simp only [lift, bind_tc_ok]
  obtain ⟨scaleq, hsqe, hsql⟩ := dup_n_s16_spec (core.num.I16.wrapping_mul sc qic)
  rw [hsqe, bind_tc_ok]
  have hvecs : backend.neon.ntt.VECS = ok 32#usize := by
    simp only [backend.neon.ntt.VECS, consts.RING_DEG]; rfl
  rw [hvecs, bind_tc_ok]
  apply WP.spec_mono (invntt_scale_val b2 qv scale scaleq q Zb Chi Bt Rinv
    (((sc.val : ℤ) : ZMod q) * Rinv) hR
    (by intro m hm; unfold laneZ; rw [hsl m hm]; rfl)
    hQv hQpos (by omega)
    (by intro i hi; rw [hsl i hi]; exact hscb) hZb
    (by
      intro i hi
      rw [hsl i hi, hsql i hi]
      have h1 : ((core.num.I16.wrapping_mul sc qic).bv).toInt = tblZq sc.val qic.val := by
        show ((sc.bv * qic.bv : BitVec 16)).toInt = _
        rw [BitVec.toInt_mul]
        rfl
      rw [h1]
      exact tblZq_mont sc.val qic.val (q : ℤ) hqiu)
    (by omega) hBZ hBt ⟨0#usize, 32#usize⟩ rfl (fun p hp _ => hb2 p hp))
  intro r hr c hc
  have h := hr c hc
  rw [if_pos (by scalar_tac)] at h
  rw [h, hb2v c hc]
  rfl

/-! ## …and the root state

Eight `State_gs` steps, one per layer, taking the CRT invariant from the leaf back to the root.
Each step doubles the constant, so the eight together multiply it by `2⁸ = 256` — which is the
factor the final scaling is there to undo. -/

open Kopis.CrtScheme.NttAlg in
theorem invAll_State {q : ℕ} (ζ : ℕ → ZMod q)
    (hsq : ∀ k, 1 ≤ k → k < 256 → ζ k ^ 2 = cst ζ k)
    (hpair : ∀ nb b : ℕ, (∃ j, j < 8 ∧ nb = 2 ^ j) → b < nb →
      ζ (nb + b) * ζ (2 * nb - 1 - b) = -1)
    {c : ZMod q} {f a : ℕ → ZMod q} (h : State ζ 256 1 c f a) :
    State ζ 1 256 (2 ^ 8 * c) f (invAllRaw q ζ a) := by
  have h1 : State ζ 128 2 (2 * c) f (gsLvl q ζ 128 1 a) :=
    State_gs hsq hpair (by norm_num) (by norm_num) ⟨7, by norm_num⟩ h
      (gsLvl_hbut q ζ 128 1 a (by norm_num))
  have h2 : State ζ 64 4 (2 * (2 * c)) f (gsLvl q ζ 64 2 (gsLvl q ζ 128 1 a)) :=
    State_gs hsq hpair (by norm_num) (by norm_num) ⟨6, by norm_num⟩ h1
      (gsLvl_hbut q ζ 64 2 _ (by norm_num))
  have h3 : State ζ 32 8 (2 * (2 * (2 * c))) f
      (gsLvl q ζ 32 4 (gsLvl q ζ 64 2 (gsLvl q ζ 128 1 a))) :=
    State_gs hsq hpair (by norm_num) (by norm_num) ⟨5, by norm_num⟩ h2
      (gsLvl_hbut q ζ 32 4 _ (by norm_num))
  have h4 : State ζ 16 16 (2 * (2 * (2 * (2 * c)))) f
      (gsLvl q ζ 16 8 (gsLvl q ζ 32 4 (gsLvl q ζ 64 2 (gsLvl q ζ 128 1 a)))) :=
    State_gs hsq hpair (by norm_num) (by norm_num) ⟨4, by norm_num⟩ h3
      (gsLvl_hbut q ζ 16 8 _ (by norm_num))
  have h5 : State ζ 8 32 (2 * (2 * (2 * (2 * (2 * c))))) f
      (gsLvl q ζ 8 16 (gsLvl q ζ 16 8 (gsLvl q ζ 32 4
        (gsLvl q ζ 64 2 (gsLvl q ζ 128 1 a))))) :=
    State_gs hsq hpair (by norm_num) (by norm_num) ⟨3, by norm_num⟩ h4
      (gsLvl_hbut q ζ 8 16 _ (by norm_num))
  have h6 : State ζ 4 64 (2 * (2 * (2 * (2 * (2 * (2 * c)))))) f (invT q ζ a) :=
    State_gs hsq hpair (by norm_num) (by norm_num) ⟨2, by norm_num⟩ h5
      (gsLvl_hbut q ζ 4 32 _ (by norm_num))
  have h7 : State ζ 2 128 (2 * (2 * (2 * (2 * (2 * (2 * (2 * c))))))) f
      (gsLvl q ζ 2 64 (invT q ζ a)) :=
    State_gs hsq hpair (by norm_num) (by norm_num) ⟨1, by norm_num⟩ h6
      (gsLvl_hbut q ζ 2 64 _ (by norm_num))
  have h8 : State ζ 1 256 (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * c)))))))) f
      (invAllRaw q ζ a) :=
    State_gs hsq hpair (by norm_num) (by norm_num) ⟨0, by norm_num⟩ h7
      (gsLvl_hbut q ζ 1 128 _ (by norm_num))
  have heq : (2 : ZMod q) ^ 8 * c = 2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * c))))))) := by ring
  rw [heq]
  exact h8

/-! ## The inverse transform at the two primes -/

open Kopis.CrtZeta in
unseal backend.crt.INVNTT_SCALE_1 in
/-- **The inverse transform on the first prime, as residues.** -/
theorem invntt_block_val_q1 (b : Array I16 256#usize) (a0 : ℕ → ZMod 7681)
    (hb : BlockBnd b 4741) (hf : ∀ c < 256, posZ 7681 b c = a0 c) :
    backend.neon.ntt.invntt_block false b
      ⦃ (r : Array I16 256#usize) => ∀ c < 256,
          posZ 7681 r c
            = (((backend.crt.INVNTT_SCALE_1.val : ℤ) : ZMod 7681) * (900 : ZMod 7681))
                * invAllRaw 7681 zeta1 a0 c ⦄ := by
  have hzo : zetasOf false = backend.crt.ZETAS_Q1 := by
    simp only [zetasOf, Bool.false_eq_true, if_false]
  have hzc : ∀ k < 256, |((zetasOf false).val[k]!).val| ≤ 3840 := by
    intro k hk
    rw [hzo]
    exact zetas_q1_centred_idx k hk
  have hinv : (2 ^ 16 : ℤ) ∣ ((qinvOf false).val * ((7681 : ℕ) : ℤ) - 1) := by
    simp only [qinvOf, Bool.false_eq_true, if_false]
    rw [show ((7681 : ℕ) : ℤ) = backend.crt.Q1.val from by rw [q1_val]; norm_num]
    exact q1_inv_unit
  have hzt : ∀ kk : Usize, kk.val < 256 → ∃ zi : I16,
      backend.crt.zeta false kk = ok zi ∧ |zi.val| ≤ 3840 ∧
      ((zi.val : ℤ) : ZMod 7681) * (900 : ZMod 7681) = zeta1 kk.val := by
    intro kk hkk
    obtain ⟨zi, _, h1, -, h3, -, h5⟩ := zeta_table_ok_q1 kk hkk
    refine ⟨zi, h1, h3, ?_⟩
    unfold zeta1 zetaQ zint
    rw [h5]
  refine invntt_block_val false b 7681 3840 17474 4741 4397 9482 4952 18964 3840 4291 7680 4741 15360 4741
    (900 : ZMod 7681) zeta1 a0 backend.crt.Q1 backend.crt.Q1_BARRETT_M 1024#i16
    backend.crt.INVNTT_SCALE_1 backend.crt.Q1_INV
    (by decide)
    (by simp only [backend.crt.q, Bool.false_eq_true, if_false]) (by rw [q1_val]; norm_num)
    (by simp only [backend.crt.barrett_m, Bool.false_eq_true, if_false]) q1_m_val
    round_const (by decide)
    (by simp only [backend.crt.invntt_scale, Bool.false_eq_true, if_false]) (by decide)
    (by simp only [backend.crt.qinv, Bool.false_eq_true, if_false])
    (by rw [show ((7681 : ℕ) : ℤ) = backend.crt.Q1.val from by rw [q1_val]; norm_num]
        exact q1_inv_unit)
    (by norm_num) (by norm_num) (by decide) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
    hzt
    (fun kk hkk => by
      obtain ⟨z, zq, he, hp, hv⟩ := psiFull_inv4 false 7681 3840 (900 : ZMod 7681) hzc hinv kk hkk
      rw [hzo] at hv
      exact ⟨z, zq, he, hp, hv⟩)
    (fun kk hkk => by
      obtain ⟨z, zq, he, hp, hv⟩ := psiFull_inv2 false 7681 3840 (900 : ZMod 7681) hzc hinv kk hkk
      rw [hzo] at hv
      exact ⟨z, zq, he, hp, hv⟩)
    (fun kk hkk => by
      obtain ⟨z, zq, he, hp, hv⟩ := psiFull_inv1 false 7681 3840 (900 : ZMod 7681) hzc hinv kk hkk
      rw [hzo] at hv
      exact ⟨z, zq, he, hp, hv⟩)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    ⟨⟨by norm_num, by norm_num, by norm_num⟩, by norm_num, by norm_num, by norm_num⟩
    ⟨⟨by norm_num, by norm_num, by norm_num⟩, by norm_num, by norm_num, by norm_num⟩
    (by norm_num)
    ⟨⟨by norm_num, by norm_num, by norm_num⟩, by norm_num, by norm_num, by norm_num⟩
    ⟨⟨by norm_num, by norm_num, by norm_num⟩, by norm_num, by norm_num, by norm_num⟩
    (by norm_num) (by norm_num) (by norm_num)
    (by simpa using hb) hf

open Kopis.CrtZeta in
unseal backend.crt.INVNTT_SCALE_2 in
/-- **The inverse transform on the second prime, as residues.** -/
theorem invntt_block_val_q2 (b : Array I16 256#usize) (a0 : ℕ → ZMod 10753)
    (hb : BlockBnd b 7141) (hf : ∀ c < 256, posZ 10753 b c = a0 c) :
    backend.neon.ntt.invntt_block true b
      ⦃ (r : Array I16 256#usize) => ∀ c < 256,
          posZ 10753 r c
            = (((backend.crt.INVNTT_SCALE_2.val : ℤ) : ZMod 10753) * (1764 : ZMod 10753))
                * invAllRaw 10753 zeta2 a0 c ⦄ := by
  have hzo : zetasOf true = backend.crt.ZETAS_Q2 := by simp only [zetasOf, if_true]
  have hzc : ∀ k < 256, |((zetasOf true).val[k]!).val| ≤ 5376 := by
    intro k hk
    rw [hzo]
    exact zetas_q2_centred_idx k hk
  have hinv : (2 ^ 16 : ℤ) ∣ ((qinvOf true).val * ((10753 : ℕ) : ℤ) - 1) := by
    simp only [qinvOf, if_true]
    rw [show ((10753 : ℕ) : ℤ) = backend.crt.Q2.val from by rw [q2_val]; norm_num]
    exact q2_inv_unit
  have hzt : ∀ kk : Usize, kk.val < 256 → ∃ zi : I16,
      backend.crt.zeta true kk = ok zi ∧ |zi.val| ≤ 5376 ∧
      ((zi.val : ℤ) : ZMod 10753) * (1764 : ZMod 10753) = zeta2 kk.val := by
    intro kk hkk
    obtain ⟨zi, _, h1, -, h3, -, h5⟩ := zeta_table_ok_q2 kk hkk
    refine ⟨zi, h1, h3, ?_⟩
    unfold zeta2 zetaQ zint
    rw [h5]
  refine invntt_block_val true b 10753 5376 12482 7141 6549 14282 7720 28564 5376 6259 10752 7141 21504 7141
    (1764 : ZMod 10753) zeta2 a0 backend.crt.Q2 backend.crt.Q2_BARRETT_M 1024#i16
    backend.crt.INVNTT_SCALE_2 backend.crt.Q2_INV
    (by decide)
    (by simp only [backend.crt.q, if_true]) (by rw [q2_val]; norm_num)
    (by simp only [backend.crt.barrett_m, if_true]) q2_m_val
    round_const (by decide)
    (by simp only [backend.crt.invntt_scale, if_true]) (by decide)
    (by simp only [backend.crt.qinv, if_true])
    (by rw [show ((10753 : ℕ) : ℤ) = backend.crt.Q2.val from by rw [q2_val]; norm_num]
        exact q2_inv_unit)
    (by norm_num) (by norm_num) (by decide) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
    hzt
    (fun kk hkk => by
      obtain ⟨z, zq, he, hp, hv⟩ :=
        psiFull_inv4 true 10753 5376 (1764 : ZMod 10753) hzc hinv kk hkk
      rw [hzo] at hv
      exact ⟨z, zq, he, hp, hv⟩)
    (fun kk hkk => by
      obtain ⟨z, zq, he, hp, hv⟩ :=
        psiFull_inv2 true 10753 5376 (1764 : ZMod 10753) hzc hinv kk hkk
      rw [hzo] at hv
      exact ⟨z, zq, he, hp, hv⟩)
    (fun kk hkk => by
      obtain ⟨z, zq, he, hp, hv⟩ :=
        psiFull_inv1 true 10753 5376 (1764 : ZMod 10753) hzc hinv kk hkk
      rw [hzo] at hv
      exact ⟨z, zq, he, hp, hv⟩)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    ⟨⟨by norm_num, by norm_num, by norm_num⟩, by norm_num, by norm_num, by norm_num⟩
    ⟨⟨by norm_num, by norm_num, by norm_num⟩, by norm_num, by norm_num, by norm_num⟩
    (by norm_num)
    ⟨⟨by norm_num, by norm_num, by norm_num⟩, by norm_num, by norm_num, by norm_num⟩
    ⟨⟨by norm_num, by norm_num, by norm_num⟩, by norm_num, by norm_num, by norm_num⟩
    (by norm_num) (by norm_num) (by norm_num)
    (by simpa using hb) hf

end Kopis.Neon
