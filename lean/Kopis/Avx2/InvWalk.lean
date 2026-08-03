/-
  # Kopis/Avx2/InvWalk.lean — phase F4, the inverse transform's code walk.

  The mirror of `Kopis/Avx2/NttWalk.lean`.  Same shape throughout: each loop is walked once,
  carrying a bound invariant and a value invariant side by side, and the value invariant names
  the layer as a function of the *view* (`tposZ` before the second transpose, `posZ` after).

  Two things differ from the forward side and drive everything here.

  * **Growth.** Gentleman-Sande sends `(lo, hi)` to `(lo + hi, ψ·(lo − hi))`.  The sum path
    *doubles* — it does not stay inside the input bound the way Cooley-Tukey's does — so a level
    takes a common input bound `A` to `2A` on one output and `T` on the other.  `Split`'s
    `A + T` shape does not fit that, hence `SplitB` below with an explicit processed bound.
  * **Sign.** `State_gs` applies `−ζ(2nb−1−b)`, and the `INV*` tables are built with `neg` set,
    so the code's `z` at the paired index already *is* `−ζ`.  The negation is written into
    `gsLvl` and nothing has to insert it at the butterfly.
-/
import Kopis.Avx2.NttWalk

open Aeneas Aeneas.Std Result
open RustKopisAvx2
open backend.avx2.intrinsics

namespace Kopis.Avx2

set_option maxHeartbeats 2000000

/-! ## The split invariant, with an explicit processed bound

`Split` charges a processed vector `A + T`, which is what Cooley-Tukey produces.  Gentleman-Sande
produces `2A` on the sum side and `T` on the product side, so the processed bound is `max (2A) T`
and neither summand is the right name for it. -/

/-- Vectors satisfying `P` are inside `B`; the rest are still inside `A`. -/
def SplitB (b : Array I16 256#usize) (P : ℕ → Prop) (A B : ℤ) : Prop :=
  (∀ v < 16, P v → BlockBndAt b v B) ∧ (∀ v < 16, ¬ P v → BlockBndAt b v A)

/-- The `len = 1` inverse level: eight butterflies pairing `2h` with `2h + 1`.

In transposed coordinates a butterfly on vectors `(2h, 2h+1)` pairs coefficients `c` and `c + 1`
with `c` even, so this is `gsLvl` at `m' = 1` and `nb = 128`.  The ζ index the table hands back
is `255 − h − 8k`, and `c / 2 = 8k + h`, so it is `2·128 − 1 − c/2` — exactly the index
`gsLvl` asks for. -/
theorem invntt_block_loop0_walk (SECOND : Bool) (iter : core.ops.range.Range Usize)
    (b : Array I16 256#usize) (qv : Vec256) (q : ℕ) (Zb A T B : ℤ) (Rinv : ZMod q)
    (ζ : ℕ → ZMod q) (a0 : ℕ → ZMod q)
    (hq0 : 0 < (q : ℤ)) (hqlt : (q : ℤ) ≤ 2 ^ 15)
    (hR : ((2 ^ 16 : ℤ) : ZMod q) * Rinv = 1)
    (hQ : ∀ i < 16, (lane16 qv i).toInt = (q : ℤ))
    (hA0 : 0 ≤ A) (hZ0 : 0 ≤ Zb) (hsum : 2 * A ≤ 2 ^ 15 - 1)
    (hAZ : 2 * A * Zb < 2 ^ 15 * (q : ℤ))
    (hT : 2 * A * Zb + 2 ^ 15 * (q : ℤ) ≤ 2 ^ 16 * T)
    (hB1 : 2 * A ≤ B) (hB2 : T ≤ B)
    (htbl : ∀ h : Usize, h.val < 8 → ∃ z zq,
      (if SECOND then (do let t ← backend.avx2.ntt.INV1_Q2; backend.avx2.ntt.ld_tbl t h)
       else (do let t ← backend.avx2.ntt.INV1_Q1; backend.avx2.ntt.ld_tbl t h))
        = ok (z, zq) ∧ PsiOk z zq (q : ℤ) Zb ∧
        ∀ k < 16, laneZ q z k * Rinv = -(ζ (255 - h.val - 8 * k)))
    (hend : iter.«end».val = 8)
    (hbnd : SplitB b (fun v => v < 2 * iter.start.val) A B)
    (hval : ∀ c < 256, tposZ q b c =
      if c % 16 < 2 * iter.start.val then gsLvl q ζ 128 1 a0 c else a0 c) :
    backend.avx2.ntt.invntt_block_loop0 SECOND iter b qv
      ⦃ (r : Array I16 256#usize) =>
          BlockBnd r B ∧ ∀ c < 256, tposZ q r c = gsLvl q ζ 128 1 a0 c ⦄ := by
  unfold backend.avx2.ntt.invntt_block_loop0
  by_cases hlt : iter.start.val < iter.«end».val
  · let* ⟨ o, iter1, ho, hstart', hend' ⟩ ← core.iter.range.IteratorRange.next_Usize_some_spec
    rw [ho]; simp only
    obtain ⟨z, zq, htz, ⟨hzb, hzqm⟩, hζ⟩ := htbl iter.start (by omega)
    rw [htz, bind_tc_ok]
    show (do let i ← 2#usize * iter.start
             let lo ← load_i16 b i
             let i1 ← i + 1#usize
             let hi ← load_i16 b i1
             let (lo1, hi1) ← backend.avx2.ntt.gs_butterfly lo hi z zq qv
             let b1 ← store_i16 b i lo1
             let i2 ← i + 1#usize
             let b2 ← store_i16 b1 i2 hi1
             backend.avx2.ntt.invntt_block_loop0 SECOND iter1 b2 qv)
        ⦃ (r : Array I16 256#usize) =>
            BlockBnd r B ∧ ∀ c < 256, tposZ q r c = gsLvl q ζ 128 1 a0 c ⦄
    obtain ⟨hgrown, hplain⟩ := hbnd
    step*
    obtain ⟨lo, hlo, hlob⟩ := load_i16_bndAt b i (by omega) (hplain i.val (by omega) (by omega))
    obtain ⟨lo', hlo', hlov⟩ := load_posZ q b i (by omega)
    rw [show lo = lo' from by rw [hlo] at hlo'; injection hlo'] at hlob
    rw [hlo', bind_tc_ok]
    step*
    obtain ⟨hiv, hhiv, hhivb⟩ := load_i16_bndAt b i1 (by omega)
      (hplain i1.val (by omega) (by omega))
    obtain ⟨hiv', hhiv', hhivv⟩ := load_posZ q b i1 (by omega)
    rw [show hiv = hiv' from by rw [hhiv] at hhiv'; injection hhiv'] at hhivb
    rw [hhiv', bind_tc_ok]
    apply WP.spec_bind (spec_and
      (gs_butterfly_bnd lo' hiv' z zq qv (q : ℤ) Zb A T hQ hq0 hqlt hzqm hlob hhivb hzb hA0 hZ0
        hsum hAZ hT)
      (gs_butterfly_val lo' hiv' z zq qv q Zb A T Rinv hq0 hqlt hR hQ hzqm hlob hhivb hzb hA0
        hZ0 hsum hAZ))
    intro r hr
    obtain ⟨lo1, hi1'⟩ := r
    obtain ⟨⟨hr1, hr2⟩, hrv⟩ := hr
    simp only at hr1 hr2 hrv
    show (do let b1 ← store_i16 b i lo1
             let i2 ← i + 1#usize
             let b2 ← store_i16 b1 i2 hi1'
             backend.avx2.ntt.invntt_block_loop0 SECOND iter1 b2 qv)
        ⦃ (r : Array I16 256#usize) =>
            BlockBnd r B ∧ ∀ c < 256, tposZ q r c = gsLvl q ζ 128 1 a0 c ⦄
    obtain ⟨b1, hb1, hb1at, hb1oth⟩ := store_i16_at b i lo1 (by omega)
    obtain ⟨b1', hb1', hb1v⟩ := store_posZ q b i lo1 (by omega)
    rw [show b1 = b1' from by rw [hb1] at hb1'; injection hb1'] at hb1at hb1oth
    rw [hb1', bind_tc_ok]
    step*
    obtain ⟨b2, hb2, hb2at, hb2oth⟩ := store_i16_at b1' i2 hi1' (by omega)
    obtain ⟨b2', hb2', hb2v⟩ := store_posZ q b1' i2 hi1' (by omega)
    rw [show b2 = b2' from by rw [hb2] at hb2'; injection hb2'] at hb2at hb2oth
    rw [hb2', bind_tc_ok]
    apply invntt_block_loop0_walk SECOND iter1 b2' qv q Zb A T B Rinv ζ a0 hq0 hqlt hR hQ hA0 hZ0
      hsum hAZ hT hB1 hB2 htbl (by rw [hend']; exact hend)
    · constructor
      · intro v hv hP
        rcases (show v = i.val ∨ v = i2.val ∨ (v ≠ i.val ∧ v ≠ i2.val) from by omega)
          with rfl | rfl | ⟨hne1, hne2⟩
        · intro k hk
          rw [hb2oth i.val (by omega) (by omega) k hk, hb1at k hk]
          exact le_trans (hr1 k hk) hB1
        · intro k hk
          rw [hb2at k hk]
          exact le_trans (hr2 k hk) hB2
        · intro k hk
          rw [hb2oth v hv hne2 k hk, hb1oth v hv hne1 k hk]
          exact hgrown v hv (by omega) k hk
      · intro v hv hP k hk
        rw [hb2oth v hv (by omega) k hk, hb1oth v hv (by omega) k hk]
        exact hplain v hv (by omega) k hk
    · intro c hc
      have hc16 : c / 16 < 16 := by omega
      have hcm : c % 16 < 16 := by omega
      have hp : 16 * (c % 16) + c / 16 < 256 := by omega
      rw [tposZ, hb2v _ hp, hb1v _ hp]
      by_cases h1 : c % 16 = i2.val
      · rw [if_pos (by omega), if_pos (by omega),
          show 16 * (c % 16) + c / 16 - 16 * i2.val = c / 16 from by omega,
          (hrv (c / 16) hc16).2, hlov (c / 16) hc16, hhivv (c / 16) hc16]
        have e1 : posZ q b (16 * i.val + c / 16) = a0 (c - 1) := by
          rw [show 16 * i.val + c / 16 = 16 * ((c - 1) % 16) + (c - 1) / 16 from by omega,
            ← tposZ, hval (c - 1) (by omega), if_neg (by omega)]
        have e2 : posZ q b (16 * i1.val + c / 16) = a0 c := by
          rw [show 16 * i1.val + c / 16 = 16 * (c % 16) + c / 16 from by omega, ← tposZ,
            hval c hc, if_neg (by omega)]
        rw [e1, e2, gsLvl, if_neg (by omega), hζ (c / 16) hc16,
          show 255 - iter.start.val - 8 * (c / 16) = 2 * 128 - 1 - c / (2 * 1) from by omega]
      · rw [if_neg (by omega)]
        by_cases h2 : c % 16 = i.val
        · rw [if_pos (by omega), if_pos (by omega),
            show 16 * (c % 16) + c / 16 - 16 * i.val = c / 16 from by omega,
            (hrv (c / 16) hc16).1, hlov (c / 16) hc16, hhivv (c / 16) hc16]
          have e1 : posZ q b (16 * i.val + c / 16) = a0 c := by
            rw [show 16 * i.val + c / 16 = 16 * (c % 16) + c / 16 from by omega, ← tposZ,
              hval c hc, if_neg (by omega)]
          have e2 : posZ q b (16 * i1.val + c / 16) = a0 (c + 1) := by
            rw [show 16 * i1.val + c / 16 = 16 * ((c + 1) % 16) + (c + 1) / 16 from by omega,
              ← tposZ, hval (c + 1) (by omega), if_neg (by omega)]
          rw [e1, e2, gsLvl, if_pos (by omega)]
        · rw [if_neg (by omega), ← tposZ, hval c hc]
          by_cases hP : c % 16 < 2 * iter.start.val
          · rw [if_pos hP, if_pos (by omega)]
          · rw [if_neg hP, if_neg (by omega)]
  · let* ⟨ o, iter1, hnone, _ ⟩ ← core.iter.range.IteratorRange.next_Usize_none_spec
    rw [hnone]; simp only [WP.spec_ok]
    refine ⟨?_, ?_⟩
    · rw [blockBnd_iff]
      intro v hv
      exact hbnd.1 v hv (by omega)
    · intro c hc
      rw [hval c hc, if_pos (by omega)]
termination_by iter.«end».val - iter.start.val
decreasing_by scalar_decr_tac

/-- The `len = 2` inverse level, one group: `2` butterflies pairing `4·h + j` with
`4·h + j + 2`.

The ζ index the table hands back is `127 − h − 4·k`, and `c / (2·2) = 4·k + h`,
so it is `2·64 − 1 − c/(2·2)` — the index `gsLvl` asks for.  Note the ζ stride and the pair
offset are different numbers: the table walks `4` per lane while the butterfly pairs at
distance `2`. -/
theorem invntt_block_loop1_loop0_walk (SECOND : Bool) (iter : core.ops.range.Range Usize)
    (b : Array I16 256#usize) (qv : Vec256) (h : Usize) (q : ℕ) (Zb A T B : ℤ) (Rinv : ZMod q)
    (ζ : ℕ → ZMod q) (a0 : ℕ → ZMod q)
    (hq0 : 0 < (q : ℤ)) (hqlt : (q : ℤ) ≤ 2 ^ 15)
    (hR : ((2 ^ 16 : ℤ) : ZMod q) * Rinv = 1)
    (hQ : ∀ i < 16, (lane16 qv i).toInt = (q : ℤ))
    (hA0 : 0 ≤ A) (hZ0 : 0 ≤ Zb) (hsum : 2 * A ≤ 2 ^ 15 - 1)
    (hAZ : 2 * A * Zb < 2 ^ 15 * (q : ℤ))
    (hT : 2 * A * Zb + 2 ^ 15 * (q : ℤ) ≤ 2 ^ 16 * T)
    (hB1 : 2 * A ≤ B) (hB2 : T ≤ B)
    (hh : h.val < 4)
    (htbl : ∃ z zq,
      (if SECOND then (do let t ← backend.avx2.ntt.INV2_Q2; backend.avx2.ntt.ld_tbl t h)
       else (do let t ← backend.avx2.ntt.INV2_Q1; backend.avx2.ntt.ld_tbl t h))
        = ok (z, zq) ∧ PsiOk z zq (q : ℤ) Zb ∧
        ∀ k < 16, laneZ q z k * Rinv = -(ζ (127 - h.val - 4 * k)))
    (hend : iter.«end».val = 2) (hstartle : iter.start.val ≤ 2)
    (hbnd : SplitB b (fun v => v < 4 * h.val
        ∨ (4 * h.val ≤ v ∧ v < 4 * h.val + iter.start.val)
        ∨ (4 * h.val + 2 ≤ v ∧ v < 4 * h.val + 2 + iter.start.val)) A B)
    (hval : ∀ c < 256, tposZ q b c =
      if c % 16 < 4 * h.val
        ∨ (4 * h.val ≤ c % 16 ∧ c % 16 < 4 * h.val + iter.start.val)
        ∨ (4 * h.val + 2 ≤ c % 16 ∧ c % 16 < 4 * h.val + 2 + iter.start.val)
      then gsLvl q ζ 64 2 a0 c else a0 c) :
    backend.avx2.ntt.invntt_block_loop1_loop0 SECOND iter b qv h
      ⦃ (r : Array I16 256#usize) =>
          SplitB r (fun v => v < 4 * h.val + 4) A B ∧
          ∀ c < 256, tposZ q r c =
            if c % 16 < 4 * h.val + 4 then gsLvl q ζ 64 2 a0 c else a0 c ⦄ := by
  unfold backend.avx2.ntt.invntt_block_loop1_loop0
  obtain ⟨z, zq, htz, ⟨hzb, hzqm⟩, hζ⟩ := htbl
  by_cases hlt : iter.start.val < iter.«end».val
  · let* ⟨ o, iter1, ho, hstart', hend' ⟩ ← core.iter.range.IteratorRange.next_Usize_some_spec
    rw [ho]; simp only
    rw [htz, bind_tc_ok]
    show (do let i ← 4#usize * h
             let i1 ← i + iter.start
             let lo ← load_i16 b i1
             let i2 ← i + iter.start
             let i3 ← i2 + 2#usize
             let hi ← load_i16 b i3
             let (lo1, hi1) ← backend.avx2.ntt.gs_butterfly lo hi z zq qv
             let i4 ← i + iter.start
             let b1 ← store_i16 b i4 lo1
             let i5 ← i + iter.start
             let i6 ← i5 + 2#usize
             let b2 ← store_i16 b1 i6 hi1
             backend.avx2.ntt.invntt_block_loop1_loop0 SECOND iter1 b2 qv h)
        ⦃ (r : Array I16 256#usize) =>
            SplitB r (fun v => v < 4 * h.val + 4) A B ∧
            ∀ c < 256, tposZ q r c =
              if c % 16 < 4 * h.val + 4 then gsLvl q ζ 64 2 a0 c else a0 c ⦄
    obtain ⟨hgrown, hplain⟩ := hbnd
    step*
    obtain ⟨lo, hlo, hlob⟩ := load_i16_bndAt b i1 (by omega)
      (hplain i1.val (by omega) (by omega))
    obtain ⟨lo', hlo', hlov⟩ := load_posZ q b i1 (by omega)
    rw [show lo = lo' from by rw [hlo] at hlo'; injection hlo'] at hlob
    rw [hlo', bind_tc_ok]
    step*
    obtain ⟨hiv, hhiv, hhivb⟩ := load_i16_bndAt b i3 (by omega)
      (hplain i3.val (by omega) (by omega))
    obtain ⟨hiv', hhiv', hhivv⟩ := load_posZ q b i3 (by omega)
    rw [show hiv = hiv' from by rw [hhiv] at hhiv'; injection hhiv'] at hhivb
    rw [hhiv', bind_tc_ok]
    apply WP.spec_bind (spec_and
      (gs_butterfly_bnd lo' hiv' z zq qv (q : ℤ) Zb A T hQ hq0 hqlt hzqm hlob hhivb hzb hA0 hZ0
        hsum hAZ hT)
      (gs_butterfly_val lo' hiv' z zq qv q Zb A T Rinv hq0 hqlt hR hQ hzqm hlob hhivb hzb hA0
        hZ0 hsum hAZ))
    intro r hr
    obtain ⟨lo1, hi1'⟩ := r
    obtain ⟨⟨hr1, hr2⟩, hrv⟩ := hr
    simp only at hr1 hr2 hrv
    show (do let i4 ← i + iter.start
             let b1 ← store_i16 b i4 lo1
             let i5 ← i + iter.start
             let i6 ← i5 + 2#usize
             let b2 ← store_i16 b1 i6 hi1'
             backend.avx2.ntt.invntt_block_loop1_loop0 SECOND iter1 b2 qv h)
        ⦃ (r : Array I16 256#usize) =>
            SplitB r (fun v => v < 4 * h.val + 4) A B ∧
            ∀ c < 256, tposZ q r c =
              if c % 16 < 4 * h.val + 4 then gsLvl q ζ 64 2 a0 c else a0 c ⦄
    step*
    obtain ⟨b1, hb1, hb1at, hb1oth⟩ := store_i16_at b i4 lo1 (by omega)
    obtain ⟨b1', hb1', hb1v⟩ := store_posZ q b i4 lo1 (by omega)
    rw [show b1 = b1' from by rw [hb1] at hb1'; injection hb1'] at hb1at hb1oth
    rw [hb1', bind_tc_ok]
    step*
    obtain ⟨b2, hb2, hb2at, hb2oth⟩ := store_i16_at b1' i6 hi1' (by omega)
    obtain ⟨b2', hb2', hb2v⟩ := store_posZ q b1' i6 hi1' (by omega)
    rw [show b2 = b2' from by rw [hb2] at hb2'; injection hb2'] at hb2at hb2oth
    rw [hb2', bind_tc_ok]
    apply invntt_block_loop1_loop0_walk SECOND iter1 b2' qv h q Zb A T B Rinv ζ a0 hq0 hqlt hR
      hQ hA0 hZ0 hsum hAZ hT hB1 hB2 hh ⟨z, zq, htz, ⟨hzb, hzqm⟩, hζ⟩ (by rw [hend']; exact hend)
      (by omega)
    · constructor
      · intro v hv hP
        rcases (show v = i4.val ∨ v = i6.val ∨ (v ≠ i4.val ∧ v ≠ i6.val) from by omega)
          with rfl | rfl | ⟨hne1, hne2⟩
        · intro k hk
          rw [hb2oth i4.val (by omega) (by omega) k hk, hb1at k hk]
          exact le_trans (hr1 k hk) hB1
        · intro k hk
          rw [hb2at k hk]
          exact le_trans (hr2 k hk) hB2
        · intro k hk
          rw [hb2oth v hv hne2 k hk, hb1oth v hv hne1 k hk]
          exact hgrown v hv (by omega) k hk
      · intro v hv hP k hk
        rw [hb2oth v hv (by omega) k hk, hb1oth v hv (by omega) k hk]
        exact hplain v hv (by omega) k hk
    · intro c hc
      have hc16 : c / 16 < 16 := by omega
      have hcm : c % 16 < 16 := by omega
      have hp : 16 * (c % 16) + c / 16 < 256 := by omega
      rw [tposZ, hb2v _ hp, hb1v _ hp]
      by_cases h1 : c % 16 = i6.val
      · rw [if_pos (by omega), if_pos (by omega),
          show 16 * (c % 16) + c / 16 - 16 * i6.val = c / 16 from by omega,
          (hrv (c / 16) hc16).2, hlov (c / 16) hc16, hhivv (c / 16) hc16]
        have hmL : (c - 2) % 16 = c % 16 - 2 := by omega
        have hdL : (c - 2) / 16 = c / 16 := by omega
        have e1 : posZ q b (16 * i1.val + c / 16) = a0 (c - 2) := by
          rw [show 16 * i1.val + c / 16 = 16 * ((c - 2) % 16) + (c - 2) / 16 from by
              rw [hmL, hdL]; omega,
            ← tposZ, hval (c - 2) (by omega), if_neg (by omega)]
        have e2 : posZ q b (16 * i3.val + c / 16) = a0 c := by
          rw [show 16 * i3.val + c / 16 = 16 * (c % 16) + c / 16 from by omega, ← tposZ,
            hval c hc, if_neg (by omega)]
        rw [e1, e2, gsLvl, if_neg (by omega), hζ (c / 16) hc16,
          show 127 - h.val - 4 * (c / 16) = 2 * 64 - 1 - c / (2 * 2) from by omega]
      · rw [if_neg (by omega)]
        by_cases h2 : c % 16 = i4.val
        · rw [if_pos (by omega), if_pos (by omega),
            show 16 * (c % 16) + c / 16 - 16 * i4.val = c / 16 from by omega,
            (hrv (c / 16) hc16).1, hlov (c / 16) hc16, hhivv (c / 16) hc16]
          have e1 : posZ q b (16 * i1.val + c / 16) = a0 c := by
            rw [show 16 * i1.val + c / 16 = 16 * (c % 16) + c / 16 from by omega, ← tposZ,
              hval c hc, if_neg (by omega)]
          have e2 : posZ q b (16 * i3.val + c / 16) = a0 (c + 2) := by
            rw [show 16 * i3.val + c / 16
              = 16 * ((c + 2) % 16) + (c + 2) / 16 from by omega,
              ← tposZ, hval (c + 2) (by omega), if_neg (by omega)]
          rw [e1, e2, gsLvl, if_pos (by omega)]
        · rw [if_neg (by omega), ← tposZ, hval c hc]
          by_cases hP : c % 16 < 4 * h.val
              ∨ (4 * h.val ≤ c % 16 ∧ c % 16 < 4 * h.val + iter.start.val)
              ∨ (4 * h.val + 2 ≤ c % 16 ∧ c % 16 < 4 * h.val + 2 + iter.start.val)
          · rw [if_pos hP, if_pos (by omega)]
          · rw [if_neg hP, if_neg (by omega)]
  · let* ⟨ o, iter1, hnone, _ ⟩ ← core.iter.range.IteratorRange.next_Usize_none_spec
    rw [hnone]; simp only [WP.spec_ok]
    obtain ⟨hgrown, hplain⟩ := hbnd
    refine ⟨⟨fun v hv hP => hgrown v hv ?_, fun v hv hP => hplain v hv ?_⟩, fun c hc => ?_⟩
    · have hP' : v < 4 * h.val + 4 := hP
      show v < 4 * h.val ∨ (4 * h.val ≤ v ∧ v < 4 * h.val + iter.start.val)
        ∨ (4 * h.val + 2 ≤ v ∧ v < 4 * h.val + 2 + iter.start.val)
      omega
    · have hP' : ¬ (v < 4 * h.val + 4) := hP
      show ¬ (v < 4 * h.val ∨ (4 * h.val ≤ v ∧ v < 4 * h.val + iter.start.val)
        ∨ (4 * h.val + 2 ≤ v ∧ v < 4 * h.val + 2 + iter.start.val))
      omega
    · rw [hval c hc]
      by_cases hP : c % 16 < 4 * h.val + 4
      · rw [if_pos hP, if_pos (by omega)]
      · rw [if_neg hP, if_neg (by omega)]
termination_by iter.«end».val - iter.start.val
decreasing_by scalar_decr_tac

/-- The `len = 2` inverse level: 4 groups. -/
theorem invntt_block_loop1_walk (SECOND : Bool) (iter : core.ops.range.Range Usize)
    (b : Array I16 256#usize) (qv : Vec256) (q : ℕ) (Zb A T B : ℤ) (Rinv : ZMod q)
    (ζ : ℕ → ZMod q) (a0 : ℕ → ZMod q)
    (hq0 : 0 < (q : ℤ)) (hqlt : (q : ℤ) ≤ 2 ^ 15)
    (hR : ((2 ^ 16 : ℤ) : ZMod q) * Rinv = 1)
    (hQ : ∀ i < 16, (lane16 qv i).toInt = (q : ℤ))
    (hA0 : 0 ≤ A) (hZ0 : 0 ≤ Zb) (hsum : 2 * A ≤ 2 ^ 15 - 1)
    (hAZ : 2 * A * Zb < 2 ^ 15 * (q : ℤ))
    (hT : 2 * A * Zb + 2 ^ 15 * (q : ℤ) ≤ 2 ^ 16 * T)
    (hB1 : 2 * A ≤ B) (hB2 : T ≤ B)
    (htbl : ∀ h : Usize, h.val < 4 → ∃ z zq,
      (if SECOND then (do let t ← backend.avx2.ntt.INV2_Q2; backend.avx2.ntt.ld_tbl t h)
       else (do let t ← backend.avx2.ntt.INV2_Q1; backend.avx2.ntt.ld_tbl t h))
        = ok (z, zq) ∧ PsiOk z zq (q : ℤ) Zb ∧
        ∀ k < 16, laneZ q z k * Rinv = -(ζ (127 - h.val - 4 * k)))
    (hend : iter.«end».val = 4) (hstartle : iter.start.val ≤ 4)
    (hbnd : SplitB b (fun v => v < 4 * iter.start.val) A B)
    (hval : ∀ c < 256, tposZ q b c =
      if c % 16 < 4 * iter.start.val then gsLvl q ζ 64 2 a0 c else a0 c) :
    backend.avx2.ntt.invntt_block_loop1 SECOND iter b qv
      ⦃ (r : Array I16 256#usize) =>
          BlockBnd r B ∧ ∀ c < 256, tposZ q r c = gsLvl q ζ 64 2 a0 c ⦄ := by
  unfold backend.avx2.ntt.invntt_block_loop1
  by_cases hlt : iter.start.val < iter.«end».val
  · let* ⟨ o, iter1, ho, hstart', hend' ⟩ ← core.iter.range.IteratorRange.next_Usize_some_spec
    rw [ho]; simp only
    apply WP.spec_bind (invntt_block_loop1_loop0_walk SECOND
      { start := 0#usize, «end» := 2#usize } b qv iter.start q Zb A T B Rinv ζ a0 hq0 hqlt hR hQ
      hA0 hZ0 hsum hAZ hT hB1 hB2 (by omega) (htbl iter.start (by omega)) rfl (by decide) ?_ ?_)
    · intro b1 hb1
      apply invntt_block_loop1_walk SECOND iter1 b1 qv q Zb A T B Rinv ζ a0 hq0 hqlt hR hQ hA0
        hZ0 hsum hAZ hT hB1 hB2 htbl (by rw [hend']; exact hend) (by omega)
      · obtain ⟨⟨hg, hp⟩, -⟩ := hb1
        refine ⟨fun v hv hP => hg v hv ?_, fun v hv hP => hp v hv ?_⟩
        · have hP' : v < 4 * iter1.start.val := hP
          show v < 4 * iter.start.val + 4
          omega
        · have hP' : ¬ (v < 4 * iter1.start.val) := hP
          show ¬ (v < 4 * iter.start.val + 4)
          omega
      · intro c hc
        rw [hb1.2 c hc]
        by_cases hP : c % 16 < 4 * iter.start.val + 4
        · rw [if_pos hP, if_pos (by omega)]
        · rw [if_neg hP, if_neg (by omega)]
    · obtain ⟨hg, hp⟩ := hbnd
      refine ⟨fun v hv hP => hg v hv ?_, fun v hv hP => hp v hv ?_⟩
      · have hP' : v < 4 * iter.start.val
            ∨ (4 * iter.start.val ≤ v ∧ v < 4 * iter.start.val + 0)
            ∨ (4 * iter.start.val + 2 ≤ v ∧ v < 4 * iter.start.val + 2 + 0) := hP
        show v < 4 * iter.start.val
        omega
      · have hP' : ¬ (v < 4 * iter.start.val
            ∨ (4 * iter.start.val ≤ v ∧ v < 4 * iter.start.val + 0)
            ∨ (4 * iter.start.val + 2 ≤ v ∧ v < 4 * iter.start.val + 2 + 0)) := hP
        show ¬ (v < 4 * iter.start.val)
        omega
    · intro c hc
      show tposZ q b c = if c % 16 < 4 * iter.start.val
        ∨ (4 * iter.start.val ≤ c % 16 ∧ c % 16 < 4 * iter.start.val + 0)
        ∨ (4 * iter.start.val + 2 ≤ c % 16 ∧ c % 16 < 4 * iter.start.val + 2 + 0)
        then gsLvl q ζ 64 2 a0 c else a0 c
      rw [hval c hc]
      by_cases hP : c % 16 < 4 * iter.start.val
      · rw [if_pos hP, if_pos (by omega)]
      · rw [if_neg hP, if_neg (by omega)]
  · let* ⟨ o, iter1, hnone, _ ⟩ ← core.iter.range.IteratorRange.next_Usize_none_spec
    rw [hnone]; simp only [WP.spec_ok]
    refine ⟨?_, ?_⟩
    · rw [blockBnd_iff]
      intro v hv
      refine hbnd.1 v hv ?_
      show v < 4 * iter.start.val
      omega
    · intro c hc
      rw [hval c hc, if_pos (by omega)]
termination_by iter.«end».val - iter.start.val
decreasing_by scalar_decr_tac

/-- The `len = 4` inverse level, one group: `4` butterflies pairing `8·h + j` with
`8·h + j + 4`.

The ζ index the table hands back is `63 − h − 2·k`, and `c / (2·4) = 2·k + h`,
so it is `2·32 − 1 − c/(2·4)` — the index `gsLvl` asks for.  Note the ζ stride and the pair
offset are different numbers: the table walks `2` per lane while the butterfly pairs at
distance `4`. -/
theorem invntt_block_loop2_loop0_walk (SECOND : Bool) (iter : core.ops.range.Range Usize)
    (b : Array I16 256#usize) (qv : Vec256) (h : Usize) (q : ℕ) (Zb A T B : ℤ) (Rinv : ZMod q)
    (ζ : ℕ → ZMod q) (a0 : ℕ → ZMod q)
    (hq0 : 0 < (q : ℤ)) (hqlt : (q : ℤ) ≤ 2 ^ 15)
    (hR : ((2 ^ 16 : ℤ) : ZMod q) * Rinv = 1)
    (hQ : ∀ i < 16, (lane16 qv i).toInt = (q : ℤ))
    (hA0 : 0 ≤ A) (hZ0 : 0 ≤ Zb) (hsum : 2 * A ≤ 2 ^ 15 - 1)
    (hAZ : 2 * A * Zb < 2 ^ 15 * (q : ℤ))
    (hT : 2 * A * Zb + 2 ^ 15 * (q : ℤ) ≤ 2 ^ 16 * T)
    (hB1 : 2 * A ≤ B) (hB2 : T ≤ B)
    (hh : h.val < 2)
    (htbl : ∃ z zq,
      (if SECOND then (do let t ← backend.avx2.ntt.INV4_Q2; backend.avx2.ntt.ld_tbl t h)
       else (do let t ← backend.avx2.ntt.INV4_Q1; backend.avx2.ntt.ld_tbl t h))
        = ok (z, zq) ∧ PsiOk z zq (q : ℤ) Zb ∧
        ∀ k < 16, laneZ q z k * Rinv = -(ζ (63 - h.val - 2 * k)))
    (hend : iter.«end».val = 4) (hstartle : iter.start.val ≤ 4)
    (hbnd : SplitB b (fun v => v < 8 * h.val
        ∨ (8 * h.val ≤ v ∧ v < 8 * h.val + iter.start.val)
        ∨ (8 * h.val + 4 ≤ v ∧ v < 8 * h.val + 4 + iter.start.val)) A B)
    (hval : ∀ c < 256, tposZ q b c =
      if c % 16 < 8 * h.val
        ∨ (8 * h.val ≤ c % 16 ∧ c % 16 < 8 * h.val + iter.start.val)
        ∨ (8 * h.val + 4 ≤ c % 16 ∧ c % 16 < 8 * h.val + 4 + iter.start.val)
      then gsLvl q ζ 32 4 a0 c else a0 c) :
    backend.avx2.ntt.invntt_block_loop2_loop0 SECOND iter b qv h
      ⦃ (r : Array I16 256#usize) =>
          SplitB r (fun v => v < 8 * h.val + 8) A B ∧
          ∀ c < 256, tposZ q r c =
            if c % 16 < 8 * h.val + 8 then gsLvl q ζ 32 4 a0 c else a0 c ⦄ := by
  unfold backend.avx2.ntt.invntt_block_loop2_loop0
  obtain ⟨z, zq, htz, ⟨hzb, hzqm⟩, hζ⟩ := htbl
  by_cases hlt : iter.start.val < iter.«end».val
  · let* ⟨ o, iter1, ho, hstart', hend' ⟩ ← core.iter.range.IteratorRange.next_Usize_some_spec
    rw [ho]; simp only
    rw [htz, bind_tc_ok]
    show (do let i ← 8#usize * h
             let i1 ← i + iter.start
             let lo ← load_i16 b i1
             let i2 ← i + iter.start
             let i3 ← i2 + 4#usize
             let hi ← load_i16 b i3
             let (lo1, hi1) ← backend.avx2.ntt.gs_butterfly lo hi z zq qv
             let i4 ← i + iter.start
             let b1 ← store_i16 b i4 lo1
             let i5 ← i + iter.start
             let i6 ← i5 + 4#usize
             let b2 ← store_i16 b1 i6 hi1
             backend.avx2.ntt.invntt_block_loop2_loop0 SECOND iter1 b2 qv h)
        ⦃ (r : Array I16 256#usize) =>
            SplitB r (fun v => v < 8 * h.val + 8) A B ∧
            ∀ c < 256, tposZ q r c =
              if c % 16 < 8 * h.val + 8 then gsLvl q ζ 32 4 a0 c else a0 c ⦄
    obtain ⟨hgrown, hplain⟩ := hbnd
    step*
    obtain ⟨lo, hlo, hlob⟩ := load_i16_bndAt b i1 (by omega)
      (hplain i1.val (by omega) (by omega))
    obtain ⟨lo', hlo', hlov⟩ := load_posZ q b i1 (by omega)
    rw [show lo = lo' from by rw [hlo] at hlo'; injection hlo'] at hlob
    rw [hlo', bind_tc_ok]
    step*
    obtain ⟨hiv, hhiv, hhivb⟩ := load_i16_bndAt b i3 (by omega)
      (hplain i3.val (by omega) (by omega))
    obtain ⟨hiv', hhiv', hhivv⟩ := load_posZ q b i3 (by omega)
    rw [show hiv = hiv' from by rw [hhiv] at hhiv'; injection hhiv'] at hhivb
    rw [hhiv', bind_tc_ok]
    apply WP.spec_bind (spec_and
      (gs_butterfly_bnd lo' hiv' z zq qv (q : ℤ) Zb A T hQ hq0 hqlt hzqm hlob hhivb hzb hA0 hZ0
        hsum hAZ hT)
      (gs_butterfly_val lo' hiv' z zq qv q Zb A T Rinv hq0 hqlt hR hQ hzqm hlob hhivb hzb hA0
        hZ0 hsum hAZ))
    intro r hr
    obtain ⟨lo1, hi1'⟩ := r
    obtain ⟨⟨hr1, hr2⟩, hrv⟩ := hr
    simp only at hr1 hr2 hrv
    show (do let i4 ← i + iter.start
             let b1 ← store_i16 b i4 lo1
             let i5 ← i + iter.start
             let i6 ← i5 + 4#usize
             let b2 ← store_i16 b1 i6 hi1'
             backend.avx2.ntt.invntt_block_loop2_loop0 SECOND iter1 b2 qv h)
        ⦃ (r : Array I16 256#usize) =>
            SplitB r (fun v => v < 8 * h.val + 8) A B ∧
            ∀ c < 256, tposZ q r c =
              if c % 16 < 8 * h.val + 8 then gsLvl q ζ 32 4 a0 c else a0 c ⦄
    step*
    obtain ⟨b1, hb1, hb1at, hb1oth⟩ := store_i16_at b i4 lo1 (by omega)
    obtain ⟨b1', hb1', hb1v⟩ := store_posZ q b i4 lo1 (by omega)
    rw [show b1 = b1' from by rw [hb1] at hb1'; injection hb1'] at hb1at hb1oth
    rw [hb1', bind_tc_ok]
    step*
    obtain ⟨b2, hb2, hb2at, hb2oth⟩ := store_i16_at b1' i6 hi1' (by omega)
    obtain ⟨b2', hb2', hb2v⟩ := store_posZ q b1' i6 hi1' (by omega)
    rw [show b2 = b2' from by rw [hb2] at hb2'; injection hb2'] at hb2at hb2oth
    rw [hb2', bind_tc_ok]
    apply invntt_block_loop2_loop0_walk SECOND iter1 b2' qv h q Zb A T B Rinv ζ a0 hq0 hqlt hR
      hQ hA0 hZ0 hsum hAZ hT hB1 hB2 hh ⟨z, zq, htz, ⟨hzb, hzqm⟩, hζ⟩ (by rw [hend']; exact hend)
      (by omega)
    · constructor
      · intro v hv hP
        rcases (show v = i4.val ∨ v = i6.val ∨ (v ≠ i4.val ∧ v ≠ i6.val) from by omega)
          with rfl | rfl | ⟨hne1, hne2⟩
        · intro k hk
          rw [hb2oth i4.val (by omega) (by omega) k hk, hb1at k hk]
          exact le_trans (hr1 k hk) hB1
        · intro k hk
          rw [hb2at k hk]
          exact le_trans (hr2 k hk) hB2
        · intro k hk
          rw [hb2oth v hv hne2 k hk, hb1oth v hv hne1 k hk]
          exact hgrown v hv (by omega) k hk
      · intro v hv hP k hk
        rw [hb2oth v hv (by omega) k hk, hb1oth v hv (by omega) k hk]
        exact hplain v hv (by omega) k hk
    · intro c hc
      have hc16 : c / 16 < 16 := by omega
      have hcm : c % 16 < 16 := by omega
      have hp : 16 * (c % 16) + c / 16 < 256 := by omega
      rw [tposZ, hb2v _ hp, hb1v _ hp]
      by_cases h1 : c % 16 = i6.val
      · rw [if_pos (by omega), if_pos (by omega),
          show 16 * (c % 16) + c / 16 - 16 * i6.val = c / 16 from by omega,
          (hrv (c / 16) hc16).2, hlov (c / 16) hc16, hhivv (c / 16) hc16]
        have hmL : (c - 4) % 16 = c % 16 - 4 := by omega
        have hdL : (c - 4) / 16 = c / 16 := by omega
        have e1 : posZ q b (16 * i1.val + c / 16) = a0 (c - 4) := by
          rw [show 16 * i1.val + c / 16 = 16 * ((c - 4) % 16) + (c - 4) / 16 from by
              rw [hmL, hdL]; omega,
            ← tposZ, hval (c - 4) (by omega), if_neg (by omega)]
        have e2 : posZ q b (16 * i3.val + c / 16) = a0 c := by
          rw [show 16 * i3.val + c / 16 = 16 * (c % 16) + c / 16 from by omega, ← tposZ,
            hval c hc, if_neg (by omega)]
        rw [e1, e2, gsLvl, if_neg (by omega), hζ (c / 16) hc16,
          show 63 - h.val - 2 * (c / 16) = 2 * 32 - 1 - c / (2 * 4) from by omega]
      · rw [if_neg (by omega)]
        by_cases h2 : c % 16 = i4.val
        · rw [if_pos (by omega), if_pos (by omega),
            show 16 * (c % 16) + c / 16 - 16 * i4.val = c / 16 from by omega,
            (hrv (c / 16) hc16).1, hlov (c / 16) hc16, hhivv (c / 16) hc16]
          have e1 : posZ q b (16 * i1.val + c / 16) = a0 c := by
            rw [show 16 * i1.val + c / 16 = 16 * (c % 16) + c / 16 from by omega, ← tposZ,
              hval c hc, if_neg (by omega)]
          have e2 : posZ q b (16 * i3.val + c / 16) = a0 (c + 4) := by
            rw [show 16 * i3.val + c / 16
              = 16 * ((c + 4) % 16) + (c + 4) / 16 from by omega,
              ← tposZ, hval (c + 4) (by omega), if_neg (by omega)]
          rw [e1, e2, gsLvl, if_pos (by omega)]
        · rw [if_neg (by omega), ← tposZ, hval c hc]
          by_cases hP : c % 16 < 8 * h.val
              ∨ (8 * h.val ≤ c % 16 ∧ c % 16 < 8 * h.val + iter.start.val)
              ∨ (8 * h.val + 4 ≤ c % 16 ∧ c % 16 < 8 * h.val + 4 + iter.start.val)
          · rw [if_pos hP, if_pos (by omega)]
          · rw [if_neg hP, if_neg (by omega)]
  · let* ⟨ o, iter1, hnone, _ ⟩ ← core.iter.range.IteratorRange.next_Usize_none_spec
    rw [hnone]; simp only [WP.spec_ok]
    obtain ⟨hgrown, hplain⟩ := hbnd
    refine ⟨⟨fun v hv hP => hgrown v hv ?_, fun v hv hP => hplain v hv ?_⟩, fun c hc => ?_⟩
    · have hP' : v < 8 * h.val + 8 := hP
      show v < 8 * h.val ∨ (8 * h.val ≤ v ∧ v < 8 * h.val + iter.start.val)
        ∨ (8 * h.val + 4 ≤ v ∧ v < 8 * h.val + 4 + iter.start.val)
      omega
    · have hP' : ¬ (v < 8 * h.val + 8) := hP
      show ¬ (v < 8 * h.val ∨ (8 * h.val ≤ v ∧ v < 8 * h.val + iter.start.val)
        ∨ (8 * h.val + 4 ≤ v ∧ v < 8 * h.val + 4 + iter.start.val))
      omega
    · rw [hval c hc]
      by_cases hP : c % 16 < 8 * h.val + 8
      · rw [if_pos hP, if_pos (by omega)]
      · rw [if_neg hP, if_neg (by omega)]
termination_by iter.«end».val - iter.start.val
decreasing_by scalar_decr_tac

/-- The `len = 4` inverse level: 2 groups. -/
theorem invntt_block_loop2_walk (SECOND : Bool) (iter : core.ops.range.Range Usize)
    (b : Array I16 256#usize) (qv : Vec256) (q : ℕ) (Zb A T B : ℤ) (Rinv : ZMod q)
    (ζ : ℕ → ZMod q) (a0 : ℕ → ZMod q)
    (hq0 : 0 < (q : ℤ)) (hqlt : (q : ℤ) ≤ 2 ^ 15)
    (hR : ((2 ^ 16 : ℤ) : ZMod q) * Rinv = 1)
    (hQ : ∀ i < 16, (lane16 qv i).toInt = (q : ℤ))
    (hA0 : 0 ≤ A) (hZ0 : 0 ≤ Zb) (hsum : 2 * A ≤ 2 ^ 15 - 1)
    (hAZ : 2 * A * Zb < 2 ^ 15 * (q : ℤ))
    (hT : 2 * A * Zb + 2 ^ 15 * (q : ℤ) ≤ 2 ^ 16 * T)
    (hB1 : 2 * A ≤ B) (hB2 : T ≤ B)
    (htbl : ∀ h : Usize, h.val < 2 → ∃ z zq,
      (if SECOND then (do let t ← backend.avx2.ntt.INV4_Q2; backend.avx2.ntt.ld_tbl t h)
       else (do let t ← backend.avx2.ntt.INV4_Q1; backend.avx2.ntt.ld_tbl t h))
        = ok (z, zq) ∧ PsiOk z zq (q : ℤ) Zb ∧
        ∀ k < 16, laneZ q z k * Rinv = -(ζ (63 - h.val - 2 * k)))
    (hend : iter.«end».val = 2) (hstartle : iter.start.val ≤ 2)
    (hbnd : SplitB b (fun v => v < 8 * iter.start.val) A B)
    (hval : ∀ c < 256, tposZ q b c =
      if c % 16 < 8 * iter.start.val then gsLvl q ζ 32 4 a0 c else a0 c) :
    backend.avx2.ntt.invntt_block_loop2 SECOND iter b qv
      ⦃ (r : Array I16 256#usize) =>
          BlockBnd r B ∧ ∀ c < 256, tposZ q r c = gsLvl q ζ 32 4 a0 c ⦄ := by
  unfold backend.avx2.ntt.invntt_block_loop2
  by_cases hlt : iter.start.val < iter.«end».val
  · let* ⟨ o, iter1, ho, hstart', hend' ⟩ ← core.iter.range.IteratorRange.next_Usize_some_spec
    rw [ho]; simp only
    apply WP.spec_bind (invntt_block_loop2_loop0_walk SECOND
      { start := 0#usize, «end» := 4#usize } b qv iter.start q Zb A T B Rinv ζ a0 hq0 hqlt hR hQ
      hA0 hZ0 hsum hAZ hT hB1 hB2 (by omega) (htbl iter.start (by omega)) rfl (by decide) ?_ ?_)
    · intro b1 hb1
      apply invntt_block_loop2_walk SECOND iter1 b1 qv q Zb A T B Rinv ζ a0 hq0 hqlt hR hQ hA0
        hZ0 hsum hAZ hT hB1 hB2 htbl (by rw [hend']; exact hend) (by omega)
      · obtain ⟨⟨hg, hp⟩, -⟩ := hb1
        refine ⟨fun v hv hP => hg v hv ?_, fun v hv hP => hp v hv ?_⟩
        · have hP' : v < 8 * iter1.start.val := hP
          show v < 8 * iter.start.val + 8
          omega
        · have hP' : ¬ (v < 8 * iter1.start.val) := hP
          show ¬ (v < 8 * iter.start.val + 8)
          omega
      · intro c hc
        rw [hb1.2 c hc]
        by_cases hP : c % 16 < 8 * iter.start.val + 8
        · rw [if_pos hP, if_pos (by omega)]
        · rw [if_neg hP, if_neg (by omega)]
    · obtain ⟨hg, hp⟩ := hbnd
      refine ⟨fun v hv hP => hg v hv ?_, fun v hv hP => hp v hv ?_⟩
      · have hP' : v < 8 * iter.start.val
            ∨ (8 * iter.start.val ≤ v ∧ v < 8 * iter.start.val + 0)
            ∨ (8 * iter.start.val + 4 ≤ v ∧ v < 8 * iter.start.val + 4 + 0) := hP
        show v < 8 * iter.start.val
        omega
      · have hP' : ¬ (v < 8 * iter.start.val
            ∨ (8 * iter.start.val ≤ v ∧ v < 8 * iter.start.val + 0)
            ∨ (8 * iter.start.val + 4 ≤ v ∧ v < 8 * iter.start.val + 4 + 0)) := hP
        show ¬ (v < 8 * iter.start.val)
        omega
    · intro c hc
      show tposZ q b c = if c % 16 < 8 * iter.start.val
        ∨ (8 * iter.start.val ≤ c % 16 ∧ c % 16 < 8 * iter.start.val + 0)
        ∨ (8 * iter.start.val + 4 ≤ c % 16 ∧ c % 16 < 8 * iter.start.val + 4 + 0)
        then gsLvl q ζ 32 4 a0 c else a0 c
      rw [hval c hc]
      by_cases hP : c % 16 < 8 * iter.start.val
      · rw [if_pos hP, if_pos (by omega)]
      · rw [if_neg hP, if_neg (by omega)]
  · let* ⟨ o, iter1, hnone, _ ⟩ ← core.iter.range.IteratorRange.next_Usize_none_spec
    rw [hnone]; simp only [WP.spec_ok]
    refine ⟨?_, ?_⟩
    · rw [blockBnd_iff]
      intro v hv
      refine hbnd.1 v hv ?_
      show v < 8 * iter.start.val
      omega
    · intro c hc
      rw [hval c hc, if_pos (by omega)]
termination_by iter.«end».val - iter.start.val
decreasing_by scalar_decr_tac

/-- The `len = 8` inverse level: eight butterflies pairing `j` with `j + 8`, one group.

`h` is the literal `0`, so the table's ζ index is just `31 − k`, and `c / (2·8) = c / 16 = k`. -/
theorem invntt_block_loop3_walk (SECOND : Bool) (iter : core.ops.range.Range Usize)
    (b : Array I16 256#usize) (qv : Vec256) (q : ℕ) (Zb A T B : ℤ) (Rinv : ZMod q)
    (ζ : ℕ → ZMod q) (a0 : ℕ → ZMod q)
    (hq0 : 0 < (q : ℤ)) (hqlt : (q : ℤ) ≤ 2 ^ 15)
    (hR : ((2 ^ 16 : ℤ) : ZMod q) * Rinv = 1)
    (hQ : ∀ i < 16, (lane16 qv i).toInt = (q : ℤ))
    (hA0 : 0 ≤ A) (hZ0 : 0 ≤ Zb) (hsum : 2 * A ≤ 2 ^ 15 - 1)
    (hAZ : 2 * A * Zb < 2 ^ 15 * (q : ℤ))
    (hT : 2 * A * Zb + 2 ^ 15 * (q : ℤ) ≤ 2 ^ 16 * T)
    (hB1 : 2 * A ≤ B) (hB2 : T ≤ B)
    (htbl : ∃ z zq,
      (if SECOND then (do let t ← backend.avx2.ntt.INV8_Q2; backend.avx2.ntt.ld_tbl t 0#usize)
       else (do let t ← backend.avx2.ntt.INV8_Q1; backend.avx2.ntt.ld_tbl t 0#usize))
        = ok (z, zq) ∧ PsiOk z zq (q : ℤ) Zb ∧ ∀ k < 16, laneZ q z k * Rinv = -(ζ (31 - k)))
    (hend : iter.«end».val = 8)
    (hbnd : SplitB b (fun v => v < iter.start.val ∨ (8 ≤ v ∧ v < 8 + iter.start.val)) A B)
    (hval : ∀ c < 256, tposZ q b c =
      if c % 16 < iter.start.val ∨ (8 ≤ c % 16 ∧ c % 16 < 8 + iter.start.val)
      then gsLvl q ζ 16 8 a0 c else a0 c) :
    backend.avx2.ntt.invntt_block_loop3 SECOND iter b qv
      ⦃ (r : Array I16 256#usize) =>
          BlockBnd r B ∧ ∀ c < 256, tposZ q r c = gsLvl q ζ 16 8 a0 c ⦄ := by
  unfold backend.avx2.ntt.invntt_block_loop3
  obtain ⟨z, zq, htz, ⟨hzb, hzqm⟩, hζ⟩ := htbl
  by_cases hlt : iter.start.val < iter.«end».val
  · let* ⟨ o, iter1, ho, hstart', hend' ⟩ ← core.iter.range.IteratorRange.next_Usize_some_spec
    rw [ho]; simp only
    rw [htz, bind_tc_ok]
    show (do let lo ← load_i16 b iter.start
             let i ← iter.start + 8#usize
             let hi ← load_i16 b i
             let (lo1, hi1) ← backend.avx2.ntt.gs_butterfly lo hi z zq qv
             let b1 ← store_i16 b iter.start lo1
             let b2 ← store_i16 b1 i hi1
             backend.avx2.ntt.invntt_block_loop3 SECOND iter1 b2 qv)
        ⦃ (r : Array I16 256#usize) =>
            BlockBnd r B ∧ ∀ c < 256, tposZ q r c = gsLvl q ζ 16 8 a0 c ⦄
    obtain ⟨hgrown, hplain⟩ := hbnd
    obtain ⟨lo, hlo, hlob⟩ := load_i16_bndAt b iter.start (by omega)
      (hplain iter.start.val (by omega) (by omega))
    obtain ⟨lo', hlo', hlov⟩ := load_posZ q b iter.start (by omega)
    rw [show lo = lo' from by rw [hlo] at hlo'; injection hlo'] at hlob
    rw [hlo', bind_tc_ok]
    step*
    obtain ⟨hiv, hhiv, hhivb⟩ := load_i16_bndAt b i (by omega)
      (hplain i.val (by omega) (by omega))
    obtain ⟨hiv', hhiv', hhivv⟩ := load_posZ q b i (by omega)
    rw [show hiv = hiv' from by rw [hhiv] at hhiv'; injection hhiv'] at hhivb
    rw [hhiv', bind_tc_ok]
    apply WP.spec_bind (spec_and
      (gs_butterfly_bnd lo' hiv' z zq qv (q : ℤ) Zb A T hQ hq0 hqlt hzqm hlob hhivb hzb hA0 hZ0
        hsum hAZ hT)
      (gs_butterfly_val lo' hiv' z zq qv q Zb A T Rinv hq0 hqlt hR hQ hzqm hlob hhivb hzb hA0
        hZ0 hsum hAZ))
    intro r hr
    obtain ⟨lo1, hi1'⟩ := r
    obtain ⟨⟨hr1, hr2⟩, hrv⟩ := hr
    simp only at hr1 hr2 hrv
    show (do let b1 ← store_i16 b iter.start lo1
             let b2 ← store_i16 b1 i hi1'
             backend.avx2.ntt.invntt_block_loop3 SECOND iter1 b2 qv)
        ⦃ (r : Array I16 256#usize) =>
            BlockBnd r B ∧ ∀ c < 256, tposZ q r c = gsLvl q ζ 16 8 a0 c ⦄
    obtain ⟨b1, hb1, hb1at, hb1oth⟩ := store_i16_at b iter.start lo1 (by omega)
    obtain ⟨b1', hb1', hb1v⟩ := store_posZ q b iter.start lo1 (by omega)
    rw [show b1 = b1' from by rw [hb1] at hb1'; injection hb1'] at hb1at hb1oth
    rw [hb1', bind_tc_ok]
    obtain ⟨b2, hb2, hb2at, hb2oth⟩ := store_i16_at b1' i hi1' (by omega)
    obtain ⟨b2', hb2', hb2v⟩ := store_posZ q b1' i hi1' (by omega)
    rw [show b2 = b2' from by rw [hb2] at hb2'; injection hb2'] at hb2at hb2oth
    rw [hb2', bind_tc_ok]
    apply invntt_block_loop3_walk SECOND iter1 b2' qv q Zb A T B Rinv ζ a0 hq0 hqlt hR hQ hA0 hZ0
      hsum hAZ hT hB1 hB2 ⟨z, zq, htz, ⟨hzb, hzqm⟩, hζ⟩ (by rw [hend']; exact hend)
    · constructor
      · intro v hv hP
        rcases (show v = iter.start.val ∨ v = i.val ∨ (v ≠ iter.start.val ∧ v ≠ i.val)
          from by omega) with rfl | rfl | ⟨hne1, hne2⟩
        · intro k hk
          rw [hb2oth iter.start.val (by omega) (by omega) k hk, hb1at k hk]
          exact le_trans (hr1 k hk) hB1
        · intro k hk
          rw [hb2at k hk]
          exact le_trans (hr2 k hk) hB2
        · intro k hk
          rw [hb2oth v hv hne2 k hk, hb1oth v hv hne1 k hk]
          exact hgrown v hv (by omega) k hk
      · intro v hv hP k hk
        rw [hb2oth v hv (by omega) k hk, hb1oth v hv (by omega) k hk]
        exact hplain v hv (by omega) k hk
    · intro c hc
      have hc16 : c / 16 < 16 := by omega
      have hcm : c % 16 < 16 := by omega
      have hp : 16 * (c % 16) + c / 16 < 256 := by omega
      have hrec : c = 16 * (c / 16) + c % 16 := by omega
      rw [tposZ, hb2v _ hp, hb1v _ hp]
      by_cases h1 : c % 16 = i.val
      · rw [if_pos (by omega), if_pos (by omega),
          show 16 * (c % 16) + c / 16 - 16 * i.val = c / 16 from by omega,
          (hrv (c / 16) hc16).2, hlov (c / 16) hc16, hhivv (c / 16) hc16]
        have e1 : posZ q b (16 * iter.start.val + c / 16) = a0 (c - 8) := by
          rw [show 16 * iter.start.val + c / 16
            = 16 * ((c - 8) % 16) + (c - 8) / 16 from by omega, ← tposZ, hval (c - 8) (by omega),
            if_neg (by omega)]
        have e2 : posZ q b (16 * i.val + c / 16) = a0 c := by
          rw [show 16 * i.val + c / 16 = 16 * (c % 16) + c / 16 from by omega, ← tposZ,
            hval c hc, if_neg (by omega)]
        rw [e1, e2, gsLvl, if_neg (by omega), hζ (c / 16) hc16,
          show 31 - c / 16 = 2 * 16 - 1 - c / (2 * 8) from by omega]
      · rw [if_neg (by omega)]
        by_cases h2 : c % 16 = iter.start.val
        · rw [if_pos (by omega), if_pos (by omega),
            show 16 * (c % 16) + c / 16 - 16 * iter.start.val = c / 16 from by omega,
            (hrv (c / 16) hc16).1, hlov (c / 16) hc16, hhivv (c / 16) hc16]
          have e1 : posZ q b (16 * iter.start.val + c / 16) = a0 c := by
            rw [show 16 * iter.start.val + c / 16 = 16 * (c % 16) + c / 16 from by omega,
              ← tposZ, hval c hc, if_neg (by omega)]
          have e2 : posZ q b (16 * i.val + c / 16) = a0 (c + 8) := by
            rw [show 16 * i.val + c / 16 = 16 * ((c + 8) % 16) + (c + 8) / 16 from by omega,
              ← tposZ, hval (c + 8) (by omega), if_neg (by omega)]
          rw [e1, e2, gsLvl, if_pos (by omega)]
        · rw [if_neg (by omega), ← tposZ, hval c hc]
          by_cases hP : c % 16 < iter.start.val ∨ (8 ≤ c % 16 ∧ c % 16 < 8 + iter.start.val)
          · rw [if_pos hP, if_pos (by omega)]
          · rw [if_neg hP, if_neg (by omega)]
  · let* ⟨ o, iter1, hnone, _ ⟩ ← core.iter.range.IteratorRange.next_Usize_none_spec
    rw [hnone]; simp only [WP.spec_ok]
    refine ⟨?_, ?_⟩
    · rw [blockBnd_iff]
      intro v hv
      exact hbnd.1 v hv (by omega)
    · intro c hc
      rw [hval c hc, if_pos (by omega)]
termination_by iter.«end».val - iter.start.val
decreasing_by scalar_decr_tac

/-! ## The horizontal inverse levels

After the second transpose the array position *is* the coefficient index, so a butterfly on
vectors `(i, i + half)` pairs coefficients `c` and `c + 16·half`: a Gentleman-Sande layer with
`m' = 16·half`.  The running `k` counts *down* — `invntt_block` starts it at 16 and decrements
once per group — and `hkk` ties it to `gsLvl`'s index `2·nb − 1 − b`, with the group index `b`
carried explicitly so no division by the variable `half` ever appears. -/

/-- One group of a horizontal inverse level: `half` butterflies sharing one broadcast `−ζ`. -/
theorem invntt_block_loop4_loop0_loop0_walk (b : Array I16 256#usize) (qv : Vec256)
    (half start i : Usize) (z zq : Vec256) (q : ℕ) (Zb A T B : ℤ) (Rinv : ZMod q)
    (ζ : ℕ → ZMod q) (a0 : ℕ → ZMod q) (nb kk bIdx : ℕ)
    (hq0 : 0 < (q : ℤ)) (hqlt : (q : ℤ) ≤ 2 ^ 15)
    (hR : ((2 ^ 16 : ℤ) : ZMod q) * Rinv = 1)
    (hQ : ∀ j < 16, (lane16 qv j).toInt = (q : ℤ))
    (hA0 : 0 ≤ A) (hZ0 : 0 ≤ Zb) (hsum : 2 * A ≤ 2 ^ 15 - 1)
    (hAZ : 2 * A * Zb < 2 ^ 15 * (q : ℤ))
    (hT : 2 * A * Zb + 2 ^ 15 * (q : ℤ) ≤ 2 ^ 16 * T)
    (hB1 : 2 * A ≤ B) (hB2 : T ≤ B)
    (hpsi : PsiOk z zq (q : ℤ) Zb)
    (hzk : ∀ k < 16, laneZ q z k * Rinv = -(ζ kk))
    (hhalf : half.val = 8 ∨ half.val = 4 ∨ half.val = 2 ∨ half.val = 1)
    (hgrp : start.val + 2 * half.val ≤ 16) (hstartb : start.val = bIdx * (2 * half.val))
    (hkk : 2 * nb - 1 - bIdx = kk)
    (hi : start.val ≤ i.val ∧ i.val ≤ start.val + half.val)
    (hbnd : SplitB b (fun v => v < start.val
        ∨ (start.val ≤ v ∧ v < i.val)
        ∨ (start.val + half.val ≤ v ∧ v < i.val + half.val)) A B)
    (hval : ∀ c < 256, posZ q b c =
      if c / 16 < start.val ∨ (start.val ≤ c / 16 ∧ c / 16 < i.val)
        ∨ (start.val + half.val ≤ c / 16 ∧ c / 16 < i.val + half.val)
      then gsLvl q ζ nb (16 * half.val) a0 c else a0 c) :
    backend.avx2.ntt.invntt_block_loop4_loop0_loop0 b qv half start z zq i
      ⦃ (r : Array I16 256#usize) =>
          SplitB r (fun v => v < start.val + 2 * half.val) A B ∧
          ∀ c < 256, posZ q r c =
            if c / 16 < start.val + 2 * half.val
            then gsLvl q ζ nb (16 * half.val) a0 c else a0 c ⦄ := by
  unfold backend.avx2.ntt.invntt_block_loop4_loop0_loop0
  obtain ⟨hzb, hzqm⟩ := hpsi
  obtain ⟨hgrown, hplain⟩ := hbnd
  by_cases hlt : i.val < start.val + half.val
  · step*
    obtain ⟨lo, hlo, hlob⟩ := load_i16_bndAt b i (by omega) (hplain i.val (by omega) (by omega))
    obtain ⟨lo', hlo', hlov⟩ := load_posZ q b i (by omega)
    rw [show lo = lo' from by rw [hlo] at hlo'; injection hlo'] at hlob
    rw [hlo', bind_tc_ok]
    step*
    obtain ⟨hiv, hhiv, hhivb⟩ := load_i16_bndAt b i2 (by omega)
      (hplain i2.val (by omega) (by omega))
    obtain ⟨hiv', hhiv', hhivv⟩ := load_posZ q b i2 (by omega)
    rw [show hiv = hiv' from by rw [hhiv] at hhiv'; injection hhiv'] at hhivb
    rw [hhiv', bind_tc_ok]
    apply WP.spec_bind (spec_and
      (gs_butterfly_bnd lo' hiv' z zq qv (q : ℤ) Zb A T hQ hq0 hqlt hzqm hlob hhivb hzb hA0 hZ0
        hsum hAZ hT)
      (gs_butterfly_val lo' hiv' z zq qv q Zb A T Rinv hq0 hqlt hR hQ hzqm hlob hhivb hzb hA0
        hZ0 hsum hAZ))
    intro r hr
    obtain ⟨lo1, hi1'⟩ := r
    obtain ⟨⟨hr1, hr2⟩, hrv⟩ := hr
    simp only at hr1 hr2 hrv
    show (do let b1 ← store_i16 b i lo1
             let b2 ← store_i16 b1 i2 hi1'
             let i3 ← i + 1#usize
             backend.avx2.ntt.invntt_block_loop4_loop0_loop0 b2 qv half start z zq i3)
        ⦃ (r : Array I16 256#usize) =>
            SplitB r (fun v => v < start.val + 2 * half.val) A B ∧
            ∀ c < 256, posZ q r c =
              if c / 16 < start.val + 2 * half.val
              then gsLvl q ζ nb (16 * half.val) a0 c else a0 c ⦄
    obtain ⟨b1, hb1, hb1at, hb1oth⟩ := store_i16_at b i lo1 (by omega)
    obtain ⟨b1', hb1', hb1v⟩ := store_posZ q b i lo1 (by omega)
    rw [show b1 = b1' from by rw [hb1] at hb1'; injection hb1'] at hb1at hb1oth
    rw [hb1', bind_tc_ok]
    obtain ⟨b2, hb2, hb2at, hb2oth⟩ := store_i16_at b1' i2 hi1' (by omega)
    obtain ⟨b2', hb2', hb2v⟩ := store_posZ q b1' i2 hi1' (by omega)
    rw [show b2 = b2' from by rw [hb2] at hb2'; injection hb2'] at hb2at hb2oth
    rw [hb2', bind_tc_ok]
    obtain ⟨i3, hi3, hi3v⟩ := WP.spec_imp_exists
      (Std.Usize.add_spec (x := i) (y := 1#usize) (by scalar_tac))
    rw [hi3, bind_tc_ok]
    have hi3n : i3.val = i.val + 1 := by scalar_tac
    apply invntt_block_loop4_loop0_loop0_walk b2' qv half start i3 z zq q Zb A T B Rinv ζ a0 nb kk
      bIdx hq0 hqlt hR hQ hA0 hZ0 hsum hAZ hT hB1 hB2 ⟨hzb, hzqm⟩ hzk hhalf hgrp hstartb hkk
      (by omega)
    · constructor
      · intro v hv hP
        rcases (show v = i.val ∨ v = i2.val ∨ (v ≠ i.val ∧ v ≠ i2.val) from by omega)
          with rfl | rfl | ⟨hne1, hne2⟩
        · intro k hk
          rw [hb2oth i.val (by omega) (by omega) k hk, hb1at k hk]
          exact le_trans (hr1 k hk) hB1
        · intro k hk
          rw [hb2at k hk]
          exact le_trans (hr2 k hk) hB2
        · intro k hk
          rw [hb2oth v hv hne2 k hk, hb1oth v hv hne1 k hk]
          exact hgrown v hv (by omega) k hk
      · intro v hv hP k hk
        rw [hb2oth v hv (by omega) k hk, hb1oth v hv (by omega) k hk]
        exact hplain v hv (by omega) k hk
    · intro c hc
      have hcm : c % 16 < 16 := by omega
      have hrec : c = 16 * (c / 16) + c % 16 := by omega
      rw [hb2v c hc, hb1v c hc]
      by_cases h1 : c / 16 = i2.val
      · rw [if_pos (by omega), if_pos (by omega),
          show c - 16 * i2.val = c % 16 from by omega, (hrv (c % 16) hcm).2,
          hlov (c % 16) hcm, hhivv (c % 16) hcm, hzk (c % 16) hcm]
        have e1 : posZ q b (16 * i.val + c % 16) = a0 (c - 16 * half.val) := by
          rw [hval _ (by omega), if_neg (by omega)]
          congr 1
          omega
        have e2 : posZ q b (16 * i2.val + c % 16) = a0 c := by
          rw [show 16 * i2.val + c % 16 = c from by omega, hval c hc, if_neg (by omega)]
        have hzi : c / (2 * (16 * half.val)) = bIdx := by
          rcases hhalf with hh | hh | hh | hh <;>
            simp only [hh] at hgrp hstartb hi hlt h1 i2_post ⊢ <;> omega
        have hhi2 : ¬ (c % (2 * (16 * half.val)) < 16 * half.val) := by
          rcases hhalf with hh | hh | hh | hh <;>
            simp only [hh] at hgrp hstartb hi hlt h1 i2_post ⊢ <;> omega
        rw [e1, e2, gsLvl, if_neg hhi2, hzi, hkk]
      · rw [if_neg (by omega)]
        by_cases h2 : c / 16 = i.val
        · rw [if_pos (by omega), if_pos (by omega),
            show c - 16 * i.val = c % 16 from by omega, (hrv (c % 16) hcm).1,
            hlov (c % 16) hcm, hhivv (c % 16) hcm]
          have e1 : posZ q b (16 * i.val + c % 16) = a0 c := by
            rw [show 16 * i.val + c % 16 = c from by omega, hval c hc, if_neg (by omega)]
          have e2 : posZ q b (16 * i2.val + c % 16) = a0 (c + 16 * half.val) := by
            rw [hval _ (by omega), if_neg (by omega)]
            congr 1
            omega
          have hlo2 : c % (2 * (16 * half.val)) < 16 * half.val := by
            rcases hhalf with hh | hh | hh | hh <;>
              simp only [hh] at hgrp hstartb hi hlt h2 ⊢ <;> omega
          rw [e1, e2, gsLvl, if_pos hlo2]
        · rw [if_neg (by omega), hval c hc]
          by_cases hP : c / 16 < start.val ∨ (start.val ≤ c / 16 ∧ c / 16 < i.val)
              ∨ (start.val + half.val ≤ c / 16 ∧ c / 16 < i.val + half.val)
          · rw [if_pos hP, if_pos (by omega)]
          · rw [if_neg hP, if_neg (by omega)]
  · step*
    rw [if_neg (by scalar_tac)]
    simp only [WP.spec_ok]
    refine ⟨⟨fun v hv hP => hgrown v hv ?_, fun v hv hP => hplain v hv ?_⟩, fun c hc => ?_⟩
    · have hP' : v < start.val + 2 * half.val := hP
      show v < start.val ∨ (start.val ≤ v ∧ v < i.val)
        ∨ (start.val + half.val ≤ v ∧ v < i.val + half.val)
      omega
    · have hP' : ¬ (v < start.val + 2 * half.val) := hP
      show ¬ (v < start.val ∨ (start.val ≤ v ∧ v < i.val)
        ∨ (start.val + half.val ≤ v ∧ v < i.val + half.val))
      omega
    · rw [hval c hc]
      by_cases hP : c / 16 < start.val + 2 * half.val
      · rw [if_pos (by omega), if_pos hP]
      · rw [if_neg (by omega), if_neg hP]
termination_by start.val + half.val - i.val
decreasing_by scalar_decr_tac

/-- One horizontal inverse level: the groups of width `2·half`, each with its own broadcast
`−ζ`.  `k` counts *down*: `hk` says `k + b = 2·nb`, so the `k − 1` this iteration computes is
`gsLvl`'s index `2·nb − 1 − b`.

The negation is a `wrapping_sub` from zero, not `wrapping_neg`: aeneas leaves the latter opaque.
Since the table is centred the subtraction is exact, so `neg_zeta` really is `−ζ`. -/
theorem invntt_block_loop4_loop0_walk (SECOND : Bool) (b : Array I16 256#usize) (qv : Vec256)
    (k half start : Usize) (q : ℕ) (Zb A T B : ℤ) (Rinv : ZMod q)
    (ζ : ℕ → ZMod q) (a0 : ℕ → ZMod q) (nb bIdx nbT : ℕ)
    (hq0 : 0 < (q : ℤ)) (hqlt : (q : ℤ) ≤ 2 ^ 15)
    (hR : ((2 ^ 16 : ℤ) : ZMod q) * Rinv = 1)
    (hQ : ∀ j < 16, (lane16 qv j).toInt = (q : ℤ))
    (hA0 : 0 ≤ A) (hZ0 : 0 ≤ Zb) (hZbfit : Zb < 2 ^ 15) (hsum : 2 * A ≤ 2 ^ 15 - 1)
    (hAZ : 2 * A * Zb < 2 ^ 15 * (q : ℤ))
    (hT : 2 * A * Zb + 2 ^ 15 * (q : ℤ) ≤ 2 ^ 16 * T)
    (hB1 : 2 * A ≤ B) (hB2 : T ≤ B)
    (hzeta : ∀ kk : Usize, kk.val < 256 → ∃ zi : I16,
      backend.crt.zeta SECOND kk = ok zi ∧ |zi.val| ≤ Zb ∧
      (((zi.val : ℤ) : ZMod q)) * Rinv = ζ kk.val)
    (hqinv : ∃ qi : I16, backend.crt.qinv SECOND = ok qi ∧
      (2 ^ 16 : ℤ) ∣ (qi.val * (q : ℤ) - 1))
    (hhalf : half.val = 8 ∨ half.val = 4 ∨ half.val = 2 ∨ half.val = 1)
    (hstartb : start.val = bIdx * (2 * half.val)) (hstart : start.val ≤ 16)
    (hnbT : 16 = nbT * (2 * half.val)) (hnbpos : 0 < nb) (hnbeq : nb = nbT)
    (hk : k.val + bIdx = 2 * nb)
    (hbnd : SplitB b (fun v => v < start.val) A B)
    (hval : ∀ c < 256, posZ q b c =
      if c / 16 < start.val then gsLvl q ζ nb (16 * half.val) a0 c else a0 c) :
    backend.avx2.ntt.invntt_block_loop4_loop0 SECOND b qv k half start
      ⦃ (r : (Array I16 256#usize) × Usize) =>
          BlockBnd r.1 B ∧
          (∀ c < 256, posZ q r.1 c = gsLvl q ζ nb (16 * half.val) a0 c) ∧
          r.2.val + nbT = 2 * nb ⦄ := by
  unfold backend.avx2.ntt.invntt_block_loop4_loop0
  obtain ⟨qi, hqi, hqiu⟩ := hqinv
  by_cases hlt : start.val < 16
  · rw [if_pos (by scalar_tac)]
    have hbIdx : bIdx < nbT := by
      rcases hhalf with h | h | h | h <;> simp only [h] at hstartb hnbT hlt ⊢ <;> omega
    have hnbTle : nbT ≤ 8 := by
      rcases hhalf with h | h | h | h <;> simp only [h] at hnbT <;> omega
    have hkpos : 1 ≤ k.val := by omega
    have hkle : k.val ≤ 16 := by omega
    step*
    obtain ⟨zi, hzi, hzib, hzpsi⟩ := hzeta k1 (by omega)
    rw [hzi, bind_tc_ok]
    have hnegv : (IScalar.wrapping_sub 0#i16 zi).val = -zi.val := by
      rw [IScalar.wrapping_sub_val_eq]
      have h0 : (0#i16 : I16).val = 0 := by scalar_tac
      rw [h0, zero_sub]
      exact bmod16_eq_self (by rw [abs_le] at hzib; omega) (by rw [abs_le] at hzib; omega)
    simp only [core.num.I16.wrapping_sub, lift, bind_tc_ok]
    obtain ⟨z, hz, hzl⟩ := set1_epi16_spec (IScalar.wrapping_sub 0#i16 zi)
    rw [hz, bind_tc_ok, hqi, bind_tc_ok]
    simp only [core.num.I16.wrapping_mul, lift, bind_tc_ok]
    obtain ⟨zq, hzq, hzql⟩ :=
      set1_epi16_spec (IScalar.wrapping_mul (IScalar.wrapping_sub 0#i16 zi) qi)
    rw [hzq, bind_tc_ok]
    have hzlv : ∀ j < 16, (lane16 z j).toInt = -zi.val := by
      intro j hj
      rw [show (lane16 z j).toInt = (IScalar.wrapping_sub 0#i16 zi).val from by
        rw [hzl j hj]; rfl, hnegv]
    have hzqlv : ∀ j < 16, (lane16 zq j).toInt = ((-zi.val) * qi.val).bmod (2 ^ 16) := by
      intro j hj
      rw [show (lane16 zq j).toInt
        = (IScalar.wrapping_mul (IScalar.wrapping_sub 0#i16 zi) qi).val from by
          rw [hzql j hj]; rfl, IScalar.wrapping_mul_val_eq, hnegv]
      rfl
    have hpsi : PsiOk z zq (q : ℤ) Zb := by
      refine ⟨fun j hj => ?_, fun j hj => ?_⟩
      · rw [hzlv j hj, abs_neg]
        exact hzib
      · rw [hzlv j hj, hzqlv j hj]
        exact mont_pair rfl hqiu
    have hzk : ∀ j < 16, laneZ q z j * Rinv = -(ζ k1.val) := by
      intro j hj
      rw [show laneZ q z j = ((-zi.val : ℤ) : ZMod q) from by unfold laneZ; rw [hzlv j hj]]
      push_cast
      rw [neg_mul, hzpsi]
    have hgrp' : start.val + 2 * half.val ≤ 16 := by
      rcases hhalf with h | h | h | h <;> simp only [h] at hstartb ⊢ <;> omega
    have hkk' : 2 * nb - 1 - bIdx = k1.val := by omega
    apply WP.spec_bind (invntt_block_loop4_loop0_loop0_walk b qv half start start z zq q Zb A T B
      Rinv ζ a0 nb k1.val bIdx hq0 hqlt hR hQ hA0 hZ0 hsum hAZ hT hB1 hB2 hpsi hzk hhalf hgrp'
      hstartb hkk' ⟨le_refl _, by omega⟩ ?_ ?_)
    · intro b1 hb1
      obtain ⟨i3, hi3, hi3v⟩ := WP.spec_imp_exists
        (Std.Usize.mul_spec (x := 2#usize) (y := half) (by scalar_tac))
      rw [hi3, bind_tc_ok]
      obtain ⟨start1, hs1, hs1v⟩ := WP.spec_imp_exists
        (Std.Usize.add_spec (x := start) (y := i3) (by scalar_tac))
      rw [hs1, bind_tc_ok]
      have hi3n : i3.val = 2 * half.val := by scalar_tac
      have hs1n : start1.val = start.val + 2 * half.val := by omega
      apply invntt_block_loop4_loop0_walk SECOND b1 qv k1 half start1 q Zb A T B Rinv ζ a0 nb
        (bIdx + 1) nbT hq0 hqlt hR hQ hA0 hZ0 hZbfit hsum hAZ hT hB1 hB2 hzeta ⟨qi, hqi, hqiu⟩
        hhalf
        (by rcases hhalf with h | h | h | h <;> simp only [h] at hstartb hs1n ⊢ <;> omega)
        (by omega) hnbT hnbpos hnbeq (by omega)
      · obtain ⟨⟨hg, hp⟩, -⟩ := hb1
        refine ⟨fun v hv hP => hg v hv ?_, fun v hv hP => hp v hv ?_⟩
        · have hP' : v < start1.val := hP
          show v < start.val + 2 * half.val
          omega
        · have hP' : ¬ (v < start1.val) := hP
          show ¬ (v < start.val + 2 * half.val)
          omega
      · intro c hc
        rw [hb1.2 c hc]
        by_cases hP : c / 16 < start.val + 2 * half.val
        · rw [if_pos hP, if_pos (by omega)]
        · rw [if_neg hP, if_neg (by omega)]
    · obtain ⟨hg, hp⟩ := hbnd
      refine ⟨fun v hv hP => hg v hv ?_, fun v hv hP => hp v hv ?_⟩
      · have hP' : v < start.val ∨ (start.val ≤ v ∧ v < start.val)
            ∨ (start.val + half.val ≤ v ∧ v < start.val + half.val) := hP
        show v < start.val
        omega
      · have hP' : ¬ (v < start.val ∨ (start.val ≤ v ∧ v < start.val)
            ∨ (start.val + half.val ≤ v ∧ v < start.val + half.val)) := hP
        show ¬ (v < start.val)
        omega
    · intro c hc
      rw [hval c hc]
      by_cases hP : c / 16 < start.val
      · rw [if_pos hP, if_pos (by omega)]
      · rw [if_neg hP, if_neg (by omega)]
  · rw [if_neg (by scalar_tac)]
    simp only [WP.spec_ok]
    refine ⟨?_, ?_, ?_⟩
    · rw [blockBnd_iff]
      intro v hv
      exact hbnd.1 v hv (by omega)
    · intro c hc
      rw [hval c hc, if_pos (by omega)]
    · rcases hhalf with h | h | h | h <;>
        simp only [h] at hstartb hnbT ⊢ <;> omega
termination_by 16 - start.val
decreasing_by scalar_decr_tac

/-! ## The horizontal section, all four levels

`half` runs `1, 2, 4, 8` and the loop re-centres once, after the `half = 2` level (the code tests
`half1 = 4`).  That is what makes the schedule fit: Gentleman-Sande doubles the sum path, so two
levels take a centred block to `4·(q/2)`, and a third would overflow the lane. -/

/-- `Usize` multiplication of two literals.  Not `rfl`: the product carries an overflow check
against the platform-opaque `Usize.max`. -/
theorem usize_mul_lit {a b c : Usize} (hc : a.val * b.val ≤ Usize.max)
    (h : a.val * b.val = c.val) : (a * b : Result Usize) = ok c := by
  obtain ⟨z, hz, hzv⟩ := WP.spec_imp_exists (Std.Usize.mul_spec (x := a) (y := b) hc)
  rw [hz, UScalar.eq_of_val_eq (show z.val = c.val by rw [hzv, h])]

/-- `SplitB` before a level runs: nothing has grown yet. -/
theorem initSplitB {b : Array I16 256#usize} {A B : ℤ} {P : ℕ → Prop}
    (hP : ∀ v, ¬ P v) (hb : BlockBnd b A) : SplitB b P A B :=
  ⟨fun v _ h => absurd h (hP v), fun v hv _ => (blockBnd_iff b A).mp hb v hv⟩

/-- The four horizontal Gentleman-Sande layers, composed.  `half = 1` runs first, so it is the
innermost. -/
noncomputable def invH (q : ℕ) (ζ : ℕ → ZMod q) (f : ℕ → ZMod q) : ℕ → ZMod q :=
  gsLvl q ζ 1 128 (gsLvl q ζ 2 64 (gsLvl q ζ 4 32 (gsLvl q ζ 8 16 f)))

/-- **The horizontal section.**  Two `(A, T, B)` triples suffice: the re-centring pass in the
middle returns the block to `A0`, so levels 3 and 4 repeat levels 1 and 2's arithmetic. -/
theorem invntt_block_loop4_walk (SECOND : Bool) (b : Array I16 256#usize) (qv bm round : Vec256)
    (q : ℕ) (Zb A0 T1 B1 T2 B2 M : ℤ) (Rinv : ZMod q) (ζ : ℕ → ZMod q) (f : ℕ → ZMod q)
    (hq0 : 0 < (q : ℤ)) (hqlt : (q : ℤ) ≤ 2 ^ 15)
    (hR : ((2 ^ 16 : ℤ) : ZMod q) * Rinv = 1)
    (hQ : ∀ i < 16, (lane16 qv i).toInt = (q : ℤ))
    (hM : ∀ i < 16, (lane16 bm i).toInt = M)
    (hRnd : ∀ i < 16, (lane16 round i).toInt = 2 ^ 10)
    (hQlt14 : (q : ℤ) < 2 ^ 14) (hQodd : ¬ (2 ∣ (q : ℤ)))
    (hMpos : 0 < M) (hMlt : M < 2 ^ 15) (hD : |2 ^ 27 - (q : ℤ) * M| ≤ 2047)
    (hA0 : 0 ≤ A0) (hbar0 : ((q : ℤ) - 1) / 2 ≤ A0)
    (hZ0 : 0 ≤ Zb) (hZbfit : Zb < 2 ^ 15)
    (hs1 : 2 * A0 ≤ 2 ^ 15 - 1) (hz1 : 2 * A0 * Zb < 2 ^ 15 * (q : ℤ))
    (ht1 : 2 * A0 * Zb + 2 ^ 15 * (q : ℤ) ≤ 2 ^ 16 * T1)
    (hb11 : 2 * A0 ≤ B1) (hb12 : T1 ≤ B1)
    (hs2 : 2 * B1 ≤ 2 ^ 15 - 1) (hz2 : 2 * B1 * Zb < 2 ^ 15 * (q : ℤ))
    (ht2 : 2 * B1 * Zb + 2 ^ 15 * (q : ℤ) ≤ 2 ^ 16 * T2)
    (hb21 : 2 * B1 ≤ B2) (hb22 : T2 ≤ B2)
    (hzeta : ∀ kk : Usize, kk.val < 256 → ∃ zi : I16,
      backend.crt.zeta SECOND kk = ok zi ∧ |zi.val| ≤ Zb ∧
      (((zi.val : ℤ) : ZMod q)) * Rinv = ζ kk.val)
    (hqinv : ∃ qi : I16, backend.crt.qinv SECOND = ok qi ∧
      (2 ^ 16 : ℤ) ∣ (qi.val * (q : ℤ) - 1))
    (hb : BlockBnd b A0) (hv : ∀ c < 256, posZ q b c = f c) :
    backend.avx2.ntt.invntt_block_loop4 SECOND b qv bm round 16#usize 1#usize
      ⦃ (r : Array I16 256#usize) =>
          BlockBnd r B2 ∧ ∀ c < 256, posZ q r c = invH q ζ f c ⦄ := by
  have hbar : ∀ (bb : Array I16 256#usize),
      backend.avx2.ntt.barrett_block bb bm round qv
        ⦃ (r : Array I16 256#usize) =>
            BlockBnd r A0 ∧ ∀ c < 256, posZ q r c = posZ q bb c ⦄ := by
    intro bb
    exact spec_and
      (WP.spec_mono (barrett_block_bnd bb bm round qv (q : ℤ) M hQ hM hRnd hq0 hQlt14 hQodd
        hMpos hMlt hD) (fun r hr => hr.mono hbar0))
      (barrett_block_val bb bm round qv q M hQ hM hRnd hq0 hQlt14 hQodd hMpos hMlt hD)
  have e1 : (16 : ℕ) * (1#usize).val = 16 := by scalar_tac
  have e2 : (16 : ℕ) * (2#usize).val = 32 := by scalar_tac
  have e4 : (16 : ℕ) * (4#usize).val = 64 := by scalar_tac
  have e8 : (16 : ℕ) * (8#usize).val = 128 := by scalar_tac
  -- level 1, `half = 1`
  unfold backend.avx2.ntt.invntt_block_loop4
  rw [if_pos (by scalar_tac)]
  apply WP.spec_bind (invntt_block_loop4_loop0_walk SECOND b qv 16#usize 1#usize 0#usize q Zb A0
    T1 B1 Rinv ζ f 8 0 8 hq0 hqlt hR hQ hA0 hZ0 hZbfit hs1 hz1 ht1 hb11 hb12 hzeta hqinv
    (by norm_num) (by scalar_tac) (by scalar_tac) (by scalar_tac) (by norm_num) rfl
    (by scalar_tac) (initSplitB (by simp) hb) (by intro c hc; rw [hv c hc, if_neg (by simp)]))
  rintro ⟨b1, k1⟩ ⟨hb1, hv1, hk1⟩
  simp only at hb1 hv1 hk1
  rw [e1] at hv1
  show (do let half1 ← 1#usize * 2#usize
           if half1 = 4#usize then
             do let b2 ← backend.avx2.ntt.barrett_block b1 bm round qv
                backend.avx2.ntt.invntt_block_loop4 SECOND b2 qv bm round k1 half1
           else backend.avx2.ntt.invntt_block_loop4 SECOND b1 qv bm round k1 half1)
      ⦃ (r : Array I16 256#usize) =>
          BlockBnd r B2 ∧ ∀ c < 256, posZ q r c = invH q ζ f c ⦄
  rw [show (1#usize * 2#usize : Result Usize) = ok 2#usize from
      usize_mul_lit (by scalar_tac) (by scalar_tac), bind_tc_ok,
    if_neg (by decide)]
  have hk1v : k1.val = 8 := by omega
  -- level 2, `half = 2`, then the re-centring pass
  unfold backend.avx2.ntt.invntt_block_loop4
  rw [if_pos (by scalar_tac)]
  apply WP.spec_bind (invntt_block_loop4_loop0_walk SECOND b1 qv k1 2#usize 0#usize q Zb B1
    T2 B2 Rinv ζ (gsLvl q ζ 8 16 f) 4 0 4 hq0 hqlt hR hQ (by omega) hZ0 hZbfit hs2 hz2 ht2 hb21
    hb22 hzeta hqinv (by norm_num) (by scalar_tac) (by scalar_tac) (by scalar_tac) (by norm_num)
    rfl (by omega) (initSplitB (by simp) hb1)
    (by intro c hc; rw [hv1 c hc, if_neg (by simp)]))
  rintro ⟨b2, k2⟩ ⟨hb2, hv2, hk2⟩
  simp only at hb2 hv2 hk2
  rw [e2] at hv2
  show (do let half1 ← 2#usize * 2#usize
           if half1 = 4#usize then
             do let b3 ← backend.avx2.ntt.barrett_block b2 bm round qv
                backend.avx2.ntt.invntt_block_loop4 SECOND b3 qv bm round k2 half1
           else backend.avx2.ntt.invntt_block_loop4 SECOND b2 qv bm round k2 half1)
      ⦃ (r : Array I16 256#usize) =>
          BlockBnd r B2 ∧ ∀ c < 256, posZ q r c = invH q ζ f c ⦄
  rw [show (2#usize * 2#usize : Result Usize) = ok 4#usize from
      usize_mul_lit (by scalar_tac) (by scalar_tac), bind_tc_ok, if_pos rfl]
  apply WP.spec_bind (hbar b2)
  rintro b3 ⟨hb3, hv3⟩
  have hk2v : k2.val = 4 := by omega
  -- level 3, `half = 4`, from a centred block again
  unfold backend.avx2.ntt.invntt_block_loop4
  rw [if_pos (by scalar_tac)]
  apply WP.spec_bind (invntt_block_loop4_loop0_walk SECOND b3 qv k2 4#usize 0#usize q Zb A0
    T1 B1 Rinv ζ (gsLvl q ζ 4 32 (gsLvl q ζ 8 16 f)) 2 0 2 hq0 hqlt hR hQ hA0 hZ0 hZbfit hs1 hz1
    ht1 hb11 hb12 hzeta hqinv (by norm_num) (by scalar_tac) (by scalar_tac) (by scalar_tac)
    (by norm_num) rfl (by omega) (initSplitB (by simp) hb3)
    (by intro c hc; rw [hv3 c hc, hv2 c hc, if_neg (by simp)]))
  rintro ⟨b4, k3⟩ ⟨hb4, hv4, hk3⟩
  simp only at hb4 hv4 hk3
  rw [e4] at hv4
  show (do let half1 ← 4#usize * 2#usize
           if half1 = 4#usize then
             do let b5 ← backend.avx2.ntt.barrett_block b4 bm round qv
                backend.avx2.ntt.invntt_block_loop4 SECOND b5 qv bm round k3 half1
           else backend.avx2.ntt.invntt_block_loop4 SECOND b4 qv bm round k3 half1)
      ⦃ (r : Array I16 256#usize) =>
          BlockBnd r B2 ∧ ∀ c < 256, posZ q r c = invH q ζ f c ⦄
  rw [show (4#usize * 2#usize : Result Usize) = ok 8#usize from
      usize_mul_lit (by scalar_tac) (by scalar_tac), bind_tc_ok,
    if_neg (by decide)]
  have hk3v : k3.val = 2 := by omega
  -- level 4, `half = 8`
  unfold backend.avx2.ntt.invntt_block_loop4
  rw [if_pos (by scalar_tac)]
  apply WP.spec_bind (invntt_block_loop4_loop0_walk SECOND b4 qv k3 8#usize 0#usize q Zb B1
    T2 B2 Rinv ζ (gsLvl q ζ 2 64 (gsLvl q ζ 4 32 (gsLvl q ζ 8 16 f))) 1 0 1 hq0 hqlt hR hQ
    (by omega) hZ0 hZbfit hs2 hz2 ht2 hb21 hb22 hzeta hqinv (by norm_num) (by scalar_tac)
    (by scalar_tac) (by scalar_tac) (by norm_num) rfl (by omega) (initSplitB (by simp) hb4)
    (by intro c hc; rw [hv4 c hc, if_neg (by simp)]))
  rintro ⟨b5, k4⟩ ⟨hb5, hv5, hk4⟩
  simp only at hb5 hv5 hk4
  rw [e8] at hv5
  show (do let half1 ← 8#usize * 2#usize
           if half1 = 4#usize then
             do let b6 ← backend.avx2.ntt.barrett_block b5 bm round qv
                backend.avx2.ntt.invntt_block_loop4 SECOND b6 qv bm round k4 half1
           else backend.avx2.ntt.invntt_block_loop4 SECOND b5 qv bm round k4 half1)
      ⦃ (r : Array I16 256#usize) =>
          BlockBnd r B2 ∧ ∀ c < 256, posZ q r c = invH q ζ f c ⦄
  rw [show (8#usize * 2#usize : Result Usize) = ok 16#usize from
      usize_mul_lit (by scalar_tac) (by scalar_tac), bind_tc_ok,
    if_neg (by decide)]
  -- `half = 16`: the loop is done
  unfold backend.avx2.ntt.invntt_block_loop4
  rw [if_neg (by scalar_tac)]
  simp only [WP.spec_ok]
  exact ⟨hb5, fun c hc => by rw [hv5 c hc, invH]⟩

/-! ## The final Montgomery scaling

One `mont_mul` per vector by `INVNTT_SCALE`, which carries both the `1/256` and the Montgomery
factor.  `mont_mul` is already specified lane-wise; these two wrappers say what it does to a
whole vector's bound and to its residues. -/

/-- `mont_mul`'s output bound, from the sharp conjunct of `mont_mul_lane_spec`. -/
theorem mont_mul_bnd (a z zq qv : Vec256) (Q Zb A T : ℤ)
    (hQ : ∀ i < 16, (lane16 qv i).toInt = Q) (hQpos : 0 < Q) (hQlt : Q ≤ 2 ^ 15)
    (hzq : ∀ i < 16, (2 ^ 16 : ℤ) ∣ ((lane16 zq i).toInt * Q - (lane16 z i).toInt))
    (ha : VecBnd a A) (hz : VecBnd z Zb) (hA0 : 0 ≤ A)
    (hAZ : A * Zb < 2 ^ 15 * Q) (hT : A * Zb + 2 ^ 15 * Q ≤ 2 ^ 16 * T) :
    backend.avx2.ntt.mont_mul a z zq qv ⦃ (c : Vec256) => VecBnd c T ⦄ := by
  have hbnd : ∀ i < 16, |(lane16 a i).toInt * (lane16 z i).toInt| < 2 ^ 15 * Q := by
    intro i hi'
    rw [abs_mul]
    calc |(lane16 a i).toInt| * |(lane16 z i).toInt| ≤ A * Zb :=
          mul_le_mul (ha i hi') (hz i hi') (abs_nonneg _) hA0
      _ < 2 ^ 15 * Q := hAZ
  apply WP.spec_mono (mont_mul_lane_spec a z zq qv Q hQ hQpos hQlt hzq hbnd)
  intro c hc i hi'
  have hsharp := (hc i hi').2.2.2
  have hle : |(lane16 a i).toInt| * |(lane16 z i).toInt| ≤ A * Zb :=
    mul_le_mul (ha i hi') (hz i hi') (abs_nonneg _) hA0
  have : (2:ℤ) ^ 16 * |(lane16 c i).toInt| ≤ 2 ^ 16 * T := by linarith
  exact le_of_mul_le_mul_left this (by norm_num)

/-- `mont_mul` as residues: the `2⁻¹⁶` is why the factor that appears is `z · R⁻¹`. -/
theorem mont_mul_val (a z zq qv : Vec256) (q : ℕ) (Zb A : ℤ) (Rinv : ZMod q)
    (hq0 : 0 < (q : ℤ)) (hqlt : (q : ℤ) ≤ 2 ^ 15)
    (hR : ((2 ^ 16 : ℤ) : ZMod q) * Rinv = 1)
    (hQ : ∀ i < 16, (lane16 qv i).toInt = (q : ℤ))
    (hzq : ∀ i < 16, (2 ^ 16 : ℤ) ∣ ((lane16 zq i).toInt * (q : ℤ) - (lane16 z i).toInt))
    (ha : VecBnd a A) (hz : VecBnd z Zb) (hA0 : 0 ≤ A)
    (hAZ : A * Zb < 2 ^ 15 * (q : ℤ)) :
    backend.avx2.ntt.mont_mul a z zq qv
      ⦃ (c : Vec256) => ∀ i < 16, laneZ q c i = laneZ q z i * Rinv * laneZ q a i ⦄ := by
  have hbnd : ∀ i < 16, |(lane16 a i).toInt * (lane16 z i).toInt| < 2 ^ 15 * (q : ℤ) := by
    intro i hi'
    rw [abs_mul]
    calc |(lane16 a i).toInt| * |(lane16 z i).toInt| ≤ A * Zb :=
          mul_le_mul (ha i hi') (hz i hi') (abs_nonneg _) hA0
      _ < 2 ^ 15 * (q : ℤ) := hAZ
  apply WP.spec_mono (mont_mul_lane_spec a z zq qv (q : ℤ) hQ hq0 hqlt hzq hbnd)
  intro t ht i hi'
  obtain ⟨c, hc⟩ := (ht i hi').1
  have hcast : (((lane16 t i).toInt * 2 ^ 16 - (lane16 a i).toInt * (lane16 z i).toInt : ℤ)
      : ZMod q) = 0 := by
    rw [(ZMod.intCast_zmod_eq_zero_iff_dvd _ q)]
    exact ⟨c, hc⟩
  push_cast at hcast
  have hmul : laneZ q t i * ((2 ^ 16 : ℤ) : ZMod q) = laneZ q a i * laneZ q z i := by
    unfold laneZ
    push_cast
    linear_combination hcast
  calc laneZ q t i = laneZ q t i * (((2 ^ 16 : ℤ) : ZMod q) * Rinv) := by rw [hR]; ring
    _ = (laneZ q t i * ((2 ^ 16 : ℤ) : ZMod q)) * Rinv := by ring
    _ = (laneZ q a i * laneZ q z i) * Rinv := by rw [hmul]
    _ = laneZ q z i * Rinv * laneZ q a i := by ring

/-- **The scaling pass.**  Sixteen `mont_mul`s by the same broadcast constant, so the whole block
is multiplied by one residue `σ`. -/
theorem invntt_block_loop5_walk (iter : core.ops.range.Range Usize) (b : Array I16 256#usize)
    (qv scale scale_q : Vec256) (q : ℕ) (Zb A T : ℤ) (Rinv : ZMod q) (σ : ZMod q)
    (a0 : ℕ → ZMod q)
    (hq0 : 0 < (q : ℤ)) (hqlt : (q : ℤ) ≤ 2 ^ 15)
    (hR : ((2 ^ 16 : ℤ) : ZMod q) * Rinv = 1)
    (hQ : ∀ i < 16, (lane16 qv i).toInt = (q : ℤ))
    (hsq : ∀ i < 16, (2 ^ 16 : ℤ) ∣ ((lane16 scale_q i).toInt * (q : ℤ) - (lane16 scale i).toInt))
    (hsb : VecBnd scale Zb) (hσ : ∀ i < 16, laneZ q scale i * Rinv = σ)
    (hA0 : 0 ≤ A) (hAZ : A * Zb < 2 ^ 15 * (q : ℤ))
    (hT : A * Zb + 2 ^ 15 * (q : ℤ) ≤ 2 ^ 16 * T)
    (hend : iter.«end».val = 16)
    (hbnd : SplitB b (fun v => v < iter.start.val) A T)
    (hval : ∀ c < 256, posZ q b c = if c / 16 < iter.start.val then σ * a0 c else a0 c) :
    backend.avx2.ntt.invntt_block_loop5 iter b qv scale scale_q
      ⦃ (r : Array I16 256#usize) =>
          BlockBnd r T ∧ ∀ c < 256, posZ q r c = σ * a0 c ⦄ := by
  unfold backend.avx2.ntt.invntt_block_loop5
  obtain ⟨hgrown, hplain⟩ := hbnd
  by_cases hlt : iter.start.val < iter.«end».val
  · let* ⟨ o, iter1, ho, hstart', hend' ⟩ ← core.iter.range.IteratorRange.next_Usize_some_spec
    rw [ho]; simp only
    obtain ⟨v, hvl, hvb⟩ := load_i16_bndAt b iter.start (by omega)
      (hplain iter.start.val (by omega) (by omega))
    obtain ⟨v', hvl', hvv⟩ := load_posZ q b iter.start (by omega)
    rw [show v = v' from by rw [hvl] at hvl'; injection hvl'] at hvb
    rw [hvl', bind_tc_ok]
    apply WP.spec_bind (spec_and
      (mont_mul_bnd v' scale scale_q qv (q : ℤ) Zb A T hQ hq0 hqlt hsq hvb hsb hA0 hAZ hT)
      (mont_mul_val v' scale scale_q qv q Zb A Rinv hq0 hqlt hR hQ hsq hvb hsb hA0 hAZ))
    intro v1 ⟨hv1b, hv1v⟩
    obtain ⟨b1, hb1, hb1at, hb1oth⟩ := store_i16_at b iter.start v1 (by omega)
    obtain ⟨b1', hb1', hb1v⟩ := store_posZ q b iter.start v1 (by omega)
    rw [show b1 = b1' from by rw [hb1] at hb1'; injection hb1'] at hb1at hb1oth
    rw [hb1', bind_tc_ok]
    apply invntt_block_loop5_walk iter1 b1' qv scale scale_q q Zb A T Rinv σ a0 hq0 hqlt hR hQ
      hsq hsb hσ hA0 hAZ hT (by rw [hend']; exact hend)
    · constructor
      · intro u hu hP
        rcases (show u = iter.start.val ∨ u ≠ iter.start.val from by omega) with rfl | hne
        · intro k hk
          rw [hb1at k hk]
          exact hv1b k hk
        · intro k hk
          rw [hb1oth u hu hne k hk]
          exact hgrown u hu (by omega) k hk
      · intro u hu hP k hk
        rw [hb1oth u hu (by omega) k hk]
        exact hplain u hu (by omega) k hk
    · intro c hc
      have hcm : c % 16 < 16 := by omega
      rw [hb1v c hc]
      by_cases h1 : c / 16 = iter.start.val
      · rw [if_pos (by omega), if_pos (by omega),
          show c - 16 * iter.start.val = c % 16 from by omega, hv1v (c % 16) hcm,
          hvv (c % 16) hcm, hσ (c % 16) hcm,
          show 16 * iter.start.val + c % 16 = c from by omega, hval c hc, if_neg (by omega)]
      · rw [if_neg (by omega), hval c hc]
        by_cases hP : c / 16 < iter.start.val
        · rw [if_pos hP, if_pos (by omega)]
        · rw [if_neg hP, if_neg (by omega)]
  · let* ⟨ o, iter1, hnone, _ ⟩ ← core.iter.range.IteratorRange.next_Usize_none_spec
    rw [hnone]; simp only [WP.spec_ok]
    refine ⟨?_, ?_⟩
    · rw [blockBnd_iff]
      intro u hu
      exact hgrown u hu (by omega)
    · intro c hc
      rw [hval c hc, if_pos (by omega)]
termination_by iter.«end».val - iter.start.val
decreasing_by scalar_decr_tac

/-! ## The whole inverse transform

Eight Gentleman-Sande layers: a transpose, four vertical, a transpose back, four horizontal, then
the scaling.  The four `barrett_block` passes are transparent to the value view, which is what
lets the growth schedule sit inside the transform without disturbing its invariant. -/

/-- The four vertical layers, composed.  `len = 1` runs first, so it is the innermost. -/
noncomputable def invV (q : ℕ) (ζ : ℕ → ZMod q) (f : ℕ → ZMod q) : ℕ → ZMod q :=
  gsLvl q ζ 16 8 (gsLvl q ζ 32 4 (gsLvl q ζ 64 2 (gsLvl q ζ 128 1 f)))

/-- All eight layers. -/
noncomputable def invAll (q : ℕ) (ζ : ℕ → ZMod q) (f : ℕ → ZMod q) : ℕ → ZMod q :=
  invH q ζ (invV q ζ f)

/-- **`invntt_block`, as residues and as a bound**, generic in the prime. -/
theorem invntt_block_walk (SECOND : Bool) (b : Array I16 256#usize)
    (q : ℕ) (Zb Ain Ti1 Bi1 Ti2 Bi2 A0 T1 B1 T2 B2 Tf M : ℤ) (Rinv : ZMod q) (σ : ZMod q)
    (ζ f : ℕ → ZMod q)
    (qc mc sc : I16)
    (hqc : backend.crt.q SECOND = ok qc) (hqcv : qc.val = (q : ℤ))
    (hmc : backend.crt.barrett_m SECOND = ok mc) (hmcv : mc.val = M)
    (hsc : backend.crt.invntt_scale SECOND = ok sc)
    (hscb : |sc.val| ≤ Zb) (hscv : ((sc.val : ℤ) : ZMod q) * Rinv = σ)
    (hq0 : 0 < (q : ℤ)) (hqlt : (q : ℤ) ≤ 2 ^ 15)
    (hR : ((2 ^ 16 : ℤ) : ZMod q) * Rinv = 1)
    (hQlt14 : (q : ℤ) < 2 ^ 14) (hQodd : ¬ (2 ∣ (q : ℤ)))
    (hMpos : 0 < M) (hMlt : M < 2 ^ 15) (hD : |2 ^ 27 - (q : ℤ) * M| ≤ 2047)
    (hA0 : 0 ≤ A0) (hbar0 : ((q : ℤ) - 1) / 2 ≤ A0)
    (hZ0 : 0 ≤ Zb) (hZbfit : Zb < 2 ^ 15)
    (hs1 : 2 * A0 ≤ 2 ^ 15 - 1) (hz1 : 2 * A0 * Zb < 2 ^ 15 * (q : ℤ))
    (ht1 : 2 * A0 * Zb + 2 ^ 15 * (q : ℤ) ≤ 2 ^ 16 * T1)
    (hb11 : 2 * A0 ≤ B1) (hb12 : T1 ≤ B1)
    (hs2 : 2 * B1 ≤ 2 ^ 15 - 1) (hz2 : 2 * B1 * Zb < 2 ^ 15 * (q : ℤ))
    (ht2 : 2 * B1 * Zb + 2 ^ 15 * (q : ℤ) ≤ 2 ^ 16 * T2)
    (hb21 : 2 * B1 ≤ B2) (hb22 : T2 ≤ B2)
    (hAin : 0 ≤ Ain)
    (hsi1 : 2 * Ain ≤ 2 ^ 15 - 1) (hzi1 : 2 * Ain * Zb < 2 ^ 15 * (q : ℤ))
    (hti1 : 2 * Ain * Zb + 2 ^ 15 * (q : ℤ) ≤ 2 ^ 16 * Ti1)
    (hbi11 : 2 * Ain ≤ Bi1) (hbi12 : Ti1 ≤ Bi1)
    (hsi2 : 2 * Bi1 ≤ 2 ^ 15 - 1) (hzi2 : 2 * Bi1 * Zb < 2 ^ 15 * (q : ℤ))
    (hti2 : 2 * Bi1 * Zb + 2 ^ 15 * (q : ℤ) ≤ 2 ^ 16 * Ti2)
    (hbi21 : 2 * Bi1 ≤ Bi2) (hbi22 : Ti2 ≤ Bi2)
    (hzf : B2 * Zb < 2 ^ 15 * (q : ℤ)) (htf : B2 * Zb + 2 ^ 15 * (q : ℤ) ≤ 2 ^ 16 * Tf)
    (hzeta : ∀ kk : Usize, kk.val < 256 → ∃ zi : I16,
      backend.crt.zeta SECOND kk = ok zi ∧ |zi.val| ≤ Zb ∧
      (((zi.val : ℤ) : ZMod q)) * Rinv = ζ kk.val)
    (hqinv : ∃ qi : I16, backend.crt.qinv SECOND = ok qi ∧
      (2 ^ 16 : ℤ) ∣ (qi.val * (q : ℤ) - 1))
    (htbl1 : ∀ h : Usize, h.val < 8 → ∃ z zq,
      (if SECOND then (do let t ← backend.avx2.ntt.INV1_Q2; backend.avx2.ntt.ld_tbl t h)
       else (do let t ← backend.avx2.ntt.INV1_Q1; backend.avx2.ntt.ld_tbl t h))
        = ok (z, zq) ∧ PsiOk z zq (q : ℤ) Zb ∧
        ∀ k < 16, laneZ q z k * Rinv = -(ζ (255 - h.val - 8 * k)))
    (htbl2 : ∀ h : Usize, h.val < 4 → ∃ z zq,
      (if SECOND then (do let t ← backend.avx2.ntt.INV2_Q2; backend.avx2.ntt.ld_tbl t h)
       else (do let t ← backend.avx2.ntt.INV2_Q1; backend.avx2.ntt.ld_tbl t h))
        = ok (z, zq) ∧ PsiOk z zq (q : ℤ) Zb ∧
        ∀ k < 16, laneZ q z k * Rinv = -(ζ (127 - h.val - 4 * k)))
    (htbl4 : ∀ h : Usize, h.val < 2 → ∃ z zq,
      (if SECOND then (do let t ← backend.avx2.ntt.INV4_Q2; backend.avx2.ntt.ld_tbl t h)
       else (do let t ← backend.avx2.ntt.INV4_Q1; backend.avx2.ntt.ld_tbl t h))
        = ok (z, zq) ∧ PsiOk z zq (q : ℤ) Zb ∧
        ∀ k < 16, laneZ q z k * Rinv = -(ζ (63 - h.val - 2 * k)))
    (htbl8 : ∃ z zq,
      (if SECOND then (do let t ← backend.avx2.ntt.INV8_Q2; backend.avx2.ntt.ld_tbl t 0#usize)
       else (do let t ← backend.avx2.ntt.INV8_Q1; backend.avx2.ntt.ld_tbl t 0#usize))
        = ok (z, zq) ∧ PsiOk z zq (q : ℤ) Zb ∧ ∀ k < 16, laneZ q z k * Rinv = -(ζ (31 - k)))
    (hb : BlockBnd b Ain) (hv : ∀ c < 256, posZ q b c = f c) :
    backend.avx2.ntt.invntt_block SECOND b
      ⦃ (r : Array I16 256#usize) =>
          BlockBnd r Tf ∧ ∀ c < 256, posZ q r c = σ * invAll q ζ f c ⦄ := by
  obtain ⟨qi, hqi, hqiu⟩ := hqinv
  unfold backend.avx2.ntt.invntt_block
  rw [hqc, bind_tc_ok]
  obtain ⟨qv, hqv, hqvl⟩ := set1_epi16_spec qc
  rw [hqv, bind_tc_ok, hmc, bind_tc_ok]
  obtain ⟨bm, hbm, hbml⟩ := set1_epi16_spec mc
  rw [hbm, bind_tc_ok]
  have hSH : (backend.crt.BARRETT_SH : I32).val = 11 := by
    simp only [backend.crt.BARRETT_SH]; rfl
  step*
  have hi2e : i2 = 10#i32 := IScalar.eq_of_val_eq (by rw [i2_post, hSH]; rfl)
  rw [hi2e, show (1#i16 <<< (10#i32) : Result I16) = ok 1024#i16 from rfl, bind_tc_ok]
  obtain ⟨rnd, hrnd, hrndl⟩ := set1_epi16_spec 1024#i16
  rw [hrnd, bind_tc_ok]
  have hQ : ∀ j < 16, (lane16 qv j).toInt = (q : ℤ) := fun j hj => by
    rw [hqvl j hj]; exact hqcv
  have hM : ∀ j < 16, (lane16 bm j).toInt = M := fun j hj => by
    rw [hbml j hj]; exact hmcv
  have hRnd : ∀ j < 16, (lane16 rnd j).toInt = 2 ^ 10 := fun j hj => by
    rw [hrndl j hj]; decide
  have hbar : ∀ (bb : Array I16 256#usize),
      backend.avx2.ntt.barrett_block bb bm rnd qv
        ⦃ (r : Array I16 256#usize) =>
            BlockBnd r A0 ∧ ∀ c < 256, posZ q r c = posZ q bb c ⦄ := by
    intro bb
    exact spec_and
      (WP.spec_mono (barrett_block_bnd bb bm rnd qv (q : ℤ) M hQ hM hRnd hq0 hQlt14 hQodd
        hMpos hMlt hD) (fun r hr => hr.mono hbar0))
      (barrett_block_val bb bm rnd qv q M hQ hM hRnd hq0 hQlt14 hQodd hMpos hMlt hD)
  -- into coefficient coordinates
  apply WP.spec_bind (spec_and (transpose16_bnd b hb) (transpose16_tpos q b))
  rintro b1 ⟨hb1, ht1'⟩
  have hv1 : ∀ c < 256, tposZ q b1 c = f c := fun c hc => by rw [ht1' c hc, hv c hc]
  -- the four vertical levels, with a re-centring pass in the middle
  apply WP.spec_bind (invntt_block_loop0_walk SECOND { start := 0#usize, «end» := 8#usize } b1 qv
    q Zb Ain Ti1 Bi1 Rinv ζ f hq0 hqlt hR hQ hAin hZ0 hsi1 hzi1 hti1 hbi11 hbi12 htbl1 rfl
    (initSplitB (by simp) hb1) (by intro c hc; rw [hv1 c hc, if_neg (by simp)]))
  rintro b2 ⟨hb2, hv2⟩
  apply WP.spec_bind (invntt_block_loop1_walk SECOND { start := 0#usize, «end» := 4#usize } b2 qv
    q Zb Bi1 Ti2 Bi2 Rinv ζ (gsLvl q ζ 128 1 f) hq0 hqlt hR hQ (by omega) hZ0 hsi2 hzi2 hti2
    hbi21 hbi22 htbl2 rfl (by decide) (initSplitB (by simp) hb2)
    (by intro c hc; rw [hv2 c hc, if_neg (by simp)]))
  rintro b3 ⟨hb3, hv3⟩
  apply WP.spec_bind (spec_and (WP.spec_mono (hbar b3) (fun r hr => hr.1))
    (WP.spec_mono (hbar b3) (fun r hr => hr.2)))
  rintro b4 ⟨hb4, hv4⟩
  apply WP.spec_bind (invntt_block_loop2_walk SECOND { start := 0#usize, «end» := 2#usize } b4 qv
    q Zb A0 T1 B1 Rinv ζ (gsLvl q ζ 64 2 (gsLvl q ζ 128 1 f)) hq0 hqlt hR hQ hA0 hZ0 hs1 hz1 ht1
    hb11 hb12 htbl4 rfl (by decide) (initSplitB (by simp) hb4)
    (by intro c hc
        rw [show tposZ q b4 c = posZ q b4 (16 * (c % 16) + c / 16) from rfl, hv4 _ (by omega),
          show posZ q b3 (16 * (c % 16) + c / 16) = tposZ q b3 c from rfl, hv3 c hc,
          if_neg (by simp)]))
  rintro b5 ⟨hb5, hv5⟩
  apply WP.spec_bind (invntt_block_loop3_walk SECOND { start := 0#usize, «end» := 8#usize } b5 qv
    q Zb B1 T2 B2 Rinv ζ (gsLvl q ζ 32 4 (gsLvl q ζ 64 2 (gsLvl q ζ 128 1 f))) hq0 hqlt hR hQ
    (by omega) hZ0 hs2 hz2 ht2 hb21 hb22 htbl8 rfl (initSplitB (by simp) hb5)
    (by intro c hc; rw [hv5 c hc, if_neg (by simp)]))
  rintro b6 ⟨hb6, hv6⟩
  apply WP.spec_bind (spec_and (WP.spec_mono (hbar b6) (fun r hr => hr.1))
    (WP.spec_mono (hbar b6) (fun r hr => hr.2)))
  rintro b7 ⟨hb7, hv7⟩
  -- back into position coordinates
  apply WP.spec_bind (spec_and (transpose16_bnd b7 hb7) (transpose16_pos q b7))
  rintro b8 ⟨hb8, ht8⟩
  have hv8 : ∀ c < 256, posZ q b8 c = invV q ζ f c := by
    intro c hc
    rw [ht8 c hc, show tposZ q b7 c = posZ q b7 (16 * (c % 16) + c / 16) from rfl,
      hv7 _ (by omega), show posZ q b6 (16 * (c % 16) + c / 16) = tposZ q b6 c from rfl,
      hv6 c hc, invV]
  -- the horizontal section
  apply WP.spec_bind (invntt_block_loop4_walk SECOND b8 qv bm rnd q Zb A0 T1 B1 T2 B2 M Rinv ζ
    (invV q ζ f) hq0 hqlt hR hQ hM hRnd hQlt14 hQodd hMpos hMlt hD hA0 hbar0 hZ0 hZbfit hs1 hz1
    ht1 hb11 hb12 hs2 hz2 ht2 hb21 hb22 hzeta ⟨qi, hqi, hqiu⟩ hb8 hv8)
  rintro b9 ⟨hb9, hv9⟩
  -- the scaling
  rw [hsc, bind_tc_ok]
  obtain ⟨scv, hscl, hscll⟩ := set1_epi16_spec sc
  rw [hscl, bind_tc_ok, hqi, bind_tc_ok]
  simp only [core.num.I16.wrapping_mul, lift, bind_tc_ok]
  obtain ⟨scqv, hscq, hscql⟩ := set1_epi16_spec (IScalar.wrapping_mul sc qi)
  rw [hscq, bind_tc_ok]
  have hscb' : VecBnd scv Zb := fun j hj => by
    rw [show (lane16 scv j).toInt = sc.val from by rw [hscll j hj]; rfl]; exact hscb
  have hsq : ∀ j < 16,
      (2 ^ 16 : ℤ) ∣ ((lane16 scqv j).toInt * (q : ℤ) - (lane16 scv j).toInt) := by
    intro j hj
    rw [show (lane16 scqv j).toInt = (IScalar.wrapping_mul sc qi).val from by
        rw [hscql j hj]; rfl,
      show (lane16 scv j).toInt = sc.val from by rw [hscll j hj]; rfl,
      IScalar.wrapping_mul_val_eq]
    exact mont_pair rfl hqiu
  have hσ : ∀ j < 16, laneZ q scv j * Rinv = σ := by
    intro j hj
    rw [show laneZ q scv j = ((sc.val : ℤ) : ZMod q) from by
      unfold laneZ; rw [show (lane16 scv j).toInt = sc.val from by rw [hscll j hj]; rfl]]
    exact hscv
  apply WP.spec_mono (invntt_block_loop5_walk { start := 0#usize, «end» := 16#usize } b9 qv scv
    scqv q Zb B2 Tf Rinv σ (invAll q ζ f) hq0 hqlt hR hQ hsq hscb' hσ (by omega) hzf htf rfl
    (initSplitB (by simp) hb9)
    (by intro c hc; simp only [invAll]; rw [hv9 c hc, if_neg (by simp)]))
  exact fun r hr => hr

/-! ## …and the eight layers are the inverse transform

`State_gs` applied eight times, from the leaf state back to the root.  Each layer halves the
number of blocks and doubles the accumulated constant, so eight layers multiply it by 256 — which
is exactly what `INVNTT_SCALE` is there to undo. -/

theorem invAll_State {q : ℕ} (ζ : ℕ → ZMod q)
    (hsq : ∀ k, 1 ≤ k → k < 256 → ζ k ^ 2 = NttAlg.cst ζ k)
    (hpair : ∀ nb b : ℕ, (∃ j, j < 8 ∧ nb = 2 ^ j) → b < nb →
      ζ (nb + b) * ζ (2 * nb - 1 - b) = -1)
    {c : ZMod q} {f a : ℕ → ZMod q} (hst : NttAlg.State ζ 256 1 c f a) :
    NttAlg.State ζ 1 256 (256 * c) f (invAll q ζ a) := by
  have h1 : NttAlg.State ζ 128 2 (2 * c) f (gsLvl q ζ 128 1 a) :=
    NttAlg.State_gs hsq hpair (by norm_num) (by norm_num) ⟨7, by norm_num⟩ hst
      (gsLvl_hbut q ζ 128 1 a (by norm_num))
  have h2 : NttAlg.State ζ 64 4 (2 * (2 * c)) f (gsLvl q ζ 64 2 (gsLvl q ζ 128 1 a)) :=
    NttAlg.State_gs hsq hpair (by norm_num) (by norm_num) ⟨6, by norm_num⟩ h1
      (gsLvl_hbut q ζ 64 2 _ (by norm_num))
  have h3 : NttAlg.State ζ 32 8 (2 * (2 * (2 * c))) f
      (gsLvl q ζ 32 4 (gsLvl q ζ 64 2 (gsLvl q ζ 128 1 a))) :=
    NttAlg.State_gs hsq hpair (by norm_num) (by norm_num) ⟨5, by norm_num⟩ h2
      (gsLvl_hbut q ζ 32 4 _ (by norm_num))
  have h4 : NttAlg.State ζ 16 16 (2 * (2 * (2 * (2 * c)))) f (invV q ζ a) :=
    NttAlg.State_gs hsq hpair (by norm_num) (by norm_num) ⟨4, by norm_num⟩ h3
      (gsLvl_hbut q ζ 16 8 _ (by norm_num))
  have h5 : NttAlg.State ζ 8 32 (2 * (2 * (2 * (2 * (2 * c))))) f (gsLvl q ζ 8 16 (invV q ζ a)) :=
    NttAlg.State_gs hsq hpair (by norm_num) (by norm_num) ⟨3, by norm_num⟩ h4
      (gsLvl_hbut q ζ 8 16 _ (by norm_num))
  have h6 : NttAlg.State ζ 4 64 (2 * (2 * (2 * (2 * (2 * (2 * c)))))) f
      (gsLvl q ζ 4 32 (gsLvl q ζ 8 16 (invV q ζ a))) :=
    NttAlg.State_gs hsq hpair (by norm_num) (by norm_num) ⟨2, by norm_num⟩ h5
      (gsLvl_hbut q ζ 4 32 _ (by norm_num))
  have h7 : NttAlg.State ζ 2 128 (2 * (2 * (2 * (2 * (2 * (2 * (2 * c))))))) f
      (gsLvl q ζ 2 64 (gsLvl q ζ 4 32 (gsLvl q ζ 8 16 (invV q ζ a)))) :=
    NttAlg.State_gs hsq hpair (by norm_num) (by norm_num) ⟨1, by norm_num⟩ h6
      (gsLvl_hbut q ζ 2 64 _ (by norm_num))
  have h8 : NttAlg.State ζ 1 256 (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * c)))))))) f
      (invAll q ζ a) :=
    NttAlg.State_gs hsq hpair (by norm_num) (by norm_num) ⟨0, by norm_num⟩ h7
      (gsLvl_hbut q ζ 1 128 _ (by norm_num))
  have hc : (256 : ZMod q) * c = 2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * c))))))) := by ring
  rw [hc]
  exact h8

/-! ## The inverse transform, unconditionally

Instantiating the walk with the real tables.  As on the forward side nothing is assumed: the ζ
tables' properties come from `Kopis/Avx2/Tables.lean` and `Kopis/Avx2/NttZeta.lean`, both
`decide`d over the literal arrays. -/

set_option maxRecDepth 20000 in
theorem invntt_block_leaf_q2 (b : Array I16 256#usize) (f : ℕ → ZMod 10753)
    (hb : BlockBnd b 7141) (hv : ∀ c < 256, posZ 10753 b c = f c) :
    backend.avx2.ntt.invntt_block true b
      ⦃ (r : Array I16 256#usize) =>
          BlockBnd r 7141 ∧ ∀ c < 256, posZ 10753 r c
            = (((2536 : ℤ) : ZMod 10753) * (1764 : ZMod 10753)) * invAll 10753 zeta2 f c ⦄ := by
  refine invntt_block_walk true b 10753 5376 7141 6549 14282 7720 28564 5376 6259 10752
    7141 21504 7141 12482
    (1764 : ZMod 10753) _ zeta2 f backend.crt.Q2 backend.crt.Q2_BARRETT_M
    backend.crt.INVNTT_SCALE_2 (by simp [backend.crt.q]) (by rw [q2_val]; norm_num)
    (by simp [backend.crt.barrett_m]) (by simp only [backend.crt.Q2_BARRETT_M]; decide)
    (by simp [backend.crt.invntt_scale]) (by simp only [backend.crt.INVNTT_SCALE_2]; scalar_tac)
    (by rw [show (backend.crt.INVNTT_SCALE_2 : I16).val = (2536 : ℤ) from by
      simp only [backend.crt.INVNTT_SCALE_2]; scalar_tac])
    (by norm_num) (by norm_num) (by decide) (by norm_num) (by decide) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    ?_ ?_ ?_ ?_ ?_ ?_ hb hv
  · intro kk hkk
    obtain ⟨zi, -, h1, -, h3, -, h5⟩ := zeta_table_ok_q2 kk hkk
    exact ⟨zi, h1, h3, by rw [h5]; rfl⟩
  · refine ⟨backend.crt.Q2_INV, by simp [backend.crt.qinv], ?_⟩
    rw [show (((10753 : ℕ) : ℤ)) = backend.crt.Q2.val from by rw [q2_val]; norm_num]
    exact q2_inv_unit
  · intro h hh
    obtain ⟨z, zq, h1, h2, h3⟩ := inv1_q2_ok h hh
    refine ⟨z, zq, h1, h2, fun k hk => ?_⟩
    rw [show laneZ 10753 z k = (((lane16 z k).toInt : ℤ) : ZMod 10753) from rfl, h3 k hk,
      show ((255#isize).val + h.val * ((-1)#isize).val + k * ((-8)#isize).val).toNat
        = 255 - h.val - 8 * k from by scalar_tac]
    push_cast
    rw [neg_mul]
    rfl
  · intro h hh
    obtain ⟨z, zq, h1, h2, h3⟩ := inv2_q2_ok h hh
    refine ⟨z, zq, h1, h2, fun k hk => ?_⟩
    rw [show laneZ 10753 z k = (((lane16 z k).toInt : ℤ) : ZMod 10753) from rfl, h3 k hk,
      show ((127#isize).val + h.val * ((-1)#isize).val + k * ((-4)#isize).val).toNat
        = 127 - h.val - 4 * k from by scalar_tac]
    push_cast
    rw [neg_mul]
    rfl
  · intro h hh
    obtain ⟨z, zq, h1, h2, h3⟩ := inv4_q2_ok h hh
    refine ⟨z, zq, h1, h2, fun k hk => ?_⟩
    rw [show laneZ 10753 z k = (((lane16 z k).toInt : ℤ) : ZMod 10753) from rfl, h3 k hk,
      show ((63#isize).val + h.val * ((-1)#isize).val + k * ((-2)#isize).val).toNat
        = 63 - h.val - 2 * k from by scalar_tac]
    push_cast
    rw [neg_mul]
    rfl
  · obtain ⟨z, zq, h1, h2, h3⟩ := inv8_q2_ok 0#usize (by simp)
    refine ⟨z, zq, h1, h2, fun k hk => ?_⟩
    rw [show laneZ 10753 z k = (((lane16 z k).toInt : ℤ) : ZMod 10753) from rfl, h3 k hk,
      show ((31#isize).val + (0#usize).val * (0#isize).val + k * ((-1)#isize).val).toNat
        = 31 - k from by scalar_tac]
    push_cast
    rw [neg_mul]
    rfl

set_option maxRecDepth 20000 in
theorem invntt_block_leaf_q1 (b : Array I16 256#usize) (f : ℕ → ZMod 7681)
    (hb : BlockBnd b 4741) (hv : ∀ c < 256, posZ 7681 b c = f c) :
    backend.avx2.ntt.invntt_block false b
      ⦃ (r : Array I16 256#usize) =>
          BlockBnd r 4741 ∧ ∀ c < 256, posZ 7681 r c
            = (((1912 : ℤ) : ZMod 7681) * (900 : ZMod 7681)) * invAll 7681 zeta1 f c ⦄ := by
  refine invntt_block_walk false b 7681 3840 4741 4397 9482 4952 18964 3840 4291 7680
    4741 15360 4741 17474
    (900 : ZMod 7681) _ zeta1 f backend.crt.Q1 backend.crt.Q1_BARRETT_M
    backend.crt.INVNTT_SCALE_1 (by simp [backend.crt.q]) (by rw [q1_val]; norm_num)
    (by simp [backend.crt.barrett_m]) (by simp only [backend.crt.Q1_BARRETT_M]; decide)
    (by simp [backend.crt.invntt_scale]) (by simp only [backend.crt.INVNTT_SCALE_1]; scalar_tac)
    (by rw [show (backend.crt.INVNTT_SCALE_1 : I16).val = (1912 : ℤ) from by
      simp only [backend.crt.INVNTT_SCALE_1]; scalar_tac])
    (by norm_num) (by norm_num) (by decide) (by norm_num) (by decide) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    ?_ ?_ ?_ ?_ ?_ ?_ hb hv
  · intro kk hkk
    obtain ⟨zi, -, h1, -, h3, -, h5⟩ := zeta_table_ok_q1 kk hkk
    exact ⟨zi, h1, h3, by rw [h5]; rfl⟩
  · refine ⟨backend.crt.Q1_INV, by simp [backend.crt.qinv], ?_⟩
    rw [show (((7681 : ℕ) : ℤ)) = backend.crt.Q1.val from by rw [q1_val]; norm_num]
    exact q1_inv_unit
  · intro h hh
    obtain ⟨z, zq, h1, h2, h3⟩ := inv1_q1_ok h hh
    refine ⟨z, zq, h1, h2, fun k hk => ?_⟩
    rw [show laneZ 7681 z k = (((lane16 z k).toInt : ℤ) : ZMod 7681) from rfl, h3 k hk,
      show ((255#isize).val + h.val * ((-1)#isize).val + k * ((-8)#isize).val).toNat
        = 255 - h.val - 8 * k from by scalar_tac]
    push_cast
    rw [neg_mul]
    rfl
  · intro h hh
    obtain ⟨z, zq, h1, h2, h3⟩ := inv2_q1_ok h hh
    refine ⟨z, zq, h1, h2, fun k hk => ?_⟩
    rw [show laneZ 7681 z k = (((lane16 z k).toInt : ℤ) : ZMod 7681) from rfl, h3 k hk,
      show ((127#isize).val + h.val * ((-1)#isize).val + k * ((-4)#isize).val).toNat
        = 127 - h.val - 4 * k from by scalar_tac]
    push_cast
    rw [neg_mul]
    rfl
  · intro h hh
    obtain ⟨z, zq, h1, h2, h3⟩ := inv4_q1_ok h hh
    refine ⟨z, zq, h1, h2, fun k hk => ?_⟩
    rw [show laneZ 7681 z k = (((lane16 z k).toInt : ℤ) : ZMod 7681) from rfl, h3 k hk,
      show ((63#isize).val + h.val * ((-1)#isize).val + k * ((-2)#isize).val).toNat
        = 63 - h.val - 2 * k from by scalar_tac]
    push_cast
    rw [neg_mul]
    rfl
  · obtain ⟨z, zq, h1, h2, h3⟩ := inv8_q1_ok 0#usize (by simp)
    refine ⟨z, zq, h1, h2, fun k hk => ?_⟩
    rw [show laneZ 7681 z k = (((lane16 z k).toInt : ℤ) : ZMod 7681) from rfl, h3 k hk,
      show ((31#isize).val + (0#usize).val * (0#isize).val + k * ((-1)#isize).val).toNat
        = 31 - k from by scalar_tac]
    push_cast
    rw [neg_mul]
    rfl

/-- **The inverse transform undoes the forward one.**  Composing the walk with the algebra: from
the leaf state, `invntt_block` returns to the root state scaled by `256·σ`, and `INVNTT_SCALE` is
chosen so that product is 1. -/
theorem invntt_block_State_q2 (b : Array I16 256#usize) (c : ZMod 10753) (f a : ℕ → ZMod 10753)
    (hst : NttAlg.State zeta2 256 1 c f a)
    (hb : BlockBnd b 7141) (hv : ∀ cc < 256, posZ 10753 b cc = a cc) :
    backend.avx2.ntt.invntt_block true b
      ⦃ (r : Array I16 256#usize) =>
          BlockBnd r 7141 ∧ ∀ cc < 256, posZ 10753 r cc
            = (((2536 : ℤ) : ZMod 10753) * (1764 : ZMod 10753)) * (256 * c) * f cc ⦄ := by
  apply WP.spec_mono (invntt_block_leaf_q2 b a hb hv)
  intro r hr
  refine ⟨hr.1, fun cc hcc => ?_⟩
  rw [hr.2 cc hcc,
    NttAlg.State_root (invAll_State zeta2 zeta2_sq zeta2_pair hst) cc hcc]
  ring

theorem invntt_block_State_q1 (b : Array I16 256#usize) (c : ZMod 7681) (f a : ℕ → ZMod 7681)
    (hst : NttAlg.State zeta1 256 1 c f a)
    (hb : BlockBnd b 4741) (hv : ∀ cc < 256, posZ 7681 b cc = a cc) :
    backend.avx2.ntt.invntt_block false b
      ⦃ (r : Array I16 256#usize) =>
          BlockBnd r 4741 ∧ ∀ cc < 256, posZ 7681 r cc
            = (((1912 : ℤ) : ZMod 7681) * (900 : ZMod 7681)) * (256 * c) * f cc ⦄ := by
  apply WP.spec_mono (invntt_block_leaf_q1 b a hb hv)
  intro r hr
  refine ⟨hr.1, fun cc hcc => ?_⟩
  rw [hr.2 cc hcc,
    NttAlg.State_root (invAll_State zeta1 zeta1_sq zeta1_pair hst) cc hcc]
  ring

end Kopis.Avx2
