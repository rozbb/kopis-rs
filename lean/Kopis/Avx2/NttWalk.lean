/-
  # Kopis/Avx2/NttWalk.lean — the forward transform's levels, as residues (plan phase F4).

  `Kopis/Avx2/NttValue.lean` says what one butterfly computes; `Kopis/Avx2/NttAlgebra.lean` says
  what one Cooley-Tukey *layer* does to the CRT invariant.  This file walks the AVX2 loops and
  shows they apply the butterfly at the index pairs the layer expects.

  ## The two coordinate systems

  A block is 256 `i16` at array positions `0 … 256`, and a vector `k` is positions `[16k, 16k+16)`.
  Before the transpose, array position *is* the coefficient index.  `transpose16` moves the `i16`
  at `16m + k` to `16k + m` (`transpose16_coeff`), so afterwards the coefficient that was at
  `16m + k` sits at position `16k + m`.

  So there are two views of the same array:

  * `posZ` — by array position, which is the coefficient index before the transpose;
  * `tposZ` — by coefficient index, `tposZ b c = posZ b (16·(c % 16) + c / 16)`, which is the
    right view *after* the transpose.

  `transpose16_tpos` is the one fact that connects them, and it is why the four vertical levels
  can be read as ordinary Cooley-Tukey layers on contiguous blocks.
-/
import Kopis.Avx2.NttValue

open Aeneas Aeneas.Std Result
open RustKopisAvx2
open RustKopisAvx2.backend.avx2.intrinsics

namespace Kopis.Avx2

set_option maxHeartbeats 1000000

/-! ## The two views -/

/-- The block by array position, as residues. -/
noncomputable def posZ (q : ℕ) (b : Array I16 256#usize) (p : ℕ) : ZMod q :=
  (((b.val[p]!).val : ℤ) : ZMod q)

/-- The block by coefficient index, after a `transpose16`. -/
noncomputable def tposZ (q : ℕ) (b : Array I16 256#usize) (c : ℕ) : ZMod q :=
  posZ q b (16 * (c % 16) + c / 16)

/-- **The transpose exchanges the two views.** -/
theorem transpose16_tpos (q : ℕ) (b : Array I16 256#usize) :
    backend.avx2.ntt.transpose16 b
      ⦃ (r : Array I16 256#usize) => ∀ c < 256, tposZ q r c = posZ q b c ⦄ := by
  apply WP.spec_mono (transpose16_coeff b)
  intro r hr c hc
  have h := hr (c % 16) (by omega) (c / 16) (by omega)
  unfold tposZ posZ
  have hval : (r.val[16 * (c % 16) + c / 16]!).val = (b.val[16 * (c / 16) + c % 16]!).val := by
    have e : (r.val[16 * (c % 16) + c / 16]!).bv = (b.val[16 * (c / 16) + c % 16]!).bv := h
    exact congrArg BitVec.toInt e
  rw [hval, show 16 * (c / 16) + c % 16 = c from by omega]

/-- **The transpose, the other way.**  Going back into position coordinates. -/
theorem transpose16_pos (q : ℕ) (b : Array I16 256#usize) :
    backend.avx2.ntt.transpose16 b
      ⦃ (r : Array I16 256#usize) => ∀ c < 256, posZ q r c = tposZ q b c ⦄ := by
  apply WP.spec_mono (transpose16_coeff b)
  intro r hr c hc
  unfold tposZ posZ
  have e := hr (c / 16) (by omega) (c % 16) (by omega)
  rw [show 16 * (c / 16) + c % 16 = c from by omega] at e
  have : (r.val[c]!).val = (b.val[16 * (c % 16) + c / 16]!).val := congrArg BitVec.toInt e
  exact congrArg (fun z : ℤ => (z : ZMod q)) this

/-! ## Loads and stores, as residues -/

theorem load_posZ (q : ℕ) (b : Array I16 256#usize) (i : Usize) (hi : i.val < 16) :
    ∃ c, load_i16 b i = ok c ∧ ∀ m < 16, laneZ q c m = posZ q b (16 * i.val + m) := by
  obtain ⟨c, hc, h⟩ := load_i16_val b i hi
  exact ⟨c, hc, fun m hm => by unfold laneZ posZ; rw [h m hm]⟩

theorem store_posZ (q : ℕ) (b : Array I16 256#usize) (i : Usize) (v : Vec256) (hi : i.val < 16) :
    ∃ b', store_i16 b i v = ok b' ∧ ∀ p < 256,
      posZ q b' p =
        if 16 * i.val ≤ p ∧ p < 16 * i.val + 16 then laneZ q v (p - 16 * i.val)
        else posZ q b p := by
  obtain ⟨d, hd, h⟩ := store_i16_val b i v hi
  refine ⟨d, hd, fun p hp => ?_⟩
  unfold posZ laneZ
  rw [h p hp]
  split <;> rfl

/-- Two specs for the same computation combine. -/
theorem spec_and {α} {m : Result α} {P Q : α → Prop}
    (hP : m ⦃ r => P r ⦄) (hQ : m ⦃ r => Q r ⦄) : m ⦃ r => P r ∧ Q r ⦄ := by
  unfold WP.spec WP.theta WP.wp_return at *
  cases m <;> simp_all

/-! ## One Cooley-Tukey layer, as a function of the view

The layer that `State_ct` describes, written as an explicit function so a loop's postcondition can
name it.  `ctLvl_hbut` is the bridge: it is exactly the `hbut` hypothesis `State_ct` asks for. -/

/-- The result of one Cooley-Tukey layer at `nb` blocks of size `2m'`. -/
noncomputable def ctLvl (q : ℕ) (ψ : ℕ → ZMod q) (nb m' : ℕ) (a : ℕ → ZMod q) (c : ℕ) : ZMod q :=
  if c % (2 * m') < m' then a c + ψ (nb + c / (2 * m')) * a (c + m')
  else a (c - m') - ψ (nb + c / (2 * m')) * a c

theorem ctLvl_hbut (q : ℕ) (ψ : ℕ → ZMod q) (nb m' : ℕ) (a : ℕ → ZMod q) (hm' : 0 < m') :
    ∀ b < nb, ∀ r < m',
      ctLvl q ψ nb m' a (b * (2 * m') + r)
          = a (b * (2 * m') + r) + ψ (nb + b) * a (b * (2 * m') + m' + r) ∧
      ctLvl q ψ nb m' a (b * (2 * m') + m' + r)
          = a (b * (2 * m') + r) - ψ (nb + b) * a (b * (2 * m') + m' + r) := by
  intro b hb r hr
  have hre : ∀ t, t < 2 * m' → (b * (2 * m') + t) % (2 * m') = t ∧
      (b * (2 * m') + t) / (2 * m') = b := by
    intro t ht
    constructor
    · rw [show b * (2 * m') + t = t + (2 * m') * b from by ring, Nat.add_mul_mod_self_left,
        Nat.mod_eq_of_lt ht]
    · rw [show b * (2 * m') + t = t + (2 * m') * b from by ring,
        Nat.add_mul_div_left _ _ (by omega), Nat.div_eq_of_lt ht, Nat.zero_add]
  obtain ⟨hm1, hd1⟩ := hre r (by omega)
  obtain ⟨hm2, hd2⟩ := hre (m' + r) (by omega)
  constructor
  · rw [ctLvl, hm1, if_pos hr, hd1,
      show b * (2 * m') + r + m' = b * (2 * m') + m' + r from by ring]
  · rw [ctLvl, show b * (2 * m') + m' + r = b * (2 * m') + (m' + r) from by ring, hm2,
      if_neg (by omega), hd2,
      show b * (2 * m') + (m' + r) - m' = b * (2 * m') + r from by omega]

/-! ## The `len = 8` vertical level

Eight butterflies pairing array vectors `j` and `j + 8` at every lane.  In the coefficient view
that is offsets `j` and `j + 8` inside each of the sixteen blocks, with the twiddle taken from
lane `c / 16` of the table — which is block `c / 16`, exactly the `ζ(16 + b)` the layer wants.

Bounds and values are carried together: `ct_butterfly_val`'s exactness hypotheses are bounds on
the two *input* vectors, and knowing those are the unprocessed ones is what the `Split` records. -/

theorem ntt_block_loop1_walk (SECOND : Bool) (iter : core.ops.range.Range Usize)
    (b : Array I16 256#usize) (qv : Vec256) (q : ℕ) (Zb A T : ℤ) (Rinv : ZMod q)
    (ψ : ℕ → ZMod q) (a0 : ℕ → ZMod q)
    (hq0 : 0 < (q : ℤ)) (hqlt : (q : ℤ) ≤ 2 ^ 15)
    (hR : ((2 ^ 16 : ℤ) : ZMod q) * Rinv = 1)
    (hQ : ∀ i < 16, (lane16 qv i).toInt = (q : ℤ))
    (hA0 : 0 ≤ A) (hAZ : A * Zb < 2 ^ 15 * (q : ℤ))
    (hT : A * Zb + 2 ^ 15 * (q : ℤ) ≤ 2 ^ 16 * T) (hfit : A + T ≤ 2 ^ 15 - 1)
    (htbl : ∃ z zq,
      (if SECOND then (do let t ← backend.avx2.ntt.FWD8_Q2; backend.avx2.ntt.ld_tbl t 0#usize)
       else (do let t ← backend.avx2.ntt.FWD8_Q1; backend.avx2.ntt.ld_tbl t 0#usize))
        = ok (z, zq) ∧ PsiOk z zq (q : ℤ) Zb ∧ ∀ k < 16, laneZ q z k * Rinv = ψ (16 + k))
    (hend : iter.«end».val = 8)
    (hbnd : Split b (fun v => v < iter.start.val ∨ (8 ≤ v ∧ v < 8 + iter.start.val)) A T)
    (hval : ∀ c < 256, tposZ q b c =
      if c % 16 < iter.start.val ∨ (8 ≤ c % 16 ∧ c % 16 < 8 + iter.start.val)
      then ctLvl q ψ 16 8 a0 c else a0 c) :
    backend.avx2.ntt.ntt_block_loop1 SECOND iter b qv
      ⦃ (r : Array I16 256#usize) =>
          BlockBnd r (A + T) ∧ ∀ c < 256, tposZ q r c = ctLvl q ψ 16 8 a0 c ⦄ := by
  unfold backend.avx2.ntt.ntt_block_loop1
  obtain ⟨z, zq, htz, ⟨hzb, hzqm⟩, hψ⟩ := htbl
  by_cases hlt : iter.start.val < iter.«end».val
  · let* ⟨ o, iter1, ho, hstart', hend' ⟩ ← core.iter.range.IteratorRange.next_Usize_some_spec
    rw [ho]; simp only
    rw [htz, bind_tc_ok]
    show (do let lo ← load_i16 b iter.start
             let i ← iter.start + 8#usize
             let hi ← load_i16 b i
             let (lo1, hi1) ← backend.avx2.ntt.ct_butterfly lo hi z zq qv
             let b1 ← store_i16 b iter.start lo1
             let b2 ← store_i16 b1 i hi1
             backend.avx2.ntt.ntt_block_loop1 SECOND iter1 b2 qv)
        ⦃ (r : Array I16 256#usize) =>
            BlockBnd r (A + T) ∧ ∀ c < 256, tposZ q r c = ctLvl q ψ 16 8 a0 c ⦄
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
      (ct_butterfly_bnd lo' hiv' z zq qv (q : ℤ) Zb A T hQ hq0 hqlt hzqm hlob hhivb hzb hA0 hAZ
        hT hfit)
      (ct_butterfly_val lo' hiv' z zq qv q Zb A T Rinv hq0 hqlt hR hQ hzqm hlob hhivb hzb hA0
        hAZ hT hfit))
    intro r hr
    obtain ⟨lo1, hi1'⟩ := r
    obtain ⟨⟨hr1, hr2⟩, hrv⟩ := hr
    simp only at hr1 hr2 hrv
    show (do let b1 ← store_i16 b iter.start lo1
             let b2 ← store_i16 b1 i hi1'
             backend.avx2.ntt.ntt_block_loop1 SECOND iter1 b2 qv)
        ⦃ (r : Array I16 256#usize) =>
            BlockBnd r (A + T) ∧ ∀ c < 256, tposZ q r c = ctLvl q ψ 16 8 a0 c ⦄
    obtain ⟨b1, hb1, hb1at, hb1oth⟩ := store_i16_at b iter.start lo1 (by omega)
    obtain ⟨b1', hb1', hb1v⟩ := store_posZ q b iter.start lo1 (by omega)
    rw [show b1 = b1' from by rw [hb1] at hb1'; injection hb1'] at hb1at hb1oth
    rw [hb1', bind_tc_ok]
    obtain ⟨b2, hb2, hb2at, hb2oth⟩ := store_i16_at b1' i hi1' (by omega)
    obtain ⟨b2', hb2', hb2v⟩ := store_posZ q b1' i hi1' (by omega)
    rw [show b2 = b2' from by rw [hb2] at hb2'; injection hb2'] at hb2at hb2oth
    rw [hb2', bind_tc_ok]
    apply ntt_block_loop1_walk SECOND iter1 b2' qv q Zb A T Rinv ψ a0 hq0 hqlt hR hQ hA0 hAZ hT
      hfit ⟨z, zq, htz, ⟨hzb, hzqm⟩, hψ⟩ (by rw [hend']; exact hend)
    · constructor
      · intro v hv hP
        rcases (show v = iter.start.val ∨ v = i.val ∨ (v ≠ iter.start.val ∧ v ≠ i.val)
          from by omega) with rfl | rfl | ⟨hne1, hne2⟩
        · intro k hk
          rw [hb2oth iter.start.val (by omega) (by omega) k hk, hb1at k hk]
          exact hr1 k hk
        · intro k hk
          rw [hb2at k hk]
          exact hr2 k hk
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
          (hrv (c / 16) hc16).2, hlov (c / 16) hc16, hhivv (c / 16) hc16, hψ (c / 16) hc16]
        have e1 : posZ q b (16 * iter.start.val + c / 16) = a0 (c - 8) := by
          rw [show 16 * iter.start.val + c / 16
            = 16 * ((c - 8) % 16) + (c - 8) / 16 from by omega, ← tposZ, hval (c - 8) (by omega),
            if_neg (by omega)]
        have e2 : posZ q b (16 * i.val + c / 16) = a0 c := by
          rw [show 16 * i.val + c / 16 = 16 * (c % 16) + c / 16 from by omega, ← tposZ,
            hval c hc, if_neg (by omega)]
        rw [e1, e2, ctLvl, if_neg (by omega), show c / (2 * 8) = c / 16 from by norm_num]
      · rw [if_neg (by omega)]
        by_cases h2 : c % 16 = iter.start.val
        · rw [if_pos (by omega), if_pos (by omega),
            show 16 * (c % 16) + c / 16 - 16 * iter.start.val = c / 16 from by omega,
            (hrv (c / 16) hc16).1, hlov (c / 16) hc16, hhivv (c / 16) hc16, hψ (c / 16) hc16]
          have e1 : posZ q b (16 * iter.start.val + c / 16) = a0 c := by
            rw [show 16 * iter.start.val + c / 16 = 16 * (c % 16) + c / 16 from by omega,
              ← tposZ, hval c hc, if_neg (by omega)]
          have e2 : posZ q b (16 * i.val + c / 16) = a0 (c + 8) := by
            rw [show 16 * i.val + c / 16 = 16 * ((c + 8) % 16) + (c + 8) / 16 from by omega,
              ← tposZ, hval (c + 8) (by omega), if_neg (by omega)]
          rw [e1, e2, ctLvl, if_pos (by omega), show c / (2 * 8) = c / 16 from by norm_num]
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

/-! ## The `len = 1` vertical level

Pairs array vectors `2h` and `2h + 1`, i.e. adjacent coefficients inside each block of two.  The
ψ index works out as `128 + h + 8·(c/16)`, which is what group `h` lane `c/16` of `FWD1` holds. -/

theorem ntt_block_loop4_walk (SECOND : Bool) (iter : core.ops.range.Range Usize)
    (b : Array I16 256#usize) (qv : Vec256) (q : ℕ) (Zb A T : ℤ) (Rinv : ZMod q)
    (ψ : ℕ → ZMod q) (a0 : ℕ → ZMod q)
    (hq0 : 0 < (q : ℤ)) (hqlt : (q : ℤ) ≤ 2 ^ 15)
    (hR : ((2 ^ 16 : ℤ) : ZMod q) * Rinv = 1)
    (hQ : ∀ i < 16, (lane16 qv i).toInt = (q : ℤ))
    (hA0 : 0 ≤ A) (hAZ : A * Zb < 2 ^ 15 * (q : ℤ))
    (hT : A * Zb + 2 ^ 15 * (q : ℤ) ≤ 2 ^ 16 * T) (hfit : A + T ≤ 2 ^ 15 - 1)
    (htbl : ∀ h : Usize, h.val < 8 → ∃ z zq,
      (if SECOND then (do let t ← backend.avx2.ntt.FWD1_Q2; backend.avx2.ntt.ld_tbl t h)
       else (do let t ← backend.avx2.ntt.FWD1_Q1; backend.avx2.ntt.ld_tbl t h))
        = ok (z, zq) ∧ PsiOk z zq (q : ℤ) Zb ∧
        ∀ k < 16, laneZ q z k * Rinv = ψ (128 + h.val + 8 * k))
    (hend : iter.«end».val = 8)
    (hbnd : Split b (fun v => v < 2 * iter.start.val) A T)
    (hval : ∀ c < 256, tposZ q b c =
      if c % 16 < 2 * iter.start.val then ctLvl q ψ 128 1 a0 c else a0 c) :
    backend.avx2.ntt.ntt_block_loop4 SECOND iter b qv
      ⦃ (r : Array I16 256#usize) =>
          BlockBnd r (A + T) ∧ ∀ c < 256, tposZ q r c = ctLvl q ψ 128 1 a0 c ⦄ := by
  unfold backend.avx2.ntt.ntt_block_loop4
  by_cases hlt : iter.start.val < iter.«end».val
  · let* ⟨ o, iter1, ho, hstart', hend' ⟩ ← core.iter.range.IteratorRange.next_Usize_some_spec
    rw [ho]; simp only
    obtain ⟨z, zq, htz, ⟨hzb, hzqm⟩, hψ⟩ := htbl iter.start (by omega)
    rw [htz, bind_tc_ok]
    show (do let i ← 2#usize * iter.start
             let lo ← load_i16 b i
             let i1 ← i + 1#usize
             let hi ← load_i16 b i1
             let (lo1, hi1) ← backend.avx2.ntt.ct_butterfly lo hi z zq qv
             let b1 ← store_i16 b i lo1
             let i2 ← i + 1#usize
             let b2 ← store_i16 b1 i2 hi1
             backend.avx2.ntt.ntt_block_loop4 SECOND iter1 b2 qv)
        ⦃ (r : Array I16 256#usize) =>
            BlockBnd r (A + T) ∧ ∀ c < 256, tposZ q r c = ctLvl q ψ 128 1 a0 c ⦄
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
      (ct_butterfly_bnd lo' hiv' z zq qv (q : ℤ) Zb A T hQ hq0 hqlt hzqm hlob hhivb hzb hA0 hAZ
        hT hfit)
      (ct_butterfly_val lo' hiv' z zq qv q Zb A T Rinv hq0 hqlt hR hQ hzqm hlob hhivb hzb hA0
        hAZ hT hfit))
    intro r hr
    obtain ⟨lo1, hi1'⟩ := r
    obtain ⟨⟨hr1, hr2⟩, hrv⟩ := hr
    simp only at hr1 hr2 hrv
    show (do let b1 ← store_i16 b i lo1
             let i2 ← i + 1#usize
             let b2 ← store_i16 b1 i2 hi1'
             backend.avx2.ntt.ntt_block_loop4 SECOND iter1 b2 qv)
        ⦃ (r : Array I16 256#usize) =>
            BlockBnd r (A + T) ∧ ∀ c < 256, tposZ q r c = ctLvl q ψ 128 1 a0 c ⦄
    obtain ⟨b1, hb1, hb1at, hb1oth⟩ := store_i16_at b i lo1 (by omega)
    obtain ⟨b1', hb1', hb1v⟩ := store_posZ q b i lo1 (by omega)
    rw [show b1 = b1' from by rw [hb1] at hb1'; injection hb1'] at hb1at hb1oth
    rw [hb1', bind_tc_ok]
    step*
    obtain ⟨b2, hb2, hb2at, hb2oth⟩ := store_i16_at b1' i2 hi1' (by omega)
    obtain ⟨b2', hb2', hb2v⟩ := store_posZ q b1' i2 hi1' (by omega)
    rw [show b2 = b2' from by rw [hb2] at hb2'; injection hb2'] at hb2at hb2oth
    rw [hb2', bind_tc_ok]
    apply ntt_block_loop4_walk SECOND iter1 b2' qv q Zb A T Rinv ψ a0 hq0 hqlt hR hQ hA0 hAZ hT
      hfit htbl (by rw [hend']; exact hend)
    · constructor
      · intro v hv hP
        rcases (show v = i.val ∨ v = i2.val ∨ (v ≠ i.val ∧ v ≠ i2.val) from by omega)
          with rfl | rfl | ⟨hne1, hne2⟩
        · intro k hk
          rw [hb2oth i.val (by omega) (by omega) k hk, hb1at k hk]
          exact hr1 k hk
        · intro k hk
          rw [hb2at k hk]
          exact hr2 k hk
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
          (hrv (c / 16) hc16).2, hlov (c / 16) hc16, hhivv (c / 16) hc16, hψ (c / 16) hc16]
        have e1 : posZ q b (16 * i.val + c / 16) = a0 (c - 1) := by
          rw [show 16 * i.val + c / 16 = 16 * ((c - 1) % 16) + (c - 1) / 16 from by omega,
            ← tposZ, hval (c - 1) (by omega), if_neg (by omega)]
        have e2 : posZ q b (16 * i1.val + c / 16) = a0 c := by
          rw [show 16 * i1.val + c / 16 = 16 * (c % 16) + c / 16 from by omega, ← tposZ,
            hval c hc, if_neg (by omega)]
        rw [e1, e2, ctLvl, if_neg (by omega),
          show 128 + iter.start.val + 8 * (c / 16) = 128 + c / (2 * 1) from by omega]
      · rw [if_neg (by omega)]
        by_cases h2 : c % 16 = i.val
        · rw [if_pos (by omega), if_pos (by omega),
            show 16 * (c % 16) + c / 16 - 16 * i.val = c / 16 from by omega,
            (hrv (c / 16) hc16).1, hlov (c / 16) hc16, hhivv (c / 16) hc16, hψ (c / 16) hc16]
          have e1 : posZ q b (16 * i.val + c / 16) = a0 c := by
            rw [show 16 * i.val + c / 16 = 16 * (c % 16) + c / 16 from by omega, ← tposZ,
              hval c hc, if_neg (by omega)]
          have e2 : posZ q b (16 * i1.val + c / 16) = a0 (c + 1) := by
            rw [show 16 * i1.val + c / 16 = 16 * ((c + 1) % 16) + (c + 1) / 16 from by omega,
              ← tposZ, hval (c + 1) (by omega), if_neg (by omega)]
          rw [e1, e2, ctLvl, if_pos (by omega),
            show 128 + iter.start.val + 8 * (c / 16) = 128 + c / (2 * 1) from by omega]
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

/-- The `len = 4` level, one group: `4` butterflies pairing `8h + j` with `8h + j + 4`. -/
theorem ntt_block_loop2_loop0_walk (SECOND : Bool) (iter : core.ops.range.Range Usize)
    (b : Array I16 256#usize) (qv : Vec256) (h : Usize) (q : ℕ) (Zb A T : ℤ) (Rinv : ZMod q)
    (ψ : ℕ → ZMod q) (a0 : ℕ → ZMod q)
    (hq0 : 0 < (q : ℤ)) (hqlt : (q : ℤ) ≤ 2 ^ 15)
    (hR : ((2 ^ 16 : ℤ) : ZMod q) * Rinv = 1)
    (hQ : ∀ i < 16, (lane16 qv i).toInt = (q : ℤ))
    (hA0 : 0 ≤ A) (hAZ : A * Zb < 2 ^ 15 * (q : ℤ))
    (hT : A * Zb + 2 ^ 15 * (q : ℤ) ≤ 2 ^ 16 * T) (hfit : A + T ≤ 2 ^ 15 - 1)
    (hh : h.val < 2)
    (htbl : ∃ z zq,
      (if SECOND then (do let t ← backend.avx2.ntt.FWD4_Q2; backend.avx2.ntt.ld_tbl t h)
       else (do let t ← backend.avx2.ntt.FWD4_Q1; backend.avx2.ntt.ld_tbl t h))
        = ok (z, zq) ∧ PsiOk z zq (q : ℤ) Zb ∧
        ∀ k < 16, laneZ q z k * Rinv = ψ (32 + h.val + 2 * k))
    (hend : iter.«end».val = 4) (hstartle : iter.start.val ≤ 4)
    (hbnd : Split b (fun v => v < 8 * h.val
        ∨ (8 * h.val ≤ v ∧ v < 8 * h.val + iter.start.val)
        ∨ (8 * h.val + 4 ≤ v ∧ v < 8 * h.val + 4 + iter.start.val)) A T)
    (hval : ∀ c < 256, tposZ q b c =
      if c % 16 < 8 * h.val
        ∨ (8 * h.val ≤ c % 16 ∧ c % 16 < 8 * h.val + iter.start.val)
        ∨ (8 * h.val + 4 ≤ c % 16 ∧ c % 16 < 8 * h.val + 4 + iter.start.val)
      then ctLvl q ψ 32 4 a0 c else a0 c) :
    backend.avx2.ntt.ntt_block_loop2_loop0 SECOND iter b qv h
      ⦃ (r : Array I16 256#usize) =>
          Split r (fun v => v < 8 * h.val + 8) A T ∧
          ∀ c < 256, tposZ q r c =
            if c % 16 < 8 * h.val + 8 then ctLvl q ψ 32 4 a0 c else a0 c ⦄ := by
  unfold backend.avx2.ntt.ntt_block_loop2_loop0
  obtain ⟨z, zq, htz, ⟨hzb, hzqm⟩, hψ⟩ := htbl
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
             let (lo1, hi1) ← backend.avx2.ntt.ct_butterfly lo hi z zq qv
             let i4 ← i + iter.start
             let b1 ← store_i16 b i4 lo1
             let i5 ← i + iter.start
             let i6 ← i5 + 4#usize
             let b2 ← store_i16 b1 i6 hi1
             backend.avx2.ntt.ntt_block_loop2_loop0 SECOND iter1 b2 qv h)
        ⦃ (r : Array I16 256#usize) =>
            Split r (fun v => v < 8 * h.val + 8) A T ∧
            ∀ c < 256, tposZ q r c =
              if c % 16 < 8 * h.val + 8 then ctLvl q ψ 32 4 a0 c else a0 c ⦄
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
      (ct_butterfly_bnd lo' hiv' z zq qv (q : ℤ) Zb A T hQ hq0 hqlt hzqm hlob hhivb hzb hA0 hAZ
        hT hfit)
      (ct_butterfly_val lo' hiv' z zq qv q Zb A T Rinv hq0 hqlt hR hQ hzqm hlob hhivb hzb hA0
        hAZ hT hfit))
    intro r hr
    obtain ⟨lo1, hi1'⟩ := r
    obtain ⟨⟨hr1, hr2⟩, hrv⟩ := hr
    simp only at hr1 hr2 hrv
    show (do let i4 ← i + iter.start
             let b1 ← store_i16 b i4 lo1
             let i5 ← i + iter.start
             let i6 ← i5 + 4#usize
             let b2 ← store_i16 b1 i6 hi1'
             backend.avx2.ntt.ntt_block_loop2_loop0 SECOND iter1 b2 qv h)
        ⦃ (r : Array I16 256#usize) =>
            Split r (fun v => v < 8 * h.val + 8) A T ∧
            ∀ c < 256, tposZ q r c =
              if c % 16 < 8 * h.val + 8 then ctLvl q ψ 32 4 a0 c else a0 c ⦄
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
    apply ntt_block_loop2_loop0_walk SECOND iter1 b2' qv h q Zb A T Rinv ψ a0 hq0 hqlt hR hQ
      hA0 hAZ hT hfit hh ⟨z, zq, htz, ⟨hzb, hzqm⟩, hψ⟩ (by rw [hend']; exact hend) (by omega)
    · constructor
      · intro v hv hP
        rcases (show v = i4.val ∨ v = i6.val ∨ (v ≠ i4.val ∧ v ≠ i6.val) from by omega)
          with rfl | rfl | ⟨hne1, hne2⟩
        · intro k hk
          rw [hb2oth i4.val (by omega) (by omega) k hk, hb1at k hk]
          exact hr1 k hk
        · intro k hk
          rw [hb2at k hk]
          exact hr2 k hk
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
          (hrv (c / 16) hc16).2, hlov (c / 16) hc16, hhivv (c / 16) hc16, hψ (c / 16) hc16]
        have hm4 : (c - 4) % 16 = c % 16 - 4 := by omega
        have hd4 : (c - 4) / 16 = c / 16 := by omega
        have e1 : posZ q b (16 * i1.val + c / 16) = a0 (c - 4) := by
          rw [show 16 * i1.val + c / 16 = 16 * ((c - 4) % 16) + (c - 4) / 16 from by
              rw [hm4, hd4]; omega,
            ← tposZ, hval (c - 4) (by omega), if_neg (by omega)]
        have e2 : posZ q b (16 * i3.val + c / 16) = a0 c := by
          rw [show 16 * i3.val + c / 16 = 16 * (c % 16) + c / 16 from by omega, ← tposZ,
            hval c hc, if_neg (by omega)]
        rw [e1, e2, ctLvl, if_neg (by omega),
          show 32 + h.val + 2 * (c / 16) = 32 + c / (2 * 4) from by omega]
      · rw [if_neg (by omega)]
        by_cases h2 : c % 16 = i4.val
        · rw [if_pos (by omega), if_pos (by omega),
            show 16 * (c % 16) + c / 16 - 16 * i4.val = c / 16 from by omega,
            (hrv (c / 16) hc16).1, hlov (c / 16) hc16, hhivv (c / 16) hc16, hψ (c / 16) hc16]
          have e1 : posZ q b (16 * i1.val + c / 16) = a0 c := by
            rw [show 16 * i1.val + c / 16 = 16 * (c % 16) + c / 16 from by omega, ← tposZ,
              hval c hc, if_neg (by omega)]
          have e2 : posZ q b (16 * i3.val + c / 16) = a0 (c + 4) := by
            rw [show 16 * i3.val + c / 16
              = 16 * ((c + 4) % 16) + (c + 4) / 16 from by omega,
              ← tposZ, hval (c + 4) (by omega), if_neg (by omega)]
          rw [e1, e2, ctLvl, if_pos (by omega),
            show 32 + h.val + 2 * (c / 16) = 32 + c / (2 * 4) from by omega]
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

/-- The `len = 2` level, one group: `2` butterflies pairing `4h + j` with `4h + j + 2`. -/
theorem ntt_block_loop3_loop0_walk (SECOND : Bool) (iter : core.ops.range.Range Usize)
    (b : Array I16 256#usize) (qv : Vec256) (h : Usize) (q : ℕ) (Zb A T : ℤ) (Rinv : ZMod q)
    (ψ : ℕ → ZMod q) (a0 : ℕ → ZMod q)
    (hq0 : 0 < (q : ℤ)) (hqlt : (q : ℤ) ≤ 2 ^ 15)
    (hR : ((2 ^ 16 : ℤ) : ZMod q) * Rinv = 1)
    (hQ : ∀ i < 16, (lane16 qv i).toInt = (q : ℤ))
    (hA0 : 0 ≤ A) (hAZ : A * Zb < 2 ^ 15 * (q : ℤ))
    (hT : A * Zb + 2 ^ 15 * (q : ℤ) ≤ 2 ^ 16 * T) (hfit : A + T ≤ 2 ^ 15 - 1)
    (hh : h.val < 4)
    (htbl : ∃ z zq,
      (if SECOND then (do let t ← backend.avx2.ntt.FWD2_Q2; backend.avx2.ntt.ld_tbl t h)
       else (do let t ← backend.avx2.ntt.FWD2_Q1; backend.avx2.ntt.ld_tbl t h))
        = ok (z, zq) ∧ PsiOk z zq (q : ℤ) Zb ∧
        ∀ k < 16, laneZ q z k * Rinv = ψ (64 + h.val + 4 * k))
    (hend : iter.«end».val = 2) (hstartle : iter.start.val ≤ 2)
    (hbnd : Split b (fun v => v < 4 * h.val
        ∨ (4 * h.val ≤ v ∧ v < 4 * h.val + iter.start.val)
        ∨ (4 * h.val + 2 ≤ v ∧ v < 4 * h.val + 2 + iter.start.val)) A T)
    (hval : ∀ c < 256, tposZ q b c =
      if c % 16 < 4 * h.val
        ∨ (4 * h.val ≤ c % 16 ∧ c % 16 < 4 * h.val + iter.start.val)
        ∨ (4 * h.val + 2 ≤ c % 16 ∧ c % 16 < 4 * h.val + 2 + iter.start.val)
      then ctLvl q ψ 64 2 a0 c else a0 c) :
    backend.avx2.ntt.ntt_block_loop3_loop0 SECOND iter b qv h
      ⦃ (r : Array I16 256#usize) =>
          Split r (fun v => v < 4 * h.val + 4) A T ∧
          ∀ c < 256, tposZ q r c =
            if c % 16 < 4 * h.val + 4 then ctLvl q ψ 64 2 a0 c else a0 c ⦄ := by
  unfold backend.avx2.ntt.ntt_block_loop3_loop0
  obtain ⟨z, zq, htz, ⟨hzb, hzqm⟩, hψ⟩ := htbl
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
             let (lo1, hi1) ← backend.avx2.ntt.ct_butterfly lo hi z zq qv
             let i4 ← i + iter.start
             let b1 ← store_i16 b i4 lo1
             let i5 ← i + iter.start
             let i6 ← i5 + 2#usize
             let b2 ← store_i16 b1 i6 hi1
             backend.avx2.ntt.ntt_block_loop3_loop0 SECOND iter1 b2 qv h)
        ⦃ (r : Array I16 256#usize) =>
            Split r (fun v => v < 4 * h.val + 4) A T ∧
            ∀ c < 256, tposZ q r c =
              if c % 16 < 4 * h.val + 4 then ctLvl q ψ 64 2 a0 c else a0 c ⦄
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
      (ct_butterfly_bnd lo' hiv' z zq qv (q : ℤ) Zb A T hQ hq0 hqlt hzqm hlob hhivb hzb hA0 hAZ
        hT hfit)
      (ct_butterfly_val lo' hiv' z zq qv q Zb A T Rinv hq0 hqlt hR hQ hzqm hlob hhivb hzb hA0
        hAZ hT hfit))
    intro r hr
    obtain ⟨lo1, hi1'⟩ := r
    obtain ⟨⟨hr1, hr2⟩, hrv⟩ := hr
    simp only at hr1 hr2 hrv
    show (do let i4 ← i + iter.start
             let b1 ← store_i16 b i4 lo1
             let i5 ← i + iter.start
             let i6 ← i5 + 2#usize
             let b2 ← store_i16 b1 i6 hi1'
             backend.avx2.ntt.ntt_block_loop3_loop0 SECOND iter1 b2 qv h)
        ⦃ (r : Array I16 256#usize) =>
            Split r (fun v => v < 4 * h.val + 4) A T ∧
            ∀ c < 256, tposZ q r c =
              if c % 16 < 4 * h.val + 4 then ctLvl q ψ 64 2 a0 c else a0 c ⦄
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
    apply ntt_block_loop3_loop0_walk SECOND iter1 b2' qv h q Zb A T Rinv ψ a0 hq0 hqlt hR hQ
      hA0 hAZ hT hfit hh ⟨z, zq, htz, ⟨hzb, hzqm⟩, hψ⟩ (by rw [hend']; exact hend) (by omega)
    · constructor
      · intro v hv hP
        rcases (show v = i4.val ∨ v = i6.val ∨ (v ≠ i4.val ∧ v ≠ i6.val) from by omega)
          with rfl | rfl | ⟨hne1, hne2⟩
        · intro k hk
          rw [hb2oth i4.val (by omega) (by omega) k hk, hb1at k hk]
          exact hr1 k hk
        · intro k hk
          rw [hb2at k hk]
          exact hr2 k hk
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
          (hrv (c / 16) hc16).2, hlov (c / 16) hc16, hhivv (c / 16) hc16, hψ (c / 16) hc16]
        have hm4 : (c - 2) % 16 = c % 16 - 2 := by omega
        have hd4 : (c - 2) / 16 = c / 16 := by omega
        have e1 : posZ q b (16 * i1.val + c / 16) = a0 (c - 2) := by
          rw [show 16 * i1.val + c / 16 = 16 * ((c - 2) % 16) + (c - 2) / 16 from by
              rw [hm4, hd4]; omega,
            ← tposZ, hval (c - 2) (by omega), if_neg (by omega)]
        have e2 : posZ q b (16 * i3.val + c / 16) = a0 c := by
          rw [show 16 * i3.val + c / 16 = 16 * (c % 16) + c / 16 from by omega, ← tposZ,
            hval c hc, if_neg (by omega)]
        rw [e1, e2, ctLvl, if_neg (by omega),
          show 64 + h.val + 4 * (c / 16) = 64 + c / (2 * 2) from by omega]
      · rw [if_neg (by omega)]
        by_cases h2 : c % 16 = i4.val
        · rw [if_pos (by omega), if_pos (by omega),
            show 16 * (c % 16) + c / 16 - 16 * i4.val = c / 16 from by omega,
            (hrv (c / 16) hc16).1, hlov (c / 16) hc16, hhivv (c / 16) hc16, hψ (c / 16) hc16]
          have e1 : posZ q b (16 * i1.val + c / 16) = a0 c := by
            rw [show 16 * i1.val + c / 16 = 16 * (c % 16) + c / 16 from by omega, ← tposZ,
              hval c hc, if_neg (by omega)]
          have e2 : posZ q b (16 * i3.val + c / 16) = a0 (c + 2) := by
            rw [show 16 * i3.val + c / 16
              = 16 * ((c + 2) % 16) + (c + 2) / 16 from by omega,
              ← tposZ, hval (c + 2) (by omega), if_neg (by omega)]
          rw [e1, e2, ctLvl, if_pos (by omega),
            show 64 + h.val + 4 * (c / 16) = 64 + c / (2 * 2) from by omega]
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

/-- The `len = 4` level: 2 groups. -/
theorem ntt_block_loop2_walk (SECOND : Bool) (iter : core.ops.range.Range Usize)
    (b : Array I16 256#usize) (qv : Vec256) (q : ℕ) (Zb A T : ℤ) (Rinv : ZMod q)
    (ψ : ℕ → ZMod q) (a0 : ℕ → ZMod q)
    (hq0 : 0 < (q : ℤ)) (hqlt : (q : ℤ) ≤ 2 ^ 15)
    (hR : ((2 ^ 16 : ℤ) : ZMod q) * Rinv = 1)
    (hQ : ∀ i < 16, (lane16 qv i).toInt = (q : ℤ))
    (hA0 : 0 ≤ A) (hAZ : A * Zb < 2 ^ 15 * (q : ℤ))
    (hT : A * Zb + 2 ^ 15 * (q : ℤ) ≤ 2 ^ 16 * T) (hfit : A + T ≤ 2 ^ 15 - 1)
    (htbl : ∀ h : Usize, h.val < 2 → ∃ z zq,
      (if SECOND then (do let t ← backend.avx2.ntt.FWD4_Q2; backend.avx2.ntt.ld_tbl t h)
       else (do let t ← backend.avx2.ntt.FWD4_Q1; backend.avx2.ntt.ld_tbl t h))
        = ok (z, zq) ∧ PsiOk z zq (q : ℤ) Zb ∧
        ∀ k < 16, laneZ q z k * Rinv = ψ (32 + h.val + 2 * k))
    (hend : iter.«end».val = 2) (hstartle : iter.start.val ≤ 2)
    (hbnd : Split b (fun v => v < 8 * iter.start.val) A T)
    (hval : ∀ c < 256, tposZ q b c =
      if c % 16 < 8 * iter.start.val then ctLvl q ψ 32 4 a0 c else a0 c) :
    backend.avx2.ntt.ntt_block_loop2 SECOND iter b qv
      ⦃ (r : Array I16 256#usize) =>
          BlockBnd r (A + T) ∧ ∀ c < 256, tposZ q r c = ctLvl q ψ 32 4 a0 c ⦄ := by
  unfold backend.avx2.ntt.ntt_block_loop2
  by_cases hlt : iter.start.val < iter.«end».val
  · let* ⟨ o, iter1, ho, hstart', hend' ⟩ ← core.iter.range.IteratorRange.next_Usize_some_spec
    rw [ho]; simp only
    apply WP.spec_bind (ntt_block_loop2_loop0_walk SECOND
      { start := 0#usize, «end» := 4#usize } b qv iter.start q Zb A T Rinv ψ a0 hq0 hqlt hR hQ
      hA0 hAZ hT hfit (by omega) (htbl iter.start (by omega)) rfl (by decide) ?_ ?_)
    · intro b1 hb1
      apply ntt_block_loop2_walk SECOND iter1 b1 qv q Zb A T Rinv ψ a0 hq0 hqlt hR hQ hA0 hAZ hT
        hfit htbl (by rw [hend']; exact hend) (by omega)
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
        then ctLvl q ψ 32 4 a0 c else a0 c
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

/-- The `len = 2` level: 4 groups. -/
theorem ntt_block_loop3_walk (SECOND : Bool) (iter : core.ops.range.Range Usize)
    (b : Array I16 256#usize) (qv : Vec256) (q : ℕ) (Zb A T : ℤ) (Rinv : ZMod q)
    (ψ : ℕ → ZMod q) (a0 : ℕ → ZMod q)
    (hq0 : 0 < (q : ℤ)) (hqlt : (q : ℤ) ≤ 2 ^ 15)
    (hR : ((2 ^ 16 : ℤ) : ZMod q) * Rinv = 1)
    (hQ : ∀ i < 16, (lane16 qv i).toInt = (q : ℤ))
    (hA0 : 0 ≤ A) (hAZ : A * Zb < 2 ^ 15 * (q : ℤ))
    (hT : A * Zb + 2 ^ 15 * (q : ℤ) ≤ 2 ^ 16 * T) (hfit : A + T ≤ 2 ^ 15 - 1)
    (htbl : ∀ h : Usize, h.val < 4 → ∃ z zq,
      (if SECOND then (do let t ← backend.avx2.ntt.FWD2_Q2; backend.avx2.ntt.ld_tbl t h)
       else (do let t ← backend.avx2.ntt.FWD2_Q1; backend.avx2.ntt.ld_tbl t h))
        = ok (z, zq) ∧ PsiOk z zq (q : ℤ) Zb ∧
        ∀ k < 16, laneZ q z k * Rinv = ψ (64 + h.val + 4 * k))
    (hend : iter.«end».val = 4) (hstartle : iter.start.val ≤ 4)
    (hbnd : Split b (fun v => v < 4 * iter.start.val) A T)
    (hval : ∀ c < 256, tposZ q b c =
      if c % 16 < 4 * iter.start.val then ctLvl q ψ 64 2 a0 c else a0 c) :
    backend.avx2.ntt.ntt_block_loop3 SECOND iter b qv
      ⦃ (r : Array I16 256#usize) =>
          BlockBnd r (A + T) ∧ ∀ c < 256, tposZ q r c = ctLvl q ψ 64 2 a0 c ⦄ := by
  unfold backend.avx2.ntt.ntt_block_loop3
  by_cases hlt : iter.start.val < iter.«end».val
  · let* ⟨ o, iter1, ho, hstart', hend' ⟩ ← core.iter.range.IteratorRange.next_Usize_some_spec
    rw [ho]; simp only
    apply WP.spec_bind (ntt_block_loop3_loop0_walk SECOND
      { start := 0#usize, «end» := 2#usize } b qv iter.start q Zb A T Rinv ψ a0 hq0 hqlt hR hQ
      hA0 hAZ hT hfit (by omega) (htbl iter.start (by omega)) rfl (by decide) ?_ ?_)
    · intro b1 hb1
      apply ntt_block_loop3_walk SECOND iter1 b1 qv q Zb A T Rinv ψ a0 hq0 hqlt hR hQ hA0 hAZ hT
        hfit htbl (by rw [hend']; exact hend) (by omega)
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
        then ctLvl q ψ 64 2 a0 c else a0 c
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

/-! ## One Gentleman-Sande layer, as a function of the view

The mirror of `ctLvl`.  The negation `State_gs` asks for is written into the definition, because
the inverse side's tables carry it: the code's `z` at the paired index *is* `−ζ`. -/

/-- The result of one Gentleman-Sande layer merging `2·nb` blocks of size `m'` into `nb`. -/
noncomputable def gsLvl (q : ℕ) (ζ : ℕ → ZMod q) (nb m' : ℕ) (a : ℕ → ZMod q) (c : ℕ) : ZMod q :=
  if c % (2 * m') < m' then a c + a (c + m')
  else (-(ζ (2 * nb - 1 - c / (2 * m')))) * (a (c - m') - a c)

theorem gsLvl_hbut (q : ℕ) (ζ : ℕ → ZMod q) (nb m' : ℕ) (a : ℕ → ZMod q) (hm' : 0 < m') :
    ∀ b < nb, ∀ r < m',
      gsLvl q ζ nb m' a (b * (2 * m') + r)
          = a (b * (2 * m') + r) + a (b * (2 * m') + m' + r) ∧
      gsLvl q ζ nb m' a (b * (2 * m') + m' + r)
          = (-(ζ (2 * nb - 1 - b)))
              * (a (b * (2 * m') + r) - a (b * (2 * m') + m' + r)) := by
  intro b hb r hr
  have hre : ∀ t, t < 2 * m' → (b * (2 * m') + t) % (2 * m') = t ∧
      (b * (2 * m') + t) / (2 * m') = b := by
    intro t ht
    constructor
    · rw [show b * (2 * m') + t = t + (2 * m') * b from by ring, Nat.add_mul_mod_self_left,
        Nat.mod_eq_of_lt ht]
    · rw [show b * (2 * m') + t = t + (2 * m') * b from by ring,
        Nat.add_mul_div_left _ _ (by omega), Nat.div_eq_of_lt ht, Nat.zero_add]
  obtain ⟨hm1, hd1⟩ := hre r (by omega)
  obtain ⟨hm2, hd2⟩ := hre (m' + r) (by omega)
  constructor
  · rw [gsLvl, hm1, if_pos hr,
      show b * (2 * m') + r + m' = b * (2 * m') + m' + r from by ring]
  · rw [gsLvl, show b * (2 * m') + m' + r = b * (2 * m') + (m' + r) from by ring, hm2,
      if_neg (by omega), hd2,
      show b * (2 * m') + (m' + r) - m' = b * (2 * m') + r from by omega]

/-! ## The horizontal levels

Before the transpose the array position *is* the coefficient index, so a butterfly on vectors
`(i, i + half)` pairs coefficients `c` and `c + 16·half`: an ordinary Cooley-Tukey layer with
`m' = 16·half`.  ψ is broadcast across the whole group, and the group's ζ index is `nb + b` with
`b = start / (2·half)` — which is what the code's running `k` counts. -/

theorem ntt_block_loop0_loop0_loop0_walk (b : Array I16 256#usize) (qv : Vec256)
    (half start i : Usize) (z zq : Vec256) (q : ℕ) (Zb A T : ℤ) (Rinv : ZMod q)
    (ψ : ℕ → ZMod q) (a0 : ℕ → ZMod q) (nb kk bIdx : ℕ)
    (hq0 : 0 < (q : ℤ)) (hqlt : (q : ℤ) ≤ 2 ^ 15)
    (hR : ((2 ^ 16 : ℤ) : ZMod q) * Rinv = 1)
    (hQ : ∀ j < 16, (lane16 qv j).toInt = (q : ℤ))
    (hA0 : 0 ≤ A) (hAZ : A * Zb < 2 ^ 15 * (q : ℤ))
    (hT : A * Zb + 2 ^ 15 * (q : ℤ) ≤ 2 ^ 16 * T) (hfit : A + T ≤ 2 ^ 15 - 1)
    (hpsi : PsiOk z zq (q : ℤ) Zb)
    (hzk : ∀ k < 16, laneZ q z k * Rinv = ψ kk)
    (hhalf : half.val = 8 ∨ half.val = 4 ∨ half.val = 2 ∨ half.val = 1)
    (hgrp : start.val + 2 * half.val ≤ 16) (hstartb : start.val = bIdx * (2 * half.val))
    (hkk : nb + bIdx = kk)
    (hi : start.val ≤ i.val ∧ i.val ≤ start.val + half.val)
    (hbnd : Split b (fun v => v < start.val
        ∨ (start.val ≤ v ∧ v < i.val)
        ∨ (start.val + half.val ≤ v ∧ v < i.val + half.val)) A T)
    (hval : ∀ c < 256, posZ q b c =
      if c / 16 < start.val ∨ (start.val ≤ c / 16 ∧ c / 16 < i.val)
        ∨ (start.val + half.val ≤ c / 16 ∧ c / 16 < i.val + half.val)
      then ctLvl q ψ nb (16 * half.val) a0 c else a0 c) :
    backend.avx2.ntt.ntt_block_loop0_loop0_loop0 b qv half start z zq i
      ⦃ (r : Array I16 256#usize) =>
          Split r (fun v => v < start.val + 2 * half.val) A T ∧
          ∀ c < 256, posZ q r c =
            if c / 16 < start.val + 2 * half.val
            then ctLvl q ψ nb (16 * half.val) a0 c else a0 c ⦄ := by
  unfold backend.avx2.ntt.ntt_block_loop0_loop0_loop0
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
      (ct_butterfly_bnd lo' hiv' z zq qv (q : ℤ) Zb A T hQ hq0 hqlt hzqm hlob hhivb hzb hA0 hAZ
        hT hfit)
      (ct_butterfly_val lo' hiv' z zq qv q Zb A T Rinv hq0 hqlt hR hQ hzqm hlob hhivb hzb hA0
        hAZ hT hfit))
    intro r hr
    obtain ⟨lo1, hi1'⟩ := r
    obtain ⟨⟨hr1, hr2⟩, hrv⟩ := hr
    simp only at hr1 hr2 hrv
    show (do let b1 ← store_i16 b i lo1
             let b2 ← store_i16 b1 i2 hi1'
             let i3 ← i + 1#usize
             backend.avx2.ntt.ntt_block_loop0_loop0_loop0 b2 qv half start z zq i3)
        ⦃ (r : Array I16 256#usize) =>
            Split r (fun v => v < start.val + 2 * half.val) A T ∧
            ∀ c < 256, posZ q r c =
              if c / 16 < start.val + 2 * half.val
              then ctLvl q ψ nb (16 * half.val) a0 c else a0 c ⦄
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
    apply ntt_block_loop0_loop0_loop0_walk b2' qv half start i3 z zq q Zb A T Rinv ψ a0 nb kk
      bIdx hq0 hqlt hR hQ hA0 hAZ hT hfit ⟨hzb, hzqm⟩ hzk hhalf hgrp hstartb hkk (by omega)
    · constructor
      · intro v hv hP
        rcases (show v = i.val ∨ v = i2.val ∨ (v ≠ i.val ∧ v ≠ i2.val) from by omega)
          with rfl | rfl | ⟨hne1, hne2⟩
        · intro k hk
          rw [hb2oth i.val (by omega) (by omega) k hk, hb1at k hk]
          exact hr1 k hk
        · intro k hk
          rw [hb2at k hk]
          exact hr2 k hk
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
        rw [e1, e2, ctLvl, if_neg hhi2, hzi, hkk]
      · rw [if_neg (by omega)]
        by_cases h2 : c / 16 = i.val
        · rw [if_pos (by omega), if_pos (by omega),
            show c - 16 * i.val = c % 16 from by omega, (hrv (c % 16) hcm).1,
            hlov (c % 16) hcm, hhivv (c % 16) hcm, hzk (c % 16) hcm]
          have e1 : posZ q b (16 * i.val + c % 16) = a0 c := by
            rw [show 16 * i.val + c % 16 = c from by omega, hval c hc, if_neg (by omega)]
          have e2 : posZ q b (16 * i2.val + c % 16) = a0 (c + 16 * half.val) := by
            rw [hval _ (by omega), if_neg (by omega)]
            congr 1
            omega
          have hzi : c / (2 * (16 * half.val)) = bIdx := by
            rcases hhalf with hh | hh | hh | hh <;>
              simp only [hh] at hgrp hstartb hi hlt h2 ⊢ <;> omega
          have hlo2 : c % (2 * (16 * half.val)) < 16 * half.val := by
            rcases hhalf with hh | hh | hh | hh <;>
              simp only [hh] at hgrp hstartb hi hlt h2 ⊢ <;> omega
          rw [e1, e2, ctLvl, if_pos hlo2, hzi, hkk]
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

/-- One horizontal level: the groups of width `2·half`, each with its own broadcast ψ.  The
running `k` counts groups; `hk` ties it to the layer's ζ index `nb + b`, with the group index `b`
carried explicitly so that no division by the variable `half` ever appears. -/
theorem ntt_block_loop0_loop0_walk (SECOND : Bool) (b : Array I16 256#usize) (qv : Vec256)
    (k half start : Usize) (q : ℕ) (Zb A T : ℤ) (Rinv : ZMod q)
    (ψ : ℕ → ZMod q) (a0 : ℕ → ZMod q) (nb bIdx nbT : ℕ)
    (hq0 : 0 < (q : ℤ)) (hqlt : (q : ℤ) ≤ 2 ^ 15)
    (hR : ((2 ^ 16 : ℤ) : ZMod q) * Rinv = 1)
    (hQ : ∀ j < 16, (lane16 qv j).toInt = (q : ℤ))
    (hA0 : 0 ≤ A) (hAZ : A * Zb < 2 ^ 15 * (q : ℤ))
    (hT : A * Zb + 2 ^ 15 * (q : ℤ) ≤ 2 ^ 16 * T) (hfit : A + T ≤ 2 ^ 15 - 1)
    (hzeta : ∀ kk : Usize, kk.val < 256 → ∃ zi zqi : I16,
      backend.crt.zeta SECOND kk = ok zi ∧ backend.crt.zeta_q SECOND kk = ok zqi ∧
      |zi.val| ≤ Zb ∧ (2 ^ 16 : ℤ) ∣ (zqi.val * (q : ℤ) - zi.val) ∧
      (((zi.val : ℤ) : ZMod q)) * Rinv = ψ kk.val)
    (hhalf : half.val = 8 ∨ half.val = 4 ∨ half.val = 2 ∨ half.val = 1)
    (hstartb : start.val = bIdx * (2 * half.val)) (hstart : start.val ≤ 16)
    (hnbT : 16 = nbT * (2 * half.val))
    (hkbnd : k.val + (16 - start.val) ≤ 255)
    (hk : k.val + 1 = nb + bIdx)
    (hbnd : Split b (fun v => v < start.val) A T)
    (hval : ∀ c < 256, posZ q b c =
      if c / 16 < start.val then ctLvl q ψ nb (16 * half.val) a0 c else a0 c) :
    backend.avx2.ntt.ntt_block_loop0_loop0 SECOND b qv k half start
      ⦃ (r : (Array I16 256#usize) × Usize) =>
          BlockBnd r.1 (A + T) ∧
          (∀ c < 256, posZ q r.1 c = ctLvl q ψ nb (16 * half.val) a0 c) ∧
          r.2.val + 1 = nb + nbT ⦄ := by
  unfold backend.avx2.ntt.ntt_block_loop0_loop0
  by_cases hlt : start.val < 16
  · rw [if_pos (by scalar_tac)]
    step*
    obtain ⟨zi, zqi, hzi, hzqi, hzib, hzqid, hzpsi⟩ := hzeta k1 (by omega)
    rw [hzi, bind_tc_ok]
    obtain ⟨z, hz, hzl⟩ := set1_epi16_spec zi
    rw [hz, bind_tc_ok, hzqi, bind_tc_ok]
    obtain ⟨zq, hzq, hzql⟩ := set1_epi16_spec zqi
    rw [hzq, bind_tc_ok]
    have hpsi : PsiOk z zq (q : ℤ) Zb := by
      constructor
      · intro j hj
        rw [show (lane16 z j).toInt = zi.val from by rw [hzl j hj]; rfl]
        exact hzib
      · intro j hj
        rw [show (lane16 zq j).toInt = zqi.val from by rw [hzql j hj]; rfl,
          show (lane16 z j).toInt = zi.val from by rw [hzl j hj]; rfl]
        exact hzqid
    have hzk : ∀ j < 16, laneZ q z j * Rinv = ψ k1.val := by
      intro j hj
      rw [show laneZ q z j = ((zi.val : ℤ) : ZMod q) from by
        unfold laneZ; rw [show (lane16 z j).toInt = zi.val from by rw [hzl j hj]; rfl]]
      exact hzpsi
    have hgrp' : start.val + 2 * half.val ≤ 16 := by
      rcases hhalf with h | h | h | h <;> simp only [h] at hstartb ⊢ <;> omega
    have hkk' : nb + bIdx = k1.val := by omega
    apply WP.spec_bind (ntt_block_loop0_loop0_loop0_walk b qv half start start z zq q Zb A T Rinv
      ψ a0 nb k1.val bIdx hq0 hqlt hR hQ hA0 hAZ hT hfit hpsi hzk hhalf hgrp' hstartb hkk'
      ⟨le_refl _, by omega⟩ ?_ ?_)
    · intro b1 hb1
      obtain ⟨i2, hi2, hi2v⟩ := WP.spec_imp_exists
        (Std.Usize.mul_spec (x := 2#usize) (y := half) (by scalar_tac))
      rw [hi2, bind_tc_ok]
      obtain ⟨start1, hs1, hs1v⟩ := WP.spec_imp_exists
        (Std.Usize.add_spec (x := start) (y := i2) (by scalar_tac))
      rw [hs1, bind_tc_ok]
      have hi2n : i2.val = 2 * half.val := by scalar_tac
      have hs1n : start1.val = start.val + 2 * half.val := by omega
      apply ntt_block_loop0_loop0_walk SECOND b1 qv k1 half start1 q Zb A T Rinv ψ a0 nb
        (bIdx + 1) nbT hq0 hqlt hR hQ hA0 hAZ hT hfit hzeta hhalf
        (by rcases hhalf with h | h | h | h <;> simp only [h] at hstartb hs1n ⊢ <;> omega)
        (by omega) hnbT (by rcases hhalf with h | h | h | h <;> omega) (by omega)
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

/-! ## The re-centring pass preserves residues

`barrett` changes the representative but not the class, so the value view is untouched by it —
which is what lets the growth schedule's two `barrett_block` passes sit inside the transform
without disturbing the transform's own invariant. -/

theorem barrett_block_loop_val (iter : core.ops.range.Range Usize) (b : Array I16 256#usize)
    (m round qv : Vec256) (q : ℕ) (M : ℤ)
    (hQ : ∀ i < 16, (lane16 qv i).toInt = (q : ℤ)) (hM : ∀ i < 16, (lane16 m i).toInt = M)
    (hRnd : ∀ i < 16, (lane16 round i).toInt = 2 ^ 10)
    (hQpos : 0 < (q : ℤ)) (hQlt : (q : ℤ) < 2 ^ 14) (hQodd : ¬ (2 ∣ (q : ℤ)))
    (hMpos : 0 < M) (hMlt : M < 2 ^ 15) (hD : |2 ^ 27 - (q : ℤ) * M| ≤ 2047)
    (hend : iter.«end».val = 16) :
    backend.avx2.ntt.barrett_block_loop iter b m round qv
      ⦃ (r : Array I16 256#usize) => ∀ c < 256, posZ q r c = posZ q b c ⦄ := by
  unfold backend.avx2.ntt.barrett_block_loop
  by_cases hlt : iter.start.val < iter.«end».val
  · let* ⟨ o, iter1, ho, hstart', hend' ⟩ ← core.iter.range.IteratorRange.next_Usize_some_spec
    rw [ho]; simp only
    obtain ⟨v, hv, hvval⟩ := load_posZ q b iter.start (by omega)
    rw [hv, bind_tc_ok]
    apply WP.spec_bind (barrett_lane_spec v m round qv (q : ℤ) M hQ hM hRnd hQpos hQlt hQodd
      hMpos hMlt hD)
    intro v1 hv1
    obtain ⟨b1, hb1, hb1v⟩ := store_posZ q b iter.start v1 (by omega)
    rw [hb1, bind_tc_ok]
    apply WP.spec_mono (barrett_block_loop_val iter1 b1 m round qv q M hQ hM hRnd hQpos hQlt
      hQodd hMpos hMlt hD (by rw [hend']; exact hend))
    intro r hr c hc
    rw [hr c hc, hb1v c hc]
    by_cases hP : 16 * iter.start.val ≤ c ∧ c < 16 * iter.start.val + 16
    · rw [if_pos hP]
      obtain ⟨hdvd, -⟩ := hv1 (c - 16 * iter.start.val) (by omega)
      have : ((lane16 v1 (c - 16 * iter.start.val)).toInt : ZMod q)
          = ((lane16 v (c - 16 * iter.start.val)).toInt : ZMod q) := by
        obtain ⟨w, hw⟩ := hdvd
        have := (ZMod.intCast_zmod_eq_zero_iff_dvd
          ((lane16 v1 (c - 16 * iter.start.val)).toInt
            - (lane16 v (c - 16 * iter.start.val)).toInt) q).mpr ⟨w, hw⟩
        push_cast at this
        linear_combination this
      rw [show laneZ q v1 (c - 16 * iter.start.val)
          = ((lane16 v1 (c - 16 * iter.start.val)).toInt : ZMod q) from rfl, this,
        show ((lane16 v (c - 16 * iter.start.val)).toInt : ZMod q)
          = laneZ q v (c - 16 * iter.start.val) from rfl,
        hvval (c - 16 * iter.start.val) (by omega),
        show 16 * iter.start.val + (c - 16 * iter.start.val) = c from by omega]
    · rw [if_neg hP]
  · let* ⟨ o, iter1, hnone, _ ⟩ ← core.iter.range.IteratorRange.next_Usize_none_spec
    rw [hnone]; simp only [WP.spec_ok]
    refine fun c _ => ?_
    trivial
termination_by iter.«end».val - iter.start.val
decreasing_by scalar_decr_tac

/-- **`barrett_block` preserves the value view.** -/
theorem barrett_block_val (b : Array I16 256#usize) (m round qv : Vec256) (q : ℕ) (M : ℤ)
    (hQ : ∀ i < 16, (lane16 qv i).toInt = (q : ℤ)) (hM : ∀ i < 16, (lane16 m i).toInt = M)
    (hRnd : ∀ i < 16, (lane16 round i).toInt = 2 ^ 10)
    (hQpos : 0 < (q : ℤ)) (hQlt : (q : ℤ) < 2 ^ 14) (hQodd : ¬ (2 ∣ (q : ℤ)))
    (hMpos : 0 < M) (hMlt : M < 2 ^ 15) (hD : |2 ^ 27 - (q : ℤ) * M| ≤ 2047) :
    backend.avx2.ntt.barrett_block b m round qv
      ⦃ (r : Array I16 256#usize) => ∀ c < 256, posZ q r c = posZ q b c ⦄ := by
  unfold backend.avx2.ntt.barrett_block
  exact barrett_block_loop_val _ b m round qv q M hQ hM hRnd hQpos hQlt hQodd hMpos hMlt hD rfl

/-! ## The horizontal half, unrolled

Four levels at `half = 8, 4, 2, 1`, i.e. Cooley-Tukey layers 0–3 with `nb = 1, 2, 4, 8`.  The
`barrett_block` after level 2 changes representatives only, so the value view passes through it.
The running `k` ends at 15, which is `2·8 − 1`: exactly the ζ index the next layer wants. -/

/-- The four horizontal layers, composed. -/
noncomputable def fwdH (q : ℕ) (ψ : ℕ → ZMod q) (f : ℕ → ZMod q) : ℕ → ZMod q :=
  ctLvl q ψ 8 16 (ctLvl q ψ 4 32 (ctLvl q ψ 2 64 (ctLvl q ψ 1 128 f)))

theorem ntt_block_loop0_walk_q2 (b : Array I16 256#usize) (qv bm round : Vec256)
    (Rinv : ZMod 10753) (ψ : ℕ → ZMod 10753) (f : ℕ → ZMod 10753)
    (hR : ((2 ^ 16 : ℤ) : ZMod 10753) * Rinv = 1)
    (hQ : ∀ i < 16, (lane16 qv i).toInt = 10753)
    (hM : ∀ i < 16, (lane16 bm i).toInt = 12482)
    (hRnd : ∀ i < 16, (lane16 round i).toInt = 2 ^ 10)
    (hzeta : ∀ kk : Usize, kk.val < 256 → ∃ zi zqi : I16,
      backend.crt.zeta true kk = ok zi ∧ backend.crt.zeta_q true kk = ok zqi ∧
      |zi.val| ≤ 5376 ∧ (2 ^ 16 : ℤ) ∣ (zqi.val * 10753 - zi.val) ∧
      (((zi.val : ℤ) : ZMod 10753)) * Rinv = ψ kk.val)
    (hb : BlockBnd b 5376) (hv : ∀ c < 256, posZ 10753 b c = f c) :
    backend.avx2.ntt.ntt_block_loop0 true b qv bm round 0#usize 8#usize 0#usize
      ⦃ (r : Array I16 256#usize) =>
          BlockBnd r 11194 ∧ ∀ c < 256, posZ 10753 r c = fwdH 10753 ψ f c ⦄ := by
  obtain ⟨s1, s2, s3, s4, -, -⟩ := growth_q2
  have hq0 : (0 : ℤ) < ((10753 : ℕ) : ℤ) := by norm_num
  have hqlt : ((10753 : ℕ) : ℤ) ≤ 2 ^ 15 := by norm_num
  have hQ' : ∀ i < 16, (lane16 qv i).toInt = ((10753 : ℕ) : ℤ) := by
    intro i hi; rw [hQ i hi]; norm_num
  have hbar : ∀ (bb : Array I16 256#usize),
      backend.avx2.ntt.barrett_block bb bm round qv
        ⦃ (r : Array I16 256#usize) =>
            BlockBnd r 5376 ∧ ∀ c < 256, posZ 10753 r c = posZ 10753 bb c ⦄ := by
    intro bb
    exact spec_and
      (WP.spec_mono (barrett_block_bnd bb bm round qv 10753 12482 hQ hM hRnd (by norm_num)
        (by norm_num) (by decide) (by norm_num) (by norm_num) (by norm_num))
        (fun r hr => hr.mono (by norm_num)))
      (barrett_block_val bb bm round qv 10753 12482 hQ' hM hRnd hq0 (by norm_num) (by decide)
        (by norm_num) (by norm_num) (by norm_num))
  -- level 0, `half = 8`
  unfold backend.avx2.ntt.ntt_block_loop0
  rw [if_pos (by scalar_tac)]
  apply WP.spec_bind (ntt_block_loop0_loop0_walk true b qv 0#usize 8#usize 0#usize 10753 5376
    5376 5818 Rinv ψ f 1 0 1 hq0 hqlt hR hQ' (by norm_num) s1.1 s1.2.1 s1.2.2 hzeta
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (initSplit (by simp) hb) (by intro c hc; rw [hv c hc, if_neg (by simp)]))
  rintro ⟨b1, k1⟩ ⟨hb1, hv1, hk1⟩
  simp only at hb1 hv1 hk1
  show (do let b2 ← (if (0#usize) = 2#usize then backend.avx2.ntt.barrett_block b1 bm round qv
             else ok b1)
           let half1 ← 8#usize / 2#usize
           let level1 ← 0#usize + 1#usize
           backend.avx2.ntt.ntt_block_loop0 true b2 qv bm round k1 half1 level1)
      ⦃ (r : Array I16 256#usize) =>
          BlockBnd r 11194 ∧ ∀ c < 256, posZ 10753 r c = fwdH 10753 ψ f c ⦄
  rw [if_neg (by decide), bind_tc_ok,
    show (8#usize / 2#usize : Result Usize) = ok 4#usize from rfl, bind_tc_ok,
    show (0#usize + 1#usize : Result Usize) = ok 1#usize from usize_add_lit (by scalar_tac) (by rfl),
    bind_tc_ok]
  have e8 : (16 : ℕ) * (8#usize).val = 128 := by scalar_tac
  have e4 : (16 : ℕ) * (4#usize).val = 64 := by scalar_tac
  have e2 : (16 : ℕ) * (2#usize).val = 32 := by scalar_tac
  have e1 : (16 : ℕ) * (1#usize).val = 16 := by scalar_tac
  rw [e8] at hv1
  -- level 1, `half = 4`
  unfold backend.avx2.ntt.ntt_block_loop0
  rw [if_pos (by scalar_tac)]
  apply WP.spec_bind (ntt_block_loop0_loop0_walk true b1 qv k1 4#usize 0#usize 10753 5376
    11194 6295 Rinv ψ (ctLvl 10753 ψ 1 128 f) 2 0 2 hq0 hqlt hR hQ' (by norm_num) s2.1 s2.2.1
    s2.2.2 hzeta (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by omega) (by omega)
    (initSplit (by simp) hb1) (by intro c hc; rw [hv1 c hc, if_neg (by simp)]))
  rintro ⟨b2, k2⟩ ⟨hb2, hv2, hk2⟩
  simp only at hb2 hv2 hk2
  rw [e4] at hv2
  show (do let b3 ← (if (1#usize) = 2#usize then backend.avx2.ntt.barrett_block b2 bm round qv
             else ok b2)
           let half1 ← 4#usize / 2#usize
           let level1 ← 1#usize + 1#usize
           backend.avx2.ntt.ntt_block_loop0 true b3 qv bm round k2 half1 level1)
      ⦃ (r : Array I16 256#usize) =>
          BlockBnd r 11194 ∧ ∀ c < 256, posZ 10753 r c = fwdH 10753 ψ f c ⦄
  rw [if_neg (by decide), bind_tc_ok,
    show (4#usize / 2#usize : Result Usize) = ok 2#usize from rfl, bind_tc_ok,
    show (1#usize + 1#usize : Result Usize) = ok 2#usize from usize_add_lit (by scalar_tac) (by rfl),
    bind_tc_ok]
  -- level 2, `half = 2`, then the re-centring pass
  unfold backend.avx2.ntt.ntt_block_loop0
  rw [if_pos (by scalar_tac)]
  apply WP.spec_bind (ntt_block_loop0_loop0_walk true b2 qv k2 2#usize 0#usize 10753 5376
    17489 6812 Rinv ψ (ctLvl 10753 ψ 2 64 (ctLvl 10753 ψ 1 128 f)) 4 0 4 hq0 hqlt hR hQ'
    (by norm_num) s3.1 s3.2.1 s3.2.2 hzeta (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by omega) (by omega)
    (initSplit (by simp) hb2) (by intro c hc; rw [hv2 c hc, if_neg (by simp)]))
  rintro ⟨b3, k3⟩ ⟨hb3, hv3, hk3⟩
  simp only at hb3 hv3 hk3
  rw [e2] at hv3
  show (do let b4 ← (if (2#usize) = 2#usize then backend.avx2.ntt.barrett_block b3 bm round qv
             else ok b3)
           let half1 ← 2#usize / 2#usize
           let level1 ← 2#usize + 1#usize
           backend.avx2.ntt.ntt_block_loop0 true b4 qv bm round k3 half1 level1)
      ⦃ (r : Array I16 256#usize) =>
          BlockBnd r 11194 ∧ ∀ c < 256, posZ 10753 r c = fwdH 10753 ψ f c ⦄
  rw [if_pos rfl]
  apply WP.spec_bind (hbar b3)
  rintro b4 ⟨hb4, hv4⟩
  rw [show (2#usize / 2#usize : Result Usize) = ok 1#usize from rfl, bind_tc_ok,
    show (2#usize + 1#usize : Result Usize) = ok 3#usize from usize_add_lit (by scalar_tac) (by rfl),
    bind_tc_ok]
  -- level 3, `half = 1`, from a centred block again
  unfold backend.avx2.ntt.ntt_block_loop0
  rw [if_pos (by scalar_tac)]
  apply WP.spec_bind (ntt_block_loop0_loop0_walk true b4 qv k3 1#usize 0#usize 10753 5376
    5376 5818 Rinv ψ (ctLvl 10753 ψ 4 32 (ctLvl 10753 ψ 2 64 (ctLvl 10753 ψ 1 128 f))) 8 0 8
    hq0 hqlt hR hQ' (by norm_num) s1.1 s1.2.1 s1.2.2 hzeta (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by omega) (by omega)
    (initSplit (by simp) hb4)
    (by intro c hc; rw [hv4 c hc, hv3 c hc, if_neg (by simp)]))
  rintro ⟨b5, k5⟩ ⟨hb5, hv5, hk5⟩
  simp only at hb5 hv5 hk5
  rw [e1] at hv5
  show (do let b6 ← (if (3#usize) = 2#usize then backend.avx2.ntt.barrett_block b5 bm round qv
             else ok b5)
           let half1 ← 1#usize / 2#usize
           let level1 ← 3#usize + 1#usize
           backend.avx2.ntt.ntt_block_loop0 true b6 qv bm round k5 half1 level1)
      ⦃ (r : Array I16 256#usize) =>
          BlockBnd r 11194 ∧ ∀ c < 256, posZ 10753 r c = fwdH 10753 ψ f c ⦄
  rw [if_neg (by decide), bind_tc_ok,
    show (1#usize / 2#usize : Result Usize) = ok 0#usize from rfl, bind_tc_ok,
    show (3#usize + 1#usize : Result Usize) = ok 4#usize from usize_add_lit (by scalar_tac) (by rfl),
    bind_tc_ok]
  -- `half = 0`: the loop is done
  unfold backend.avx2.ntt.ntt_block_loop0
  rw [if_neg (by scalar_tac)]
  simp only [WP.spec_ok]
  exact ⟨hb5, fun c hc => by rw [hv5 c hc, fwdH]⟩

/-! ## The whole forward transform

Eight Cooley-Tukey layers: four horizontal, a transpose, four vertical, and a transpose back,
with the two `barrett_block` passes transparent to the value view. -/

/-- The eight layers, composed. -/
noncomputable def fwdAll (q : ℕ) (ψ : ℕ → ZMod q) (f : ℕ → ZMod q) : ℕ → ZMod q :=
  ctLvl q ψ 128 1 (ctLvl q ψ 64 2 (ctLvl q ψ 32 4 (ctLvl q ψ 16 8 (fwdH q ψ f))))

theorem ntt_block_walk_q2 (b : Array I16 256#usize) (Rinv : ZMod 10753)
    (ψ f : ℕ → ZMod 10753)
    (hR : ((2 ^ 16 : ℤ) : ZMod 10753) * Rinv = 1)
    (hzeta : ∀ kk : Usize, kk.val < 256 → ∃ zi zqi : I16,
      backend.crt.zeta true kk = ok zi ∧ backend.crt.zeta_q true kk = ok zqi ∧
      |zi.val| ≤ 5376 ∧ (2 ^ 16 : ℤ) ∣ (zqi.val * 10753 - zi.val) ∧
      (((zi.val : ℤ) : ZMod 10753)) * Rinv = ψ kk.val)
    (htbl8 : ∃ z zq,
      (do let t ← backend.avx2.ntt.FWD8_Q2; backend.avx2.ntt.ld_tbl t 0#usize) = ok (z, zq) ∧
        PsiOk z zq 10753 5376 ∧ ∀ k < 16, laneZ 10753 z k * Rinv = ψ (16 + k))
    (htbl4 : ∀ h : Usize, h.val < 2 → ∃ z zq,
      (do let t ← backend.avx2.ntt.FWD4_Q2; backend.avx2.ntt.ld_tbl t h) = ok (z, zq) ∧
        PsiOk z zq 10753 5376 ∧ ∀ k < 16, laneZ 10753 z k * Rinv = ψ (32 + h.val + 2 * k))
    (htbl2 : ∀ h : Usize, h.val < 4 → ∃ z zq,
      (do let t ← backend.avx2.ntt.FWD2_Q2; backend.avx2.ntt.ld_tbl t h) = ok (z, zq) ∧
        PsiOk z zq 10753 5376 ∧ ∀ k < 16, laneZ 10753 z k * Rinv = ψ (64 + h.val + 4 * k))
    (htbl1 : ∀ h : Usize, h.val < 8 → ∃ z zq,
      (do let t ← backend.avx2.ntt.FWD1_Q2; backend.avx2.ntt.ld_tbl t h) = ok (z, zq) ∧
        PsiOk z zq 10753 5376 ∧ ∀ k < 16, laneZ 10753 z k * Rinv = ψ (128 + h.val + 8 * k))
    (hb : BlockBnd b 5376) (hv : ∀ c < 256, posZ 10753 b c = f c) :
    backend.avx2.ntt.ntt_block true b
      ⦃ (r : Array I16 256#usize) =>
          BlockBnd r 5376 ∧ ∀ c < 256, posZ 10753 r c = fwdAll 10753 ψ f c ⦄ := by
  obtain ⟨s1, s2, s3, s4, -, -⟩ := growth_q2
  have hq0 : (0 : ℤ) < ((10753 : ℕ) : ℤ) := by norm_num
  have hqlt : ((10753 : ℕ) : ℤ) ≤ 2 ^ 15 := by norm_num
  unfold backend.avx2.ntt.ntt_block backend.crt.q backend.crt.barrett_m
  simp only [if_true, bind_tc_ok]
  obtain ⟨qv, hqv, hqvl⟩ := set1_epi16_spec backend.crt.Q2
  rw [hqv, bind_tc_ok]
  obtain ⟨bm, hbm, hbml⟩ := set1_epi16_spec backend.crt.Q2_BARRETT_M
  rw [hbm, bind_tc_ok]
  have hSH : (backend.crt.BARRETT_SH : I32).val = 11 := by
    simp only [backend.crt.BARRETT_SH]; rfl
  step*
  have hi2e : i2 = 10#i32 := IScalar.eq_of_val_eq (by rw [i2_post, hSH]; rfl)
  rw [hi2e, show (1#i16 <<< (10#i32) : Result I16) = ok 1024#i16 from rfl, bind_tc_ok]
  obtain ⟨rnd, hrnd, hrndl⟩ := set1_epi16_spec 1024#i16
  rw [hrnd, bind_tc_ok]
  have hQ : ∀ j < 16, (lane16 qv j).toInt = 10753 := fun j hj => by
    rw [hqvl j hj]; simp only [backend.crt.Q2]; decide
  have hQ' : ∀ j < 16, (lane16 qv j).toInt = ((10753 : ℕ) : ℤ) := by
    intro j hj; rw [hQ j hj]; norm_num
  have hM : ∀ j < 16, (lane16 bm j).toInt = 12482 := fun j hj => by
    rw [hbml j hj]; simp only [backend.crt.Q2_BARRETT_M]; decide
  have hRnd : ∀ j < 16, (lane16 rnd j).toInt = 2 ^ 10 := fun j hj => by
    rw [hrndl j hj]; decide
  have hbar : ∀ (bb : Array I16 256#usize),
      backend.avx2.ntt.barrett_block bb bm rnd qv
        ⦃ (r : Array I16 256#usize) =>
            BlockBnd r 5376 ∧ ∀ c < 256, posZ 10753 r c = posZ 10753 bb c ⦄ := by
    intro bb
    exact spec_and
      (WP.spec_mono (barrett_block_bnd bb bm rnd qv 10753 12482 hQ hM hRnd (by norm_num)
        (by norm_num) (by decide) (by norm_num) (by norm_num) (by norm_num))
        (fun r hr => hr.mono (by norm_num)))
      (barrett_block_val bb bm rnd qv 10753 12482 hQ' hM hRnd hq0 (by norm_num) (by decide)
        (by norm_num) (by norm_num) (by norm_num))
  -- the horizontal half
  apply WP.spec_bind (ntt_block_loop0_walk_q2 b qv bm rnd Rinv ψ f hR hQ hM hRnd hzeta hb hv)
  rintro b1 ⟨hb1, hv1⟩
  -- into coefficient coordinates
  apply WP.spec_bind (spec_and (transpose16_bnd b1 hb1) (transpose16_tpos 10753 b1))
  rintro b2 ⟨hb2, ht2⟩
  have hv2 : ∀ c < 256, tposZ 10753 b2 c = fwdH 10753 ψ f c := fun c hc => by
    rw [ht2 c hc, hv1 c hc]
  -- three vertical levels
  apply WP.spec_bind (ntt_block_loop1_walk true { start := 0#usize, «end» := 8#usize } b2 qv
    10753 5376 11194 6295 Rinv ψ (fwdH 10753 ψ f) hq0 hqlt hR hQ' (by norm_num) s2.1 s2.2.1
    s2.2.2 htbl8 rfl (initSplit (by simp) hb2)
    (by intro c hc; rw [hv2 c hc, if_neg (by simp)]))
  rintro b3 ⟨hb3, hv3⟩
  apply WP.spec_bind (ntt_block_loop2_walk true { start := 0#usize, «end» := 2#usize } b3 qv
    10753 5376 17489 6812 Rinv ψ (ctLvl 10753 ψ 16 8 (fwdH 10753 ψ f)) hq0 hqlt hR hQ'
    (by norm_num) s3.1 s3.2.1 s3.2.2 htbl4 rfl (by decide) (initSplit (by simp) hb3)
    (by intro c hc; rw [hv3 c hc, if_neg (by simp)]))
  rintro b4 ⟨hb4, hv4⟩
  apply WP.spec_bind (ntt_block_loop3_walk true { start := 0#usize, «end» := 4#usize } b4 qv
    10753 5376 24301 7370 Rinv ψ (ctLvl 10753 ψ 32 4 (ctLvl 10753 ψ 16 8 (fwdH 10753 ψ f)))
    hq0 hqlt hR hQ' (by norm_num) s4.1 s4.2.1 s4.2.2 htbl2 rfl (by decide)
    (initSplit (by simp) hb4) (by intro c hc; rw [hv4 c hc, if_neg (by simp)]))
  rintro b5 ⟨hb5, hv5⟩
  -- re-centre, the last level, transpose back, re-centre
  apply WP.spec_bind (hbar b5)
  rintro b6 ⟨hb6, hv6⟩
  apply WP.spec_bind (ntt_block_loop4_walk true { start := 0#usize, «end» := 8#usize } b6 qv
    10753 5376 5376 5818 Rinv ψ
    (ctLvl 10753 ψ 64 2 (ctLvl 10753 ψ 32 4 (ctLvl 10753 ψ 16 8 (fwdH 10753 ψ f))))
    hq0 hqlt hR hQ' (by norm_num) s1.1 s1.2.1 s1.2.2 htbl1 rfl
    (initSplit (by simp) (hb6.mono (by norm_num)))
    (by intro c hc
        rw [show tposZ 10753 b6 c = posZ 10753 b6 (16 * (c % 16) + c / 16) from rfl,
          hv6 _ (by omega), show posZ 10753 b5 (16 * (c % 16) + c / 16)
            = tposZ 10753 b5 c from rfl, hv5 c hc, if_neg (by simp)]))
  rintro b7 ⟨hb7, hv7⟩
  apply WP.spec_bind (spec_and (transpose16_bnd b7 hb7) (transpose16_pos 10753 b7))
  rintro b8 ⟨hb8, ht8⟩
  apply WP.spec_mono (hbar b8)
  rintro r ⟨hbr, hvr⟩
  refine ⟨hbr, fun c hc => ?_⟩
  rw [hvr c hc, ht8 c hc, hv7 c hc, fwdAll]

/-! ## …and the eight layers are the transform

`State_ct` applied eight times, from the untransformed state to the leaf state.  This is where
the code walk meets `NttAlgebra`: after `ntt_block` the block holds, coefficient by coefficient,
the evaluation of the input polynomial at the 256 leaf constants. -/

theorem fwdAll_State {q : ℕ} (ψ : ℕ → ZMod q)
    (hsq : ∀ k, 1 ≤ k → k < 256 → ψ k ^ 2 = NttAlg.cst ψ k) (f : ℕ → ZMod q) :
    NttAlg.State ψ 256 1 1 f (fwdAll q ψ f) := by
  have h0 : NttAlg.State ψ 1 256 1 f f :=
    NttAlg.State_root_intro (fun r _ => by ring)
  have h1 : NttAlg.State ψ 2 128 1 f (ctLvl q ψ 1 128 f) :=
    NttAlg.State_ct hsq (by norm_num) (by norm_num) h0 (ctLvl_hbut q ψ 1 128 f (by norm_num))
  have h2 : NttAlg.State ψ 4 64 1 f (ctLvl q ψ 2 64 (ctLvl q ψ 1 128 f)) :=
    NttAlg.State_ct hsq (by norm_num) (by norm_num) h1 (ctLvl_hbut q ψ 2 64 _ (by norm_num))
  have h3 : NttAlg.State ψ 8 32 1 f (ctLvl q ψ 4 32 (ctLvl q ψ 2 64 (ctLvl q ψ 1 128 f))) :=
    NttAlg.State_ct hsq (by norm_num) (by norm_num) h2 (ctLvl_hbut q ψ 4 32 _ (by norm_num))
  have h4 : NttAlg.State ψ 16 16 1 f (fwdH q ψ f) :=
    NttAlg.State_ct hsq (by norm_num) (by norm_num) h3 (ctLvl_hbut q ψ 8 16 _ (by norm_num))
  have h5 : NttAlg.State ψ 32 8 1 f (ctLvl q ψ 16 8 (fwdH q ψ f)) :=
    NttAlg.State_ct hsq (by norm_num) (by norm_num) h4 (ctLvl_hbut q ψ 16 8 _ (by norm_num))
  have h6 : NttAlg.State ψ 64 4 1 f (ctLvl q ψ 32 4 (ctLvl q ψ 16 8 (fwdH q ψ f))) :=
    NttAlg.State_ct hsq (by norm_num) (by norm_num) h5 (ctLvl_hbut q ψ 32 4 _ (by norm_num))
  have h7 : NttAlg.State ψ 128 2 1 f
      (ctLvl q ψ 64 2 (ctLvl q ψ 32 4 (ctLvl q ψ 16 8 (fwdH q ψ f)))) :=
    NttAlg.State_ct hsq (by norm_num) (by norm_num) h6 (ctLvl_hbut q ψ 64 2 _ (by norm_num))
  exact NttAlg.State_ct hsq (by norm_num) (by norm_num) h7 (ctLvl_hbut q ψ 128 1 _ (by norm_num))

/-! ## The forward transform, unconditionally

Instantiating the walk with the real `q₂` tables.  Nothing is assumed: the ψ tables' properties
come from `Kopis/Avx2/Tables.lean` and `Kopis/Avx2/NttZeta.lean`, both of which are `decide`d
over the literal arrays. -/

theorem ntt_block_leaf_q2 (b : Array I16 256#usize) (f : ℕ → ZMod 10753)
    (hb : BlockBnd b 5376) (hv : ∀ c < 256, posZ 10753 b c = f c) :
    backend.avx2.ntt.ntt_block true b
      ⦃ (r : Array I16 256#usize) =>
          BlockBnd r 5376 ∧ ∀ c < 256, posZ 10753 r c = fwdAll 10753 zeta2 f c ⦄ := by
  refine ntt_block_walk_q2 b (1764 : ZMod 10753) zeta2 f (by decide) ?_ ?_ ?_ ?_ ?_ hb hv
  · intro kk hkk
    obtain ⟨zi, zqi, h1, h2, h3, h4, h5⟩ := zeta_table_ok_q2 kk hkk
    exact ⟨zi, zqi, h1, h2, h3, h4, by rw [h5]; rfl⟩
  · obtain ⟨z, zq, h1, h2, h3⟩ := fwd8_q2_ok 0#usize (by simp)
    refine ⟨z, zq, h1, h2, fun k hk => ?_⟩
    rw [show laneZ 10753 z k = (((lane16 z k).toInt : ℤ) : ZMod 10753) from rfl, h3 k hk]
    rw [show ((16#isize).val + (0#usize).val * (0#isize).val + k * (1#isize).val).toNat
      = 16 + k from by scalar_tac]
    rfl
  · intro h hh
    obtain ⟨z, zq, h1, h2, h3⟩ := fwd4_q2_ok h hh
    refine ⟨z, zq, h1, h2, fun k hk => ?_⟩
    rw [show laneZ 10753 z k = (((lane16 z k).toInt : ℤ) : ZMod 10753) from rfl, h3 k hk]
    rw [show ((32#isize).val + h.val * (1#isize).val + k * (2#isize).val).toNat
      = 32 + h.val + 2 * k from by scalar_tac]
    rfl
  · intro h hh
    obtain ⟨z, zq, h1, h2, h3⟩ := fwd2_q2_ok h hh
    refine ⟨z, zq, h1, h2, fun k hk => ?_⟩
    rw [show laneZ 10753 z k = (((lane16 z k).toInt : ℤ) : ZMod 10753) from rfl, h3 k hk]
    rw [show ((64#isize).val + h.val * (1#isize).val + k * (4#isize).val).toNat
      = 64 + h.val + 4 * k from by scalar_tac]
    rfl
  · intro h hh
    obtain ⟨z, zq, h1, h2, h3⟩ := fwd1_q2_ok h hh
    refine ⟨z, zq, h1, h2, fun k hk => ?_⟩
    rw [show laneZ 10753 z k = (((lane16 z k).toInt : ℤ) : ZMod 10753) from rfl, h3 k hk]
    rw [show ((128#isize).val + h.val * (1#isize).val + k * (8#isize).val).toNat
      = 128 + h.val + 8 * k from by scalar_tac]
    rfl

/-- **The forward transform reaches the leaf state.**  Composing the walk with the algebra: after
`ntt_block`, the block holds the evaluation of its input at the 256 leaf constants of `q₂`'s CRT
tree.  This is the shape `State_leaf_mul_q2` consumes. -/
theorem ntt_block_State_q2 (b : Array I16 256#usize) (f : ℕ → ZMod 10753)
    (hb : BlockBnd b 5376) (hv : ∀ c < 256, posZ 10753 b c = f c) :
    backend.avx2.ntt.ntt_block true b
      ⦃ (r : Array I16 256#usize) =>
          BlockBnd r 5376 ∧ (∀ c < 256, posZ 10753 r c = fwdAll 10753 zeta2 f c) ∧
          NttAlg.State zeta2 256 1 1 f (fwdAll 10753 zeta2 f) ⦄ := by
  apply WP.spec_mono (ntt_block_leaf_q2 b f hb hv)
  exact fun r hr => ⟨hr.1, hr.2, fwdAll_State zeta2 zeta2_sq f⟩

theorem ntt_block_loop0_walk_q1 (b : Array I16 256#usize) (qv bm round : Vec256)
    (Rinv : ZMod 7681) (ψ : ℕ → ZMod 7681) (f : ℕ → ZMod 7681)
    (hR : ((2 ^ 16 : ℤ) : ZMod 7681) * Rinv = 1)
    (hQ : ∀ i < 16, (lane16 qv i).toInt = 7681)
    (hM : ∀ i < 16, (lane16 bm i).toInt = 17474)
    (hRnd : ∀ i < 16, (lane16 round i).toInt = 2 ^ 10)
    (hzeta : ∀ kk : Usize, kk.val < 256 → ∃ zi zqi : I16,
      backend.crt.zeta false kk = ok zi ∧ backend.crt.zeta_q false kk = ok zqi ∧
      |zi.val| ≤ 3840 ∧ (2 ^ 16 : ℤ) ∣ (zqi.val * 7681 - zi.val) ∧
      (((zi.val : ℤ) : ZMod 7681)) * Rinv = ψ kk.val)
    (hb : BlockBnd b 3840) (hv : ∀ c < 256, posZ 7681 b c = f c) :
    backend.avx2.ntt.ntt_block_loop0 false b qv bm round 0#usize 8#usize 0#usize
      ⦃ (r : Array I16 256#usize) =>
          BlockBnd r 7906 ∧ ∀ c < 256, posZ 7681 r c = fwdH 7681 ψ f c ⦄ := by
  obtain ⟨s1, s2, s3, s4, -, -⟩ := growth_q1
  have hq0 : (0 : ℤ) < ((7681 : ℕ) : ℤ) := by norm_num
  have hqlt : ((7681 : ℕ) : ℤ) ≤ 2 ^ 15 := by norm_num
  have hQ' : ∀ i < 16, (lane16 qv i).toInt = ((7681 : ℕ) : ℤ) := by
    intro i hi; rw [hQ i hi]; norm_num
  have hbar : ∀ (bb : Array I16 256#usize),
      backend.avx2.ntt.barrett_block bb bm round qv
        ⦃ (r : Array I16 256#usize) =>
            BlockBnd r 3840 ∧ ∀ c < 256, posZ 7681 r c = posZ 7681 bb c ⦄ := by
    intro bb
    exact spec_and
      (WP.spec_mono (barrett_block_bnd bb bm round qv 7681 17474 hQ hM hRnd (by norm_num)
        (by norm_num) (by decide) (by norm_num) (by norm_num) (by norm_num))
        (fun r hr => hr.mono (by norm_num)))
      (barrett_block_val bb bm round qv 7681 17474 hQ' hM hRnd hq0 (by norm_num) (by decide)
        (by norm_num) (by norm_num) (by norm_num))
  -- level 0, `half = 8`
  unfold backend.avx2.ntt.ntt_block_loop0
  rw [if_pos (by scalar_tac)]
  apply WP.spec_bind (ntt_block_loop0_loop0_walk false b qv 0#usize 8#usize 0#usize 7681 3840
    3840 4066 Rinv ψ f 1 0 1 hq0 hqlt hR hQ' (by norm_num) s1.1 s1.2.1 s1.2.2 hzeta
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (initSplit (by simp) hb) (by intro c hc; rw [hv c hc, if_neg (by simp)]))
  rintro ⟨b1, k1⟩ ⟨hb1, hv1, hk1⟩
  simp only at hb1 hv1 hk1
  show (do let b2 ← (if (0#usize) = 2#usize then backend.avx2.ntt.barrett_block b1 bm round qv
             else ok b1)
           let half1 ← 8#usize / 2#usize
           let level1 ← 0#usize + 1#usize
           backend.avx2.ntt.ntt_block_loop0 false b2 qv bm round k1 half1 level1)
      ⦃ (r : Array I16 256#usize) =>
          BlockBnd r 7906 ∧ ∀ c < 256, posZ 7681 r c = fwdH 7681 ψ f c ⦄
  rw [if_neg (by decide), bind_tc_ok,
    show (8#usize / 2#usize : Result Usize) = ok 4#usize from rfl, bind_tc_ok,
    show (0#usize + 1#usize : Result Usize) = ok 1#usize from usize_add_lit (by scalar_tac) (by rfl),
    bind_tc_ok]
  have e8 : (16 : ℕ) * (8#usize).val = 128 := by scalar_tac
  have e4 : (16 : ℕ) * (4#usize).val = 64 := by scalar_tac
  have e2 : (16 : ℕ) * (2#usize).val = 32 := by scalar_tac
  have e1 : (16 : ℕ) * (1#usize).val = 16 := by scalar_tac
  rw [e8] at hv1
  -- level 1, `half = 4`
  unfold backend.avx2.ntt.ntt_block_loop0
  rw [if_pos (by scalar_tac)]
  apply WP.spec_bind (ntt_block_loop0_loop0_walk false b1 qv k1 4#usize 0#usize 7681 3840
    7906 4304 Rinv ψ (ctLvl 7681 ψ 1 128 f) 2 0 2 hq0 hqlt hR hQ' (by norm_num) s2.1 s2.2.1
    s2.2.2 hzeta (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by omega) (by omega)
    (initSplit (by simp) hb1) (by intro c hc; rw [hv1 c hc, if_neg (by simp)]))
  rintro ⟨b2, k2⟩ ⟨hb2, hv2, hk2⟩
  simp only at hb2 hv2 hk2
  rw [e4] at hv2
  show (do let b3 ← (if (1#usize) = 2#usize then backend.avx2.ntt.barrett_block b2 bm round qv
             else ok b2)
           let half1 ← 4#usize / 2#usize
           let level1 ← 1#usize + 1#usize
           backend.avx2.ntt.ntt_block_loop0 false b3 qv bm round k2 half1 level1)
      ⦃ (r : Array I16 256#usize) =>
          BlockBnd r 7906 ∧ ∀ c < 256, posZ 7681 r c = fwdH 7681 ψ f c ⦄
  rw [if_neg (by decide), bind_tc_ok,
    show (4#usize / 2#usize : Result Usize) = ok 2#usize from rfl, bind_tc_ok,
    show (1#usize + 1#usize : Result Usize) = ok 2#usize from usize_add_lit (by scalar_tac) (by rfl),
    bind_tc_ok]
  -- level 2, `half = 2`, then the re-centring pass
  unfold backend.avx2.ntt.ntt_block_loop0
  rw [if_pos (by scalar_tac)]
  apply WP.spec_bind (ntt_block_loop0_loop0_walk false b2 qv k2 2#usize 0#usize 7681 3840
    12210 4556 Rinv ψ (ctLvl 7681 ψ 2 64 (ctLvl 7681 ψ 1 128 f)) 4 0 4 hq0 hqlt hR hQ'
    (by norm_num) s3.1 s3.2.1 s3.2.2 hzeta (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by omega) (by omega)
    (initSplit (by simp) hb2) (by intro c hc; rw [hv2 c hc, if_neg (by simp)]))
  rintro ⟨b3, k3⟩ ⟨hb3, hv3, hk3⟩
  simp only at hb3 hv3 hk3
  rw [e2] at hv3
  show (do let b4 ← (if (2#usize) = 2#usize then backend.avx2.ntt.barrett_block b3 bm round qv
             else ok b3)
           let half1 ← 2#usize / 2#usize
           let level1 ← 2#usize + 1#usize
           backend.avx2.ntt.ntt_block_loop0 false b4 qv bm round k3 half1 level1)
      ⦃ (r : Array I16 256#usize) =>
          BlockBnd r 7906 ∧ ∀ c < 256, posZ 7681 r c = fwdH 7681 ψ f c ⦄
  rw [if_pos rfl]
  apply WP.spec_bind (hbar b3)
  rintro b4 ⟨hb4, hv4⟩
  rw [show (2#usize / 2#usize : Result Usize) = ok 1#usize from rfl, bind_tc_ok,
    show (2#usize + 1#usize : Result Usize) = ok 3#usize from usize_add_lit (by scalar_tac) (by rfl),
    bind_tc_ok]
  -- level 3, `half = 1`, from a centred block again
  unfold backend.avx2.ntt.ntt_block_loop0
  rw [if_pos (by scalar_tac)]
  apply WP.spec_bind (ntt_block_loop0_loop0_walk false b4 qv k3 1#usize 0#usize 7681 3840
    3840 4066 Rinv ψ (ctLvl 7681 ψ 4 32 (ctLvl 7681 ψ 2 64 (ctLvl 7681 ψ 1 128 f))) 8 0 8
    hq0 hqlt hR hQ' (by norm_num) s1.1 s1.2.1 s1.2.2 hzeta (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by omega) (by omega)
    (initSplit (by simp) hb4)
    (by intro c hc; rw [hv4 c hc, hv3 c hc, if_neg (by simp)]))
  rintro ⟨b5, k5⟩ ⟨hb5, hv5, hk5⟩
  simp only at hb5 hv5 hk5
  rw [e1] at hv5
  show (do let b6 ← (if (3#usize) = 2#usize then backend.avx2.ntt.barrett_block b5 bm round qv
             else ok b5)
           let half1 ← 1#usize / 2#usize
           let level1 ← 3#usize + 1#usize
           backend.avx2.ntt.ntt_block_loop0 false b6 qv bm round k5 half1 level1)
      ⦃ (r : Array I16 256#usize) =>
          BlockBnd r 7906 ∧ ∀ c < 256, posZ 7681 r c = fwdH 7681 ψ f c ⦄
  rw [if_neg (by decide), bind_tc_ok,
    show (1#usize / 2#usize : Result Usize) = ok 0#usize from rfl, bind_tc_ok,
    show (3#usize + 1#usize : Result Usize) = ok 4#usize from usize_add_lit (by scalar_tac) (by rfl),
    bind_tc_ok]
  -- `half = 0`: the loop is done
  unfold backend.avx2.ntt.ntt_block_loop0
  rw [if_neg (by scalar_tac)]
  simp only [WP.spec_ok]
  exact ⟨hb5, fun c hc => by rw [hv5 c hc, fwdH]⟩


theorem ntt_block_walk_q1 (b : Array I16 256#usize) (Rinv : ZMod 7681)
    (ψ f : ℕ → ZMod 7681)
    (hR : ((2 ^ 16 : ℤ) : ZMod 7681) * Rinv = 1)
    (hzeta : ∀ kk : Usize, kk.val < 256 → ∃ zi zqi : I16,
      backend.crt.zeta false kk = ok zi ∧ backend.crt.zeta_q false kk = ok zqi ∧
      |zi.val| ≤ 3840 ∧ (2 ^ 16 : ℤ) ∣ (zqi.val * 7681 - zi.val) ∧
      (((zi.val : ℤ) : ZMod 7681)) * Rinv = ψ kk.val)
    (htbl8 : ∃ z zq,
      (do let t ← backend.avx2.ntt.FWD8_Q1; backend.avx2.ntt.ld_tbl t 0#usize) = ok (z, zq) ∧
        PsiOk z zq 7681 3840 ∧ ∀ k < 16, laneZ 7681 z k * Rinv = ψ (16 + k))
    (htbl4 : ∀ h : Usize, h.val < 2 → ∃ z zq,
      (do let t ← backend.avx2.ntt.FWD4_Q1; backend.avx2.ntt.ld_tbl t h) = ok (z, zq) ∧
        PsiOk z zq 7681 3840 ∧ ∀ k < 16, laneZ 7681 z k * Rinv = ψ (32 + h.val + 2 * k))
    (htbl2 : ∀ h : Usize, h.val < 4 → ∃ z zq,
      (do let t ← backend.avx2.ntt.FWD2_Q1; backend.avx2.ntt.ld_tbl t h) = ok (z, zq) ∧
        PsiOk z zq 7681 3840 ∧ ∀ k < 16, laneZ 7681 z k * Rinv = ψ (64 + h.val + 4 * k))
    (htbl1 : ∀ h : Usize, h.val < 8 → ∃ z zq,
      (do let t ← backend.avx2.ntt.FWD1_Q1; backend.avx2.ntt.ld_tbl t h) = ok (z, zq) ∧
        PsiOk z zq 7681 3840 ∧ ∀ k < 16, laneZ 7681 z k * Rinv = ψ (128 + h.val + 8 * k))
    (hb : BlockBnd b 3840) (hv : ∀ c < 256, posZ 7681 b c = f c) :
    backend.avx2.ntt.ntt_block false b
      ⦃ (r : Array I16 256#usize) =>
          BlockBnd r 3840 ∧ ∀ c < 256, posZ 7681 r c = fwdAll 7681 ψ f c ⦄ := by
  obtain ⟨s1, s2, s3, s4, -, -⟩ := growth_q1
  have hq0 : (0 : ℤ) < ((7681 : ℕ) : ℤ) := by norm_num
  have hqlt : ((7681 : ℕ) : ℤ) ≤ 2 ^ 15 := by norm_num
  unfold backend.avx2.ntt.ntt_block backend.crt.q backend.crt.barrett_m
  simp only [Bool.false_eq_true, reduceIte, bind_tc_ok]
  obtain ⟨qv, hqv, hqvl⟩ := set1_epi16_spec backend.crt.Q1
  rw [hqv, bind_tc_ok]
  obtain ⟨bm, hbm, hbml⟩ := set1_epi16_spec backend.crt.Q1_BARRETT_M
  rw [hbm, bind_tc_ok]
  have hSH : (backend.crt.BARRETT_SH : I32).val = 11 := by
    simp only [backend.crt.BARRETT_SH]; rfl
  step*
  have hi2e : i2 = 10#i32 := IScalar.eq_of_val_eq (by rw [i2_post, hSH]; rfl)
  rw [hi2e, show (1#i16 <<< (10#i32) : Result I16) = ok 1024#i16 from rfl, bind_tc_ok]
  obtain ⟨rnd, hrnd, hrndl⟩ := set1_epi16_spec 1024#i16
  rw [hrnd, bind_tc_ok]
  have hQ : ∀ j < 16, (lane16 qv j).toInt = 7681 := fun j hj => by
    rw [hqvl j hj]; simp only [backend.crt.Q1]; decide
  have hQ' : ∀ j < 16, (lane16 qv j).toInt = ((7681 : ℕ) : ℤ) := by
    intro j hj; rw [hQ j hj]; norm_num
  have hM : ∀ j < 16, (lane16 bm j).toInt = 17474 := fun j hj => by
    rw [hbml j hj]; simp only [backend.crt.Q1_BARRETT_M]; decide
  have hRnd : ∀ j < 16, (lane16 rnd j).toInt = 2 ^ 10 := fun j hj => by
    rw [hrndl j hj]; decide
  have hbar : ∀ (bb : Array I16 256#usize),
      backend.avx2.ntt.barrett_block bb bm rnd qv
        ⦃ (r : Array I16 256#usize) =>
            BlockBnd r 3840 ∧ ∀ c < 256, posZ 7681 r c = posZ 7681 bb c ⦄ := by
    intro bb
    exact spec_and
      (WP.spec_mono (barrett_block_bnd bb bm rnd qv 7681 17474 hQ hM hRnd (by norm_num)
        (by norm_num) (by decide) (by norm_num) (by norm_num) (by norm_num))
        (fun r hr => hr.mono (by norm_num)))
      (barrett_block_val bb bm rnd qv 7681 17474 hQ' hM hRnd hq0 (by norm_num) (by decide)
        (by norm_num) (by norm_num) (by norm_num))
  -- the horizontal half
  apply WP.spec_bind (ntt_block_loop0_walk_q1 b qv bm rnd Rinv ψ f hR hQ hM hRnd hzeta hb hv)
  rintro b1 ⟨hb1, hv1⟩
  -- into coefficient coordinates
  apply WP.spec_bind (spec_and (transpose16_bnd b1 hb1) (transpose16_tpos 7681 b1))
  rintro b2 ⟨hb2, ht2⟩
  have hv2 : ∀ c < 256, tposZ 7681 b2 c = fwdH 7681 ψ f c := fun c hc => by
    rw [ht2 c hc, hv1 c hc]
  -- three vertical levels
  apply WP.spec_bind (ntt_block_loop1_walk false { start := 0#usize, «end» := 8#usize } b2 qv
    7681 3840 7906 4304 Rinv ψ (fwdH 7681 ψ f) hq0 hqlt hR hQ' (by norm_num) s2.1 s2.2.1
    s2.2.2 htbl8 rfl (initSplit (by simp) hb2)
    (by intro c hc; rw [hv2 c hc, if_neg (by simp)]))
  rintro b3 ⟨hb3, hv3⟩
  apply WP.spec_bind (ntt_block_loop2_walk false { start := 0#usize, «end» := 2#usize } b3 qv
    7681 3840 12210 4556 Rinv ψ (ctLvl 7681 ψ 16 8 (fwdH 7681 ψ f)) hq0 hqlt hR hQ'
    (by norm_num) s3.1 s3.2.1 s3.2.2 htbl4 rfl (by decide) (initSplit (by simp) hb3)
    (by intro c hc; rw [hv3 c hc, if_neg (by simp)]))
  rintro b4 ⟨hb4, hv4⟩
  apply WP.spec_bind (ntt_block_loop3_walk false { start := 0#usize, «end» := 4#usize } b4 qv
    7681 3840 16766 4823 Rinv ψ (ctLvl 7681 ψ 32 4 (ctLvl 7681 ψ 16 8 (fwdH 7681 ψ f)))
    hq0 hqlt hR hQ' (by norm_num) s4.1 s4.2.1 s4.2.2 htbl2 rfl (by decide)
    (initSplit (by simp) hb4) (by intro c hc; rw [hv4 c hc, if_neg (by simp)]))
  rintro b5 ⟨hb5, hv5⟩
  -- re-centre, the last level, transpose back, re-centre
  apply WP.spec_bind (hbar b5)
  rintro b6 ⟨hb6, hv6⟩
  apply WP.spec_bind (ntt_block_loop4_walk false { start := 0#usize, «end» := 8#usize } b6 qv
    7681 3840 3840 4066 Rinv ψ
    (ctLvl 7681 ψ 64 2 (ctLvl 7681 ψ 32 4 (ctLvl 7681 ψ 16 8 (fwdH 7681 ψ f))))
    hq0 hqlt hR hQ' (by norm_num) s1.1 s1.2.1 s1.2.2 htbl1 rfl
    (initSplit (by simp) (hb6.mono (by norm_num)))
    (by intro c hc
        rw [show tposZ 7681 b6 c = posZ 7681 b6 (16 * (c % 16) + c / 16) from rfl,
          hv6 _ (by omega), show posZ 7681 b5 (16 * (c % 16) + c / 16)
            = tposZ 7681 b5 c from rfl, hv5 c hc, if_neg (by simp)]))
  rintro b7 ⟨hb7, hv7⟩
  apply WP.spec_bind (spec_and (transpose16_bnd b7 hb7) (transpose16_pos 7681 b7))
  rintro b8 ⟨hb8, ht8⟩
  apply WP.spec_mono (hbar b8)
  rintro r ⟨hbr, hvr⟩
  refine ⟨hbr, fun c hc => ?_⟩
  rw [hvr c hc, ht8 c hc, hv7 c hc, fwdAll]

/-! ## The forward transform, unconditionally

Instantiating the walk with the real `q₂` tables.  Nothing is assumed: the ψ tables' properties
come from `Kopis/Avx2/Tables.lean` and `Kopis/Avx2/NttZeta.lean`, both of which are `decide`d
over the literal arrays. -/

theorem ntt_block_leaf_q1 (b : Array I16 256#usize) (f : ℕ → ZMod 7681)
    (hb : BlockBnd b 3840) (hv : ∀ c < 256, posZ 7681 b c = f c) :
    backend.avx2.ntt.ntt_block false b
      ⦃ (r : Array I16 256#usize) =>
          BlockBnd r 3840 ∧ ∀ c < 256, posZ 7681 r c = fwdAll 7681 zeta1 f c ⦄ := by
  refine ntt_block_walk_q1 b (900 : ZMod 7681) zeta1 f (by decide) ?_ ?_ ?_ ?_ ?_ hb hv
  · intro kk hkk
    obtain ⟨zi, zqi, h1, h2, h3, h4, h5⟩ := zeta_table_ok_q1 kk hkk
    exact ⟨zi, zqi, h1, h2, h3, h4, by rw [h5]; rfl⟩
  · obtain ⟨z, zq, h1, h2, h3⟩ := fwd8_q1_ok 0#usize (by simp)
    refine ⟨z, zq, h1, h2, fun k hk => ?_⟩
    rw [show laneZ 7681 z k = (((lane16 z k).toInt : ℤ) : ZMod 7681) from rfl, h3 k hk]
    rw [show ((16#isize).val + (0#usize).val * (0#isize).val + k * (1#isize).val).toNat
      = 16 + k from by scalar_tac]
    rfl
  · intro h hh
    obtain ⟨z, zq, h1, h2, h3⟩ := fwd4_q1_ok h hh
    refine ⟨z, zq, h1, h2, fun k hk => ?_⟩
    rw [show laneZ 7681 z k = (((lane16 z k).toInt : ℤ) : ZMod 7681) from rfl, h3 k hk]
    rw [show ((32#isize).val + h.val * (1#isize).val + k * (2#isize).val).toNat
      = 32 + h.val + 2 * k from by scalar_tac]
    rfl
  · intro h hh
    obtain ⟨z, zq, h1, h2, h3⟩ := fwd2_q1_ok h hh
    refine ⟨z, zq, h1, h2, fun k hk => ?_⟩
    rw [show laneZ 7681 z k = (((lane16 z k).toInt : ℤ) : ZMod 7681) from rfl, h3 k hk]
    rw [show ((64#isize).val + h.val * (1#isize).val + k * (4#isize).val).toNat
      = 64 + h.val + 4 * k from by scalar_tac]
    rfl
  · intro h hh
    obtain ⟨z, zq, h1, h2, h3⟩ := fwd1_q1_ok h hh
    refine ⟨z, zq, h1, h2, fun k hk => ?_⟩
    rw [show laneZ 7681 z k = (((lane16 z k).toInt : ℤ) : ZMod 7681) from rfl, h3 k hk]
    rw [show ((128#isize).val + h.val * (1#isize).val + k * (8#isize).val).toNat
      = 128 + h.val + 8 * k from by scalar_tac]
    rfl

/-- **The forward transform reaches the leaf state.**  Composing the walk with the algebra: after
`ntt_block`, the block holds the evaluation of its input at the 256 leaf constants of `q₂`'s CRT
tree.  This is the shape `State_leaf_mul_q2` consumes. -/
theorem ntt_block_State_q1 (b : Array I16 256#usize) (f : ℕ → ZMod 7681)
    (hb : BlockBnd b 3840) (hv : ∀ c < 256, posZ 7681 b c = f c) :
    backend.avx2.ntt.ntt_block false b
      ⦃ (r : Array I16 256#usize) =>
          BlockBnd r 3840 ∧ (∀ c < 256, posZ 7681 r c = fwdAll 7681 zeta1 f c) ∧
          NttAlg.State zeta1 256 1 1 f (fwdAll 7681 zeta1 f) ⦄ := by
  apply WP.spec_mono (ntt_block_leaf_q1 b f hb hv)
  exact fun r hr => ⟨hr.1, hr.2, fwdAll_State zeta1 zeta1_sq f⟩

end Kopis.Avx2
