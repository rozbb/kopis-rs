/-
  # Kopis/Neon/NttWalk.lean — the forward transform's levels, as residues (plan phase F4).

  `Kopis/Neon/NttValue.lean` says what one butterfly computes; `Kopis/Crt/NttAlgebra.lean` says
  what one Cooley-Tukey *layer* does to the CRT invariant.  This file walks the NEON loops and
  shows they apply the butterfly at the index pairs the layer expects.

  ## Coordinates

  NEON's whole-vector levels are the easy half: a vector `j` is array positions `[8j, 8j+8)`, and
  before the transpose array position *is* the coefficient index.  So a level with vector-stride
  `half` is a Cooley-Tukey layer with coefficient-stride `8·half`, and the loop nest maps onto
  `State_ct` with `m' = 8·half` and `nb = 16 / half` — no re-indexing at all.

  The transposed levels are where the two coordinate systems part company; that is
  `Kopis/Neon/Transpose.lean`'s business and it enters further down.

  ## Why the bounds come along

  Every value statement carries the same bound hypotheses the corresponding statement in
  `Kopis/Neon/NttLevel.lean` carries, and for the same reason: they are what makes the wrapping
  `vaddq_s16` / `vsubq_s16` exact, so that the integer identity survives the cast into `ZMod q`.
  They are hypotheses rather than conclusions here — the growth side is already proved, and
  re-proving it inside the walk would double the work for nothing.
-/
import Kopis.Neon.NttValue
import Kopis.Neon.NttGroupLoop
import Kopis.Crt.NttLevelFn

open Aeneas Aeneas.Std Result
open RustKopisNeon
open RustKopisNeon.backend.neon.intrinsics

namespace Kopis.Neon

set_option maxHeartbeats 1000000

open Kopis.CrtScheme.LevelFn

/-- **Two specs of the same program are one spec of their conjunction.**  `Result` is
deterministic, so a program cannot satisfy `P` at one value and `Q` at another.  This is
what lets the walk pass a loop's *bound* and its *value* to the same recursive call
without either theorem having to re-prove the other.  -/
theorem WP.spec_both {α : Type} {prog : Result α} {P Q : α → Prop}
    (h1 : prog ⦃P⦄) (h2 : prog ⦃Q⦄) : prog ⦃(r : α) => P r ∧ Q r⦄ := by
  obtain ⟨r1, hr1, hp1⟩ := Aeneas.Std.WP.spec_imp_exists h1
  obtain ⟨r2, hr2, hp2⟩ := Aeneas.Std.WP.spec_imp_exists h2
  rw [hr1] at hr2
  cases hr2
  rw [hr1]
  exact (Aeneas.Std.WP.spec_ok _).mpr ⟨hp1, hp2⟩

/-- **One whole-vector level's butterfly pass, as residues.**  The two intervals `pending` names
come out as the two halves of a Cooley-Tukey butterfly with the broadcast twiddle `ψ`; everything
else is untouched. -/
theorem ntt_inner_val (b : Array I16 256#usize) (qv z zq : Vec128) (q : ℕ) (Zb B Bt : ℤ)
    (Rinv ψ : ZMod q) (hR : ((2 ^ 16 : ℤ) : ZMod q) * Rinv = 1)
    (hψ : ∀ m < 8, laneZ q z m * Rinv = ψ)
    (hQ : ∀ i < 8, (lane16 qv i).toInt = (q : ℤ)) (hQpos : 0 < (q : ℤ)) (hQlt : (q : ℤ) ≤ 2 ^ 14)
    (hz : ∀ i < 8, |(lane16 z i).toInt| ≤ Zb) (hZb : Zb ≤ 2 ^ 14)
    (hzq : ∀ i < 8, (2 ^ 16 : ℤ) ∣ ((lane16 zq i).toInt * (q : ℤ) - (lane16 z i).toInt))
    (hB0 : 0 ≤ B) (hBZ : B * Zb < 2 ^ 15 * (q : ℤ))
    (hBt : B * Zb + 2 ^ 15 * (q : ℤ) ≤ 2 ^ 16 * Bt) (hfit : B + Bt ≤ 32767)
    (half start i : Usize) (hhalf : 1 ≤ half.val)
    (hrange : start.val + 2 * half.val ≤ 32) (hstart : start.val ≤ i.val)
    (hb : ∀ p < 256, pending start.val half.val i.val p → |(b.val[p]!).val| ≤ B) :
    backend.neon.ntt.ntt_block_loop0_loop0_loop0 b qv half start z zq i
      ⦃ (r : Array I16 256#usize) => ∀ p < 256,
          if 8 * i.val ≤ p ∧ p < 8 * (start.val + half.val) then
            posZ q r p = posZ q b p + ψ * posZ q b (p + 8 * half.val)
          else if 8 * (i.val + half.val) ≤ p ∧ p < 8 * (start.val + 2 * half.val) then
            posZ q r p = posZ q b (p - 8 * half.val) - ψ * posZ q b p
          else posZ q r p = posZ q b p ⦄ := by
  unfold backend.neon.ntt.ntt_block_loop0_loop0_loop0
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
    apply WP.spec_bind (ct_butterfly_val lo hv z zq qv q Zb B Bt Rinv hR hQ hQpos hQlt hz hZb
      hzq hlob hhib hB0 hBZ hBt hfit)
    rintro ⟨lo1, hi1'⟩ hval
    show (do let b1 ← backend.neon.intrinsics.store_i16 b i lo1
             let b2 ← backend.neon.intrinsics.store_i16 b1 i2 hi1'
             let i3 ← i + 1#usize
             backend.neon.ntt.ntt_block_loop0_loop0_loop0 b2 qv half start z zq i3)
        ⦃ (r : Array I16 256#usize) => ∀ p < 256,
            if 8 * i.val ≤ p ∧ p < 8 * (start.val + half.val) then
              posZ q r p = posZ q b p + ψ * posZ q b (p + 8 * half.val)
            else if 8 * (i.val + half.val) ≤ p ∧ p < 8 * (start.val + 2 * half.val) then
              posZ q r p = posZ q b (p - 8 * half.val) - ψ * posZ q b p
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
    apply WP.spec_mono (ntt_inner_val b2 qv z zq q Zb B Bt Rinv ψ hR hψ hQ hQpos hQlt hz hZb hzq
      hB0 hBZ hBt hfit half start i3 hhalf hrange (by omega) (by
        intro p hp hpend
        rw [hb2all p hp, if_neg (by unfold pending at hpend; omega),
          if_neg (by unfold pending at hpend; omega)]
        exact hb p hp (by unfold pending at hpend ⊢; omega)))
    intro r hr p hp
    have hrp := hr p hp
    by_cases hL : 8 * i.val ≤ p ∧ p < 8 * (start.val + half.val)
    · rw [if_pos hL]
      by_cases hLv : p < 8 * i.val + 8
      · -- `p` is in the vector this iteration just wrote as the low half
        rw [if_neg (by omega), if_neg (by omega)] at hrp
        rw [hrp, hb2Z p hp, if_pos ⟨hL.1, hLv⟩, (hval (p - 8 * i.val) (by omega)).1,
          hloZ _ (by omega), hhvZ _ (by omega), hψ _ (by omega),
          show 8 * i.val + (p - 8 * i.val) = p from by omega,
          show 8 * i2.val + (p - 8 * i.val) = p + 8 * half.val from by omega]
      · rw [if_pos (by omega : 8 * i3.val ≤ p ∧ p < 8 * (start.val + half.val))] at hrp
        rw [hrp, hb2Z p hp, if_neg (by omega), if_neg (by omega),
          hb2Z (p + 8 * half.val) (by omega), if_neg (by omega), if_neg (by omega)]
    · rw [if_neg hL]
      by_cases hH : 8 * (i.val + half.val) ≤ p ∧ p < 8 * (start.val + 2 * half.val)
      · rw [if_pos hH]
        by_cases hHv : p < 8 * i2.val + 8
        · -- …and here it is the vector written as the high half
          rw [if_neg (by omega), if_neg (by omega)] at hrp
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

/-! ## The blocks of one level

`start` walks the block boundaries in steps of `2·half`, taking a fresh ψ from the ζ table each
time.  The running `k` counts groups; `hkeq` ties it to the layer's ζ index `nb + bIdx`, with the
block index `bIdx` carried explicitly so that no division by the variable `half` ever appears in
the invariant.

Bound and value travel together through `WP.spec_both`: the value statement needs the bound as a
hypothesis on the *next* block, and the bound statement is already proved in
`Kopis/Neon/NttLevel.lean`. -/

theorem ntt_start_val (SECOND : Bool) (b : Array I16 256#usize) (qv : Vec128)
    (q : ℕ) (Zb B Bt : ℤ) (Rinv : ZMod q) (ψ a0 : ℕ → ZMod q) (nb bIdx : ℕ)
    (hR : ((2 ^ 16 : ℤ) : ZMod q) * Rinv = 1)
    (hQ : ∀ i < 8, (lane16 qv i).toInt = (q : ℤ)) (hQpos : 0 < (q : ℤ)) (hQlt : (q : ℤ) ≤ 2 ^ 14)
    (hZb : Zb ≤ 2 ^ 14)
    (hB0 : 0 ≤ B) (hBZ : B * Zb < 2 ^ 15 * (q : ℤ))
    (hBt : B * Zb + 2 ^ 15 * (q : ℤ) ≤ 2 ^ 16 * Bt) (hfit : B + Bt ≤ 32767)
    (hzeta : ∀ kk : Usize, kk.val < 256 → ∃ zi zqi : I16,
        backend.crt.zeta SECOND kk = ok zi ∧ backend.crt.zeta_q SECOND kk = ok zqi ∧
        |zi.val| ≤ Zb ∧ (2 ^ 16 : ℤ) ∣ (zqi.val * (q : ℤ) - zi.val) ∧
        ((zi.val : ℤ) : ZMod q) * Rinv = ψ kk.val)
    (k half start : Usize) (hhalf : 1 ≤ half.val) (hnb32 : 32 = nb * (2 * half.val))
    (hstartb : start.val = bIdx * (2 * half.val)) (hstart32 : start.val ≤ 32)
    (hkeq : k.val + 1 = nb + bIdx) (hk : k.val + (32 - start.val) ≤ 255)
    (hb : ∀ p < 256, 8 * start.val ≤ p → |(b.val[p]!).val| ≤ B)
    (hva : ∀ c < 256, posZ q b c =
        if c < 8 * start.val then ctLvl q ψ nb (8 * half.val) a0 c else a0 c) :
    backend.neon.ntt.ntt_block_loop0_loop0 SECOND b qv k half start
      ⦃ (r : Array I16 256#usize × Usize) =>
          (∀ p < 256, if 8 * start.val ≤ p then |(r.1.val[p]!).val| ≤ B + Bt
            else (r.1.val[p]!).val = (b.val[p]!).val) ∧
          (∀ c < 256, posZ q r.1 c = ctLvl q ψ nb (8 * half.val) a0 c) ∧
          r.2.val + 1 = nb + nb ⦄ := by
  have hdvd : 2 * half.val ∣ start.val := ⟨bIdx, by rw [hstartb]; ring⟩
  have hhalfdvd : 2 * half.val ∣ 32 := ⟨nb, by rw [hnb32]; ring⟩
  have hm' : 0 < 8 * half.val := by omega
  have hbs : bIdx * (2 * (8 * half.val)) = 8 * start.val := by rw [hstartb]; ring
  unfold backend.neon.ntt.ntt_block_loop0_loop0
  have hvecs : backend.neon.ntt.VECS = ok 32#usize := by
    simp only [backend.neon.ntt.VECS, consts.RING_DEG]; rfl
  rw [hvecs, bind_tc_ok]
  by_cases hlt : start < 32#usize
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
    let* ⟨ k1, hk1 ⟩ ← Std.Usize.add_spec (x := k) (y := 1#usize) (by scalar_tac)
    have hk1v : k1.val = k.val + 1 := by scalar_tac
    obtain ⟨zi, zqi, hzi, hzqi, hzib, hzqib, hzpsi⟩ := hzeta k1 (by omega)
    rw [hzi, bind_tc_ok]
    obtain ⟨z, hz, hzl⟩ := dup_n_s16_spec zi
    rw [hz, bind_tc_ok, hzqi, bind_tc_ok]
    obtain ⟨zq, hzq, hzql⟩ := dup_n_s16_spec zqi
    rw [hzq, bind_tc_ok]
    have hzlv : ∀ i < 8, |(lane16 z i).toInt| ≤ Zb := by
      intro i hi; rw [hzl i hi]; exact hzib
    have hzqlv : ∀ i < 8, (2 ^ 16 : ℤ) ∣ ((lane16 zq i).toInt * (q : ℤ) - (lane16 z i).toInt) := by
      intro i hi; rw [hzl i hi, hzql i hi]; exact hzqib
    have hzk : ∀ m < 8, laneZ q z m * Rinv = ψ (nb + bIdx) := by
      intro m hm
      have he : k1.val = nb + bIdx := by omega
      unfold laneZ
      rw [hzl m hm, ← he]
      exact hzpsi
    apply WP.spec_bind (WP.spec_both
      (ntt_inner_bnd b qv z zq (q : ℤ) Zb B Bt hQ hQpos hQlt hzlv hZb hzqlv hB0 hBZ hBt hfit
        half start start hhalf hfits (le_refl _) (by
          intro p hp hpend
          exact hb p hp (by unfold pending at hpend; omega)))
      (ntt_inner_val b qv z zq q Zb B Bt Rinv (ψ (nb + bIdx)) hR hzk hQ hQpos hQlt hzlv hZb
        hzqlv hB0 hBZ hBt hfit half start start hhalf hfits (le_refl _) (by
          intro p hp hpend
          exact hb p hp (by unfold pending at hpend; omega))))
    rintro b1 ⟨hb1, hb1v⟩
    -- what one block leaves behind, as residues
    have hb1all : ∀ c < 256, posZ q b1 c =
        if c < 8 * (start.val + 2 * half.val) then ctLvl q ψ nb (8 * half.val) a0 c
        else a0 c := by
      intro c hc
      have hcv := hb1v c hc
      by_cases hLo : 8 * start.val ≤ c ∧ c < 8 * (start.val + half.val)
      · rw [if_pos hLo] at hcv
        have hr : c - 8 * start.val < 8 * half.val := by omega
        obtain ⟨hct, -⟩ := ctLvl_hbut q ψ nb (8 * half.val) a0 hm' bIdx hbIdx
          (c - 8 * start.val) hr
        rw [show bIdx * (2 * (8 * half.val)) + (c - 8 * start.val) = c from by omega] at hct
        rw [show bIdx * (2 * (8 * half.val)) + 8 * half.val + (c - 8 * start.val)
              = c + 8 * half.val from by omega] at hct
        rw [if_pos (by omega), hct, hcv, hva c hc, if_neg (by omega),
          hva (c + 8 * half.val) (by omega), if_neg (by omega)]
      · by_cases hHi : 8 * (start.val + half.val) ≤ c ∧ c < 8 * (start.val + 2 * half.val)
        · rw [if_neg hLo, if_pos hHi] at hcv
          have hr : c - 8 * (start.val + half.val) < 8 * half.val := by omega
          obtain ⟨-, hct⟩ := ctLvl_hbut q ψ nb (8 * half.val) a0 hm' bIdx hbIdx
            (c - 8 * (start.val + half.val)) hr
          rw [show bIdx * (2 * (8 * half.val)) + (c - 8 * (start.val + half.val))
                = c - 8 * half.val from by omega] at hct
          rw [show bIdx * (2 * (8 * half.val)) + 8 * half.val
                + (c - 8 * (start.val + half.val)) = c from by omega] at hct
          rw [if_pos (by omega), hct, hcv, hva c hc, if_neg (by omega),
            hva (c - 8 * half.val) (by omega), if_neg (by omega)]
        · rw [if_neg hLo, if_neg hHi] at hcv
          rw [hcv, hva c hc]
          by_cases hbelow : c < 8 * start.val
          · rw [if_pos hbelow, if_pos (by omega)]
          · rw [if_neg hbelow, if_neg (by omega)]
    let* ⟨ i3, hi3 ⟩ ← Std.Usize.mul_spec (x := 2#usize) (y := half) (by scalar_tac)
    let* ⟨ start1, hstart1 ⟩ ← Std.Usize.add_spec (x := start) (y := i3) (by scalar_tac)
    have hs1v : start1.val = start.val + 2 * half.val := by scalar_tac
    apply WP.spec_mono (ntt_start_val SECOND b1 qv q Zb B Bt Rinv ψ a0 nb (bIdx + 1) hR hQ hQpos
      hQlt hZb hB0 hBZ hBt hfit hzeta k1 half start1 hhalf hnb32
      (by rw [hs1v, hstartb]; ring) (by omega) (by omega) (by omega)
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
    have hkk : k.val + 1 = nb + nb := by omega
    refine (WP.spec_ok _).mpr ⟨fun p hp => ?_, fun c hc => ?_, hkk⟩
    · rw [if_neg (by omega)]
    · rw [hva c hc, if_pos (by omega)]

termination_by 32 - start.val
decreasing_by scalar_decr_tac

/-! ## The five whole-vector levels

`half = 16, 8, 4, 2, 1` with `m' = 8·half` and `nb = 32 / (2·half)`, re-centring after the third —
the "runs of 3, 3, 2" schedule.  The Barrett pass moves the representative but not the residue, so
it is invisible to the value chain and only the bound has to be threaded through it.

The `k` counter needs no invariant of its own: `ntt_start_val` *reports* it as `nb + nb`, so each
level's starting `k` is fixed by the level before it — `0, 1, 3, 7, 15`. -/

/-- The five whole-vector levels, as a function of the input view. -/
noncomputable def fwdH (q : ℕ) (ψ f : ℕ → ZMod q) : ℕ → ZMod q :=
  ctLvl q ψ 16 8 (ctLvl q ψ 8 16 (ctLvl q ψ 4 32 (ctLvl q ψ 2 64 (ctLvl q ψ 1 128 f))))

theorem ntt_horizontal_val (SECOND : Bool) (b : Array I16 256#usize) (qv bm round : Vec128)
    (q : ℕ) (Zb M A0 A1 A2 A3 A4 A5 : ℤ) (Rinv : ZMod q) (ψ f : ℕ → ZMod q)
    (hR : ((2 ^ 16 : ℤ) : ZMod q) * Rinv = 1)
    (hQ : ∀ i < 8, (lane16 qv i).toInt = (q : ℤ)) (hQpos : 0 < (q : ℤ))
    (hQ14 : (q : ℤ) < 2 ^ 14) (hQodd : ¬ (2 ∣ (q : ℤ))) (hZb : Zb ≤ 2 ^ 14)
    (hM : ∀ i < 8, (lane16 bm i).toInt = M) (hMpos : 0 < M) (hMlt : M < 2 ^ 15)
    (hD : |2 ^ 27 - (q : ℤ) * M| ≤ 2047)
    (hRnd : ∀ i < 8, (lane16 round i).toInt = 2 ^ 10)
    (hzeta : ∀ kk : Usize, kk.val < 256 → ∃ zi zqi : I16,
        backend.crt.zeta SECOND kk = ok zi ∧ backend.crt.zeta_q SECOND kk = ok zqi ∧
        |zi.val| ≤ Zb ∧ (2 ^ 16 : ℤ) ∣ (zqi.val * (q : ℤ) - zi.val) ∧
        ((zi.val : ℤ) : ZMod q) * Rinv = ψ kk.val)
    (hA0 : 0 ≤ A0) (hA1 : 0 ≤ A1) (hA2 : 0 ≤ A2) (hA4 : 0 ≤ A4)
    (hreset : ((q : ℤ) - 1) / 2 ≤ A0)
    (hs0 : LevelStep (q : ℤ) Zb A0 (A1 - A0)) (hs1 : LevelStep (q : ℤ) Zb A1 (A2 - A1))
    (hs2 : LevelStep (q : ℤ) Zb A2 (A3 - A2))
    (hs3 : LevelStep (q : ℤ) Zb A0 (A4 - A0)) (hs4 : LevelStep (q : ℤ) Zb A4 (A5 - A4))
    (hb : BlockBnd b A0) (hf : ∀ c < 256, posZ q b c = f c) :
    backend.neon.ntt.ntt_block_loop0 SECOND b qv bm round 0#usize 16#usize 0#usize
      ⦃ (r : Array I16 256#usize) => BlockBnd r A5 ∧ ∀ c < 256, posZ q r c = fwdH q ψ f c ⦄ := by
  have hQ14' : (q : ℤ) ≤ 2 ^ 14 := by omega

  -- level 0: half = 16, nb = 1, m' = 128
  unfold backend.neon.ntt.ntt_block_loop0
  rw [if_pos (show (1#usize : Usize) ≤ 16#usize by decide)]
  apply WP.spec_bind (ntt_start_val SECOND b qv q Zb A0 (A1 - A0) Rinv ψ f 1 0 hR hQ hQpos hQ14'
    hZb (by omega) hs0.1 hs0.2.1 hs0.2.2 hzeta 0#usize 16#usize 0#usize (by scalar_tac)
    (by scalar_tac) (by scalar_tac) (by scalar_tac) (by scalar_tac) (by scalar_tac)
    (by intro p hp _; exact hb p hp)
    (by intro c hc; rw [hf c hc, if_neg (by scalar_tac)]))
  rintro ⟨b1, k1⟩ ⟨hsb1, hvb1, hkb1⟩
  have hvb1n : ∀ c < 256, posZ q b1 c = ctLvl q ψ 1 128 f c := by
    intro c hc
    have h := hvb1 c hc
    rwa [show (8 : ℕ) * (16#usize : Usize).val = 128 from by scalar_tac] at h
  show (do let b2 ← if (0#usize : Usize) = 2#usize
                    then backend.neon.ntt.barrett_block b1 bm round qv else ok b1
           let half1 ← (16#usize : Usize) / 2#usize
           let level1 ← (0#usize : Usize) + 1#usize
           backend.neon.ntt.ntt_block_loop0 SECOND b2 qv bm round k1 half1 level1)
      ⦃ (r : Array I16 256#usize) => BlockBnd r A5 ∧ ∀ c < 256, posZ q r c = fwdH q ψ f c ⦄
  rw [if_neg (by decide), bind_tc_ok,
    show (16#usize : Usize) / 2#usize = ok 8#usize from by rfl, bind_tc_ok,
    usize_add_one (0#usize) (1#usize) (by scalar_tac), bind_tc_ok]
  have hb1 : BlockBnd b1 A1 := (blockBnd_of_start hsb1).mono (by omega)

  -- level 1: half = 8, nb = 2, m' = 64
  unfold backend.neon.ntt.ntt_block_loop0
  rw [if_pos (show (1#usize : Usize) ≤ 8#usize by decide)]
  apply WP.spec_bind (ntt_start_val SECOND b1 qv q Zb A1 (A2 - A1) Rinv ψ
    (ctLvl q ψ 1 128 f) 2 0 hR hQ hQpos hQ14' hZb (by omega) hs1.1 hs1.2.1 hs1.2.2 hzeta
    k1 8#usize 0#usize (by scalar_tac) (by scalar_tac) (by scalar_tac) (by scalar_tac)
    (by omega) (by scalar_tac) (by intro p hp _; exact hb1 p hp)
    (by intro c hc; rw [hvb1n c hc, if_neg (by scalar_tac)]))
  rintro ⟨b2, k2⟩ ⟨hsb2, hvb2, hkb2⟩
  have hvb2n : ∀ c < 256, posZ q b2 c = ctLvl q ψ 2 64 (ctLvl q ψ 1 128 f) c := by
    intro c hc
    have h := hvb2 c hc
    rwa [show (8 : ℕ) * (8#usize : Usize).val = 64 from by scalar_tac] at h
  show (do let b2' ← if (1#usize : Usize) = 2#usize
                     then backend.neon.ntt.barrett_block b2 bm round qv else ok b2
           let half1 ← (8#usize : Usize) / 2#usize
           let level1 ← (1#usize : Usize) + 1#usize
           backend.neon.ntt.ntt_block_loop0 SECOND b2' qv bm round k2 half1 level1)
      ⦃ (r : Array I16 256#usize) => BlockBnd r A5 ∧ ∀ c < 256, posZ q r c = fwdH q ψ f c ⦄
  rw [if_neg (by decide), bind_tc_ok,
    show (8#usize : Usize) / 2#usize = ok 4#usize from by rfl, bind_tc_ok,
    usize_add_one (1#usize) (2#usize) (by scalar_tac), bind_tc_ok]
  have hb2 : BlockBnd b2 A2 := (blockBnd_of_start hsb2).mono (by omega)

  -- level 2: half = 4, nb = 4, m' = 32 — and the re-centring pass
  unfold backend.neon.ntt.ntt_block_loop0
  rw [if_pos (show (1#usize : Usize) ≤ 4#usize by decide)]
  apply WP.spec_bind (ntt_start_val SECOND b2 qv q Zb A2 (A3 - A2) Rinv ψ
    (ctLvl q ψ 2 64 (ctLvl q ψ 1 128 f)) 4 0 hR hQ hQpos hQ14' hZb (by omega) hs2.1 hs2.2.1
    hs2.2.2 hzeta k2 4#usize 0#usize (by scalar_tac) (by scalar_tac) (by scalar_tac)
    (by scalar_tac) (by omega) (by scalar_tac) (by intro p hp _; exact hb2 p hp)
    (by intro c hc; rw [hvb2n c hc, if_neg (by scalar_tac)]))
  rintro ⟨b3, k3⟩ ⟨hsb3, hvb3, hkb3⟩
  have hvb3n : ∀ c < 256, posZ q b3 c = ctLvl q ψ 4 32 (ctLvl q ψ 2 64 (ctLvl q ψ 1 128 f)) c := by
    intro c hc
    have h := hvb3 c hc
    rwa [show (8 : ℕ) * (4#usize : Usize).val = 32 from by scalar_tac] at h
  show (do let b2' ← if (2#usize : Usize) = 2#usize
                     then backend.neon.ntt.barrett_block b3 bm round qv else ok b3
           let half1 ← (4#usize : Usize) / 2#usize
           let level1 ← (2#usize : Usize) + 1#usize
           backend.neon.ntt.ntt_block_loop0 SECOND b2' qv bm round k3 half1 level1)
      ⦃ (r : Array I16 256#usize) => BlockBnd r A5 ∧ ∀ c < 256, posZ q r c = fwdH q ψ f c ⦄
  rw [if_pos rfl]
  apply WP.spec_bind (barrett_block_spec b3 bm round qv (q : ℤ) M hQ hM hRnd hQpos hQ14 hQodd
    hMpos hMlt hD)
  rintro b3' ⟨hb3'bnd, hb3'res⟩
  show (do let half1 ← (4#usize : Usize) / 2#usize
           let level1 ← (2#usize : Usize) + 1#usize
           backend.neon.ntt.ntt_block_loop0 SECOND b3' qv bm round k3 half1 level1)
      ⦃ (r : Array I16 256#usize) => BlockBnd r A5 ∧ ∀ c < 256, posZ q r c = fwdH q ψ f c ⦄
  rw [show (4#usize : Usize) / 2#usize = ok 2#usize from by rfl, bind_tc_ok,
    usize_add_one (2#usize) (3#usize) (by scalar_tac), bind_tc_ok]
  have hb3' : BlockBnd b3' A0 := hb3'bnd.mono hreset
  -- the Barrett pass moves the representative, not the residue
  have hvb3' : ∀ c < 256, posZ q b3' c = ctLvl q ψ 4 32 (ctLvl q ψ 2 64 (ctLvl q ψ 1 128 f)) c := by
    intro c hc
    rw [← hvb3n c hc]
    unfold posZ
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd
      ((b3'.val[c]!).val - (b3.val[c]!).val) q).mpr (hb3'res c hc)
    push_cast at this
    linear_combination this

  -- level 3: half = 2, nb = 8, m' = 16
  unfold backend.neon.ntt.ntt_block_loop0
  rw [if_pos (show (1#usize : Usize) ≤ 2#usize by decide)]
  apply WP.spec_bind (ntt_start_val SECOND b3' qv q Zb A0 (A4 - A0) Rinv ψ
    (ctLvl q ψ 4 32 (ctLvl q ψ 2 64 (ctLvl q ψ 1 128 f))) 8 0 hR hQ hQpos hQ14' hZb (by omega)
    hs3.1 hs3.2.1 hs3.2.2 hzeta k3 2#usize 0#usize (by scalar_tac) (by scalar_tac)
    (by scalar_tac) (by scalar_tac) (by omega) (by scalar_tac)
    (by intro p hp _; exact hb3' p hp)
    (by intro c hc; rw [hvb3' c hc, if_neg (by scalar_tac)]))
  rintro ⟨b4, k4⟩ ⟨hsb4, hvb4, hkb4⟩
  have hvb4n : ∀ c < 256, posZ q b4 c = ctLvl q ψ 8 16 (ctLvl q ψ 4 32 (ctLvl q ψ 2 64 (ctLvl q ψ 1 128 f))) c := by
    intro c hc
    have h := hvb4 c hc
    rwa [show (8 : ℕ) * (2#usize : Usize).val = 16 from by scalar_tac] at h
  show (do let b2' ← if (3#usize : Usize) = 2#usize
                     then backend.neon.ntt.barrett_block b4 bm round qv else ok b4
           let half1 ← (2#usize : Usize) / 2#usize
           let level1 ← (3#usize : Usize) + 1#usize
           backend.neon.ntt.ntt_block_loop0 SECOND b2' qv bm round k4 half1 level1)
      ⦃ (r : Array I16 256#usize) => BlockBnd r A5 ∧ ∀ c < 256, posZ q r c = fwdH q ψ f c ⦄
  rw [if_neg (by decide), bind_tc_ok,
    show (2#usize : Usize) / 2#usize = ok 1#usize from by rfl, bind_tc_ok,
    usize_add_one (3#usize) (4#usize) (by scalar_tac), bind_tc_ok]
  have hb4 : BlockBnd b4 A4 := (blockBnd_of_start hsb4).mono (by omega)

  -- level 4: half = 1, nb = 16, m' = 8
  unfold backend.neon.ntt.ntt_block_loop0
  rw [if_pos (show (1#usize : Usize) ≤ 1#usize by decide)]
  apply WP.spec_bind (ntt_start_val SECOND b4 qv q Zb A4 (A5 - A4) Rinv ψ
    (ctLvl q ψ 8 16 (ctLvl q ψ 4 32 (ctLvl q ψ 2 64 (ctLvl q ψ 1 128 f)))) 16 0 hR hQ hQpos
    hQ14' hZb (by omega) hs4.1 hs4.2.1 hs4.2.2 hzeta k4 1#usize 0#usize (by scalar_tac)
    (by scalar_tac) (by scalar_tac) (by scalar_tac) (by omega) (by scalar_tac)
    (by intro p hp _; exact hb4 p hp)
    (by intro c hc; rw [hvb4n c hc, if_neg (by scalar_tac)]))
  rintro ⟨b5, k5⟩ ⟨hsb5, hvb5, hkb5⟩
  have hvb5n : ∀ c < 256, posZ q b5 c = fwdH q ψ f c := by
    intro c hc
    have h := hvb5 c hc
    rwa [show (8 : ℕ) * (1#usize : Usize).val = 8 from by scalar_tac] at h
  show (do let b2' ← if (4#usize : Usize) = 2#usize
                     then backend.neon.ntt.barrett_block b5 bm round qv else ok b5
           let half1 ← (1#usize : Usize) / 2#usize
           let level1 ← (4#usize : Usize) + 1#usize
           backend.neon.ntt.ntt_block_loop0 SECOND b2' qv bm round k5 half1 level1)
      ⦃ (r : Array I16 256#usize) => BlockBnd r A5 ∧ ∀ c < 256, posZ q r c = fwdH q ψ f c ⦄
  rw [if_neg (by decide), bind_tc_ok,
    show (1#usize : Usize) / 2#usize = ok 0#usize from by rfl, bind_tc_ok,
    usize_add_one (4#usize) (5#usize) (by scalar_tac), bind_tc_ok]
  unfold backend.neon.ntt.ntt_block_loop0
  rw [if_neg (by decide)]
  refine (WP.spec_ok _).mpr ⟨(blockBnd_of_start hsb5).mono (by omega), fun c hc => ?_⟩
  exact hvb5n c hc

/-! ## The transposed levels

`load_group_spec` puts coefficient `64g + 8m + k` in lane `m` of the group's vector `k` — the
transpose is *inside* `load_group`, not beside it — so pairing vectors `(k, k ± len)` at a fixed
lane is a butterfly at coefficient stride `len`.  The three levels `len = 4, 2, 1` are therefore
the layers `ctLvl q ψ 32 4`, `ctLvl q ψ 64 2` and `ctLvl q ψ 128 1`.

The partner of vector `j` is written `j % 4 + 4` (its high half) and `j % 4` (its low half) rather
than `j ± 4`, so that the index is in range without knowing which side of the pairing `j` is on —
`Vec128` has no `Inhabited` instance, so every access has to carry its bound. -/

/-- **The `len = 4` transposed level, as residues.** -/
theorem ntt_len4_val (qv z zq : Vec128) (q : ℕ) (Zb B Bt : ℤ) (Rinv : ZMod q) (ψm : ℕ → ZMod q)
    (hR : ((2 ^ 16 : ℤ) : ZMod q) * Rinv = 1) (hψ : ∀ m < 8, laneZ q z m * Rinv = ψm m)
    (hQ : ∀ i < 8, (lane16 qv i).toInt = (q : ℤ)) (hQpos : 0 < (q : ℤ)) (hQlt : (q : ℤ) ≤ 2 ^ 14)
    (hz : ∀ i < 8, |(lane16 z i).toInt| ≤ Zb) (hZb : Zb ≤ 2 ^ 14)
    (hzq : ∀ i < 8, (2 ^ 16 : ℤ) ∣ ((lane16 zq i).toInt * (q : ℤ) - (lane16 z i).toInt))
    (hB0 : 0 ≤ B) (hBZ : B * Zb < 2 ^ 15 * (q : ℤ))
    (hBt : B * Zb + 2 ^ 15 * (q : ℤ) ≤ 2 ^ 16 * Bt) (hfit : B + Bt ≤ 32767)
    (v : Array Vec128 8#usize) (iter : core.ops.range.Range Usize) (hend : iter.«end».val = 4)
    (hv : ∀ j (hj : j < 8), pend4 iter.start.val j → VecBnd (vAt v j hj) B) :
    backend.neon.ntt.ntt_block_loop1_loop0 iter qv v z zq
      ⦃ (r : Array Vec128 8#usize) => ∀ j (hj : j < 8), ∀ m < 8,
          if iter.start.val ≤ j ∧ j < 4 then
            laneZ q (vAt r j hj) m = laneZ q (vAt v (j % 4) (by omega)) m
              + ψm m * laneZ q (vAt v (j % 4 + 4) (by omega)) m
          else if 4 + iter.start.val ≤ j ∧ j < 8 then
            laneZ q (vAt r j hj) m = laneZ q (vAt v (j % 4) (by omega)) m
              - ψm m * laneZ q (vAt v (j % 4 + 4) (by omega)) m
          else laneZ q (vAt r j hj) m = laneZ q (vAt v j hj) m ⦄ := by
  unfold backend.neon.ntt.ntt_block_loop1_loop0
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
      (ct_butterfly_spec lo hiv z zq qv (q : ℤ) Zb B Bt hQ hQpos hQlt hz hZb hzq
        (by rw [hloe]; exact hv _ (by omega) (Or.inl ⟨by omega, by omega⟩))
        (by rw [hhie]; exact hv _ (by omega) (Or.inr ⟨by omega, by omega⟩))
        hB0 hBZ hBt hfit)
      (ct_butterfly_val lo hiv z zq qv q Zb B Bt Rinv hR hQ hQpos hQlt hz hZb hzq
        (by rw [hloe]; exact hv _ (by omega) (Or.inl ⟨by omega, by omega⟩))
        (by rw [hhie]; exact hv _ (by omega) (Or.inr ⟨by omega, by omega⟩))
        hB0 hBZ hBt hfit))
    rintro ⟨lo1, hi1'⟩ ⟨⟨hlo1b, hhi1b, -⟩, hbutval⟩
    show (do let v1 ← Array.update v iter.start lo1
             let a ← Array.update v1 i1 hi1'
             backend.neon.ntt.ntt_block_loop1_loop0 iter1 qv a z zq)
        ⦃ (r : Array Vec128 8#usize) => ∀ j (hj : j < 8), ∀ m < 8,
            if iter.start.val ≤ j ∧ j < 4 then
              laneZ q (vAt r j hj) m = laneZ q (vAt v (j % 4) (by omega)) m
                + ψm m * laneZ q (vAt v (j % 4 + 4) (by omega)) m
            else if 4 + iter.start.val ≤ j ∧ j < 8 then
              laneZ q (vAt r j hj) m = laneZ q (vAt v (j % 4) (by omega)) m
                - ψm m * laneZ q (vAt v (j % 4 + 4) (by omega)) m
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
    apply WP.spec_mono (ntt_len4_val qv z zq q Zb B Bt Rinv ψm hR hψ hQ hQpos hQlt hz hZb hzq
      hB0 hBZ hBt hfit a iter1 (by rw [hend']; exact hend) (by
        intro j hj hpend
        rw [hav j hj, if_neg (by unfold pend4 at hpend; omega),
          if_neg (by unfold pend4 at hpend; omega)]
        exact hv j hj (by unfold pend4 at hpend ⊢; omega)))
    intro r hr j hj m hm
    have hrj := hr j hj m hm
    -- the two vectors this iteration wrote, and the value of each
    have hlo1v : laneZ q lo1 m = laneZ q (vAt v (iter.start.val % 4) (by omega)) m
        + ψm m * laneZ q (vAt v (iter.start.val % 4 + 4) (by omega)) m := by
      have h := (hbutval m hm).1
      rw [hψ m hm, hloe, hhie] at h
      rw [h, vAt_congr v (by omega) (by omega) (show iter.start.val = iter.start.val % 4 from
          by omega),
        vAt_congr v (by omega) (by omega) (show i1.val = iter.start.val % 4 + 4 from by omega)]
    have hhi1v : laneZ q hi1' m = laneZ q (vAt v (iter.start.val % 4) (by omega)) m
        - ψm m * laneZ q (vAt v (iter.start.val % 4 + 4) (by omega)) m := by
      have h := (hbutval m hm).2
      rw [hψ m hm, hloe, hhie] at h
      rw [h, vAt_congr v (by omega) (by omega) (show iter.start.val = iter.start.val % 4 from
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

/-- **The `len = 2` transposed level, as residues.**  The partner index is written
`4·(j/4) + j%2` (+2 for the high side) so that it is in range without knowing which side of the
pairing — or which half of the group — `j` is on. -/
theorem ntt_len2_val (qv z zq : Vec128) (q : ℕ) (Zb B Bt : ℤ) (Rinv : ZMod q) (ψm : ℕ → ZMod q)
    (hR : ((2 ^ 16 : ℤ) : ZMod q) * Rinv = 1) (hψ : ∀ m < 8, laneZ q z m * Rinv = ψm m)
    (hQ : ∀ i < 8, (lane16 qv i).toInt = (q : ℤ)) (hQpos : 0 < (q : ℤ)) (hQlt : (q : ℤ) ≤ 2 ^ 14)
    (hz : ∀ i < 8, |(lane16 z i).toInt| ≤ Zb) (hZb : Zb ≤ 2 ^ 14)
    (hzq : ∀ i < 8, (2 ^ 16 : ℤ) ∣ ((lane16 zq i).toInt * (q : ℤ) - (lane16 z i).toInt))
    (hB0 : 0 ≤ B) (hBZ : B * Zb < 2 ^ 15 * (q : ℤ))
    (hBt : B * Zb + 2 ^ 15 * (q : ℤ) ≤ 2 ^ 16 * Bt) (hfit : B + Bt ≤ 32767)
    (v : Array Vec128 8#usize) (h : Usize) (hh : h.val < 2)
    (iter : core.ops.range.Range Usize) (hend : iter.«end».val = 2)
    (hv : ∀ j (hj : j < 8), pend2 h.val iter.start.val j → VecBnd (vAt v j hj) B) :
    backend.neon.ntt.ntt_block_loop1_loop2_loop0 iter qv v h z zq
      ⦃ (r : Array Vec128 8#usize) => ∀ j (hj : j < 8), ∀ m < 8,
          if 4 * h.val + iter.start.val ≤ j ∧ j < 4 * h.val + 2 then
            laneZ q (vAt r j hj) m = laneZ q (vAt v (4 * (j / 4) + j % 2) (by omega)) m
              + ψm m * laneZ q (vAt v (4 * (j / 4) + j % 2 + 2) (by omega)) m
          else if 4 * h.val + 2 + iter.start.val ≤ j ∧ j < 4 * h.val + 4 then
            laneZ q (vAt r j hj) m = laneZ q (vAt v (4 * (j / 4) + j % 2) (by omega)) m
              - ψm m * laneZ q (vAt v (4 * (j / 4) + j % 2 + 2) (by omega)) m
          else laneZ q (vAt r j hj) m = laneZ q (vAt v j hj) m ⦄ := by
  unfold backend.neon.ntt.ntt_block_loop1_loop2_loop0
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
      (ct_butterfly_spec lo hiv z zq qv (q : ℤ) Zb B Bt hQ hQpos hQlt hz hZb hzq
        (by rw [hloe]; exact hv _ (by omega) (Or.inl ⟨by omega, by omega⟩))
        (by rw [hhie]; exact hv _ (by omega) (Or.inr ⟨by omega, by omega⟩))
        hB0 hBZ hBt hfit)
      (ct_butterfly_val lo hiv z zq qv q Zb B Bt Rinv hR hQ hQpos hQlt hz hZb hzq
        (by rw [hloe]; exact hv _ (by omega) (Or.inl ⟨by omega, by omega⟩))
        (by rw [hhie]; exact hv _ (by omega) (Or.inr ⟨by omega, by omega⟩))
        hB0 hBZ hBt hfit))
    rintro ⟨lo1, hi1'⟩ ⟨⟨hlo1b, hhi1b, -⟩, hbutval⟩
    show (do let v1 ← Array.update v base lo1
             let a ← Array.update v1 i2 hi1'
             backend.neon.ntt.ntt_block_loop1_loop2_loop0 iter1 qv a h z zq)
        ⦃ (r : Array Vec128 8#usize) => ∀ j (hj : j < 8), ∀ m < 8,
            if 4 * h.val + iter.start.val ≤ j ∧ j < 4 * h.val + 2 then
              laneZ q (vAt r j hj) m = laneZ q (vAt v (4 * (j / 4) + j % 2) (by omega)) m
                + ψm m * laneZ q (vAt v (4 * (j / 4) + j % 2 + 2) (by omega)) m
            else if 4 * h.val + 2 + iter.start.val ≤ j ∧ j < 4 * h.val + 4 then
              laneZ q (vAt r j hj) m = laneZ q (vAt v (4 * (j / 4) + j % 2) (by omega)) m
                - ψm m * laneZ q (vAt v (4 * (j / 4) + j % 2 + 2) (by omega)) m
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
    apply WP.spec_mono (ntt_len2_val qv z zq q Zb B Bt Rinv ψm hR hψ hQ hQpos hQlt hz hZb hzq
      hB0 hBZ hBt hfit a h hh iter1 (by rw [hend']; exact hend) (by
        intro j hj hpend
        rw [hav j hj, if_neg (by unfold pend2 at hpend; omega),
          if_neg (by unfold pend2 at hpend; omega)]
        exact hv j hj (by unfold pend2 at hpend ⊢; omega)))
    intro r hr j hj m hm
    have hrj := hr j hj m hm
    have hlo1v : laneZ q lo1 m = laneZ q (vAt v (4 * (base.val / 4) + base.val % 2) (by omega)) m
        + ψm m * laneZ q (vAt v (4 * (base.val / 4) + base.val % 2 + 2) (by omega)) m := by
      have hb := (hbutval m hm).1
      rw [hψ m hm, hloe, hhie] at hb
      rw [hb, vAt_congr v (by omega) (by omega)
          (show base.val = 4 * (base.val / 4) + base.val % 2 from by omega),
        vAt_congr v (by omega) (by omega)
          (show i2.val = 4 * (base.val / 4) + base.val % 2 + 2 from by omega)]
    have hhi1v : laneZ q hi1' m = laneZ q (vAt v (4 * (base.val / 4) + base.val % 2) (by omega)) m
        - ψm m * laneZ q (vAt v (4 * (base.val / 4) + base.val % 2 + 2) (by omega)) m := by
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

/-- **The `len = 1` transposed level, as residues.**  Four adjacent pairs, four distinct
coefficient blocks per lane, so ψ is a family indexed by the table position `4g + r` — one fresh
pair per iteration rather than one for the whole level. -/
theorem ntt_len1_val (SECOND : Bool) (qv : Vec128) (q : ℕ) (Zb B Bt : ℤ) (Rinv : ZMod q)
    (ψm : ℕ → ℕ → ZMod q) (hR : ((2 ^ 16 : ℤ) : ZMod q) * Rinv = 1)
    (hQ : ∀ i < 8, (lane16 qv i).toInt = (q : ℤ)) (hQpos : 0 < (q : ℤ)) (hQlt : (q : ℤ) ≤ 2 ^ 14)
    (hZb : Zb ≤ 2 ^ 14)
    (hB0 : 0 ≤ B) (hBZ : B * Zb < 2 ^ 15 * (q : ℤ))
    (hBt : B * Zb + 2 ^ 15 * (q : ℤ) ≤ 2 ^ 16 * Bt) (hfit : B + Bt ≤ 32767)
    (htbl : ∀ kk : Usize, kk.val < 16 → ∃ z zq : Vec128,
        backend.neon.ntt.fwd1 SECOND kk = ok (z, zq) ∧
        (∀ i < 8, |(lane16 z i).toInt| ≤ Zb) ∧
        (∀ i < 8, (2 ^ 16 : ℤ) ∣ ((lane16 zq i).toInt * (q : ℤ) - (lane16 z i).toInt)) ∧
        (∀ m < 8, laneZ q z m * Rinv = ψm kk.val m))
    (g : Usize) (hg : g.val < 4) (v : Array Vec128 8#usize)
    (iter : core.ops.range.Range Usize) (hend : iter.«end».val = 4)
    (hv : ∀ j (hj : j < 8), pend1 iter.start.val j → VecBnd (vAt v j hj) B) :
    backend.neon.ntt.ntt_block_loop1_loop3 SECOND iter qv g v
      ⦃ (r : Array Vec128 8#usize) => ∀ j (hj : j < 8), ∀ m < 8,
          if 2 * iter.start.val ≤ j then
            (if j % 2 = 0 then
              laneZ q (vAt r j hj) m = laneZ q (vAt v (2 * (j / 2)) (by omega)) m
                + ψm (4 * g.val + j / 2) m * laneZ q (vAt v (2 * (j / 2) + 1) (by omega)) m
            else
              laneZ q (vAt r j hj) m = laneZ q (vAt v (2 * (j / 2)) (by omega)) m
                - ψm (4 * g.val + j / 2) m * laneZ q (vAt v (2 * (j / 2) + 1) (by omega)) m)
          else laneZ q (vAt r j hj) m = laneZ q (vAt v j hj) m ⦄ := by
  unfold backend.neon.ntt.ntt_block_loop1_loop3
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
      (ct_butterfly_spec lo hiv z zq qv (q : ℤ) Zb B Bt hQ hQpos hQlt hz hZb hzq
        (by rw [hloe]; exact hv _ (by omega) ⟨by omega, by omega⟩)
        (by rw [hhie]; exact hv _ (by omega) ⟨by omega, by omega⟩)
        hB0 hBZ hBt hfit)
      (ct_butterfly_val lo hiv z zq qv q Zb B Bt Rinv hR hQ hQpos hQlt hz hZb hzq
        (by rw [hloe]; exact hv _ (by omega) ⟨by omega, by omega⟩)
        (by rw [hhie]; exact hv _ (by omega) ⟨by omega, by omega⟩)
        hB0 hBZ hBt hfit))
    rintro ⟨lo1, hi1'⟩ ⟨⟨hlo1b, hhi1b, -⟩, hbutval⟩
    show (do let v1 ← Array.update v i2 lo1
             let i4 ← i2 + 1#usize
             let a ← Array.update v1 i4 hi1'
             backend.neon.ntt.ntt_block_loop1_loop3 SECOND iter1 qv g a)
        ⦃ (r : Array Vec128 8#usize) => ∀ j (hj : j < 8), ∀ m < 8,
            if 2 * iter.start.val ≤ j then
              (if j % 2 = 0 then
                laneZ q (vAt r j hj) m = laneZ q (vAt v (2 * (j / 2)) (by omega)) m
                  + ψm (4 * g.val + j / 2) m * laneZ q (vAt v (2 * (j / 2) + 1) (by omega)) m
              else
                laneZ q (vAt r j hj) m = laneZ q (vAt v (2 * (j / 2)) (by omega)) m
                  - ψm (4 * g.val + j / 2) m * laneZ q (vAt v (2 * (j / 2) + 1) (by omega)) m)
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
    apply WP.spec_mono (ntt_len1_val SECOND qv q Zb B Bt Rinv ψm hR hQ hQpos hQlt hZb hB0 hBZ
      hBt hfit htbl g hg a iter1 (by rw [hend']; exact hend) (by
        intro j hj hpend
        rw [hav j hj, if_neg (by unfold pend1 at hpend; omega),
          if_neg (by unfold pend1 at hpend; omega)]
        exact hv j hj (by unfold pend1 at hpend ⊢; omega)))
    intro r hr j hj m hm
    have hrj := hr j hj m hm
    have hlo1v : laneZ q lo1 m = laneZ q (vAt v i2.val (by omega)) m
        + ψm i1.val m * laneZ q (vAt v i3.val (by omega)) m := by
      have hb := (hbutval m hm).1
      rw [hzpsi m hm, hloe, hhie] at hb
      exact hb
    have hhi1v : laneZ q hi1' m = laneZ q (vAt v i2.val (by omega)) m
        - ψm i1.val m * laneZ q (vAt v i3.val (by omega)) m := by
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
            vAt_congr v (by omega) (by omega) (show i3.val = 2 * (j / 2) + 1 from by omega),
            show i1.val = 4 * g.val + j / 2 from by omega]
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

/-- **The `len = 2` level's two halves, as residues.**  `h` walks the two halves of the group,
each taking its own ψ pair — `fwd2` at table position `2g + h` — so the ψ family is indexed by
that position, and `j / 4` recovers `h`. -/
theorem ntt_len2_outer_val (SECOND : Bool) (qv : Vec128) (q : ℕ) (Zb B Bt : ℤ) (Rinv : ZMod q)
    (ψ2 : ℕ → ℕ → ZMod q) (hR : ((2 ^ 16 : ℤ) : ZMod q) * Rinv = 1)
    (hQ : ∀ i < 8, (lane16 qv i).toInt = (q : ℤ)) (hQpos : 0 < (q : ℤ)) (hQlt : (q : ℤ) ≤ 2 ^ 14)
    (hZb : Zb ≤ 2 ^ 14)
    (hB0 : 0 ≤ B) (hBZ : B * Zb < 2 ^ 15 * (q : ℤ))
    (hBt : B * Zb + 2 ^ 15 * (q : ℤ) ≤ 2 ^ 16 * Bt) (hfit : B + Bt ≤ 32767)
    (htbl : ∀ kk : Usize, kk.val < 8 → ∃ z zq : Vec128,
        backend.neon.ntt.fwd2 SECOND kk = ok (z, zq) ∧
        (∀ i < 8, |(lane16 z i).toInt| ≤ Zb) ∧
        (∀ i < 8, (2 ^ 16 : ℤ) ∣ ((lane16 zq i).toInt * (q : ℤ) - (lane16 z i).toInt)) ∧
        (∀ m < 8, laneZ q z m * Rinv = ψ2 kk.val m))
    (g : Usize) (hg : g.val < 4) (v : Array Vec128 8#usize)
    (iter : core.ops.range.Range Usize) (hend : iter.«end».val = 2)
    (hv : ∀ j (hj : j < 8), 4 * iter.start.val ≤ j → VecBnd (vAt v j hj) B) :
    backend.neon.ntt.ntt_block_loop1_loop2 SECOND iter qv g v
      ⦃ (r : Array Vec128 8#usize) => ∀ j (hj : j < 8), ∀ m < 8,
          if 4 * iter.start.val ≤ j then
            (if j % 4 < 2 then
              laneZ q (vAt r j hj) m = laneZ q (vAt v (4 * (j / 4) + j % 2) (by omega)) m
                + ψ2 (2 * g.val + j / 4) m
                    * laneZ q (vAt v (4 * (j / 4) + j % 2 + 2) (by omega)) m
            else
              laneZ q (vAt r j hj) m = laneZ q (vAt v (4 * (j / 4) + j % 2) (by omega)) m
                - ψ2 (2 * g.val + j / 4) m
                    * laneZ q (vAt v (4 * (j / 4) + j % 2 + 2) (by omega)) m)
          else laneZ q (vAt r j hj) m = laneZ q (vAt v j hj) m ⦄ := by
  unfold backend.neon.ntt.ntt_block_loop1_loop2
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
      (ntt_len2_bnd qv z zq (q : ℤ) Zb B Bt hQ hQpos hQlt hz hZb hzq hB0 hBZ hBt hfit
        v iter.start hh2 ⟨0#usize, 2#usize⟩ rfl (by
          intro j hj hpend
          exact hv j hj (by unfold pend2 at hpend; scalar_tac)))
      (ntt_len2_val qv z zq q Zb B Bt Rinv (ψ2 i1.val) hR (fun m hm => hzpsi m hm) hQ hQpos hQlt
        hz hZb hzq hB0 hBZ hBt hfit v iter.start hh2 ⟨0#usize, 2#usize⟩ rfl (by
          intro j hj hpend
          exact hv j hj (by unfold pend2 at hpend; scalar_tac))))
    rintro v1 ⟨hv1b, hv1v⟩
    have hz0 : ((⟨0#usize, 2#usize⟩ : core.ops.range.Range Usize)).start.val = 0 := by scalar_tac
    simp only [hz0, Nat.add_zero] at hv1v
    apply WP.spec_mono (ntt_len2_outer_val SECOND qv q Zb B Bt Rinv ψ2 hR hQ hQpos hQlt hZb hB0
      hBZ hBt hfit htbl g hg v1 iter1 (by rw [hend']; exact hend) (by
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
      · -- a later half: `v1` still agrees with `v` at every index this iteration reads
        rw [if_pos hnext] at hrj
        have hp1 := hv1v (4 * (j / 4) + j % 2) (by omega) m hm
        have hp2 := hv1v (4 * (j / 4) + j % 2 + 2) (by omega) m hm
        rw [if_neg (by omega), if_neg (by omega)] at hp1
        rw [if_neg (by omega), if_neg (by omega)] at hp2
        by_cases hpar : j % 4 < 2
        · rw [if_pos hpar] at hrj ⊢
          rw [hrj, hp1, hp2]
        · rw [if_neg hpar] at hrj ⊢
          rw [hrj, hp1, hp2]
      · -- this half: the inner pass has already written it, and the rest is untouched
        rw [if_neg hnext] at hrj
        rw [hrj]
        have hjq : j / 4 = iter.start.val := by omega
        have hpsi : ψ2 i1.val m = ψ2 (2 * g.val + j / 4) m := by rw [hi1v, hjq]
        by_cases hpar : j % 4 < 2
        · rw [if_pos hpar]
          rw [if_pos (show 4 * iter.start.val ≤ j ∧ j < 4 * iter.start.val + 2 from
            ⟨by omega, by omega⟩)] at hvj
          rw [hvj, hpsi]
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

/-! ## The re-centring pass between the transposed levels

`ntt_block_loop1_loop1` Barrett-reduces every vector of the group.  That moves the representative
but not the residue, so for the walk it is the identity — but saying so still needs the whole
`IterMut` framing of `Kopis/Neon/NttBarrettIter.lean`, because the loop writes through an
accumulated `back` closure rather than into an array.

The slice itself never changes across the induction (`iter1.slice = iter.slice`), so the original
is carried as a separate parameter `s0` and every written entry is compared against it. -/

theorem ntt_barrett_iter_val (iter : core.slice.iter.IterMut Vec128)
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
    backend.neon.ntt.ntt_block_loop1_loop1 iter back qv bm round
      ⦃ (r : core.slice.iter.IterMut Vec128 ×
             (core.slice.iter.IterMut Vec128 → core.slice.iter.IterMut Vec128)) =>
          ∀ (im : core.slice.iter.IterMut Vec128), im.slice.val.length = 8 →
            ∀ (j : ℕ) (hj : j < (r.2 im).slice.val.length) (m : ℕ), m < 8 →
              laneZ q (sAt (r.2 im).slice j hj) m = val0 j m ⦄ := by
  unfold backend.neon.ntt.ntt_block_loop1_loop1
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
    apply WP.spec_mono (ntt_barrett_iter_val iter1
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

/-! ## The three transposed layers, in coefficient coordinates

`load_group_spec` puts coefficient `64g + 8m + k` in lane `m` of the group's vector `k`.  These
three read `ctLvl` at that coefficient and say what it is in terms of `k` alone — which is the
form the three level walks produce.  The block index falls out as `c / (2m')`, and it is exactly
the index the matching table accessor loads:

* `len = 4`: block `8g + m`, ψ index `32 + (8g + m)` = `fwd4Idx (8g + m)`;
* `len = 2`: block `16g + 2m + k/4`, ψ index `64 + 16g + k/4 + 2m` = `fwd2Idx (8·(2g + k/4) + m)`;
* `len = 1`: block `32g + 4m + k/2`, ψ index `128 + 32g + k/2 + 4m` = `fwd1Idx (8·(4g + k/2) + m)`.
-/

theorem ctLvl_group4 (q : ℕ) (ψ a0 : ℕ → ZMod q) (g m k : ℕ) (_hm : m < 8) (hk : k < 8) :
    ctLvl q ψ 32 4 a0 (64 * g + 8 * m + k) =
      if k < 4 then a0 (64 * g + 8 * m + k)
          + ψ (32 + (8 * g + m)) * a0 (64 * g + 8 * m + k + 4)
      else a0 (64 * g + 8 * m + k - 4)
          - ψ (32 + (8 * g + m)) * a0 (64 * g + 8 * m + k) := by
  unfold ctLvl
  rw [show (64 * g + 8 * m + k) % (2 * 4) = k from by omega,
    show (64 * g + 8 * m + k) / (2 * 4) = 8 * g + m from by omega]

theorem ctLvl_group2 (q : ℕ) (ψ a0 : ℕ → ZMod q) (g m k : ℕ) (_hm : m < 8) (_hk : k < 8) :
    ctLvl q ψ 64 2 a0 (64 * g + 8 * m + k) =
      if k % 4 < 2 then a0 (64 * g + 8 * m + k)
          + ψ (64 + (16 * g + 2 * m + k / 4)) * a0 (64 * g + 8 * m + k + 2)
      else a0 (64 * g + 8 * m + k - 2)
          - ψ (64 + (16 * g + 2 * m + k / 4)) * a0 (64 * g + 8 * m + k) := by
  unfold ctLvl
  rw [show (64 * g + 8 * m + k) % (2 * 2) = k % 4 from by omega,
    show (64 * g + 8 * m + k) / (2 * 2) = 16 * g + 2 * m + k / 4 from by omega]

theorem ctLvl_group1 (q : ℕ) (ψ a0 : ℕ → ZMod q) (g m k : ℕ) (_hm : m < 8) (_hk : k < 8) :
    ctLvl q ψ 128 1 a0 (64 * g + 8 * m + k) =
      if k % 2 = 0 then a0 (64 * g + 8 * m + k)
          + ψ (128 + (32 * g + 4 * m + k / 2)) * a0 (64 * g + 8 * m + k + 1)
      else a0 (64 * g + 8 * m + k - 1)
          - ψ (128 + (32 * g + 4 * m + k / 2)) * a0 (64 * g + 8 * m + k) := by
  unfold ctLvl
  rw [show (64 * g + 8 * m + k) % (2 * 1) = k % 2 from by omega,
    show (64 * g + 8 * m + k) / (2 * 1) = 32 * g + 4 * m + k / 2 from by omega]
  by_cases h : k % 2 = 0
  · rw [if_pos (by omega), if_pos h]
  · rw [if_neg (by omega), if_neg h]

/-! ## The forward tables carry the ψ the layers want

`Kopis/Neon/Tables.lean` says each accessor's lane `m` is the ζ table at a closed-form index;
`Kopis/CrtZeta.lean`'s `zetaQ` is that entry times `R⁻¹`, which is the plain twiddle.  Putting the
two together turns the closed forms `fwd4Idx` / `fwd2Idx` / `fwd1Idx` into exactly the block
indices `ctLvl_group4` / `_group2` / `_group1` ask for. -/

open Kopis.CrtZeta in
theorem psiVal_fwd4 (SECOND : Bool) (q : ℕ) (Rinv : ZMod q) (g : Usize) (hg : g.val < 4) :
    ∃ z zq : Vec128, backend.neon.ntt.fwd4 SECOND g = ok (z, zq) ∧
      ∀ m < 8, laneZ q z m * Rinv
        = zetaQ (zetasOf SECOND) Rinv (32 + (8 * g.val + m)) := by
  obtain ⟨r, hr, hp⟩ := WP.spec_imp_exists (fwd4_spec SECOND g (by scalar_tac))
  refine ⟨r.1, r.2, by rw [hr], fun m hm => ?_⟩
  unfold laneZ zetaQ zint
  rw [(hp m hm).1]
  simp only [tblZ, Bool.false_eq_true, if_false]
  rw [show (fwd4Idx (8 * g.val + m)).toNat = 32 + (8 * g.val + m) from by
    unfold fwd4Idx; omega]

open Kopis.CrtZeta in
theorem psiVal_fwd2 (SECOND : Bool) (q : ℕ) (Rinv : ZMod q) (kk : Usize) (hkk : kk.val < 8) :
    ∃ z zq : Vec128, backend.neon.ntt.fwd2 SECOND kk = ok (z, zq) ∧
      ∀ m < 8, laneZ q z m * Rinv
        = zetaQ (zetasOf SECOND) Rinv (64 + (16 * (kk.val / 2) + 2 * m + kk.val % 2)) := by
  obtain ⟨r, hr, hp⟩ := WP.spec_imp_exists (fwd2_spec SECOND kk (by scalar_tac))
  refine ⟨r.1, r.2, by rw [hr], fun m hm => ?_⟩
  unfold laneZ zetaQ zint
  rw [(hp m hm).1]
  simp only [tblZ, Bool.false_eq_true, if_false]
  rw [show (fwd2Idx (8 * kk.val + m)).toNat
      = 64 + (16 * (kk.val / 2) + 2 * m + kk.val % 2) from by
    unfold fwd2Idx; omega]

open Kopis.CrtZeta in
theorem psiVal_fwd1 (SECOND : Bool) (q : ℕ) (Rinv : ZMod q) (kk : Usize) (hkk : kk.val < 16) :
    ∃ z zq : Vec128, backend.neon.ntt.fwd1 SECOND kk = ok (z, zq) ∧
      ∀ m < 8, laneZ q z m * Rinv
        = zetaQ (zetasOf SECOND) Rinv (128 + (32 * (kk.val / 4) + 4 * m + kk.val % 4)) := by
  obtain ⟨r, hr, hp⟩ := WP.spec_imp_exists (fwd1_spec SECOND kk (by scalar_tac))
  refine ⟨r.1, r.2, by rw [hr], fun m hm => ?_⟩
  unfold laneZ zetaQ zint
  rw [(hp m hm).1]
  simp only [tblZ, Bool.false_eq_true, if_false]
  rw [show (fwd1Idx (8 * kk.val + m)).toNat
      = 128 + (32 * (kk.val / 4) + 4 * m + kk.val % 4) from by
    unfold fwd1Idx; omega]

/-! ## The four transposed groups, as residues

The bookkeeping the last three sections set up, run once per group: `load_group_spec` puts
coefficient `64g + 8m + k` in lane `m` of vector `k`; each level walk rewrites `k` to its partner;
`ctLvl_group4` / `_group2` / `_group1` read the answer back as a Cooley-Tukey layer at that
coefficient; and `store_group_spec` returns it to the block. -/

/-- The three transposed levels, as a function of the view they start from. -/
noncomputable def fwdT (q : ℕ) (ψ a0 : ℕ → ZMod q) : ℕ → ZMod q :=
  ctLvl q ψ 128 1 (ctLvl q ψ 64 2 (ctLvl q ψ 32 4 a0))

theorem ntt_group_val (SECOND : Bool) (b : Array I16 256#usize) (qv bm round : Vec128)
    (q : ℕ) (Zb M Ain Amid Ar A2 A3 : ℤ) (Rinv : ZMod q) (ψ a0 : ℕ → ZMod q)
    (hR : ((2 ^ 16 : ℤ) : ZMod q) * Rinv = 1)
    (hQ : ∀ i < 8, (lane16 qv i).toInt = (q : ℤ)) (hQpos : 0 < (q : ℤ))
    (hQ14 : (q : ℤ) < 2 ^ 14) (hQodd : ¬ (2 ∣ (q : ℤ))) (hZb : Zb ≤ 2 ^ 14)
    (hM : ∀ i < 8, (lane16 bm i).toInt = M) (hMpos : 0 < M) (hMlt : M < 2 ^ 15)
    (hD : |2 ^ 27 - (q : ℤ) * M| ≤ 2047)
    (hRnd : ∀ i < 8, (lane16 round i).toInt = 2 ^ 10)
    (htbl4 : ∀ kk : Usize, kk.val < 4 → ∃ z zq : Vec128,
        backend.neon.ntt.fwd4 SECOND kk = ok (z, zq) ∧ PsiOk z zq (q : ℤ) Zb ∧
        ∀ m < 8, laneZ q z m * Rinv = ψ (32 + (8 * kk.val + m)))
    (htbl2 : ∀ kk : Usize, kk.val < 8 → ∃ z zq : Vec128,
        backend.neon.ntt.fwd2 SECOND kk = ok (z, zq) ∧ PsiOk z zq (q : ℤ) Zb ∧
        ∀ m < 8, laneZ q z m * Rinv = ψ (64 + (16 * (kk.val / 2) + 2 * m + kk.val % 2)))
    (htbl1 : ∀ kk : Usize, kk.val < 16 → ∃ z zq : Vec128,
        backend.neon.ntt.fwd1 SECOND kk = ok (z, zq) ∧ PsiOk z zq (q : ℤ) Zb ∧
        ∀ m < 8, laneZ q z m * Rinv = ψ (128 + (32 * (kk.val / 4) + 4 * m + kk.val % 4)))
    (hAin : 0 ≤ Ain) (hAr : 0 ≤ Ar) (hA2 : 0 ≤ A2) (hreset : ((q : ℤ) - 1) / 2 ≤ Ar)
    (hs4 : LevelStep (q : ℤ) Zb Ain (Amid - Ain))
    (hs2 : LevelStep (q : ℤ) Zb Ar (A2 - Ar))
    (hs1 : LevelStep (q : ℤ) Zb A2 (A3 - A2))
    (iter : core.ops.range.Range Usize) (hend : iter.«end».val = 4)
    (hb : ∀ p < 256, 64 * iter.start.val ≤ p → |(b.val[p]!).val| ≤ Ain)
    (hva : ∀ c < 256, posZ q b c =
        if c < 64 * iter.start.val then fwdT q ψ a0 c else a0 c) :
    backend.neon.ntt.ntt_block_loop1 SECOND iter b qv bm round
      ⦃ (r : Array I16 256#usize) =>
          (∀ p < 256, if 64 * iter.start.val ≤ p then |(r.val[p]!).val| ≤ A3
            else (r.val[p]!).val = (b.val[p]!).val) ∧
          (∀ c < 256, posZ q r c = fwdT q ψ a0 c) ⦄ := by
  unfold backend.neon.ntt.ntt_block_loop1
  by_cases hlt : iter.start.val < iter.«end».val
  · let* ⟨ o, iter1, ho, hstart', hend' ⟩ ← core.iter.range.IteratorRange.next_Usize_some_spec
    rw [ho]
    simp only
    have hg4 : iter.start.val < 4 := by omega
    set g := iter.start with hg_def
    -- 1. load and transpose
    apply WP.spec_bind (load_group_spec b g hg4)
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
    -- 2. the `len = 4` ψ pair, and 3. that level
    obtain ⟨z4, zq4, hz4e, ⟨hz4, hzq4⟩, hz4v⟩ := htbl4 g hg4
    rw [hz4e, bind_tc_ok]
    apply WP.spec_bind (WP.spec_both
      (ntt_len4_bnd qv z4 zq4 (q : ℤ) Zb Ain (Amid - Ain) hQ hQpos (by omega)
        hz4 hZb hzq4 hAin hs4.1 hs4.2.1 hs4.2.2 v ⟨0#usize, 4#usize⟩ rfl
        (fun j hj _ => hvb j hj))
      (ntt_len4_val qv z4 zq4 q Zb Ain (Amid - Ain) Rinv
        (fun m => ψ (32 + (8 * g.val + m))) hR (fun m hm => hz4v m hm) hQ hQpos (by omega)
        hz4 hZb hzq4 hAin hs4.1 hs4.2.1 hs4.2.2 v ⟨0#usize, 4#usize⟩ rfl
        (fun j hj _ => hvb j hj)))
    rintro v1 ⟨hv1, hv1v⟩
    have hv1b : ∀ j (hj : j < 8), VecBnd (vAt v1 j hj) Amid := by
      intro j hj
      have := hv1 j hj
      rw [if_pos (by unfold pend4; scalar_tac)] at this
      exact this.mono (by omega)
    have hv1Z : ∀ k (hk : k < 8), ∀ m < 8,
        laneZ q (vAt v1 k hk) m = ctLvl q ψ 32 4 a0 (64 * g.val + 8 * m + k) := by
      intro k hk m hm
      have h := hv1v k hk m hm
      rw [ctLvl_group4 q ψ a0 g.val m k hm hk]
      by_cases hk4 : k < 4
      · rw [if_pos (show ((⟨0#usize, 4#usize⟩ : core.ops.range.Range Usize)).start.val ≤ k
              ∧ k < 4 from ⟨by scalar_tac, hk4⟩)] at h
        rw [h, if_pos hk4, hvZ (k % 4) (by omega) m hm, hvZ (k % 4 + 4) (by omega) m hm,
          show 64 * g.val + 8 * m + k % 4 = 64 * g.val + 8 * m + k from by omega,
          show 64 * g.val + 8 * m + (k % 4 + 4) = 64 * g.val + 8 * m + k + 4 from by omega]
      · rw [if_neg (show ¬ (((⟨0#usize, 4#usize⟩ : core.ops.range.Range Usize)).start.val ≤ k
              ∧ k < 4) from by scalar_tac),
          if_pos (show 4 + ((⟨0#usize, 4#usize⟩ : core.ops.range.Range Usize)).start.val ≤ k
              ∧ k < 8 from ⟨by scalar_tac, hk⟩)] at h
        rw [h, if_neg hk4, hvZ (k % 4) (by omega) m hm, hvZ (k % 4 + 4) (by omega) m hm,
          show 64 * g.val + 8 * m + k % 4 = 64 * g.val + 8 * m + k - 4 from by omega,
          show 64 * g.val + 8 * m + (k % 4 + 4) = 64 * g.val + 8 * m + k from by omega]
    -- 4. the slice round trip, and 5. the re-centring pass
    let* ⟨ s, to_back, hs_val, hto_back ⟩ ← Array.to_slice_mut_spec
    let* ⟨ iter2, imb, hi2_slice, hi2_zero, hi2_back ⟩ ← iter_mut_spec
    have hs_len : s.val.length = 8 := by rw [hs_val]; have := v1.property; scalar_tac
    have hi2_len : iter2.slice.val.length = 8 := by rw [hi2_slice]; exact hs_len
    have hi2Z : ∀ (j : ℕ) (hj : j < iter2.slice.val.length), ∀ m < 8,
        laneZ q (sAt iter2.slice j hj) m = ctLvl q ψ 32 4 a0 (64 * g.val + 8 * m + j) := by
      intro j hj m hm
      have hjv : j < 8 := by omega
      have heq : sAt iter2.slice j hj = vAt v1 j hjv := by
        unfold sAt vAt
        exact List.getElem_of_eq (by rw [hi2_slice, hs_val]) _
      rw [heq]
      exact hv1Z j hjv m hm
    apply WP.spec_bind (WP.spec_both
      (ntt_barrett_iter_bnd iter2 (fun im1 => im1) bm round qv (q : ℤ) M hQ hM hRnd
        hQpos hQ14 hQodd hMpos hMlt hD hi2_len (by rw [hi2_zero]; omega)
        (fun im him => him)
        (fun im him j hj hbnd => absurd hj (by rw [hi2_zero]; omega))
        (fun im him j _ hbnd hbnd' => rfl))
      (ntt_barrett_iter_val iter2 (fun im1 => im1) bm round qv q M
        (fun j m => ctLvl q ψ 32 4 a0 (64 * g.val + 8 * m + j)) hQ hM hRnd
        hQpos hQ14 hQodd hMpos hMlt hD hi2_len (by rw [hi2_zero]; omega) hi2Z
        (fun im him => him)
        (fun im him j hj hbnd m hm => absurd hj (by rw [hi2_zero]; omega))
        (fun im him j _ hbnd hbnd' => rfl)))
    rintro ⟨im, bk⟩ ⟨⟨him_len, hbk⟩, hbkv⟩
    obtain ⟨hbk_len, hbk_bnd⟩ := hbk im him_len
    show (do let v2 ← backend.neon.ntt.ntt_block_loop1_loop2 SECOND
                        { start := 0#usize, «end» := 2#usize } qv g
                        (to_back (imb (bk im)))
             let v3 ← backend.neon.ntt.ntt_block_loop1_loop3 SECOND
                        { start := 0#usize, «end» := 4#usize } qv g v2
             let (b1, _) ← backend.neon.ntt.store_group b g v3
             backend.neon.ntt.ntt_block_loop1 SECOND iter1 b1 qv bm round)
        ⦃ (r : Array I16 256#usize) =>
            (∀ p < 256, if 64 * g.val ≤ p then |(r.val[p]!).val| ≤ A3
              else (r.val[p]!).val = (b.val[p]!).val) ∧
            (∀ c < 256, posZ q r c = fwdT q ψ a0 c) ⦄
    set a := to_back (imb (bk im)) with ha_def
    have ha_val : a.val = (bk im).slice.val := by
      rw [ha_def, hi2_back, hto_back]
      exact Std.Array.from_slice_val _ _ (by rw [hbk_len]; simp)
    have hab : ∀ j (hj : j < 8), VecBnd (vAt a j hj) Ar := by
      intro j hj
      have hjb : j < (bk im).slice.val.length := by rw [hbk_len]; omega
      have := hbk_bnd j hjb
      have heq : vAt a j hj = sAt (bk im).slice j hjb := by
        unfold vAt sAt
        exact List.getElem_of_eq ha_val _
      rw [heq]
      exact this.mono hreset
    have haZ : ∀ j (hj : j < 8), ∀ m < 8,
        laneZ q (vAt a j hj) m = ctLvl q ψ 32 4 a0 (64 * g.val + 8 * m + j) := by
      intro j hj m hm
      have hjb : j < (bk im).slice.val.length := by rw [hbk_len]; omega
      have heq : vAt a j hj = sAt (bk im).slice j hjb := by
        unfold vAt sAt
        exact List.getElem_of_eq ha_val _
      rw [heq]
      exact hbkv im him_len j hjb m hm
    -- 7. `len = 2` in its two halves
    apply WP.spec_bind (WP.spec_both
      (ntt_len2_outer_bnd SECOND qv (q : ℤ) Zb Ar (A2 - Ar) hQ hQpos (by omega) hZb
        hAr hs2.1 hs2.2.1 hs2.2.2 (fun kk hkk => by
          obtain ⟨z, zq, he, hp, -⟩ := htbl2 kk hkk
          exact ⟨z, zq, he, hp.1, hp.2⟩)
        g hg4 a ⟨0#usize, 2#usize⟩ rfl (fun j hj _ => hab j hj))
      (ntt_len2_outer_val SECOND qv q Zb Ar (A2 - Ar) Rinv
        (fun kk m => ψ (64 + (16 * (kk / 2) + 2 * m + kk % 2))) hR hQ hQpos (by omega) hZb
        hAr hs2.1 hs2.2.1 hs2.2.2 (fun kk hkk => by
          obtain ⟨z, zq, he, hp, hv⟩ := htbl2 kk hkk
          exact ⟨z, zq, he, hp.1, hp.2, hv⟩)
        g hg4 a ⟨0#usize, 2#usize⟩ rfl (fun j hj _ => hab j hj)))
    rintro v2 ⟨hv2, hv2v⟩
    have hv2b : ∀ j (hj : j < 8), VecBnd (vAt v2 j hj) A2 := by
      intro j hj
      have := hv2 j hj
      rw [if_pos (by scalar_tac)] at this
      exact this.mono (by omega)
    have hv2Z : ∀ k (hk : k < 8), ∀ m < 8, laneZ q (vAt v2 k hk) m
        = ctLvl q ψ 64 2 (ctLvl q ψ 32 4 a0) (64 * g.val + 8 * m + k) := by
      intro k hk m hm
      have h := hv2v k hk m hm
      rw [if_pos (show 4 * ((⟨0#usize, 2#usize⟩ : core.ops.range.Range Usize)).start.val ≤ k
        from by scalar_tac)] at h
      rw [ctLvl_group2 q ψ (ctLvl q ψ 32 4 a0) g.val m k hm hk]
      have hpsi : ψ (64 + (16 * ((2 * g.val + k / 4) / 2) + 2 * m + (2 * g.val + k / 4) % 2))
          = ψ (64 + (16 * g.val + 2 * m + k / 4)) := by
        rw [show (2 * g.val + k / 4) / 2 = g.val from by omega,
          show (2 * g.val + k / 4) % 2 = k / 4 from by omega]
      by_cases hk2 : k % 4 < 2
      · rw [if_pos hk2] at h
        rw [h, if_pos hk2, hpsi, haZ (4 * (k / 4) + k % 2) (by omega) m hm,
          haZ (4 * (k / 4) + k % 2 + 2) (by omega) m hm,
          show 64 * g.val + 8 * m + (4 * (k / 4) + k % 2) = 64 * g.val + 8 * m + k from by omega,
          show 64 * g.val + 8 * m + (4 * (k / 4) + k % 2 + 2)
            = 64 * g.val + 8 * m + k + 2 from by omega]
      · rw [if_neg hk2] at h
        rw [h, if_neg hk2, hpsi, haZ (4 * (k / 4) + k % 2) (by omega) m hm,
          haZ (4 * (k / 4) + k % 2 + 2) (by omega) m hm,
          show 64 * g.val + 8 * m + (4 * (k / 4) + k % 2)
            = 64 * g.val + 8 * m + k - 2 from by omega,
          show 64 * g.val + 8 * m + (4 * (k / 4) + k % 2 + 2)
            = 64 * g.val + 8 * m + k from by omega]
    -- 8. `len = 1`
    apply WP.spec_bind (WP.spec_both
      (ntt_len1_bnd SECOND qv (q : ℤ) Zb A2 (A3 - A2) hQ hQpos (by omega) hZb
        hA2 hs1.1 hs1.2.1 hs1.2.2 (fun kk hkk => by
          obtain ⟨z, zq, he, hp, -⟩ := htbl1 kk hkk
          exact ⟨z, zq, he, hp.1, hp.2⟩)
        g hg4 v2 ⟨0#usize, 4#usize⟩ rfl (fun j hj _ => hv2b j hj))
      (ntt_len1_val SECOND qv q Zb A2 (A3 - A2) Rinv
        (fun kk m => ψ (128 + (32 * (kk / 4) + 4 * m + kk % 4))) hR hQ hQpos (by omega) hZb
        hA2 hs1.1 hs1.2.1 hs1.2.2 (fun kk hkk => by
          obtain ⟨z, zq, he, hp, hv⟩ := htbl1 kk hkk
          exact ⟨z, zq, he, hp.1, hp.2, hv⟩)
        g hg4 v2 ⟨0#usize, 4#usize⟩ rfl (fun j hj _ => hv2b j hj)))
    rintro v3 ⟨hv3, hv3v⟩
    have hv3b : ∀ j (hj : j < 8), VecBnd (vAt v3 j hj) A3 := by
      intro j hj
      have := hv3 j hj
      rw [if_pos (by unfold pend1; scalar_tac)] at this
      exact this.mono (by omega)
    have hv3Z : ∀ k (hk : k < 8), ∀ m < 8,
        laneZ q (vAt v3 k hk) m = fwdT q ψ a0 (64 * g.val + 8 * m + k) := by
      intro k hk m hm
      have h := hv3v k hk m hm
      rw [if_pos (show 2 * ((⟨0#usize, 4#usize⟩ : core.ops.range.Range Usize)).start.val ≤ k
        from by scalar_tac)] at h
      unfold fwdT
      rw [ctLvl_group1 q ψ (ctLvl q ψ 64 2 (ctLvl q ψ 32 4 a0)) g.val m k hm hk]
      have hpsi : ψ (128 + (32 * ((4 * g.val + k / 2) / 4) + 4 * m + (4 * g.val + k / 2) % 4))
          = ψ (128 + (32 * g.val + 4 * m + k / 2)) := by
        rw [show (4 * g.val + k / 2) / 4 = g.val from by omega,
          show (4 * g.val + k / 2) % 4 = k / 2 from by omega]
      by_cases hpar : k % 2 = 0
      · rw [if_pos hpar] at h
        rw [h, if_pos hpar, hpsi, hv2Z (2 * (k / 2)) (by omega) m hm,
          hv2Z (2 * (k / 2) + 1) (by omega) m hm,
          show 64 * g.val + 8 * m + 2 * (k / 2) = 64 * g.val + 8 * m + k from by omega,
          show 64 * g.val + 8 * m + (2 * (k / 2) + 1)
            = 64 * g.val + 8 * m + k + 1 from by omega]
      · rw [if_neg hpar] at h
        rw [h, if_neg hpar, hpsi, hv2Z (2 * (k / 2)) (by omega) m hm,
          hv2Z (2 * (k / 2) + 1) (by omega) m hm,
          show 64 * g.val + 8 * m + 2 * (k / 2) = 64 * g.val + 8 * m + k - 1 from by omega,
          show 64 * g.val + 8 * m + (2 * (k / 2) + 1) = 64 * g.val + 8 * m + k from by omega]
    -- 9. store the group back
    apply WP.spec_bind (store_group_spec b g hg4 v3)
    rintro ⟨b1, unused⟩ hb1
    show backend.neon.ntt.ntt_block_loop1 SECOND iter1 b1 qv bm round
        ⦃ (r : Array I16 256#usize) =>
            (∀ p < 256, if 64 * g.val ≤ p then |(r.val[p]!).val| ≤ A3
              else (r.val[p]!).val = (b.val[p]!).val) ∧
            (∀ c < 256, posZ q r c = fwdT q ψ a0 c) ⦄
    have hb1Z : ∀ c < 256, posZ q b1 c =
        if c < 64 * g.val + 64 then fwdT q ψ a0 c else a0 c := by
      intro c hc
      have h := hb1 c hc
      unfold posZ
      rw [h]
      by_cases hin : 64 * g.val ≤ c ∧ c < 64 * g.val + 64
      · rw [if_pos hin, if_pos (by omega)]
        have := hv3Z ((c - 64 * g.val) % 8) (by omega) ((c - 64 * g.val) / 8) (by omega)
        unfold laneZ at this
        rw [this, show 64 * g.val + 8 * ((c - 64 * g.val) / 8) + (c - 64 * g.val) % 8 = c
          from by omega]
      · rw [if_neg hin]
        have := hva c hc
        unfold posZ at this
        rw [this]
        by_cases hbelow : c < 64 * g.val
        · rw [if_pos hbelow, if_pos (by omega)]
        · rw [if_neg hbelow, if_neg (by omega)]
    -- 10. and the remaining groups
    apply WP.spec_mono (ntt_group_val SECOND b1 qv bm round q Zb M Ain Amid Ar A2 A3 Rinv ψ a0
      hR hQ hQpos hQ14 hQodd hZb hM hMpos hMlt hD hRnd htbl4 htbl2 htbl1 hAin hAr hA2 hreset
      hs4 hs2 hs1 iter1 (by rw [hend']; exact hend) (by
        intro p hp hge
        have := hb1 p hp
        rw [if_neg (by scalar_tac)] at this
        rw [this]
        exact hb p hp (by omega))
      (by
        intro c hc
        rw [hb1Z c hc]
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
        rw [hrp]
        have := hb1 p hp
        rw [if_pos (by scalar_tac)] at this
        rw [this]
        exact hv3b _ (by omega) _ (by omega)
    · rw [if_neg hge]
      rw [if_neg (by omega)] at hrp
      rw [hrp]
      have := hb1 p hp
      rw [if_neg (by scalar_tac)] at this
      exact this
  · let* ⟨ o, iter1, hnone, _ ⟩ ← core.iter.range.IteratorRange.next_Usize_none_spec
    rw [hnone]
    have hs4' : 4 ≤ iter.start.val := by scalar_tac
    refine (WP.spec_ok _).mpr ⟨fun p hp => ?_, fun c hc => ?_⟩
    · rw [if_neg (by omega)]
    · rw [hva c hc, if_pos (by omega)]
termination_by 4 - iter.start.val
decreasing_by scalar_decr_tac

/-! ## The forward transform

The constant setup, the five whole-vector levels, the four transposed groups, and the final
re-centring pass — the same composition `ntt_block_bnd` makes, with the value chain riding along.
The result is centred *and* equal to the eight Cooley-Tukey layers applied to the input view. -/

/-- The whole forward transform, as a function of the input view. -/
noncomputable def fwdAll (q : ℕ) (ψ f : ℕ → ZMod q) : ℕ → ZMod q := fwdT q ψ (fwdH q ψ f)

theorem ntt_block_val (SECOND : Bool) (b : Array I16 256#usize) (q : ℕ) (Zb M : ℤ)
    (A1 A2 A3 A4 A5 Amid Ar A6 A7 : ℤ) (Rinv : ZMod q) (ψ f : ℕ → ZMod q)
    (qc mc rc : I16)
    (hR : ((2 ^ 16 : ℤ) : ZMod q) * Rinv = 1)
    (hq : backend.crt.q SECOND = ok qc) (hqv : qc.val = (q : ℤ))
    (hm : backend.crt.barrett_m SECOND = ok mc) (hmv : mc.val = M)
    (hrc : (1#i16 : I16) <<< (10#i32 : Std.I32) = ok rc) (hrcv : rc.val = 2 ^ 10)
    (hQpos : 0 < (q : ℤ)) (hQ14 : (q : ℤ) < 2 ^ 14) (hQodd : ¬ (2 ∣ (q : ℤ)))
    (hZb : Zb ≤ 2 ^ 14)
    (hMpos : 0 < M) (hMlt : M < 2 ^ 15) (hD : |2 ^ 27 - (q : ℤ) * M| ≤ 2047)
    (hzeta : ∀ kk : Usize, kk.val < 256 → ∃ zi zqi : I16,
        backend.crt.zeta SECOND kk = ok zi ∧ backend.crt.zeta_q SECOND kk = ok zqi ∧
        |zi.val| ≤ Zb ∧ (2 ^ 16 : ℤ) ∣ (zqi.val * (q : ℤ) - zi.val) ∧
        ((zi.val : ℤ) : ZMod q) * Rinv = ψ kk.val)
    (htbl4 : ∀ kk : Usize, kk.val < 4 → ∃ z zq : Vec128,
        backend.neon.ntt.fwd4 SECOND kk = ok (z, zq) ∧ PsiOk z zq (q : ℤ) Zb ∧
        ∀ m < 8, laneZ q z m * Rinv = ψ (32 + (8 * kk.val + m)))
    (htbl2 : ∀ kk : Usize, kk.val < 8 → ∃ z zq : Vec128,
        backend.neon.ntt.fwd2 SECOND kk = ok (z, zq) ∧ PsiOk z zq (q : ℤ) Zb ∧
        ∀ m < 8, laneZ q z m * Rinv = ψ (64 + (16 * (kk.val / 2) + 2 * m + kk.val % 2)))
    (htbl1 : ∀ kk : Usize, kk.val < 16 → ∃ z zq : Vec128,
        backend.neon.ntt.fwd1 SECOND kk = ok (z, zq) ∧ PsiOk z zq (q : ℤ) Zb ∧
        ∀ m < 8, laneZ q z m * Rinv = ψ (128 + (32 * (kk.val / 4) + 4 * m + kk.val % 4)))
    (hA1 : 0 ≤ A1) (hA2 : 0 ≤ A2) (hA4 : 0 ≤ A4) (hA5 : 0 ≤ A5) (hAr : 0 ≤ Ar)
    (hA6 : 0 ≤ A6)
    (hresetR : ((q : ℤ) - 1) / 2 ≤ Ar)
    (hs0 : LevelStep (q : ℤ) Zb (((q : ℤ) - 1) / 2) (A1 - ((q : ℤ) - 1) / 2))
    (hs1 : LevelStep (q : ℤ) Zb A1 (A2 - A1)) (hs2 : LevelStep (q : ℤ) Zb A2 (A3 - A2))
    (hs3 : LevelStep (q : ℤ) Zb (((q : ℤ) - 1) / 2) (A4 - ((q : ℤ) - 1) / 2))
    (hs4 : LevelStep (q : ℤ) Zb A4 (A5 - A4))
    (hg4 : LevelStep (q : ℤ) Zb A5 (Amid - A5))
    (hg2 : LevelStep (q : ℤ) Zb Ar (A6 - Ar)) (hg1 : LevelStep (q : ℤ) Zb A6 (A7 - A6))
    (hb : BlockBnd b (((q : ℤ) - 1) / 2)) (hf : ∀ c < 256, posZ q b c = f c) :
    backend.neon.ntt.ntt_block SECOND b
      ⦃ (r : Array I16 256#usize) =>
          BlockBnd r (((q : ℤ) - 1) / 2) ∧ ∀ c < 256, posZ q r c = fwdAll q ψ f c ⦄ := by
  have hQ0 : 0 ≤ ((q : ℤ) - 1) / 2 := by omega
  unfold backend.neon.ntt.ntt_block
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
  -- the five whole-vector levels
  apply WP.spec_bind (ntt_horizontal_val SECOND b qv bm round q Zb M (((q : ℤ) - 1) / 2) A1 A2 A3
    A4 A5 Rinv ψ f hR hQv hQpos hQ14 hQodd hZb hMv hMpos hMlt hD hRv hzeta hQ0 hA1 hA2 hA4
    (le_refl _) hs0 hs1 hs2 hs3 hs4 hb hf)
  rintro b1 ⟨hb1, hb1v⟩
  -- the four transposed groups
  apply WP.spec_bind (ntt_group_val SECOND b1 qv bm round q Zb M A5 Amid Ar A6 A7 Rinv ψ
    (fwdH q ψ f) hR hQv hQpos hQ14 hQodd hZb hMv hMpos hMlt hD hRv htbl4 htbl2 htbl1 hA5 hAr
    hA6 hresetR hg4 hg2 hg1 ⟨0#usize, 4#usize⟩ rfl (fun p hp _ => hb1 p hp)
    (by intro c hc; rw [hb1v c hc, if_neg (by scalar_tac)]))
  rintro b2 ⟨hb2, hb2v⟩
  -- and the final re-centring pass
  apply WP.spec_mono (barrett_block_spec b2 bm round qv (q : ℤ) M hQv hMv hRv hQpos hQ14 hQodd
    hMpos hMlt hD)
  rintro r ⟨hrb, hrres⟩
  refine ⟨hrb, fun c hc => ?_⟩
  have hcast : (((r.val[c]!).val - (b2.val[c]!).val : ℤ) : ZMod q) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ q).mpr (hrres c hc)
  push_cast at hcast
  unfold fwdAll
  rw [← hb2v c hc]
  unfold posZ
  linear_combination hcast

/-! ## The table hypotheses of `ntt_block_val`, discharged

`psiOk_fwd4` and `psiVal_fwd4` are two statements about the same accessor call; the walk wants
them together, and pairing them after the fact would mean identifying the two `ok (z, zq)`s.
These prove all three conjuncts from one `fwd4_spec`. -/

open Kopis.CrtZeta in
theorem psiFull_fwd4 (SECOND : Bool) (q : ℕ) (Zb : ℤ) (Rinv : ZMod q)
    (hz : ∀ k < 256, |((zetasOf SECOND).val[k]!).val| ≤ Zb)
    (hinv : (2 ^ 16 : ℤ) ∣ ((qinvOf SECOND).val * (q : ℤ) - 1))
    (kk : Usize) (hkk : kk.val < 4) :
    ∃ z zq : Vec128, backend.neon.ntt.fwd4 SECOND kk = ok (z, zq) ∧ PsiOk z zq (q : ℤ) Zb ∧
      ∀ m < 8, laneZ q z m * Rinv
        = zetaQ (zetasOf SECOND) Rinv (32 + (8 * kk.val + m)) := by
  obtain ⟨r, hr, hp⟩ := WP.spec_imp_exists (fwd4_spec SECOND kk (by scalar_tac))
  refine ⟨r.1, r.2, by rw [hr], ⟨fun i hi => ?_, fun i hi => ?_⟩, fun m hm => ?_⟩
  · rw [(hp i hi).1]
    unfold tblZ
    split
    · rw [abs_neg]; exact hz _ (by unfold fwd4Idx; omega)
    · exact hz _ (by unfold fwd4Idx; omega)
  · rw [(hp i hi).1, (hp i hi).2]
    exact tblZq_mont _ _ _ hinv
  · unfold laneZ zetaQ zint
    rw [(hp m hm).1]
    simp only [tblZ, Bool.false_eq_true, if_false]
    rw [show (fwd4Idx (8 * kk.val + m)).toNat = 32 + (8 * kk.val + m) from by
      unfold fwd4Idx; omega]

open Kopis.CrtZeta in
theorem psiFull_fwd2 (SECOND : Bool) (q : ℕ) (Zb : ℤ) (Rinv : ZMod q)
    (hz : ∀ k < 256, |((zetasOf SECOND).val[k]!).val| ≤ Zb)
    (hinv : (2 ^ 16 : ℤ) ∣ ((qinvOf SECOND).val * (q : ℤ) - 1))
    (kk : Usize) (hkk : kk.val < 8) :
    ∃ z zq : Vec128, backend.neon.ntt.fwd2 SECOND kk = ok (z, zq) ∧ PsiOk z zq (q : ℤ) Zb ∧
      ∀ m < 8, laneZ q z m * Rinv
        = zetaQ (zetasOf SECOND) Rinv (64 + (16 * (kk.val / 2) + 2 * m + kk.val % 2)) := by
  obtain ⟨r, hr, hp⟩ := WP.spec_imp_exists (fwd2_spec SECOND kk (by scalar_tac))
  refine ⟨r.1, r.2, by rw [hr], ⟨fun i hi => ?_, fun i hi => ?_⟩, fun m hm => ?_⟩
  · rw [(hp i hi).1]
    unfold tblZ
    split
    · rw [abs_neg]; exact hz _ (by unfold fwd2Idx; omega)
    · exact hz _ (by unfold fwd2Idx; omega)
  · rw [(hp i hi).1, (hp i hi).2]
    exact tblZq_mont _ _ _ hinv
  · unfold laneZ zetaQ zint
    rw [(hp m hm).1]
    simp only [tblZ, Bool.false_eq_true, if_false]
    rw [show (fwd2Idx (8 * kk.val + m)).toNat
        = 64 + (16 * (kk.val / 2) + 2 * m + kk.val % 2) from by
      unfold fwd2Idx; omega]

open Kopis.CrtZeta in
theorem psiFull_fwd1 (SECOND : Bool) (q : ℕ) (Zb : ℤ) (Rinv : ZMod q)
    (hz : ∀ k < 256, |((zetasOf SECOND).val[k]!).val| ≤ Zb)
    (hinv : (2 ^ 16 : ℤ) ∣ ((qinvOf SECOND).val * (q : ℤ) - 1))
    (kk : Usize) (hkk : kk.val < 16) :
    ∃ z zq : Vec128, backend.neon.ntt.fwd1 SECOND kk = ok (z, zq) ∧ PsiOk z zq (q : ℤ) Zb ∧
      ∀ m < 8, laneZ q z m * Rinv
        = zetaQ (zetasOf SECOND) Rinv (128 + (32 * (kk.val / 4) + 4 * m + kk.val % 4)) := by
  obtain ⟨r, hr, hp⟩ := WP.spec_imp_exists (fwd1_spec SECOND kk (by scalar_tac))
  refine ⟨r.1, r.2, by rw [hr], ⟨fun i hi => ?_, fun i hi => ?_⟩, fun m hm => ?_⟩
  · rw [(hp i hi).1]
    unfold tblZ
    split
    · rw [abs_neg]; exact hz _ (by unfold fwd1Idx; omega)
    · exact hz _ (by unfold fwd1Idx; omega)
  · rw [(hp i hi).1, (hp i hi).2]
    exact tblZq_mont _ _ _ hinv
  · unfold laneZ zetaQ zint
    rw [(hp m hm).1]
    simp only [tblZ, Bool.false_eq_true, if_false]
    rw [show (fwd1Idx (8 * kk.val + m)).toNat
        = 128 + (32 * (kk.val / 4) + 4 * m + kk.val % 4) from by
      unfold fwd1Idx; omega]

/-! ## The forward transform at the two primes

`Rinv` is `900` at `q₁` and `1764` at `q₂` — the same constants `Kopis/Neon/NttZeta.lean` feeds
`zetaQ`, which is what makes the ψ the code loads and the ψ the algebra names the same function.
-/

open Kopis.CrtZeta in
/-- **The forward transform on the first prime, as residues.** -/
theorem ntt_block_val_q1 (b : Array I16 256#usize) (f : ℕ → ZMod 7681)
    (hb : BlockBnd b 3840) (hf : ∀ c < 256, posZ 7681 b c = f c) :
    backend.neon.ntt.ntt_block false b
      ⦃ (r : Array I16 256#usize) =>
          BlockBnd r 3840 ∧ ∀ c < 256, posZ 7681 r c = fwdAll 7681 zeta1 f c ⦄ := by
  obtain ⟨s0, s1, s2, -, -⟩ := growth_q1
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
  have hzt : ∀ kk : Usize, kk.val < 256 → ∃ zi zqi : I16,
      backend.crt.zeta false kk = ok zi ∧ backend.crt.zeta_q false kk = ok zqi ∧
      |zi.val| ≤ 3840 ∧ (2 ^ 16 : ℤ) ∣ (zqi.val * ((7681 : ℕ) : ℤ) - zi.val) ∧
      ((zi.val : ℤ) : ZMod 7681) * (900 : ZMod 7681) = zeta1 kk.val := by
    intro kk hkk
    obtain ⟨zi, zqi, h1, h2, h3, h4, h5⟩ := zeta_table_ok_q1 kk hkk
    refine ⟨zi, zqi, h1, h2, h3, by simpa using h4, ?_⟩
    unfold zeta1 zetaQ zint
    rw [h5]
  apply WP.spec_mono (ntt_block_val false b 7681 3840 17474 7906 12210 16766 7906 12210 16766
    3840 7906 12210 (900 : ZMod 7681) zeta1 f backend.crt.Q1 backend.crt.Q1_BARRETT_M 1024#i16
    (by decide)
    (by simp only [backend.crt.q, Bool.false_eq_true, if_false]) (by rw [q1_val]; norm_num)
    (by simp only [backend.crt.barrett_m, Bool.false_eq_true, if_false]) q1_m_val
    round_const (by decide)
    (by norm_num) (by norm_num) (by decide) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
    hzt
    (fun kk hkk => by
      obtain ⟨z, zq, he, hp, hv⟩ := psiFull_fwd4 false 7681 3840 (900 : ZMod 7681) hzc hinv kk hkk
      rw [hzo] at hv
      exact ⟨z, zq, he, hp, hv⟩)
    (fun kk hkk => by
      obtain ⟨z, zq, he, hp, hv⟩ := psiFull_fwd2 false 7681 3840 (900 : ZMod 7681) hzc hinv kk hkk
      rw [hzo] at hv
      exact ⟨z, zq, he, hp, hv⟩)
    (fun kk hkk => by
      obtain ⟨z, zq, he, hp, hv⟩ := psiFull_fwd1 false 7681 3840 (900 : ZMod 7681) hzc hinv kk hkk
      rw [hzo] at hv
      exact ⟨z, zq, he, hp, hv⟩)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)
    (by simpa using s0) (by simpa using s1) (by simpa using s2)
    (by simpa using s0) (by simpa using s1)
    (by simpa using s2) (by simpa using s0) (by simpa using s1)
    (by simpa using hb) hf)
  rintro r ⟨h1, h2⟩
  exact ⟨by simpa using h1, h2⟩

open Kopis.CrtZeta in
/-- **The forward transform on the second prime, as residues.** -/
theorem ntt_block_val_q2 (b : Array I16 256#usize) (f : ℕ → ZMod 10753)
    (hb : BlockBnd b 5376) (hf : ∀ c < 256, posZ 10753 b c = f c) :
    backend.neon.ntt.ntt_block true b
      ⦃ (r : Array I16 256#usize) =>
          BlockBnd r 5376 ∧ ∀ c < 256, posZ 10753 r c = fwdAll 10753 zeta2 f c ⦄ := by
  obtain ⟨s0, s1, s2, -, -⟩ := growth_q2
  have hzo : zetasOf true = backend.crt.ZETAS_Q2 := by simp only [zetasOf, if_true]
  have hzc : ∀ k < 256, |((zetasOf true).val[k]!).val| ≤ 5376 := by
    intro k hk
    rw [hzo]
    exact zetas_q2_centred_idx k hk
  have hinv : (2 ^ 16 : ℤ) ∣ ((qinvOf true).val * ((10753 : ℕ) : ℤ) - 1) := by
    simp only [qinvOf, if_true]
    rw [show ((10753 : ℕ) : ℤ) = backend.crt.Q2.val from by rw [q2_val]; norm_num]
    exact q2_inv_unit
  have hzt : ∀ kk : Usize, kk.val < 256 → ∃ zi zqi : I16,
      backend.crt.zeta true kk = ok zi ∧ backend.crt.zeta_q true kk = ok zqi ∧
      |zi.val| ≤ 5376 ∧ (2 ^ 16 : ℤ) ∣ (zqi.val * ((10753 : ℕ) : ℤ) - zi.val) ∧
      ((zi.val : ℤ) : ZMod 10753) * (1764 : ZMod 10753) = zeta2 kk.val := by
    intro kk hkk
    obtain ⟨zi, zqi, h1, h2, h3, h4, h5⟩ := zeta_table_ok_q2 kk hkk
    refine ⟨zi, zqi, h1, h2, h3, by simpa using h4, ?_⟩
    unfold zeta2 zetaQ zint
    rw [h5]
  apply WP.spec_mono (ntt_block_val true b 10753 5376 12482 11194 17489 24301 11194 17489 24301
    5376 11194 17489 (1764 : ZMod 10753) zeta2 f backend.crt.Q2 backend.crt.Q2_BARRETT_M
    1024#i16
    (by decide)
    (by simp only [backend.crt.q, if_true]) (by rw [q2_val]; norm_num)
    (by simp only [backend.crt.barrett_m, if_true]) q2_m_val
    round_const (by decide)
    (by norm_num) (by norm_num) (by decide) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
    hzt
    (fun kk hkk => by
      obtain ⟨z, zq, he, hp, hv⟩ :=
        psiFull_fwd4 true 10753 5376 (1764 : ZMod 10753) hzc hinv kk hkk
      rw [hzo] at hv
      exact ⟨z, zq, he, hp, hv⟩)
    (fun kk hkk => by
      obtain ⟨z, zq, he, hp, hv⟩ :=
        psiFull_fwd2 true 10753 5376 (1764 : ZMod 10753) hzc hinv kk hkk
      rw [hzo] at hv
      exact ⟨z, zq, he, hp, hv⟩)
    (fun kk hkk => by
      obtain ⟨z, zq, he, hp, hv⟩ :=
        psiFull_fwd1 true 10753 5376 (1764 : ZMod 10753) hzc hinv kk hkk
      rw [hzo] at hv
      exact ⟨z, zq, he, hp, hv⟩)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)
    (by simpa using s0) (by simpa using s1) (by simpa using s2)
    (by simpa using s0) (by simpa using s1)
    (by simpa using s2) (by simpa using s0) (by simpa using s1)
    (by simpa using hb) hf)
  rintro r ⟨h1, h2⟩
  exact ⟨by simpa using h1, h2⟩

/-! ## …and the leaf state

Eight `State_ct` steps, one per layer, taking the CRT invariant from the root
(`State ψ 1 256 1 f f`) to the leaf (`State ψ 256 1 1 f (fwdAll q ψ f)`).  `ctLvl_hbut` is the
bridge at each step, so nothing here mentions the code. -/

open Kopis.CrtScheme.NttAlg in
theorem fwdAll_State {q : ℕ} (ψ : ℕ → ZMod q)
    (hsq : ∀ k, 1 ≤ k → k < 256 → ψ k ^ 2 = cst ψ k) (f : ℕ → ZMod q) :
    State ψ 256 1 1 f (fwdAll q ψ f) := by
  have h0 : State ψ 1 256 1 f f := State_root_intro (fun r _ => by ring)
  have h1 : State ψ 2 128 1 f (ctLvl q ψ 1 128 f) :=
    State_ct hsq (by norm_num) (by norm_num) h0 (ctLvl_hbut q ψ 1 128 f (by norm_num))
  have h2 : State ψ 4 64 1 f (ctLvl q ψ 2 64 (ctLvl q ψ 1 128 f)) :=
    State_ct hsq (by norm_num) (by norm_num) h1 (ctLvl_hbut q ψ 2 64 _ (by norm_num))
  have h3 : State ψ 8 32 1 f (ctLvl q ψ 4 32 (ctLvl q ψ 2 64 (ctLvl q ψ 1 128 f))) :=
    State_ct hsq (by norm_num) (by norm_num) h2 (ctLvl_hbut q ψ 4 32 _ (by norm_num))
  have h4 : State ψ 16 16 1 f
      (ctLvl q ψ 8 16 (ctLvl q ψ 4 32 (ctLvl q ψ 2 64 (ctLvl q ψ 1 128 f)))) :=
    State_ct hsq (by norm_num) (by norm_num) h3 (ctLvl_hbut q ψ 8 16 _ (by norm_num))
  have h5 : State ψ 32 8 1 f (fwdH q ψ f) :=
    State_ct hsq (by norm_num) (by norm_num) h4 (ctLvl_hbut q ψ 16 8 _ (by norm_num))
  have h6 : State ψ 64 4 1 f (ctLvl q ψ 32 4 (fwdH q ψ f)) :=
    State_ct hsq (by norm_num) (by norm_num) h5 (ctLvl_hbut q ψ 32 4 _ (by norm_num))
  have h7 : State ψ 128 2 1 f (ctLvl q ψ 64 2 (ctLvl q ψ 32 4 (fwdH q ψ f))) :=
    State_ct hsq (by norm_num) (by norm_num) h6 (ctLvl_hbut q ψ 64 2 _ (by norm_num))
  exact State_ct hsq (by norm_num) (by norm_num) h7 (ctLvl_hbut q ψ 128 1 _ (by norm_num))

open Kopis.CrtScheme.NttAlg in
/-- **The forward transform reaches the leaf state, at `q₁`.** -/
theorem ntt_block_State_q1 (b : Array I16 256#usize) (f : ℕ → ZMod 7681)
    (hb : BlockBnd b 3840) (hf : ∀ c < 256, posZ 7681 b c = f c) :
    backend.neon.ntt.ntt_block false b
      ⦃ (r : Array I16 256#usize) =>
          BlockBnd r 3840 ∧ (∀ c < 256, posZ 7681 r c = fwdAll 7681 zeta1 f c) ∧
          State zeta1 256 1 1 f (fwdAll 7681 zeta1 f) ⦄ := by
  apply WP.spec_mono (ntt_block_val_q1 b f hb hf)
  exact fun r hr => ⟨hr.1, hr.2, fwdAll_State zeta1 zeta1_sq f⟩

open Kopis.CrtScheme.NttAlg in
/-- **The forward transform reaches the leaf state, at `q₂`.** -/
theorem ntt_block_State_q2 (b : Array I16 256#usize) (f : ℕ → ZMod 10753)
    (hb : BlockBnd b 5376) (hf : ∀ c < 256, posZ 10753 b c = f c) :
    backend.neon.ntt.ntt_block true b
      ⦃ (r : Array I16 256#usize) =>
          BlockBnd r 5376 ∧ (∀ c < 256, posZ 10753 r c = fwdAll 10753 zeta2 f c) ∧
          State zeta2 256 1 1 f (fwdAll 10753 zeta2 f) ⦄ := by
  apply WP.spec_mono (ntt_block_val_q2 b f hb hf)
  exact fun r hr => ⟨hr.1, hr.2, fwdAll_State zeta2 zeta2_sq f⟩

end Kopis.Neon
