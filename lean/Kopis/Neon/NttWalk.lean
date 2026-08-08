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
else is untouched.

Coefficients are numbered inside the window, so window position `c` is array position
`8·base + c`; the bound hypothesis stays in absolute positions, because that is the shape
`Kopis/Neon/NttLevel.lean` proves. -/
theorem ntt_inner_val {N : Usize} (b : Array I16 N) (base : Usize) (qv z zq : Vec128)
    (q : ℕ) (Zb B Bt : ℤ)
    (Rinv ψ : ZMod q) (hR : ((2 ^ 16 : ℤ) : ZMod q) * Rinv = 1)
    (hψ : ∀ m < 8, laneZ q z m * Rinv = ψ)
    (hQ : ∀ i < 8, (lane16 qv i).toInt = (q : ℤ)) (hQpos : 0 < (q : ℤ)) (hQlt : (q : ℤ) ≤ 2 ^ 14)
    (hz : ∀ i < 8, |(lane16 z i).toInt| ≤ Zb) (hZb : Zb ≤ 2 ^ 14)
    (hzq : ∀ i < 8, (2 ^ 16 : ℤ) ∣ ((lane16 zq i).toInt * (q : ℤ) - (lane16 z i).toInt))
    (hB0 : 0 ≤ B) (hBZ : B * Zb < 2 ^ 15 * (q : ℤ))
    (hBt : B * Zb + 2 ^ 15 * (q : ℤ) ≤ 2 ^ 16 * Bt) (hfit : B + Bt ≤ 32767)
    (hN : 8 * base.val + 256 ≤ N.val)
    (half start i : Usize) (hhalf : 1 ≤ half.val)
    (hrange : start.val + 2 * half.val ≤ 32) (hstart : start.val ≤ i.val)
    (hb : ∀ p < N.val, pendingAt base.val start.val half.val i.val p →
      |(b.val[p]!).val| ≤ B) :
    backend.neon.ntt.ntt_block_loop0_loop0_loop0 b base qv half start z zq i
      ⦃ (r : Array I16 N) => ∀ c < 256,
          if 8 * i.val ≤ c ∧ c < 8 * (start.val + half.val) then
            posZ q r (8 * base.val + c)
              = posZ q b (8 * base.val + c) + ψ * posZ q b (8 * base.val + (c + 8 * half.val))
          else if 8 * (i.val + half.val) ≤ c ∧ c < 8 * (start.val + 2 * half.val) then
            posZ q r (8 * base.val + c)
              = posZ q b (8 * base.val + (c - 8 * half.val)) - ψ * posZ q b (8 * base.val + c)
          else posZ q r (8 * base.val + c) = posZ q b (8 * base.val + c) ⦄ := by
  have hNmax : N.val ≤ Usize.max := by scalar_tac
  have hbig : 256 ≤ Usize.max := by omega
  unfold backend.neon.ntt.ntt_block_loop0_loop0_loop0
  let* ⟨ i1, hi1 ⟩ ← Std.Usize.add_spec (x := start) (y := half) (by scalar_tac)
  by_cases hlt : i < i1
  · rw [if_pos hlt]
    have hiv : i.val < start.val + half.val := by scalar_tac
    let* ⟨ i2, hi2 ⟩ ← Std.Usize.add_spec (x := base) (y := i) (by omega)
    have hi2v : i2.val = base.val + i.val := by scalar_tac
    obtain ⟨lo, hlo, hlol⟩ := load_i16_gen b i2 (by omega)
    rw [hlo, bind_tc_ok]
    let* ⟨ i3, hi3 ⟩ ← Std.Usize.add_spec (x := i2) (y := half) (by omega)
    have hi3v : i3.val = base.val + i.val + half.val := by scalar_tac
    obtain ⟨hv, hhi, hhil⟩ := load_i16_gen b i3 (by omega)
    rw [hhi, bind_tc_ok]
    have hlob : VecBnd lo B := by
      intro k hk
      rw [hlol k hk, hi2v]
      exact hb _ (by omega) ⟨by omega, by omega, Or.inl ⟨by omega, by omega⟩⟩
    have hhib : VecBnd hv B := by
      intro k hk
      rw [hhil k hk, hi3v]
      exact hb _ (by omega) ⟨by omega, by omega, Or.inr ⟨by omega, by omega⟩⟩
    have hloZ : ∀ m < 8, laneZ q lo m = posZ q b (8 * base.val + (8 * i.val + m)) := by
      intro m hm
      unfold laneZ posZ
      rw [hlol m hm, show 8 * i2.val + m = 8 * base.val + (8 * i.val + m) from by omega]
    have hhvZ : ∀ m < 8, laneZ q hv m
        = posZ q b (8 * base.val + (8 * (i.val + half.val) + m)) := by
      intro m hm
      unfold laneZ posZ
      rw [hhil m hm,
        show 8 * i3.val + m = 8 * base.val + (8 * (i.val + half.val) + m) from by omega]
    apply WP.spec_bind (ct_butterfly_val lo hv z zq qv q Zb B Bt Rinv hR hQ hQpos hQlt hz hZb
      hzq hlob hhib hB0 hBZ hBt hfit)
    rintro ⟨lo1, hi1'⟩ hval
    show (do let b1 ← backend.neon.intrinsics.store_i16 b i2 lo1
             let i4 ← i2 + half
             let b2 ← backend.neon.intrinsics.store_i16 b1 i4 hi1'
             let i5 ← i + 1#usize
             backend.neon.ntt.ntt_block_loop0_loop0_loop0 b2 base qv half start z zq i5)
        ⦃ (r : Array I16 N) => ∀ c < 256,
            if 8 * i.val ≤ c ∧ c < 8 * (start.val + half.val) then
              posZ q r (8 * base.val + c)
                = posZ q b (8 * base.val + c) + ψ * posZ q b (8 * base.val + (c + 8 * half.val))
            else if 8 * (i.val + half.val) ≤ c ∧ c < 8 * (start.val + 2 * half.val) then
              posZ q r (8 * base.val + c)
                = posZ q b (8 * base.val + (c - 8 * half.val)) - ψ * posZ q b (8 * base.val + c)
            else posZ q r (8 * base.val + c) = posZ q b (8 * base.val + c) ⦄
    obtain ⟨b1, hb1, hb1v⟩ := store_i16_gen b i2 lo1 (by omega)
    rw [hb1, bind_tc_ok]
    let* ⟨ i4, hi4 ⟩ ← Std.Usize.add_spec (x := i2) (y := half) (by omega)
    have hi4v : i4.val = base.val + i.val + half.val := by scalar_tac
    obtain ⟨b2, hb2, hb2v⟩ := store_i16_gen b1 i4 hi1' (by omega)
    rw [hb2, bind_tc_ok]
    let* ⟨ i5, hi5 ⟩ ← Std.Usize.add_spec (x := i) (y := 1#usize) (by scalar_tac)
    have hi5v : i5.val = i.val + 1 := by scalar_tac
    have hb2all : ∀ c < 256, (b2.val[8 * base.val + c]!).val =
        if 8 * i.val ≤ c ∧ c < 8 * i.val + 8 then (lane16 lo1 (c - 8 * i.val)).toInt
        else if 8 * i.val + 8 * half.val ≤ c ∧ c < 8 * i.val + 8 * half.val + 8 then
          (lane16 hi1' (c - 8 * i.val - 8 * half.val)).toInt
        else (b.val[8 * base.val + c]!).val := by
      intro c hc
      rw [hb2v (8 * base.val + c) (by omega), hb1v (8 * base.val + c) (by omega)]
      by_cases h2 : 8 * i.val + 8 * half.val ≤ c ∧ c < 8 * i.val + 8 * half.val + 8
      · rw [if_pos (show 8 * i4.val ≤ 8 * base.val + c ∧ 8 * base.val + c < 8 * i4.val + 8
              by omega),
          if_neg (show ¬(8 * i.val ≤ c ∧ c < 8 * i.val + 8) by omega), if_pos h2,
          show 8 * base.val + c - 8 * i4.val = c - 8 * i.val - 8 * half.val from by omega]
      · rw [if_neg (show ¬(8 * i4.val ≤ 8 * base.val + c ∧ 8 * base.val + c < 8 * i4.val + 8)
              by omega)]
        by_cases h1 : 8 * i.val ≤ c ∧ c < 8 * i.val + 8
        · rw [if_pos (show 8 * i2.val ≤ 8 * base.val + c ∧ 8 * base.val + c < 8 * i2.val + 8
                by omega), if_pos h1,
            show 8 * base.val + c - 8 * i2.val = c - 8 * i.val from by omega]
        · rw [if_neg (show ¬(8 * i2.val ≤ 8 * base.val + c ∧ 8 * base.val + c < 8 * i2.val + 8)
                by omega), if_neg h1, if_neg h2]
    have hb2Z : ∀ c < 256, posZ q b2 (8 * base.val + c) =
        if 8 * i.val ≤ c ∧ c < 8 * i.val + 8 then laneZ q lo1 (c - 8 * i.val)
        else if 8 * i.val + 8 * half.val ≤ c ∧ c < 8 * i.val + 8 * half.val + 8 then
          laneZ q hi1' (c - 8 * i.val - 8 * half.val)
        else posZ q b (8 * base.val + c) := by
      intro c hc
      unfold posZ laneZ
      rw [hb2all c hc]
      split
      · rfl
      · split <;> rfl
    apply WP.spec_mono (ntt_inner_val b2 base qv z zq q Zb B Bt Rinv ψ hR hψ hQ hQpos hQlt hz hZb
      hzq hB0 hBZ hBt hfit hN half start i5 hhalf hrange (by omega) (by
        intro p hp hpend
        rw [hb2v p hp, hb1v p hp,
          if_neg (by unfold pendingAt pending at hpend; omega),
          if_neg (by unfold pendingAt pending at hpend; omega)]
        exact hb p hp (by unfold pendingAt pending at hpend ⊢; omega)))
    intro r hr c hc
    have hrc := hr c hc
    by_cases hL : 8 * i.val ≤ c ∧ c < 8 * (start.val + half.val)
    · rw [if_pos hL]
      by_cases hLv : c < 8 * i.val + 8
      · -- `c` is in the vector this iteration just wrote as the low half
        rw [if_neg (by omega), if_neg (by omega)] at hrc
        rw [hrc, hb2Z c hc, if_pos ⟨hL.1, hLv⟩, (hval (c - 8 * i.val) (by omega)).1,
          hloZ _ (by omega), hhvZ _ (by omega), hψ _ (by omega),
          show 8 * i.val + (c - 8 * i.val) = c from by omega,
          show 8 * (i.val + half.val) + (c - 8 * i.val) = c + 8 * half.val from by omega]
      · rw [if_pos (by omega : 8 * i5.val ≤ c ∧ c < 8 * (start.val + half.val))] at hrc
        rw [hrc, hb2Z c hc, if_neg (by omega), if_neg (by omega),
          hb2Z (c + 8 * half.val) (by omega), if_neg (by omega), if_neg (by omega)]
    · rw [if_neg hL]
      by_cases hH : 8 * (i.val + half.val) ≤ c ∧ c < 8 * (start.val + 2 * half.val)
      · rw [if_pos hH]
        by_cases hHv : c < 8 * (i.val + half.val) + 8
        · -- …and here it is the vector written as the high half
          rw [if_neg (by omega), if_neg (by omega)] at hrc
          rw [hrc, hb2Z c hc, if_neg (by omega), if_pos ⟨by omega, by omega⟩,
            show c - 8 * i.val - 8 * half.val = c - 8 * (i.val + half.val) from by omega,
            (hval (c - 8 * (i.val + half.val)) (by omega)).2, hloZ _ (by omega),
            hhvZ _ (by omega), hψ _ (by omega),
            show 8 * i.val + (c - 8 * (i.val + half.val)) = c - 8 * half.val from by omega,
            show 8 * (i.val + half.val) + (c - 8 * (i.val + half.val)) = c from by omega]
        · rw [if_neg (by omega), if_pos (by omega :
            8 * (i5.val + half.val) ≤ c ∧ c < 8 * (start.val + 2 * half.val))] at hrc
          rw [hrc, hb2Z c hc, if_neg (by omega), if_neg (by omega),
            hb2Z (c - 8 * half.val) (by omega), if_neg (by omega), if_neg (by omega)]
      · rw [if_neg hH]
        rw [if_neg (by omega), if_neg (by omega)] at hrc
        rw [hrc, hb2Z c hc, if_neg (by omega), if_neg (by omega)]
  · rw [if_neg hlt]
    refine (WP.spec_ok _).mpr (fun c hc => ?_)
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

theorem ntt_start_val (SECOND : Bool) {N : Usize} (b : Array I16 N) (base : Usize) (qv : Vec128)
    (q : ℕ) (Zb B Bt : ℤ) (Rinv : ZMod q) (ψ a0 : ℕ → ZMod q) (nb bIdx : ℕ)
    (hR : ((2 ^ 16 : ℤ) : ZMod q) * Rinv = 1)
    (hQ : ∀ i < 8, (lane16 qv i).toInt = (q : ℤ)) (hQpos : 0 < (q : ℤ)) (hQlt : (q : ℤ) ≤ 2 ^ 14)
    (hZb : Zb ≤ 2 ^ 14)
    (hB0 : 0 ≤ B) (hBZ : B * Zb < 2 ^ 15 * (q : ℤ))
    (hBt : B * Zb + 2 ^ 15 * (q : ℤ) ≤ 2 ^ 16 * Bt) (hfit : B + Bt ≤ 32767)
    (hN : 8 * base.val + 256 ≤ N.val)
    (hzeta : ∀ kk : Usize, kk.val < 256 → ∃ zi zqi : I16,
        backend.crt.zeta SECOND kk = ok zi ∧ backend.crt.zeta_q SECOND kk = ok zqi ∧
        |zi.val| ≤ Zb ∧ (2 ^ 16 : ℤ) ∣ (zqi.val * (q : ℤ) - zi.val) ∧
        ((zi.val : ℤ) : ZMod q) * Rinv = ψ kk.val)
    (k half start : Usize) (hhalf : 1 ≤ half.val) (hnb32 : 32 = nb * (2 * half.val))
    (hstartb : start.val = bIdx * (2 * half.val)) (hstart32 : start.val ≤ 32)
    (hkeq : k.val + 1 = nb + bIdx) (hk : k.val + (32 - start.val) ≤ 255)
    (hb : ∀ p < N.val, fromVec base.val start.val p → |(b.val[p]!).val| ≤ B)
    (hva : ∀ c < 256, posZ q b (8 * base.val + c) =
        if c < 8 * start.val then ctLvl q ψ nb (8 * half.val) a0 c else a0 c) :
    backend.neon.ntt.ntt_block_loop0_loop0 SECOND b base qv k half start
      ⦃ (r : Array I16 N × Usize) =>
          (∀ p < N.val, if fromVec base.val start.val p then |(r.1.val[p]!).val| ≤ B + Bt
            else (r.1.val[p]!).val = (b.val[p]!).val) ∧
          (∀ c < 256, posZ q r.1 (8 * base.val + c) = ctLvl q ψ nb (8 * half.val) a0 c) ∧
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
      (ntt_inner_bnd b base qv z zq (q : ℤ) Zb B Bt hQ hQpos hQlt hzlv hZb hzqlv hB0 hBZ hBt hfit
        hN half start start hhalf hfits (le_refl _) (by
          intro p hp hpend
          exact hb p hp (by unfold pendingAt pending at hpend; unfold fromVec; omega)))
      (ntt_inner_val b base qv z zq q Zb B Bt Rinv (ψ (nb + bIdx)) hR hzk hQ hQpos hQlt hzlv hZb
        hzqlv hB0 hBZ hBt hfit hN half start start hhalf hfits (le_refl _) (by
          intro p hp hpend
          exact hb p hp (by unfold pendingAt pending at hpend; unfold fromVec; omega))))
    rintro b1 ⟨hb1, hb1v⟩
    -- what one block leaves behind, as residues
    have hb1all : ∀ c < 256, posZ q b1 (8 * base.val + c) =
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
    apply WP.spec_mono (ntt_start_val SECOND b1 base qv q Zb B Bt Rinv ψ a0 nb (bIdx + 1) hR hQ
      hQpos hQlt hZb hB0 hBZ hBt hfit hN hzeta k1 half start1 hhalf hnb32
      (by rw [hs1v, hstartb]; ring) (by omega) (by omega) (by omega)
      (by
        intro p hp hge
        have h := hb1 p hp
        rw [if_neg (by unfold pendingAt pending; unfold fromVec at hge; omega)] at h
        rw [h]
        exact hb p hp (by unfold fromVec at hge ⊢; omega))
      (by
        intro c hc
        rw [hb1all c hc, hs1v]))
    rintro ⟨r, kk⟩ ⟨hr1, hr2, hr3⟩
    refine ⟨fun p hp => ?_, hr2, hr3⟩
    have h1 := hr1 p hp
    have h2 := hb1 p hp
    by_cases hge : fromVec base.val start.val p
    · rw [if_pos hge]
      by_cases hge1 : fromVec base.val start1.val p
      · rw [if_pos hge1] at h1
        exact h1
      · rw [if_neg hge1] at h1
        rw [if_pos (by unfold pendingAt pending; unfold fromVec at hge hge1; omega)] at h2
        rw [h1]
        exact h2
    · rw [if_neg hge]
      rw [if_neg (by unfold fromVec at hge ⊢; omega)] at h1
      rw [if_neg (by unfold pendingAt pending; unfold fromVec at hge; omega)] at h2
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
    · rw [if_neg (by unfold fromVec; omega)]
    · rw [hva c hc, if_pos (by omega)]

termination_by 32 - start.val
decreasing_by scalar_decr_tac

/-! ## The two whole-vector levels

`half = 16` and `half = 8`, with `m' = 8·half` and `nb = 32 / (2·half)`.  There is no re-centring
pass among them any more: both of the forward transform's reductions happen inside the group
loop, so the whole-vector half of `ntt_block` is two Cooley-Tukey layers and nothing else.

The `k` counter needs no invariant of its own: `ntt_start_val` *reports* it as `nb + nb`, so each
level's starting `k` is fixed by the level before it — `0` and then `1`. -/

/-- The two whole-vector levels, as a function of the input view. -/
noncomputable def fwdH (q : ℕ) (ψ f : ℕ → ZMod q) : ℕ → ZMod q :=
  ctLvl q ψ 2 64 (ctLvl q ψ 1 128 f)

theorem ntt_horizontal_val (SECOND : Bool) {N : Usize} (b : Array I16 N) (base : Usize)
    (qv : Vec128) (q : ℕ) (Zb A0 A1 A2 : ℤ) (Rinv : ZMod q) (ψ f : ℕ → ZMod q)
    (hR : ((2 ^ 16 : ℤ) : ZMod q) * Rinv = 1)
    (hQ : ∀ i < 8, (lane16 qv i).toInt = (q : ℤ)) (hQpos : 0 < (q : ℤ))
    (hQ14 : (q : ℤ) < 2 ^ 14) (hZb : Zb ≤ 2 ^ 14) (hN : 8 * base.val + 256 ≤ N.val)
    (hzeta : ∀ kk : Usize, kk.val < 256 → ∃ zi zqi : I16,
        backend.crt.zeta SECOND kk = ok zi ∧ backend.crt.zeta_q SECOND kk = ok zqi ∧
        |zi.val| ≤ Zb ∧ (2 ^ 16 : ℤ) ∣ (zqi.val * (q : ℤ) - zi.val) ∧
        ((zi.val : ℤ) : ZMod q) * Rinv = ψ kk.val)
    (hA0 : 0 ≤ A0) (hA1 : 0 ≤ A1)
    (hs0 : LevelStep (q : ℤ) Zb A0 (A1 - A0)) (hs1 : LevelStep (q : ℤ) Zb A1 (A2 - A1))
    (hb : ∀ p < N.val, fromVec base.val 0 p → |(b.val[p]!).val| ≤ A0)
    (hf : ∀ c < 256, posZ q b (8 * base.val + c) = f c) :
    backend.neon.ntt.ntt_block_loop0 SECOND b base qv 0#usize 16#usize
      ⦃ (r : Array I16 N) =>
          (∀ p < N.val, if fromVec base.val 0 p then |(r.val[p]!).val| ≤ A2
            else (r.val[p]!).val = (b.val[p]!).val) ∧
          (∀ c < 256, posZ q r (8 * base.val + c) = fwdH q ψ f c) ⦄ := by
  have hQ14' : (q : ℤ) ≤ 2 ^ 14 := by omega

  -- level 0: half = 16, nb = 1, m' = 128
  unfold backend.neon.ntt.ntt_block_loop0
  rw [if_pos (show (8#usize : Usize) ≤ 16#usize by decide)]
  apply WP.spec_bind (ntt_start_val SECOND b base qv q Zb A0 (A1 - A0) Rinv ψ f 1 0 hR hQ hQpos
    hQ14' hZb (by omega) hs0.1 hs0.2.1 hs0.2.2 hN hzeta 0#usize 16#usize 0#usize (by scalar_tac)
    (by scalar_tac) (by scalar_tac) (by scalar_tac) (by scalar_tac) (by scalar_tac) hb
    (by intro c hc; rw [hf c hc, if_neg (by scalar_tac)]))
  rintro ⟨b1, k1⟩ ⟨hsb1, hvb1, hkb1⟩
  have hsb1' : ∀ p < N.val, if fromVec base.val 0 p then |(b1.val[p]!).val| ≤ A0 + (A1 - A0)
      else (b1.val[p]!).val = (b.val[p]!).val := hsb1
  have hvb1n : ∀ c < 256, posZ q b1 (8 * base.val + c) = ctLvl q ψ 1 128 f c := by
    intro c hc
    have h := hvb1 c hc
    rwa [show (8 : ℕ) * (16#usize : Usize).val = 128 from by scalar_tac] at h
  show (do let half1 ← (16#usize : Usize) / 2#usize
           backend.neon.ntt.ntt_block_loop0 SECOND b1 base qv k1 half1)
      ⦃ (r : Array I16 N) =>
          (∀ p < N.val, if fromVec base.val 0 p then |(r.val[p]!).val| ≤ A2
            else (r.val[p]!).val = (b.val[p]!).val) ∧
          (∀ c < 256, posZ q r (8 * base.val + c) = fwdH q ψ f c) ⦄
  rw [show (16#usize : Usize) / 2#usize = ok 8#usize from by rfl, bind_tc_ok]

  -- level 1: half = 8, nb = 2, m' = 64
  unfold backend.neon.ntt.ntt_block_loop0
  rw [if_pos (show (8#usize : Usize) ≤ 8#usize by decide)]
  apply WP.spec_bind (ntt_start_val SECOND b1 base qv q Zb A1 (A2 - A1) Rinv ψ
    (ctLvl q ψ 1 128 f) 2 0 hR hQ hQpos hQ14' hZb (by omega) hs1.1 hs1.2.1 hs1.2.2 hN hzeta
    k1 8#usize 0#usize (by scalar_tac) (by scalar_tac) (by scalar_tac) (by scalar_tac)
    (by omega) (by scalar_tac)
    (by
      intro p hp hin
      have h := hsb1' p hp
      rw [if_pos (show fromVec base.val 0 p from hin)] at h
      linarith)
    (by intro c hc; rw [hvb1n c hc, if_neg (by scalar_tac)]))
  rintro ⟨b2, k2⟩ ⟨hsb2, hvb2, hkb2⟩
  have hsb2' : ∀ p < N.val, if fromVec base.val 0 p then |(b2.val[p]!).val| ≤ A1 + (A2 - A1)
      else (b2.val[p]!).val = (b1.val[p]!).val := hsb2
  have hvb2n : ∀ c < 256, posZ q b2 (8 * base.val + c) = fwdH q ψ f c := by
    intro c hc
    have h := hvb2 c hc
    rwa [show (8 : ℕ) * (8#usize : Usize).val = 64 from by scalar_tac] at h
  show (do let half1 ← (8#usize : Usize) / 2#usize
           backend.neon.ntt.ntt_block_loop0 SECOND b2 base qv k2 half1)
      ⦃ (r : Array I16 N) =>
          (∀ p < N.val, if fromVec base.val 0 p then |(r.val[p]!).val| ≤ A2
            else (r.val[p]!).val = (b.val[p]!).val) ∧
          (∀ c < 256, posZ q r (8 * base.val + c) = fwdH q ψ f c) ⦄
  rw [show (8#usize : Usize) / 2#usize = ok 4#usize from by rfl, bind_tc_ok]

  -- half = 4: the loop stops
  unfold backend.neon.ntt.ntt_block_loop0
  rw [if_neg (by decide)]
  refine (WP.spec_ok _).mpr ⟨fun p hp => ?_, hvb2n⟩
  have h2 := hsb2' p hp
  have h1 := hsb1' p hp
  by_cases hin : fromVec base.val 0 p
  · rw [if_pos hin] at h2 ⊢
    linarith
  · rw [if_neg hin] at h1 h2 ⊢
    rw [h2, h1]

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
    backend.neon.ntt.ntt_block_loop1_loop5_loop0 iter qv v h z zq
      ⦃ (r : Array Vec128 8#usize) => ∀ j (hj : j < 8), ∀ m < 8,
          if 4 * h.val + iter.start.val ≤ j ∧ j < 4 * h.val + 2 then
            laneZ q (vAt r j hj) m = laneZ q (vAt v (4 * (j / 4) + j % 2) (by omega)) m
              + ψm m * laneZ q (vAt v (4 * (j / 4) + j % 2 + 2) (by omega)) m
          else if 4 * h.val + 2 + iter.start.val ≤ j ∧ j < 4 * h.val + 4 then
            laneZ q (vAt r j hj) m = laneZ q (vAt v (4 * (j / 4) + j % 2) (by omega)) m
              - ψm m * laneZ q (vAt v (4 * (j / 4) + j % 2 + 2) (by omega)) m
          else laneZ q (vAt r j hj) m = laneZ q (vAt v j hj) m ⦄ := by
  unfold backend.neon.ntt.ntt_block_loop1_loop5_loop0
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
             backend.neon.ntt.ntt_block_loop1_loop5_loop0 iter1 qv a h z zq)
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
    backend.neon.ntt.ntt_block_loop1_loop6 SECOND iter qv g v
      ⦃ (r : Array Vec128 8#usize) => ∀ j (hj : j < 8), ∀ m < 8,
          if 2 * iter.start.val ≤ j then
            (if j % 2 = 0 then
              laneZ q (vAt r j hj) m = laneZ q (vAt v (2 * (j / 2)) (by omega)) m
                + ψm (4 * g.val + j / 2) m * laneZ q (vAt v (2 * (j / 2) + 1) (by omega)) m
            else
              laneZ q (vAt r j hj) m = laneZ q (vAt v (2 * (j / 2)) (by omega)) m
                - ψm (4 * g.val + j / 2) m * laneZ q (vAt v (2 * (j / 2) + 1) (by omega)) m)
          else laneZ q (vAt r j hj) m = laneZ q (vAt v j hj) m ⦄ := by
  unfold backend.neon.ntt.ntt_block_loop1_loop6
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
             backend.neon.ntt.ntt_block_loop1_loop6 SECOND iter1 qv g a)
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
    backend.neon.ntt.ntt_block_loop1_loop5 SECOND iter qv g v
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
  unfold backend.neon.ntt.ntt_block_loop1_loop5
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

`ntt_block_loop1_loop2` Barrett-reduces every vector of the group.  That moves the representative
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
    backend.neon.ntt.ntt_block_loop1_loop2 iter back qv bm round
      ⦃ (r : core.slice.iter.IterMut Vec128 ×
             (core.slice.iter.IterMut Vec128 → core.slice.iter.IterMut Vec128)) =>
          ∀ (im : core.slice.iter.IterMut Vec128), im.slice.val.length = 8 →
            ∀ (j : ℕ) (hj : j < (r.2 im).slice.val.length) (m : ℕ), m < 8 →
              laneZ q (sAt (r.2 im).slice j hj) m = val0 j m ⦄ := by
  unfold backend.neon.ntt.ntt_block_loop1_loop2
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

/-! ## The three layers the group carries *before* the transpose, in coefficient coordinates

Levels 2, 3 and 4 run while the group is still in coefficient order, so lane `m` of vector `j` is
coefficient `64g + 8j + m`, and pairing vectors `d` apart is a Cooley-Tukey layer at coefficient
stride `8d`.  These three read `ctLvl` at that coefficient and say what it is in terms of `j`
alone; the block index falls out as `c / (2m')`, and it is exactly the ζ index the Rust computes:

* level 2 (`m' = 32`): block `g`,           ζ index `4 + g`;
* level 3 (`m' = 16`): block `2g + j/4`,    ζ index `8 + 2g + j/4`;
* level 4 (`m' = 8`):  block `4g + j/2`,    ζ index `16 + 4g + j/2`.
-/

theorem ctLvl_lvl2 (q : ℕ) (ψ a0 : ℕ → ZMod q) (g j m : ℕ) (hj : j < 8) (hm : m < 8) :
    ctLvl q ψ 4 32 a0 (64 * g + 8 * j + m) =
      if j < 4 then a0 (64 * g + 8 * j + m) + ψ (4 + g) * a0 (64 * g + 8 * j + m + 32)
      else a0 (64 * g + 8 * j + m - 32) - ψ (4 + g) * a0 (64 * g + 8 * j + m) := by
  unfold ctLvl
  rw [show (64 * g + 8 * j + m) % (2 * 32) = 8 * j + m from by omega,
    show (64 * g + 8 * j + m) / (2 * 32) = g from by omega]
  by_cases h : j < 4
  · rw [if_pos (by omega), if_pos h]
  · rw [if_neg (by omega), if_neg h]

theorem ctLvl_lvl3 (q : ℕ) (ψ a0 : ℕ → ZMod q) (g j m : ℕ) (_hj : j < 8) (hm : m < 8) :
    ctLvl q ψ 8 16 a0 (64 * g + 8 * j + m) =
      if j % 4 < 2 then a0 (64 * g + 8 * j + m)
          + ψ (8 + (2 * g + j / 4)) * a0 (64 * g + 8 * j + m + 16)
      else a0 (64 * g + 8 * j + m - 16)
          - ψ (8 + (2 * g + j / 4)) * a0 (64 * g + 8 * j + m) := by
  unfold ctLvl
  rw [show (64 * g + 8 * j + m) % (2 * 16) = (8 * j + m) % 32 from by omega,
    show (64 * g + 8 * j + m) / (2 * 16) = 2 * g + j / 4 from by omega]
  by_cases h : j % 4 < 2
  · rw [if_pos (by omega), if_pos h]
  · rw [if_neg (by omega), if_neg h]

theorem ctLvl_lvl4 (q : ℕ) (ψ a0 : ℕ → ZMod q) (g j m : ℕ) (_hj : j < 8) (hm : m < 8) :
    ctLvl q ψ 16 8 a0 (64 * g + 8 * j + m) =
      if j % 2 = 0 then a0 (64 * g + 8 * j + m)
          + ψ (16 + (4 * g + j / 2)) * a0 (64 * g + 8 * j + m + 8)
      else a0 (64 * g + 8 * j + m - 8)
          - ψ (16 + (4 * g + j / 2)) * a0 (64 * g + 8 * j + m) := by
  unfold ctLvl
  rw [show (64 * g + 8 * j + m) % (2 * 8) = (8 * j + m) % 16 from by omega,
    show (64 * g + 8 * j + m) / (2 * 8) = 4 * g + j / 2 from by omega]
  by_cases h : j % 2 = 0
  · rw [if_pos (by omega), if_pos h]
  · rw [if_neg (by omega), if_neg h]

/-! ## Levels 3 and 4, as residues

Both take a broadcast ζ from the table rather than a per-lane ψ, so the twiddle that appears is
`ψ kk` for the flat index `kk` — the same family `ntt_start_val` uses — rather than a family
indexed by lane. -/

theorem ntt_lvl3_val (SECOND : Bool) (qv : Vec128) (q : ℕ) (Zb B Bt : ℤ) (Rinv : ZMod q)
    (ψ : ℕ → ZMod q) (hR : ((2 ^ 16 : ℤ) : ZMod q) * Rinv = 1)
    (hQ : ∀ i < 8, (lane16 qv i).toInt = (q : ℤ)) (hQpos : 0 < (q : ℤ)) (hQlt : (q : ℤ) ≤ 2 ^ 14)
    (hZb : Zb ≤ 2 ^ 14)
    (hB0 : 0 ≤ B) (hBZ : B * Zb < 2 ^ 15 * (q : ℤ))
    (hBt : B * Zb + 2 ^ 15 * (q : ℤ) ≤ 2 ^ 16 * Bt) (hfit : B + Bt ≤ 32767)
    (hzeta : ∀ kk : Usize, kk.val < 256 → ∃ zi zqi : I16,
        backend.crt.zeta SECOND kk = ok zi ∧ backend.crt.zeta_q SECOND kk = ok zqi ∧
        |zi.val| ≤ Zb ∧ (2 ^ 16 : ℤ) ∣ (zqi.val * (q : ℤ) - zi.val) ∧
        ((zi.val : ℤ) : ZMod q) * Rinv = ψ kk.val)
    (g : Usize) (hg : g.val < 4) (v : Array Vec128 8#usize)
    (iter : core.ops.range.Range Usize) (hend : iter.«end».val = 2)
    (hv : ∀ j (hj : j < 8), 4 * iter.start.val ≤ j → VecBnd (vAt v j hj) B) :
    backend.neon.ntt.ntt_block_loop1_loop1 SECOND iter qv g v
      ⦃ (r : Array Vec128 8#usize) => ∀ j (hj : j < 8), ∀ m < 8,
          if 4 * iter.start.val ≤ j then
            (if j % 4 < 2 then
              laneZ q (vAt r j hj) m = laneZ q (vAt v (4 * (j / 4) + j % 2) (by omega)) m
                + ψ (8 + (2 * g.val + j / 4))
                    * laneZ q (vAt v (4 * (j / 4) + j % 2 + 2) (by omega)) m
            else
              laneZ q (vAt r j hj) m = laneZ q (vAt v (4 * (j / 4) + j % 2) (by omega)) m
                - ψ (8 + (2 * g.val + j / 4))
                    * laneZ q (vAt v (4 * (j / 4) + j % 2 + 2) (by omega)) m)
          else laneZ q (vAt r j hj) m = laneZ q (vAt v j hj) m ⦄ := by
  unfold backend.neon.ntt.ntt_block_loop1_loop1
  by_cases hlt : iter.start.val < iter.«end».val
  · let* ⟨ o, iter1, ho, hstart', hend' ⟩ ← core.iter.range.IteratorRange.next_Usize_some_spec
    rw [ho]
    simp only
    have hh2 : iter.start.val < 2 := by omega
    let* ⟨ i, hi ⟩ ← Std.Usize.mul_spec (x := 2#usize) (y := g) (by scalar_tac)
    let* ⟨ i0, hi0 ⟩ ← Std.Usize.add_spec (x := 8#usize) (y := i) (by scalar_tac)
    let* ⟨ kk, hkk ⟩ ← Std.Usize.add_spec (x := i0) (y := iter.start) (by scalar_tac)
    have hkkv : kk.val = 8 + (2 * g.val + iter.start.val) := by scalar_tac
    obtain ⟨zi, zqi, hzi, hzqi, hzib, hzqib, hzpsi⟩ := hzeta kk (by scalar_tac)
    rw [hzi, bind_tc_ok]
    obtain ⟨z, hz, hzl⟩ := dup_n_s16_spec zi
    rw [hz, bind_tc_ok, hzqi, bind_tc_ok]
    obtain ⟨zq, hzq, hzql⟩ := dup_n_s16_spec zqi
    rw [hzq, bind_tc_ok]
    have hzlv : ∀ i < 8, |(lane16 z i).toInt| ≤ Zb := by
      intro i hi'; rw [hzl i hi']; exact hzib
    have hzqlv : ∀ i < 8, (2 ^ 16 : ℤ) ∣ ((lane16 zq i).toInt * (q : ℤ) - (lane16 z i).toInt) := by
      intro i hi'; rw [hzl i hi', hzql i hi']; exact hzqib
    have hzk : ∀ m < 8, laneZ q z m * Rinv = ψ kk.val := by
      intro m hm
      unfold laneZ
      rw [hzl m hm]
      exact hzpsi
    rw [loop1_loop1_loop0_eq]
    apply WP.spec_bind (WP.spec_both
      (ntt_len2_bnd qv z zq (q : ℤ) Zb B Bt hQ hQpos hQlt hzlv hZb hzqlv hB0 hBZ hBt hfit
        v iter.start hh2 ⟨0#usize, 2#usize⟩ rfl (by
          intro j hj hpend
          exact hv j hj (by unfold pend2 at hpend; scalar_tac)))
      (ntt_len2_val qv z zq q Zb B Bt Rinv (fun _ => ψ kk.val) hR hzk hQ hQpos hQlt
        hzlv hZb hzqlv hB0 hBZ hBt hfit v iter.start hh2 ⟨0#usize, 2#usize⟩ rfl (by
          intro j hj hpend
          exact hv j hj (by unfold pend2 at hpend; scalar_tac))))
    rintro v1 ⟨hv1b, hv1v⟩
    have hz0 : ((⟨0#usize, 2#usize⟩ : core.ops.range.Range Usize)).start.val = 0 := by scalar_tac
    simp only [hz0, Nat.add_zero] at hv1v
    apply WP.spec_mono (ntt_lvl3_val SECOND qv q Zb B Bt Rinv ψ hR hQ hQpos hQlt hZb hB0
      hBZ hBt hfit hzeta g hg v1 iter1 (by rw [hend']; exact hend) (by
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
        have hpsi : ψ kk.val = ψ (8 + (2 * g.val + j / 4)) := by rw [hkkv, hjq]
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

theorem ntt_lvl4_val (SECOND : Bool) (qv : Vec128) (q : ℕ) (Zb B Bt : ℤ) (Rinv : ZMod q)
    (ψ : ℕ → ZMod q) (hR : ((2 ^ 16 : ℤ) : ZMod q) * Rinv = 1)
    (hQ : ∀ i < 8, (lane16 qv i).toInt = (q : ℤ)) (hQpos : 0 < (q : ℤ)) (hQlt : (q : ℤ) ≤ 2 ^ 14)
    (hZb : Zb ≤ 2 ^ 14)
    (hB0 : 0 ≤ B) (hBZ : B * Zb < 2 ^ 15 * (q : ℤ))
    (hBt : B * Zb + 2 ^ 15 * (q : ℤ) ≤ 2 ^ 16 * Bt) (hfit : B + Bt ≤ 32767)
    (hzeta : ∀ kk : Usize, kk.val < 256 → ∃ zi zqi : I16,
        backend.crt.zeta SECOND kk = ok zi ∧ backend.crt.zeta_q SECOND kk = ok zqi ∧
        |zi.val| ≤ Zb ∧ (2 ^ 16 : ℤ) ∣ (zqi.val * (q : ℤ) - zi.val) ∧
        ((zi.val : ℤ) : ZMod q) * Rinv = ψ kk.val)
    (g : Usize) (hg : g.val < 4) (v : Array Vec128 8#usize)
    (iter : core.ops.range.Range Usize) (hend : iter.«end».val = 4)
    (hv : ∀ j (hj : j < 8), pend1 iter.start.val j → VecBnd (vAt v j hj) B) :
    backend.neon.ntt.ntt_block_loop1_loop3 SECOND iter qv g v
      ⦃ (r : Array Vec128 8#usize) => ∀ j (hj : j < 8), ∀ m < 8,
          if 2 * iter.start.val ≤ j then
            (if j % 2 = 0 then
              laneZ q (vAt r j hj) m = laneZ q (vAt v (2 * (j / 2)) (by omega)) m
                + ψ (16 + (4 * g.val + j / 2))
                    * laneZ q (vAt v (2 * (j / 2) + 1) (by omega)) m
            else
              laneZ q (vAt r j hj) m = laneZ q (vAt v (2 * (j / 2)) (by omega)) m
                - ψ (16 + (4 * g.val + j / 2))
                    * laneZ q (vAt v (2 * (j / 2) + 1) (by omega)) m)
          else laneZ q (vAt r j hj) m = laneZ q (vAt v j hj) m ⦄ := by
  unfold backend.neon.ntt.ntt_block_loop1_loop3
  by_cases hlt : iter.start.val < iter.«end».val
  · let* ⟨ o, iter1, ho, hstart', hend' ⟩ ← core.iter.range.IteratorRange.next_Usize_some_spec
    rw [ho]
    simp only
    have hr4 : iter.start.val < 4 := by omega
    let* ⟨ i, hi ⟩ ← Std.Usize.mul_spec (x := 4#usize) (y := g) (by scalar_tac)
    let* ⟨ i0, hi0 ⟩ ← Std.Usize.add_spec (x := 16#usize) (y := i) (by scalar_tac)
    let* ⟨ kk, hkk ⟩ ← Std.Usize.add_spec (x := i0) (y := iter.start) (by scalar_tac)
    have hkkv : kk.val = 16 + (4 * g.val + iter.start.val) := by scalar_tac
    obtain ⟨zi, zqi, hzi, hzqi, hzib, hzqib, hzpsi⟩ := hzeta kk (by scalar_tac)
    rw [hzi, bind_tc_ok]
    obtain ⟨z, hz, hzl⟩ := dup_n_s16_spec zi
    rw [hz, bind_tc_ok, hzqi, bind_tc_ok]
    obtain ⟨zq, hzq, hzql⟩ := dup_n_s16_spec zqi
    rw [hzq, bind_tc_ok]
    have hzlv : ∀ i < 8, |(lane16 z i).toInt| ≤ Zb := by
      intro i hi'; rw [hzl i hi']; exact hzib
    have hzqlv : ∀ i < 8, (2 ^ 16 : ℤ) ∣ ((lane16 zq i).toInt * (q : ℤ) - (lane16 z i).toInt) := by
      intro i hi'; rw [hzl i hi', hzql i hi']; exact hzqib
    have hzk : ∀ m < 8, laneZ q z m * Rinv = ψ kk.val := by
      intro m hm
      unfold laneZ
      rw [hzl m hm]
      exact hzpsi
    let* ⟨ i2, hi2 ⟩ ← Std.Usize.mul_spec (x := 2#usize) (y := iter.start) (by scalar_tac)
    have hi2v : i2.val = 2 * iter.start.val := by scalar_tac
    let* ⟨ lo, hlo ⟩ ← Array.index_usize_spec v i2 (by scalar_tac)
    have hloe : lo = vAt v i2.val (by omega) := by rw [hlo]; rfl
    let* ⟨ i3, hi3 ⟩ ← Std.Usize.add_spec (x := i2) (y := 1#usize) (by scalar_tac)
    have hi3v : i3.val = i2.val + 1 := by scalar_tac
    let* ⟨ hiv, hhi ⟩ ← Array.index_usize_spec v i3 (by scalar_tac)
    have hhie : hiv = vAt v i3.val (by omega) := by rw [hhi]; rfl
    apply WP.spec_bind (WP.spec_both
      (ct_butterfly_spec lo hiv z zq qv (q : ℤ) Zb B Bt hQ hQpos hQlt hzlv hZb hzqlv
        (by rw [hloe]; exact hv _ (by omega) ⟨by omega, by omega⟩)
        (by rw [hhie]; exact hv _ (by omega) ⟨by omega, by omega⟩)
        hB0 hBZ hBt hfit)
      (ct_butterfly_val lo hiv z zq qv q Zb B Bt Rinv hR hQ hQpos hQlt hzlv hZb hzqlv
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
                  + ψ (16 + (4 * g.val + j / 2))
                      * laneZ q (vAt v (2 * (j / 2) + 1) (by omega)) m
              else
                laneZ q (vAt r j hj) m = laneZ q (vAt v (2 * (j / 2)) (by omega)) m
                  - ψ (16 + (4 * g.val + j / 2))
                      * laneZ q (vAt v (2 * (j / 2) + 1) (by omega)) m)
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
    apply WP.spec_mono (ntt_lvl4_val SECOND qv q Zb B Bt Rinv ψ hR hQ hQpos hQlt hZb hB0 hBZ
      hBt hfit hzeta g hg a iter1 (by rw [hend']; exact hend) (by
        intro j hj hpend
        rw [hav j hj, if_neg (by unfold pend1 at hpend; omega),
          if_neg (by unfold pend1 at hpend; omega)]
        exact hv j hj (by unfold pend1 at hpend ⊢; omega)))
    intro r hr j hj m hm
    have hrj := hr j hj m hm
    have hlo1v : laneZ q lo1 m = laneZ q (vAt v i2.val (by omega)) m
        + ψ kk.val * laneZ q (vAt v i3.val (by omega)) m := by
      have hb := (hbutval m hm).1
      rw [hzk m hm, hloe, hhie] at hb
      exact hb
    have hhi1v : laneZ q hi1' m = laneZ q (vAt v i2.val (by omega)) m
        - ψ kk.val * laneZ q (vAt v i3.val (by omega)) m := by
      have hb := (hbutval m hm).2
      rw [hzk m hm, hloe, hhie] at hb
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
            show kk.val = 16 + (4 * g.val + j / 2) from by omega]
        · rw [if_neg hpar, if_pos (by omega), hhi1v,
            vAt_congr v (by omega) (by omega) (show i2.val = 2 * (j / 2) from by omega),
            vAt_congr v (by omega) (by omega) (show i3.val = 2 * (j / 2) + 1 from by omega),
            show kk.val = 16 + (4 * g.val + j / 2) from by omega]
    · rw [if_neg hge]
      rw [if_neg (by omega)] at hrj
      rw [hrj, havZ j hj m hm, if_neg (by omega), if_neg (by omega)]
  · let* ⟨ o, iter1, hnone, _ ⟩ ← core.iter.range.IteratorRange.next_Usize_none_spec
    rw [hnone]
    refine (WP.spec_ok _).mpr (fun j hj m hm => ?_)
    rw [if_neg (by omega)]
termination_by iter.«end».val - iter.start.val
decreasing_by scalar_decr_tac

/-- A transpose swaps the two indices of the group's value table. -/
theorem transpose8_val (v : Array Vec128 8#usize) (q : ℕ) (val : ℕ → ℕ → ZMod q)
    (hv : ∀ j (hj : j < 8), ∀ m < 8, laneZ q (vAt v j hj) m = val j m) :
    backend.neon.ntt.transpose8 v
      ⦃ (r : Array Vec128 8#usize) => ∀ k (hk : k < 8), ∀ m < 8,
          laneZ q (vAt r k hk) m = val m k ⦄ := by
  apply WP.spec_mono (transpose8_spec v)
  intro r hr k hk m hm
  unfold laneZ
  rw [hr k hk m hm]
  exact hv m hm k hk

/-! ## The four groups, as residues

The bookkeeping the last sections set up, run once per group.  The eight vectors are loaded in
coefficient order, so lane `m` of vector `j` is coefficient `64g + 8j + m` and levels 2, 3 and 4
read back through `ctLvl_lvl2` / `_lvl3` / `_lvl4`.  The transpose swaps the two indices, after
which lane `m` of vector `k` is coefficient `64g + 8m + k` — `load_group_spec`'s arrangement —
and levels 5, 6 and 7 read back through `ctLvl_group4` / `_group2` / `_group1`.  The transpose
back returns to coefficient order, and the store puts the group where it came from. -/

/-- The six levels a group carries, as a function of the view it starts from. -/
noncomputable def fwdG (q : ℕ) (ψ a0 : ℕ → ZMod q) : ℕ → ZMod q :=
  ctLvl q ψ 128 1 (ctLvl q ψ 64 2 (ctLvl q ψ 32 4
    (ctLvl q ψ 16 8 (ctLvl q ψ 8 16 (ctLvl q ψ 4 32 a0)))))

set_option maxRecDepth 8000 in
set_option maxHeartbeats 16000000 in
theorem ntt_group_val (SECOND : Bool) {N : Usize} (b : Array I16 N) (base : Usize)
    (qv bm round : Vec128)
    (q : ℕ) (Zb M Ain A3 A4 Ar B1 B2 B3 B4 : ℤ) (Rinv : ZMod q) (ψ a0 : ℕ → ZMod q)
    (hR : ((2 ^ 16 : ℤ) : ZMod q) * Rinv = 1)
    (hQ : ∀ i < 8, (lane16 qv i).toInt = (q : ℤ)) (hQpos : 0 < (q : ℤ))
    (hQ14 : (q : ℤ) < 2 ^ 14) (hQodd : ¬ (2 ∣ (q : ℤ))) (hZb : Zb ≤ 2 ^ 14)
    (hM : ∀ i < 8, (lane16 bm i).toInt = M) (hMpos : 0 < M) (hMlt : M < 2 ^ 15)
    (hD : |2 ^ 27 - (q : ℤ) * M| ≤ 2047)
    (hRnd : ∀ i < 8, (lane16 round i).toInt = 2 ^ 10)
    (hN : 8 * base.val + 256 ≤ N.val)
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
    (hAin : 0 ≤ Ain) (hA3 : 0 ≤ A3) (hAr : 0 ≤ Ar)
    (hB1 : 0 ≤ B1) (hB2 : 0 ≤ B2) (hB3 : 0 ≤ B3) (hreset : ((q : ℤ) - 1) / 2 ≤ Ar)
    (hs2 : LevelStep (q : ℤ) Zb Ain (A3 - Ain)) (hs3 : LevelStep (q : ℤ) Zb A3 (A4 - A3))
    (hs4 : LevelStep (q : ℤ) Zb Ar (B1 - Ar)) (hs5 : LevelStep (q : ℤ) Zb B1 (B2 - B1))
    (hs6 : LevelStep (q : ℤ) Zb B2 (B3 - B2)) (hs7 : LevelStep (q : ℤ) Zb B3 (B4 - B3))
    (iter : core.ops.range.Range Usize) (hend : iter.«end».val = 4)
    (hb : ∀ p < N.val, fromVec base.val (8 * iter.start.val) p → |(b.val[p]!).val| ≤ Ain)
    (hva : ∀ c < 256, posZ q b (8 * base.val + c) =
        if c < 64 * iter.start.val then fwdG q ψ a0 c else a0 c) :
    backend.neon.ntt.ntt_block_loop1 SECOND iter b base qv bm round
      ⦃ (r : Array I16 N) =>
          (∀ p < N.val, if fromVec base.val (8 * iter.start.val) p then
              |(r.val[p]!).val| ≤ ((q : ℤ) - 1) / 2
            else (r.val[p]!).val = (b.val[p]!).val) ∧
          (∀ c < 256, posZ q r (8 * base.val + c) = fwdG q ψ a0 c) ⦄ := by
  have hNmax : N.val ≤ Usize.max := by scalar_tac
  have hbig : 256 ≤ Usize.max := by omega
  have hQ0 : (0 : ℤ) ≤ ((q : ℤ) - 1) / 2 := by omega
  unfold backend.neon.ntt.ntt_block_loop1
  by_cases hlt : iter.start.val < iter.«end».val
  · let* ⟨ o, iter1, ho, hstart', hend' ⟩ ← core.iter.range.IteratorRange.next_Usize_some_spec
    rw [ho]
    simp only
    have hg4 : iter.start.val < 4 := by omega
    set g := iter.start with hg_def
    -- 1. the eight vectors of the group, in coefficient order
    let* ⟨ i, hi ⟩ ← Std.Usize.mul_spec (x := 8#usize) (y := g) (by scalar_tac)
    have hiv : i.val = 8 * g.val := by scalar_tac
    let* ⟨ j0, hj0 ⟩ ← Std.Usize.add_spec (x := base) (y := i) (by omega)
    obtain ⟨w0, hw0, hw0l⟩ := load_i16_gen b j0 (by omega)
    rw [hw0, bind_tc_ok]
    let* ⟨ e1, he1 ⟩ ← Std.Usize.add_spec (x := base) (y := i) (by omega)
    let* ⟨ j1, hj1 ⟩ ← Std.Usize.add_spec (x := e1) (y := 1#usize) (by scalar_tac)
    obtain ⟨w1, hw1, hw1l⟩ := load_i16_gen b j1 (by omega)
    rw [hw1, bind_tc_ok]
    let* ⟨ e2, he2 ⟩ ← Std.Usize.add_spec (x := base) (y := i) (by omega)
    let* ⟨ j2, hj2 ⟩ ← Std.Usize.add_spec (x := e2) (y := 2#usize) (by scalar_tac)
    obtain ⟨w2, hw2, hw2l⟩ := load_i16_gen b j2 (by omega)
    rw [hw2, bind_tc_ok]
    let* ⟨ e3, he3 ⟩ ← Std.Usize.add_spec (x := base) (y := i) (by omega)
    let* ⟨ j3, hj3 ⟩ ← Std.Usize.add_spec (x := e3) (y := 3#usize) (by scalar_tac)
    obtain ⟨w3, hw3, hw3l⟩ := load_i16_gen b j3 (by omega)
    rw [hw3, bind_tc_ok]
    let* ⟨ e4, he4 ⟩ ← Std.Usize.add_spec (x := base) (y := i) (by omega)
    let* ⟨ j4, hj4 ⟩ ← Std.Usize.add_spec (x := e4) (y := 4#usize) (by scalar_tac)
    obtain ⟨w4, hw4, hw4l⟩ := load_i16_gen b j4 (by omega)
    rw [hw4, bind_tc_ok]
    let* ⟨ e5, he5 ⟩ ← Std.Usize.add_spec (x := base) (y := i) (by omega)
    let* ⟨ j5, hj5 ⟩ ← Std.Usize.add_spec (x := e5) (y := 5#usize) (by scalar_tac)
    obtain ⟨w5, hw5, hw5l⟩ := load_i16_gen b j5 (by omega)
    rw [hw5, bind_tc_ok]
    let* ⟨ e6, he6 ⟩ ← Std.Usize.add_spec (x := base) (y := i) (by omega)
    let* ⟨ j6, hj6 ⟩ ← Std.Usize.add_spec (x := e6) (y := 6#usize) (by scalar_tac)
    obtain ⟨w6, hw6, hw6l⟩ := load_i16_gen b j6 (by omega)
    rw [hw6, bind_tc_ok]
    let* ⟨ e7, he7 ⟩ ← Std.Usize.add_spec (x := base) (y := i) (by omega)
    let* ⟨ j7, hj7 ⟩ ← Std.Usize.add_spec (x := e7) (y := 7#usize) (by scalar_tac)
    obtain ⟨w7, hw7, hw7l⟩ := load_i16_gen b j7 (by omega)
    rw [hw7, bind_tc_ok]
    set v : Array Vec128 8#usize := Array.make 8#usize [w0, w1, w2, w3, w4, w5, w6, w7] with hvdef
    have hvlane : ∀ j (hj : j < 8), ∀ m < 8,
        (lane16 (vAt v j hj) m).toInt = (b.val[8 * base.val + (64 * g.val + 8 * j + m)]!).val := by
      intro j hj m hm
      have e0 : ∀ h, vAt v 0 h = w0 := fun _ => rfl
      have e1' : ∀ h, vAt v 1 h = w1 := fun _ => rfl
      have e2' : ∀ h, vAt v 2 h = w2 := fun _ => rfl
      have e3' : ∀ h, vAt v 3 h = w3 := fun _ => rfl
      have e4' : ∀ h, vAt v 4 h = w4 := fun _ => rfl
      have e5' : ∀ h, vAt v 5 h = w5 := fun _ => rfl
      have e6' : ∀ h, vAt v 6 h = w6 := fun _ => rfl
      have e7' : ∀ h, vAt v 7 h = w7 := fun _ => rfl
      rcases show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 from by omega with
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [e0, e1', e2', e3', e4', e5', e6', e7'] <;>
      [ (rw [hw0l m hm]); (rw [hw1l m hm]); (rw [hw2l m hm]); (rw [hw3l m hm]);
        (rw [hw4l m hm]); (rw [hw5l m hm]); (rw [hw6l m hm]); (rw [hw7l m hm]) ] <;>
      congr 2 <;> omega
    have hvb : ∀ j (hj : j < 8), VecBnd (vAt v j hj) Ain := by
      intro j hj m hm
      rw [hvlane j hj m hm]
      exact hb _ (by omega) (by unfold fromVec; omega)
    have hvZ : ∀ j (hj : j < 8), ∀ m < 8,
        laneZ q (vAt v j hj) m = a0 (64 * g.val + 8 * j + m) := by
      intro j hj m hm
      unfold laneZ
      rw [hvlane j hj m hm]
      have := hva (64 * g.val + 8 * j + m) (by omega)
      rw [if_neg (by omega)] at this
      exact this
    clear_value v
    clear hvlane hvdef
    -- 2. level 2
    let* ⟨ k2, hk2 ⟩ ← Std.Usize.add_spec (x := 4#usize) (y := g) (by scalar_tac)
    have hk2v : k2.val = 4 + g.val := by scalar_tac
    obtain ⟨zi, zqi, hzi, hzqi, hzib, hzqib, hzpsi⟩ := hzeta k2 (by scalar_tac)
    rw [hzi, bind_tc_ok]
    obtain ⟨z2, hz2, hz2l⟩ := dup_n_s16_spec zi
    rw [hz2, bind_tc_ok, hzqi, bind_tc_ok]
    obtain ⟨zq2, hzq2, hzq2l⟩ := dup_n_s16_spec zqi
    rw [hzq2, bind_tc_ok]
    have hz2v : ∀ i < 8, |(lane16 z2 i).toInt| ≤ Zb := by
      intro i hi'; rw [hz2l i hi']; exact hzib
    have hzq2v : ∀ i < 8, (2 ^ 16 : ℤ) ∣ ((lane16 zq2 i).toInt * (q : ℤ) - (lane16 z2 i).toInt) := by
      intro i hi'; rw [hz2l i hi', hzq2l i hi']; exact hzqib
    have hz2k : ∀ m < 8, laneZ q z2 m * Rinv = ψ (4 + g.val) := by
      intro m hm
      unfold laneZ
      rw [hz2l m hm, ← hk2v]
      exact hzpsi
    apply WP.spec_bind (WP.spec_both
      (ntt_len4_bnd qv z2 zq2 (q : ℤ) Zb Ain (A3 - Ain) hQ hQpos (by omega)
        hz2v hZb hzq2v hAin hs2.1 hs2.2.1 hs2.2.2 v ⟨0#usize, 4#usize⟩ rfl
        (fun j hj _ => hvb j hj))
      (ntt_len4_val qv z2 zq2 q Zb Ain (A3 - Ain) Rinv (fun _ => ψ (4 + g.val)) hR hz2k
        hQ hQpos (by omega) hz2v hZb hzq2v hAin hs2.1 hs2.2.1 hs2.2.2 v ⟨0#usize, 4#usize⟩ rfl
        (fun j hj _ => hvb j hj)))
    rintro v1 ⟨hv1, hv1v⟩
    have hv1b : ∀ j (hj : j < 8), VecBnd (vAt v1 j hj) A3 := by
      intro j hj
      have := hv1 j hj
      rw [if_pos (by unfold pend4; scalar_tac)] at this
      exact this.mono (by omega)
    have hv1Z : ∀ j (hj : j < 8), ∀ m < 8,
        laneZ q (vAt v1 j hj) m = ctLvl q ψ 4 32 a0 (64 * g.val + 8 * j + m) := by
      intro j hj m hm
      have h := hv1v j hj m hm
      rw [ctLvl_lvl2 q ψ a0 g.val j m hj hm]
      by_cases hj4 : j < 4
      · rw [if_pos (show ((⟨0#usize, 4#usize⟩ : core.ops.range.Range Usize)).start.val ≤ j
              ∧ j < 4 from ⟨by scalar_tac, hj4⟩)] at h
        rw [h, if_pos hj4, hvZ (j % 4) (by omega) m hm, hvZ (j % 4 + 4) (by omega) m hm,
          show 64 * g.val + 8 * (j % 4) + m = 64 * g.val + 8 * j + m from by omega,
          show 64 * g.val + 8 * (j % 4 + 4) + m = 64 * g.val + 8 * j + m + 32 from by omega]
      · rw [if_neg (show ¬ (((⟨0#usize, 4#usize⟩ : core.ops.range.Range Usize)).start.val ≤ j
                ∧ j < 4) from by scalar_tac),
          if_pos (show 4 + ((⟨0#usize, 4#usize⟩ : core.ops.range.Range Usize)).start.val ≤ j
              ∧ j < 8 from ⟨by scalar_tac, hj⟩)] at h
        rw [h, if_neg hj4, hvZ (j % 4) (by omega) m hm, hvZ (j % 4 + 4) (by omega) m hm,
          show 64 * g.val + 8 * (j % 4) + m = 64 * g.val + 8 * j + m - 32 from by omega,
          show 64 * g.val + 8 * (j % 4 + 4) + m = 64 * g.val + 8 * j + m from by omega]
    -- 3. level 3
    apply WP.spec_bind (WP.spec_both
      (ntt_lvl3_bnd SECOND qv (q : ℤ) Zb A3 (A4 - A3) hQ hQpos (by omega) hZb
        hA3 hs3.1 hs3.2.1 hs3.2.2 (fun kk hkk => by
          obtain ⟨zi', zqi', h1, h2, h3, h4, -⟩ := hzeta kk hkk
          exact ⟨zi', zqi', h1, h2, h3, h4⟩)
        g hg4 v1 ⟨0#usize, 2#usize⟩ rfl (fun j hj _ => hv1b j hj))
      (ntt_lvl3_val SECOND qv q Zb A3 (A4 - A3) Rinv ψ hR hQ hQpos (by omega) hZb
        hA3 hs3.1 hs3.2.1 hs3.2.2 hzeta g hg4 v1 ⟨0#usize, 2#usize⟩ rfl
        (fun j hj _ => hv1b j hj)))
    rintro v2 ⟨hv2, hv2v⟩
    have hv2b : ∀ j (hj : j < 8), VecBnd (vAt v2 j hj) A4 := by
      intro j hj
      have := hv2 j hj
      rw [if_pos (by scalar_tac)] at this
      exact this.mono (by omega)
    have hv2Z : ∀ j (hj : j < 8), ∀ m < 8, laneZ q (vAt v2 j hj) m
        = ctLvl q ψ 8 16 (ctLvl q ψ 4 32 a0) (64 * g.val + 8 * j + m) := by
      intro j hj m hm
      have h := hv2v j hj m hm
      rw [if_pos (show 4 * ((⟨0#usize, 2#usize⟩ : core.ops.range.Range Usize)).start.val ≤ j
        from by scalar_tac)] at h
      rw [ctLvl_lvl3 q ψ (ctLvl q ψ 4 32 a0) g.val j m hj hm]
      by_cases hj2 : j % 4 < 2
      · rw [if_pos hj2] at h
        rw [h, if_pos hj2, hv1Z (4 * (j / 4) + j % 2) (by omega) m hm,
          hv1Z (4 * (j / 4) + j % 2 + 2) (by omega) m hm,
          show 64 * g.val + 8 * (4 * (j / 4) + j % 2) + m
            = 64 * g.val + 8 * j + m from by omega,
          show 64 * g.val + 8 * (4 * (j / 4) + j % 2 + 2) + m
            = 64 * g.val + 8 * j + m + 16 from by omega]
      · rw [if_neg hj2] at h
        rw [h, if_neg hj2, hv1Z (4 * (j / 4) + j % 2) (by omega) m hm,
          hv1Z (4 * (j / 4) + j % 2 + 2) (by omega) m hm,
          show 64 * g.val + 8 * (4 * (j / 4) + j % 2) + m
            = 64 * g.val + 8 * j + m - 16 from by omega,
          show 64 * g.val + 8 * (4 * (j / 4) + j % 2 + 2) + m
            = 64 * g.val + 8 * j + m from by omega]
    -- 4. the slice round trip, and the first re-centring pass
    let* ⟨ s, to_back, hs_val, hto_back ⟩ ← Array.to_slice_mut_spec
    let* ⟨ iter2, imb, hi2_slice, hi2_zero, hi2_back ⟩ ← iter_mut_spec
    have hs_len : s.val.length = 8 := by rw [hs_val]; have := v2.property; scalar_tac
    have hi2_len : iter2.slice.val.length = 8 := by rw [hi2_slice]; exact hs_len
    have hi2Z : ∀ (j : ℕ) (hj : j < iter2.slice.val.length), ∀ m < 8,
        laneZ q (sAt iter2.slice j hj) m
          = ctLvl q ψ 8 16 (ctLvl q ψ 4 32 a0) (64 * g.val + 8 * j + m) := by
      intro j hj m hm
      have hjv : j < 8 := by omega
      have heq : sAt iter2.slice j hj = vAt v2 j hjv := by
        unfold sAt vAt
        exact List.getElem_of_eq (by rw [hi2_slice, hs_val]) _
      rw [heq]
      exact hv2Z j hjv m hm
    apply WP.spec_bind (WP.spec_both
      (ntt_barrett_iter_bnd iter2 (fun im1 => im1) bm round qv (q : ℤ) M hQ hM hRnd
        hQpos hQ14 hQodd hMpos hMlt hD hi2_len (by rw [hi2_zero]; omega)
        (fun im him => him)
        (fun im him j hj hbnd => absurd hj (by rw [hi2_zero]; omega))
        (fun im him j _ hbnd hbnd' => rfl))
      (ntt_barrett_iter_val iter2 (fun im1 => im1) bm round qv q M
        (fun j m => ctLvl q ψ 8 16 (ctLvl q ψ 4 32 a0) (64 * g.val + 8 * j + m)) hQ hM hRnd
        hQpos hQ14 hQodd hMpos hMlt hD hi2_len (by rw [hi2_zero]; omega) hi2Z
        (fun im him => him)
        (fun im him j hj hbnd m hm => absurd hj (by rw [hi2_zero]; omega))
        (fun im him j _ hbnd hbnd' => rfl)))
    rintro ⟨im, bk⟩ ⟨⟨him_len, hbk⟩, hbkv⟩
    obtain ⟨hbk_len, hbk_bnd⟩ := hbk im him_len
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
        = ctLvl q ψ 8 16 (ctLvl q ψ 4 32 a0) (64 * g.val + 8 * j + m) := by
      intro j hj m hm
      obtain ⟨hjb, heq⟩ := haeq j hj
      rw [heq]
      exact hbkv im him_len j hjb m hm
    show (do let v3 ← backend.neon.ntt.ntt_block_loop1_loop3 SECOND
                        { start := 0#usize, «end» := 4#usize } qv g a
             let v4 ← backend.neon.ntt.transpose8 v3
             let (z1, zq1) ← backend.neon.ntt.fwd4 SECOND g
             let v5 ← backend.neon.ntt.ntt_block_loop1_loop4
                        { start := 0#usize, «end» := 4#usize } qv v4 z1 zq1
             let v6 ← backend.neon.ntt.ntt_block_loop1_loop5 SECOND
                        { start := 0#usize, «end» := 2#usize } qv g v5
             let v7 ← backend.neon.ntt.ntt_block_loop1_loop6 SECOND
                        { start := 0#usize, «end» := 4#usize } qv g v6
             let (s2, to_slice_mut_back1) ← lift (Array.to_slice_mut v7)
             let (iter3, iter_mut_back1) ← core.slice.Slice.iter_mut s2
             let (im2, back1) ← backend.neon.ntt.ntt_block_loop1_loop7 iter3 (fun im3 => im3) qv
                                  bm round
             let im3 := back1 im2
             let s3 := iter_mut_back1 im3
             let v8 := to_slice_mut_back1 s3
             let v9 ← backend.neon.ntt.transpose8 v8
             let b1 ← backend.neon.ntt.ntt_block_loop1_loop8
                        { start := 0#usize, «end» := 8#usize } b base g v9
             backend.neon.ntt.ntt_block_loop1 SECOND iter1 b1 base qv bm round)
        ⦃ (r : Array I16 N) =>
            (∀ p < N.val, if fromVec base.val (8 * g.val) p then
                |(r.val[p]!).val| ≤ ((q : ℤ) - 1) / 2
              else (r.val[p]!).val = (b.val[p]!).val) ∧
            (∀ c < 256, posZ q r (8 * base.val + c) = fwdG q ψ a0 c) ⦄
    clear_value a
    clear haeq ha_val ha_def hbkv hbk_bnd hbk_len hbk him_len
    -- 5. level 4
    apply WP.spec_bind (WP.spec_both
      (ntt_lvl4_bnd SECOND qv (q : ℤ) Zb Ar (B1 - Ar) hQ hQpos (by omega) hZb
        hAr hs4.1 hs4.2.1 hs4.2.2 (fun kk hkk => by
          obtain ⟨zi', zqi', h1, h2, h3, h4, -⟩ := hzeta kk hkk
          exact ⟨zi', zqi', h1, h2, h3, h4⟩)
        g hg4 a ⟨0#usize, 4#usize⟩ rfl (fun j hj _ => hab j hj))
      (ntt_lvl4_val SECOND qv q Zb Ar (B1 - Ar) Rinv ψ hR hQ hQpos (by omega) hZb
        hAr hs4.1 hs4.2.1 hs4.2.2 hzeta g hg4 a ⟨0#usize, 4#usize⟩ rfl
        (fun j hj _ => hab j hj)))
    rintro v3 ⟨hv3, hv3v⟩
    have hv3b : ∀ j (hj : j < 8), VecBnd (vAt v3 j hj) B1 := by
      intro j hj
      have := hv3 j hj
      rw [if_pos (by unfold pend1; scalar_tac)] at this
      exact this.mono (by omega)
    have hv3Z : ∀ j (hj : j < 8), ∀ m < 8, laneZ q (vAt v3 j hj) m
        = ctLvl q ψ 16 8 (ctLvl q ψ 8 16 (ctLvl q ψ 4 32 a0)) (64 * g.val + 8 * j + m) := by
      intro j hj m hm
      have h := hv3v j hj m hm
      rw [if_pos (show 2 * ((⟨0#usize, 4#usize⟩ : core.ops.range.Range Usize)).start.val ≤ j
        from by scalar_tac)] at h
      rw [ctLvl_lvl4 q ψ (ctLvl q ψ 8 16 (ctLvl q ψ 4 32 a0)) g.val j m hj hm]
      by_cases hpar : j % 2 = 0
      · rw [if_pos hpar] at h
        rw [h, if_pos hpar, haZ (2 * (j / 2)) (by omega) m hm,
          haZ (2 * (j / 2) + 1) (by omega) m hm,
          show 64 * g.val + 8 * (2 * (j / 2)) + m = 64 * g.val + 8 * j + m from by omega,
          show 64 * g.val + 8 * (2 * (j / 2) + 1) + m
            = 64 * g.val + 8 * j + m + 8 from by omega]
      · rw [if_neg hpar] at h
        rw [h, if_neg hpar, haZ (2 * (j / 2)) (by omega) m hm,
          haZ (2 * (j / 2) + 1) (by omega) m hm,
          show 64 * g.val + 8 * (2 * (j / 2)) + m = 64 * g.val + 8 * j + m - 8 from by omega,
          show 64 * g.val + 8 * (2 * (j / 2) + 1) + m
            = 64 * g.val + 8 * j + m from by omega]
    -- 6. into the transposed view
    apply WP.spec_bind (WP.spec_both (transpose8_bnd v3 B1 hv3b)
      (transpose8_val v3 q (fun j m =>
        ctLvl q ψ 16 8 (ctLvl q ψ 8 16 (ctLvl q ψ 4 32 a0)) (64 * g.val + 8 * j + m)) hv3Z))
    rintro v4 ⟨hv4b, hv4v⟩
    have hv4Z : ∀ k (hk : k < 8), ∀ m < 8, laneZ q (vAt v4 k hk) m
        = ctLvl q ψ 16 8 (ctLvl q ψ 8 16 (ctLvl q ψ 4 32 a0)) (64 * g.val + 8 * m + k) :=
      hv4v
    -- 7. `len = 4`
    obtain ⟨z4, zq4, hz4e, ⟨hz4, hzq4⟩, hz4v⟩ := htbl4 g hg4
    rw [hz4e, bind_tc_ok, loop1_loop4_eq]
    apply WP.spec_bind (WP.spec_both
      (ntt_len4_bnd qv z4 zq4 (q : ℤ) Zb B1 (B2 - B1) hQ hQpos (by omega)
        hz4 hZb hzq4 hB1 hs5.1 hs5.2.1 hs5.2.2 v4 ⟨0#usize, 4#usize⟩ rfl
        (fun j hj _ => hv4b j hj))
      (ntt_len4_val qv z4 zq4 q Zb B1 (B2 - B1) Rinv
        (fun m => ψ (32 + (8 * g.val + m))) hR (fun m hm => hz4v m hm) hQ hQpos (by omega)
        hz4 hZb hzq4 hB1 hs5.1 hs5.2.1 hs5.2.2 v4 ⟨0#usize, 4#usize⟩ rfl
        (fun j hj _ => hv4b j hj)))
    rintro v5 ⟨hv5, hv5v⟩
    have hv5b : ∀ j (hj : j < 8), VecBnd (vAt v5 j hj) B2 := by
      intro j hj
      have := hv5 j hj
      rw [if_pos (by unfold pend4; scalar_tac)] at this
      exact this.mono (by omega)
    have hv5Z : ∀ k (hk : k < 8), ∀ m < 8,
        laneZ q (vAt v5 k hk) m = ctLvl q ψ 32 4 (ctLvl q ψ 16 8 (ctLvl q ψ 8 16 (ctLvl q ψ 4 32 a0))) (64 * g.val + 8 * m + k) := by
      intro k hk m hm
      have h := hv5v k hk m hm
      rw [ctLvl_group4 q ψ (ctLvl q ψ 16 8 (ctLvl q ψ 8 16 (ctLvl q ψ 4 32 a0))) g.val m k hm hk]
      by_cases hk4 : k < 4
      · rw [if_pos (show ((⟨0#usize, 4#usize⟩ : core.ops.range.Range Usize)).start.val ≤ k
              ∧ k < 4 from ⟨by scalar_tac, hk4⟩)] at h
        rw [h, if_pos hk4, hv4Z (k % 4) (by omega) m hm, hv4Z (k % 4 + 4) (by omega) m hm,
          show 64 * g.val + 8 * m + k % 4 = 64 * g.val + 8 * m + k from by omega,
          show 64 * g.val + 8 * m + (k % 4 + 4) = 64 * g.val + 8 * m + k + 4 from by omega]
      · rw [if_neg (show ¬ (((⟨0#usize, 4#usize⟩ : core.ops.range.Range Usize)).start.val ≤ k
                ∧ k < 4) from by scalar_tac),
          if_pos (show 4 + ((⟨0#usize, 4#usize⟩ : core.ops.range.Range Usize)).start.val ≤ k
              ∧ k < 8 from ⟨by scalar_tac, hk⟩)] at h
        rw [h, if_neg hk4, hv4Z (k % 4) (by omega) m hm, hv4Z (k % 4 + 4) (by omega) m hm,
          show 64 * g.val + 8 * m + k % 4 = 64 * g.val + 8 * m + k - 4 from by omega,
          show 64 * g.val + 8 * m + (k % 4 + 4) = 64 * g.val + 8 * m + k from by omega]
    -- 8. `len = 2` in its two halves
    apply WP.spec_bind (WP.spec_both
      (ntt_len2_outer_bnd SECOND qv (q : ℤ) Zb B2 (B3 - B2) hQ hQpos (by omega) hZb
        hB2 hs6.1 hs6.2.1 hs6.2.2 (fun kk hkk => by
          obtain ⟨z, zq, he, hp, -⟩ := htbl2 kk hkk
          exact ⟨z, zq, he, hp.1, hp.2⟩)
        g hg4 v5 ⟨0#usize, 2#usize⟩ rfl (fun j hj _ => hv5b j hj))
      (ntt_len2_outer_val SECOND qv q Zb B2 (B3 - B2) Rinv
        (fun kk m => ψ (64 + (16 * (kk / 2) + 2 * m + kk % 2))) hR hQ hQpos (by omega) hZb
        hB2 hs6.1 hs6.2.1 hs6.2.2 (fun kk hkk => by
          obtain ⟨z, zq, he, hp, hv⟩ := htbl2 kk hkk
          exact ⟨z, zq, he, hp.1, hp.2, hv⟩)
        g hg4 v5 ⟨0#usize, 2#usize⟩ rfl (fun j hj _ => hv5b j hj)))
    rintro v6 ⟨hv6, hv6v⟩
    have hv6b : ∀ j (hj : j < 8), VecBnd (vAt v6 j hj) B3 := by
      intro j hj
      have := hv6 j hj
      rw [if_pos (by scalar_tac)] at this
      exact this.mono (by omega)
    have hv6Z : ∀ k (hk : k < 8), ∀ m < 8, laneZ q (vAt v6 k hk) m
        = ctLvl q ψ 64 2 (ctLvl q ψ 32 4 (ctLvl q ψ 16 8 (ctLvl q ψ 8 16 (ctLvl q ψ 4 32 a0)))) (64 * g.val + 8 * m + k) := by
      intro k hk m hm
      have h := hv6v k hk m hm
      rw [if_pos (show 4 * ((⟨0#usize, 2#usize⟩ : core.ops.range.Range Usize)).start.val ≤ k
        from by scalar_tac)] at h
      rw [ctLvl_group2 q ψ (ctLvl q ψ 32 4 (ctLvl q ψ 16 8 (ctLvl q ψ 8 16 (ctLvl q ψ 4 32 a0)))) g.val m k hm hk]
      have hpsi : ψ (64 + (16 * ((2 * g.val + k / 4) / 2) + 2 * m + (2 * g.val + k / 4) % 2))
          = ψ (64 + (16 * g.val + 2 * m + k / 4)) := by
        rw [show (2 * g.val + k / 4) / 2 = g.val from by omega,
          show (2 * g.val + k / 4) % 2 = k / 4 from by omega]
      by_cases hk2 : k % 4 < 2
      · rw [if_pos hk2] at h
        rw [h, if_pos hk2, hpsi, hv5Z (4 * (k / 4) + k % 2) (by omega) m hm,
          hv5Z (4 * (k / 4) + k % 2 + 2) (by omega) m hm,
          show 64 * g.val + 8 * m + (4 * (k / 4) + k % 2) = 64 * g.val + 8 * m + k from by omega,
          show 64 * g.val + 8 * m + (4 * (k / 4) + k % 2 + 2)
            = 64 * g.val + 8 * m + k + 2 from by omega]
      · rw [if_neg hk2] at h
        rw [h, if_neg hk2, hpsi, hv5Z (4 * (k / 4) + k % 2) (by omega) m hm,
          hv5Z (4 * (k / 4) + k % 2 + 2) (by omega) m hm,
          show 64 * g.val + 8 * m + (4 * (k / 4) + k % 2)
            = 64 * g.val + 8 * m + k - 2 from by omega,
          show 64 * g.val + 8 * m + (4 * (k / 4) + k % 2 + 2)
            = 64 * g.val + 8 * m + k from by omega]
    -- 9. `len = 1`
    apply WP.spec_bind (WP.spec_both
      (ntt_len1_bnd SECOND qv (q : ℤ) Zb B3 (B4 - B3) hQ hQpos (by omega) hZb
        hB3 hs7.1 hs7.2.1 hs7.2.2 (fun kk hkk => by
          obtain ⟨z, zq, he, hp, -⟩ := htbl1 kk hkk
          exact ⟨z, zq, he, hp.1, hp.2⟩)
        g hg4 v6 ⟨0#usize, 4#usize⟩ rfl (fun j hj _ => hv6b j hj))
      (ntt_len1_val SECOND qv q Zb B3 (B4 - B3) Rinv
        (fun kk m => ψ (128 + (32 * (kk / 4) + 4 * m + kk % 4))) hR hQ hQpos (by omega) hZb
        hB3 hs7.1 hs7.2.1 hs7.2.2 (fun kk hkk => by
          obtain ⟨z, zq, he, hp, hv⟩ := htbl1 kk hkk
          exact ⟨z, zq, he, hp.1, hp.2, hv⟩)
        g hg4 v6 ⟨0#usize, 4#usize⟩ rfl (fun j hj _ => hv6b j hj)))
    rintro v7 ⟨hv7, hv7v⟩
    have hv7b : ∀ j (hj : j < 8), VecBnd (vAt v7 j hj) B4 := by
      intro j hj
      have := hv7 j hj
      rw [if_pos (by unfold pend1; scalar_tac)] at this
      exact this.mono (by omega)
    have hv7Z : ∀ k (hk : k < 8), ∀ m < 8,
        laneZ q (vAt v7 k hk) m = fwdG q ψ a0 (64 * g.val + 8 * m + k) := by
      intro k hk m hm
      have h := hv7v k hk m hm
      rw [if_pos (show 2 * ((⟨0#usize, 4#usize⟩ : core.ops.range.Range Usize)).start.val ≤ k
        from by scalar_tac)] at h
      unfold fwdG
      rw [ctLvl_group1 q ψ (ctLvl q ψ 64 2 (ctLvl q ψ 32 4 (ctLvl q ψ 16 8 (ctLvl q ψ 8 16 (ctLvl q ψ 4 32 a0))))) g.val m k hm hk]
      have hpsi : ψ (128 + (32 * ((4 * g.val + k / 2) / 4) + 4 * m + (4 * g.val + k / 2) % 4))
          = ψ (128 + (32 * g.val + 4 * m + k / 2)) := by
        rw [show (4 * g.val + k / 2) / 4 = g.val from by omega,
          show (4 * g.val + k / 2) % 4 = k / 2 from by omega]
      by_cases hpar : k % 2 = 0
      · rw [if_pos hpar] at h
        rw [h, if_pos hpar, hpsi, hv6Z (2 * (k / 2)) (by omega) m hm,
          hv6Z (2 * (k / 2) + 1) (by omega) m hm,
          show 64 * g.val + 8 * m + 2 * (k / 2) = 64 * g.val + 8 * m + k from by omega,
          show 64 * g.val + 8 * m + (2 * (k / 2) + 1)
            = 64 * g.val + 8 * m + k + 1 from by omega]
      · rw [if_neg hpar] at h
        rw [h, if_neg hpar, hpsi, hv6Z (2 * (k / 2)) (by omega) m hm,
          hv6Z (2 * (k / 2) + 1) (by omega) m hm,
          show 64 * g.val + 8 * m + 2 * (k / 2) = 64 * g.val + 8 * m + k - 1 from by omega,
          show 64 * g.val + 8 * m + (2 * (k / 2) + 1) = 64 * g.val + 8 * m + k from by omega]
    -- 10. the second re-centring pass
    let* ⟨ s2, to_back2, hs2_val, hto_back2 ⟩ ← Array.to_slice_mut_spec
    let* ⟨ iter3, imb3, hi3_slice, hi3_zero, hi3_back ⟩ ← iter_mut_spec
    have hs2_len : s2.val.length = 8 := by rw [hs2_val]; have := v7.property; scalar_tac
    have hi3_len : iter3.slice.val.length = 8 := by rw [hi3_slice]; exact hs2_len
    have hi3Z : ∀ (j : ℕ) (hj : j < iter3.slice.val.length), ∀ m < 8,
        laneZ q (sAt iter3.slice j hj) m = fwdG q ψ a0 (64 * g.val + 8 * m + j) := by
      intro j hj m hm
      have hjv : j < 8 := by omega
      have heq : sAt iter3.slice j hj = vAt v7 j hjv := by
        unfold sAt vAt
        exact List.getElem_of_eq (by rw [hi3_slice, hs2_val]) _
      rw [heq]
      exact hv7Z j hjv m hm
    rw [loop1_loop7_eq]
    apply WP.spec_bind (WP.spec_both
      (ntt_barrett_iter_bnd iter3 (fun im1 => im1) bm round qv (q : ℤ) M hQ hM hRnd
        hQpos hQ14 hQodd hMpos hMlt hD hi3_len (by rw [hi3_zero]; omega)
        (fun im him => him)
        (fun im him j hj hbnd => absurd hj (by rw [hi3_zero]; omega))
        (fun im him j _ hbnd hbnd' => rfl))
      (ntt_barrett_iter_val iter3 (fun im1 => im1) bm round qv q M
        (fun j m => fwdG q ψ a0 (64 * g.val + 8 * m + j)) hQ hM hRnd
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
    have ha2b : ∀ j (hj : j < 8), VecBnd (vAt a2 j hj) (((q : ℤ) - 1) / 2) := by
      intro j hj
      obtain ⟨hjb, heq⟩ := ha2eq j hj
      rw [heq]
      exact hbk2_bnd j hjb
    have ha2Z : ∀ j (hj : j < 8), ∀ m < 8,
        laneZ q (vAt a2 j hj) m = fwdG q ψ a0 (64 * g.val + 8 * m + j) := by
      intro j hj m hm
      obtain ⟨hjb, heq⟩ := ha2eq j hj
      rw [heq]
      exact hbk2v im2 him2_len j hjb m hm
    clear ha2eq hbk2v hbk2_bnd hbk2_len hbk2 him2_len
    -- 11. back to coefficient order, and out to memory
    apply WP.spec_bind (WP.spec_both (transpose8_bnd a2 (((q : ℤ) - 1) / 2) ha2b)
      (transpose8_val a2 q (fun j m => fwdG q ψ a0 (64 * g.val + 8 * m + j)) ha2Z))
    rintro v9 ⟨hv9b, hv9v⟩
    have hv9Z : ∀ j (hj : j < 8), ∀ m < 8,
        laneZ q (vAt v9 j hj) m = fwdG q ψ a0 (64 * g.val + 8 * j + m) := hv9v
    apply WP.spec_bind (store_vecs_spec b base g hg4 hN v9)
    intro b1 hb1
    have hb1Z : ∀ c < 256, posZ q b1 (8 * base.val + c) =
        if c < 64 * g.val + 64 then fwdG q ψ a0 c else a0 c := by
      intro c hc
      have h := hb1 (8 * base.val + c) (by omega)
      unfold posZ
      rw [h]
      by_cases hin : 64 * g.val ≤ c ∧ c < 64 * g.val + 64
      · rw [if_pos (show 8 * base.val + 64 * g.val ≤ 8 * base.val + c
              ∧ 8 * base.val + c < 8 * base.val + 64 * g.val + 64 from ⟨by omega, by omega⟩),
          if_pos (by omega)]
        have hj8 : (8 * base.val + c - 8 * base.val - 64 * g.val) / 8 % 8 = (c - 64 * g.val) / 8
          := by omega
        have hm8 : (8 * base.val + c - 8 * base.val - 64 * g.val) % 8 = (c - 64 * g.val) % 8
          := by omega
        rw [vAt_congr v9 (by omega) (show (c - 64 * g.val) / 8 < 8 from by omega) hj8, hm8]
        have := hv9Z ((c - 64 * g.val) / 8) (by omega) ((c - 64 * g.val) % 8) (by omega)
        unfold laneZ at this
        rw [this, show 64 * g.val + 8 * ((c - 64 * g.val) / 8) + (c - 64 * g.val) % 8 = c
          from by omega]
      · rw [if_neg (show ¬ (8 * base.val + 64 * g.val ≤ 8 * base.val + c
              ∧ 8 * base.val + c < 8 * base.val + 64 * g.val + 64) from by omega)]
        have := hva c hc
        unfold posZ at this
        rw [this]
        by_cases hbelow : c < 64 * g.val
        · rw [if_pos hbelow, if_pos (by omega)]
        · rw [if_neg hbelow, if_neg (by omega)]
    -- 12. and the remaining groups
    apply WP.spec_mono (ntt_group_val SECOND b1 base qv bm round q Zb M Ain A3 A4 Ar B1 B2 B3 B4
      Rinv ψ a0 hR hQ hQpos hQ14 hQodd hZb hM hMpos hMlt hD hRnd hN hzeta htbl4 htbl2 htbl1
      hAin hA3 hAr hB1 hB2 hB3 hreset hs2 hs3 hs4 hs5 hs6 hs7 iter1 (by rw [hend']; exact hend)
      (by
        intro p hp hge
        have := hb1 p hp
        rw [if_neg (by unfold fromVec at hge; omega)] at this
        rw [this]
        exact hb p hp (by unfold fromVec at hge ⊢; omega))
      (by
        intro c hc
        rw [hb1Z c hc]
        by_cases hbelow : c < 64 * g.val + 64
        · rw [if_pos hbelow, if_pos (by omega)]
        · rw [if_neg hbelow, if_neg (by omega)]))
    rintro r ⟨hr1, hr2⟩
    refine ⟨fun p hp => ?_, hr2⟩
    have hrp := hr1 p hp
    by_cases hge : fromVec base.val (8 * g.val) p
    · rw [if_pos hge]
      by_cases hge1 : fromVec base.val (8 * iter1.start.val) p
      · rw [if_pos hge1] at hrp
        exact hrp
      · rw [if_neg hge1] at hrp
        rw [hrp]
        have := hb1 p hp
        rw [if_pos (by unfold fromVec at hge hge1; omega)] at this
        rw [this]
        exact hv9b _ (by omega) _ (by omega)
    · rw [if_neg hge]
      rw [if_neg (by unfold fromVec at hge ⊢; omega)] at hrp
      rw [hrp]
      have := hb1 p hp
      rw [if_neg (by unfold fromVec at hge; omega)] at this
      exact this
  · let* ⟨ o, iter1, hnone, _ ⟩ ← core.iter.range.IteratorRange.next_Usize_none_spec
    rw [hnone]
    have hs4' : 4 ≤ iter.start.val := by scalar_tac
    refine (WP.spec_ok _).mpr ⟨fun p hp => ?_, fun c hc => ?_⟩
    · rw [if_neg (by unfold fromVec; omega)]
    · rw [hva c hc, if_pos (by omega)]
termination_by 4 - iter.start.val
decreasing_by scalar_decr_tac

/-! ## The forward transform

The constant setup, the two whole-vector levels and the four groups — the same composition
`ntt_block_bnd` makes, with the value chain riding along.  The result is centred *and* equal to
the eight Cooley-Tukey layers applied to the input view, and everything outside this prime's
window is untouched. -/

/-- The whole forward transform, as a function of the input view. -/
noncomputable def fwdAll (q : ℕ) (ψ f : ℕ → ZMod q) : ℕ → ZMod q := fwdG q ψ (fwdH q ψ f)

set_option maxHeartbeats 2000000 in
theorem ntt_block_val (SECOND : Bool) {N : Usize} (b : Array I16 N) (base : Usize)
    (q : ℕ) (Zb M A1 A2 A3 A4 : ℤ) (Rinv : ZMod q) (ψ f : ℕ → ZMod q)
    (qc mc rc : I16)
    (hR : ((2 ^ 16 : ℤ) : ZMod q) * Rinv = 1)
    (hq : backend.crt.q SECOND = ok qc) (hqv : qc.val = (q : ℤ))
    (hm : backend.crt.barrett_m SECOND = ok mc) (hmv : mc.val = M)
    (hrc : (1#i16 : I16) <<< (10#i32 : Std.I32) = ok rc) (hrcv : rc.val = 2 ^ 10)
    (hQpos : 0 < (q : ℤ)) (hQ14 : (q : ℤ) < 2 ^ 14) (hQodd : ¬ (2 ∣ (q : ℤ)))
    (hZb : Zb ≤ 2 ^ 14)
    (hMpos : 0 < M) (hMlt : M < 2 ^ 15) (hD : |2 ^ 27 - (q : ℤ) * M| ≤ 2047)
    (hN : 8 * base.val + 256 ≤ N.val)
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
    (hA1 : 0 ≤ A1) (hA2 : 0 ≤ A2) (hA3 : 0 ≤ A3)
    (hs0 : LevelStep (q : ℤ) Zb (((q : ℤ) - 1) / 2) (A1 - ((q : ℤ) - 1) / 2))
    (hs1 : LevelStep (q : ℤ) Zb A1 (A2 - A1)) (hs2 : LevelStep (q : ℤ) Zb A2 (A3 - A2))
    (hs3 : LevelStep (q : ℤ) Zb A3 (A4 - A3))
    (hb : ∀ p < N.val, fromVec base.val 0 p → |(b.val[p]!).val| ≤ ((q : ℤ) - 1) / 2)
    (hf : ∀ c < 256, posZ q b (8 * base.val + c) = f c) :
    backend.neon.ntt.ntt_block SECOND b base
      ⦃ (r : Array I16 N) =>
          (∀ p < N.val, if fromVec base.val 0 p then |(r.val[p]!).val| ≤ ((q : ℤ) - 1) / 2
            else (r.val[p]!).val = (b.val[p]!).val) ∧
          (∀ c < 256, posZ q r (8 * base.val + c) = fwdAll q ψ f c) ⦄ := by
  have hQ0 : (0 : ℤ) ≤ ((q : ℤ) - 1) / 2 := by omega
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
  -- levels 0 and 1
  apply WP.spec_bind (ntt_horizontal_val SECOND b base qv q Zb (((q : ℤ) - 1) / 2) A1 A2
    Rinv ψ f hR hQv hQpos hQ14 hZb hN hzeta hQ0 hA1 hs0 hs1 hb hf)
  rintro b1 ⟨hb1, hb1v⟩
  -- levels 2 to 7, a group at a time
  apply WP.spec_mono (ntt_group_val SECOND b1 base qv bm round q Zb M A2 A3 A4 (((q : ℤ) - 1) / 2)
    A1 A2 A3 A4 Rinv ψ (fwdH q ψ f) hR hQv hQpos hQ14 hQodd hZb hMv hMpos hMlt hD hRv hN hzeta
    htbl4 htbl2 htbl1 hA2 hA3 hQ0 hA1 hA2 hA3 (le_refl _) hs2 hs3 hs0 hs1 hs2 hs3
    ⟨0#usize, 4#usize⟩ rfl
    (by
      intro p hp hin
      have h := hb1 p hp
      rw [if_pos (show fromVec base.val 0 p by unfold fromVec at hin ⊢; scalar_tac)] at h
      exact h)
    (by intro c hc; rw [hb1v c hc, if_neg (by scalar_tac)]))
  rintro r ⟨hr1, hr2⟩
  refine ⟨fun p hp => ?_, ?_⟩
  · have hrp := hr1 p hp
    have hb1p := hb1 p hp
    by_cases hin : fromVec base.val 0 p
    · rw [if_pos hin]
      rw [if_pos (show fromVec base.val (8 * (0#usize : Usize).val) p by
        unfold fromVec at hin ⊢; scalar_tac)] at hrp
      exact hrp
    · rw [if_neg hin]
      rw [if_neg (show ¬ fromVec base.val (8 * (0#usize : Usize).val) p by
        unfold fromVec at hin ⊢; scalar_tac)] at hrp
      rw [if_neg hin] at hb1p
      rw [hrp, hb1p]
  · intro c hc
    rw [hr2 c hc]
    rfl

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
theorem ntt_block_val_q1 {N : Usize} (b : Array I16 N) (base : Usize) (f : ℕ → ZMod 7681)
    (hN : 8 * base.val + 256 ≤ N.val)
    (hb : ∀ p < N.val, fromVec base.val 0 p → |(b.val[p]!).val| ≤ 3840)
    (hf : ∀ c < 256, posZ 7681 b (8 * base.val + c) = f c) :
    backend.neon.ntt.ntt_block false b base
      ⦃ (r : Array I16 N) =>
          (∀ p < N.val, if fromVec base.val 0 p then |(r.val[p]!).val| ≤ 3840
            else (r.val[p]!).val = (b.val[p]!).val) ∧
          (∀ c < 256, posZ 7681 r (8 * base.val + c) = fwdAll 7681 zeta1 f c) ⦄ := by
  obtain ⟨s0, s1, s2, s3, -, -⟩ := growth_q1
  have hQ : (((7681 : ℕ) : ℤ) - 1) / 2 = 3840 := by norm_num
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
  apply WP.spec_mono (ntt_block_val false b base 7681 3840 17474 7906 12210 16766 21589
    (900 : ZMod 7681) zeta1 f backend.crt.Q1 backend.crt.Q1_BARRETT_M 1024#i16
    (by decide)
    (by simp only [backend.crt.q, Bool.false_eq_true, if_false]) (by rw [q1_val]; norm_num)
    (by simp only [backend.crt.barrett_m, Bool.false_eq_true, if_false]) q1_m_val
    round_const (by decide)
    (by norm_num) (by norm_num) (by decide) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hN
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
    (by norm_num) (by norm_num) (by norm_num)
    (by rw [hQ]; simpa using s0) (by simpa using s1) (by simpa using s2) (by simpa using s3)
    (by rw [hQ]; exact hb) hf)
  rintro r ⟨h1, h2⟩
  refine ⟨fun p hp => ?_, h2⟩
  have := h1 p hp
  rwa [hQ] at this

open Kopis.CrtZeta in
/-- **The forward transform on the second prime, as residues.** -/
theorem ntt_block_val_q2 {N : Usize} (b : Array I16 N) (base : Usize) (f : ℕ → ZMod 10753)
    (hN : 8 * base.val + 256 ≤ N.val)
    (hb : ∀ p < N.val, fromVec base.val 0 p → |(b.val[p]!).val| ≤ 5376)
    (hf : ∀ c < 256, posZ 10753 b (8 * base.val + c) = f c) :
    backend.neon.ntt.ntt_block true b base
      ⦃ (r : Array I16 N) =>
          (∀ p < N.val, if fromVec base.val 0 p then |(r.val[p]!).val| ≤ 5376
            else (r.val[p]!).val = (b.val[p]!).val) ∧
          (∀ c < 256, posZ 10753 r (8 * base.val + c) = fwdAll 10753 zeta2 f c) ⦄ := by
  obtain ⟨s0, s1, s2, s3, -, -⟩ := growth_q2
  have hQ : (((10753 : ℕ) : ℤ) - 1) / 2 = 5376 := by norm_num
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
  apply WP.spec_mono (ntt_block_val true b base 10753 5376 12482 11194 17489 24301 31671
    (1764 : ZMod 10753) zeta2 f backend.crt.Q2 backend.crt.Q2_BARRETT_M 1024#i16
    (by decide)
    (by simp only [backend.crt.q, if_true]) (by rw [q2_val]; norm_num)
    (by simp only [backend.crt.barrett_m, if_true]) q2_m_val
    round_const (by decide)
    (by norm_num) (by norm_num) (by decide) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hN
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
    (by norm_num) (by norm_num) (by norm_num)
    (by rw [hQ]; simpa using s0) (by simpa using s1) (by simpa using s2) (by simpa using s3)
    (by rw [hQ]; exact hb) hf)
  rintro r ⟨h1, h2⟩
  refine ⟨fun p hp => ?_, h2⟩
  have := h1 p hp
  rwa [hQ] at this

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
  have h2 : State ψ 4 64 1 f (fwdH q ψ f) :=
    State_ct hsq (by norm_num) (by norm_num) h1 (ctLvl_hbut q ψ 2 64 _ (by norm_num))
  have h3 : State ψ 8 32 1 f (ctLvl q ψ 4 32 (fwdH q ψ f)) :=
    State_ct hsq (by norm_num) (by norm_num) h2 (ctLvl_hbut q ψ 4 32 _ (by norm_num))
  have h4 : State ψ 16 16 1 f (ctLvl q ψ 8 16 (ctLvl q ψ 4 32 (fwdH q ψ f))) :=
    State_ct hsq (by norm_num) (by norm_num) h3 (ctLvl_hbut q ψ 8 16 _ (by norm_num))
  have h5 : State ψ 32 8 1 f
      (ctLvl q ψ 16 8 (ctLvl q ψ 8 16 (ctLvl q ψ 4 32 (fwdH q ψ f)))) :=
    State_ct hsq (by norm_num) (by norm_num) h4 (ctLvl_hbut q ψ 16 8 _ (by norm_num))
  have h6 : State ψ 64 4 1 f
      (ctLvl q ψ 32 4 (ctLvl q ψ 16 8 (ctLvl q ψ 8 16 (ctLvl q ψ 4 32 (fwdH q ψ f))))) :=
    State_ct hsq (by norm_num) (by norm_num) h5 (ctLvl_hbut q ψ 32 4 _ (by norm_num))
  have h7 : State ψ 128 2 1 f (ctLvl q ψ 64 2
      (ctLvl q ψ 32 4 (ctLvl q ψ 16 8 (ctLvl q ψ 8 16 (ctLvl q ψ 4 32 (fwdH q ψ f)))))) :=
    State_ct hsq (by norm_num) (by norm_num) h6 (ctLvl_hbut q ψ 64 2 _ (by norm_num))
  exact State_ct hsq (by norm_num) (by norm_num) h7 (ctLvl_hbut q ψ 128 1 _ (by norm_num))

open Kopis.CrtScheme.NttAlg in
/-- **The forward transform reaches the leaf state, at `q₁`.** -/
theorem ntt_block_State_q1 {N : Usize} (b : Array I16 N) (base : Usize) (f : ℕ → ZMod 7681)
    (hN : 8 * base.val + 256 ≤ N.val)
    (hb : ∀ p < N.val, fromVec base.val 0 p → |(b.val[p]!).val| ≤ 3840)
    (hf : ∀ c < 256, posZ 7681 b (8 * base.val + c) = f c) :
    backend.neon.ntt.ntt_block false b base
      ⦃ (r : Array I16 N) =>
          (∀ p < N.val, if fromVec base.val 0 p then |(r.val[p]!).val| ≤ 3840
            else (r.val[p]!).val = (b.val[p]!).val) ∧
          (∀ c < 256, posZ 7681 r (8 * base.val + c) = fwdAll 7681 zeta1 f c) ∧
          State zeta1 256 1 1 f (fwdAll 7681 zeta1 f) ⦄ := by
  apply WP.spec_mono (ntt_block_val_q1 b base f hN hb hf)
  exact fun r hr => ⟨hr.1, hr.2, fwdAll_State zeta1 zeta1_sq f⟩

open Kopis.CrtScheme.NttAlg in
/-- **The forward transform reaches the leaf state, at `q₂`.** -/
theorem ntt_block_State_q2 {N : Usize} (b : Array I16 N) (base : Usize) (f : ℕ → ZMod 10753)
    (hN : 8 * base.val + 256 ≤ N.val)
    (hb : ∀ p < N.val, fromVec base.val 0 p → |(b.val[p]!).val| ≤ 5376)
    (hf : ∀ c < 256, posZ 10753 b (8 * base.val + c) = f c) :
    backend.neon.ntt.ntt_block true b base
      ⦃ (r : Array I16 N) =>
          (∀ p < N.val, if fromVec base.val 0 p then |(r.val[p]!).val| ≤ 5376
            else (r.val[p]!).val = (b.val[p]!).val) ∧
          (∀ c < 256, posZ 10753 r (8 * base.val + c) = fwdAll 10753 zeta2 f c) ∧
          State zeta2 256 1 1 f (fwdAll 10753 zeta2 f) ⦄ := by
  apply WP.spec_mono (ntt_block_val_q2 b base f hN hb hf)
  exact fun r hr => ⟨hr.1, hr.2, fwdAll_State zeta2 zeta2_sq f⟩

end Kopis.Neon
