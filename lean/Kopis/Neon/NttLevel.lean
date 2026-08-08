/-
  # Kopis/Neon/NttLevel.lean — one whole-vector level of the forward transform, as a bound.

  The first five forward levels have `len ≥ 8`, so both halves of every butterfly are whole
  vectors and ψ is constant across a block.  `ntt_block`'s innermost loop walks `i` from `start`
  to `start + half`, pairing vector `i` with vector `i + half`.

  This file is that loop's *magnitude* behaviour, which is what the reduction schedule is checked
  against: a level takes a block bounded by `B` to one bounded by `B + Bt`, where `Bt` is the
  Montgomery bound `NttGrowth.lean` supplies.  Three such levels from `B = (q−1)/2` reach `2.75q`,
  inside the `3.05q` an `i16` lane holds, which is why `src/backend/neon/ntt.rs` re-centres after
  levels 3 and 6 rather than after 3 and 7 as AVX2 does — see §2(c).

  ## Why the hypothesis is about *pending* coefficients

  The obvious statement — "`BlockBnd b B` in, `BlockBnd r (B + Bt)` out" — does not induct: after
  one iteration the block is no longer bounded by `B`, so the next iteration's butterfly has
  nothing to stand on.  What *is* invariant is that the coefficients this pass has not reached
  yet are still bounded by `B`, and that everything outside the pass's range is untouched.  That
  is `pending` below, and it is the same shape every store loop in this stack uses, just with a
  two-interval range instead of one.
-/
import Kopis.Neon.Group

open Aeneas Aeneas.Std Result
open RustKopisNeon
open RustKopisNeon.backend.neon.intrinsics

namespace Kopis.Neon

set_option maxHeartbeats 1000000

/-- The coefficients the butterfly pass still has to reach, once it has advanced to vector `i`:
the two intervals `[i, start+half)` and `[i+half, start+2·half)`, in coefficients. -/
def pending (start half i p : ℕ) : Prop :=
  (8 * i ≤ p ∧ p < 8 * (start + half)) ∨
  (8 * (i + half) ≤ p ∧ p < 8 * (start + 2 * half))

instance (start half i p : ℕ) : Decidable (pending start half i p) := by
  unfold pending; infer_instance

/-- **One whole-vector level's butterfly pass, as a bound.**  Coefficients the pass reaches end
bounded by `B + Bt`; everything else is untouched. -/
theorem ntt_inner_bnd (b : Array I16 256#usize) (qv z zq : Vec128) (Q Zb B Bt : ℤ)
    (hQ : ∀ i < 8, (lane16 qv i).toInt = Q) (hQpos : 0 < Q) (hQlt : Q ≤ 2 ^ 14)
    (hz : ∀ i < 8, |(lane16 z i).toInt| ≤ Zb) (hZb : Zb ≤ 2 ^ 14)
    (hzq : ∀ i < 8, (2 ^ 16 : ℤ) ∣ ((lane16 zq i).toInt * Q - (lane16 z i).toInt))
    (hB0 : 0 ≤ B) (hBZ : B * Zb < 2 ^ 15 * Q) (hBt : B * Zb + 2 ^ 15 * Q ≤ 2 ^ 16 * Bt)
    (hfit : B + Bt ≤ 32767)
    (half start i : Usize) (hhalf : 1 ≤ half.val)
    (hrange : start.val + 2 * half.val ≤ 32) (hstart : start.val ≤ i.val)
    (hb : ∀ p < 256, pending start.val half.val i.val p → |(b.val[p]!).val| ≤ B) :
    backend.neon.ntt.ntt_block_loop0_loop0_loop0 b qv half start z zq i
      ⦃ (r : Array I16 256#usize) => ∀ p < 256,
          if pending start.val half.val i.val p then |(r.val[p]!).val| ≤ B + Bt
          else (r.val[p]!).val = (b.val[p]!).val ⦄ := by
  unfold backend.neon.ntt.ntt_block_loop0_loop0_loop0
  let* ⟨ i1, hi1 ⟩ ← Std.Usize.add_spec (x := start) (y := half) (by scalar_tac)
  by_cases hlt : i < i1
  · rw [if_pos hlt]
    have hiv : i.val < start.val + half.val := by scalar_tac
    -- the two halves of this butterfly, both still bounded by `B`
    obtain ⟨lo, hlo, hlol⟩ := load_i16_val b i (by omega)
    rw [hlo, bind_tc_ok]
    let* ⟨ i2, hi2 ⟩ ← Std.Usize.add_spec (x := i) (y := half) (by scalar_tac)
    obtain ⟨hiv2, -⟩ : i2.val = i.val + half.val ∧ True := ⟨by scalar_tac, trivial⟩
    obtain ⟨hi', hhi, hhil⟩ := load_i16_val b i2 (by omega)
    rw [hhi, bind_tc_ok]
    have hlob : VecBnd lo B := by
      intro k hk
      rw [hlol k hk]
      exact hb _ (by omega) (Or.inl ⟨by omega, by omega⟩)
    have hhib : VecBnd hi' B := by
      intro k hk
      rw [hhil k hk, hiv2]
      exact hb _ (by omega) (Or.inr ⟨by omega, by omega⟩)
    apply WP.spec_bind (ct_butterfly_spec lo hi' z zq qv Q Zb B Bt hQ hQpos hQlt hz hZb hzq
      hlob hhib hB0 hBZ hBt hfit)
    rintro ⟨lo1, hi1'⟩ ⟨hlo1b, hhi1b, -⟩
    show (do let b1 ← backend.neon.intrinsics.store_i16 b i lo1
             let b2 ← backend.neon.intrinsics.store_i16 b1 i2 hi1'
             let i3 ← i + 1#usize
             backend.neon.ntt.ntt_block_loop0_loop0_loop0 b2 qv half start z zq i3)
        ⦃ (r : Array I16 256#usize) => ∀ p < 256,
            if pending start.val half.val i.val p then |(r.val[p]!).val| ≤ B + Bt
            else (r.val[p]!).val = (b.val[p]!).val ⦄
    obtain ⟨b1, hb1, hb1v⟩ := store_i16_val b i lo1 (by omega)
    rw [hb1, bind_tc_ok]
    obtain ⟨b2, hb2, hb2v⟩ := store_i16_val b1 i2 hi1' (by omega)
    rw [hb2, bind_tc_ok]
    let* ⟨ i3, hi3 ⟩ ← Std.Usize.add_spec (x := i) (y := 1#usize) (by scalar_tac)
    -- what `b2` looks like, in one statement
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
    -- the pending coefficients of the *next* iteration are still bounded by `B`
    apply WP.spec_mono (ntt_inner_bnd b2 qv z zq Q Zb B Bt hQ hQpos hQlt hz hZb hzq hB0 hBZ hBt
      hfit half start i3 hhalf hrange (by scalar_tac) (by
        intro p hp hpend
        rw [hb2all p hp, if_neg (by unfold pending at hpend; scalar_tac),
          if_neg (by unfold pending at hpend; scalar_tac)]
        exact hb p hp (by unfold pending at hpend ⊢; scalar_tac)))
    intro r hr p hp
    have hrp := hr p hp
    by_cases hpend : pending start.val half.val i.val p
    · rw [if_pos hpend]
      by_cases hnext : pending start.val half.val i3.val p
      · rw [if_pos hnext] at hrp
        exact hrp
      · rw [if_neg hnext, hb2all p hp] at hrp
        rw [hrp]
        by_cases h1 : 8 * i.val ≤ p ∧ p < 8 * i.val + 8
        · rw [if_pos h1]
          exact hlo1b _ (by omega)
        · rw [if_neg h1]
          have h2 : 8 * i2.val ≤ p ∧ p < 8 * i2.val + 8 := by
            unfold pending at hpend hnext; scalar_tac
          rw [if_pos h2]
          exact hhi1b _ (by omega)
    · rw [if_neg hpend]
      rw [if_neg (by unfold pending at hpend ⊢; scalar_tac), hb2all p hp,
        if_neg (by unfold pending at hpend; scalar_tac),
        if_neg (by unfold pending at hpend; scalar_tac)] at hrp
      exact hrp
  · rw [if_neg hlt]
    refine (WP.spec_ok _).mpr (fun p hp => ?_)
    rw [if_neg (by unfold pending; scalar_tac)]
termination_by (start.val + half.val) - i.val
decreasing_by scalar_decr_tac

/-! ## The blocks of one level

`start` walks the block boundaries in steps of `2·half`, taking a fresh ψ from the ζ table each
time.  The two intervals `ntt_inner_bnd` leaves bounded are adjacent — `[start, start+half)` and
`[start+half, start+2·half)` — so a whole block comes out bounded and the invariant collapses to
"everything from `8·start` on". -/

theorem ntt_start_bnd (SECOND : Bool) (b : Array I16 256#usize) (qv : Vec128) (Q Zb B Bt : ℤ)
    (hQ : ∀ i < 8, (lane16 qv i).toInt = Q) (hQpos : 0 < Q) (hQlt : Q ≤ 2 ^ 14)
    (hZb : Zb ≤ 2 ^ 14)
    (hB0 : 0 ≤ B) (hBZ : B * Zb < 2 ^ 15 * Q) (hBt : B * Zb + 2 ^ 15 * Q ≤ 2 ^ 16 * Bt)
    (hfit : B + Bt ≤ 32767)
    (hzeta : ∀ kk : Usize, kk.val < 256 → ∃ zi zqi : I16,
        backend.crt.zeta SECOND kk = ok zi ∧ backend.crt.zeta_q SECOND kk = ok zqi ∧
        |zi.val| ≤ Zb ∧ (2 ^ 16 : ℤ) ∣ (zqi.val * Q - zi.val))
    (k half start : Usize) (hhalf : 1 ≤ half.val) (hhalfdvd : 2 * half.val ∣ 32)
    (hdvd : 2 * half.val ∣ start.val) (hk : k.val + (32 - start.val) ≤ 255)
    (hb : ∀ p < 256, 8 * start.val ≤ p → |(b.val[p]!).val| ≤ B) :
    backend.neon.ntt.ntt_block_loop0_loop0 SECOND b qv k half start
      ⦃ (r : Array I16 256#usize × Usize) =>
          r.2.val ≤ k.val + (32 - start.val) ∧ ∀ p < 256,
            if 8 * start.val ≤ p then |(r.1.val[p]!).val| ≤ B + Bt
            else (r.1.val[p]!).val = (b.val[p]!).val ⦄ := by
  unfold backend.neon.ntt.ntt_block_loop0_loop0
  have hvecs : backend.neon.ntt.VECS = ok 32#usize := by
    simp only [backend.neon.ntt.VECS, consts.RING_DEG]; rfl
  rw [hvecs, bind_tc_ok]
  by_cases hlt : start < 32#usize
  · rw [if_pos hlt]
    have hs32 : start.val < 32 := by scalar_tac
    have hh16 : 2 * half.val ≤ 32 := Nat.le_of_dvd (by omega) hhalfdvd
    have hfits : start.val + 2 * half.val ≤ 32 := by
      obtain ⟨c, hc⟩ := hdvd
      obtain ⟨d, hd⟩ := hhalfdvd
      have hcd : c + 1 ≤ d := by
        by_contra hcon
        have hdc : d ≤ c := by omega
        have : 2 * half.val * d ≤ 2 * half.val * c := Nat.mul_le_mul_left _ hdc
        omega
      have hmul : 2 * half.val * (c + 1) ≤ 2 * half.val * d := Nat.mul_le_mul_left _ hcd
      calc start.val + 2 * half.val = 2 * half.val * (c + 1) := by rw [hc]; ring
        _ ≤ 2 * half.val * d := hmul
        _ = 32 := hd.symm
    let* ⟨ k1, hk1 ⟩ ← Std.Usize.add_spec (x := k) (y := 1#usize) (by scalar_tac)
    obtain ⟨zi, zqi, hzi, hzqi, hzib, hzqib⟩ := hzeta k1 (by scalar_tac)
    rw [hzi, bind_tc_ok]
    obtain ⟨z, hz, hzl⟩ := dup_n_s16_spec zi
    rw [hz, bind_tc_ok, hzqi, bind_tc_ok]
    obtain ⟨zq, hzq, hzql⟩ := dup_n_s16_spec zqi
    rw [hzq, bind_tc_ok]
    have hzlv : ∀ i < 8, |(lane16 z i).toInt| ≤ Zb := by
      intro i hi; rw [hzl i hi]; exact hzib
    have hzqlv : ∀ i < 8, (2 ^ 16 : ℤ) ∣ ((lane16 zq i).toInt * Q - (lane16 z i).toInt) := by
      intro i hi; rw [hzl i hi, hzql i hi]; exact hzqib
    apply WP.spec_bind (ntt_inner_bnd b qv z zq Q Zb B Bt hQ hQpos hQlt hzlv hZb hzqlv hB0 hBZ
      hBt hfit half start start hhalf hfits (le_refl _) (by
        intro p hp hpend
        exact hb p hp (by unfold pending at hpend; omega)))
    intro b1 hb1
    let* ⟨ i3, hi3 ⟩ ← Std.Usize.mul_spec (x := 2#usize) (y := half) (by scalar_tac)
    let* ⟨ start1, hstart1 ⟩ ← Std.Usize.add_spec (x := start) (y := i3) (by scalar_tac)
    have hs1v : start1.val = start.val + 2 * half.val := by scalar_tac
    apply WP.spec_mono (ntt_start_bnd SECOND b1 qv Q Zb B Bt hQ hQpos hQlt hZb hB0 hBZ hBt hfit
      hzeta k1 half start1 hhalf hhalfdvd (by rw [hs1v]; exact Nat.dvd_add hdvd dvd_rfl)
      (by scalar_tac) (by
        intro p hp hge
        have := hb1 p hp
        rw [if_neg (by unfold pending; omega)] at this
        rw [this]
        exact hb p hp (by omega)))
    rintro ⟨r, kk⟩ ⟨hkk, hr⟩
    refine ⟨by scalar_tac, fun p hp => ?_⟩
    have hrp := hr p hp
    by_cases hge : 8 * start.val ≤ p
    · rw [if_pos hge]
      by_cases hge1 : 8 * start1.val ≤ p
      · rw [if_pos hge1] at hrp
        exact hrp
      · rw [if_neg hge1] at hrp
        rw [hrp]
        have := hb1 p hp
        rw [if_pos (by unfold pending; omega)] at this
        exact this
    · rw [if_neg hge]
      rw [if_neg (by omega)] at hrp
      rw [hrp]
      have := hb1 p hp
      rw [if_neg (by unfold pending; omega)] at this
      exact this
  · rw [if_neg hlt]
    refine (WP.spec_ok _).mpr ⟨by scalar_tac, fun p hp => ?_⟩
    rw [if_neg (by scalar_tac)]
termination_by 32 - start.val
decreasing_by scalar_decr_tac

/-! ## The schedule arithmetic

This is the claim `src/backend/crt.rs` and `src/backend/neon/ntt.rs` make in prose.  A
Cooley-Tukey level takes a bound `A` to `A + T` where `2¹⁶·T ≥ A·Zb + 2¹⁵·q` — that is
`ct_butterfly_spec` — and `T` is proportional to `A`, which is why the levels compound.  From a
centred block with `|ψ| ≤ q/2`:

* `q₂ = 10753`: `5376 → 11194 → 17489 → 24301`;
* `q₁ = 7681`:  `3840 → 7906 → 12210 → 16766`.

**Three** steps, not four.  That is the whole difference from AVX2, whose chains these are a
prefix of: `src/backend/neon/ntt.rs` re-centres after levels 3 and 6, so its runs are three long,
and three flat `+0.75·q₂` steps would reach `29440` — inside the lane.  So unlike AVX2's
four-level run, the NEON schedule *is* justified by the crude budget, exactly as §2(c) says; the
sharp chain below is recorded because it is what the proof actually uses and because it shows how
much room is left (`24301` against `32767`).

Each `T` is the least integer satisfying the `ct_butterfly_spec` premise at that level, so the
chain is tight. -/

/-- One level's growth, as `ct_butterfly_spec` needs it. -/
def LevelStep (Q Zb A T : ℤ) : Prop :=
  A * Zb < 2 ^ 15 * Q ∧ A * Zb + 2 ^ 15 * Q ≤ 2 ^ 16 * T ∧ A + T ≤ 2 ^ 15 - 1

/-- **The three-level run fits, for `q₂ = 10753`** — the binding prime. -/
theorem growth_q2 :
    LevelStep 10753 5376 5376 5818 ∧ LevelStep 10753 5376 11194 6295 ∧
    LevelStep 10753 5376 17489 6812 ∧ (17489 : ℤ) + 6812 = 24301 ∧ (24301 : ℤ) ≤ 32767 := by
  refine ⟨⟨by norm_num, by norm_num, by norm_num⟩, ⟨by norm_num, by norm_num, by norm_num⟩,
    ⟨by norm_num, by norm_num, by norm_num⟩, by norm_num, by norm_num⟩

/-- **The three-level run fits, for `q₁ = 7681`.** -/
theorem growth_q1 :
    LevelStep 7681 3840 3840 4066 ∧ LevelStep 7681 3840 7906 4304 ∧
    LevelStep 7681 3840 12210 4556 ∧ (12210 : ℤ) + 4556 = 16766 ∧ (16766 : ℤ) ≤ 32767 := by
  refine ⟨⟨by norm_num, by norm_num, by norm_num⟩, ⟨by norm_num, by norm_num, by norm_num⟩,
    ⟨by norm_num, by norm_num, by norm_num⟩, by norm_num, by norm_num⟩

/-- **The crude budget covers this schedule** — which is the difference from AVX2.  Three flat
`+0.75·q₂` steps from `q₂/2` stay inside an `i16` lane; the fourth, which AVX2's schedule needs,
would not. -/
theorem crude_budget_suffices :
    (5376 : ℤ) + 3 * (3 * 10753 / 4) ≤ 32767 ∧ (5376 : ℤ) + 4 * (3 * 10753 / 4) > 32767 := by
  constructor <;> norm_num

/-! ## The five whole-vector levels

`ntt_block_loop0` runs `half = 16, 8, 4, 2, 1` with `level = 0 … 4`, re-centring after
`level = 2` — the third — which is the "runs of 3, 3, 2" schedule `ntt.rs` documents.  The loop
is unrolled here rather than inducted over: `half` takes five concrete values and the schedule
differs between them, so there is no invariant to induct on that is not just the list.

`A0 … A5` are the chain; `growth_q1` and `growth_q2` supply them. -/

theorem usize_add_one (a c : Usize) (h : a.val + 1 = c.val) : a + 1#usize = ok c := by
  obtain ⟨v, hv, hvv⟩ :=
    WP.spec_imp_exists (Std.Usize.add_spec (x := a) (y := 1#usize) (by scalar_tac))
  rw [hv]
  congr 1
  exact UScalar.eq_of_val_eq (by scalar_tac)

theorem blockBnd_of_start {r bb : Array I16 256#usize} {B' : ℤ}
    (h : ∀ p < 256, if 8 * (0#usize).val ≤ p then |(r.val[p]!).val| ≤ B'
                    else (r.val[p]!).val = (bb.val[p]!).val) : BlockBnd r B' := by
  intro p hp
  have := h p hp
  rwa [if_pos (by scalar_tac)] at this


theorem ntt_horizontal_bnd (SECOND : Bool) (b : Array I16 256#usize) (qv bm round : Vec128)
    (Q Zb M A0 A1 A2 A3 A4 A5 : ℤ)
    (hQ : ∀ i < 8, (lane16 qv i).toInt = Q) (hQpos : 0 < Q) (hQ14 : Q < 2 ^ 14)
    (hQodd : ¬ (2 ∣ Q)) (hZb : Zb ≤ 2 ^ 14)
    (hM : ∀ i < 8, (lane16 bm i).toInt = M) (hMpos : 0 < M) (hMlt : M < 2 ^ 15)
    (hD : |2 ^ 27 - Q * M| ≤ 2047)
    (hRnd : ∀ i < 8, (lane16 round i).toInt = 2 ^ 10)
    (hzeta : ∀ kk : Usize, kk.val < 256 → ∃ zi zqi : I16,
        backend.crt.zeta SECOND kk = ok zi ∧ backend.crt.zeta_q SECOND kk = ok zqi ∧
        |zi.val| ≤ Zb ∧ (2 ^ 16 : ℤ) ∣ (zqi.val * Q - zi.val))
    (hA0 : 0 ≤ A0) (hA1 : 0 ≤ A1) (hA2 : 0 ≤ A2) (hA4 : 0 ≤ A4)
    (hreset : (Q - 1) / 2 ≤ A0)
    (hs0 : LevelStep Q Zb A0 (A1 - A0)) (hs1 : LevelStep Q Zb A1 (A2 - A1))
    (hs2 : LevelStep Q Zb A2 (A3 - A2))
    (hs3 : LevelStep Q Zb A0 (A4 - A0)) (hs4 : LevelStep Q Zb A4 (A5 - A4))
    (hb : BlockBnd b A0) :
    backend.neon.ntt.ntt_block_loop0 SECOND b qv bm round 0#usize 16#usize 0#usize
      ⦃ (r : Array I16 256#usize) => BlockBnd r A5 ⦄ := by
  have hQ14' : Q ≤ 2 ^ 14 := by omega

  -- level 0: half = 16
  unfold backend.neon.ntt.ntt_block_loop0
  rw [if_pos (show (1#usize : Usize) ≤ 16#usize by decide)]
  apply WP.spec_bind (ntt_start_bnd SECOND b qv Q Zb A0 (A1 - A0) hQ hQpos hQ14'
    hZb (by omega) hs0.1 hs0.2.1 hs0.2.2 hzeta 0#usize 16#usize 0#usize (by decide)
    (by decide) (by decide) (by scalar_tac) (by intro p hp _; exact hb p hp))
  rintro ⟨b1, k1⟩ ⟨hkb1, hsb1⟩
  show (do let b2 ← if (0#usize : Usize) = 2#usize
                    then backend.neon.ntt.barrett_block b1 bm round qv else ok b1
           let half1 ← (16#usize : Usize) / 2#usize
           let level1 ← (0#usize : Usize) + 1#usize
           backend.neon.ntt.ntt_block_loop0 SECOND b2 qv bm round k1 half1 level1)
      ⦃ (r : Array I16 256#usize) => BlockBnd r A5 ⦄
  rw [if_neg (by decide), bind_tc_ok,
    show (16#usize : Usize) / 2#usize = ok 8#usize from by rfl, bind_tc_ok,
    usize_add_one (0#usize) (1#usize) (by scalar_tac), bind_tc_ok]
  have hb1 : BlockBnd b1 A1 := (blockBnd_of_start hsb1).mono (by omega)

  -- level 1: half = 8
  unfold backend.neon.ntt.ntt_block_loop0
  rw [if_pos (show (1#usize : Usize) ≤ 8#usize by decide)]
  apply WP.spec_bind (ntt_start_bnd SECOND b1 qv Q Zb A1 (A2 - A1) hQ hQpos hQ14'
    hZb (by omega) hs1.1 hs1.2.1 hs1.2.2 hzeta k1 8#usize 0#usize (by decide)
    (by decide) (by decide) (by scalar_tac) (by intro p hp _; exact hb1 p hp))
  rintro ⟨b2, k2⟩ ⟨hkb2, hsb2⟩
  show (do let b2 ← if (1#usize : Usize) = 2#usize
                    then backend.neon.ntt.barrett_block b2 bm round qv else ok b2
           let half1 ← (8#usize : Usize) / 2#usize
           let level1 ← (1#usize : Usize) + 1#usize
           backend.neon.ntt.ntt_block_loop0 SECOND b2 qv bm round k2 half1 level1)
      ⦃ (r : Array I16 256#usize) => BlockBnd r A5 ⦄
  rw [if_neg (by decide), bind_tc_ok,
    show (8#usize : Usize) / 2#usize = ok 4#usize from by rfl, bind_tc_ok,
    usize_add_one (1#usize) (2#usize) (by scalar_tac), bind_tc_ok]
  have hb2 : BlockBnd b2 A2 := (blockBnd_of_start hsb2).mono (by omega)

  -- level 2: half = 4, and the re-centring pass the schedule calls for
  unfold backend.neon.ntt.ntt_block_loop0
  rw [if_pos (show (1#usize : Usize) ≤ 4#usize by decide)]
  apply WP.spec_bind (ntt_start_bnd SECOND b2 qv Q Zb A2 (A3 - A2) hQ hQpos hQ14'
    hZb (by omega) hs2.1 hs2.2.1 hs2.2.2 hzeta k2 4#usize 0#usize (by decide)
    (by decide) (by decide) (by scalar_tac) (by intro p hp _; exact hb2 p hp))
  rintro ⟨b3, k3⟩ ⟨hkb3, hsb3⟩
  show (do let b2' ← if (2#usize : Usize) = 2#usize
                     then backend.neon.ntt.barrett_block b3 bm round qv else ok b3
           let half1 ← (4#usize : Usize) / 2#usize
           let level1 ← (2#usize : Usize) + 1#usize
           backend.neon.ntt.ntt_block_loop0 SECOND b2' qv bm round k3 half1 level1)
      ⦃ (r : Array I16 256#usize) => BlockBnd r A5 ⦄
  rw [if_pos rfl]
  apply WP.spec_bind (barrett_block_spec b3 bm round qv Q M hQ hM hRnd hQpos hQ14 hQodd hMpos
    hMlt hD)
  rintro b3' ⟨hb3'bnd, -⟩
  show (do let half1 ← (4#usize : Usize) / 2#usize
           let level1 ← (2#usize : Usize) + 1#usize
           backend.neon.ntt.ntt_block_loop0 SECOND b3' qv bm round k3 half1 level1)
      ⦃ (r : Array I16 256#usize) => BlockBnd r A5 ⦄
  rw [show (4#usize : Usize) / 2#usize = ok 2#usize from by rfl, bind_tc_ok,
    usize_add_one (2#usize) (3#usize) (by scalar_tac), bind_tc_ok]
  have hb3' : BlockBnd b3' A0 := hb3'bnd.mono hreset

  -- level 3: half = 2
  unfold backend.neon.ntt.ntt_block_loop0
  rw [if_pos (show (1#usize : Usize) ≤ 2#usize by decide)]
  apply WP.spec_bind (ntt_start_bnd SECOND b3' qv Q Zb A0 (A4 - A0) hQ hQpos hQ14'
    hZb (by omega) hs3.1 hs3.2.1 hs3.2.2 hzeta k3 2#usize 0#usize (by decide)
    (by decide) (by decide) (by scalar_tac) (by intro p hp _; exact hb3' p hp))
  rintro ⟨b4, k4⟩ ⟨hkb4, hsb4⟩
  show (do let b2 ← if (3#usize : Usize) = 2#usize
                    then backend.neon.ntt.barrett_block b4 bm round qv else ok b4
           let half1 ← (2#usize : Usize) / 2#usize
           let level1 ← (3#usize : Usize) + 1#usize
           backend.neon.ntt.ntt_block_loop0 SECOND b2 qv bm round k4 half1 level1)
      ⦃ (r : Array I16 256#usize) => BlockBnd r A5 ⦄
  rw [if_neg (by decide), bind_tc_ok,
    show (2#usize : Usize) / 2#usize = ok 1#usize from by rfl, bind_tc_ok,
    usize_add_one (3#usize) (4#usize) (by scalar_tac), bind_tc_ok]
  have hb4 : BlockBnd b4 A4 := (blockBnd_of_start hsb4).mono (by omega)

  -- level 4: half = 1
  unfold backend.neon.ntt.ntt_block_loop0
  rw [if_pos (show (1#usize : Usize) ≤ 1#usize by decide)]
  apply WP.spec_bind (ntt_start_bnd SECOND b4 qv Q Zb A4 (A5 - A4) hQ hQpos hQ14'
    hZb (by omega) hs4.1 hs4.2.1 hs4.2.2 hzeta k4 1#usize 0#usize (by decide)
    (by decide) (by decide) (by scalar_tac) (by intro p hp _; exact hb4 p hp))
  rintro ⟨b5, k5⟩ ⟨hkb5, hsb5⟩
  show (do let b2 ← if (4#usize : Usize) = 2#usize
                    then backend.neon.ntt.barrett_block b5 bm round qv else ok b5
           let half1 ← (1#usize : Usize) / 2#usize
           let level1 ← (4#usize : Usize) + 1#usize
           backend.neon.ntt.ntt_block_loop0 SECOND b2 qv bm round k5 half1 level1)
      ⦃ (r : Array I16 256#usize) => BlockBnd r A5 ⦄
  rw [if_neg (by decide), bind_tc_ok,
    show (1#usize : Usize) / 2#usize = ok 0#usize from by rfl, bind_tc_ok,
    usize_add_one (4#usize) (5#usize) (by scalar_tac), bind_tc_ok]
  have hb5 : BlockBnd b5 A5 := (blockBnd_of_start hsb5).mono (by omega)

  -- half = 0: the loop stops
  unfold backend.neon.ntt.ntt_block_loop0
  rw [if_neg (by decide)]
  exact (WP.spec_ok _).mpr hb5

end Kopis.Neon
