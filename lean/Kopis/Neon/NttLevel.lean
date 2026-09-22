/-
  # Kopis/Neon/NttLevel.lean — one whole-vector level of the forward transform, as a bound.

  The first two forward levels pair vectors 16 and 8 apart, which crosses the group of eight
  vectors the rest of the transform is blocked over, so they — and only they — walk the whole
  block.  `ntt_block`'s innermost loop walks `i` from `start` to `start + half`, pairing vector
  `i` with vector `i + half`.

  This file is that loop's *magnitude* behaviour, which is what the reduction schedule is checked
  against: a level takes a block bounded by `B` to one bounded by `B + Bt`, where `Bt` is the
  Montgomery bound `NttGrowth.lean` supplies.  Four such levels from `B = (q−1)/2` reach `2.95q`,
  inside the `3.05q` an `i16` lane holds, which is why `src/backend/neon/ntt.rs` re-centres after
  levels 3 and 7; the first two of those four levels are here and the other two are in the group
  loop.

  ## The window

  The forward transform runs in place inside a longer buffer — `split_and_transform` hands it the
  whole `[i16; 512]` and the vector index `base` at which this prime's half starts — so every
  statement below is about the 256 coefficients from `8·base`, and says that everything outside
  them is untouched.  `pendingAt` and `fromVec` are the two window predicates that carry that.

  ## Why the hypothesis is about *pending* coefficients

  The obvious statement — "bounded by `B` in, bounded by `B + Bt` out" — does not induct: after
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
the two intervals `[i, start+half)` and `[i+half, start+2·half)`, in coefficients, relative to
the start of the window. -/
def pending (start half i p : ℕ) : Prop :=
  (8 * i ≤ p ∧ p < 8 * (start + half)) ∨
  (8 * (i + half) ≤ p ∧ p < 8 * (start + 2 * half))

instance (start half i p : ℕ) : Decidable (pending start half i p) := by
  unfold pending; infer_instance

/-- `pending`, as a predicate on an absolute index into the enclosing buffer. -/
def pendingAt (base start half i p : ℕ) : Prop :=
  8 * base ≤ p ∧ p < 8 * base + 256 ∧ pending start half i (p - 8 * base)

instance (base start half i p : ℕ) : Decidable (pendingAt base start half i p) := by
  unfold pendingAt; infer_instance

/-- The window's coefficients from vector `start` on, as absolute indices.  `fromVec base 0` is
the whole window. -/
def fromVec (base start p : ℕ) : Prop := 8 * base + 8 * start ≤ p ∧ p < 8 * base + 256

instance (base start p : ℕ) : Decidable (fromVec base start p) := by
  unfold fromVec; infer_instance

/-- **One whole-vector level's butterfly pass, as a bound.**  Coefficients the pass reaches end
bounded by `B + Bt`; everything else, inside the window or out of it, is untouched. -/
theorem ntt_inner_bnd {N : Usize} (b : Array I16 N) (base : Usize) (qv z zq : Vec128)
    (Q Zb B Bt : ℤ)
    (hQ : ∀ i < 8, (lane16 qv i).toInt = Q) (hQpos : 0 < Q) (hQlt : Q ≤ 2 ^ 14)
    (hz : ∀ i < 8, |(lane16 z i).toInt| ≤ Zb) (hZb : Zb ≤ 2 ^ 14)
    (hzq : ∀ i < 8, (2 ^ 16 : ℤ) ∣ ((lane16 zq i).toInt * Q - (lane16 z i).toInt))
    (hB0 : 0 ≤ B) (hBZ : B * Zb < 2 ^ 15 * Q) (hBt : B * Zb + 2 ^ 15 * Q ≤ 2 ^ 16 * Bt)
    (hfit : B + Bt ≤ 32767) (hN : 8 * base.val + 256 ≤ N.val)
    (half start i : Usize) (hhalf : 1 ≤ half.val)
    (hrange : start.val + 2 * half.val ≤ 32) (hstart : start.val ≤ i.val)
    (hb : ∀ p < N.val, pendingAt base.val start.val half.val i.val p →
      |(b.val[p]!).val| ≤ B) :
    backend.neon.ntt.ntt_block_loop0_loop0_loop0 b base qv half start z zq i
      ⦃ (r : Array I16 N) => ∀ p < N.val,
          if pendingAt base.val start.val half.val i.val p then |(r.val[p]!).val| ≤ B + Bt
          else (r.val[p]!).val = (b.val[p]!).val ⦄ := by
  have hNmax : N.val ≤ Usize.max := by scalar_tac
  unfold backend.neon.ntt.ntt_block_loop0_loop0_loop0
  let* ⟨ i1, hi1 ⟩ ← Std.Usize.add_spec (x := start) (y := half) (by scalar_tac)
  by_cases hlt : i < i1
  · rw [if_pos hlt]
    have hiv : i.val < start.val + half.val := by scalar_tac
    let* ⟨ i2, hi2 ⟩ ← Std.Usize.add_spec (x := base) (y := i) (by omega)
    have hi2v : i2.val = base.val + i.val := by scalar_tac
    -- the two halves of this butterfly, both still bounded by `B`
    obtain ⟨lo, hlo, hlol⟩ := load_i16_gen b i2 (by omega)
    rw [hlo, bind_tc_ok]
    let* ⟨ i3, hi3 ⟩ ← Std.Usize.add_spec (x := i2) (y := half) (by omega)
    have hi3v : i3.val = base.val + i.val + half.val := by scalar_tac
    obtain ⟨hi', hhi, hhil⟩ := load_i16_gen b i3 (by omega)
    rw [hhi, bind_tc_ok]
    have hlob : VecBnd lo B := by
      intro k hk
      rw [hlol k hk, hi2v]
      exact hb _ (by omega) ⟨by omega, by omega, Or.inl ⟨by omega, by omega⟩⟩
    have hhib : VecBnd hi' B := by
      intro k hk
      rw [hhil k hk, hi3v]
      exact hb _ (by omega) ⟨by omega, by omega, Or.inr ⟨by omega, by omega⟩⟩
    apply WP.spec_bind (ct_butterfly_spec lo hi' z zq qv Q Zb B Bt hQ hQpos hQlt hz hZb hzq
      hlob hhib hB0 hBZ hBt hfit)
    rintro ⟨lo1, hi1'⟩ ⟨hlo1b, hhi1b, -⟩
    show (do let b1 ← backend.neon.intrinsics.store_i16 b i2 lo1
             let i4 ← i2 + half
             let b2 ← backend.neon.intrinsics.store_i16 b1 i4 hi1'
             let i5 ← i + 1#usize
             backend.neon.ntt.ntt_block_loop0_loop0_loop0 b2 base qv half start z zq i5)
        ⦃ (r : Array I16 N) => ∀ p < N.val,
            if pendingAt base.val start.val half.val i.val p then |(r.val[p]!).val| ≤ B + Bt
            else (r.val[p]!).val = (b.val[p]!).val ⦄
    obtain ⟨b1, hb1, hb1v⟩ := store_i16_gen b i2 lo1 (by omega)
    rw [hb1, bind_tc_ok]
    let* ⟨ i4, hi4 ⟩ ← Std.Usize.add_spec (x := i2) (y := half) (by omega)
    have hi4v : i4.val = base.val + i.val + half.val := by scalar_tac
    obtain ⟨b2, hb2, hb2v⟩ := store_i16_gen b1 i4 hi1' (by omega)
    rw [hb2, bind_tc_ok]
    let* ⟨ i5, hi5 ⟩ ← Std.Usize.add_spec (x := i) (y := 1#usize) (by scalar_tac)
    -- what `b2` looks like, in one statement
    have hb2all : ∀ p < N.val, (b2.val[p]!).val =
        if 8 * i2.val ≤ p ∧ p < 8 * i2.val + 8 then (lane16 lo1 (p - 8 * i2.val)).toInt
        else if 8 * i4.val ≤ p ∧ p < 8 * i4.val + 8 then
          (lane16 hi1' (p - 8 * i4.val)).toInt
        else (b.val[p]!).val := by
      intro p hp
      rw [hb2v p hp, hb1v p hp]
      by_cases h2 : 8 * i4.val ≤ p ∧ p < 8 * i4.val + 8
      · rw [if_pos h2, if_neg (by omega), if_pos h2]
      · rw [if_neg h2, if_neg h2]
    -- the pending coefficients of the *next* iteration are still bounded by `B`
    apply WP.spec_mono (ntt_inner_bnd b2 base qv z zq Q Zb B Bt hQ hQpos hQlt hz hZb hzq hB0 hBZ
      hBt hfit hN half start i5 hhalf hrange (by scalar_tac) (by
        intro p hp hpend
        rw [hb2all p hp, if_neg (by unfold pendingAt pending at hpend; omega),
          if_neg (by unfold pendingAt pending at hpend; omega)]
        exact hb p hp (by unfold pendingAt pending at hpend ⊢; omega)))
    intro r hr p hp
    have hrp := hr p hp
    by_cases hpend : pendingAt base.val start.val half.val i.val p
    · rw [if_pos hpend]
      by_cases hnext : pendingAt base.val start.val half.val i5.val p
      · rw [if_pos hnext] at hrp
        exact hrp
      · rw [if_neg hnext, hb2all p hp] at hrp
        rw [hrp]
        by_cases h1 : 8 * i2.val ≤ p ∧ p < 8 * i2.val + 8
        · rw [if_pos h1]
          exact hlo1b _ (by omega)
        · rw [if_neg h1]
          have h2 : 8 * i4.val ≤ p ∧ p < 8 * i4.val + 8 := by
            unfold pendingAt pending at hpend hnext; omega
          rw [if_pos h2]
          exact hhi1b _ (by omega)
    · rw [if_neg hpend]
      rw [if_neg (by unfold pendingAt pending at hpend ⊢; omega), hb2all p hp,
        if_neg (by unfold pendingAt pending at hpend; omega),
        if_neg (by unfold pendingAt pending at hpend; omega)] at hrp
      exact hrp
  · rw [if_neg hlt]
    refine (WP.spec_ok _).mpr (fun p hp => ?_)
    rw [if_neg (by unfold pendingAt pending; scalar_tac)]
termination_by (start.val + half.val) - i.val
decreasing_by scalar_decr_tac

/-! ## The blocks of one level

`start` walks the block boundaries in steps of `2·half`, taking a fresh ψ from the ζ table each
time.  The two intervals `ntt_inner_bnd` leaves bounded are adjacent — `[start, start+half)` and
`[start+half, start+2·half)` — so a whole block comes out bounded and the invariant collapses to
"everything from vector `start` on". -/

/-! ## The schedule arithmetic

This is the claim `src/backend/neon/ntt.rs` makes in prose.  A Cooley-Tukey level takes a bound
`A` to `A + T` where `2¹⁶·T ≥ A·Zb + 2¹⁵·q` — that is `ct_butterfly_spec` — and `T` is
proportional to `A`, which is why the levels compound.  From a centred block with `|ψ| ≤ q/2`:

* `q₂ = 10753`: `5376 → 11194 → 17489 → 24301 → 31671`;
* `q₁ = 7681`:  `3840 → 7906 → 12210 → 16766 → 21589`.

**Four** steps.  The crude 0.75q-per-level budget in `src/arithmetic/ntt_crt.rs` does not cover four —
it reaches `37635` for `q₂`, outside an `i16` lane — so unlike the three-level schedule this
replaces, the run rests on the sharp chain above and on nothing else.  `31671` against `32767`
is the whole margin, and `forward_growth_fits_an_i16_lane` in the Rust re-derives it on every
test run so that a fifth level cannot quietly start to fit.

Each `T` is the least integer satisfying the `ct_butterfly_spec` premise at that level, so the
chain is tight. -/

/-- One level's growth, as `ct_butterfly_spec` needs it. -/
def LevelStep (Q Zb A T : ℤ) : Prop :=
  A * Zb < 2 ^ 15 * Q ∧ A * Zb + 2 ^ 15 * Q ≤ 2 ^ 16 * T ∧ A + T ≤ 2 ^ 15 - 1

/-- **The four-level run fits, for `q₂ = 10753`** — the binding prime. -/
theorem growth_q2 :
    LevelStep 10753 5376 5376 5818 ∧ LevelStep 10753 5376 11194 6295 ∧
    LevelStep 10753 5376 17489 6812 ∧ LevelStep 10753 5376 24301 7370 ∧
    (24301 : ℤ) + 7370 = 31671 ∧ (31671 : ℤ) ≤ 32767 := by
  refine ⟨⟨by norm_num, by norm_num, by norm_num⟩, ⟨by norm_num, by norm_num, by norm_num⟩,
    ⟨by norm_num, by norm_num, by norm_num⟩, ⟨by norm_num, by norm_num, by norm_num⟩,
    by norm_num, by norm_num⟩

/-- **The four-level run fits, for `q₁ = 7681`.** -/
theorem growth_q1 :
    LevelStep 7681 3840 3840 4066 ∧ LevelStep 7681 3840 7906 4304 ∧
    LevelStep 7681 3840 12210 4556 ∧ LevelStep 7681 3840 16766 4823 ∧
    (16766 : ℤ) + 4823 = 21589 ∧ (21589 : ℤ) ≤ 32767 := by
  refine ⟨⟨by norm_num, by norm_num, by norm_num⟩, ⟨by norm_num, by norm_num, by norm_num⟩,
    ⟨by norm_num, by norm_num, by norm_num⟩, ⟨by norm_num, by norm_num, by norm_num⟩,
    by norm_num, by norm_num⟩

/-! ## The two whole-vector levels

`ntt_block_loop0` runs `half = 16` and `half = 8` and then stops, because from `half = 4` on
every butterfly partner is inside the group of eight vectors the second half of `ntt_block`
carries in registers.  The loop is unrolled here rather than inducted over: `half` takes two
concrete values and there is no invariant to induct on that is not just the list.

`A0 → A1 → A2` is the first half of the four-level chain; `growth_q1` and `growth_q2` supply
it. -/
end Kopis.Neon
