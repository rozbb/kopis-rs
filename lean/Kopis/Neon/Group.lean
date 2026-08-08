/-
  # Kopis/Neon/Group.lean — a transposed group of eight vectors.

  The last three forward levels (and the first three inverse ones) have `len < 8`, so their
  butterflies live inside a vector.  `load_group b g` reads vectors `8g … 8g+7` of a block and
  transposes them; `store_group` transposes back and writes them.  Between the two, lane `m` of
  vector `k` holds coefficient `8·(8g + m) + k` — that is, **lane `m` owns the whole
  eight-coefficient block `8g + m`**, which is what makes the three short levels ordinary
  vertical butterflies with a per-lane ψ.

  That sentence is the Rust module comment, and these two specs are it:

      lane `m` of the loaded group's vector `k`  =  b[64g + 8m + k]

  `Kopis/Neon/Transpose.lean` does the work; this file is the arithmetic that turns "vector `k`
  lane `m` is vector `m` lane `k`" into a statement about coefficient indices, plus the store
  loop that puts them back.
-/
import Kopis.Neon.Butterfly
import Kopis.Neon.Transpose

open Aeneas Aeneas.Std Result
open RustKopisNeon
open RustKopisNeon.backend.neon.intrinsics

namespace Kopis.Neon

set_option maxHeartbeats 1000000

/-- Reading vector `a` of a group depends only on `a`, not on the proof that it is in range —
which is what lets an index be rewritten under `vAt` without a dependent motive. -/
theorem vAt_congr (v : Array Vec128 8#usize) {a b : ℕ} (ha : a < 8) (hb : b < 8) (h : a = b) :
    vAt v a ha = vAt v b hb := by subst h; rfl

/-! ## Loading

Eight loads and a transpose.  The eight vectors go into an `Array.make`, which `vAt` reads back
positionally. -/

theorem load_group_spec (b : Array I16 256#usize) (g : Usize) (hg : g.val < 4) :
    backend.neon.ntt.load_group b g
      ⦃ (r : Array Vec128 8#usize) => ∀ k (hk : k < 8), ∀ m < 8,
          (lane16 (vAt r k hk) m).toInt = (b.val[64 * g.val + 8 * m + k]!).val ⦄ := by
  unfold backend.neon.ntt.load_group
  let* ⟨ i, hi ⟩ ← Std.Usize.mul_spec (x := 8#usize) (y := g) (by scalar_tac)
  have hiv : i.val = 8 * g.val := by scalar_tac
  obtain ⟨v0, hv0, hv0l⟩ := load_i16_val b i (by omega)
  rw [hv0, bind_tc_ok]
  let* ⟨ i1, hi1 ⟩ ← Std.Usize.add_spec (x := i) (y := 1#usize) (by scalar_tac)
  obtain ⟨v1, hv1, hv1l⟩ := load_i16_val b i1 (by scalar_tac)
  rw [hv1, bind_tc_ok]
  let* ⟨ i2, hi2 ⟩ ← Std.Usize.add_spec (x := i) (y := 2#usize) (by scalar_tac)
  obtain ⟨v2, hv2, hv2l⟩ := load_i16_val b i2 (by scalar_tac)
  rw [hv2, bind_tc_ok]
  let* ⟨ i3, hi3 ⟩ ← Std.Usize.add_spec (x := i) (y := 3#usize) (by scalar_tac)
  obtain ⟨v3, hv3, hv3l⟩ := load_i16_val b i3 (by scalar_tac)
  rw [hv3, bind_tc_ok]
  let* ⟨ i4, hi4 ⟩ ← Std.Usize.add_spec (x := i) (y := 4#usize) (by scalar_tac)
  obtain ⟨v4, hv4, hv4l⟩ := load_i16_val b i4 (by scalar_tac)
  rw [hv4, bind_tc_ok]
  let* ⟨ i5, hi5 ⟩ ← Std.Usize.add_spec (x := i) (y := 5#usize) (by scalar_tac)
  obtain ⟨v5, hv5, hv5l⟩ := load_i16_val b i5 (by scalar_tac)
  rw [hv5, bind_tc_ok]
  let* ⟨ i6, hi6 ⟩ ← Std.Usize.add_spec (x := i) (y := 6#usize) (by scalar_tac)
  obtain ⟨v6, hv6, hv6l⟩ := load_i16_val b i6 (by scalar_tac)
  rw [hv6, bind_tc_ok]
  let* ⟨ i7, hi7 ⟩ ← Std.Usize.add_spec (x := i) (y := 7#usize) (by scalar_tac)
  obtain ⟨v7, hv7, hv7l⟩ := load_i16_val b i7 (by scalar_tac)
  rw [hv7, bind_tc_ok]
  -- the untransposed group: vector `m` holds coefficients `8(8g+m) … +8`
  apply WP.spec_mono (transpose8_spec (Array.make 8#usize [v0, v1, v2, v3, v4, v5, v6, v7]))
  intro r hr k hk m hm
  rw [hr k hk m hm]
  have e0 : ∀ h, vAt (Array.make 8#usize [v0, v1, v2, v3, v4, v5, v6, v7]) 0 h = v0 :=
    fun _ => rfl
  have e1 : ∀ h, vAt (Array.make 8#usize [v0, v1, v2, v3, v4, v5, v6, v7]) 1 h = v1 :=
    fun _ => rfl
  have e2 : ∀ h, vAt (Array.make 8#usize [v0, v1, v2, v3, v4, v5, v6, v7]) 2 h = v2 :=
    fun _ => rfl
  have e3 : ∀ h, vAt (Array.make 8#usize [v0, v1, v2, v3, v4, v5, v6, v7]) 3 h = v3 :=
    fun _ => rfl
  have e4 : ∀ h, vAt (Array.make 8#usize [v0, v1, v2, v3, v4, v5, v6, v7]) 4 h = v4 :=
    fun _ => rfl
  have e5 : ∀ h, vAt (Array.make 8#usize [v0, v1, v2, v3, v4, v5, v6, v7]) 5 h = v5 :=
    fun _ => rfl
  have e6 : ∀ h, vAt (Array.make 8#usize [v0, v1, v2, v3, v4, v5, v6, v7]) 6 h = v6 :=
    fun _ => rfl
  have e7 : ∀ h, vAt (Array.make 8#usize [v0, v1, v2, v3, v4, v5, v6, v7]) 7 h = v7 :=
    fun _ => rfl
  rcases show m = 0 ∨ m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 4 ∨ m = 5 ∨ m = 6 ∨ m = 7 from by omega with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  simp only [e0, e1, e2, e3, e4, e5, e6, e7] <;>
  [ (rw [hv0l k hk, hiv]); (rw [hv1l k hk, hi1, hiv]); (rw [hv2l k hk, hi2, hiv]);
    (rw [hv3l k hk, hi3, hiv]); (rw [hv4l k hk, hi4, hiv]); (rw [hv5l k hk, hi5, hiv]);
    (rw [hv6l k hk, hi6, hiv]); (rw [hv7l k hk, hi7, hiv]) ] <;>
  congr 2 <;> scalar_tac

/-! ## Storing

Transpose back, then eight stores.  The loop's spec records the prefix it has already written,
as every store loop in this stack does. -/

theorem store_group_loop_spec (b : Array I16 256#usize) (g : Usize) (hg : g.val < 4)
    (v : Array Vec128 8#usize) (iter : core.ops.range.Range Usize) (hend : iter.«end».val = 8) :
    backend.neon.ntt.store_group_loop iter b g v
      ⦃ (r : Array I16 256#usize) => ∀ p < 256,
          (r.val[p]!).val =
            if 64 * g.val + 8 * iter.start.val ≤ p ∧ p < 64 * g.val + 64 then
              (lane16 (vAt v ((p - 64 * g.val) / 8 % 8) (by omega)) ((p - 64 * g.val) % 8)).toInt
            else (b.val[p]!).val ⦄ := by
  unfold backend.neon.ntt.store_group_loop
  by_cases hlt : iter.start.val < iter.«end».val
  · let* ⟨ o, iter1, ho, hstart', hend' ⟩ ← core.iter.range.IteratorRange.next_Usize_some_spec
    rw [ho]
    simp only
    have hj8 : iter.start.val < 8 := by omega
    let* ⟨ i, hi ⟩ ← Std.Usize.mul_spec (x := 8#usize) (y := g) (by scalar_tac)
    let* ⟨ i1, hi1 ⟩ ← Std.Usize.add_spec (x := i) (y := iter.start) (by scalar_tac)
    have hi1v : i1.val = 8 * g.val + iter.start.val := by scalar_tac
    let* ⟨ v1, hv1 ⟩ ← Array.index_usize_spec v iter.start (by scalar_tac)
    have hv1e : v1 = vAt v iter.start.val hj8 := by rw [hv1]; rfl
    obtain ⟨b1, hb1, hb1v⟩ := store_i16_val b i1 v1 (by omega)
    rw [hb1, bind_tc_ok]
    apply WP.spec_mono (store_group_loop_spec b1 g hg v iter1 (by rw [hend']; exact hend))
    intro r hr p hp
    rw [hr p hp, hb1v p hp, hi1v]
    by_cases hlow : 64 * g.val + 8 * iter1.start.val ≤ p ∧ p < 64 * g.val + 64
    · rw [if_pos hlow,
        if_pos (show 64 * g.val + 8 * iter.start.val ≤ p ∧ p < 64 * g.val + 64 by scalar_tac)]
    · rw [if_neg hlow]
      by_cases hin : 8 * (8 * g.val + iter.start.val) ≤ p
                     ∧ p < 8 * (8 * g.val + iter.start.val) + 8
      · rw [if_pos hin,
          if_pos (show 64 * g.val + 8 * iter.start.val ≤ p ∧ p < 64 * g.val + 64 by scalar_tac),
          vAt_congr v (by omega) hj8
            (show (p - 64 * g.val) / 8 % 8 = iter.start.val by scalar_tac),
          show (p - 64 * g.val) % 8 = p - 8 * (8 * g.val + iter.start.val) from by scalar_tac,
          hv1e]
      · rw [if_neg hin,
          if_neg (show ¬(64 * g.val + 8 * iter.start.val ≤ p ∧ p < 64 * g.val + 64)
            by scalar_tac)]
  · let* ⟨ o, iter1, hnone, _ ⟩ ← core.iter.range.IteratorRange.next_Usize_none_spec
    rw [hnone]
    refine (WP.spec_ok _).mpr (fun p hp => ?_)
    rw [if_neg (by scalar_tac)]
termination_by iter.«end».val - iter.start.val
decreasing_by scalar_decr_tac

/-- **`store_group` is `load_group`'s inverse on the block.**  Coefficient `64g + 8m + k` of the
result is lane `m` of the group's vector `k`, which is the same indexing `load_group_spec`
states — so a group loaded, transformed lane-wise and stored lands where it started. -/
theorem store_group_spec (b : Array I16 256#usize) (g : Usize) (hg : g.val < 4)
    (v : Array Vec128 8#usize) :
    backend.neon.ntt.store_group b g v
      ⦃ (r : Array I16 256#usize × Array Vec128 8#usize) => ∀ p < 256,
          (r.1.val[p]!).val =
            if 64 * g.val ≤ p ∧ p < 64 * g.val + 64 then
              (lane16 (vAt v ((p - 64 * g.val) % 8) (by omega))
                ((p - 64 * g.val) / 8)).toInt
            else (b.val[p]!).val ⦄ := by
  unfold backend.neon.ntt.store_group
  apply WP.spec_bind (transpose8_spec v)
  intro v1 hv1
  apply WP.spec_bind (store_group_loop_spec b g hg v1 ⟨0#usize, 8#usize⟩ rfl)
  intro b1 hb1
  refine (WP.spec_ok _).mpr (fun p hp => ?_)
  rw [hb1 p hp]
  by_cases hin : 64 * g.val ≤ p ∧ p < 64 * g.val + 64
  · rw [if_pos (show 64 * g.val + 8 * (0#usize).val ≤ p ∧ p < 64 * g.val + 64 by scalar_tac),
      if_pos hin,
      hv1 ((p - 64 * g.val) / 8 % 8) (by omega) ((p - 64 * g.val) % 8) (by omega),
      show (p - 64 * g.val) / 8 % 8 = (p - 64 * g.val) / 8 from by omega]
  · rw [if_neg (show ¬(64 * g.val + 8 * (0#usize).val ≤ p ∧ p < 64 * g.val + 64) by scalar_tac),
      if_neg hin]

end Kopis.Neon
