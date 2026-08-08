/-
  # Kopis/Neon/SerPlan.lean — the constant tables the NEON deserializer indexes.

  `src/backend/neon/ser.rs` builds, at compile time, one `Plan` per coefficient width: a `tbl`
  control naming, for 32-bit lane `k`, the four bytes starting at that coefficient's first byte,
  and the matching `ushl` count.  `PLANS` is that table for widths `0..=13`.

  Nothing here is deep — it is `⌊k·w/8⌋` and `(k·w) % 8` written into arrays by two nested
  loops — but the deserializer's correctness is stated in terms of those two expressions, so the
  table has to be pinned down before anything else can be said.  Three loop specs, in the order
  the code nests them:

  * `plan_inner_spec`   — the four bytes of one lane's `tbl` control;
  * `plan_outer_spec`   — all eight lanes, control and count together;
  * `plans_loop_spec`   — every width.

  **The one difference from `Kopis/Avx2/SerPlan.lean` is the sign of the count.**  `vpsrlvd`
  takes an unsigned right-shift count; `ushl` takes a signed *left*-shift count, so the Rust
  writes `-(((k * bits) % 8) as i32)` where the AVX2 version writes the bit offset itself.  The
  spec below therefore says `-(planShift w m)`, and `Kopis/Neon/SerLane.lean`'s `ushlLane_neg`
  is what turns that back into a right shift.  Everything else transfers with a change of
  namespace.

  A note on why this is proved rather than evaluated: the loops extract as `partial_fixpoint`
  definitions, which do not reduce, so `decide` cannot see through them; and `bits` stays
  symbolic here rather than being case-split thirteen ways, which keeps everything downstream
  symbolic too.
-/
import Kopis.Neon.SerLane

open Aeneas Aeneas.Std Result
open RustKopisNeon

namespace Kopis.Neon

set_option maxHeartbeats 1000000

/-- `PLANS` is indexed with `getElem!`, which needs a default.  Every index used below is in
bounds, so the choice is immaterial; the all-zero plan is the one `plans` itself starts from. -/
instance : Inhabited backend.neon.ser.Plan :=
  ⟨{ shuffle := Array.repeat 32#usize 0#u8, shift := Array.repeat 8#usize 0#i32 }⟩

/-- `getElem!` after a `List.set` at an in-bounds index. -/
private theorem getElem!_list_set {α : Type _} [Inhabited α] (l : List α) (j : ℕ)
    (v : α) (k : ℕ) (hj : j < l.length) :
    (l.set j v)[k]! = if k = j then v else l[k]! := by
  by_cases h : k = j
  · subst h
    rw [getElem!_pos _ k (by rw [List.length_set]; exact hj), List.getElem_set_self, if_pos rfl]
  · by_cases hk : k < l.length
    · rw [getElem!_pos _ k (by rw [List.length_set]; exact hk),
        List.getElem_set_of_ne (Ne.symm h), ← getElem!_pos _ k hk, if_neg h]
    · rw [getElem!_neg _ k (by rw [List.length_set]; exact hk), getElem!_neg _ k hk, if_neg h]

/-! ## The inner loop: one lane's four control bytes -/

theorem plan_inner_spec (shuffle : Array U8 32#usize) (k offset byte : Usize)
    (hk : k.val < 8) (hoff : offset.val + 4 ≤ 255) :
    backend.neon.ser.plan_loop0_loop0 shuffle k offset byte
      ⦃ (a : Array U8 32#usize) => ∀ j < 32,
          (a.val[j]!).val =
            if 4 * k.val + byte.val ≤ j ∧ j < 4 * k.val + 4
              then offset.val + (j - 4 * k.val)
              else (shuffle.val[j]!).val ⦄ := by
  unfold backend.neon.ser.plan_loop0_loop0
  by_cases hlt : byte < 4#usize
  · rw [if_pos hlt]
    have hbyte : byte.val < 4 := by scalar_tac
    let* ⟨ i, hi ⟩ ← Std.Usize.add_spec
    let* ⟨ i1, hi1 ⟩ ← Std.Usize.mul_spec
    let* ⟨ i2, hi2 ⟩ ← Std.Usize.add_spec
    have hi2v : i2.val = 4 * k.val + byte.val := by scalar_tac
    have hi2lt : i2.val < shuffle.length := by
      have : shuffle.length = 32 := by simp [Array.length]
      omega
    let* ⟨ i3, hi3 ⟩ ← UScalar.cast_inBounds_spec .U8 i (by scalar_tac)
    let* ⟨ a, ha ⟩ ← Array.update_spec
    let* ⟨ byte1, hbyte1 ⟩ ← Std.Usize.add_spec
    -- the recursive call fills `4k+byte+1 .. 4k+4`; this step filled `4k+byte`
    apply WP.spec_mono (plan_inner_spec a k offset byte1 hk hoff)
    intro r hr j hj
    rw [hr j hj, ha, Array.set_val_eq,
      getElem!_list_set shuffle.val i2.val i3 j (by simpa using hi2lt)]
    by_cases hcase : j = i2.val
    · rw [if_pos hcase, if_neg (by scalar_tac), if_pos (by scalar_tac)]
      scalar_tac
    · rw [if_neg hcase]
      by_cases hin : 4 * k.val + byte1.val ≤ j ∧ j < 4 * k.val + 4
      · rw [if_pos hin, if_pos (by scalar_tac)]
      · rw [if_neg hin, if_neg (by scalar_tac)]
  · rw [if_neg hlt]
    simp only [WP.spec_ok]
    intro j hj
    rw [if_neg (by scalar_tac)]
termination_by 4 - byte.val
decreasing_by scalar_decr_tac

/-! ## The outer loop: all eight lanes

The count is written negated; that is the whole of what distinguishes this from the AVX2
version. -/

theorem plan_outer_spec (bits : Usize) (hbits : bits.val ≤ 13)
    (shuffle : Array U8 32#usize) (shift : Array I32 8#usize) (k : Usize) :
    backend.neon.ser.plan_loop0 bits shuffle shift k
      ⦃ (r : Array Std.U8 32#usize × Array Std.I32 8#usize) =>
          (∀ j < 32, (r.1.val[j]!).val =
              if 4 * k.val ≤ j then planShuffle bits.val (j / 4) (j % 4)
              else (shuffle.val[j]!).val) ∧
          (∀ m < 8, (r.2.val[m]!).val =
              if k.val ≤ m then -(planShift bits.val m : ℤ)
              else (shift.val[m]!).val) ⦄ := by
  unfold backend.neon.ser.plan_loop0
  by_cases hlt : k < 8#usize
  · rw [if_pos hlt]
    have hk : k.val < 8 := by scalar_tac
    let* ⟨ i, hi ⟩ ← Std.Usize.mul_spec
    let* ⟨ offset, hoffset ⟩ ← Std.Usize.div_spec
    let* ⟨ i1, hi1 ⟩ ← Std.Usize.rem_spec
    have hoffv : offset.val = planShuffle bits.val k.val 0 := by
      unfold planShuffle; scalar_tac
    have hi1v : i1.val = planShift bits.val k.val := by unfold planShift; scalar_tac
    let* ⟨ i2, hi2 ⟩ ← UScalar.hcast_inBounds_spec .I32 i1 (by scalar_tac)
    let* ⟨ i3, hi3 ⟩ ← Std.IScalar.neg_step i2 (by scalar_tac)
    let* ⟨ a, ha ⟩ ← Array.update_spec
    let* ⟨ shuffle1, hshuffle1 ⟩ ← plan_inner_spec shuffle k offset 0#usize hk (by
      have : k.val * bits.val ≤ 7 * 13 := Nat.mul_le_mul (by omega) hbits
      unfold planShuffle at hoffv; omega)
    let* ⟨ k1, hk1 ⟩ ← Std.Usize.add_spec
    apply WP.spec_mono (plan_outer_spec bits hbits shuffle1 a k1)
    rintro ⟨r1, r2⟩ ⟨hr1, hr2⟩
    refine ⟨fun j hj => ?_, fun m hm => ?_⟩
    · rw [hr1 j hj]
      by_cases hj4 : 4 * k1.val ≤ j
      · rw [if_pos hj4, if_pos (by scalar_tac)]
      · rw [if_neg hj4, hshuffle1 j hj]
        by_cases hin : 4 * k.val + 0 ≤ j ∧ j < 4 * k.val + 4
        · rw [if_pos hin, if_pos (by omega)]
          have hjk : j / 4 = k.val := by omega
          rw [hoffv]
          unfold planShuffle
          rw [hjk]
          omega
        · rw [if_neg hin, if_neg (by scalar_tac)]
    · rw [hr2 m hm, ha, Array.set_val_eq,
        getElem!_list_set shift.val k.val i3 m (by simpa using hk)]
      by_cases hmk : k1.val ≤ m
      · rw [if_pos hmk, if_pos (by scalar_tac)]
      · rw [if_neg hmk]
        by_cases hmeq : m = k.val
        · rw [if_pos hmeq, if_pos (by omega), hi3, hi2, hi1v, hmeq]
        · rw [if_neg hmeq, if_neg (by omega)]
  · rw [if_neg hlt]
    simp only [WP.spec_ok]
    exact ⟨fun j hj => by rw [if_neg (by scalar_tac)],
           fun m hm => by rw [if_neg (by scalar_tac)]⟩
termination_by 8 - k.val
decreasing_by scalar_decr_tac

/-! ## One plan -/

theorem plan_spec (bits : Usize) (hbits : bits.val ≤ 13) :
    backend.neon.ser.plan bits
      ⦃ (p : backend.neon.ser.Plan) =>
          (∀ j < 32, (p.shuffle.val[j]!).val = planShuffle bits.val (j / 4) (j % 4)) ∧
          (∀ m < 8, (p.shift.val[m]!).val = -(planShift bits.val m : ℤ)) ⦄ := by
  unfold backend.neon.ser.plan
  let* ⟨ rshuf, rshift, hr1, hr2 ⟩ ← plan_outer_spec bits hbits
  exact ⟨fun j hj => by rw [hr1 j hj, if_pos (by omega)],
         fun m hm => by rw [hr2 m hm, if_pos (by omega)]⟩

/-! ## Every width

`plans_loop` fills entries `1 .. 13` in order, so the spec has to record that the earlier
entries stay put — otherwise nothing rules out a later iteration overwriting the one just
written. -/

theorem plans_loop_spec (plans : Array backend.neon.ser.Plan 14#usize) (b : Usize)
    (hb : 1 ≤ b.val) :
    backend.neon.ser.plans_loop plans b
      ⦃ (r : Array backend.neon.ser.Plan 14#usize) =>
          (∀ w < b.val, r.val[w]! = plans.val[w]!) ∧
          (∀ w, b.val ≤ w → w ≤ 13 →
            (∀ j < 32, ((r.val[w]!).shuffle.val[j]!).val = planShuffle w (j / 4) (j % 4)) ∧
            (∀ m < 8, ((r.val[w]!).shift.val[m]!).val = -(planShift w m : ℤ))) ⦄ := by
  unfold backend.neon.ser.plans_loop
  by_cases hle : b ≤ backend.neon.ser.MAX_BITS
  · rw [if_pos hle]
    have hb13 : b.val ≤ 13 := by
      simp only [backend.neon.ser.MAX_BITS] at hle; scalar_tac
    let* ⟨ p, hp1, hp2 ⟩ ← plan_spec b hb13
    let* ⟨ a, ha ⟩ ← Array.update_spec
    let* ⟨ b1, hb1 ⟩ ← Std.Usize.add_spec
    apply WP.spec_mono (plans_loop_spec a b1 (by omega))
    rintro r ⟨hkeep, hprop⟩
    have hplen : plans.val.length = 14 := by simp
    have hab : ∀ w < b.val, a.val[w]! = plans.val[w]! := by
      intro w hw
      rw [ha, Array.set_val_eq, getElem!_list_set plans.val b.val p w (by omega),
        if_neg (by omega)]
    have hbb : a.val[b.val]! = p := by
      rw [ha, Array.set_val_eq, getElem!_list_set plans.val b.val p b.val (by omega),
        if_pos rfl]
    refine ⟨fun w hw => ?_, fun w hlo hhi => ?_⟩
    · rw [hkeep w (by omega), hab w hw]
    · rcases Nat.lt_or_ge w b1.val with h | h
      · -- the entry just written
        have hwb : w = b.val := by omega
        subst hwb
        rw [hkeep b.val (by omega), hbb]
        exact ⟨hp1, hp2⟩
      · exact hprop w h hhi
  · rw [if_neg hle]
    have : 13 < b.val := by simp only [backend.neon.ser.MAX_BITS] at hle; scalar_tac
    exact ⟨fun w _ => rfl, fun w hlo hhi => by omega⟩
termination_by 14 - b.val
decreasing_by
  simp only [backend.neon.ser.MAX_BITS] at hle
  scalar_decr_tac

/-- **The table.**  For every width the crate uses, `PLANS[w]` holds the `tbl` control and the
negated shift the deserializer's correctness is stated through. -/
theorem PLANS_spec :
    backend.neon.ser.PLANS
      ⦃ (r : Array backend.neon.ser.Plan 14#usize) => ∀ w, 1 ≤ w → w ≤ 13 →
          (∀ j < 32, ((r.val[w]!).shuffle.val[j]!).val = planShuffle w (j / 4) (j % 4)) ∧
          (∀ m < 8, ((r.val[w]!).shift.val[m]!).val = -(planShift w m : ℤ)) ⦄ := by
  simp only [backend.neon.ser.PLANS]
  unfold backend.neon.ser.plans
  let* ⟨ p, hp1, hp2 ⟩ ← plan_spec 0#usize (by scalar_tac)
  apply WP.spec_mono (plans_loop_spec (Array.repeat 14#usize p) 1#usize (by scalar_tac))
  rintro r ⟨-, hprop⟩
  exact hprop

end Kopis.Neon
