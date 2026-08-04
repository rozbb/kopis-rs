/-
  # Kopis/Properties/NttMul.lean — the pointwise product and the inverse pipeline.

  `NttMatrix::mul` computes one output ring element as

      acc  := Σ_j  lhs_j ∘ rhs_j        (`pointwise_mul_acc`, an `i64` accumulator)
      out  := to_wrapping_u16 ∘ invntt ∘ mont_reduce (acc)   (`reduce_invntt_to_ring_elem`)

  This file proves both halves.  The first is exact `i64` arithmetic: the operands are centred
  mod-`p` values, so each product is below `p²` and at most `MAX_L = 4` of them are summed.
  The second is where the mathematics lands: `mont_reduce` divides by `2³²`, `invntt` multiplies
  by `2⁸·invScale`, and the two cancel exactly (`invScale_cancel`), so the coefficient the
  pipeline produces is the negacyclic convolution *mod `p`*.  `reduce_invntt_to_ring_elem_spec`
  then converts that into an answer mod `2¹⁶`, using the caller-supplied integer convolution `H`
  and the exactness bound `|H| ≤ ⌊p/2⌋`: two integers congruent mod `p` and both within `⌊p/2⌋`
  of zero are equal, so the mod-`p` computation determines the integer answer, and reducing that
  mod `2¹⁶` is what `to_wrapping_u16` returns.
-/
import Kopis.Properties.NttForward
import Kopis.Properties.NttInverse

open Aeneas Aeneas.Std Result RustKopisSerial
open scoped BigOperators

namespace Kopis.Properties

open NttMath

set_option maxHeartbeats 1000000

/-! ### Reading the `[i64; 256]` accumulator -/

/-- The integer value of accumulator entry `c`. -/
def accZ (a : Array I64 256#usize) (c : ℕ) : ℤ := ((a.val[c]!).val : ℤ)

/-- `getElem!` after a `List.set` at an in-bounds index (local copy). -/
private theorem mul_getElem!_list_set {α : Type _} [Inhabited α] (l : List α) (j : ℕ) (v : α)
    (k : ℕ) (hj : j < l.length) : (l.set j v)[k]! = if k = j then v else l[k]! := by
  by_cases h : k = j
  · subst h
    rw [getElem!_pos _ k (by rw [List.length_set]; exact hj), List.getElem_set_self, if_pos rfl]
  · by_cases hk : k < l.length
    · rw [getElem!_pos _ k (by rw [List.length_set]; exact hk),
        List.getElem_set_of_ne (Ne.symm h), ← getElem!_pos _ k hk, if_neg h]
    · rw [getElem!_neg _ k (by rw [List.length_set]; exact hk), getElem!_neg _ k hk, if_neg h]

theorem accZ_set (a : Array I64 256#usize) (i : Usize) (v : I64) (hi : i.val < 256) (c : ℕ) :
    accZ (a.set i v) c = if c = i.val then (v.val : ℤ) else accZ a c := by
  have hlen : a.val.length = 256 := by simp
  unfold accZ
  rw [Array.set_val_eq, mul_getElem!_list_set a.val i.val v c (by rw [hlen]; exact hi)]
  split <;> rfl

theorem accZ_getElem (a : Array I64 256#usize) (i : Usize) (hi : i.val < 256) :
    ((a.val[i.val]'(by rw [show a.val.length = 256 by simp]; exact hi)).val : ℤ)
      = accZ a i.val := by
  unfold accZ
  rw [getElem!_pos a.val i.val
    (by rw [show a.val.length = 256 by simp]; exact hi)]

/-! ## `pointwise_mul_acc`: exact `i64` multiply-accumulate

Both operands are centred mod-`p` values, so each product is below `p² ≈ 2.53·10¹⁵` and the
accumulator — at most `MAX_L = 4` terms — stays far inside `i64`.  The loop invariant splits the
accumulator bound in two: entries at or past `iter.start` still carry the incoming bound `Bacc`,
entries below it have already grown by one product. -/

theorem pointwise_mul_acc_loop_spec (iter : core.ops.range.Range Usize)
    (acc : Array I64 256#usize) (lhs rhs : arithmetic.ntt.NttElem) (Bacc : ℤ)
    (hend : iter.«end».val = 256)
    (hlhs : ∀ c, c < 256 → |aZ lhs c| ≤ pNtt)
    (hrhs : ∀ c, c < 256 → |aZ rhs c| ≤ pNtt)
    (hB0 : 0 ≤ Bacc)
    (hBhi : Bacc + pNtt * pNtt ≤ 9223372036854775807)
    (hacc : ∀ c, c < 256 → |accZ acc c| ≤ Bacc + pNtt * pNtt)
    (haccHi : ∀ c, iter.start.val ≤ c → c < 256 → |accZ acc c| ≤ Bacc) :
    arithmetic.ntt.pointwise_mul_acc_loop iter acc lhs rhs
      ⦃ (r : Array I64 256#usize) =>
          (∀ c, c < 256 →
              accZ r c = if iter.start.val ≤ c then accZ acc c + aZ lhs c * aZ rhs c
                         else accZ acc c)
          ∧ (∀ c, c < 256 → |accZ r c| ≤ Bacc + pNtt * pNtt) ⦄ := by
  have hp0 : (0:ℤ) < pNtt := by unfold pNtt; norm_num
  unfold arithmetic.ntt.pointwise_mul_acc_loop
  by_cases hlt : iter.start.val < iter.«end».val
  · let* ⟨o, iter1, ho, hstart', hend'⟩ ← core.iter.range.IteratorRange.next_Usize_some_spec
    rw [ho]; simp only
    have hi_lt : iter.start.val < 256 := by omega
    have hacl : iter.start.val < acc.length := by have := acc.property; scalar_tac
    have hll : iter.start.val < (lhs : Array I32 256#usize).length := by
      have := (lhs : Array I32 256#usize).property; scalar_tac
    have hrl : iter.start.val < (rhs : Array I32 256#usize).length := by
      have := (rhs : Array I32 256#usize).property; scalar_tac
    have hend1 : iter1.«end».val = 256 := by rw [hend']; exact hend
    step*
    all_goals
      have e_i1 : (i1.val : ℤ) = accZ acc iter.start.val := by
        rw [i1_post]; exact accZ_getElem acc iter.start hi_lt
      have e_i2 : (i2.val : ℤ) = aZ lhs iter.start.val := by
        rw [i2_post]; exact aZ_getElem lhs iter.start hi_lt
      have e_i4 : (i4.val : ℤ) = aZ rhs iter.start.val := by
        rw [i4_post]; exact aZ_getElem rhs iter.start hi_lt
      have e_i3 : (i3.val : ℤ) = (i2.val : ℤ) := by
        rw [i3_post, IScalar.cast_val_eq,
          show Min.min IScalarTy.I64.numBits IScalarTy.I32.numBits = 32 from rfl]
        exact bmod_i32_exact (by scalar_tac) (by scalar_tac)
      have e_i5 : (i5.val : ℤ) = (i4.val : ℤ) := by
        rw [i5_post, IScalar.cast_val_eq,
          show Min.min IScalarTy.I64.numBits IScalarTy.I32.numBits = 32 from rfl]
        exact bmod_i32_exact (by scalar_tac) (by scalar_tac)
      have habs3 : |(i3.val : ℤ)| ≤ pNtt := by rw [e_i3, e_i2]; exact hlhs _ hi_lt
      have habs5 : |(i5.val : ℤ)| ≤ pNtt := by rw [e_i5, e_i4]; exact hrhs _ hi_lt
      have hpp : pNtt * pNtt = 2533120274592769 := by unfold pNtt; norm_num
      have hBhi' : Bacc + 2533120274592769 ≤ 9223372036854775807 := by rw [← hpp]; exact hBhi
      have hprodb : -2533120274592769 ≤ (i3.val : ℤ) * (i5.val : ℤ)
          ∧ (i3.val : ℤ) * (i5.val : ℤ) ≤ 2533120274592769 := by
        have h : |(i3.val : ℤ) * (i5.val : ℤ)| ≤ 2533120274592769 := by
          rw [abs_mul, ← hpp]
          exact mul_le_mul habs3 habs5 (abs_nonneg _) (le_of_lt hp0)
        rw [abs_le] at h; exact h
      have e_i6 : (i6.val : ℤ) = (i3.val : ℤ) * (i5.val : ℤ) := by
        rw [i6_post, I64_wrapping_mul_exact i3 i5 (by linarith [hprodb.1])
          (by linarith [hprodb.2])]
      have hi1b : -Bacc ≤ (i1.val : ℤ) ∧ (i1.val : ℤ) ≤ Bacc := by
        have h := haccHi iter.start.val (le_refl _) hi_lt
        rw [← e_i1, abs_le] at h; exact h
      have e_i7 : (i7.val : ℤ) = (i1.val : ℤ) + (i6.val : ℤ) := by
        rw [i7_post, I64_wrapping_add_exact i1 i6
          (by rw [e_i6]; linarith [hi1b.1, hprodb.1])
          (by rw [e_i6]; linarith [hi1b.2, hprodb.2])]
      have ha : ∀ c, accZ a c = if c = iter.start.val then (i7.val : ℤ) else accZ acc c := by
        intro c; rw [a_post, accZ_set acc iter.start i7 hi_lt c]
      have hi7b : |(i7.val : ℤ)| ≤ Bacc + pNtt * pNtt := by
        rw [abs_le, hpp, e_i7, e_i6]
        exact ⟨by linarith [hi1b.1, hprodb.1], by linarith [hi1b.2, hprodb.2]⟩
    case hacc =>
      intro c hc
      rw [ha c]
      split_ifs
      · exact hi7b
      · exact hacc c hc
    case haccHi =>
      intro c hc1 hc2
      rw [ha c, if_neg (by rw [hstart'] at hc1; omega)]
      exact haccHi c (by rw [hstart'] at hc1; omega) hc2
    refine ⟨?_, r_post2⟩
    intro c hc
    rw [r_post1 c hc, hstart']
    by_cases hcase : iter.start.val + 1 ≤ c
    · rw [if_pos hcase, if_pos (by omega : iter.start.val ≤ c), ha c, if_neg (by omega)]
    · rw [if_neg hcase]
      by_cases hci : c = iter.start.val
      · rw [ha c, if_pos hci, if_pos (by omega : iter.start.val ≤ c), e_i7, e_i6, e_i1, e_i3,
          e_i5, e_i2, e_i4, hci]
      · rw [ha c, if_neg hci, if_neg (by omega : ¬ iter.start.val ≤ c)]
  · let* ⟨o, iter1, hnone, _⟩ ← core.iter.range.IteratorRange.next_Usize_none_spec
    rw [hnone]; simp only [WP.spec_ok]
    refine ⟨fun c hc => ?_, fun c hc => hacc c hc⟩
    rw [if_neg (by omega : ¬ iter.start.val ≤ c)]
  termination_by iter.«end».val - iter.start.val
  decreasing_by scalar_decr_tac

/-- **`pointwise_mul_acc` adds the pointwise product into the accumulator, exactly.** -/
theorem pointwise_mul_acc_spec
    (acc : Array I64 256#usize) (lhs rhs : arithmetic.ntt.NttElem) (Bacc : ℤ)
    (hlhs : ∀ c, c < 256 → |aZ lhs c| ≤ pNtt)
    (hrhs : ∀ c, c < 256 → |aZ rhs c| ≤ pNtt)
    (hB0 : 0 ≤ Bacc)
    (hBhi : Bacc + pNtt * pNtt ≤ 9223372036854775807)
    (hacc : ∀ c, c < 256 → |accZ acc c| ≤ Bacc) :
    arithmetic.ntt.pointwise_mul_acc acc lhs rhs
      ⦃ (r : Array I64 256#usize) =>
          (∀ c, c < 256 → accZ r c = accZ acc c + aZ lhs c * aZ rhs c)
          ∧ (∀ c, c < 256 → |accZ r c| ≤ Bacc + pNtt * pNtt) ⦄ := by
  have hp0 : (0:ℤ) < pNtt := by unfold pNtt; norm_num
  have hRD : (consts.RING_DEG : Usize).val = 256 := by simp only [consts.RING_DEG]; rfl
  unfold arithmetic.ntt.pointwise_mul_acc
  apply WP.spec_mono
    (pointwise_mul_acc_loop_spec { start := 0#usize, «end» := consts.RING_DEG } acc lhs rhs Bacc
      hRD hlhs hrhs hB0 hBhi
      (fun c hc => le_trans (hacc c hc) (by nlinarith)) (fun c _ hc => hacc c hc))
  rintro r ⟨hr1, hr2⟩
  exact ⟨fun c hc => by simpa using hr1 c hc, hr2⟩

/-! ## `reduce_invntt_to_ring_elem`

Three passes: a Montgomery reduction of every accumulator entry, the inverse transform, and the
centring `to_wrapping_u16`. -/

/-- The first pass: `v[c] := mont_reduce (acc[c])`. -/
theorem reduce_loop0_spec (iter : core.ops.range.Range Usize)
    (acc : Array I64 256#usize) (v : Array I32 256#usize)
    (hend : iter.«end».val = 256)
    (hacc : ∀ c, c < 256 → |accZ acc c| ≤ 2 ^ 31 * pNtt - 1) :
    arithmetic.ntt.reduce_invntt_to_ring_elem_loop0 iter acc v
      ⦃ (r : Array I32 256#usize) =>
          (∀ c, iter.start.val ≤ c → c < 256 →
              (aZ r c * 2 ^ 32) % pNtt = accZ acc c % pNtt
              ∧ -pNtt < aZ r c ∧ aZ r c < pNtt)
          ∧ (∀ c, c < iter.start.val → aZ r c = aZ v c) ⦄ := by
  unfold arithmetic.ntt.reduce_invntt_to_ring_elem_loop0
  by_cases hlt : iter.start.val < iter.«end».val
  · let* ⟨o, iter1, ho, hstart', hend'⟩ ← core.iter.range.IteratorRange.next_Usize_some_spec
    rw [ho]; simp only
    have hi_lt : iter.start.val < 256 := by omega
    have hacl : iter.start.val < acc.length := by have := acc.property; scalar_tac
    have hvl : iter.start.val < v.length := by have := v.property; scalar_tac
    have hend1 : iter1.«end».val = 256 := by rw [hend']; exact hend
    let* ⟨i1, hi1⟩ ← Array.index_usize_spec acc iter.start hacl
    have e_i1 : (i1.val : ℤ) = accZ acc iter.start.val := by
      rw [hi1]; exact accZ_getElem acc iter.start hi_lt
    have hb := hacc iter.start.val hi_lt
    rw [abs_le] at hb
    apply WP.spec_bind (mont_reduce_spec i1 (by rw [e_i1]; linarith [hb.1])
      (by rw [e_i1]; linarith [hb.2]))
    intro i2 hi2
    obtain ⟨h2mod, h2lo, h2hi⟩ := hi2
    let* ⟨a, ha⟩ ← Array.update_spec v iter.start i2 hvl
    have haz : ∀ c, aZ a c = if c = iter.start.val then (i2.val : ℤ) else aZ v c := by
      intro c; rw [ha, aZ_set v iter.start i2 hi_lt c]
    apply WP.spec_mono (reduce_loop0_spec iter1 acc a hend1 hacc)
    rintro r ⟨hr1, hr2⟩
    rw [hstart'] at hr1 hr2
    refine ⟨?_, ?_⟩
    · intro c hc1 hc2
      by_cases hci : c = iter.start.val
      · rw [hr2 c (by omega), haz c, if_pos hci, hci, e_i1] at *
        exact ⟨h2mod, h2lo, h2hi⟩
      · exact hr1 c (by omega) hc2
    · intro c hc
      rw [hr2 c (by omega), haz c, if_neg (by omega)]
  · let* ⟨o, iter1, hnone, _⟩ ← core.iter.range.IteratorRange.next_Usize_none_spec
    rw [hnone]; simp only [WP.spec_ok]
    exact ⟨fun c hc1 hc2 => absurd hc2 (by omega), by simp⟩
  termination_by iter.«end».val - iter.start.val
  decreasing_by scalar_decr_tac

/-- The third pass: `out[c] := to_wrapping_u16 (v[c])`.  The caller supplies the *integer* answer
`H`; the exactness hypothesis `hHb` (`|H| ≤ ⌊p/2⌋`) together with `hH` (`H ≡ v` mod `p`) is what
turns the mod-`p` computation into the integer one. -/
theorem reduce_loop1_spec (iter : core.ops.range.Range Usize)
    (v : Array I32 256#usize) (out : arithmetic.ring_arith.RingElem) (H : ℕ → ℤ)
    (hend : iter.«end».val = 256)
    (hv : ∀ c, c < 256 → -pNtt < aZ v c ∧ aZ v c < pNtt)
    (hH : ∀ c, c < 256 → ((H c : ℤ) : Zp) = ((aZ v c : ℤ) : Zp))
    (hHb : ∀ c, c < 256 → |H c| ≤ 25165056) :
    arithmetic.ntt.reduce_invntt_to_ring_elem_loop1 iter v out
      ⦃ (r : arithmetic.ring_arith.RingElem) =>
          (∀ c, iter.start.val ≤ c → c < 256 →
              ((r.val[c]!).val : ℤ) % 65536 = H c % 65536)
          ∧ (∀ c, c < iter.start.val → r.val[c]! = out.val[c]!) ⦄ := by
  unfold arithmetic.ntt.reduce_invntt_to_ring_elem_loop1
  by_cases hlt : iter.start.val < iter.«end».val
  · let* ⟨o, iter1, ho, hstart', hend'⟩ ← core.iter.range.IteratorRange.next_Usize_some_spec
    rw [ho]; simp only
    have hi_lt : iter.start.val < 256 := by omega
    have hvl : iter.start.val < v.length := by have := v.property; scalar_tac
    have hol : iter.start.val < (out : Array U16 256#usize).length := by
      have := (out : Array U16 256#usize).property; scalar_tac
    have hend1 : iter1.«end».val = 256 := by rw [hend']; exact hend
    let* ⟨i1, hi1⟩ ← Array.index_usize_spec v iter.start hvl
    have e_i1 : (i1.val : ℤ) = aZ v iter.start.val := by
      rw [hi1]; exact aZ_getElem v iter.start hi_lt
    obtain ⟨hvlo, hvhi⟩ := hv iter.start.val hi_lt
    apply WP.spec_bind (to_wrapping_u16_spec i1 (by rw [e_i1]; exact hvlo)
      (by rw [e_i1]; exact hvhi))
    intro i2 hi2
    obtain ⟨x2, hx2mod, hx2lo, hx2hi, hx2r⟩ := hi2
    -- exactness: `x2` and `H` are congruent mod `p` and both within `⌊p/2⌋`, hence equal
    have hHmod : H iter.start.val ≡ (i1.val : ℤ) [ZMOD pNtt] := by
      have h := hH iter.start.val hi_lt
      rw [← e_i1] at h
      exact (ZMod.intCast_eq_intCast_iff' _ _ _).mp h
    have hx2eq : x2 = H iter.start.val := by
      have hb := hHb iter.start.val hi_lt
      rw [abs_le] at hb
      have hdvd : (pNtt : ℤ) ∣ (x2 - H iter.start.val) := by
        have := (Int.ModEq.trans hx2mod (Int.ModEq.symm hHmod))
        exact Int.ModEq.dvd (Int.ModEq.symm this)
      have hp : pNtt = 50330113 := rfl
      rcases hdvd with ⟨q, hq⟩
      rw [hp] at hq
      have : q = 0 := by nlinarith [hb.1, hb.2, hx2lo, hx2hi]
      omega
    let* ⟨a, ha⟩ ← Array.update_spec out iter.start i2 hol
    have haz : ∀ c, a.val[c]! = if c = iter.start.val then i2 else out.val[c]! := by
      intro c
      rw [ha, Array.set_val_eq,
        mul_getElem!_list_set (out : Array U16 256#usize).val iter.start.val i2 c hol]
    apply WP.spec_mono (reduce_loop1_spec iter1 v a H hend1 hv hH hHb)
    rintro r ⟨hr1, hr2⟩
    rw [hstart'] at hr1 hr2
    refine ⟨?_, ?_⟩
    · intro c hc1 hc2
      by_cases hci : c = iter.start.val
      · rw [hr2 c (by omega), haz c, if_pos hci, hci, ← hx2eq]
        exact hx2r
      · exact hr1 c (by omega) hc2
    · intro c hc
      rw [hr2 c (by omega), haz c, if_neg (by omega)]
  · let* ⟨o, iter1, hnone, _⟩ ← core.iter.range.IteratorRange.next_Usize_none_spec
    rw [hnone]; simp only [WP.spec_ok]
    exact ⟨fun c hc1 hc2 => absurd hc2 (by omega), by simp⟩
  termination_by iter.«end».val - iter.start.val
  decreasing_by scalar_decr_tac

/-- The Montgomery factor of the pointwise step and the `2⁸·INVNTT_SCALE` of the inverse
transform cancel exactly: `INVNTT_SCALE = 256⁻¹·2⁶⁴ mod p`, so `invScale · 2⁸ · 2⁻³² = 1`. -/
theorem invScale_cancel : invScale * ((2 : Zp) ^ 8 * Rinv) = 1 := by
  have h64 : ((44652572 * 256 : ℕ) : Zp) = ((6122781 : ℕ) : Zp) := cast_eq_of_mod (by norm_num)
  push_cast at h64
  have hkey : (44652572 : Zp) * (2 : Zp) ^ 8 = (6122781 : Zp) := by
    rw [show (2 : Zp) ^ 8 = (256 : Zp) by norm_num]
    exact h64
  unfold invScale
  push_cast
  calc (44652572 : Zp) * Rinv * ((2 : Zp) ^ 8 * Rinv)
      = ((44652572 : Zp) * (2 : Zp) ^ 8) * Rinv ^ 2 := by ring
    _ = (6122781 : Zp) * Rinv ^ 2 := by rw [hkey]
    _ = 1 := R64_Rinv_sq

/-- **`reduce_invntt_to_ring_elem` produces the negacyclic convolution mod `2¹⁶`.**  The caller
supplies both the `ℤ/p` coefficient function `h` that the accumulator evaluates (`hst`) and its
integer lift `H` (`hHz`, `hHb`); the conclusion is that the returned `u16` coefficients agree with
`H` mod `2¹⁶`. -/
theorem reduce_invntt_to_ring_elem_spec (acc : Array I64 256#usize) (h : ℕ → Zp) (H : ℕ → ℤ)
    (hacc : ∀ c, c < 256 → |accZ acc c| ≤ 2 ^ 31 * pNtt - 1)
    (hst : ∀ c, c < 256 →
        ((accZ acc c : ℤ) : Zp) = ∑ i ∈ Finset.range 256, h i * cst (256 + c) ^ i)
    (hHz : ∀ n, n < 256 → ((H n : ℤ) : Zp) = h n)
    (hHb : ∀ n, n < 256 → |H n| ≤ 25165056) :
    arithmetic.ntt.reduce_invntt_to_ring_elem acc
      ⦃ (r : arithmetic.ring_arith.RingElem) =>
          ∀ n, n < 256 → ((r.val[n]!).val : ℤ) % 65536 = H n % 65536 ⦄ := by
  have hRD : (consts.RING_DEG : Usize).val = 256 := by simp only [consts.RING_DEG]; rfl
  unfold arithmetic.ntt.reduce_invntt_to_ring_elem
  let* ⟨v1, hv1a, hv1b⟩ ← reduce_loop0_spec { start := 0#usize, «end» := consts.RING_DEG } acc
    (Array.repeat 256#usize 0#i32) hRD hacc
  -- the Montgomery pass leaves `Rinv` times the accumulator's residue
  have hv1P : ∀ c, c < 256 → aP v1 c = Rinv * ((accZ acc c : ℤ) : Zp) := by
    intro c hc
    obtain ⟨hmod, _, _⟩ := hv1a c (Nat.zero_le c) hc
    have hcast : ((aZ v1 c * 2 ^ 32 : ℤ) : Zp) = ((accZ acc c : ℤ) : Zp) :=
      intCast_eq_of_emod hmod
    push_cast at hcast
    unfold aP
    calc ((aZ v1 c : ℤ) : Zp) = ((aZ v1 c : ℤ) : Zp) * ((16907691 : Zp) * Rinv) := by
          rw [twoPow32_Rinv, mul_one]
      _ = (((aZ v1 c : ℤ) : Zp) * (16907691 : Zp)) * Rinv := by ring
      _ = ((accZ acc c : ℤ) : Zp) * Rinv := by rw [hcast]
      _ = Rinv * ((accZ acc c : ℤ) : Zp) := by ring
  have hstate : State 256 1 Rinv h (aP v1) := by
    intro b hb r' hr'
    have hr0 : r' = 0 := by omega
    subst hr0
    simp only [Nat.mul_one, Nat.add_zero]
    rw [hv1P b hb, hst b hb]
  have hv1bd : ∀ x, x < 256 → |aZ v1 x| ≤ pNtt := by
    intro x hx
    obtain ⟨_, hlo, hhi⟩ := hv1a x (Nat.zero_le x) hx
    rw [abs_le]; constructor <;> omega
  let* ⟨v2, hv2a, hv2b⟩ ← invntt_full_spec v1 h Rinv hstate hv1bd
  have hv2 : ∀ x, x < 256 → aP v2 x = h x := by
    intro x hx
    rw [hv2a x hx, invScale_cancel, one_mul]
  rw [show (arithmetic.ring_arith.RingElem.Insts.CoreDefaultDefault.default :
      Result arithmetic.ring_arith.RingElem) = ok (Array.repeat 256#usize 0#u16) from rfl]
  simp only [bind_tc_ok]
  apply WP.spec_mono
    (reduce_loop1_spec { start := 0#usize, «end» := consts.RING_DEG } v2
      (Array.repeat 256#usize 0#u16) H hRD hv2b
      (fun c hc => by rw [hHz c hc, ← hv2 c hc]; rfl) hHb)
  rintro r ⟨hr1, _⟩
  exact fun n hn => hr1 n (Nat.zero_le n) hn

end Kopis.Properties
