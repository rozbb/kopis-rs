/-
  # Kopis/Avx2/TransposeSpec.lean — the extracted `transpose16` meets its model.

  `Kopis/Avx2/Transpose.lean` proves the transpose property of the *model*, on sixteen abstract
  256-bit words.  This file connects that to the extracted Rust: `inlane_transpose8` computes
  `inlane8`, and `transpose16` moves the block's `i16` at index `16m + k` to index `16k + m`.

  Both loops have literal bounds (2, 8, 8), so they are unrolled rather than given invariants:
  there is no induction to state, and unrolling keeps every step's index a numeral, which is what
  makes the `laneOf` bookkeeping discharge by `omega`.
-/
import Kopis.Avx2.Transpose

open Aeneas Aeneas.Std Result
open RustKopisAvx2
open RustKopisAvx2.backend.avx2.intrinsics

namespace Kopis.Avx2

set_option maxHeartbeats 2000000

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

/-- **`inlane_transpose8` computes `inlane8`.**  `Vec256` is an opaque type with no `Inhabited`
instance, so the input is described by an abstract lane function `V` rather than by `[·]!`. -/
theorem inlane_transpose8_spec (v : Array Vec256 8#usize) (V : ℕ → BitVec 256)
    (hV : ∀ (j : ℕ) (x : Vec256), v.val[j]? = some x → V j = bits x) :
    backend.avx2.ntt.inlane_transpose8 v
      ⦃ (r : Array Vec256 8#usize) => ∀ (p : ℕ) (x : Vec256), r.val[p]? = some x →
          bits x = inlane8 V p ⦄ := by
  unfold backend.avx2.ntt.inlane_transpose8
  let* ⟨ w0, hw0 ⟩ ← Array.index_usize_spec v 0#usize (by simp)
  let* ⟨ w1, hw1 ⟩ ← Array.index_usize_spec v 1#usize (by simp)
  obtain ⟨a0, ha0, hb0⟩ := unpacklo_epi16_model w0 w1
  rw [ha0, bind_tc_ok]
  obtain ⟨a1, ha1, hb1⟩ := unpackhi_epi16_model w0 w1
  rw [ha1, bind_tc_ok]
  let* ⟨ w2, hw2 ⟩ ← Array.index_usize_spec v 2#usize (by simp)
  let* ⟨ w3, hw3 ⟩ ← Array.index_usize_spec v 3#usize (by simp)
  obtain ⟨a2, ha2, hb2⟩ := unpacklo_epi16_model w2 w3
  rw [ha2, bind_tc_ok]
  obtain ⟨a3, ha3, hb3⟩ := unpackhi_epi16_model w2 w3
  rw [ha3, bind_tc_ok]
  let* ⟨ w4, hw4 ⟩ ← Array.index_usize_spec v 4#usize (by simp)
  let* ⟨ w5, hw5 ⟩ ← Array.index_usize_spec v 5#usize (by simp)
  obtain ⟨a4, ha4, hb4⟩ := unpacklo_epi16_model w4 w5
  rw [ha4, bind_tc_ok]
  obtain ⟨a5, ha5, hb5⟩ := unpackhi_epi16_model w4 w5
  rw [ha5, bind_tc_ok]
  let* ⟨ w6, hw6 ⟩ ← Array.index_usize_spec v 6#usize (by simp)
  let* ⟨ w7, hw7 ⟩ ← Array.index_usize_spec v 7#usize (by simp)
  obtain ⟨a6, ha6, hb6⟩ := unpacklo_epi16_model w6 w7
  rw [ha6, bind_tc_ok]
  obtain ⟨a7, ha7, hb7⟩ := unpackhi_epi16_model w6 w7
  rw [ha7, bind_tc_ok]
  obtain ⟨c0, hc0, hd0⟩ := unpacklo_epi32_model a0 a2
  rw [hc0, bind_tc_ok]
  obtain ⟨c1, hc1, hd1⟩ := unpackhi_epi32_model a0 a2
  rw [hc1, bind_tc_ok]
  obtain ⟨c2, hc2, hd2⟩ := unpacklo_epi32_model a1 a3
  rw [hc2, bind_tc_ok]
  obtain ⟨c3, hc3, hd3⟩ := unpackhi_epi32_model a1 a3
  rw [hc3, bind_tc_ok]
  obtain ⟨c4, hc4, hd4⟩ := unpacklo_epi32_model a4 a6
  rw [hc4, bind_tc_ok]
  obtain ⟨c5, hc5, hd5⟩ := unpackhi_epi32_model a4 a6
  rw [hc5, bind_tc_ok]
  obtain ⟨c6, hc6, hd6⟩ := unpacklo_epi32_model a5 a7
  rw [hc6, bind_tc_ok]
  obtain ⟨c7, hc7, hd7⟩ := unpackhi_epi32_model a5 a7
  rw [hc7, bind_tc_ok]
  obtain ⟨e0, he0, hf0⟩ := unpacklo_epi64_model c0 c4
  rw [he0, bind_tc_ok]
  let* ⟨ u0, hu0 ⟩ ← Array.update_spec v 0#usize e0 (by simp)
  obtain ⟨e1, he1, hf1⟩ := unpackhi_epi64_model c0 c4
  rw [he1, bind_tc_ok]
  let* ⟨ u1, hu1 ⟩ ← Array.update_spec u0 1#usize e1 (by simp)
  obtain ⟨e2, he2, hf2⟩ := unpacklo_epi64_model c1 c5
  rw [he2, bind_tc_ok]
  let* ⟨ u2, hu2 ⟩ ← Array.update_spec u1 2#usize e2 (by simp)
  obtain ⟨e3, he3, hf3⟩ := unpackhi_epi64_model c1 c5
  rw [he3, bind_tc_ok]
  let* ⟨ u3, hu3 ⟩ ← Array.update_spec u2 3#usize e3 (by simp)
  obtain ⟨e4, he4, hf4⟩ := unpacklo_epi64_model c2 c6
  rw [he4, bind_tc_ok]
  let* ⟨ u4, hu4 ⟩ ← Array.update_spec u3 4#usize e4 (by simp)
  obtain ⟨e5, he5, hf5⟩ := unpackhi_epi64_model c2 c6
  rw [he5, bind_tc_ok]
  let* ⟨ u5, hu5 ⟩ ← Array.update_spec u4 5#usize e5 (by simp)
  obtain ⟨e6, he6, hf6⟩ := unpacklo_epi64_model c3 c7
  rw [he6, bind_tc_ok]
  let* ⟨ u6, hu6 ⟩ ← Array.update_spec u5 6#usize e6 (by simp)
  obtain ⟨e7, he7, hf7⟩ := unpackhi_epi64_model c3 c7
  rw [he7, bind_tc_ok]
  let* ⟨ u7, hu7 ⟩ ← Array.update_spec u6 7#usize e7 (by simp)
  rename_i p x hx
  have hV0 : V 0 = bits w0 := hV 0 w0 (by rw [hw0]; exact List.getElem?_eq_getElem _)
  have hV1 : V 1 = bits w1 := hV 1 w1 (by rw [hw1]; exact List.getElem?_eq_getElem _)
  have hV2 : V 2 = bits w2 := hV 2 w2 (by rw [hw2]; exact List.getElem?_eq_getElem _)
  have hV3 : V 3 = bits w3 := hV 3 w3 (by rw [hw3]; exact List.getElem?_eq_getElem _)
  have hV4 : V 4 = bits w4 := hV 4 w4 (by rw [hw4]; exact List.getElem?_eq_getElem _)
  have hV5 : V 5 = bits w5 := hV 5 w5 (by rw [hw5]; exact List.getElem?_eq_getElem _)
  have hV6 : V 6 = bits w6 := hV 6 w6 (by rw [hw6]; exact List.getElem?_eq_getElem _)
  have hV7 : V 7 = bits w7 := hV 7 w7 (by rw [hw7]; exact List.getElem?_eq_getElem _)
  simp only [hu7, hu6, hu5, hu4, hu3, hu2, hu1, hu0, Std.Array.set_val_eq] at hx
  have hlen : v.val.length = 8 := v.property
  rcases (show p < 8 ∨ 8 ≤ p from by omega) with hp | hp
  · rcases (show p = 0 ∨ p = 1 ∨ p = 2 ∨ p = 3 ∨ p = 4 ∨ p = 5 ∨ p = 6 ∨ p = 7 from by omega)
      with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
      · simp only [List.getElem?_set, hlen, List.length_set] at hx
        norm_num at hx
        subst hx
        simp only [inlane8, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7,
          hd0, hd1, hd2, hd3, hd4, hd5, hd6, hd7,
          hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7,
          hV0, hV1, hV2, hV3, hV4, hV5, hV6, hV7]
  · exfalso
    rw [List.getElem?_eq_none (by simp [List.length_set, hlen]; omega)] at hx
    simp at hx

/-! ## The block as sixteen vectors

`transpose16` moves whole vectors, so the array is described one 16-lane block at a time: a
`store_i16` replaces one block and leaves the other fifteen alone.  Composing the pointwise
store spec sixteen times instead would leave sixteen nested range conditions at every index. -/

/-- Block `k` of a 256-`i16` array, as a 256-bit word. -/
def blockVec (b : Array I16 256#usize) (k : ℕ) : BitVec 256 :=
  ofLanes16 fun i => (b.val[16 * k + i]!).bv

theorem load_i16_block (b : Array I16 256#usize) (k : Usize) (hk : k.val < 16) :
    ∃ c, load_i16 b k = ok c ∧ bits c = blockVec b k.val := by
  obtain ⟨c, hc, h⟩ := load_i16_spec b k (by scalar_tac)
  exact ⟨c, hc, eq_of_lane16_bv fun i hi => by
    rw [blockVec, laneOf_ofLanes16 _ hi]; exact h i hi⟩

theorem store_i16_block (dst : Array I16 256#usize) (k : Usize) (v : Vec256) (hk : k.val < 16) :
    ∃ dst', store_i16 dst k v = ok dst' ∧ ∀ k' < 16,
      blockVec dst' k' = if k' = k.val then bits v else blockVec dst k' := by
  obtain ⟨d, hd, h⟩ := store_i16_spec dst k v (by scalar_tac)
  refine ⟨d, hd, fun k' hk' => ?_⟩
  by_cases he : k' = k.val
  · subst he
    rw [if_pos rfl]
    refine eq_of_lane16_bv fun i hi => ?_
    rw [blockVec, laneOf_ofLanes16 _ hi, h (16 * k.val + i) (by scalar_tac),
      if_pos (⟨by omega, by omega⟩ :
        16 * k.val ≤ 16 * k.val + i ∧ 16 * k.val + i < 16 * k.val + 16)]
    congr 1
    omega
  · rw [if_neg he]
    refine eq_of_lane16_bv fun i hi => ?_
    rw [blockVec, laneOf_ofLanes16 _ hi, h (16 * k' + i) (by scalar_tac), if_neg (by omega),
      blockVec, laneOf_ofLanes16 _ hi]

/-! ## `transpose16`

Two loops.  The inner one writes the eight transposed vectors of one 128-bit half into scratch;
the outer runs it for both halves; the last one recombines with `vperm2i128`.  These get
invariants rather than unrolling: the bound is literal but the accumulator is not, and an
invariant is shorter than eight copies of the same three steps. -/

/-- The inner store loop: blocks `8·half + start … 8·half + 8` take the transposed vectors. -/
theorem transpose16_loop0_loop0_spec (iter : core.ops.range.Range Usize)
    (scratch : Array I16 256#usize) (half : Usize) (v : Array Vec256 8#usize)
    (V8 : ℕ → BitVec 256) (hhalf : half.val < 2) (hend : iter.«end».val = 8)
    (hV8 : ∀ (j : ℕ) (x : Vec256), v.val[j]? = some x → V8 j = bits x) :
    backend.avx2.ntt.transpose16_loop0_loop0 iter scratch half v
      ⦃ (r : Array I16 256#usize) => ∀ k < 16,
          blockVec r k =
            if 8 * half.val + iter.start.val ≤ k ∧ k < 8 * half.val + 8
            then V8 (k - 8 * half.val) else blockVec scratch k ⦄ := by
  unfold backend.avx2.ntt.transpose16_loop0_loop0
  by_cases hlt : iter.start.val < iter.«end».val
  · let* ⟨ o, iter1, ho, hstart', hend' ⟩ ← core.iter.range.IteratorRange.next_Usize_some_spec
    rw [ho]; simp only
    step*
    obtain ⟨s1, hs1, hs1b⟩ := store_i16_block scratch i1 v1 (by scalar_tac)
    rw [hs1, bind_tc_ok]
    apply WP.spec_mono (transpose16_loop0_loop0_spec iter1 s1 half v V8 hhalf (by
      rw [hend']; exact hend) hV8)
    intro r hr k hk
    rw [hr k hk, hs1b k hk]
    have hv1 : V8 iter.start.val = bits v1 :=
      hV8 iter.start.val v1 (by rw [v1_post]; exact List.getElem?_eq_getElem _)
    by_cases h1 : 8 * half.val + iter1.start.val ≤ k ∧ k < 8 * half.val + 8
    · rw [if_pos h1, if_pos (show 8 * half.val + iter.start.val ≤ k ∧ k < 8 * half.val + 8
        from by omega)]
    · rw [if_neg h1]
      by_cases h2 : k = i1.val
      · rw [if_pos h2, if_pos (show 8 * half.val + iter.start.val ≤ k ∧ k < 8 * half.val + 8
          from by omega), ← hv1]
        congr 1
        omega
      · rw [if_neg h2, if_neg (show ¬(8 * half.val + iter.start.val ≤ k ∧ k < 8 * half.val + 8)
          from by omega)]
  · let* ⟨ o, iter1, hnone, _ ⟩ ← core.iter.range.IteratorRange.next_Usize_none_spec
    rw [hnone]; simp only [WP.spec_ok]
    intro k hk
    rw [if_neg (by omega)]
termination_by iter.«end».val - iter.start.val
decreasing_by scalar_decr_tac

/-- The outer loop: for each 128-bit half, eight loads, `inlane_transpose8`, eight stores. -/
theorem transpose16_loop0_spec (iter : core.ops.range.Range Usize)
    (b scratch : Array I16 256#usize) (hend : iter.«end».val = 2) :
    backend.avx2.ntt.transpose16_loop0 iter b scratch
      ⦃ (r : Array I16 256#usize) => ∀ k < 16,
          blockVec r k =
            if 8 * iter.start.val ≤ k
            then inlane8 (fun t => blockVec b (8 * (k / 8) + t)) (k % 8)
            else blockVec scratch k ⦄ := by
  unfold backend.avx2.ntt.transpose16_loop0
  by_cases hlt : iter.start.val < iter.«end».val
  · let* ⟨ o, iter1, ho, hstart', hend' ⟩ ← core.iter.range.IteratorRange.next_Usize_some_spec
    rw [ho]; simp only
    step*
    obtain ⟨d0, hd0, he0⟩ := load_i16_block b i (by scalar_tac)
    rw [hd0, bind_tc_ok]
    step*
    obtain ⟨d1, hd1, he1⟩ := load_i16_block b i1 (by scalar_tac)
    rw [hd1, bind_tc_ok]
    step*
    obtain ⟨d2, hd2, he2⟩ := load_i16_block b i2 (by scalar_tac)
    rw [hd2, bind_tc_ok]
    step*
    obtain ⟨d3, hd3, he3⟩ := load_i16_block b i3 (by scalar_tac)
    rw [hd3, bind_tc_ok]
    step*
    obtain ⟨d4, hd4, he4⟩ := load_i16_block b i4 (by scalar_tac)
    rw [hd4, bind_tc_ok]
    step*
    obtain ⟨d5, hd5, he5⟩ := load_i16_block b i5 (by scalar_tac)
    rw [hd5, bind_tc_ok]
    step*
    obtain ⟨d6, hd6, he6⟩ := load_i16_block b i6 (by scalar_tac)
    rw [hd6, bind_tc_ok]
    step*
    obtain ⟨d7, hd7, he7⟩ := load_i16_block b i7 (by scalar_tac)
    rw [hd7, bind_tc_ok]
    have hVin : ∀ (j : ℕ) (x : Vec256),
        (Array.make 8#usize [d0, d1, d2, d3, d4, d5, d6, d7]).val[j]? = some x →
          blockVec b (8 * iter.start.val + j) = bits x := by
      intro j x hx
      rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 ∨ 8 ≤ j
        from by omega) with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|hj
      · simp only [Array.make, List.getElem?_cons_zero, Option.some.injEq] at hx
        rw [← hx, he0]
        congr 1
        omega
      · simp only [Array.make, List.getElem?_cons_zero, List.getElem?_cons_succ,
          Option.some.injEq] at hx
        rw [← hx, he1]
        congr 1
        omega
      · simp only [Array.make, List.getElem?_cons_zero, List.getElem?_cons_succ,
          Option.some.injEq] at hx
        rw [← hx, he2]
        congr 1
        omega
      · simp only [Array.make, List.getElem?_cons_zero, List.getElem?_cons_succ,
          Option.some.injEq] at hx
        rw [← hx, he3]
        congr 1
        omega
      · simp only [Array.make, List.getElem?_cons_zero, List.getElem?_cons_succ,
          Option.some.injEq] at hx
        rw [← hx, he4]
        congr 1
        omega
      · simp only [Array.make, List.getElem?_cons_zero, List.getElem?_cons_succ,
          Option.some.injEq] at hx
        rw [← hx, he5]
        congr 1
        omega
      · simp only [Array.make, List.getElem?_cons_zero, List.getElem?_cons_succ,
          Option.some.injEq] at hx
        rw [← hx, he6]
        congr 1
        omega
      · simp only [Array.make, List.getElem?_cons_zero, List.getElem?_cons_succ,
          Option.some.injEq] at hx
        rw [← hx, he7]
        congr 1
        omega
      · exfalso
        rw [List.getElem?_eq_none (by simp [Array.make]; omega)] at hx
        simp at hx
    apply WP.spec_bind (inlane_transpose8_spec _ _ hVin)
    intro v8 hv8
    apply WP.spec_bind (transpose16_loop0_loop0_spec { start := 0#usize, «end» := 8#usize }
      scratch iter.start v8 (fun t => inlane8 (fun u => blockVec b (8 * iter.start.val + u)) t)
      (by omega) rfl (fun j x h => (hv8 j x h).symm))
    intro s1 hs1
    apply WP.spec_mono (transpose16_loop0_spec iter1 b s1 (by rw [hend']; exact hend))
    intro r hr k hk
    rw [hr k hk, hs1 k hk,
      show ({ start := 0#usize, «end» := 8#usize } : core.ops.range.Range Usize).start.val = 0
        from rfl, Nat.add_zero]
    by_cases h1 : 8 * iter1.start.val ≤ k
    · rw [if_pos h1, if_pos (by omega)]
    · rw [if_neg h1]
      by_cases h2 : 8 * iter.start.val ≤ k ∧ k < 8 * iter.start.val + 8
      · rw [if_pos h2, if_pos (by omega : 8 * iter.start.val ≤ k)]
        have hfun : (fun t => blockVec b (8 * (k / 8) + t))
            = fun u => blockVec b (8 * iter.start.val + u) := by
          funext t
          congr 1
          omega
        rw [hfun, show k % 8 = k - 8 * iter.start.val from by omega]
      · rw [if_neg h2, if_neg (by omega : ¬ 8 * iter.start.val ≤ k)]
  · let* ⟨ o, iter1, hnone, _ ⟩ ← core.iter.range.IteratorRange.next_Usize_none_spec
    rw [hnone]; simp only [WP.spec_ok]
    intro k hk
    rw [if_neg (by omega)]
termination_by iter.«end».val - iter.start.val
decreasing_by scalar_decr_tac

/-- The recombination loop: one `vperm2i128` pair per output row. -/
theorem transpose16_loop1_spec (iter : core.ops.range.Range Usize)
    (b scratch : Array I16 256#usize) (hend : iter.«end».val = 8) :
    backend.avx2.ntt.transpose16_loop1 iter b scratch
      ⦃ (r : Array I16 256#usize) => ∀ k < 16,
          blockVec r k =
            if iter.start.val ≤ k % 8 then
              (if k < 8
               then Model.permute2x128Si256 0x20#32 (blockVec scratch k) (blockVec scratch (8 + k))
               else Model.permute2x128Si256 0x31#32 (blockVec scratch (k - 8)) (blockVec scratch k))
            else blockVec b k ⦄ := by
  unfold backend.avx2.ntt.transpose16_loop1
  by_cases hlt : iter.start.val < iter.«end».val
  · let* ⟨ o, iter1, ho, hstart', hend' ⟩ ← core.iter.range.IteratorRange.next_Usize_some_spec
    rw [ho]; simp only
    obtain ⟨av, hav, havb⟩ := load_i16_block scratch iter.start (by scalar_tac)
    rw [hav, bind_tc_ok]
    step*
    obtain ⟨cv, hcv, hcvb⟩ := load_i16_block scratch i (by scalar_tac)
    rw [hcv, bind_tc_ok]
    obtain ⟨w, hw, hwb⟩ := permute2x128_si256_model 32#i32 av cv
    rw [hw, bind_tc_ok]
    obtain ⟨b1, hb1, hb1b⟩ := store_i16_block b iter.start w (by scalar_tac)
    rw [hb1, bind_tc_ok]
    obtain ⟨w1, hw1, hw1b⟩ := permute2x128_si256_model 49#i32 av cv
    rw [hw1, bind_tc_ok]
    obtain ⟨b2, hb2, hb2b⟩ := store_i16_block b1 i w1 (by scalar_tac)
    rw [hb2, bind_tc_ok]
    apply WP.spec_mono (transpose16_loop1_spec iter1 b2 scratch (by rw [hend']; exact hend))
    intro r hr k hk
    rw [hr k hk, hb2b k hk, hb1b k hk]
    rw [show I32.bv 32#i32 = 0x20#32 from by decide] at hwb
    rw [show I32.bv 49#i32 = 0x31#32 from by decide] at hw1b
    by_cases h1 : iter1.start.val ≤ k % 8
    · rw [if_pos h1, if_pos (show iter.start.val ≤ k % 8 from by omega)]
    · rw [if_neg h1]
      by_cases h2 : k % 8 = iter.start.val
      · rw [if_pos (by omega : iter.start.val ≤ k % 8)]
        by_cases h3 : k < 8
        · rw [if_neg (show ¬ k = i.val from by rw [i_post]; omega),
            if_pos (by omega : k = iter.start.val),
            if_pos h3, hwb, havb, hcvb]
          congr 2 <;> omega
        · rw [if_pos (show k = i.val from by rw [i_post]; omega), if_neg h3, hw1b, havb, hcvb]
          congr 2 <;> omega
      · rw [if_neg (show ¬ k = i.val from by rw [i_post]; omega),
          if_neg (by omega : ¬ k = iter.start.val),
          if_neg (by omega : ¬ iter.start.val ≤ k % 8)]
  · let* ⟨ o, iter1, hnone, _ ⟩ ← core.iter.range.IteratorRange.next_Usize_none_spec
    rw [hnone]; simp only [WP.spec_ok]
    intro k hk
    rw [if_neg (by omega)]
termination_by iter.«end».val - iter.start.val
decreasing_by scalar_decr_tac

/-- **`transpose16` computes `transpose16Model`.** -/
theorem transpose16_spec (b : Array I16 256#usize) :
    backend.avx2.ntt.transpose16 b
      ⦃ (r : Array I16 256#usize) => ∀ k < 16,
          blockVec r k = transpose16Model (blockVec b) k ⦄ := by
  unfold backend.avx2.ntt.transpose16
  apply WP.spec_bind (transpose16_loop0_spec { start := 0#usize, «end» := 2#usize } b
    (Array.repeat 256#usize 0#i16) rfl)
  intro s hs
  apply WP.spec_mono (transpose16_loop1_spec { start := 0#usize, «end» := 8#usize } b s rfl)
  intro r hr k hk
  have hz2 : ({ start := 0#usize, «end» := 2#usize } : core.ops.range.Range Usize).start.val = 0 :=
    rfl
  have hs0 : ∀ k' < 16, blockVec s k' = inlane8 (fun t => blockVec b (8 * (k' / 8) + t)) (k' % 8) :=
    fun k' hk' => by rw [hs k' hk', hz2, if_pos (by omega)]
  have hz8 : ({ start := 0#usize, «end» := 8#usize } : core.ops.range.Range Usize).start.val = 0 :=
    rfl
  rw [hr k hk, hz8, if_pos (show 0 ≤ k % 8 from by omega), transpose16Model]
  by_cases h3 : k < 8
  · rw [if_pos h3, if_pos h3, hs0 k hk, hs0 (8 + k) (by omega),
      show k / 8 = 0 from by omega, show k % 8 = k from by omega,
      show (8 + k) / 8 = 1 from by omega, show (8 + k) % 8 = k from by omega]
    simp only [Nat.mul_zero, Nat.zero_add, Nat.mul_one]
  · rw [if_neg h3, if_neg h3, hs0 (k - 8) (by omega), hs0 k hk,
      show (k - 8) / 8 = 0 from by omega, show (k - 8) % 8 = k - 8 from by omega,
      show k / 8 = 1 from by omega, show k % 8 = k - 8 from by omega]
    simp only [Nat.mul_zero, Nat.zero_add, Nat.mul_one]

/-- **The transpose, coefficient by coefficient.**  The `i16` at index `16m + k` moves to index
`16k + m`. -/
theorem transpose16_coeff (b : Array I16 256#usize) :
    backend.avx2.ntt.transpose16 b
      ⦃ (r : Array I16 256#usize) => ∀ k < 16, ∀ m < 16,
          (r.val[16 * k + m]!).bv = (b.val[16 * m + k]!).bv ⦄ := by
  apply WP.spec_mono (transpose16_spec b)
  intro r hr k hk m hm
  have hL : laneOf 16 (blockVec r k) m = (r.val[16 * k + m]!).bv := by
    rw [blockVec, laneOf_ofLanes16 _ hm]
  have hR : laneOf 16 (blockVec b m) k = (b.val[16 * m + k]!).bv := by
    rw [blockVec, laneOf_ofLanes16 _ hk]
  rw [← hL, ← hR, hr k hk, laneOf_transpose16Model (blockVec b) k m hk hm]

/-- **`transpose16` is an involution** — the Rust doc's claim, and what lets the transform go
back into coefficient order after running its four innermost levels vertically. -/
theorem transpose16_involutive (b : Array I16 256#usize) :
    (do let t ← backend.avx2.ntt.transpose16 b
        backend.avx2.ntt.transpose16 t)
      ⦃ (r : Array I16 256#usize) => ∀ j < 256, (r.val[j]!).bv = (b.val[j]!).bv ⦄ := by
  apply WP.spec_bind (transpose16_coeff b)
  intro t ht
  apply WP.spec_mono (transpose16_coeff t)
  intro r hr j hj
  have hsplit : 16 * (j / 16) + j % 16 = j := by omega
  have h1 := hr (j / 16) (by omega) (j % 16) (by omega)
  have h2 := ht (j % 16) (by omega) (j / 16) (by omega)
  rw [hsplit] at h1
  rw [h1, h2, hsplit]

end Kopis.Avx2
