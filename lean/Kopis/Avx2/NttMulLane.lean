/-
  # Kopis/Avx2/NttMulLane.lean — what `pointwise_mul_acc` actually computes.

  The AVX2 `pointwise_mul_acc` does **not** compute the same function as the portable loop it
  sits next to, and it is not meant to.  The portable branch multiplies whole `i32`s into an
  `i64`; the vector branch reads the same arrays as 512 `i16` and 512 `i32` and computes

      acc32[t] += lhs16[t] · rhs16[t]      for every t < 512

  with no carry between the two halves of an `i64`.  That is the two-prime CRT representation:
  each `i32` holds one residue mod `q₁` and one mod `q₂`, and the two are multiplied
  independently.  See the phase E/F notes in `AVX2_VERIFICATION_PLAN.md` for why this means the
  serial spec cannot be transferred.

  This file proves the statement above.  The interesting step is the middle: `vpmullw` and
  `vpmulhw` give the low and high halves of each 16×16 product, and the `vpunpck`/`vperm2i128`
  pair rejoins them into 32-bit products *in coefficient order*.
-/
import Kopis.Avx2.Transpose

open Aeneas Aeneas.Std Result
open RustKopisAvx2
open RustKopisAvx2.backend.avx2.intrinsics

namespace Kopis.Avx2

set_option maxHeartbeats 2000000

/-! ## Reading the arrays at half width -/

/-- The `t`-th of the 512 `i16` a 256-`i32` array is read as. -/
def i16View (a : Array I32 256#usize) (t : ℕ) : BitVec 16 :=
  BitVec.extractLsb' (16 * (t % 2)) 16 (a.val[t / 2]!).bv

/-- The `t`-th of the 512 `i32` a 256-`i64` array is read as. -/
def i32View (a : Array I64 256#usize) (t : ℕ) : BitVec 32 :=
  BitVec.extractLsb' (32 * (t % 2)) 32 (a.val[t / 2]!).bv

/-- The 32-bit signed product of the two `i16` lanes at position `t`. -/
def prod32 (lhs rhs : Array I32 256#usize) (t : ℕ) : BitVec 32 :=
  (i16View lhs t).signExtend 32 * (i16View rhs t).signExtend 32

/-! ## Rejoining the halves of a 16×16 product

`vpmullw` keeps the low 16 bits and `vpmulhw` the high 16; `vpunpcklwd` puts them back together
in the order `hi ++ lo`, which is the 32-bit product. -/

private theorem join_prod (a b : BitVec 16) :
    BitVec.extractLsb' 16 16 (a.signExtend 32 * b.signExtend 32) ++ (a * b)
      = a.signExtend 32 * b.signExtend 32 := by bv_decide

/-- The first output vector holds the 32-bit products of `i16` lanes `0 … 8`. -/
theorem prod_lane_first (l r : BitVec 256) (k : ℕ) (hk : k < 8) :
    laneOf 32 (Model.permute2x128Si256 0x20#32
        (Model.unpackloEpi16 (Model.mulloEpi16 l r) (Model.mulhiEpi16 l r))
        (Model.unpackhiEpi16 (Model.mulloEpi16 l r) (Model.mulhiEpi16 l r))) k
      = (laneOf 16 l k).signExtend 32 * (laneOf 16 r k).signExtend 32 := by
  rw [lane32_eq_lane16]
  rcases (show k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 from by omega)
    with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
    · norm_num [lane16_perm2x128_20, lane16_unpackloEpi16, lane16_unpackhiEpi16,
        Model.mulloEpi16, Model.mulhiEpi16, laneOf_ofLanes16]
      rw [join_prod]

/-- The second output vector holds the products of `i16` lanes `8 … 16`. -/
theorem prod_lane_second (l r : BitVec 256) (k : ℕ) (hk : k < 8) :
    laneOf 32 (Model.permute2x128Si256 0x31#32
        (Model.unpackloEpi16 (Model.mulloEpi16 l r) (Model.mulhiEpi16 l r))
        (Model.unpackhiEpi16 (Model.mulloEpi16 l r) (Model.mulhiEpi16 l r))) k
      = (laneOf 16 l (8 + k)).signExtend 32 * (laneOf 16 r (8 + k)).signExtend 32 := by
  rw [lane32_eq_lane16]
  rcases (show k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 from by omega)
    with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
    · norm_num [lane16_perm2x128_31, lane16_unpackloEpi16, lane16_unpackhiEpi16,
        Model.mulloEpi16, Model.mulhiEpi16, laneOf_ofLanes16]
      rw [join_prod]

/-! ## The half-width loads and stores, at vector granularity -/

/-- The eight `i32` at `i32`-index `8i`, as a 256-bit word. -/
def accVec (a : Array I64 256#usize) (i : ℕ) : BitVec 256 := ofLanes32 fun k => i32View a (8 * i + k)

private theorem extract_lo (h l : BitVec 32) : BitVec.extractLsb' 0 32 (h ++ l) = l := by bv_decide
private theorem extract_hi (h l : BitVec 32) : BitVec.extractLsb' 32 32 (h ++ l) = h := by bv_decide

theorem load_i16_view (a : Array I32 256#usize) (i : Usize) (hi : i.val < 32) :
    ∃ c, load_i16_of_i32 a i = ok c ∧ ∀ k < 16, lane16 c k = i16View a (16 * i.val + k) :=
  load_i16_of_i32_spec a i (by scalar_tac)

theorem load_i32_view (a : Array I64 256#usize) (i : Usize) (hi : i.val < 64) :
    ∃ c, load_i32_of_i64 a i = ok c ∧ bits c = accVec a i.val := by
  obtain ⟨c, hc, h⟩ := load_i32_of_i64_spec a i (by scalar_tac)
  exact ⟨c, hc, eq_of_lane32_bv fun k hk => by
    rw [accVec, laneOf_ofLanes32 _ hk]; exact h k hk⟩

theorem store_i32_view (a : Array I64 256#usize) (i : Usize) (v : Vec256) (hi : i.val < 64) :
    ∃ a', store_i32_of_i64 a i v = ok a' ∧ ∀ t < 512,
      i32View a' t =
        if 8 * i.val ≤ t ∧ t < 8 * i.val + 8 then laneOf 32 (bits v) (t - 8 * i.val)
        else i32View a t := by
  obtain ⟨d, hd, h⟩ := store_i32_of_i64_spec a i v (by scalar_tac)
  refine ⟨d, hd, fun t ht => ?_⟩
  rw [i32View, h (t / 2) (by scalar_tac)]
  by_cases hin : 8 * i.val ≤ t ∧ t < 8 * i.val + 8
  · rw [if_pos (by omega : 4 * i.val ≤ t / 2 ∧ t / 2 < 4 * i.val + 4), if_pos hin]
    rcases (show t % 2 = 0 ∨ t % 2 = 1 from by omega) with h2 | h2
    · rw [h2, Nat.mul_zero, extract_lo]
      congr 1
      omega
    · rw [h2, Nat.mul_one, extract_hi]
      congr 1
      omega
  · rw [if_neg (by omega : ¬(4 * i.val ≤ t / 2 ∧ t / 2 < 4 * i.val + 4)), if_neg hin, i32View]

/-! ## The two loops -/

/-- The inner loop: sixteen vectors of one block, each sixteen `i16` products. -/
theorem pointwise_mul_acc_loop0_loop0_spec (iter : core.ops.range.Range Usize)
    (acc : Array I64 256#usize) (lhs rhs : Array I32 256#usize) (block : Usize)
    (hblock : block.val < 2) (hend : iter.«end».val = 16) :
    backend.avx2.ntt.pointwise_mul_acc_loop0_loop0 iter acc lhs rhs block
      ⦃ (r : Array I64 256#usize) => ∀ t < 512,
          i32View r t =
            if 256 * block.val + 16 * iter.start.val ≤ t ∧ t < 256 * block.val + 256
            then i32View acc t + prod32 lhs rhs t else i32View acc t ⦄ := by
  unfold backend.avx2.ntt.pointwise_mul_acc_loop0_loop0
  by_cases hlt : iter.start.val < iter.«end».val
  · let* ⟨ o, iter1, ho, hstart', hend' ⟩ ← core.iter.range.IteratorRange.next_Usize_some_spec
    rw [ho]; simp only
    step*
    obtain ⟨lv, hlv, hlvb⟩ := load_i16_view lhs i2 (by scalar_tac)
    rw [hlv, bind_tc_ok]
    step*
    obtain ⟨rv, hrv, hrvb⟩ := load_i16_view rhs i3 (by scalar_tac)
    rw [hrv, bind_tc_ok]
    obtain ⟨lov, hlo, hlob⟩ := mullo_epi16_model lv rv
    rw [hlo, bind_tc_ok]
    obtain ⟨hiv, hhi, hhib⟩ := mulhi_epi16_model lv rv
    rw [hhi, bind_tc_ok]
    obtain ⟨p0, hp0, hp0b⟩ := unpacklo_epi16_model lov hiv
    rw [hp0, bind_tc_ok]
    obtain ⟨p1, hp1, hp1b⟩ := unpackhi_epi16_model lov hiv
    rw [hp1, bind_tc_ok]
    obtain ⟨fst, hfst, hfstb⟩ := permute2x128_si256_model 32#i32 p0 p1
    rw [hfst, bind_tc_ok]
    obtain ⟨snd, hsnd, hsndb⟩ := permute2x128_si256_model 49#i32 p0 p1
    rw [hsnd, bind_tc_ok]
    step*
    obtain ⟨vv, hv, hvb⟩ := load_i32_view acc a0 (by scalar_tac)
    rw [hv, bind_tc_ok]
    obtain ⟨v1, hv1, hv1b⟩ := add_epi32_model vv fst
    rw [hv1, bind_tc_ok]
    obtain ⟨acc1, hacc1, hacc1b⟩ := store_i32_view acc a0 v1 (by scalar_tac)
    rw [hacc1, bind_tc_ok]
    obtain ⟨v2, hv2, hv2b⟩ := load_i32_view acc1 a1 (by scalar_tac)
    rw [hv2, bind_tc_ok]
    obtain ⟨v3, hv3, hv3b⟩ := add_epi32_model v2 snd
    rw [hv3, bind_tc_ok]
    obtain ⟨acc2, hacc2, hacc2b⟩ := store_i32_view acc1 a1 v3 (by scalar_tac)
    rw [hacc2, bind_tc_ok]
    -- the two output vectors hold the products of the sixteen lanes, in order
    rw [show I32.bv 32#i32 = 0x20#32 from by decide] at hfstb
    rw [show I32.bv 49#i32 = 0x31#32 from by decide] at hsndb
    have hfstl : ∀ k < 8, laneOf 32 (bits fst) k = prod32 lhs rhs (8 * a0.val + k) := by
      intro k hk
      rw [hfstb, hp0b, hp1b, hlob, hhib, prod_lane_first _ _ k hk, prod32]
      rw [show laneOf 16 (bits lv) k = i16View lhs (16 * i2.val + k) from hlvb k (by omega),
        show laneOf 16 (bits rv) k = i16View rhs (16 * i3.val + k) from hrvb k (by omega),
        show 16 * i2.val + k = 8 * a0.val + k from by omega,
        show 16 * i3.val + k = 8 * a0.val + k from by omega]
    have hsndl : ∀ k < 8, laneOf 32 (bits snd) k = prod32 lhs rhs (8 * a0.val + 8 + k) := by
      intro k hk
      rw [hsndb, hp0b, hp1b, hlob, hhib, prod_lane_second _ _ k hk, prod32]
      rw [show laneOf 16 (bits lv) (8 + k) = i16View lhs (16 * i2.val + (8 + k)) from
          hlvb (8 + k) (by omega),
        show laneOf 16 (bits rv) (8 + k) = i16View rhs (16 * i3.val + (8 + k)) from
          hrvb (8 + k) (by omega),
        show 16 * i2.val + (8 + k) = 8 * a0.val + 8 + k from by omega,
        show 16 * i3.val + (8 + k) = 8 * a0.val + 8 + k from by omega]
    -- so the two stores add the product into the sixteen accumulator slots of this vector
    have hacc2v : ∀ t < 512, i32View acc2 t =
        if 8 * a0.val ≤ t ∧ t < 8 * a0.val + 16 then i32View acc t + prod32 lhs rhs t
        else i32View acc t := by
      intro t ht
      rw [hacc2b t ht]
      by_cases h1 : 8 * a1.val ≤ t ∧ t < 8 * a1.val + 8
      · rw [if_pos h1, hv3b, Model.addEpi32, laneOf_ofLanes32 _ (by omega), hv2b,
          hsndl _ (by omega),
          accVec, laneOf_ofLanes32 _ (by omega), hacc1b _ (by omega),
          if_neg (by omega : ¬(8 * a0.val ≤ 8 * a1.val + (t - 8 * a1.val)
            ∧ 8 * a1.val + (t - 8 * a1.val) < 8 * a0.val + 8)),
          if_pos (by omega : 8 * a0.val ≤ t ∧ t < 8 * a0.val + 16),
          show 8 * a1.val + (t - 8 * a1.val) = t from by omega,
          show 8 * a0.val + 8 + (t - 8 * a1.val) = t from by omega]
      · rw [if_neg h1, hacc1b t ht]
        by_cases h2 : 8 * a0.val ≤ t ∧ t < 8 * a0.val + 8
        · rw [if_pos h2, hv1b, Model.addEpi32, laneOf_ofLanes32 _ (by omega), hvb,
            hfstl _ (by omega),
            accVec, laneOf_ofLanes32 _ (by omega),
            if_pos (by omega : 8 * a0.val ≤ t ∧ t < 8 * a0.val + 16),
            show 8 * a0.val + (t - 8 * a0.val) = t from by omega]
        · rw [if_neg h2, if_neg (by omega : ¬(8 * a0.val ≤ t ∧ t < 8 * a0.val + 16))]
    apply WP.spec_mono (pointwise_mul_acc_loop0_loop0_spec iter1 acc2 lhs rhs block hblock
      (by rw [hend']; exact hend))
    intro r hr t ht
    rw [hr t ht, hacc2v t ht]
    by_cases h1 : 256 * block.val + 16 * iter1.start.val ≤ t ∧ t < 256 * block.val + 256
    · rw [if_pos h1, if_neg (by omega : ¬(8 * a0.val ≤ t ∧ t < 8 * a0.val + 16)),
        if_pos (by omega : 256 * block.val + 16 * iter.start.val ≤ t
          ∧ t < 256 * block.val + 256)]
    · rw [if_neg h1]
      by_cases h2 : 8 * a0.val ≤ t ∧ t < 8 * a0.val + 16
      · rw [if_pos h2, if_pos (by omega : 256 * block.val + 16 * iter.start.val ≤ t
          ∧ t < 256 * block.val + 256)]
      · rw [if_neg h2, if_neg (by omega : ¬(256 * block.val + 16 * iter.start.val ≤ t
          ∧ t < 256 * block.val + 256))]
  · let* ⟨ o, iter1, hnone, _ ⟩ ← core.iter.range.IteratorRange.next_Usize_none_spec
    rw [hnone]; simp only [WP.spec_ok]
    intro t ht
    rw [if_neg (by omega)]
termination_by iter.«end».val - iter.start.val
decreasing_by scalar_decr_tac

/-- The outer loop: the two blocks. -/
theorem pointwise_mul_acc_loop0_spec (iter : core.ops.range.Range Usize)
    (acc : Array I64 256#usize) (lhs rhs : Array I32 256#usize) (hend : iter.«end».val = 2) :
    backend.avx2.ntt.pointwise_mul_acc_loop0 iter acc lhs rhs
      ⦃ (r : Array I64 256#usize) => ∀ t < 512,
          i32View r t =
            if 256 * iter.start.val ≤ t then i32View acc t + prod32 lhs rhs t
            else i32View acc t ⦄ := by
  have hz : ({ start := 0#usize, «end» := 16#usize } : core.ops.range.Range Usize).start.val = 0 :=
    rfl
  unfold backend.avx2.ntt.pointwise_mul_acc_loop0
  by_cases hlt : iter.start.val < iter.«end».val
  · let* ⟨ o, iter1, ho, hstart', hend' ⟩ ← core.iter.range.IteratorRange.next_Usize_some_spec
    rw [ho]; simp only
    apply WP.spec_bind (pointwise_mul_acc_loop0_loop0_spec { start := 0#usize, «end» := 16#usize }
      acc lhs rhs iter.start (by omega) rfl)
    intro acc1 hacc1
    apply WP.spec_mono (pointwise_mul_acc_loop0_spec iter1 acc1 lhs rhs (by rw [hend']; exact hend))
    intro r hr t ht
    rw [hr t ht, hacc1 t ht, hz, Nat.mul_zero, Nat.add_zero]
    by_cases h1 : 256 * iter1.start.val ≤ t
    · rw [if_pos h1, if_neg (by omega : ¬(256 * iter.start.val ≤ t
        ∧ t < 256 * iter.start.val + 256)), if_pos (by omega : 256 * iter.start.val ≤ t)]
    · rw [if_neg h1]
      by_cases h2 : 256 * iter.start.val ≤ t ∧ t < 256 * iter.start.val + 256
      · rw [if_pos h2, if_pos (by omega : 256 * iter.start.val ≤ t)]
      · rw [if_neg h2, if_neg (by omega : ¬ 256 * iter.start.val ≤ t)]
  · let* ⟨ o, iter1, hnone, _ ⟩ ← core.iter.range.IteratorRange.next_Usize_none_spec
    rw [hnone]; simp only [WP.spec_ok]
    intro t ht
    rw [if_neg (by omega)]
termination_by iter.«end».val - iter.start.val
decreasing_by scalar_decr_tac

/-- **What `pointwise_mul_acc` computes.**  Reading the `i32` operands as 512 `i16` and the `i64`
accumulator as 512 `i32`, it adds the lanewise product into every slot — independently, with no
carry between the two halves of an `i64`.  That is *not* the portable branch's `i32 × i32 → i64`
product; it is the two-prime CRT representation, where each `i32` holds one residue per prime. -/
theorem pointwise_mul_acc_lane_spec (acc : Array I64 256#usize) (lhs rhs : Array I32 256#usize) :
    backend.avx2.ntt.pointwise_mul_acc acc lhs rhs
      ⦃ (r : Array I64 256#usize) => ∀ t < 512,
          i32View r t = i32View acc t + prod32 lhs rhs t ⦄ := by
  have hz : ({ start := 0#usize, «end» := 2#usize } : core.ops.range.Range Usize).start.val = 0 :=
    rfl
  unfold backend.avx2.ntt.pointwise_mul_acc
  apply WP.spec_mono (pointwise_mul_acc_loop0_spec { start := 0#usize, «end» := 2#usize }
    acc lhs rhs rfl)
  intro r hr t ht
  rw [hr t ht, hz, Nat.mul_zero, if_pos (Nat.zero_le t)]

end Kopis.Avx2
