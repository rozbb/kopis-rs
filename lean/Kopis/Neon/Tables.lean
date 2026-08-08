/-
  # Kopis/Neon/Tables.lean — the per-lane ψ tables (plan phase F4).

  The last three NTT levels run on a transposed group, so lane `m` of vector `k` owns a different
  coefficient block from lane `m+1` and each lane needs its *own* twiddle.  `lane_tbl` in
  `src/backend/neon/ntt.rs` builds those tables at compile time: entry `8g + m` of a table is

      zetas[base + g_hi·q_stride + g_lo·h_stride + m·m_stride]

  with `g = g_hi·h_count + g_lo` splitting the group index into "which group of eight vectors"
  and "which butterfly pair within the level", optionally negated for the inverse transform's
  Gentleman-Sande butterfly.  Its twin `zq` holds `z ·(wrapping) q⁻¹`, which is what makes
  `mont_mul` a Montgomery multiply.

  This file pins that construction down: `tblIdx` and `tblZ` name the entry, `tblZq` names its
  Montgomery twin, `tblZq_mont` proves `zq·q ≡ z (mod 2¹⁶)` — precisely the `hzq` side condition
  of `mont_mul_lane_spec`, and the only property of `zq` any butterfly ever uses — and the two
  loop specs say the extracted table holds exactly those entries.

  It is the NEON counterpart of `Kopis/Avx2/Tables.lean` and nothing transfers: AVX2's tables are
  indexed by a 16-lane arrangement and this one by a six-parameter stride scheme.  That is what
  §1(c) of the plan means when it lists `Tables.lean` among the files about the shared scheme but
  the lane arrangement as the new work.

  What is deliberately *not* here: which `zetas` entries each of the twelve concrete tables
  reaches, and the proof that they are the ψ powers the serial transform's `k` counter would have
  used.  That is stated against the walk and belongs with it.

  ## The hypotheses, and why they are hypotheses

  Every arithmetic step below is an `Isize` operation that aeneas makes fallible, and the array
  read `zetas[idx as usize]` needs `0 ≤ idx < 256`.  Both are properties of the *parameters*, not
  facts to be discharged in passing — and all twelve call sites use `|stride| ≤ 32`,
  `0 ≤ base ≤ 255` and a `g` below 16, so each discharges them by evaluation.  `hzne` is the same
  kind of thing: negating a `zetas` entry is fallible at `−2¹⁵`, and no ψ is anywhere near.
-/
import Kopis.Neon.NttGrowth

open Aeneas Aeneas.Std Result
open RustKopisNeon

namespace Kopis.Neon

set_option maxHeartbeats 1000000
set_option maxRecDepth 20000

/-! ## What an entry is -/

/-- The part of the index that depends on the group: `base + g_hi·q_stride + g_lo·h_stride`,
with `g = g_hi·h_count + g_lo`. -/
def tblC (base qStride hStride : ℤ) (hCount g : ℕ) : ℤ :=
  base + ((g / hCount : ℕ) : ℤ) * qStride + ((g % hCount : ℕ) : ℤ) * hStride

/-- The `zetas` index entry `8g + m` reads, once the group index has been split.  `c` is
`base + g_hi·q_stride + g_lo·h_stride`; the `m·m_stride` is what varies inside a group. -/
def tblIdx (c mStride : ℤ) (m : ℕ) : ℤ := c + (m : ℤ) * mStride

/-- The value written into `z`: a `zetas` entry, negated for the inverse tables. -/
def tblZ (zetas : Array I16 256#usize) (neg : Bool) (idx : ℤ) : ℤ :=
  if neg then -((zetas.val[idx.toNat]!).val) else (zetas.val[idx.toNat]!).val

/-- The value written into `zq`: the wrapping product with `q⁻¹`. -/
def tblZq (v qinv : ℤ) : ℤ := (v * qinv).bmod (2 ^ 16)

/-- **`zq` satisfies the Montgomery side condition.**  Given that `q⁻¹` inverts `q` mod `2¹⁶`,
the table's `zq` entry satisfies `zq·q ≡ z (mod 2¹⁶)` — which is exactly the `hzq` hypothesis of
`mont_mul_lane_spec`, and the only property of `zq` the transform ever uses. -/
theorem tblZq_mont (v qinv Q : ℤ) (hinv : (2 ^ 16 : ℤ) ∣ (qinv * Q - 1)) :
    (2 ^ 16 : ℤ) ∣ (tblZq v qinv * Q - v) := by
  unfold tblZq
  obtain ⟨k, hk⟩ : (2 ^ 16 : ℤ) ∣ ((v * qinv).bmod (2 ^ 16) - v * qinv) := by
    have h : ((v * qinv).bmod (2 ^ 16)) % (2 ^ 16) = (v * qinv) % (2 ^ 16) := by
      unfold Int.bmod
      norm_num
      split <;> omega
    exact dvd_sub_comm.mp (Int.ModEq.dvd h)
  obtain ⟨l, hl⟩ := hinv
  refine ⟨k * Q + v * l, ?_⟩
  have hb : (v * qinv).bmod (2 ^ 16) = v * qinv + 2 ^ 16 * k := by linarith
  have hq : qinv * Q = 1 + 2 ^ 16 * l := by linarith
  rw [hb]
  calc (v * qinv + 2 ^ 16 * k) * Q - v
      = v * (qinv * Q) + 2 ^ 16 * (k * Q) - v := by ring
    _ = v * (1 + 2 ^ 16 * l) + 2 ^ 16 * (k * Q) - v := by rw [hq]
    _ = 2 ^ 16 * (k * Q + v * l) := by ring

/-- `getElem!` after a `List.set` at an in-bounds index. -/
private theorem getElem!_set {α : Type _} [Inhabited α] (l : List α) (j : ℕ)
    (v : α) (k : ℕ) (hj : j < l.length) :
    (l.set j v)[k]! = if k = j then v else l[k]! := by
  by_cases h : k = j
  · subst h
    rw [getElem!_pos _ k (by rw [List.length_set]; exact hj), List.getElem_set_self, if_pos rfl]
  · by_cases hk : k < l.length
    · rw [getElem!_pos _ k (by rw [List.length_set]; exact hk),
        List.getElem_set_of_ne (Ne.symm h), ← getElem!_pos _ k hk, if_neg h]
    · rw [getElem!_neg _ k (by rw [List.length_set]; exact hk), getElem!_neg _ k hk, if_neg h]

/-! ## The inner loop: the eight lanes of one group

`m` runs from 0 to 8, writing `z[8g+m]` and `zq[8g+m]`.  The spec records that everything outside
`[8g+m, 8g+8)` is untouched, which is what lets the outer loop compose. -/

theorem lane_tbl_inner_spec {N : Usize} (zetas : Array I16 256#usize) (qinv : I16)
    (base q_stride h_stride m_stride : Isize) (neg : Bool)
    (z zq : Array I16 N) (g : Usize) (g_hi g_lo : Isize) (m : Usize)
    (hgN : 8 * g.val + 8 ≤ N.val)
    (hb : 0 ≤ base.val ∧ base.val ≤ 255)
    (hgh : |g_hi.val| ≤ 16) (hgl : |g_lo.val| ≤ 16)
    (hqs : |q_stride.val| ≤ 32) (hhs : |h_stride.val| ≤ 32) (hms : |m_stride.val| ≤ 32)
    (hzne : ∀ k < 256, (zetas.val[k]!).val ≠ -32768)
    (hidx : ∀ k < 8,
      0 ≤ tblIdx (base.val + g_hi.val * q_stride.val + g_lo.val * h_stride.val) m_stride.val k ∧
      tblIdx (base.val + g_hi.val * q_stride.val + g_lo.val * h_stride.val) m_stride.val k
        < 256) :
    backend.neon.ntt.lane_tbl_loop0_loop0 zetas qinv base q_stride h_stride m_stride neg
        z zq g g_hi g_lo m
      ⦃ (r : Array I16 N × Array I16 N) => ∀ j < N.val,
          (r.1.val[j]!).val =
            (if 8 * g.val + m.val ≤ j ∧ j < 8 * g.val + 8 then
                tblZ zetas neg (tblIdx (base.val + g_hi.val * q_stride.val
                  + g_lo.val * h_stride.val) m_stride.val (j - 8 * g.val))
              else (z.val[j]!).val) ∧
          (r.2.val[j]!).val =
            (if 8 * g.val + m.val ≤ j ∧ j < 8 * g.val + 8 then
                tblZq (tblZ zetas neg (tblIdx (base.val + g_hi.val * q_stride.val
                  + g_lo.val * h_stride.val) m_stride.val (j - 8 * g.val))) qinv.val
              else (zq.val[j]!).val) ⦄ := by
  unfold backend.neon.ntt.lane_tbl_loop0_loop0
  by_cases hlt : m < 8#usize
  · rw [if_pos hlt]
    have hm8 : m.val < 8 := by scalar_tac
    have hzlen : z.val.length = N.val := by have := z.property; scalar_tac
    have hzqlen : zq.val.length = N.val := by have := zq.property; scalar_tac
    obtain ⟨hidx0, hidx1⟩ := hidx m.val hm8
    unfold tblIdx at hidx0 hidx1
    -- every intermediate is bounded by a few hundred, so nothing overflows an `isize`
    have hgh' := abs_le.mp hgh
    have hgl' := abs_le.mp hgl
    have hqs' := abs_le.mp hqs
    have hhs' := abs_le.mp hhs
    have hms' := abs_le.mp hms
    have hp1 : -512 ≤ g_hi.val * q_stride.val ∧ g_hi.val * q_stride.val ≤ 512 := by
      constructor <;> nlinarith [hgh'.1, hgh'.2, hqs'.1, hqs'.2]
    have hp2 : -512 ≤ g_lo.val * h_stride.val ∧ g_lo.val * h_stride.val ≤ 512 := by
      constructor <;> nlinarith [hgl'.1, hgl'.2, hhs'.1, hhs'.2]
    let* ⟨ i, hi ⟩ ← Std.Isize.mul_spec (x := g_hi) (y := q_stride) (by scalar_tac)
      (by scalar_tac)
    let* ⟨ i1, hi1 ⟩ ← Std.Isize.add_spec (x := base) (y := i) (by scalar_tac) (by scalar_tac)
    let* ⟨ i2, hi2 ⟩ ← Std.Isize.mul_spec (x := g_lo) (y := h_stride) (by scalar_tac)
      (by scalar_tac)
    let* ⟨ i3, hi3 ⟩ ← Std.Isize.add_spec (x := i1) (y := i2) (by scalar_tac) (by scalar_tac)
    let* ⟨ i4, hi4 ⟩ ← UScalar.hcast_inBounds_spec .Isize m (by scalar_tac)
    have hi4eq : i4.val = (m.val : ℤ) := by scalar_tac
    have hp3 : -256 ≤ i4.val * m_stride.val ∧ i4.val * m_stride.val ≤ 256 := by
      have h0 : 0 ≤ i4.val := by scalar_tac
      have h8 : i4.val ≤ 8 := by scalar_tac
      constructor <;> nlinarith [hms'.1, hms'.2, h0, h8]
    let* ⟨ i5, hi5 ⟩ ← Std.Isize.mul_spec (x := i4) (y := m_stride) (by scalar_tac)
      (by scalar_tac)
    let* ⟨ idx, hidxv ⟩ ← Std.Isize.add_spec (x := i3) (y := i5) (by scalar_tac) (by scalar_tac)
    have hidxval : idx.val = base.val + g_hi.val * q_stride.val + g_lo.val * h_stride.val
        + (m.val : ℤ) * m_stride.val := by
      rw [hidxv, hi5, hi4eq, hi3, hi1, hi, hi2]
    let* ⟨ i6, hi6 ⟩ ← IScalar.hcast_inBounds_spec .Usize idx
      (by constructor <;> scalar_tac)
    have hi6v : i6.val = idx.val.toNat := by scalar_tac
    have hi6lt : i6.val < 256 := by omega
    let* ⟨ value, hvalue ⟩ ← Array.index_usize_spec zetas i6 (by scalar_tac)
    have hvaluev : value.val = (zetas.val[idx.val.toNat]!).val := by
      rw [hvalue, ← hi6v, getElem!_pos zetas.val i6.val (by simpa using hi6lt)]
    -- the optional negation, which is fallible only at `−2¹⁵`
    obtain ⟨value1, hvalue1, hvalue1v⟩ :
        ∃ v1 : I16, (if neg = true then (-. value : Result I16) else ok value) = ok v1 ∧
          v1.val = tblZ zetas neg idx.val := by
      cases neg
      · exact ⟨value, by simp, by simp only [tblZ, Bool.false_eq_true, if_false]; exact hvaluev⟩
      · obtain ⟨v1, hv1, hv1v⟩ := WP.spec_imp_exists (Std.IScalar.neg_step value (by
          intro hcon
          refine hzne idx.val.toNat (by omega) ?_
          rw [← hvaluev, hcon]
          simp [Std.I16.min_eq]))
        exact ⟨v1, hv1, by simp only [tblZ, if_true]; rw [hv1v, hvaluev]⟩
    rw [hvalue1, bind_tc_ok]
    let* ⟨ i7, hi7 ⟩ ← Std.Usize.mul_spec
    let* ⟨ i8, hi8 ⟩ ← Std.Usize.add_spec
    have hi8v : i8.val = 8 * g.val + m.val := by scalar_tac
    let* ⟨ a, ha ⟩ ← Array.update_spec
    have hi9 : (core.num.I16.wrapping_mul value1 qinv).val
        = tblZq (tblZ zetas neg idx.val) qinv.val := by
      show ((value1.bv * qinv.bv : BitVec 16)).toInt = _
      rw [BitVec.toInt_mul, ← hvalue1v]
      rfl
    simp only [lift, bind_tc_ok]
    let* ⟨ i10, hi10 ⟩ ← Std.Usize.add_spec
    have hi10v : i10.val = 8 * g.val + m.val := by scalar_tac
    let* ⟨ a1, ha1 ⟩ ← Array.update_spec
    let* ⟨ m1, hm1 ⟩ ← Std.Usize.add_spec
    apply WP.spec_mono (lane_tbl_inner_spec zetas qinv base q_stride h_stride m_stride neg
      a a1 g g_hi g_lo m1 hgN hb hgh hgl hqs hhs hms hzne hidx)
    rintro ⟨r1, r2⟩ hr j hj
    obtain ⟨hr1, hr2⟩ := hr j hj
    have hset1 : (a.val[j]!).val
        = if j = 8 * g.val + m.val then tblZ zetas neg idx.val else (z.val[j]!).val := by
      rw [ha, Array.set_val_eq, getElem!_set z.val i8.val value1 j (by omega), hi8v]
      split
      · exact hvalue1v
      · rfl
    have hset2 : (a1.val[j]!).val
        = if j = 8 * g.val + m.val then tblZq (tblZ zetas neg idx.val) qinv.val
          else (zq.val[j]!).val := by
      rw [ha1, Array.set_val_eq, getElem!_set zq.val i10.val _ j (by omega), hi10v]
      split
      · exact hi9
      · rfl
    have hidxeq : idx.val = tblIdx (base.val + g_hi.val * q_stride.val
        + g_lo.val * h_stride.val) m_stride.val m.val := by
      unfold tblIdx; rw [hidxval]
    constructor
    · rw [hr1, hset1]
      by_cases hin : 8 * g.val + m1.val ≤ j ∧ j < 8 * g.val + 8
      · rw [if_pos hin, if_pos (show 8 * g.val + m.val ≤ j ∧ j < 8 * g.val + 8 by scalar_tac)]
      · rw [if_neg hin]
        by_cases heq : j = 8 * g.val + m.val
        · rw [if_pos heq, if_pos (show 8 * g.val + m.val ≤ j ∧ j < 8 * g.val + 8 by scalar_tac),
            hidxeq, heq, show 8 * g.val + m.val - 8 * g.val = m.val from by omega]
        · rw [if_neg heq,
            if_neg (show ¬(8 * g.val + m.val ≤ j ∧ j < 8 * g.val + 8) by scalar_tac)]
    · rw [hr2, hset2]
      by_cases hin : 8 * g.val + m1.val ≤ j ∧ j < 8 * g.val + 8
      · rw [if_pos hin, if_pos (show 8 * g.val + m.val ≤ j ∧ j < 8 * g.val + 8 by scalar_tac)]
      · rw [if_neg hin]
        by_cases heq : j = 8 * g.val + m.val
        · rw [if_pos heq, if_pos (show 8 * g.val + m.val ≤ j ∧ j < 8 * g.val + 8 by scalar_tac),
            hidxeq, heq, show 8 * g.val + m.val - 8 * g.val = m.val from by omega]
        · rw [if_neg heq,
            if_neg (show ¬(8 * g.val + m.val ≤ j ∧ j < 8 * g.val + 8) by scalar_tac)]
  · rw [if_neg hlt]
    simp only [WP.spec_ok]
    intro j hj
    exact ⟨by rw [if_neg (by scalar_tac)], by rw [if_neg (by scalar_tac)]⟩
termination_by 8 - m.val
decreasing_by scalar_decr_tac

/-! ## The outer loop: every group

`g` runs while `8g < N`, filling `[8g, 8g+8)` at each step.  The spec records that the entries
*below* `8g` are untouched, which is what makes the recursion compose into "every entry". -/

theorem lane_tbl_outer_spec {N : Usize} (zetas : Array I16 256#usize) (qinv : I16)
    (base q_stride h_stride m_stride : Isize) (h_count : Usize) (neg : Bool)
    (z zq : Array I16 N) (g : Usize) (hgsmall : g.val ≤ 16)
    (hN8 : N.val % 8 = 0) (hN : N.val ≤ 128)
    (hcount : 0 < h_count.val) (hcount16 : h_count.val ≤ 16)
    (hb : 0 ≤ base.val ∧ base.val ≤ 255)
    (hqs : |q_stride.val| ≤ 32) (hhs : |h_stride.val| ≤ 32) (hms : |m_stride.val| ≤ 32)
    (hzne : ∀ k < 256, (zetas.val[k]!).val ≠ -32768)
    (hidx : ∀ gg, 8 * gg < N.val → ∀ k < 8,
      0 ≤ tblIdx (tblC base.val q_stride.val h_stride.val h_count.val gg) m_stride.val k ∧
      tblIdx (tblC base.val q_stride.val h_stride.val h_count.val gg) m_stride.val k < 256) :
    backend.neon.ntt.lane_tbl_loop0 zetas qinv base q_stride h_stride m_stride h_count neg
        z zq g
      ⦃ (r : Array I16 N × Array I16 N) => ∀ j < N.val,
          (if j < 8 * g.val then
              (r.1.val[j]!).val = (z.val[j]!).val ∧ (r.2.val[j]!).val = (zq.val[j]!).val
            else
              (r.1.val[j]!).val = tblZ zetas neg
                  (tblIdx (tblC base.val q_stride.val h_stride.val h_count.val (j / 8))
                    m_stride.val (j % 8)) ∧
              (r.2.val[j]!).val = tblZq (tblZ zetas neg
                  (tblIdx (tblC base.val q_stride.val h_stride.val h_count.val (j / 8))
                    m_stride.val (j % 8))) qinv.val) ⦄ := by
  unfold backend.neon.ntt.lane_tbl_loop0
  let* ⟨ i, hi ⟩ ← Std.Usize.mul_spec (x := g) (y := 8#usize) (by scalar_tac)
  by_cases hlt : i < N
  · rw [if_pos hlt]
    have hgN : 8 * g.val + 8 ≤ N.val := by scalar_tac
    have hg16 : g.val < 16 := by omega
    let* ⟨ i1, hi1 ⟩ ← Std.Usize.div_spec
    have hi1le : i1.val ≤ 16 := by
      rw [hi1]; exact le_trans (Nat.div_le_self _ _) hgsmall
    let* ⟨ g_hi, hghv ⟩ ← UScalar.hcast_inBounds_spec .Isize i1 (by scalar_tac)
    let* ⟨ i2, hi2 ⟩ ← Std.Usize.rem_spec
    have hi2le : i2.val ≤ 16 := by
      rw [hi2]; exact le_trans (Nat.mod_le _ _) hgsmall
    let* ⟨ g_lo, hglv ⟩ ← UScalar.hcast_inBounds_spec .Isize i2 (by scalar_tac)
    have hghb : |g_hi.val| ≤ 16 := by
      rw [abs_le]
      constructor <;> scalar_tac
    have hglb : |g_lo.val| ≤ 16 := by
      rw [abs_le]
      constructor <;> scalar_tac
    -- the split of `g` this iteration uses is exactly `tblC`'s
    have hC : base.val + g_hi.val * q_stride.val + g_lo.val * h_stride.val
        = tblC base.val q_stride.val h_stride.val h_count.val g.val := by
      unfold tblC
      rw [hghv, hi1, hglv, hi2]
    have hidxg : ∀ k < 8,
        0 ≤ tblIdx (base.val + g_hi.val * q_stride.val + g_lo.val * h_stride.val)
              m_stride.val k ∧
        tblIdx (base.val + g_hi.val * q_stride.val + g_lo.val * h_stride.val) m_stride.val k
          < 256 := by
      rw [hC]
      exact hidx g.val (by omega)
    apply WP.spec_bind (lane_tbl_inner_spec zetas qinv base q_stride h_stride m_stride neg
      z zq g g_hi g_lo 0#usize hgN hb hghb hglb hqs hhs hms hzne hidxg)
    rintro ⟨z1, zq1⟩ hinner
    let* ⟨ g1, hg1 ⟩ ← Std.Usize.add_spec
    apply WP.spec_mono (lane_tbl_outer_spec zetas qinv base q_stride h_stride m_stride h_count
      neg z1 zq1 g1 (by scalar_tac) hN8 hN hcount hcount16 hb hqs hhs hms hzne hidx)
    rintro ⟨r1, r2⟩ hr j hj
    have hrj := hr j hj
    obtain ⟨hz1, hzq1⟩ := hinner j hj
    rw [hC] at hz1 hzq1
    by_cases hlow : j < 8 * g.val
    · rw [if_pos hlow]
      rw [if_pos (by scalar_tac)] at hrj
      rw [hrj.1, hrj.2, hz1, hzq1, if_neg (by scalar_tac), if_neg (by scalar_tac)]
      exact ⟨rfl, rfl⟩
    · rw [if_neg hlow]
      by_cases hin : j < 8 * g1.val
      · have hj1 : 8 * g.val ≤ j := by omega
        have hj2 : j < 8 * g.val + 8 := by scalar_tac
        rw [if_pos (by scalar_tac)] at hrj
        rw [hrj.1, hrj.2, hz1, hzq1, if_pos (by scalar_tac), if_pos (by scalar_tac),
          show j / 8 = g.val from
            Nat.div_eq_of_lt_le (by omega) (by omega),
          show j - 8 * g.val = j % 8 from by omega]
        exact ⟨rfl, rfl⟩
      · rw [if_neg (by scalar_tac)] at hrj
        exact hrj
  · rw [if_neg hlt]
    simp only [WP.spec_ok]
    intro j hj
    rw [if_pos (by scalar_tac)]
    exact ⟨trivial, trivial⟩
termination_by N.val - 8 * g.val
decreasing_by scalar_decr_tac

/-! ## The table -/

/-- **`lane_tbl` builds the table it documents.**  Entry `8g + m` of `z` is the `zetas` entry the
six-parameter stride scheme names, negated when asked, and the matching entry of `zq` is its
wrapping product with `q⁻¹`. -/
theorem lane_tbl_spec (N : Usize) (zetas : Array I16 256#usize) (qinv : I16)
    (base q_stride h_stride m_stride : Isize) (h_count : Usize) (neg : Bool)
    (hN8 : N.val % 8 = 0) (hN : N.val ≤ 128)
    (hcount : 0 < h_count.val) (hcount16 : h_count.val ≤ 16)
    (hb : 0 ≤ base.val ∧ base.val ≤ 255)
    (hqs : |q_stride.val| ≤ 32) (hhs : |h_stride.val| ≤ 32) (hms : |m_stride.val| ≤ 32)
    (hzne : ∀ k < 256, (zetas.val[k]!).val ≠ -32768)
    (hidx : ∀ gg, 8 * gg < N.val → ∀ k < 8,
      0 ≤ tblIdx (tblC base.val q_stride.val h_stride.val h_count.val gg) m_stride.val k ∧
      tblIdx (tblC base.val q_stride.val h_stride.val h_count.val gg) m_stride.val k < 256) :
    backend.neon.ntt.lane_tbl N zetas qinv base q_stride h_stride m_stride h_count neg
      ⦃ (t : backend.neon.ntt.Tbl N) => ∀ j < N.val,
          (t.z.val[j]!).val = tblZ zetas neg
              (tblIdx (tblC base.val q_stride.val h_stride.val h_count.val (j / 8))
                m_stride.val (j % 8)) ∧
          (t.zq.val[j]!).val = tblZq (tblZ zetas neg
              (tblIdx (tblC base.val q_stride.val h_stride.val h_count.val (j / 8))
                m_stride.val (j % 8))) qinv.val ⦄ := by
  unfold backend.neon.ntt.lane_tbl
  apply WP.spec_bind (lane_tbl_outer_spec zetas qinv base q_stride h_stride m_stride h_count neg
    (Array.repeat N 0#i16) (Array.repeat N 0#i16) 0#usize (by scalar_tac) hN8 hN hcount hcount16
    hb hqs hhs hms hzne hidx)
  rintro ⟨z1, zq1⟩ hr
  refine (WP.spec_ok _).mpr ?_
  intro j hj
  have := hr j hj
  rw [if_neg (by simp)] at this
  exact this

/-! ## The two ζ tables are centred

The only place the 512 literal entries are touched.  Centredness is what bounds every twiddle,
and it is also what rules out the `sqdmulh` saturation and the fallible negation — a `zetas`
entry is nowhere near `−2¹⁵`. -/

unseal backend.crt.ZETAS_Q1 in
theorem zetas_q1_centred : ∀ x ∈ backend.crt.ZETAS_Q1.val, |x.val| ≤ 3840 := by decide

unseal backend.crt.ZETAS_Q2 in
theorem zetas_q2_centred : ∀ x ∈ backend.crt.ZETAS_Q2.val, |x.val| ≤ 5376 := by decide

theorem zetas_q1_centred_idx (k : ℕ) (hk : k < 256) :
    |(backend.crt.ZETAS_Q1.val[k]!).val| ≤ 3840 := by
  have hlen : backend.crt.ZETAS_Q1.val.length = (256#usize).val := backend.crt.ZETAS_Q1.property
  rw [getElem!_pos _ k (by rw [hlen]; simpa using hk)]
  exact zetas_q1_centred _ (List.getElem_mem _)

theorem zetas_q2_centred_idx (k : ℕ) (hk : k < 256) :
    |(backend.crt.ZETAS_Q2.val[k]!).val| ≤ 5376 := by
  have hlen : backend.crt.ZETAS_Q2.val.length = (256#usize).val := backend.crt.ZETAS_Q2.property
  rw [getElem!_pos _ k (by rw [hlen]; simpa using hk)]
  exact zetas_q2_centred _ (List.getElem_mem _)

theorem zetas_q1_ne_min (k : ℕ) (hk : k < 256) : (backend.crt.ZETAS_Q1.val[k]!).val ≠ -32768 := by
  have := zetas_q1_centred_idx k hk
  rw [abs_le] at this
  omega

theorem zetas_q2_ne_min (k : ℕ) (hk : k < 256) : (backend.crt.ZETAS_Q2.val[k]!).val ≠ -32768 := by
  have := zetas_q2_centred_idx k hk
  rw [abs_le] at this
  omega

/-! ## The Montgomery constants really are inverses mod `2¹⁶`

With these, `tblZq_mont` turns every table's `zq` into the `hzq` hypothesis of
`mont_mul_lane_spec` without any further evaluation. -/

unseal backend.crt.Q1_INV backend.crt.Q1 in
theorem q1_inv_unit : (2 ^ 16 : ℤ) ∣ (backend.crt.Q1_INV.val * backend.crt.Q1.val - 1) := by
  decide

unseal backend.crt.Q2_INV backend.crt.Q2 in
theorem q2_inv_unit : (2 ^ 16 : ℤ) ∣ (backend.crt.Q2_INV.val * backend.crt.Q2.val - 1) := by
  decide

unseal backend.crt.Q1 in
theorem q1_val : backend.crt.Q1.val = 7681 := by decide

unseal backend.crt.Q1_BARRETT_M in
theorem q1_m_val : backend.crt.Q1_BARRETT_M.val = 17474 := by decide

unseal backend.crt.Q2_BARRETT_M in
theorem q2_m_val : backend.crt.Q2_BARRETT_M.val = 12482 := by decide

unseal backend.crt.Q2 in
theorem q2_val : backend.crt.Q2.val = 10753 := by decide

/-! ## `zetas_qinv` multiplies through by `q⁻¹`

Every entry of the derived table is the wrapping product of the matching ζ with `q⁻¹`; that is
all the Montgomery pairing needs. -/

theorem zetas_qinv_loop_spec (zetas : Array I16 256#usize) (qinv : I16)
    (table : Array I16 256#usize) (k : Usize) (hk : k.val ≤ 256)
    (hpre : ∀ j < k.val,
      (table.val[j]!).val = ((zetas.val[j]!).val * qinv.val).bmod (2 ^ 16)) :
    backend.crt.zetas_qinv_loop zetas qinv table k
      ⦃ (t : Array I16 256#usize) => ∀ j < 256,
          (t.val[j]!).val = ((zetas.val[j]!).val * qinv.val).bmod (2 ^ 16) ⦄ := by
  unfold backend.crt.zetas_qinv_loop
  by_cases hlt : k.val < 256
  · rw [if_pos (by scalar_tac)]
    obtain ⟨zk, hzk, hzkv⟩ := WP.spec_imp_exists
      (Array.index_usize_spec zetas k (by simp [Array.length]; omega))
    rw [hzk, bind_tc_ok]
    simp only [core.num.I16.wrapping_mul, lift, bind_tc_ok]
    obtain ⟨a, ha, hav⟩ := WP.spec_imp_exists
      (Array.update_spec table k (IScalar.wrapping_mul zk qinv) (by simp [Array.length]; omega))
    rw [ha, bind_tc_ok]
    step*
    all_goals first
      | omega
      | (intro j hj
         rw [hav, Std.Array.set_val_eq, getElem!_set _ _ _ _ (by
           rw [table.property]; simp; omega)]
         by_cases hje : j = k.val
         · rw [if_pos hje, IScalar.wrapping_mul_val_eq, hzkv, hje,
             getElem!_pos zetas.val k.val (by rw [zetas.property]; simp; omega)]
           rfl
         · rw [if_neg hje]
           exact hpre j (by omega))
  · rw [if_neg (by scalar_tac)]
    simp only [WP.spec_ok]
    intro j hj
    exact hpre j (by omega)
termination_by 256 - k.val
decreasing_by scalar_decr_tac

theorem zetas_qinv_spec (zetas : Array I16 256#usize) (qinv : I16) :
    ∃ t, backend.crt.zetas_qinv zetas qinv = ok t ∧ ∀ j < 256,
      (t.val[j]!).val = ((zetas.val[j]!).val * qinv.val).bmod (2 ^ 16) := by
  apply WP.spec_imp_exists
  unfold backend.crt.zetas_qinv
  exact zetas_qinv_loop_spec zetas qinv _ 0#usize (by simp) (by intro j hj; simp at hj)

/-- **The ζ hypothesis of `ntt_block_bnd`, discharged.** -/
theorem zeta_table_ok_q1 : ∀ kk : Usize, kk.val < 256 → ∃ zi zqi : I16,
    backend.crt.zeta false kk = ok zi ∧ backend.crt.zeta_q false kk = ok zqi ∧
    |zi.val| ≤ 3840 ∧ (2 ^ 16 : ℤ) ∣ (zqi.val * 7681 - zi.val) ∧
    zi.val = (backend.crt.ZETAS_Q1.val[kk.val]!).val := by
  intro kk hkk
  obtain ⟨t, ht, htv⟩ := zetas_qinv_spec backend.crt.ZETAS_Q1 backend.crt.Q1_INV
  obtain ⟨zi, hzi, hziv⟩ := WP.spec_imp_exists
    (Array.index_usize_spec backend.crt.ZETAS_Q1 kk (by simp [Array.length]; omega))
  obtain ⟨zqi, hzqi, hzqiv⟩ := WP.spec_imp_exists
    (Array.index_usize_spec t kk (by simp [Array.length]; omega))
  refine ⟨zi, zqi, ?_, ?_, ?_, ?_, ?_⟩
  · unfold backend.crt.zeta
    simp only [Bool.false_eq_true, reduceIte]
    exact hzi
  · unfold backend.crt.zeta_q
    simp only [Bool.false_eq_true, reduceIte, backend.crt.ZETAS_Q1_QINV, ht, bind_tc_ok]
    exact hzqi
  · rw [hziv]
    exact zetas_q1_centred _ (List.getElem_mem _)
  · -- `zq ≡ z·q⁻¹`, and `q⁻¹·q ≡ 1`, so `zq·q ≡ z`
    have hzv : zqi.val = (zi.val * backend.crt.Q1_INV.val).bmod (2 ^ 16) := by
      rw [hzqiv, ← getElem!_pos t.val kk.val (by rw [t.property]; simp; omega),
        htv kk.val hkk, hziv,
        ← getElem!_pos _ kk.val (by rw [backend.crt.ZETAS_Q1.property]; simp; omega)]
    obtain ⟨c, hc⟩ : (2 ^ 16 : ℤ) ∣ (zqi.val - zi.val * backend.crt.Q1_INV.val) := by
      rw [hzv]
      exact Int.ModEq.dvd (Int.bmod_emod (x := zi.val * backend.crt.Q1_INV.val) (m := 2 ^ 16)).symm
    obtain ⟨d, hd⟩ := q1_inv_unit
    rw [q1_val] at hd
    refine ⟨zi.val * d + c * 7681, ?_⟩
    have e1 : zqi.val = zi.val * backend.crt.Q1_INV.val + 2 ^ 16 * c := by omega
    have e2 : backend.crt.Q1_INV.val * 7681 = 1 + 2 ^ 16 * d := by omega
    calc zqi.val * 7681 - zi.val
        = (zi.val * backend.crt.Q1_INV.val + 2 ^ 16 * c) * 7681 - zi.val := by rw [e1]
      _ = zi.val * (backend.crt.Q1_INV.val * 7681) + 2 ^ 16 * (c * 7681) - zi.val := by ring
      _ = zi.val * (1 + 2 ^ 16 * d) + 2 ^ 16 * (c * 7681) - zi.val := by rw [e2]
      _ = 2 ^ 16 * (zi.val * d + c * 7681) := by ring
  · rw [hziv, getElem!_pos _ kk.val (by rw [backend.crt.ZETAS_Q1.property]; simpa using hkk)]

/-- **The ζ hypothesis of `ntt_block_bnd_q2`, discharged.** -/
theorem zeta_table_ok_q2 : ∀ kk : Usize, kk.val < 256 → ∃ zi zqi : I16,
    backend.crt.zeta true kk = ok zi ∧ backend.crt.zeta_q true kk = ok zqi ∧
    |zi.val| ≤ 5376 ∧ (2 ^ 16 : ℤ) ∣ (zqi.val * 10753 - zi.val) ∧
    zi.val = (backend.crt.ZETAS_Q2.val[kk.val]!).val := by
  intro kk hkk
  obtain ⟨t, ht, htv⟩ := zetas_qinv_spec backend.crt.ZETAS_Q2 backend.crt.Q2_INV
  obtain ⟨zi, hzi, hziv⟩ := WP.spec_imp_exists
    (Array.index_usize_spec backend.crt.ZETAS_Q2 kk (by simp [Array.length]; omega))
  obtain ⟨zqi, hzqi, hzqiv⟩ := WP.spec_imp_exists
    (Array.index_usize_spec t kk (by simp [Array.length]; omega))
  refine ⟨zi, zqi, ?_, ?_, ?_, ?_, ?_⟩
  · unfold backend.crt.zeta
    simp only [if_true]
    exact hzi
  · unfold backend.crt.zeta_q
    simp only [if_true, backend.crt.ZETAS_Q2_QINV, ht, bind_tc_ok]
    exact hzqi
  · rw [hziv]
    exact zetas_q2_centred _ (List.getElem_mem _)
  · -- `zq ≡ z·q⁻¹`, and `q⁻¹·q ≡ 1`, so `zq·q ≡ z`
    have hzv : zqi.val = (zi.val * backend.crt.Q2_INV.val).bmod (2 ^ 16) := by
      rw [hzqiv, ← getElem!_pos t.val kk.val (by rw [t.property]; simp; omega),
        htv kk.val hkk, hziv,
        ← getElem!_pos _ kk.val (by rw [backend.crt.ZETAS_Q2.property]; simp; omega)]
    obtain ⟨c, hc⟩ : (2 ^ 16 : ℤ) ∣ (zqi.val - zi.val * backend.crt.Q2_INV.val) := by
      rw [hzv]
      exact Int.ModEq.dvd (Int.bmod_emod (x := zi.val * backend.crt.Q2_INV.val) (m := 2 ^ 16)).symm
    obtain ⟨d, hd⟩ := q2_inv_unit
    rw [q2_val] at hd
    refine ⟨zi.val * d + c * 10753, ?_⟩
    have e1 : zqi.val = zi.val * backend.crt.Q2_INV.val + 2 ^ 16 * c := by omega
    have e2 : backend.crt.Q2_INV.val * 10753 = 1 + 2 ^ 16 * d := by omega
    calc zqi.val * 10753 - zi.val
        = (zi.val * backend.crt.Q2_INV.val + 2 ^ 16 * c) * 10753 - zi.val := by rw [e1]
      _ = zi.val * (backend.crt.Q2_INV.val * 10753) + 2 ^ 16 * (c * 10753) - zi.val := by ring
      _ = zi.val * (1 + 2 ^ 16 * d) + 2 ^ 16 * (c * 10753) - zi.val := by rw [e2]
      _ = 2 ^ 16 * (zi.val * d + c * 10753) := by ring
  · rw [hziv, getElem!_pos _ kk.val (by rw [backend.crt.ZETAS_Q2.property]; simpa using hkk)]

/-! ## The twelve concrete tables

Each is `lane_tbl_spec` with the parameters plugged in and its index expression put in closed
form.  `tbl_at` packages the plumbing so that each of the twelve is one application: the bounds
on the parameters are `decide`s over literals, and the index bound is `omega` over a division by
1, 2 or 4. -/

private theorem tbl_at (N : Usize) (zetas : Array I16 256#usize) (qinv : I16)
    (base q_stride h_stride m_stride : Isize) (h_count : Usize) (neg : Bool) (f : ℕ → ℤ)
    (hN8 : N.val % 8 = 0) (hN : N.val ≤ 128)
    (hcount : 0 < h_count.val) (hcount16 : h_count.val ≤ 16)
    (hb : 0 ≤ base.val ∧ base.val ≤ 255)
    (hqs : |q_stride.val| ≤ 32) (hhs : |h_stride.val| ≤ 32) (hms : |m_stride.val| ≤ 32)
    (hzne : ∀ k < 256, (zetas.val[k]!).val ≠ -32768)
    (hf : ∀ j < N.val,
      tblIdx (tblC base.val q_stride.val h_stride.val h_count.val (j / 8)) m_stride.val (j % 8)
        = f j)
    (hrange : ∀ j < N.val, 0 ≤ f j ∧ f j < 256) :
    backend.neon.ntt.lane_tbl N zetas qinv base q_stride h_stride m_stride h_count neg
      ⦃ (t : backend.neon.ntt.Tbl N) => ∀ j < N.val,
          (t.z.val[j]!).val = tblZ zetas neg (f j) ∧
          (t.zq.val[j]!).val = tblZq (tblZ zetas neg (f j)) qinv.val ⦄ := by
  apply WP.spec_mono (lane_tbl_spec N zetas qinv base q_stride h_stride m_stride h_count neg
    hN8 hN hcount hcount16 hb hqs hhs hms hzne (by
      intro gg hgg k hk
      have h8 : 8 * gg + k < N.val := by omega
      have := hf (8 * gg + k) h8
      rw [show (8 * gg + k) / 8 = gg from by omega, show (8 * gg + k) % 8 = k from by omega]
        at this
      rw [this]
      exact hrange _ h8))
  intro t ht j hj
  obtain ⟨h1, h2⟩ := ht j hj
  rw [h1, h2, hf j hj]
  exact ⟨rfl, rfl⟩

/-! ### The six index functions

One per level and direction, in closed form.  The forward `len = 4` table is the cleanest and
shows the shape: entry `j` is ψ index `32 + j`, which is exactly the Rust comment's
"level len=4: ψ index 32 + (8g + m)". -/

/-- Forward, `len = 4`: entry `j` is ψ index `32 + j`. -/
def fwd4Idx (j : ℕ) : ℤ := 32 + (j : ℤ)
/-- Forward, `len = 2`. -/
def fwd2Idx (j : ℕ) : ℤ :=
  64 + 16 * ((j / 16 : ℕ) : ℤ) + ((j / 8 % 2 : ℕ) : ℤ) + 2 * ((j % 8 : ℕ) : ℤ)
/-- Forward, `len = 1`. -/
def fwd1Idx (j : ℕ) : ℤ :=
  128 + 32 * ((j / 32 : ℕ) : ℤ) + ((j / 8 % 4 : ℕ) : ℤ) + 4 * ((j % 8 : ℕ) : ℤ)
/-- Inverse, `len = 1`: the Gentleman-Sande pass walks the table downwards. -/
def inv1Idx (j : ℕ) : ℤ :=
  255 - 32 * ((j / 32 : ℕ) : ℤ) - ((j / 8 % 4 : ℕ) : ℤ) - 4 * ((j % 8 : ℕ) : ℤ)
/-- Inverse, `len = 2`. -/
def inv2Idx (j : ℕ) : ℤ :=
  127 - 16 * ((j / 16 : ℕ) : ℤ) - ((j / 8 % 2 : ℕ) : ℤ) - 2 * ((j % 8 : ℕ) : ℤ)
/-- Inverse, `len = 4`: entry `j` is ψ index `63 − j`. -/
def inv4Idx (j : ℕ) : ℤ := 63 - (j : ℤ)


theorem FWD4_Q1_spec :
    backend.neon.ntt.FWD4_Q1
      ⦃ (t : backend.neon.ntt.Tbl 32#usize) => ∀ j < 32,
          (t.z.val[j]!).val = tblZ backend.crt.ZETAS_Q1 false (fwd4Idx j) ∧
          (t.zq.val[j]!).val =
            tblZq (tblZ backend.crt.ZETAS_Q1 false (fwd4Idx j)) backend.crt.Q1_INV.val ⦄ := by
  unfold backend.neon.ntt.FWD4_Q1
  exact tbl_at 32#usize _ _ 32#isize 8#isize 0#isize 1#isize 1#usize false fwd4Idx
    (by scalar_tac) (by scalar_tac) (by scalar_tac) (by scalar_tac)
    (by constructor <;> scalar_tac)
    (by rw [abs_le]; constructor <;> scalar_tac) (by rw [abs_le]; constructor <;> scalar_tac)
    (by rw [abs_le]; constructor <;> scalar_tac) zetas_q1_ne_min
    (by intro j hj; unfold tblIdx tblC fwd4Idx; scalar_tac)
    (by intro j hj; unfold fwd4Idx; scalar_tac)

theorem FWD2_Q1_spec :
    backend.neon.ntt.FWD2_Q1
      ⦃ (t : backend.neon.ntt.Tbl 64#usize) => ∀ j < 64,
          (t.z.val[j]!).val = tblZ backend.crt.ZETAS_Q1 false (fwd2Idx j) ∧
          (t.zq.val[j]!).val =
            tblZq (tblZ backend.crt.ZETAS_Q1 false (fwd2Idx j)) backend.crt.Q1_INV.val ⦄ := by
  unfold backend.neon.ntt.FWD2_Q1
  exact tbl_at 64#usize _ _ 64#isize 16#isize 1#isize 2#isize 2#usize false fwd2Idx
    (by scalar_tac) (by scalar_tac) (by scalar_tac) (by scalar_tac)
    (by constructor <;> scalar_tac)
    (by rw [abs_le]; constructor <;> scalar_tac) (by rw [abs_le]; constructor <;> scalar_tac)
    (by rw [abs_le]; constructor <;> scalar_tac) zetas_q1_ne_min
    (by intro j hj; unfold tblIdx tblC fwd2Idx; scalar_tac)
    (by intro j hj; unfold fwd2Idx; scalar_tac)

theorem FWD1_Q1_spec :
    backend.neon.ntt.FWD1_Q1
      ⦃ (t : backend.neon.ntt.Tbl 128#usize) => ∀ j < 128,
          (t.z.val[j]!).val = tblZ backend.crt.ZETAS_Q1 false (fwd1Idx j) ∧
          (t.zq.val[j]!).val =
            tblZq (tblZ backend.crt.ZETAS_Q1 false (fwd1Idx j)) backend.crt.Q1_INV.val ⦄ := by
  unfold backend.neon.ntt.FWD1_Q1
  exact tbl_at 128#usize _ _ 128#isize 32#isize 1#isize 4#isize 4#usize false fwd1Idx
    (by scalar_tac) (by scalar_tac) (by scalar_tac) (by scalar_tac)
    (by constructor <;> scalar_tac)
    (by rw [abs_le]; constructor <;> scalar_tac) (by rw [abs_le]; constructor <;> scalar_tac)
    (by rw [abs_le]; constructor <;> scalar_tac) zetas_q1_ne_min
    (by intro j hj; unfold tblIdx tblC fwd1Idx; scalar_tac)
    (by intro j hj; unfold fwd1Idx; scalar_tac)

theorem INV1_Q1_spec :
    backend.neon.ntt.INV1_Q1
      ⦃ (t : backend.neon.ntt.Tbl 128#usize) => ∀ j < 128,
          (t.z.val[j]!).val = tblZ backend.crt.ZETAS_Q1 true (inv1Idx j) ∧
          (t.zq.val[j]!).val =
            tblZq (tblZ backend.crt.ZETAS_Q1 true (inv1Idx j)) backend.crt.Q1_INV.val ⦄ := by
  unfold backend.neon.ntt.INV1_Q1
  exact tbl_at 128#usize _ _ 255#isize (-32)#isize (-1)#isize (-4)#isize 4#usize true inv1Idx
    (by scalar_tac) (by scalar_tac) (by scalar_tac) (by scalar_tac)
    (by constructor <;> scalar_tac)
    (by rw [abs_le]; constructor <;> scalar_tac) (by rw [abs_le]; constructor <;> scalar_tac)
    (by rw [abs_le]; constructor <;> scalar_tac) zetas_q1_ne_min
    (by intro j hj; unfold tblIdx tblC inv1Idx; scalar_tac)
    (by intro j hj; unfold inv1Idx; scalar_tac)

theorem INV2_Q1_spec :
    backend.neon.ntt.INV2_Q1
      ⦃ (t : backend.neon.ntt.Tbl 64#usize) => ∀ j < 64,
          (t.z.val[j]!).val = tblZ backend.crt.ZETAS_Q1 true (inv2Idx j) ∧
          (t.zq.val[j]!).val =
            tblZq (tblZ backend.crt.ZETAS_Q1 true (inv2Idx j)) backend.crt.Q1_INV.val ⦄ := by
  unfold backend.neon.ntt.INV2_Q1
  exact tbl_at 64#usize _ _ 127#isize (-16)#isize (-1)#isize (-2)#isize 2#usize true inv2Idx
    (by scalar_tac) (by scalar_tac) (by scalar_tac) (by scalar_tac)
    (by constructor <;> scalar_tac)
    (by rw [abs_le]; constructor <;> scalar_tac) (by rw [abs_le]; constructor <;> scalar_tac)
    (by rw [abs_le]; constructor <;> scalar_tac) zetas_q1_ne_min
    (by intro j hj; unfold tblIdx tblC inv2Idx; scalar_tac)
    (by intro j hj; unfold inv2Idx; scalar_tac)

theorem INV4_Q1_spec :
    backend.neon.ntt.INV4_Q1
      ⦃ (t : backend.neon.ntt.Tbl 32#usize) => ∀ j < 32,
          (t.z.val[j]!).val = tblZ backend.crt.ZETAS_Q1 true (inv4Idx j) ∧
          (t.zq.val[j]!).val =
            tblZq (tblZ backend.crt.ZETAS_Q1 true (inv4Idx j)) backend.crt.Q1_INV.val ⦄ := by
  unfold backend.neon.ntt.INV4_Q1
  exact tbl_at 32#usize _ _ 63#isize (-8)#isize 0#isize (-1)#isize 1#usize true inv4Idx
    (by scalar_tac) (by scalar_tac) (by scalar_tac) (by scalar_tac)
    (by constructor <;> scalar_tac)
    (by rw [abs_le]; constructor <;> scalar_tac) (by rw [abs_le]; constructor <;> scalar_tac)
    (by rw [abs_le]; constructor <;> scalar_tac) zetas_q1_ne_min
    (by intro j hj; unfold tblIdx tblC inv4Idx; scalar_tac)
    (by intro j hj; unfold inv4Idx; scalar_tac)

theorem FWD4_Q2_spec :
    backend.neon.ntt.FWD4_Q2
      ⦃ (t : backend.neon.ntt.Tbl 32#usize) => ∀ j < 32,
          (t.z.val[j]!).val = tblZ backend.crt.ZETAS_Q2 false (fwd4Idx j) ∧
          (t.zq.val[j]!).val =
            tblZq (tblZ backend.crt.ZETAS_Q2 false (fwd4Idx j)) backend.crt.Q2_INV.val ⦄ := by
  unfold backend.neon.ntt.FWD4_Q2
  exact tbl_at 32#usize _ _ 32#isize 8#isize 0#isize 1#isize 1#usize false fwd4Idx
    (by scalar_tac) (by scalar_tac) (by scalar_tac) (by scalar_tac)
    (by constructor <;> scalar_tac)
    (by rw [abs_le]; constructor <;> scalar_tac) (by rw [abs_le]; constructor <;> scalar_tac)
    (by rw [abs_le]; constructor <;> scalar_tac) zetas_q2_ne_min
    (by intro j hj; unfold tblIdx tblC fwd4Idx; scalar_tac)
    (by intro j hj; unfold fwd4Idx; scalar_tac)

theorem FWD2_Q2_spec :
    backend.neon.ntt.FWD2_Q2
      ⦃ (t : backend.neon.ntt.Tbl 64#usize) => ∀ j < 64,
          (t.z.val[j]!).val = tblZ backend.crt.ZETAS_Q2 false (fwd2Idx j) ∧
          (t.zq.val[j]!).val =
            tblZq (tblZ backend.crt.ZETAS_Q2 false (fwd2Idx j)) backend.crt.Q2_INV.val ⦄ := by
  unfold backend.neon.ntt.FWD2_Q2
  exact tbl_at 64#usize _ _ 64#isize 16#isize 1#isize 2#isize 2#usize false fwd2Idx
    (by scalar_tac) (by scalar_tac) (by scalar_tac) (by scalar_tac)
    (by constructor <;> scalar_tac)
    (by rw [abs_le]; constructor <;> scalar_tac) (by rw [abs_le]; constructor <;> scalar_tac)
    (by rw [abs_le]; constructor <;> scalar_tac) zetas_q2_ne_min
    (by intro j hj; unfold tblIdx tblC fwd2Idx; scalar_tac)
    (by intro j hj; unfold fwd2Idx; scalar_tac)

theorem FWD1_Q2_spec :
    backend.neon.ntt.FWD1_Q2
      ⦃ (t : backend.neon.ntt.Tbl 128#usize) => ∀ j < 128,
          (t.z.val[j]!).val = tblZ backend.crt.ZETAS_Q2 false (fwd1Idx j) ∧
          (t.zq.val[j]!).val =
            tblZq (tblZ backend.crt.ZETAS_Q2 false (fwd1Idx j)) backend.crt.Q2_INV.val ⦄ := by
  unfold backend.neon.ntt.FWD1_Q2
  exact tbl_at 128#usize _ _ 128#isize 32#isize 1#isize 4#isize 4#usize false fwd1Idx
    (by scalar_tac) (by scalar_tac) (by scalar_tac) (by scalar_tac)
    (by constructor <;> scalar_tac)
    (by rw [abs_le]; constructor <;> scalar_tac) (by rw [abs_le]; constructor <;> scalar_tac)
    (by rw [abs_le]; constructor <;> scalar_tac) zetas_q2_ne_min
    (by intro j hj; unfold tblIdx tblC fwd1Idx; scalar_tac)
    (by intro j hj; unfold fwd1Idx; scalar_tac)

theorem INV1_Q2_spec :
    backend.neon.ntt.INV1_Q2
      ⦃ (t : backend.neon.ntt.Tbl 128#usize) => ∀ j < 128,
          (t.z.val[j]!).val = tblZ backend.crt.ZETAS_Q2 true (inv1Idx j) ∧
          (t.zq.val[j]!).val =
            tblZq (tblZ backend.crt.ZETAS_Q2 true (inv1Idx j)) backend.crt.Q2_INV.val ⦄ := by
  unfold backend.neon.ntt.INV1_Q2
  exact tbl_at 128#usize _ _ 255#isize (-32)#isize (-1)#isize (-4)#isize 4#usize true inv1Idx
    (by scalar_tac) (by scalar_tac) (by scalar_tac) (by scalar_tac)
    (by constructor <;> scalar_tac)
    (by rw [abs_le]; constructor <;> scalar_tac) (by rw [abs_le]; constructor <;> scalar_tac)
    (by rw [abs_le]; constructor <;> scalar_tac) zetas_q2_ne_min
    (by intro j hj; unfold tblIdx tblC inv1Idx; scalar_tac)
    (by intro j hj; unfold inv1Idx; scalar_tac)

theorem INV2_Q2_spec :
    backend.neon.ntt.INV2_Q2
      ⦃ (t : backend.neon.ntt.Tbl 64#usize) => ∀ j < 64,
          (t.z.val[j]!).val = tblZ backend.crt.ZETAS_Q2 true (inv2Idx j) ∧
          (t.zq.val[j]!).val =
            tblZq (tblZ backend.crt.ZETAS_Q2 true (inv2Idx j)) backend.crt.Q2_INV.val ⦄ := by
  unfold backend.neon.ntt.INV2_Q2
  exact tbl_at 64#usize _ _ 127#isize (-16)#isize (-1)#isize (-2)#isize 2#usize true inv2Idx
    (by scalar_tac) (by scalar_tac) (by scalar_tac) (by scalar_tac)
    (by constructor <;> scalar_tac)
    (by rw [abs_le]; constructor <;> scalar_tac) (by rw [abs_le]; constructor <;> scalar_tac)
    (by rw [abs_le]; constructor <;> scalar_tac) zetas_q2_ne_min
    (by intro j hj; unfold tblIdx tblC inv2Idx; scalar_tac)
    (by intro j hj; unfold inv2Idx; scalar_tac)

theorem INV4_Q2_spec :
    backend.neon.ntt.INV4_Q2
      ⦃ (t : backend.neon.ntt.Tbl 32#usize) => ∀ j < 32,
          (t.z.val[j]!).val = tblZ backend.crt.ZETAS_Q2 true (inv4Idx j) ∧
          (t.zq.val[j]!).val =
            tblZq (tblZ backend.crt.ZETAS_Q2 true (inv4Idx j)) backend.crt.Q2_INV.val ⦄ := by
  unfold backend.neon.ntt.INV4_Q2
  exact tbl_at 32#usize _ _ 63#isize (-8)#isize 0#isize (-1)#isize 1#usize true inv4Idx
    (by scalar_tac) (by scalar_tac) (by scalar_tac) (by scalar_tac)
    (by constructor <;> scalar_tac)
    (by rw [abs_le]; constructor <;> scalar_tac) (by rw [abs_le]; constructor <;> scalar_tac)
    (by rw [abs_le]; constructor <;> scalar_tac) zetas_q2_ne_min
    (by intro j hj; unfold tblIdx tblC inv4Idx; scalar_tac)
    (by intro j hj; unfold inv4Idx; scalar_tac)

/-! ## Loading a group's twiddles

`ld_tbl` reads entries `[8g, 8g+8)` of a table into a pair of vectors, and the six accessors
`fwd4` … `inv4` pick which table.  They exist because of aeneas trap 4 in
`NEON_VERIFICATION_PLAN.md` §4 — a `let (x, y) = if …` at statement level does not translate —
and they must return the loaded pair *by value*, which is why the specs below are about lanes
rather than about a `&'static Tbl`. -/

/-- Which ζ table a `SECOND` flag selects. -/
def zetasOf (SECOND : Bool) : Array I16 256#usize :=
  if SECOND then backend.crt.ZETAS_Q2 else backend.crt.ZETAS_Q1

/-- …and which Montgomery constant. -/
def qinvOf (SECOND : Bool) : I16 :=
  if SECOND then backend.crt.Q2_INV else backend.crt.Q1_INV

theorem ld_tbl_spec {N : Usize} (zetas : Array I16 256#usize) (qinv : I16) (neg : Bool)
    (f : ℕ → ℤ) (table : backend.neon.ntt.Tbl N) (g : Usize)
    (hg : 8 * (g.val + 1) ≤ N.val)
    (ht : ∀ j < N.val, (table.z.val[j]!).val = tblZ zetas neg (f j) ∧
                       (table.zq.val[j]!).val = tblZq (tblZ zetas neg (f j)) qinv.val) :
    backend.neon.ntt.ld_tbl table g
      ⦃ (r : RustKopisNeon.backend.neon.intrinsics.Vec128 ×
             RustKopisNeon.backend.neon.intrinsics.Vec128) => ∀ m < 8,
          (lane16 r.1 m).toInt = tblZ zetas neg (f (8 * g.val + m)) ∧
          (lane16 r.2 m).toInt = tblZq (tblZ zetas neg (f (8 * g.val + m))) qinv.val ⦄ := by
  unfold backend.neon.ntt.ld_tbl
  obtain ⟨v, hv, hvl⟩ := load_i16_spec table.z g hg
  rw [hv, bind_tc_ok]
  obtain ⟨v1, hv1, hv1l⟩ := load_i16_spec table.zq g hg
  rw [hv1, bind_tc_ok]
  refine (WP.spec_ok _).mpr ?_
  intro m hm
  obtain ⟨h1, h2⟩ := ht (8 * g.val + m) (by omega)
  exact ⟨by rw [hvl m hm]; exact h1, by rw [hv1l m hm]; exact h2⟩


theorem fwd4_spec (SECOND : Bool) (g : Usize) (hg : 8 * (g.val + 1) ≤ 32) :
    backend.neon.ntt.fwd4 SECOND g
      ⦃ (r : RustKopisNeon.backend.neon.intrinsics.Vec128 ×
             RustKopisNeon.backend.neon.intrinsics.Vec128) => ∀ m < 8,
          (lane16 r.1 m).toInt = tblZ (zetasOf SECOND) false (fwd4Idx (8 * g.val + m)) ∧
          (lane16 r.2 m).toInt =
            tblZq (tblZ (zetasOf SECOND) false (fwd4Idx (8 * g.val + m))) (qinvOf SECOND).val ⦄ := by
  unfold backend.neon.ntt.fwd4
  by_cases hS : SECOND = true
  · simp only [hS, reduceIte, zetasOf, qinvOf]
    apply WP.spec_bind FWD4_Q2_spec
    intro t ht
    exact ld_tbl_spec _ _ false fwd4Idx t g hg ht
  · have hS' : SECOND = false := by simpa using hS
    simp only [hS', Bool.false_eq_true, reduceIte, zetasOf, qinvOf]
    apply WP.spec_bind FWD4_Q1_spec
    intro t ht
    exact ld_tbl_spec _ _ false fwd4Idx t g hg ht

theorem fwd2_spec (SECOND : Bool) (g : Usize) (hg : 8 * (g.val + 1) ≤ 64) :
    backend.neon.ntt.fwd2 SECOND g
      ⦃ (r : RustKopisNeon.backend.neon.intrinsics.Vec128 ×
             RustKopisNeon.backend.neon.intrinsics.Vec128) => ∀ m < 8,
          (lane16 r.1 m).toInt = tblZ (zetasOf SECOND) false (fwd2Idx (8 * g.val + m)) ∧
          (lane16 r.2 m).toInt =
            tblZq (tblZ (zetasOf SECOND) false (fwd2Idx (8 * g.val + m))) (qinvOf SECOND).val ⦄ := by
  unfold backend.neon.ntt.fwd2
  by_cases hS : SECOND = true
  · simp only [hS, reduceIte, zetasOf, qinvOf]
    apply WP.spec_bind FWD2_Q2_spec
    intro t ht
    exact ld_tbl_spec _ _ false fwd2Idx t g hg ht
  · have hS' : SECOND = false := by simpa using hS
    simp only [hS', Bool.false_eq_true, reduceIte, zetasOf, qinvOf]
    apply WP.spec_bind FWD2_Q1_spec
    intro t ht
    exact ld_tbl_spec _ _ false fwd2Idx t g hg ht

theorem fwd1_spec (SECOND : Bool) (g : Usize) (hg : 8 * (g.val + 1) ≤ 128) :
    backend.neon.ntt.fwd1 SECOND g
      ⦃ (r : RustKopisNeon.backend.neon.intrinsics.Vec128 ×
             RustKopisNeon.backend.neon.intrinsics.Vec128) => ∀ m < 8,
          (lane16 r.1 m).toInt = tblZ (zetasOf SECOND) false (fwd1Idx (8 * g.val + m)) ∧
          (lane16 r.2 m).toInt =
            tblZq (tblZ (zetasOf SECOND) false (fwd1Idx (8 * g.val + m))) (qinvOf SECOND).val ⦄ := by
  unfold backend.neon.ntt.fwd1
  by_cases hS : SECOND = true
  · simp only [hS, reduceIte, zetasOf, qinvOf]
    apply WP.spec_bind FWD1_Q2_spec
    intro t ht
    exact ld_tbl_spec _ _ false fwd1Idx t g hg ht
  · have hS' : SECOND = false := by simpa using hS
    simp only [hS', Bool.false_eq_true, reduceIte, zetasOf, qinvOf]
    apply WP.spec_bind FWD1_Q1_spec
    intro t ht
    exact ld_tbl_spec _ _ false fwd1Idx t g hg ht

theorem inv1_spec (SECOND : Bool) (g : Usize) (hg : 8 * (g.val + 1) ≤ 128) :
    backend.neon.ntt.inv1 SECOND g
      ⦃ (r : RustKopisNeon.backend.neon.intrinsics.Vec128 ×
             RustKopisNeon.backend.neon.intrinsics.Vec128) => ∀ m < 8,
          (lane16 r.1 m).toInt = tblZ (zetasOf SECOND) true (inv1Idx (8 * g.val + m)) ∧
          (lane16 r.2 m).toInt =
            tblZq (tblZ (zetasOf SECOND) true (inv1Idx (8 * g.val + m))) (qinvOf SECOND).val ⦄ := by
  unfold backend.neon.ntt.inv1
  by_cases hS : SECOND = true
  · simp only [hS, reduceIte, zetasOf, qinvOf]
    apply WP.spec_bind INV1_Q2_spec
    intro t ht
    exact ld_tbl_spec _ _ true inv1Idx t g hg ht
  · have hS' : SECOND = false := by simpa using hS
    simp only [hS', Bool.false_eq_true, reduceIte, zetasOf, qinvOf]
    apply WP.spec_bind INV1_Q1_spec
    intro t ht
    exact ld_tbl_spec _ _ true inv1Idx t g hg ht

theorem inv2_spec (SECOND : Bool) (g : Usize) (hg : 8 * (g.val + 1) ≤ 64) :
    backend.neon.ntt.inv2 SECOND g
      ⦃ (r : RustKopisNeon.backend.neon.intrinsics.Vec128 ×
             RustKopisNeon.backend.neon.intrinsics.Vec128) => ∀ m < 8,
          (lane16 r.1 m).toInt = tblZ (zetasOf SECOND) true (inv2Idx (8 * g.val + m)) ∧
          (lane16 r.2 m).toInt =
            tblZq (tblZ (zetasOf SECOND) true (inv2Idx (8 * g.val + m))) (qinvOf SECOND).val ⦄ := by
  unfold backend.neon.ntt.inv2
  by_cases hS : SECOND = true
  · simp only [hS, reduceIte, zetasOf, qinvOf]
    apply WP.spec_bind INV2_Q2_spec
    intro t ht
    exact ld_tbl_spec _ _ true inv2Idx t g hg ht
  · have hS' : SECOND = false := by simpa using hS
    simp only [hS', Bool.false_eq_true, reduceIte, zetasOf, qinvOf]
    apply WP.spec_bind INV2_Q1_spec
    intro t ht
    exact ld_tbl_spec _ _ true inv2Idx t g hg ht

theorem inv4_spec (SECOND : Bool) (g : Usize) (hg : 8 * (g.val + 1) ≤ 32) :
    backend.neon.ntt.inv4 SECOND g
      ⦃ (r : RustKopisNeon.backend.neon.intrinsics.Vec128 ×
             RustKopisNeon.backend.neon.intrinsics.Vec128) => ∀ m < 8,
          (lane16 r.1 m).toInt = tblZ (zetasOf SECOND) true (inv4Idx (8 * g.val + m)) ∧
          (lane16 r.2 m).toInt =
            tblZq (tblZ (zetasOf SECOND) true (inv4Idx (8 * g.val + m))) (qinvOf SECOND).val ⦄ := by
  unfold backend.neon.ntt.inv4
  by_cases hS : SECOND = true
  · simp only [hS, reduceIte, zetasOf, qinvOf]
    apply WP.spec_bind INV4_Q2_spec
    intro t ht
    exact ld_tbl_spec _ _ true inv4Idx t g hg ht
  · have hS' : SECOND = false := by simpa using hS
    simp only [hS', Bool.false_eq_true, reduceIte, zetasOf, qinvOf]
    apply WP.spec_bind INV4_Q1_spec
    intro t ht
    exact ld_tbl_spec _ _ true inv4Idx t g hg ht

end Kopis.Neon
