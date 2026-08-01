/-
  # Kopis/Properties/NttInverse.lean — the extracted inverse NTT.

  The Gentleman-Sande network of `arithmetic.ntt.invntt`, connected to `NttMath.State_gs` the
  same way `NttForward.lean` connects the Cooley-Tukey network to `State_ct`.

  ## The magnitude schedule

  `p` is too large for Dilithium-style lazy growth to survive all eight levels in an `i32`: the
  un-reduced sum path *doubles* every level while the Montgomery path resets to `< p`.  Starting
  from `|a| ≤ p`, four levels reach `16p < 2³¹`; the code then Barrett-reduces everything back
  under `p` (the `if len1 = 16` branch) and the remaining four levels reach `16p` again.

  The tightest constraint is the Montgomery input `ζ·(t - a[j+len])`: with `|ζ| < p` and
  `|t - a[j+len]| ≤ 2B`, it must stay below `2³¹·p`.  The bound `2B ≤ 2³¹-1` is exactly enough —
  `p·(2³¹-1) = 108083094619162111 < 108083094669492224 = 2³¹·p` — which is why the loop specs
  below carry `2 * B ≤ 2147483647` rather than something rounder.
-/
import Kopis.Properties.NttForward

open Aeneas Aeneas.Std Result RustKopis
open scoped BigOperators

namespace Kopis.Properties

open NttMath

set_option maxHeartbeats 1000000

/-! ## The innermost loop: one Gentleman-Sande block

`invntt_loop0_loop0_loop0 iter a len neg_zeta` runs `j` over `[iter.start, st + len)` performing
`t := a[j]; a[j] := t + a[j+len]; a[j+len] := δ·(t - a[j+len])`, where `δ` is the plain value of
`neg_zeta`.  This is exactly the `hbut` hypothesis of `NttMath.State_gs`. -/

theorem invntt_inner_spec {st lenv : ℕ} (iter : core.ops.range.Range Usize)
    (a : Array I32 256#usize) (len : Usize) (neg_zeta : I64) (δ : Zp) (B : ℤ)
    (hlen : len.val = lenv) (hlpos : 0 < lenv)
    (hend : iter.«end».val = st + lenv)
    (hlo : st ≤ iter.start.val) (hhi : iter.start.val ≤ st + lenv)
    (hblk : st + 2 * lenv ≤ 256)
    (hzeta : ((neg_zeta.val : ℤ) : Zp) * Rinv = δ)
    (hzlo : -pNtt < (neg_zeta.val : ℤ)) (hzhi : (neg_zeta.val : ℤ) < pNtt)
    (hpB : pNtt ≤ B) (hBhi : 2 * B ≤ 2147483647)
    (hBu : ∀ c, iter.start.val ≤ c → c < st + lenv → |aZ a c| ≤ B)
    (hBu2 : ∀ c, iter.start.val + lenv ≤ c → c < st + 2 * lenv → |aZ a c| ≤ B)
    (hBg : ∀ c, c < 256 → |aZ a c| ≤ 2 * B) :
    arithmetic.ntt.invntt_loop0_loop0_loop0 iter a len neg_zeta
      ⦃ (r : Array I32 256#usize) =>
        (∀ j, iter.start.val ≤ j → j < st + lenv →
            aP r j = aP a j + aP a (j + lenv)
            ∧ aP r (j + lenv) = δ * (aP a j - aP a (j + lenv)))
        ∧ (∀ c, c < iter.start.val → aZ r c = aZ a c)
        ∧ (∀ c, st + lenv ≤ c → c < iter.start.val + lenv → aZ r c = aZ a c)
        ∧ (∀ c, st + 2 * lenv ≤ c → aZ r c = aZ a c)
        ∧ (∀ c, c < 256 → |aZ r c| ≤ 2 * B) ⦄ := by
  have hp0 : (0:ℤ) < pNtt := by unfold pNtt; norm_num
  unfold arithmetic.ntt.invntt_loop0_loop0_loop0
  by_cases hlt : iter.start.val < iter.«end».val
  · let* ⟨ o, iter1, ho, hstart', hend' ⟩ ← core.iter.range.IteratorRange.next_Usize_some_spec
    rw [ho]; simp only
    have hj_lt : iter.start.val < st + lenv := by omega
    have hjb : iter.start.val < 256 := by omega
    have hjl : iter.start.val + lenv < 256 := by omega
    step*
    -- the two operands
    have hiv : i.val = iter.start.val + lenv := by rw [i_post, hlen]
    have e_t : (t.val : ℤ) = aZ a iter.start.val := by
      rw [t_post]; exact aZ_getElem a iter.start (by omega)
    have e_i1 : (i1.val : ℤ) = aZ a (iter.start.val + lenv) := by
      rw [i1_post, aZ_getElem a i (by omega), hiv]
    have htB : -B ≤ (t.val : ℤ) ∧ (t.val : ℤ) ≤ B := by
      have h := hBu iter.start.val (le_refl _) hj_lt
      rw [abs_le] at h; rw [e_t]; exact h
    have hi1B : -B ≤ (i1.val : ℤ) ∧ (i1.val : ℤ) ≤ B := by
      have h := hBu2 (iter.start.val + lenv) (le_refl _) (by omega)
      rw [abs_le] at h; rw [e_i1]; exact h
    -- the sum path, written to `a[j]`
    have e_i2 : (i2.val : ℤ) = (t.val : ℤ) + (i1.val : ℤ) := by
      rw [i2_post, I32_wrapping_add_exact t i1 (by linarith [htB.1, hi1B.1])
        (by linarith [htB.2, hi1B.2])]
    -- reading `a1[j+len]` still gives the old value: the write went to `j ≠ j+len`
    have e_i3 : (i3.val : ℤ) = (i1.val : ℤ) := by
      have h1 : (i3.val : ℤ) = aZ a1 i.val := by
        rw [i3_post]; exact aZ_getElem a1 i (by omega)
      rw [h1, a1_post, aZ_set a iter.start i2 (by omega) i.val, if_neg (by omega), hiv, ← e_i1]
    have e_i4 : (i4.val : ℤ) = (t.val : ℤ) - (i1.val : ℤ) := by
      rw [i4_post, I32_wrapping_sub_exact t i3 (by rw [e_i3]; linarith [htB.1, hi1B.2])
        (by rw [e_i3]; linarith [htB.2, hi1B.1]), e_i3]
    have e_i5 : (i5.val : ℤ) = (i4.val : ℤ) := by
      rw [i5_post, IScalar.cast_val_eq,
        show Min.min IScalarTy.I64.numBits IScalarTy.I32.numBits = 32 from rfl]
      exact bmod_i32_exact (by scalar_tac) (by scalar_tac)
    -- the Montgomery product is inside `mont_reduce`'s input range: `|ζ| < p`, `|i4| ≤ 2B`
    have hi4B : -(2 * B) ≤ (i4.val : ℤ) ∧ (i4.val : ℤ) ≤ 2 * B := by
      rw [e_i4]
      refine ⟨?_, ?_⟩
      · linarith [htB.1, hi1B.2]
      · linarith [htB.2, hi1B.1]
    have habs : |(neg_zeta.val : ℤ) * (i5.val : ℤ)| ≤ 108083094619162111 := by
      rw [abs_mul]
      have h1 : |(neg_zeta.val : ℤ)| ≤ 50330113 := by
        rw [abs_le]; unfold pNtt at hzlo hzhi; constructor <;> linarith
      have h2 : |(i5.val : ℤ)| ≤ 2147483647 := by
        rw [e_i5, abs_le]; constructor <;> linarith [hi4B.1, hi4B.2]
      calc |(neg_zeta.val : ℤ)| * |(i5.val : ℤ)|
          ≤ 50330113 * 2147483647 := mul_le_mul h1 h2 (abs_nonneg _) (by norm_num)
        _ = 108083094619162111 := by norm_num
    rw [abs_le] at habs
    have e_i6 : (i6.val : ℤ) = (neg_zeta.val : ℤ) * (i5.val : ℤ) := by
      rw [i6_post, I64_wrapping_mul_exact neg_zeta i5 (by linarith [habs.1])
        (by linarith [habs.2])]
    have hpow31 : (2:ℤ) ^ 31 * pNtt = 108083094669492224 := by unfold pNtt; norm_num
    apply WP.spec_bind (mont_reduce_spec i6
      (by rw [e_i6, hpow31]; linarith [habs.1]) (by rw [e_i6, hpow31]; linarith [habs.2]))
    intro i7 hi7
    obtain ⟨h7mod, h7lo, h7hi⟩ := hi7
    step*
    -- the pointwise effect of the two writes (`a[j]` first, then `a[j+len]`)
    all_goals
      have ha2 : ∀ c, aZ a2 c = if c = iter.start.val + lenv then (i7.val : ℤ)
          else if c = iter.start.val then (i2.val : ℤ) else aZ a c := by
        intro c
        rw [a2_post, a1_post, aZ_set (a.set iter.start i2) i i7 (by omega) c,
          aZ_set a iter.start i2 (by omega) c, hiv]
    case hBu =>
      intro c hc1 hc2
      rw [ha2 c, if_neg (by omega), if_neg (by omega)]
      exact hBu c (by omega) hc2
    case hBu2 =>
      intro c hc1 hc2
      rw [ha2 c, if_neg (by omega), if_neg (by omega)]
      exact hBu2 c (by omega) hc2
    case hBg =>
      intro c hc
      rw [ha2 c]
      split_ifs
      · rw [abs_le]; unfold pNtt at h7lo h7hi hpB; constructor <;> linarith
      · rw [e_i2, abs_le]; constructor <;> linarith [htB.1, htB.2, hi1B.1, hi1B.2]
      · exact hBg c hc
    -- the Montgomery product read in `ℤ/p`
    have hmt : ((i7.val : ℤ) : Zp) = δ * (aP a iter.start.val - aP a (iter.start.val + lenv)) := by
      have h := mont_val_Zp (t := (i7.val : ℤ)) (x := (i5.val : ℤ)) hzeta
        (by rw [← e_i6]; exact h7mod)
      rw [h, e_i5, e_i4]
      congr 1
      unfold aP
      rw [← e_t, ← e_i1]
      push_cast
      ring
    have hrj : aZ r iter.start.val = (t.val : ℤ) + (i1.val : ℤ) := by
      rw [r_post2 _ (by omega), ha2 _, if_neg (by omega), if_pos rfl, e_i2]
    have hrjl : aZ r (iter.start.val + lenv) = (i7.val : ℤ) := by
      rw [r_post3 _ (by omega) (by omega), ha2 _, if_pos rfl]
    refine ⟨?_, ?_, ?_, ?_, r_post5⟩
    · intro j hj1 hj2
      rcases eq_or_lt_of_le hj1 with hje | hjgt
      · subst hje
        refine ⟨?_, ?_⟩
        · rw [aP_def, hrj, e_t, e_i1]
          unfold aP
          push_cast
          ring
        · rw [aP_def, hrjl]
          exact hmt
      · have h1 := r_post1 j (by omega) hj2
        have hu1 : aP a2 j = aP a j := by
          unfold aP; rw [ha2 j, if_neg (by omega), if_neg (by omega)]
        have hu2 : aP a2 (j + lenv) = aP a (j + lenv) := by
          unfold aP; rw [ha2 _, if_neg (by omega), if_neg (by omega)]
        rw [hu1, hu2] at h1
        exact h1
    · intro c hc
      rw [r_post2 c (by omega), ha2 c, if_neg (by omega), if_neg (by omega)]
    · intro c hc1 hc2
      rw [r_post3 c hc1 (by omega), ha2 c, if_neg (by omega), if_neg (by omega)]
    · intro c hc
      rw [r_post4 c hc, ha2 c, if_neg (by omega), if_neg (by omega)]
  · let* ⟨ o, iter1, hnone, _ ⟩ ← core.iter.range.IteratorRange.next_Usize_none_spec
    rw [hnone]; simp only [WP.spec_ok]
    refine ⟨?_, ?_, ?_, ?_, hBg⟩
    · intro j hj1 hj2; omega
    · intro c _; trivial
    · intro c _ _; trivial
    · intro c _; trivial
  termination_by iter.«end».val - iter.start.val
  decreasing_by scalar_decr_tac

end Kopis.Properties
