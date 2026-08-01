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
set_option maxRecDepth 100000

/-! ## The one assumed intrinsic

`ExtractedRust.lean` declares `core.num.I64.wrapping_neg` as an `axiom`: aeneas leaves Rust's
`i64::wrapping_neg` opaque, so it carries no definition to unfold.  Its meaning therefore has to
be assumed, exactly as for the two `count_ones` popcount intrinsics in `GenSecret.lean`.  The
opaque function itself is already on `TopLevelTheorems.lean`'s audited list; this spec is added
alongside it.

Note this assumption is *avoidable*: writing `0i64.wrapping_sub(ZETAS[k] as i64)` instead of
`(ZETAS[k] as i64).wrapping_neg()` in `src/arithmetic/ntt.rs` extracts to `IScalar.wrapping_sub`,
which has real semantics, and would remove this axiom from the trust base.  That is a Rust
change requiring re-extraction, so it is left as a recommendation. -/

/-- **Assumed spec for `i64::wrapping_neg`.**  Two's-complement negation, i.e. `Int.bmod` of the
negation — the same value semantics aeneas gives every other `wrapping_*` operation. -/
@[step] axiom I64.wrapping_neg_spec (x : I64) :
    core.num.I64.wrapping_neg x
      ⦃ (r : I64) => (r.val : ℤ) = Int.bmod (-(x.val : ℤ)) (2 ^ 64) ⦄

/-- On the range the twiddles occupy, `wrapping_neg` is exact negation. -/
theorem I64_wrapping_neg_exact (x : I64)
    (hlo : -9223372036854775808 < (x.val : ℤ)) (hhi : (x.val : ℤ) < 9223372036854775808) :
    core.num.I64.wrapping_neg x ⦃ (r : I64) => (r.val : ℤ) = -(x.val : ℤ) ⦄ := by
  apply WP.spec_mono (I64.wrapping_neg_spec x)
  intro r hr
  rw [hr]
  exact bmod_i64_exact (by omega) (by omega)

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

/-! ## The middle loop: every block at one level

`invntt_loop0_loop0 a k len start` walks `start` over the blocks being merged.  `k` counts *down*
here: entering with `b₀` blocks merged, `k = 2·nb - b₀`, so the block's table index is
`k - 1 = 2·nb - 1 - b₀` — exactly the index `NttMath.zetaP_pair` pairs with the forward
transform's `nb + b₀`. -/

theorem invntt_mid_spec {nb lenv b0 : ℕ}
    (a : Array I32 256#usize) (k len start : Usize) (B : ℤ)
    (hlen : len.val = lenv) (hlpos : 0 < lenv)
    (hnb : nb * (2 * lenv) = 256)
    (hb0 : b0 ≤ nb) (hstart : start.val = b0 * (2 * lenv)) (hk : k.val = 2 * nb - b0)
    (hpB : pNtt ≤ B) (hBhi : 2 * B ≤ 2147483647)
    (hBu : ∀ c, start.val ≤ c → c < 256 → |aZ a c| ≤ B)
    (hBg : ∀ c, c < 256 → |aZ a c| ≤ 2 * B) :
    arithmetic.ntt.invntt_loop0_loop0 a k len start
      ⦃ (rk : Array I32 256#usize × Usize) =>
        (∀ b, b0 ≤ b → b < nb → ∀ r', r' < lenv →
            aP rk.1 (b * (2 * lenv) + r')
              = aP a (b * (2 * lenv) + r') + aP a (b * (2 * lenv) + lenv + r')
            ∧ aP rk.1 (b * (2 * lenv) + lenv + r')
              = (-(zetaP (2 * nb - 1 - b)))
                * (aP a (b * (2 * lenv) + r') - aP a (b * (2 * lenv) + lenv + r')))
        ∧ (∀ c, c < start.val → aZ rk.1 c = aZ a c)
        ∧ (∀ c, c < 256 → |aZ rk.1 c| ≤ 2 * B)
        ∧ rk.2.val = nb ⦄ := by
  have hp0 : (0:ℤ) < pNtt := by unfold pNtt; norm_num
  have hnb1 : 1 ≤ nb := by
    rcases Nat.eq_zero_or_pos nb with h | h
    · rw [h] at hnb; simp at hnb
    · exact h
  have hnb128 : nb ≤ 128 := by nlinarith
  have hRD : (consts.RING_DEG : Usize).val = 256 := by simp only [consts.RING_DEG]; rfl
  unfold arithmetic.ntt.invntt_loop0_loop0
  by_cases hlt : start < consts.RING_DEG
  · have hltv : start.val < 256 := by rw [← hRD]; scalar_tac
    have hb0lt : b0 < nb := by nlinarith
    have hkb : 2 * nb - 1 - b0 < 256 := by omega
    have hlenb : lenv ≤ 128 := by nlinarith
    have hkpos : 1 ≤ k.val := by omega
    step*
    case hbound => scalar_tac
    case hmax => scalar_tac
    have hk1v : k1.val = 2 * nb - 1 - b0 := by omega
    -- the twiddle: `neg_zeta = -ZETAS[k-1]`, so it denotes `-ζ_{2nb-1-b₀}`
    have hzv : (i1.val : ℤ) = (ZN[2 * nb - 1 - b0]! : ℤ) := by
      have h1 : (i1.val : ℤ) = (i.val : ℤ) := by
        rw [i1_post, IScalar.cast_val_eq,
          show Min.min IScalarTy.I64.numBits IScalarTy.I32.numBits = 32 from rfl]
        exact bmod_i32_exact (by scalar_tac) (by scalar_tac)
      have h2 : (i.val : ℤ) = (ZN[k1.val]! : ℤ) := by
        rw [i_post]; exact zetas_val' k1.val (by omega) _
      rw [h1, h2, hk1v]
    have hznlt : ZN[2 * nb - 1 - b0]! < pNtt := by
      have := ZN_lt (2 * nb - 1 - b0) (by omega); unfold pNtt; exact_mod_cast this
    have hzn0 : (0:ℤ) ≤ (ZN[2 * nb - 1 - b0]! : ℤ) := by positivity
    have hnz : (neg_zeta.val : ℤ) = -(i1.val : ℤ) := by
      rw [neg_zeta_post]
      exact bmod_i64_exact (by rw [hzv]; unfold pNtt at hznlt; omega)
        (by rw [hzv]; unfold pNtt at hznlt; omega)
    have hnzlo : -pNtt < (neg_zeta.val : ℤ) := by
      rw [hnz, hzv]; unfold pNtt at hznlt ⊢; omega
    have hnzhi : (neg_zeta.val : ℤ) < pNtt := by rw [hnz, hzv]; linarith
    have hnzeta : ((neg_zeta.val : ℤ) : Zp) * Rinv = -(zetaP (2 * nb - 1 - b0)) := by
      rw [hnz, hzv, zetaP]
      push_cast
      ring
    -- run the block's merge
    have hi2v : i2.val = start.val + lenv := by rw [i2_post, hlen]
    have hiS : ({ start := start, «end» := i2 } : core.ops.range.Range Usize).start.val
        = start.val := rfl
    have hblkv : start.val + 2 * lenv ≤ 256 := by nlinarith
    apply WP.spec_bind (invntt_inner_spec (st := start.val) (lenv := lenv)
      { start := start, «end» := i2 } a len neg_zeta (-(zetaP (2 * nb - 1 - b0))) B hlen hlpos
      (by omega) (by omega) (by omega) hblkv hnzeta hnzlo hnzhi hpB hBhi
      (fun c hc1 hc2 => hBu c (by omega) (by omega))
      (fun c hc1 hc2 => hBu c (by omega) (by omega))
      hBg)
    intro a1 ha1
    obtain ⟨hA1, hU1, hU2, hU3, hBd1⟩ := ha1
    rw [hiS] at hA1 hU1 hU2
    -- advance to the next block
    -- `scalar_tac` is avoided here: it would try to normalise the `ZN[...]` literal in context
    have hUmax : 512 ≤ Usize.max := by
      rcases Usize.bounds_eq with h | h <;> rw [h] <;> simp only [U32.max_eq, U64.max_eq] <;> omega
    have h2u : (2#usize).val = 2 := rfl
    let* ⟨ i3, hi3 ⟩ ←
      Std.Usize.mul_spec (show (2#usize).val * len.val ≤ Usize.max from by rw [h2u, hlen]; omega)
    let* ⟨ start1, hs1 ⟩ ←
      Std.Usize.add_spec (show start.val + i3.val ≤ Usize.max from by
        rw [hi3, hlen]; omega)
    have hi3v : i3.val = 2 * lenv := by rw [hi3, hlen]
    have hs1v : start1.val = (b0 + 1) * (2 * lenv) := by rw [hs1, hi3v, hstart]; ring
    have IH := invntt_mid_spec (nb := nb) (lenv := lenv) (b0 := b0 + 1)
      a1 k1 len start1 B hlen hlpos hnb (by omega) hs1v (by omega) hpB hBhi
      (fun c hc1 hc2 => by rw [hU3 c (by omega)]; exact hBu c (by omega) hc2)
      hBd1
    apply WP.spec_mono IH
    rintro rk ⟨hR1, hR2, hR3, hR4⟩
    refine ⟨?_, ?_, hR3, hR4⟩
    · intro b hb1 hb2 r' hr'
      rcases eq_or_lt_of_le hb1 with hbe | hbgt
      · subst hbe
        have hx1 : aP rk.1 (b0 * (2 * lenv) + r') = aP a1 (b0 * (2 * lenv) + r') :=
          aP_congr (hR2 _ (by omega))
        have hx2 : aP rk.1 (b0 * (2 * lenv) + lenv + r') = aP a1 (b0 * (2 * lenv) + lenv + r') :=
          aP_congr (hR2 _ (by omega))
        have hA := hA1 (start.val + r') (by omega) (by omega)
        rw [show start.val + r' + lenv = b0 * (2 * lenv) + lenv + r' by omega, hstart] at hA
        rw [hx1, hx2]
        exact hA
      · have h := hR1 b (by omega) hb2 r' hr'
        rw [aP_congr (hU3 (b * (2 * lenv) + r') (by nlinarith)),
          aP_congr (hU3 (b * (2 * lenv) + lenv + r') (by nlinarith))] at h
        exact h
    · intro c hc
      rw [hR2 c (by omega), hU1 c (by omega)]
  · have hgev : 256 ≤ start.val := by rw [← hRD]; scalar_tac
    have hb0eq : b0 = nb := by nlinarith
    rw [if_neg hlt]
    simp only [WP.spec_ok]
    refine ⟨?_, ?_, hBg, by omega⟩
    · intro b hb1 hb2; omega
    · intro c _; trivial
  termination_by 256 - start.val
  decreasing_by
    -- `scalar_decr_tac` is avoided: its `simp` normalises the `ZN` list literal in context
    simp_wf
    omega

end Kopis.Properties
