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


/-! ## The mid-way Barrett pass

After the `len = 8` level the code re-centres every coefficient (the `if len1 = 16` branch), so
the remaining four levels start from `|a| < p` again.  `invntt_loop0_loop1` has the same body as
the forward transform's `ntt_loop1`, so this is `ntt_barrett_loop_spec` verbatim on the other
function. -/

theorem invntt_barrett_loop_spec
    (iter : core.slice.iter.IterMut I32)
    (back : core.slice.iter.IterMut I32 → core.slice.iter.IterMut I32)
    (orig : Slice I32) (B : ℤ)
    (h_slice : iter.slice = orig)
    (h_iter_i : iter.i ≤ orig.length)
    (hlen : orig.length = 256)
    (hB : ∀ j, j < 256 → |((orig.val[j]!).val : ℤ)| ≤ B)
    (hBle : B ≤ 42 * pNtt)
    (hback_len : ∀ im : core.slice.iter.IterMut I32,
      im.slice.length = 256 → (back im).slice.length = 256)
    (hback_writes : ∀ im : core.slice.iter.IterMut I32, im.slice.length = 256 →
      ∀ j, j < iter.i → BarrettOK (((back im).slice.val[j]!).val : ℤ) ((orig.val[j]!).val : ℤ))
    (hback_rest : ∀ im : core.slice.iter.IterMut I32, im.slice.length = 256 →
      ∀ j, iter.i ≤ j → j < 256 → (back im).slice.val[j]! = im.slice.val[j]!) :
    arithmetic.ntt.invntt_loop0_loop1 iter back
      ⦃ (p : core.slice.iter.IterMut I32 ×
              (core.slice.iter.IterMut I32 → core.slice.iter.IterMut I32)) =>
          (p.2 p.1).slice.length = 256 ∧
          ∀ j, j < 256 →
            BarrettOK (((p.2 p.1).slice.val[j]!).val : ℤ) ((orig.val[j]!).val : ℤ) ⦄ := by
  unfold arithmetic.ntt.invntt_loop0_loop1
  by_cases hlt : iter.i < iter.slice.len
  · let* ⟨ o, iter1, next_back, h_all ⟩ ← iter_mut_next_spec
    obtain ⟨ho, hit2_slice, hit2_i, _, hsome_set⟩ := h_all
    rw [ho]
    simp only []
    have hi_pe : iter.slice.length = orig.length := by rw [h_slice]
    have hi_lt : iter.i < 256 := by rw [← hlen, ← hi_pe]; scalar_tac
    -- the element being reduced is `orig[iter.i]`
    have hbv : orig.val.length = 256 := by rw [← hlen]
    have hb : iter.i < orig.val.length := by omega
    have helem : iter.slice[iter.i] = orig.val[iter.i]! := by
      rw [getElem!_pos orig.val iter.i hb]
      exact List.getElem_of_eq (by rw [h_slice]) _
    have hBelem : |((iter.slice[iter.i]).val : ℤ)| ≤ B := by rw [helem]; exact hB _ hi_lt
    rw [abs_le] at hBelem
    let* ⟨ coeff1, hc1mod, hc1lo, hc1hi ⟩ ←
      barrett_reduce_spec (iter.slice[iter.i]) (by linarith [hBelem.1]) (by linarith [hBelem.2])
    apply WP.spec_mono
      (invntt_barrett_loop_spec iter1 (fun im => back (next_back im (some coeff1))) orig B
        (by rw [hit2_slice, h_slice]) (by rw [hit2_i]; omega) hlen hB hBle ?len ?writes ?rest)
    case len =>
      intro im him
      have him_set : (next_back im (some coeff1)).slice.length = 256 := by
        rw [hsome_set]; simp only; rw [Slice.setAtNat_length]; exact him
      exact hback_len _ him_set
    case writes =>
      intro im him j hj
      rw [hit2_i] at hj
      have him_set : (next_back im (some coeff1)).slice.length = 256 := by
        rw [hsome_set]; simp only; rw [Slice.setAtNat_length]; exact him
      by_cases hji : j = iter.i
      · subst hji
        have hrest := hback_rest (next_back im (some coeff1)) him_set iter.i (le_refl _) hi_lt
        have hkey : (back (next_back im (some coeff1))).slice.val[iter.i]! = coeff1 := by
          rw [hrest, hsome_set]
          exact Slice.getElem!_Nat_setAtNat_eq _ _ _ (by rw [him]; exact hi_lt)
        rw [hkey]
        refine ⟨?_, hc1lo, hc1hi⟩
        rw [← helem]
        exact hc1mod
      · exact hback_writes (next_back im (some coeff1)) him_set j (by omega)
    case rest =>
      intro im him j hj_ge hj_lt
      rw [hit2_i] at hj_ge
      have him_set : (next_back im (some coeff1)).slice.length = 256 := by
        rw [hsome_set]; simp only; rw [Slice.setAtNat_length]; exact him
      have hrest := hback_rest (next_back im (some coeff1)) him_set j (by omega) hj_lt
      rw [hrest, hsome_set]
      exact Slice.getElem!_Nat_setAtNat_ne _ _ _ _ (by omega)
    intro r hpost; exact hpost
  · have hge : iter.i ≥ iter.slice.len := by scalar_tac
    have hi_eq : iter.i = 256 := by
      have hpe : iter.slice.length = orig.length := by rw [h_slice]
      have hl : iter.slice.len.val = 256 := by
        rw [← hlen, ← hpe]; simp [Slice.len, Slice.length]
      scalar_tac
    let* ⟨ o, iter1, next_back, h_all ⟩ ← iter_mut_next_spec_none
    obtain ⟨ho, hit2_eq, hsome_back⟩ := h_all
    rw [ho]
    have hbi : next_back iter1 none = iter := (hsome_back iter1 none).trans hit2_eq
    show (back (next_back iter1 none)).slice.length = 256 ∧
        ∀ j, j < 256 →
          BarrettOK (((back (next_back iter1 none)).slice.val[j]!).val : ℤ)
            ((orig.val[j]!).val : ℤ)
    refine ⟨by rw [hbi]; exact hback_len iter (by rw [h_slice, hlen]), ?_⟩
    intro j hj
    rw [hbi]
    exact hback_writes iter (by rw [h_slice, hlen]) j (by omega)
  termination_by iter.slice.len.val - iter.i
  decreasing_by scalar_decr_tac

/-! ## The outer loop: all eight merge levels

`invntt_loop0 a k len` doubles `len` until it reaches 256.  Writing `len = 2^e`, the level merges
`2^(8-e)` blocks in pairs, so the invariant carried across iterations is
`State (2^(8-e)) (2^e) c f`, and each iteration is one `State_gs` step — which *doubles* the
scale `c`, giving the `2^8` that `INVNTT_SCALE` cancels at the end.

The magnitude schedule is `B_e = 2^(e mod 4) · p`: the sum path doubles each level, and the
`if len1 = 16` branch (i.e. after the `e = 3` level) Barrett-reduces everything back under `p`.
That is why the bound hypothesis below is stated as `2 ^ (e % 4) * pNtt` — it is exactly the
schedule the code realises. -/

/-- The coefficient bound entering the level with `len = 2^e`.  The sum path doubles each level
and the `if len1 = 16` branch resets it after `e = 3`, giving `p, 2p, 4p, 8p, p, 2p, 4p, 8p`; once
the loop has finished (`e = 8`) the last level's doubling leaves `16p`. -/
def invBnd (e : ℕ) : ℤ := if e = 8 then 16 * pNtt else 2 ^ (e % 4) * pNtt

theorem invBnd_le (e : ℕ) : invBnd e ≤ 16 * pNtt := by
  have hp : (0:ℤ) < pNtt := by unfold pNtt; norm_num
  unfold invBnd
  split
  · exact le_refl _
  · have h : (2:ℤ) ^ (e % 4) ≤ 8 := by
      have : e % 4 ≤ 3 := by omega
      calc (2:ℤ) ^ (e % 4) ≤ 2 ^ 3 := pow_le_pow_right₀ (by norm_num) this
        _ = 8 := by norm_num
    nlinarith

/-- `invntt_loop0` with `len = 256` does nothing: this is how the level loop stops. -/
theorem invntt_loop0_done (a : Array I32 256#usize) (k len : Usize) (hlen : len.val = 256) :
    arithmetic.ntt.invntt_loop0 a k len ⦃ (r : Array I32 256#usize) => r = a ⦄ := by
  have hRD : (consts.RING_DEG : Usize).val = 256 := by simp only [consts.RING_DEG]; rfl
  unfold arithmetic.ntt.invntt_loop0
  rw [if_neg (by scalar_tac)]
  simp only [WP.spec_ok]

theorem invntt_outer_spec : ∀ (d e : ℕ) (a : Array I32 256#usize) (k len : Usize)
    (f : ℕ → Zp) (cc : Zp),
    e + d = 8 →
    len.val = 2 ^ e →
    k.val = 2 ^ (8 - e) →
    State (2 ^ (8 - e)) (2 ^ e) cc f (aP a) →
    (∀ x, x < 256 → |aZ a x| ≤ invBnd e) →
    arithmetic.ntt.invntt_loop0 a k len
      ⦃ (r : Array I32 256#usize) =>
          State 1 256 (cc * 2 ^ (8 - e)) f (aP r)
          ∧ (∀ x, x < 256 → |aZ r x| ≤ 16 * pNtt) ⦄ := by
  have hp0 : (0:ℤ) < pNtt := by unfold pNtt; norm_num
  intro d
  induction d with
  | zero =>
    intro e a k len f cc hed hlen hk hst hBd
    have he : e = 8 := by omega
    subst he
    have Hz := invntt_loop0_done a k len (by rw [hlen]; norm_num)
    apply WP.spec_mono Hz
    rintro r rfl
    refine ⟨by simpa using hst, fun x hx => ?_⟩
    have h := hBd x hx
    unfold invBnd at h
    rw [if_pos rfl] at h
    exact h
  | succ d ih =>
    intro e a k len f cc hed hlen hk hst hBd
    have he7 : e ≤ 7 := by omega
    have hsub : 8 - e = (7 - e) + 1 := by omega
    have hnbeq : (2:ℕ) ^ (8 - e) = 2 * 2 ^ (7 - e) := by rw [hsub]; ring
    have hnb256 : 2 ^ (7 - e) * (2 * 2 ^ e) = 256 := by
      rw [show 2 ^ (7 - e) * (2 * 2 ^ e) = 2 ^ ((7 - e) + (e + 1)) by ring,
        show (7 - e) + (e + 1) = 8 by omega]
      norm_num
    have hlpos : 0 < (2:ℕ) ^ e := Nat.one_le_two_pow
    have hlt256 : (2:ℕ) ^ e < 256 := by
      calc (2:ℕ) ^ e ≤ 2 ^ 7 := Nat.pow_le_pow_right (by norm_num) he7
        _ < 256 := by norm_num
    have hRD : (consts.RING_DEG : Usize).val = 256 := by simp only [consts.RING_DEG]; rfl
    -- the magnitude bound entering this level, and after it
    have hBe : (2:ℤ) ^ (e % 4) ≤ 8 := by
      have : e % 4 ≤ 3 := by omega
      calc (2:ℤ) ^ (e % 4) ≤ 2 ^ 3 := by
            exact pow_le_pow_right₀ (by norm_num) this
        _ = 8 := by norm_num
    have hBe1 : (1:ℤ) ≤ 2 ^ (e % 4) := one_le_pow₀ (by norm_num)
    have hBv : invBnd e = 2 ^ (e % 4) * pNtt := by unfold invBnd; rw [if_neg (by omega)]
    have hB0 : pNtt ≤ invBnd e := by rw [hBv]; nlinarith
    have hBhi : 2 * invBnd e ≤ 2147483647 := by rw [hBv]; unfold pNtt at *; nlinarith
    unfold arithmetic.ntt.invntt_loop0
    rw [if_pos (by scalar_tac)]
    -- merge every block at this level
    apply WP.spec_bind (invntt_mid_spec (nb := 2 ^ (7 - e)) (lenv := 2 ^ e) (b0 := 0)
      a k len 0#usize (invBnd e) hlen hlpos hnb256 (Nat.zero_le _) (by simp)
      (by rw [hk, hnbeq]; omega) hB0 hBhi
      (fun x _ hx2 => hBd x hx2) (fun x hx => le_trans (hBd x hx) (by linarith)))
    rintro ⟨a1, k1⟩ ⟨hA1, _, hBd1, hk1⟩
    simp only at hA1 hBd1 hk1
    -- one `State_gs` step, which doubles the scale
    have hstep : State (2 ^ (7 - e)) (2 * 2 ^ e) (2 * cc) f (aP a1) :=
      State_gs (nb := 2 ^ (7 - e)) (m' := 2 ^ e) (c := cc) (f := f) (a := aP a) (a' := aP a1)
        Nat.one_le_two_pow
        (by have h : (2:ℕ) ^ (7 - e) ≤ 2 ^ 7 := Nat.pow_le_pow_right (by norm_num) (by omega)
            norm_num at h ⊢
            omega)
        ⟨7 - e, by omega, rfl⟩
        (by rw [hnbeq] at hst; exact hst)
        (fun b hb r' hr' => hA1 b (Nat.zero_le _) hb r' hr')
    -- `len1 = 2·len`
    let* ⟨ len1, hlen1v ⟩ ←
      Std.Usize.mul_spec (show len.val * (2#usize).val ≤ Usize.max from by scalar_tac)
    have hlen1 : len1.val = 2 ^ (e + 1) := by rw [hlen1v, hlen, pow_succ]
    have hst1 : State (2 ^ (8 - (e + 1))) (2 ^ (e + 1)) (2 * cc) f (aP a1) := by
      rw [show 8 - (e + 1) = 7 - e by omega, pow_succ, mul_comm ((2:ℕ) ^ e) 2]
      exact hstep
    have hk1' : k1.val = 2 ^ (8 - (e + 1)) := by rw [hk1, show 8 - (e + 1) = 7 - e by omega]
    have hscale : cc * 2 ^ (8 - e) = (2 * cc) * 2 ^ (8 - (e + 1)) := by
      rw [show 8 - e = (8 - (e + 1)) + 1 by omega, pow_succ]
      ring
    rw [hscale]
    -- either the Barrett pass fires (after the `e = 3` level) or it does not
    by_cases hbar : len1 = 16#usize
    · rw [if_pos hbar]
      have he3 : e = 3 := by
        have h16 : len1.val = 16 := by rw [hbar]; rfl
        rw [hlen1] at h16
        have : (2:ℕ) ^ (e + 1) = 2 ^ 4 := by rw [h16]; norm_num
        exact Nat.succ_injective (Nat.pow_right_injective (by norm_num) this)
      -- after the `e = 3` level the bound is `16p`, which is inside Barrett's input range
      have hBd1' : ∀ x, x < 256 → |aZ a1 x| ≤ 16 * pNtt := by
        intro x hx
        have h := hBd1 x hx
        rw [hBv, he3] at h
        norm_num at h ⊢
        linarith
      let* ⟨ s, to_back, hs_val, hto_back ⟩ ← Array.to_slice_mut_spec
      let* ⟨ it0, it_back, h_it_slice, h_it_zero, h_it_back ⟩ ← iter_mut_spec
      have hs_len : s.length = 256 := by
        rw [Slice.length, hs_val]; simpa using a1.property
      have hit_len : it0.slice.length = 256 := by rw [h_it_slice]; exact hs_len
      have horig : ∀ x, x < 256 → ((it0.slice.val[x]!).val : ℤ) = aZ a1 x := by
        intro x _
        unfold aZ
        exact congrArg (fun l => ((l[x]! : I32).val : ℤ)) (by rw [h_it_slice, hs_val])
      have hsB : ∀ x, x < 256 → |((it0.slice.val[x]!).val : ℤ)| ≤ 16 * pNtt := by
        intro x hx; rw [horig x hx]; exact hBd1' x hx
      let* ⟨ r_it, r_back, hr_len, hr_writes ⟩ ←
        invntt_barrett_loop_spec it0 (fun im => im) it0.slice (16 * pNtt) rfl
          (by rw [h_it_zero]; exact Nat.zero_le _) hit_len hsB (by unfold pNtt; norm_num)
          (fun _ him => him)
          (fun _ _ x hx => by rw [h_it_zero] at hx; omega)
          (fun _ _ _ _ _ => rfl)
      simp only [h_it_back]
      have hval_eq : (to_back (r_back r_it).slice).val = (r_back r_it).slice.val := by
        rw [hto_back]
        exact Std.Array.from_slice_val a1 (r_back r_it).slice hr_len
      have hres : ∀ x, x < 256 →
          aZ (to_back (r_back r_it).slice) x = (((r_back r_it).slice.val[x]!).val : ℤ) := by
        intro x _
        unfold aZ
        rw [show (to_back (r_back r_it).slice).val[x]! = (r_back r_it).slice.val[x]! from
          congrArg (fun l => l[x]!) hval_eq]
      -- the Barrett pass preserves residues, so the `State` invariant survives it
      have hst2 : State (2 ^ (8 - (e + 1))) (2 ^ (e + 1)) (2 * cc) f
          (aP (to_back (r_back r_it).slice)) := by
        refine State_congr (by rw [show 8 - (e + 1) = 7 - e by omega, ← pow_add,
          show (7 - e) + (e + 1) = 8 by omega]; norm_num) hst1 (fun x hx => ?_)
        have hb := hr_writes x hx
        unfold aP
        rw [hres x hx, horig x hx] at *
        exact intCast_eq_of_emod hb.1
      have hBd2 : ∀ x, x < 256 →
          |aZ (to_back (r_back r_it).slice) x| ≤ invBnd (e + 1) := by
        intro x hx
        have hb := hr_writes x hx
        have hpow : invBnd (e + 1) = pNtt := by
          unfold invBnd; rw [he3, if_neg (by norm_num)]; norm_num
        rw [hres x hx, abs_le, hpow]
        exact ⟨le_of_lt hb.2.1, le_of_lt hb.2.2⟩
      have IH := ih (e + 1) (to_back (r_back r_it).slice) k1 len1 f (2 * cc) (by omega) hlen1
        hk1' hst2 hBd2
      exact IH
    · rw [if_neg hbar]
      -- `len1 ≠ 16` rules out `e = 3`; `e = 7` is the last level, where the bound becomes `16p`
      have hne3 : e ≠ 3 := by
        rintro rfl
        have h16 : len1.val = 16 := by rw [hlen1]; norm_num
        exact hbar (by scalar_tac)
      have hBd1' : ∀ x, x < 256 → |aZ a1 x| ≤ invBnd (e + 1) := by
        intro x hx
        have hb := hBd1 x hx
        rw [hBv] at hb
        rcases Nat.eq_or_lt_of_le he7 with he7' | he7'
        · -- `e = 7`: the loop is about to stop, and `16p` is the final bound
          subst he7'
          have hpow : invBnd (7 + 1) = 16 * pNtt := by unfold invBnd; rw [if_pos rfl]
          rw [hpow]
          norm_num at hb ⊢
          linarith
        · have hmod : (e + 1) % 4 = (e % 4) + 1 := by omega
          have hpow : invBnd (e + 1) = 2 ^ (e % 4) * 2 * pNtt := by
            unfold invBnd; rw [if_neg (by omega), hmod, pow_succ]
          rw [hpow]
          have hring : (2:ℤ) ^ (e % 4) * 2 * pNtt = 2 * (2 ^ (e % 4) * pNtt) := by ring
          rw [hring]
          exact hb
      have IH := ih (e + 1) a1 k1 len1 f (2 * cc) (by omega) hlen1 hk1' hst1 hBd1'
      exact IH


/-! ## The final `INVNTT_SCALE` pass

`invntt_loop1` multiplies every coefficient by `INVNTT_SCALE = 256⁻¹·2⁶⁴` and Montgomery-reduces,
which divides by `2³²`.  Net: multiplication by `256⁻¹·2³²`, cancelling the `2⁸` the eight
Gentleman-Sande layers accumulated and one Montgomery factor from the pointwise product. -/

/-- The scalar the final pass applies: `INVNTT_SCALE · 2⁻³²`. -/
def invScale : Zp := ((44652572 : ℕ) : Zp) * Rinv

/-- What the final pass establishes for one coefficient. -/
def ScaleOK (x orig : ℤ) : Prop :=
  ((x : ℤ) : Zp) = invScale * ((orig : ℤ) : Zp) ∧ -pNtt < x ∧ x < pNtt

theorem invntt_scale_loop_spec
    (iter : core.slice.iter.IterMut I32)
    (back : core.slice.iter.IterMut I32 → core.slice.iter.IterMut I32)
    (orig : Slice I32) (B : ℤ)
    (h_slice : iter.slice = orig)
    (h_iter_i : iter.i ≤ orig.length)
    (hlen : orig.length = 256)
    (hB : ∀ j, j < 256 → |((orig.val[j]!).val : ℤ)| ≤ B)
    (hBle : B ≤ 16 * pNtt)
    (hback_len : ∀ im : core.slice.iter.IterMut I32,
      im.slice.length = 256 → (back im).slice.length = 256)
    (hback_writes : ∀ im : core.slice.iter.IterMut I32, im.slice.length = 256 →
      ∀ j, j < iter.i → ScaleOK (((back im).slice.val[j]!).val : ℤ) ((orig.val[j]!).val : ℤ))
    (hback_rest : ∀ im : core.slice.iter.IterMut I32, im.slice.length = 256 →
      ∀ j, iter.i ≤ j → j < 256 → (back im).slice.val[j]! = im.slice.val[j]!) :
    arithmetic.ntt.invntt_loop1 iter back
      ⦃ (p : core.slice.iter.IterMut I32 ×
              (core.slice.iter.IterMut I32 → core.slice.iter.IterMut I32)) =>
          (p.2 p.1).slice.length = 256 ∧
          ∀ j, j < 256 →
            ScaleOK (((p.2 p.1).slice.val[j]!).val : ℤ) ((orig.val[j]!).val : ℤ) ⦄ := by
  unfold arithmetic.ntt.invntt_loop1
  by_cases hlt : iter.i < iter.slice.len
  · let* ⟨ o, iter1, next_back, h_all ⟩ ← iter_mut_next_spec
    obtain ⟨ho, hit2_slice, hit2_i, _, hsome_set⟩ := h_all
    rw [ho]
    simp only []
    have hi_pe : iter.slice.length = orig.length := by rw [h_slice]
    have hi_lt : iter.i < 256 := by rw [← hlen, ← hi_pe]; scalar_tac
    -- the element being reduced is `orig[iter.i]`
    have hbv : orig.val.length = 256 := by rw [← hlen]
    have hb : iter.i < orig.val.length := by omega
    have helem : iter.slice[iter.i] = orig.val[iter.i]! := by
      rw [getElem!_pos orig.val iter.i hb]
      exact List.getElem_of_eq (by rw [h_slice]) _
    have hBelem : |((iter.slice[iter.i]).val : ℤ)| ≤ B := by rw [helem]; exact hB _ hi_lt
    rw [abs_le] at hBelem
    step*
    have e_i : (i.val : ℤ) = ((iter.slice[iter.i]).val : ℤ) := by
      rw [i_post, IScalar.cast_val_eq,
        show Min.min IScalarTy.I64.numBits IScalarTy.I32.numBits = 32 from rfl]
      exact bmod_i32_exact (by scalar_tac) (by scalar_tac)
    have e_i1 : (i1.val : ℤ) = 44652572 := by
      rw [i1_post, IScalar.cast_val_eq,
        show Min.min IScalarTy.I64.numBits IScalarTy.I32.numBits = 32 from rfl,
        show (arithmetic.ntt.INVNTT_SCALE : I32).val = 44652572 from by
          simp only [arithmetic.ntt.INVNTT_SCALE]; rfl]
      exact bmod_i32_exact (by norm_num) (by norm_num)
    -- `|coeff| ≤ 16p` and `INVNTT_SCALE < p`, so the product is well inside `2^31·p`
    have hprod : -35957903912010176 ≤ (i.val : ℤ) * (i1.val : ℤ)
        ∧ (i.val : ℤ) * (i1.val : ℤ) ≤ 35957903912010176 := by
      rw [e_i, e_i1]
      unfold pNtt at hBle
      constructor <;> nlinarith [hBelem.1, hBelem.2]
    have e_i2 : (i2.val : ℤ) = (i.val : ℤ) * (i1.val : ℤ) := by
      rw [i2_post, I64_wrapping_mul_exact i i1 (by linarith [hprod.1]) (by linarith [hprod.2])]
    have hpow31 : (2:ℤ) ^ 31 * pNtt = 108083094669492224 := by unfold pNtt; norm_num
    apply WP.spec_bind (mont_reduce_spec i2
      (by rw [e_i2, hpow31]; linarith [hprod.1]) (by rw [e_i2, hpow31]; linarith [hprod.2]))
    intro coeff1 hcc
    obtain ⟨hc1mod, hc1lo, hc1hi⟩ := hcc
    apply WP.spec_mono
      (invntt_scale_loop_spec iter1 (fun im => back (next_back im (some coeff1))) orig B
        (by rw [hit2_slice, h_slice]) (by rw [hit2_i]; omega) hlen hB hBle ?len ?writes ?rest)
    case len =>
      intro im him
      have him_set : (next_back im (some coeff1)).slice.length = 256 := by
        rw [hsome_set]; simp only; rw [Slice.setAtNat_length]; exact him
      exact hback_len _ him_set
    case writes =>
      intro im him j hj
      rw [hit2_i] at hj
      have him_set : (next_back im (some coeff1)).slice.length = 256 := by
        rw [hsome_set]; simp only; rw [Slice.setAtNat_length]; exact him
      by_cases hji : j = iter.i
      · subst hji
        have hrest := hback_rest (next_back im (some coeff1)) him_set iter.i (le_refl _) hi_lt
        have hkey : (back (next_back im (some coeff1))).slice.val[iter.i]! = coeff1 := by
          rw [hrest, hsome_set]
          exact Slice.getElem!_Nat_setAtNat_eq _ _ _ (by rw [him]; exact hi_lt)
        rw [hkey]
        refine ⟨?_, hc1lo, hc1hi⟩
        rw [← helem]
        have hmodfix : ((coeff1.val : ℤ) * 2 ^ 32) % pNtt
            = (44652572 * ((iter.slice[iter.i]).val : ℤ)) % pNtt := by
          rw [hc1mod, e_i2, e_i, e_i1]
          ring_nf
        exact mont_val_Zp (t := (coeff1.val : ℤ)) (x := ((iter.slice[iter.i]).val : ℤ))
          (zeta := 44652572) (γ := invScale) (by rw [invScale]; push_cast; ring) hmodfix
      · exact hback_writes (next_back im (some coeff1)) him_set j (by omega)
    case rest =>
      intro im him j hj_ge hj_lt
      rw [hit2_i] at hj_ge
      have him_set : (next_back im (some coeff1)).slice.length = 256 := by
        rw [hsome_set]; simp only; rw [Slice.setAtNat_length]; exact him
      have hrest := hback_rest (next_back im (some coeff1)) him_set j (by omega) hj_lt
      rw [hrest, hsome_set]
      exact Slice.getElem!_Nat_setAtNat_ne _ _ _ _ (by omega)
    intro r hpost; exact hpost
  · have hge : iter.i ≥ iter.slice.len := by scalar_tac
    have hi_eq : iter.i = 256 := by
      have hpe : iter.slice.length = orig.length := by rw [h_slice]
      have hl : iter.slice.len.val = 256 := by
        rw [← hlen, ← hpe]; simp [Slice.len, Slice.length]
      scalar_tac
    let* ⟨ o, iter1, next_back, h_all ⟩ ← iter_mut_next_spec_none
    obtain ⟨ho, hit2_eq, hsome_back⟩ := h_all
    rw [ho]
    have hbi : next_back iter1 none = iter := (hsome_back iter1 none).trans hit2_eq
    show (back (next_back iter1 none)).slice.length = 256 ∧
        ∀ j, j < 256 →
          ScaleOK (((back (next_back iter1 none)).slice.val[j]!).val : ℤ)
            ((orig.val[j]!).val : ℤ)
    refine ⟨by rw [hbi]; exact hback_len iter (by rw [h_slice, hlen]), ?_⟩
    intro j hj
    rw [hbi]
    exact hback_writes iter (by rw [h_slice, hlen]) j (by omega)
  termination_by iter.slice.len.val - iter.i
  decreasing_by scalar_decr_tac

end Kopis.Properties
