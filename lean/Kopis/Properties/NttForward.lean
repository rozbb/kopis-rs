/-
  # Kopis/Properties/NttForward.lean — the extracted forward NTT computes the CRT transform.

  This file connects the three nested loops of `arithmetic.ntt.ntt` (plus its closing Barrett
  pass) to the pure-math layer in `NttMath.lean`.  The mathematical content is entirely there;
  what happens here is the extracted-code bookkeeping:

  * reading an `[i32; 256]` as a coefficient function (`aZ` for the integer value, `aP` for its
    residue mod `p`);
  * showing every `wrapping_*` in the butterfly is exact, which is a magnitude argument: an
    input bounded by `B` produces an output bounded by `B + p`, and eight layers starting from
    `|a| < 2¹⁶` stay under `2¹⁶ + 8p < 2³¹`;
  * matching the loop's `(k, len, start, j)` index arithmetic to the `State` invariant's
    `(nb, m, b, r)`.

  The innermost loop is the butterfly over one block; `ntt_inner_spec` describes its effect
  pointwise, which is exactly the `hbut` hypothesis `NttMath.State_ct` asks for.
-/
import Kopis.Properties.NttMath
import Kopis.Properties.NttReduce

open Aeneas Aeneas.Std Result RustKopis
open scoped BigOperators

namespace Kopis.Properties

open NttMath

set_option maxHeartbeats 1000000

/-! ## Reading an `[i32; 256]` -/

/-- The integer value of coefficient `c`. -/
def aZ (a : Array I32 256#usize) (c : ℕ) : ℤ := ((a.val[c]!).val : ℤ)

/-- The residue of coefficient `c` mod the NTT prime. -/
def aP (a : Array I32 256#usize) (c : ℕ) : Zp := ((aZ a c : ℤ) : Zp)

theorem aP_def (a : Array I32 256#usize) (c : ℕ) : aP a c = ((aZ a c : ℤ) : Zp) := rfl

theorem aP_congr {x y : Array I32 256#usize} {c : ℕ} (h : aZ x c = aZ y c) : aP x c = aP y c := by
  unfold aP; rw [h]

/-- `getElem!` after a `List.set` at an in-bounds index. -/
theorem getElem!_list_set {α : Type _} [Inhabited α] (l : List α) (j : ℕ) (v : α) (k : ℕ)
    (hj : j < l.length) : (l.set j v)[k]! = if k = j then v else l[k]! := by
  by_cases h : k = j
  · subst h
    rw [getElem!_pos _ k (by rw [List.length_set]; exact hj), List.getElem_set_self, if_pos rfl]
  · by_cases hk : k < l.length
    · rw [getElem!_pos _ k (by rw [List.length_set]; exact hk),
        List.getElem_set_of_ne (Ne.symm h), ← getElem!_pos _ k hk, if_neg h]
    · rw [getElem!_neg _ k (by rw [List.length_set]; exact hk), getElem!_neg _ k hk, if_neg h]

theorem aZ_set (a : Array I32 256#usize) (i : Usize) (v : I32) (hi : i.val < 256) (c : ℕ) :
    aZ (a.set i v) c = if c = i.val then (v.val : ℤ) else aZ a c := by
  have hlen : a.val.length = 256 := by simpa using a.property
  unfold aZ
  rw [Array.set_val_eq, getElem!_list_set a.val i.val v c (by rw [hlen]; exact hi)]
  split <;> rfl

theorem aP_set (a : Array I32 256#usize) (i : Usize) (v : I32) (hi : i.val < 256) (c : ℕ) :
    aP (a.set i v) c = if c = i.val then ((v.val : ℤ) : Zp) else aP a c := by
  unfold aP
  rw [aZ_set a i v hi c]
  split <;> rfl

/-- The value read by `Array.index_usize` is `aZ`. -/
theorem aZ_getElem (a : Array I32 256#usize) (i : Usize) (hi : i.val < 256) :
    ((a.val[i.val]'(by rw [show a.val.length = 256 by simpa using a.property]; exact hi)).val : ℤ)
      = aZ a i.val := by
  unfold aZ
  rw [getElem!_pos a.val i.val (by rw [show a.val.length = 256 by simpa using a.property]; exact hi)]

/-! ## From an integer congruence mod `p` to an equation in `ℤ/p` -/

theorem intCast_eq_of_emod {u v : ℤ} (h : u % pNtt = v % pNtt) : ((u : ℤ) : Zp) = ((v : ℤ) : Zp) :=
  (ZMod.intCast_eq_intCast_iff' u v pN).mpr (by simpa [pNtt] using h)

/-- `2³² · 2⁻³² = 1` in `ℤ/p`.  Stated with `2³²` already reduced to its residue `16907691`,
which is the normal form `push_cast` produces inside `ℤ/p`. -/
theorem twoPow32_Rinv : (16907691 : Zp) * Rinv = 1 := by
  have h := R32_Rinv
  push_cast at h
  exact h

/-- **What one `mont_reduce (ζ · x)` computes, in `ℤ/p`.**  The stored twiddle is `γ·2³²`, and
`mont_reduce` divides by `2³²`, so the two cancel and the result denotes `γ · x`.  This is the
only place the Montgomery representation is reasoned about. -/
theorem mont_val_Zp {t x zeta : ℤ} {γ : Zp}
    (hzeta : ((zeta : ℤ) : Zp) * Rinv = γ)
    (h : (t * 2 ^ 32) % pNtt = (zeta * x) % pNtt) :
    ((t : ℤ) : Zp) = γ * ((x : ℤ) : Zp) := by
  have hc : ((t * 2 ^ 32 : ℤ) : Zp) = ((zeta * x : ℤ) : Zp) := intCast_eq_of_emod h
  push_cast at hc
  calc ((t : ℤ) : Zp) = ((t : ℤ) : Zp) * ((16907691 : Zp) * Rinv) := by
        rw [twoPow32_Rinv, mul_one]
    _ = (((t : ℤ) : Zp) * (16907691 : Zp)) * Rinv := by ring
    _ = (((zeta : ℤ) : Zp) * ((x : ℤ) : Zp)) * Rinv := by rw [hc]
    _ = (((zeta : ℤ) : Zp) * Rinv) * ((x : ℤ) : Zp) := by ring
    _ = γ * ((x : ℤ) : Zp) := by rw [hzeta]

/-- The pointwise effect of one butterfly's two writes (`a[j+len]` first, then `a[j]`). -/
theorem aZ_butterfly (a : Array I32 256#usize) (j jl : Usize) (v5 v7 : I32)
    (hj : j.val < 256) (hjl : jl.val < 256) (c : ℕ) :
    aZ ((a.set jl v5).set j v7) c
      = if c = j.val then (v7.val : ℤ) else if c = jl.val then (v5.val : ℤ) else aZ a c := by
  rw [aZ_set (a.set jl v5) j v7 hj c, aZ_set a jl v5 hjl c]

/-! ## The innermost loop: one butterfly block

`ntt_loop0_loop0_loop0 iter a len zeta` runs `j` over `[iter.start, st + len)` performing
`t := ζ·a[j+len]; a[j+len] := a[j] - t; a[j] := a[j] + t`.  The postcondition describes the
result pointwise, which is precisely `State_ct`'s `hbut`. -/

theorem ntt_inner_spec {st lenv : ℕ} (iter : core.ops.range.Range Usize)
    (a : Array I32 256#usize) (len : Usize) (zeta : I64) (γ : Zp) (B : ℤ)
    (hlen : len.val = lenv) (hlpos : 0 < lenv)
    (hend : iter.«end».val = st + lenv)
    (hlo : st ≤ iter.start.val) (hhi : iter.start.val ≤ st + lenv)
    (hblk : st + 2 * lenv ≤ 256)
    (hzeta : ((zeta.val : ℤ) : Zp) * Rinv = γ)
    (hzlo : -pNtt < (zeta.val : ℤ)) (hzhi : (zeta.val : ℤ) < pNtt)
    (hB0 : 0 ≤ B) (hBhi : B + pNtt ≤ 2147483647)
    (hBu : ∀ c, iter.start.val ≤ c → c < st + lenv → |aZ a c| ≤ B)
    (hBu2 : ∀ c, iter.start.val + lenv ≤ c → c < st + 2 * lenv → |aZ a c| ≤ B)
    (hBg : ∀ c, c < 256 → |aZ a c| ≤ B + pNtt) :
    arithmetic.ntt.ntt_loop0_loop0_loop0 iter a len zeta
      ⦃ (r : Array I32 256#usize) =>
        (∀ j, iter.start.val ≤ j → j < st + lenv →
            aP r j = aP a j + γ * aP a (j + lenv)
            ∧ aP r (j + lenv) = aP a j - γ * aP a (j + lenv))
        ∧ (∀ c, c < iter.start.val → aZ r c = aZ a c)
        ∧ (∀ c, st + lenv ≤ c → c < iter.start.val + lenv → aZ r c = aZ a c)
        ∧ (∀ c, st + 2 * lenv ≤ c → aZ r c = aZ a c)
        ∧ (∀ c, c < 256 → |aZ r c| ≤ B + pNtt) ⦄ := by
  unfold arithmetic.ntt.ntt_loop0_loop0_loop0
  by_cases hlt : iter.start.val < iter.«end».val
  · let* ⟨ o, iter1, ho, hstart', hend' ⟩ ← core.iter.range.IteratorRange.next_Usize_some_spec
    rw [ho]; simp only
    have hj_lt : iter.start.val < st + lenv := by omega
    have hjb : iter.start.val < 256 := by omega
    have hjl : iter.start.val + lenv < 256 := by omega
    step*
    -- ## the two operands of the butterfly
    have hiv : i.val = iter.start.val + lenv := by rw [i_post, hlen]
    have hi1v : (i1.val : ℤ) = aZ a (iter.start.val + lenv) := by
      rw [i1_post, aZ_getElem a i (by omega), hiv]
    have hi1B : |(i1.val : ℤ)| ≤ B := by
      rw [hi1v]; exact hBu2 _ (by omega) (by omega)
    have e_i2 : (i2.val : ℤ) = (i1.val : ℤ) := by
      rw [i2_post, IScalar.cast_val_eq,
        show Min.min IScalarTy.I64.numBits IScalarTy.I32.numBits = 32 from rfl]
      exact bmod_i32_exact (by scalar_tac) (by scalar_tac)
    -- the `i64` product `ζ · a[j+len]` is exact and inside `mont_reduce`'s input range:
    -- `|ζ| < p` and `|a[j+len]| ≤ B ≤ 2¹⁵³⁴…`, so the product is ≤ 1.056·10¹⁷ < 2³¹·p
    have hBlt : B ≤ 2097153534 := by unfold pNtt at hBhi; linarith
    have habs : |(zeta.val : ℤ) * (i1.val : ℤ)| ≤ 105549974344569342 := by
      rw [abs_mul]
      have h1 : |(zeta.val : ℤ)| ≤ 50330113 := by
        rw [abs_le]; unfold pNtt at hzlo hzhi; constructor <;> linarith
      have h2 : |(i1.val : ℤ)| ≤ 2097153534 := le_trans hi1B hBlt
      calc |(zeta.val : ℤ)| * |(i1.val : ℤ)|
          ≤ 50330113 * 2097153534 := mul_le_mul h1 h2 (abs_nonneg _) (by norm_num)
        _ = 105549974344569342 := by norm_num
    rw [abs_le] at habs
    obtain ⟨hab_lo, hab_hi⟩ := habs
    have e_i3 : (i3.val : ℤ) = (zeta.val : ℤ) * (i1.val : ℤ) := by
      have hb1 : -9223372036854775808 ≤ (zeta.val : ℤ) * (i2.val : ℤ) := by
        rw [e_i2]; linarith
      have hb2 : (zeta.val : ℤ) * (i2.val : ℤ) < 9223372036854775808 := by
        rw [e_i2]; linarith
      rw [i3_post, I64_wrapping_mul_exact zeta i2 hb1 hb2, e_i2]
    -- ## the Montgomery multiplication
    have hpow31 : (2:ℤ) ^ 31 * pNtt = 108083094669492224 := by unfold pNtt; norm_num
    apply WP.spec_bind (mont_reduce_spec i3
      (by rw [e_i3, hpow31]; linarith) (by rw [e_i3, hpow31]; linarith))
    intro t ht
    obtain ⟨htmod, htlo, hthi⟩ := ht
    step*
    -- the pointwise effect of the two writes, and what they store, in every remaining goal
    all_goals
      have ha2 : ∀ c, aZ a2 c = if c = iter.start.val then (i7.val : ℤ)
          else if c = iter.start.val + lenv then (i5.val : ℤ) else aZ a c := by
        intro c
        rw [a2_post, a1_post, aZ_butterfly a iter.start i i5 i7 (by omega) (by omega) c, hiv]
      have e_i4 : (i4.val : ℤ) = aZ a iter.start.val := by
        rw [i4_post]
        exact aZ_getElem a iter.start (by omega)
      have hi4B : -B ≤ (i4.val : ℤ) ∧ (i4.val : ℤ) ≤ B := by
        have h := hBu iter.start.val (le_refl _) hj_lt
        rw [abs_le] at h
        rw [e_i4]
        exact h
      have e_i5 : (i5.val : ℤ) = (i4.val : ℤ) - (t.val : ℤ) := by
        unfold pNtt at hBhi htlo hthi
        rw [i5_post, I32_wrapping_sub_exact i4 t (by linarith [hi4B.1, hi4B.2])
          (by linarith [hi4B.1, hi4B.2])]
      have e_i6 : (i6.val : ℤ) = (i4.val : ℤ) := by
        rw [i6_post, aZ_getElem a1 iter.start (by omega), a1_post,
          aZ_set a i i5 (by omega) iter.start.val, if_neg (by omega), e_i4]
      have e_i7 : (i7.val : ℤ) = (i4.val : ℤ) + (t.val : ℤ) := by
        unfold pNtt at hBhi htlo hthi
        rw [i7_post, I32_wrapping_add_exact i6 t
          (by rw [e_i6]; linarith [hi4B.1, hi4B.2]) (by rw [e_i6]; linarith [hi4B.1, hi4B.2]),
          e_i6]
    -- ## the side goals `step*` left, then the postcondition
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
      · rw [e_i7, abs_le]; unfold pNtt at htlo hthi ⊢; constructor <;> linarith [hi4B.1, hi4B.2]
      · rw [e_i5, abs_le]; unfold pNtt at htlo hthi ⊢; constructor <;> linarith [hi4B.1, hi4B.2]
      · exact hBg c hc
    -- the Montgomery product, read in `ℤ/p`
    have hmt : ((t.val : ℤ) : Zp) = γ * aP a (iter.start.val + lenv) := by
      rw [aP_def, ← hi1v]
      exact mont_val_Zp hzeta (by rw [← e_i3]; exact htmod)
    have hrj : aZ r iter.start.val = (i4.val : ℤ) + (t.val : ℤ) := by
      rw [r_post2 _ (by omega), ha2 _, if_pos rfl, e_i7]
    have hrjl : aZ r (iter.start.val + lenv) = (i4.val : ℤ) - (t.val : ℤ) := by
      rw [r_post3 _ (by omega) (by omega), ha2 _, if_neg (by omega), if_pos rfl, e_i5]
    refine ⟨?_, ?_, ?_, ?_, r_post5⟩
    · intro j hj1 hj2
      rcases eq_or_lt_of_le hj1 with hje | hjgt
      · subst hje
        refine ⟨?_, ?_⟩
        · rw [aP_def, hrj, e_i4]
          push_cast
          rw [hmt, ← aP_def]
        · rw [aP_def, hrjl, e_i4]
          push_cast
          rw [hmt, ← aP_def]
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

/-- The `ZETAS` entry read by `Array.index_usize`, as an integer. -/
theorem zetas_val' (k : ℕ) (hk : k < 256)
    (h : k < (arithmetic.ntt.ZETAS).val.length) :
    (((arithmetic.ntt.ZETAS).val[k]'h).val : ℤ) = (ZN[k]! : ℤ) := by
  rw [← zetas_val k hk, getElem!_pos _ k h]

/-! ## The middle loop: every block at one level

`ntt_loop0_loop0 a k len start` walks `start` over the blocks of the current level, running one
butterfly per block.  At entry, `start = b₀·2·len` and `k + 1 = nb + b₀`, where `nb` is the number
of blocks; the `b`-th block's twiddle is table entry `nb + b`.  The postcondition gives the
butterfly relation for every block from `b₀` on, which at `b₀ = 0` is exactly `State_ct`'s
`hbut`. -/

theorem ntt_mid_spec {nb lenv b0 : ℕ}
    (a : Array I32 256#usize) (k len start : Usize) (B : ℤ)
    (hlen : len.val = lenv) (hlpos : 0 < lenv)
    (hnb : nb * (2 * lenv) = 256)
    (hb0 : b0 ≤ nb) (hstart : start.val = b0 * (2 * lenv)) (hk : k.val + 1 = nb + b0)
    (hB0 : 0 ≤ B) (hBhi : B + pNtt ≤ 2147483647)
    (hBu : ∀ c, start.val ≤ c → c < 256 → |aZ a c| ≤ B)
    (hBg : ∀ c, c < 256 → |aZ a c| ≤ B + pNtt) :
    arithmetic.ntt.ntt_loop0_loop0 a k len start
      ⦃ (rk : Array I32 256#usize × Usize) =>
        (∀ b, b0 ≤ b → b < nb → ∀ r', r' < lenv →
            aP rk.1 (b * (2 * lenv) + r')
              = aP a (b * (2 * lenv) + r') + zetaP (nb + b) * aP a (b * (2 * lenv) + lenv + r')
            ∧ aP rk.1 (b * (2 * lenv) + lenv + r')
              = aP a (b * (2 * lenv) + r') - zetaP (nb + b) * aP a (b * (2 * lenv) + lenv + r'))
        ∧ (∀ c, c < start.val → aZ rk.1 c = aZ a c)
        ∧ (∀ c, c < 256 → |aZ rk.1 c| ≤ B + pNtt)
        ∧ rk.2.val = 2 * nb - 1 ⦄ := by
  have hnb1 : 1 ≤ nb := by rcases Nat.eq_zero_or_pos nb with h | h; · omega
                           exact h
  have hnb128 : nb ≤ 128 := by nlinarith
  have hRD : (consts.RING_DEG : Usize).val = 256 := by simp only [consts.RING_DEG]; rfl
  unfold arithmetic.ntt.ntt_loop0_loop0
  by_cases hlt : start < consts.RING_DEG
  · -- one more block
    have hltv : start.val < 256 := by rw [← hRD]; scalar_tac
    have hb0lt : b0 < nb := by nlinarith
    have hkb : nb + b0 < 256 := by omega
    have hlenb : lenv ≤ 128 := by nlinarith
    step*
    have hk1v : k1.val = nb + b0 := by omega
    -- the twiddle read from the table
    have hzv : (zeta.val : ℤ) = (ZN[nb + b0]! : ℤ) := by
      have h1 : (zeta.val : ℤ) = (i.val : ℤ) := by
        rw [zeta_post, IScalar.cast_val_eq,
          show Min.min IScalarTy.I64.numBits IScalarTy.I32.numBits = 32 from rfl]
        exact bmod_i32_exact (by scalar_tac) (by scalar_tac)
      have h2 : (i.val : ℤ) = (ZN[k1.val]! : ℤ) := by
        rw [i_post]; exact zetas_val' k1.val (by omega) _
      rw [h1, h2, hk1v]
    have hznlt : ZN[nb + b0]! < pNtt := by
      have := ZN_lt (nb + b0) (by omega); unfold pNtt; exact_mod_cast this
    have hzlo : -pNtt < (zeta.val : ℤ) := by rw [hzv]; exact_mod_cast (by omega : -(pNtt) < (ZN[nb + b0]! : ℤ))
    have hzhi : (zeta.val : ℤ) < pNtt := by rw [hzv]; exact_mod_cast hznlt
    have hzeta : ((zeta.val : ℤ) : Zp) * Rinv = zetaP (nb + b0) := by
      rw [hzv, zetaP]; push_cast; ring
    -- run the block's butterfly.  The two `rfl`s let `omega` see through the anonymous
    -- `Range` constructor, whose projections it otherwise treats as opaque atoms.
    have hi1v : i1.val = start.val + lenv := by rw [i1_post, hlen]
    have hiS : ({ start := start, «end» := i1 } : core.ops.range.Range Usize).start.val
        = start.val := rfl
    have hiE : ({ start := start, «end» := i1 } : core.ops.range.Range Usize).«end».val
        = i1.val := rfl
    have hblkv : start.val + 2 * lenv ≤ 256 := by nlinarith
    apply WP.spec_bind (ntt_inner_spec (st := start.val) (lenv := lenv)
      { start := start, «end» := i1 } a len zeta (zetaP (nb + b0)) B hlen hlpos
      (by omega) (by omega) (by omega) hblkv hzeta hzlo hzhi hB0 hBhi
      (fun c hc1 hc2 => hBu c (by omega) (by omega))
      (fun c hc1 hc2 => hBu c (by omega) (by omega))
      hBg)
    intro a1 ha1
    obtain ⟨hA1, hU1, hU2, hU3, hBd1⟩ := ha1
    rw [hiS] at hA1 hU1 hU2
    -- advance to the next block
    let* ⟨ i2, hi2 ⟩ ←
      Std.Usize.mul_spec (show (2#usize).val * len.val ≤ Usize.max from by scalar_tac)
    let* ⟨ start1, hs1 ⟩ ←
      Std.Usize.add_spec (show start.val + i2.val ≤ Usize.max from by scalar_tac)
    have hi2v : i2.val = 2 * lenv := by rw [hi2, hlen]
    have hs1v : start1.val = (b0 + 1) * (2 * lenv) := by rw [hs1, hi2v, hstart]; ring
    apply WP.spec_mono (ntt_mid_spec (nb := nb) (lenv := lenv) (b0 := b0 + 1)
      a1 k1 len start1 B hlen hlpos hnb (by omega) hs1v (by omega) hB0 hBhi
      (fun c hc1 hc2 => by rw [hU3 c (by omega)]; exact hBu c (by omega) hc2)
      hBd1)
    rintro rk ⟨hR1, hR2, hR3, hR4⟩
    refine ⟨?_, ?_, hR3, hR4⟩
    · intro b hb1 hb2 r' hr'
      rcases eq_or_lt_of_le hb1 with hbe | hbgt
      · -- this block: `rk` agrees with `a1` here, and `a1` is what the butterfly wrote
        subst hbe
        have hx1 : aP rk.1 (b0 * (2 * lenv) + r') = aP a1 (b0 * (2 * lenv) + r') :=
          aP_congr (hR2 _ (by omega))
        have hx2 : aP rk.1 (b0 * (2 * lenv) + lenv + r') = aP a1 (b0 * (2 * lenv) + lenv + r') :=
          aP_congr (hR2 _ (by omega))
        have hA := hA1 (start.val + r') (by omega) (by omega)
        rw [show start.val + r' + lenv = b0 * (2 * lenv) + lenv + r' by omega, hstart] at hA
        rw [hx1, hx2]
        exact hA
      · -- a later block: `a1` still agrees with `a` there
        have h := hR1 b (by omega) hb2 r' hr'
        rw [aP_congr (hU3 (b * (2 * lenv) + r') (by nlinarith)),
          aP_congr (hU3 (b * (2 * lenv) + lenv + r') (by nlinarith))] at h
        exact h
    · intro c hc
      rw [hR2 c (by omega), hU1 c (by omega)]
  · -- done: `b0 = nb`
    have hgev : 256 ≤ start.val := by rw [← hRD]; scalar_tac
    have hb0eq : b0 = nb := by nlinarith
    rw [if_neg hlt]
    simp only [WP.spec_ok]
    refine ⟨?_, ?_, hBg, by omega⟩
    · intro b hb1 hb2; omega
    · intro c _; trivial
  termination_by 256 - start.val
  decreasing_by scalar_decr_tac

/-! ## The outer loop: all eight levels

`ntt_loop0 a k len` halves `len` until it reaches zero, running one full level per iteration.
Writing `len = 2^d`, the level has `nb = 2^(7-d)` blocks, so the invariant carried across
iterations is `State (2^(7-d)) (2·2^d) 1 f`, and each iteration is one `State_ct` step.  Every
level adds at most `p` to the coefficient magnitude, which is where the `(d+1)·p` in the bound
comes from. -/

/-- `ntt_loop0` with `len = 0` does nothing: this is how the level loop stops. -/
theorem ntt_loop0_zero (a : Array I32 256#usize) (k len : Usize) (hlen : len.val = 0) :
    arithmetic.ntt.ntt_loop0 a k len ⦃ (r : Array I32 256#usize) => r = a ⦄ := by
  unfold arithmetic.ntt.ntt_loop0
  rw [if_neg (by scalar_tac)]
  simp only [WP.spec_ok]

theorem ntt_outer_spec : ∀ (d : ℕ) (a : Array I32 256#usize) (k len : Usize) (f : ℕ → Zp) (B : ℤ),
    d ≤ 7 →
    len.val = 2 ^ d →
    k.val + 1 = 2 ^ (7 - d) →
    State (2 ^ (7 - d)) (2 * 2 ^ d) 1 f (aP a) →
    0 ≤ B → B + ((d : ℤ) + 1) * pNtt ≤ 2147483647 →
    (∀ c, c < 256 → |aZ a c| ≤ B) →
    arithmetic.ntt.ntt_loop0 a k len
      ⦃ (r : Array I32 256#usize) =>
          State 256 1 1 f (aP r) ∧ (∀ c, c < 256 → |aZ r c| ≤ B + ((d : ℤ) + 1) * pNtt) ⦄ := by
  intro d
  induction d with
  | zero =>
    intro a k len f B _ hlen hk hst hB0 hBhi hBd
    have hp0 : (0:ℤ) ≤ pNtt := by unfold pNtt; norm_num
    have hlen1 : len.val = 1 := by simpa using hlen
    have hst' : State 128 (2 * 1) 1 f (aP a) := by simpa using hst
    unfold arithmetic.ntt.ntt_loop0
    rw [if_pos (by scalar_tac)]
    -- the last level: 128 blocks of size 2
    apply WP.spec_bind (ntt_mid_spec (nb := 128) (lenv := 1) (b0 := 0) a k len 0#usize B
      hlen1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by simpa using hk)
      hB0 (by push_cast at hBhi; linarith)
      (fun c _ hc2 => hBd c hc2) (fun c hc => le_trans (hBd c hc) (by linarith)))
    rintro ⟨a1, k1⟩ ⟨hA1, _, hBd1, hk1⟩
    simp only at hA1 hBd1 hk1
    -- one `State_ct` step takes `State 128 2` to `State 256 1`
    have hst1 : State 256 1 1 f (aP a1) :=
      State_ct (nb := 128) (m' := 1) (c := 1) (f := f) (a := aP a) (a' := aP a1)
        (by norm_num) (by norm_num) hst'
        (fun b hb r' hr' => hA1 b (Nat.zero_le _) hb r' hr')
    -- the loop exits: `len / 2 = 0`
    let* ⟨ len1, len1_post ⟩ ← Std.Usize.div_spec
    have Hz := ntt_loop0_zero a1 k1 len1 (by rw [len1_post, hlen1])
    apply WP.spec_mono Hz
    rintro r rfl
    refine ⟨hst1, fun c hc => ?_⟩
    push_cast
    linarith [hBd1 c hc]
  | succ d ih =>
    intro a k len f B hd hlen hk hst hB0 hBhi hBd
    have hp0 : (0:ℤ) ≤ pNtt := by unfold pNtt; norm_num
    have hdz : (0:ℤ) ≤ (d : ℤ) := Int.natCast_nonneg d
    have hd6 : d ≤ 6 := by omega
    have hsub : 7 - (d + 1) = 6 - d := by omega
    have hsub2 : 7 - d = 6 - d + 1 := by omega
    have hnbeq : 2 ^ (7 - d) = 2 * 2 ^ (6 - d) := by rw [hsub2]; ring
    have hnb256 : 2 ^ (6 - d) * (2 * 2 ^ (d + 1)) = 256 := by
      rw [show 2 ^ (6 - d) * (2 * 2 ^ (d + 1)) = 2 ^ ((6 - d) + (d + 2)) by ring,
        show (6 - d) + (d + 2) = 8 by omega]
      norm_num
    have hlpos : 0 < 2 ^ (d + 1) := Nat.one_le_two_pow
    have hnble : 2 * 2 ^ (6 - d) ≤ 256 := by
      rw [← hnbeq]
      have : (2:ℕ) ^ (7 - d) ≤ 2 ^ 7 := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    have hst' : State (2 ^ (6 - d)) (2 * 2 ^ (d + 1)) 1 f (aP a) := by rw [hsub] at hst; exact hst
    unfold arithmetic.ntt.ntt_loop0
    rw [if_pos (by scalar_tac)]
    -- run this level
    apply WP.spec_bind (ntt_mid_spec (nb := 2 ^ (6 - d)) (lenv := 2 ^ (d + 1)) (b0 := 0)
      a k len 0#usize B hlen hlpos hnb256 (Nat.zero_le _) (by simp)
      (by rw [hk, hsub]; omega)
      hB0 (by push_cast at hBhi ⊢; nlinarith)
      (fun c _ hc2 => hBd c hc2) (fun c hc => le_trans (hBd c hc) (by linarith)))
    rintro ⟨a1, k1⟩ ⟨hA1, _, hBd1, hk1⟩
    simp only at hA1 hBd1 hk1
    -- one `State_ct` step: `State nb (2·2^(d+1))` becomes `State (2·nb) (2^(d+1))`
    have hstep : State (2 * 2 ^ (6 - d)) (2 ^ (d + 1)) 1 f (aP a1) :=
      State_ct (nb := 2 ^ (6 - d)) (m' := 2 ^ (d + 1)) (c := 1) (f := f)
        (a := aP a) (a' := aP a1) Nat.one_le_two_pow hnble hst'
        (fun b hb r' hr' => hA1 b (Nat.zero_le _) hb r' hr')
    have hst1 : State (2 ^ (7 - d)) (2 * 2 ^ d) 1 f (aP a1) := by
      rw [hnbeq, show 2 * 2 ^ d = 2 ^ (d + 1) by ring]
      exact hstep
    -- halve `len` and recurse
    let* ⟨ len1, len1_post ⟩ ← Std.Usize.div_spec
    have hlen1 : len1.val = 2 ^ d := by
      rw [len1_post, hlen, pow_succ]
      omega
    have hpos1 : 1 ≤ 2 ^ (6 - d) := Nat.one_le_two_pow
    have IH := ih a1 k1 len1 f (B + pNtt) (by omega) hlen1
      (by rw [hk1, hnbeq]; omega) hst1 (by linarith) (by push_cast at hBhi ⊢; nlinarith) hBd1
    apply WP.spec_mono IH
    rintro r ⟨hstr, hbr⟩
    refine ⟨hstr, fun c hc => ?_⟩
    have := hbr c hc
    push_cast at this ⊢
    linarith

end Kopis.Properties
