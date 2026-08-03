/-
  # Kopis/Avx2/Tables.lean — discharging the ψ-table hypotheses of phase F3.

  `Kopis/Avx2/NttGrowth.lean` proves the AVX2 forward transform stays inside an `i16` lane
  *given* that every ψ it uses is centred (`|ψ| ≤ q/2`) and paired with its Montgomery companion.
  This file supplies those two facts, and neither needs the 240-odd derived table entries to be
  computed:

  * **Centredness** is a property of `ZETAS_Q1` and `ZETAS_Q2` alone — two 256-entry literal
    arrays, checked by `decide` — because every derived table is built by *copying* (and
    sometimes negating) their entries.  `|−x| = |x|`, so nothing is lost.
  * **The Montgomery pairing** needs one numeric fact per prime, `q⁻¹·q ≡ 1 (mod 2¹⁶)`, and the
    structural fact that every `zq` entry is `wrapping_mul` of the matching `z` entry by `q⁻¹`.
    Then `zq·q ≡ z·q⁻¹·q ≡ z`, whatever `z` happens to be.

  So the tables are pinned down by two `decide`s over literals and two loop specifications —
  rather than by evaluating `zetas_qinv` and `lane_tbl`, which are `partial_fixpoint` loops and
  so not reducible by the kernel at all.
-/
import Kopis.Avx2.NttGrowth

open Aeneas Aeneas.Std Result
open RustKopisAvx2

namespace Kopis.Avx2

set_option maxHeartbeats 1000000
set_option maxRecDepth 20000

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

/-! ## The two ζ tables are centred

The only place the 512 literal entries are touched. -/

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

/-! ## The Montgomery constants really are inverses mod `2¹⁶` -/

unseal backend.crt.Q1_INV backend.crt.Q1 in
theorem q1_inv_unit : (2 ^ 16 : ℤ) ∣ (backend.crt.Q1_INV.val * backend.crt.Q1.val - 1) := by
  decide

unseal backend.crt.Q2_INV backend.crt.Q2 in
theorem q2_inv_unit : (2 ^ 16 : ℤ) ∣ (backend.crt.Q2_INV.val * backend.crt.Q2.val - 1) := by
  decide

unseal backend.crt.Q1 in
theorem q1_val : backend.crt.Q1.val = 7681 := by decide

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
         rw [hav, Std.Array.set_val_eq, getElem!_list_set _ _ _ _ (by
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

/-- **The ζ hypothesis of `ntt_block_bnd_q1`, discharged.** -/
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

/-! ## `lane_tbl` only copies ζ entries

Every entry it writes into `z` is some `zetas[idx]`, and the matching `zq` entry is that times
`q⁻¹`.  The initial `0` already satisfies both, so the invariant is uniform over the whole table
rather than split into written and unwritten halves.  All four forward tables use `neg = false`,
so no negation arises. -/

private theorem hcast_usize_isize_val (x : Usize) (h : x.val ≤ IScalar.max IScalarTy.Isize) :
    (UScalar.hcast IScalarTy.Isize x).val = x.val := by
  obtain ⟨y, hy, hyv⟩ := WP.spec_imp_exists (UScalar.hcast_inBounds_spec IScalarTy.Isize x h)
  have he : (ok (UScalar.hcast IScalarTy.Isize x) : Result Isize) = ok y := by
    simpa [lift] using hy
  injection he with he'
  rw [he']
  exact hyv

private theorem hcast_isize_usize_val (x : Isize)
    (h : 0 ≤ x.val ∧ x.val ≤ (UScalar.max UScalarTy.Usize : ℤ)) :
    ((IScalar.hcast UScalarTy.Usize x).val : ℤ) = x.val := by
  obtain ⟨y, hy, hyv⟩ := WP.spec_imp_exists (IScalar.hcast_inBounds_spec UScalarTy.Usize x h)
  have he : (ok (IScalar.hcast UScalarTy.Usize x) : Result Usize) = ok y := by
    simpa [lift] using hy
  injection he with he'
  rw [he']
  exact hyv

/-- A `lane_tbl` table under construction: centred, and Montgomery-paired entrywise. -/
def TblOk (Zb : ℤ) (qinv : I16) {N : Usize} (z zq : Array I16 N) : Prop :=
  ∀ i < N.val, |(z.val[i]!).val| ≤ Zb ∧
    (zq.val[i]!).val = ((z.val[i]!).val * qinv.val).bmod (2 ^ 16)

/-- Which ζ each lane holds.  Phase F3 needs only `TblOk`; phase F4 must *name* the twiddle the
code applies.  It rides along on the same walk: the entries are copied rather than computed, so
the index arithmetic is shared and deriving it a second time is wasted work. -/
def TblAt (zetas : Array I16 256#usize) (base h_stride m_stride : Isize) (neg : Bool) {N : Usize}
    (z : Array I16 N) (upto : ℕ) : Prop :=
  ∀ h < upto, ∀ m < 16, 16 * h + m < N.val →
    (z.val[16 * h + m]!).val
      = (if neg then -1 else 1) *
        (zetas.val[(base.val + h * h_stride.val + m * m_stride.val).toNat]!).val

set_option maxRecDepth 100000 in
theorem lane_tbl_loop0_loop0_spec {N : Usize} (zetas : Array I16 256#usize) (qinv : I16)
    (base h_stride m_stride : Isize) (neg : Bool) (z zq : Array I16 N) (h m : Usize) (Zb : ℤ)
    (hzet : ∀ x ∈ zetas.val, |x.val| ≤ Zb) (hZb : Zb ≤ 32767)
    (hbase : 0 ≤ base.val ∧ base.val ≤ 255)
    (hhs : h_stride.val = 0 ∨ h_stride.val = 1 ∨ h_stride.val = -1)
    (hms : m_stride.val = 1 ∨ m_stride.val = 2 ∨ m_stride.val = 4 ∨ m_stride.val = 8 ∨
      m_stride.val = -1 ∨ m_stride.val = -2 ∨ m_stride.val = -4 ∨ m_stride.val = -8)
    (hh : h.val ≤ 8) (hm : m.val ≤ 16)
    (hidx : ∀ mm : ℕ, mm < 16 →
      0 ≤ base.val + h.val * h_stride.val + mm * m_stride.val ∧
      base.val + h.val * h_stride.val + mm * m_stride.val < 256)
    (hN : 16 * h.val + 16 ≤ N.val)
    (hinv : TblOk Zb qinv z zq)
    (hpre : ∀ mm < m.val, (z.val[16 * h.val + mm]!).val
      = (if neg then -1 else 1) *
        (zetas.val[(base.val + h.val * h_stride.val + mm * m_stride.val).toNat]!).val)
    (hold : TblAt zetas base h_stride m_stride neg z h.val) :
    backend.avx2.ntt.lane_tbl_loop0_loop0 zetas qinv base h_stride m_stride neg z zq h m
      ⦃ (r : (Array I16 N) × (Array I16 N)) =>
          TblOk Zb qinv r.1 r.2 ∧ TblAt zetas base h_stride m_stride neg r.1 (h.val + 1) ⦄ := by
  unfold backend.avx2.ntt.lane_tbl_loop0_loop0
  by_cases hlt : m.val < 16
  · rw [if_pos (by scalar_tac)]
    have hImin : (Isize.min : ℤ) ≤ -2147483648 := by scalar_tac
    have hImax : (2147483647 : ℤ) ≤ Isize.max := by scalar_tac
    have hImax' : (2147483647 : ℤ) ≤ IScalar.max IScalarTy.Isize := by scalar_tac
    have hUmax : (256 : ℤ) ≤ (UScalar.max UScalarTy.Usize : ℤ) := by scalar_tac
    have hzlen : zetas.length = 256 := by simp [Array.length]
    step*
    all_goals (try (
      have hiv : i.val = h.val := by rw [i_post]; exact hcast_usize_isize_val h (by omega)
      rcases hhs with hs | hs | hs <;> rcases hms with ms | ms | ms | ms | ms | ms | ms | ms <;>
        (obtain ⟨hI0, hI1⟩ := hidx m.val hlt
         simp only [hs, ms, hiv, mul_zero, mul_one] at *
         omega)))
    all_goals (try (
      have hiv : i.val = h.val := by rw [i_post]; exact hcast_usize_isize_val h (by omega)
      have hi3v : i3.val = m.val := by rw [i3_post]; exact hcast_usize_isize_val m (by omega)
      rcases hhs with hs | hs | hs <;> rcases hms with ms | ms | ms | ms | ms | ms | ms | ms <;>
        (obtain ⟨hI0, hI1⟩ := hidx m.val hlt
         simp only [hs, ms, hiv, hi3v, mul_zero, mul_one] at *
         omega)))
    · have hiv : i.val = h.val := by rw [i_post]; exact hcast_usize_isize_val h (by omega)
      have hi3v : i3.val = m.val := by rw [i3_post]; exact hcast_usize_isize_val m (by omega)
      have hi5v : ((i5 : Usize).val : ℤ) = idx.val := by
        rw [i5_post]
        refine hcast_isize_usize_val idx ⟨?_, ?_⟩ <;>
          (rcases hhs with hs | hs | hs <;>
            rcases hms with ms | ms | ms | ms | ms | ms | ms | ms <;>
            (obtain ⟨hI0, hI1⟩ := hidx m.val hlt
             try simp only [hs, ms, hiv, hi3v, mul_zero, mul_one] at *
             omega))
      have hbound : ((i5 : Usize).val : ℤ) < 256 := by
        obtain ⟨hI0, hI1⟩ := hidx m.val hlt
        rw [hi5v, idx_post, i2_post, i4_post, i1_post, hiv, hi3v]
        linarith [hI1]
      rw [hzlen]
      omega
    -- the write: `z[16h+m] := ±zetas[idx]`, `zq[16h+m] := that · q⁻¹`.  The inverse tables set
    -- `neg`, and the negation is the checked one, so it has to be shown not to trap: the table is
    -- centred well inside `i16`, so `value` is never `I16.min`.
    have hvz0 : |value.val| ≤ Zb := by rw [value_post]; exact hzet _ (List.getElem_mem _)
    obtain ⟨value1, hval1, hval1v⟩ :
        ∃ v1 : I16, (if neg then (-. value : Result I16) else ok value) = ok v1 ∧
          v1.val = (if neg then -1 else 1) * value.val := by
      cases neg
      · exact ⟨value, by simp, by simp⟩
      · have hne : value.val ≠ Std.IScalar.min Std.IScalarTy.I16 := by
          have hmin : (Std.IScalar.min Std.IScalarTy.I16 : ℤ) = -32768 := by scalar_tac
          rw [abs_le] at hvz0
          omega
        obtain ⟨r, hr, hrv⟩ := WP.spec_imp_exists (Std.HNeg.hNeg.step value hne)
        exact ⟨r, by simpa using hr, by simp [hrv]⟩
    rw [hval1, bind_tc_ok]
    have hvz : |value1.val| ≤ Zb := by
      have habs : |(if neg then (-1 : ℤ) else 1) * value.val| = |value.val| := by
        cases neg <;> simp
      rw [hval1v, habs]
      exact hvz0
    step*
    all_goals (
      have hidxlt : i7.val < N.val := by omega
      have hi9lt : i9.val < N.val := by omega
      -- naming the ζ this iteration copies
      have hivW : i.val = h.val := by rw [i_post]; exact hcast_usize_isize_val h (by omega)
      have hi3vW : i3.val = m.val := by rw [i3_post]; exact hcast_usize_isize_val m (by omega)
      have hidxZ : idx.val = base.val + h.val * h_stride.val + m.val * m_stride.val := by
        rw [idx_post, i2_post, i4_post, i1_post, hivW, hi3vW]
      have hi5vW : ((i5 : Usize).val : ℤ) = idx.val := by
        rw [i5_post]
        refine hcast_isize_usize_val idx ⟨?_, ?_⟩
        · rw [hidxZ]
          exact (hidx m.val hlt).1
        · rw [hidxZ]
          have hI := (hidx m.val hlt).2
          omega
      have hidxv : (i5 : Usize).val
          = (base.val + h.val * h_stride.val + m.val * m_stride.val).toNat := by
        rw [← hidxZ]; omega
      have hlt5 : (i5 : Usize).val < zetas.val.length := by
        have hI := (hidx m.val hlt).2
        have h256 : zetas.val.length = 256 := by simp
        rw [h256, hidxv]
        omega
      have hvalv : value1.val
          = (if neg then -1 else 1) * (zetas.val[(i5 : Usize).val]!).val := by
        rw [hval1v, getElem!_pos zetas.val _ hlt5, value_post]
      have hbnd : ∀ mm : ℕ, mm < 16 → 16 * h.val + mm < N.val := by intro mm hmm; omega
      have hstore : ∀ w, w < N.val →
          (a.val[w]!).val = if w = i7.val then value1.val else (z.val[w]!).val := by
        intro w hw
        rw [a_post, Std.Array.set_val_eq,
          getElem!_list_set _ _ _ _ (by rw [z.property]; simpa using hidxlt)]
        split <;> rfl
      all_goals first
        | (intro mm hmm
           rw [hstore (16 * h.val + mm) (hbnd mm (by omega))]
           by_cases hme : mm = m.val
           · rw [if_pos (by omega), hme, hvalv, hidxv]
           · rw [if_neg (by omega)]
             exact hpre mm (by omega))
        | (intro h' hh' mm hmm hN'
           try rw [← a_post]
           rw [hstore (16 * h' + mm) (by omega), if_neg (by omega)]
           exact hold h' (by omega) mm hmm (by omega))
        | omega
        | (intro w hw
           try rw [a_post, a1_post]
           rw [Std.Array.set_val_eq, Std.Array.set_val_eq,
             getElem!_list_set _ _ _ _ (by rw [z.property]; simpa using hidxlt),
             getElem!_list_set _ _ _ _ (by rw [zq.property]; simpa using hi9lt)]
           by_cases hwe : w = i7.val
           · rw [if_pos hwe, if_pos (show w = i9.val by omega), i8_post,
               core.num.I16.wrapping_mul, IScalar.wrapping_mul_val_eq]
             exact ⟨hvz, rfl⟩
           · rw [if_neg hwe, if_neg (show ¬ w = i9.val by omega)]
             exact hinv w hw))
  · rw [if_neg (by scalar_tac)]
    simp only [WP.spec_ok]
    refine ⟨hinv, ?_⟩
    intro h' hh' mm hmm hN'
    rcases (show h' < h.val ∨ h' = h.val from by omega) with hlt' | rfl
    · exact hold h' hlt' mm hmm hN'
    · exact hpre mm (by omega)
termination_by 16 - m.val
decreasing_by scalar_decr_tac

set_option maxRecDepth 100000 in
theorem lane_tbl_loop0_spec {N : Usize} (zetas : Array I16 256#usize) (qinv : I16)
    (base h_stride m_stride : Isize) (neg : Bool) (z zq : Array I16 N) (h : Usize) (Zb : ℤ)
    (hzet : ∀ x ∈ zetas.val, |x.val| ≤ Zb) (hZb : Zb ≤ 32767)
    (hbase : 0 ≤ base.val ∧ base.val ≤ 255)
    (hhs : h_stride.val = 0 ∨ h_stride.val = 1 ∨ h_stride.val = -1)
    (hms : m_stride.val = 1 ∨ m_stride.val = 2 ∨ m_stride.val = 4 ∨ m_stride.val = 8 ∨
      m_stride.val = -1 ∨ m_stride.val = -2 ∨ m_stride.val = -4 ∨ m_stride.val = -8)
    (hN : N.val ≤ 128) (hNdvd : 16 ∣ N.val) (hh : h.val ≤ 8)
    (hidx : ∀ hh mm : ℕ, hh < 8 → mm < 16 →
      0 ≤ base.val + hh * h_stride.val + mm * m_stride.val ∧
      base.val + hh * h_stride.val + mm * m_stride.val < 256)
    (hinv : TblOk Zb qinv z zq) (hold : TblAt zetas base h_stride m_stride neg z h.val) :
    backend.avx2.ntt.lane_tbl_loop0 zetas qinv base h_stride m_stride neg z zq h
      ⦃ (r : (Array I16 N) × (Array I16 N)) =>
          TblOk Zb qinv r.1 r.2 ∧ TblAt zetas base h_stride m_stride neg r.1 8 ⦄ := by
  unfold backend.avx2.ntt.lane_tbl_loop0
  step*
  · apply WP.spec_bind (lane_tbl_loop0_loop0_spec zetas qinv base h_stride m_stride neg z zq h
      0#usize Zb hzet hZb hbase hhs hms (by scalar_tac) (by simp)
      (fun mm hmm => hidx h.val mm (by scalar_tac) hmm) (by scalar_tac) hinv
      (by intro mm hmm; simp at hmm) hold)
    rintro ⟨z1, zq1⟩ hz1
    obtain ⟨hz1a, hz1b⟩ := hz1
    simp only at hz1a hz1b
    step*
  · refine ⟨hinv, fun h' hh' mm hmm hN' => ?_⟩
    rcases (show h' < h.val ∨ h.val ≤ h' from by omega) with hlt' | hge'
    · exact hold h' hlt' mm hmm hN'
    · exact absurd hN' (by scalar_tac)
termination_by N.val - 16 * h.val
decreasing_by scalar_decr_tac

theorem lane_tbl_spec (N : Usize) (zetas : Array I16 256#usize) (qinv : I16)
    (base h_stride m_stride : Isize) (neg : Bool) (Zb : ℤ) (hZb : 0 ≤ Zb) (hZb' : Zb ≤ 32767)
    (hzet : ∀ x ∈ zetas.val, |x.val| ≤ Zb)
    (hbase : 0 ≤ base.val ∧ base.val ≤ 255)
    (hhs : h_stride.val = 0 ∨ h_stride.val = 1 ∨ h_stride.val = -1)
    (hms : m_stride.val = 1 ∨ m_stride.val = 2 ∨ m_stride.val = 4 ∨ m_stride.val = 8 ∨
      m_stride.val = -1 ∨ m_stride.val = -2 ∨ m_stride.val = -4 ∨ m_stride.val = -8)
    (hN : N.val ≤ 128) (hNdvd : 16 ∣ N.val)
    (hidx : ∀ hh mm : ℕ, hh < 8 → mm < 16 →
      0 ≤ base.val + hh * h_stride.val + mm * m_stride.val ∧
      base.val + hh * h_stride.val + mm * m_stride.val < 256) :
    ∃ t, backend.avx2.ntt.lane_tbl N zetas qinv base h_stride m_stride neg = ok t ∧
      TblOk Zb qinv t.z t.zq ∧ TblAt zetas base h_stride m_stride neg t.z 8 := by
  apply WP.spec_imp_exists
  unfold backend.avx2.ntt.lane_tbl
  apply WP.spec_bind (lane_tbl_loop0_spec zetas qinv base h_stride m_stride neg _ _ 0#usize Zb
    hzet hZb' hbase hhs hms hN hNdvd (by simp) hidx ?_
    (by intro h' hh' mm hmm hN'; simp at hh'))
  · rintro ⟨z1, zq1⟩ hz1
    obtain ⟨hz1a, hz1b⟩ := hz1
    simp only at hz1a hz1b
    show (ok ({ z := z1, zq := zq1 } : backend.avx2.ntt.Tbl N))
      ⦃ (t : backend.avx2.ntt.Tbl N) =>
          TblOk Zb qinv t.z t.zq ∧ TblAt zetas base h_stride m_stride neg t.z 8 ⦄
    simp only [WP.spec_ok]
    exact ⟨hz1a, hz1b⟩
  · intro w hw
    refine ⟨?_, ?_⟩ <;>
      rw [Array.repeat_val, getElem!_pos _ w (by rw [List.length_replicate]; simpa using hw),
        List.getElem_replicate] <;>
      simp [hZb]

/-! ## From a table to a usable ψ pair -/

/-- The Montgomery pairing, once: if `zq ≡ z·q⁻¹` and `q⁻¹·q ≡ 1`, then `zq·q ≡ z`. -/
theorem mont_pair {zv zqv Q : ℤ} {qinv : I16}
    (h : zqv = (zv * qinv.val).bmod (2 ^ 16))
    (hunit : (2 ^ 16 : ℤ) ∣ (qinv.val * Q - 1)) :
    (2 ^ 16 : ℤ) ∣ (zqv * Q - zv) := by
  obtain ⟨c, hc⟩ : (2 ^ 16 : ℤ) ∣ (zqv - zv * qinv.val) := by
    rw [h]; exact Int.ModEq.dvd (Int.bmod_emod (x := zv * qinv.val) (m := 2 ^ 16)).symm
  obtain ⟨d, hd⟩ := hunit
  refine ⟨zv * d + c * Q, ?_⟩
  have e1 : zqv = zv * qinv.val + 2 ^ 16 * c := by omega
  have e2 : qinv.val * Q = 1 + 2 ^ 16 * d := by omega
  calc zqv * Q - zv
      = (zv * qinv.val + 2 ^ 16 * c) * Q - zv := by rw [e1]
    _ = zv * (qinv.val * Q) + 2 ^ 16 * (c * Q) - zv := by ring
    _ = zv * (1 + 2 ^ 16 * d) + 2 ^ 16 * (c * Q) - zv := by rw [e2]
    _ = 2 ^ 16 * (zv * d + c * Q) := by ring

/-- **`ld_tbl` hands back a usable ψ pair.** -/
theorem ld_tbl_psiOk {N : Usize} (t : backend.avx2.ntt.Tbl N) (hh : Usize) (Zb Q : ℤ) (qinv : I16)
    (zetas : Array I16 256#usize) (base h_stride m_stride : Isize) (neg : Bool)
    (hTbl : TblOk Zb qinv t.z t.zq) (hAt : TblAt zetas base h_stride m_stride neg t.z 8)
    (hhh : hh.val < 8) (hunit : (2 ^ 16 : ℤ) ∣ (qinv.val * Q - 1))
    (hlt : 16 * (hh.val + 1) ≤ N.val) :
    ∃ z zq, backend.avx2.ntt.ld_tbl t hh = ok (z, zq) ∧ PsiOk z zq Q Zb ∧
      ∀ k < 16, (lane16 z k).toInt
        = (if neg then -1 else 1) *
          (zetas.val[(base.val + hh.val * h_stride.val + k * m_stride.val).toNat]!).val := by
  obtain ⟨v, hv, hvl⟩ := load_i16_spec t.z hh hlt
  obtain ⟨v1, hv1, hv1l⟩ := load_i16_spec t.zq hh hlt
  refine ⟨v, v1, ?_, ⟨?_, ?_⟩, ?_⟩
  · unfold backend.avx2.ntt.ld_tbl
    rw [hv, bind_tc_ok, hv1, bind_tc_ok]
  · intro k hk
    rw [show (lane16 v k).toInt = (t.z.val[16 * hh.val + k]!).val from by rw [hvl k hk]; rfl]
    exact (hTbl (16 * hh.val + k) (by omega)).1
  · intro k hk
    rw [show (lane16 v1 k).toInt = (t.zq.val[16 * hh.val + k]!).val from by rw [hv1l k hk]; rfl,
      show (lane16 v k).toInt = (t.z.val[16 * hh.val + k]!).val from by rw [hvl k hk]; rfl]
    exact mont_pair (hTbl (16 * hh.val + k) (by omega)).2 hunit
  · intro k hk
    rw [show (lane16 v k).toInt = (t.z.val[16 * hh.val + k]!).val from by rw [hvl k hk]; rfl]
    exact hAt hh.val hhh k hk (by omega)

/-- `ld_tbl_psiOk` with `neg` known to be `false`, so the sign factor disappears.  The four
forward tables are built this way; only the inverse ones set `neg`. -/
theorem ld_tbl_psiOk_pos {N : Usize} (t : backend.avx2.ntt.Tbl N) (hh : Usize) (Zb Q : ℤ)
    (qinv : I16) (zetas : Array I16 256#usize) (base h_stride m_stride : Isize)
    (hTbl : TblOk Zb qinv t.z t.zq) (hAt : TblAt zetas base h_stride m_stride false t.z 8)
    (hhh : hh.val < 8) (hunit : (2 ^ 16 : ℤ) ∣ (qinv.val * Q - 1))
    (hlt : 16 * (hh.val + 1) ≤ N.val) :
    ∃ z zq, backend.avx2.ntt.ld_tbl t hh = ok (z, zq) ∧ PsiOk z zq Q Zb ∧
      ∀ k < 16, (lane16 z k).toInt
        = (zetas.val[(base.val + hh.val * h_stride.val + k * m_stride.val).toNat]!).val := by
  obtain ⟨z, zq, h1, h2, h3⟩ :=
    ld_tbl_psiOk t hh Zb Q qinv zetas base h_stride m_stride false hTbl hAt hhh hunit hlt
  exact ⟨z, zq, h1, h2, fun k hk => by simpa using h3 k hk⟩

/-! ## The four forward tables, for each prime

Each is `lane_tbl` at concrete strides; the ζ index it reads stays inside `[0, 256)`, which is
what `hidx` records. -/

/-- The `FWD8` table for `q1` is centred and Montgomery-paired. -/
theorem fwd8_q1_ok : ∀ h : Usize, h.val < 1 → ∃ z zq,
    (do let t ← backend.avx2.ntt.FWD8_Q1; backend.avx2.ntt.ld_tbl t h) = ok (z, zq) ∧
      PsiOk z zq 7681 3840 ∧
      (∀ k < 16, (lane16 z k).toInt
        = (backend.crt.ZETAS_Q1.val[((16#isize).val + h.val * (0#isize).val
            + k * (1#isize).val).toNat]!).val) := by
  intro h hh
  have hb : (16#isize).val = 16 := by scalar_tac
  have hhs : (0#isize).val = 0 := by scalar_tac
  have hms : (1#isize).val = 1 := by scalar_tac
  have hNv : ((16#usize) : Usize).val = 16 := by scalar_tac
  obtain ⟨t, ht, hTbl, hAt⟩ := lane_tbl_spec 16#usize backend.crt.ZETAS_Q1 backend.crt.Q1_INV
    16#isize 0#isize 1#isize false 3840 (by norm_num) (by norm_num) zetas_q1_centred
    ⟨by omega, by omega⟩ (Or.inl (by scalar_tac)) (Or.inl (by scalar_tac))
    (by scalar_tac) (by omega)
    (by intro hh' mm h1 h2; rw [hb, hhs, hms]; omega)
  rw [show backend.avx2.ntt.FWD8_Q1 = ok t from by
    unfold backend.avx2.ntt.FWD8_Q1; exact ht, bind_tc_ok]
  exact ld_tbl_psiOk_pos t h 3840 7681 backend.crt.Q1_INV _ _ _ _ hTbl hAt (by omega)
    (by rw [← q1_val]; exact q1_inv_unit)
    (by omega)

/-- The `FWD4` table for `q1` is centred and Montgomery-paired. -/
theorem fwd4_q1_ok : ∀ h : Usize, h.val < 2 → ∃ z zq,
    (do let t ← backend.avx2.ntt.FWD4_Q1; backend.avx2.ntt.ld_tbl t h) = ok (z, zq) ∧
      PsiOk z zq 7681 3840 ∧
      (∀ k < 16, (lane16 z k).toInt
        = (backend.crt.ZETAS_Q1.val[((32#isize).val + h.val * (1#isize).val
            + k * (2#isize).val).toNat]!).val) := by
  intro h hh
  have hb : (32#isize).val = 32 := by scalar_tac
  have hhs : (1#isize).val = 1 := by scalar_tac
  have hms : (2#isize).val = 2 := by scalar_tac
  have hNv : ((32#usize) : Usize).val = 32 := by scalar_tac
  obtain ⟨t, ht, hTbl, hAt⟩ := lane_tbl_spec 32#usize backend.crt.ZETAS_Q1 backend.crt.Q1_INV
    32#isize 1#isize 2#isize false 3840 (by norm_num) (by norm_num) zetas_q1_centred
    ⟨by omega, by omega⟩ (Or.inr (Or.inl (by scalar_tac))) (Or.inr (Or.inl (by scalar_tac)))
    (by scalar_tac) (by omega)
    (by intro hh' mm h1 h2; rw [hb, hhs, hms]; omega)
  rw [show backend.avx2.ntt.FWD4_Q1 = ok t from by
    unfold backend.avx2.ntt.FWD4_Q1; exact ht, bind_tc_ok]
  exact ld_tbl_psiOk_pos t h 3840 7681 backend.crt.Q1_INV _ _ _ _ hTbl hAt (by omega)
    (by rw [← q1_val]; exact q1_inv_unit)
    (by omega)

/-- The `FWD2` table for `q1` is centred and Montgomery-paired. -/
theorem fwd2_q1_ok : ∀ h : Usize, h.val < 4 → ∃ z zq,
    (do let t ← backend.avx2.ntt.FWD2_Q1; backend.avx2.ntt.ld_tbl t h) = ok (z, zq) ∧
      PsiOk z zq 7681 3840 ∧
      (∀ k < 16, (lane16 z k).toInt
        = (backend.crt.ZETAS_Q1.val[((64#isize).val + h.val * (1#isize).val
            + k * (4#isize).val).toNat]!).val) := by
  intro h hh
  have hb : (64#isize).val = 64 := by scalar_tac
  have hhs : (1#isize).val = 1 := by scalar_tac
  have hms : (4#isize).val = 4 := by scalar_tac
  have hNv : ((64#usize) : Usize).val = 64 := by scalar_tac
  obtain ⟨t, ht, hTbl, hAt⟩ := lane_tbl_spec 64#usize backend.crt.ZETAS_Q1 backend.crt.Q1_INV
    64#isize 1#isize 4#isize false 3840 (by norm_num) (by norm_num) zetas_q1_centred
    ⟨by omega, by omega⟩ (Or.inr (Or.inl (by scalar_tac))) (Or.inr (Or.inr (Or.inl (by scalar_tac))))
    (by scalar_tac) (by omega)
    (by intro hh' mm h1 h2; rw [hb, hhs, hms]; omega)
  rw [show backend.avx2.ntt.FWD2_Q1 = ok t from by
    unfold backend.avx2.ntt.FWD2_Q1; exact ht, bind_tc_ok]
  exact ld_tbl_psiOk_pos t h 3840 7681 backend.crt.Q1_INV _ _ _ _ hTbl hAt (by omega)
    (by rw [← q1_val]; exact q1_inv_unit)
    (by omega)

/-- The `FWD1` table for `q1` is centred and Montgomery-paired. -/
theorem fwd1_q1_ok : ∀ h : Usize, h.val < 8 → ∃ z zq,
    (do let t ← backend.avx2.ntt.FWD1_Q1; backend.avx2.ntt.ld_tbl t h) = ok (z, zq) ∧
      PsiOk z zq 7681 3840 ∧
      (∀ k < 16, (lane16 z k).toInt
        = (backend.crt.ZETAS_Q1.val[((128#isize).val + h.val * (1#isize).val
            + k * (8#isize).val).toNat]!).val) := by
  intro h hh
  have hb : (128#isize).val = 128 := by scalar_tac
  have hhs : (1#isize).val = 1 := by scalar_tac
  have hms : (8#isize).val = 8 := by scalar_tac
  have hNv : ((128#usize) : Usize).val = 128 := by scalar_tac
  obtain ⟨t, ht, hTbl, hAt⟩ := lane_tbl_spec 128#usize backend.crt.ZETAS_Q1 backend.crt.Q1_INV
    128#isize 1#isize 8#isize false 3840 (by norm_num) (by norm_num) zetas_q1_centred
    ⟨by omega, by omega⟩ (Or.inr (Or.inl (by scalar_tac))) (Or.inr (Or.inr (Or.inr (Or.inl (by scalar_tac)))))
    (by scalar_tac) (by omega)
    (by intro hh' mm h1 h2; rw [hb, hhs, hms]; omega)
  rw [show backend.avx2.ntt.FWD1_Q1 = ok t from by
    unfold backend.avx2.ntt.FWD1_Q1; exact ht, bind_tc_ok]
  exact ld_tbl_psiOk_pos t h 3840 7681 backend.crt.Q1_INV _ _ _ _ hTbl hAt (by omega)
    (by rw [← q1_val]; exact q1_inv_unit)
    (by omega)

/-- The `FWD8` table for `q2` is centred and Montgomery-paired. -/
theorem fwd8_q2_ok : ∀ h : Usize, h.val < 1 → ∃ z zq,
    (do let t ← backend.avx2.ntt.FWD8_Q2; backend.avx2.ntt.ld_tbl t h) = ok (z, zq) ∧
      PsiOk z zq 10753 5376 ∧
      (∀ k < 16, (lane16 z k).toInt
        = (backend.crt.ZETAS_Q2.val[((16#isize).val + h.val * (0#isize).val
            + k * (1#isize).val).toNat]!).val) := by
  intro h hh
  have hb : (16#isize).val = 16 := by scalar_tac
  have hhs : (0#isize).val = 0 := by scalar_tac
  have hms : (1#isize).val = 1 := by scalar_tac
  have hNv : ((16#usize) : Usize).val = 16 := by scalar_tac
  obtain ⟨t, ht, hTbl, hAt⟩ := lane_tbl_spec 16#usize backend.crt.ZETAS_Q2 backend.crt.Q2_INV
    16#isize 0#isize 1#isize false 5376 (by norm_num) (by norm_num) zetas_q2_centred
    ⟨by omega, by omega⟩ (Or.inl (by scalar_tac)) (Or.inl (by scalar_tac))
    (by scalar_tac) (by omega)
    (by intro hh' mm h1 h2; rw [hb, hhs, hms]; omega)
  rw [show backend.avx2.ntt.FWD8_Q2 = ok t from by
    unfold backend.avx2.ntt.FWD8_Q2; exact ht, bind_tc_ok]
  exact ld_tbl_psiOk_pos t h 5376 10753 backend.crt.Q2_INV _ _ _ _ hTbl hAt (by omega)
    (by rw [← q2_val]; exact q2_inv_unit)
    (by omega)

/-- The `FWD4` table for `q2` is centred and Montgomery-paired. -/
theorem fwd4_q2_ok : ∀ h : Usize, h.val < 2 → ∃ z zq,
    (do let t ← backend.avx2.ntt.FWD4_Q2; backend.avx2.ntt.ld_tbl t h) = ok (z, zq) ∧
      PsiOk z zq 10753 5376 ∧
      (∀ k < 16, (lane16 z k).toInt
        = (backend.crt.ZETAS_Q2.val[((32#isize).val + h.val * (1#isize).val
            + k * (2#isize).val).toNat]!).val) := by
  intro h hh
  have hb : (32#isize).val = 32 := by scalar_tac
  have hhs : (1#isize).val = 1 := by scalar_tac
  have hms : (2#isize).val = 2 := by scalar_tac
  have hNv : ((32#usize) : Usize).val = 32 := by scalar_tac
  obtain ⟨t, ht, hTbl, hAt⟩ := lane_tbl_spec 32#usize backend.crt.ZETAS_Q2 backend.crt.Q2_INV
    32#isize 1#isize 2#isize false 5376 (by norm_num) (by norm_num) zetas_q2_centred
    ⟨by omega, by omega⟩ (Or.inr (Or.inl (by scalar_tac))) (Or.inr (Or.inl (by scalar_tac)))
    (by scalar_tac) (by omega)
    (by intro hh' mm h1 h2; rw [hb, hhs, hms]; omega)
  rw [show backend.avx2.ntt.FWD4_Q2 = ok t from by
    unfold backend.avx2.ntt.FWD4_Q2; exact ht, bind_tc_ok]
  exact ld_tbl_psiOk_pos t h 5376 10753 backend.crt.Q2_INV _ _ _ _ hTbl hAt (by omega)
    (by rw [← q2_val]; exact q2_inv_unit)
    (by omega)

/-- The `FWD2` table for `q2` is centred and Montgomery-paired. -/
theorem fwd2_q2_ok : ∀ h : Usize, h.val < 4 → ∃ z zq,
    (do let t ← backend.avx2.ntt.FWD2_Q2; backend.avx2.ntt.ld_tbl t h) = ok (z, zq) ∧
      PsiOk z zq 10753 5376 ∧
      (∀ k < 16, (lane16 z k).toInt
        = (backend.crt.ZETAS_Q2.val[((64#isize).val + h.val * (1#isize).val
            + k * (4#isize).val).toNat]!).val) := by
  intro h hh
  have hb : (64#isize).val = 64 := by scalar_tac
  have hhs : (1#isize).val = 1 := by scalar_tac
  have hms : (4#isize).val = 4 := by scalar_tac
  have hNv : ((64#usize) : Usize).val = 64 := by scalar_tac
  obtain ⟨t, ht, hTbl, hAt⟩ := lane_tbl_spec 64#usize backend.crt.ZETAS_Q2 backend.crt.Q2_INV
    64#isize 1#isize 4#isize false 5376 (by norm_num) (by norm_num) zetas_q2_centred
    ⟨by omega, by omega⟩ (Or.inr (Or.inl (by scalar_tac))) (Or.inr (Or.inr (Or.inl (by scalar_tac))))
    (by scalar_tac) (by omega)
    (by intro hh' mm h1 h2; rw [hb, hhs, hms]; omega)
  rw [show backend.avx2.ntt.FWD2_Q2 = ok t from by
    unfold backend.avx2.ntt.FWD2_Q2; exact ht, bind_tc_ok]
  exact ld_tbl_psiOk_pos t h 5376 10753 backend.crt.Q2_INV _ _ _ _ hTbl hAt (by omega)
    (by rw [← q2_val]; exact q2_inv_unit)
    (by omega)

/-- The `FWD1` table for `q2` is centred and Montgomery-paired. -/
theorem fwd1_q2_ok : ∀ h : Usize, h.val < 8 → ∃ z zq,
    (do let t ← backend.avx2.ntt.FWD1_Q2; backend.avx2.ntt.ld_tbl t h) = ok (z, zq) ∧
      PsiOk z zq 10753 5376 ∧
      (∀ k < 16, (lane16 z k).toInt
        = (backend.crt.ZETAS_Q2.val[((128#isize).val + h.val * (1#isize).val
            + k * (8#isize).val).toNat]!).val) := by
  intro h hh
  have hb : (128#isize).val = 128 := by scalar_tac
  have hhs : (1#isize).val = 1 := by scalar_tac
  have hms : (8#isize).val = 8 := by scalar_tac
  have hNv : ((128#usize) : Usize).val = 128 := by scalar_tac
  obtain ⟨t, ht, hTbl, hAt⟩ := lane_tbl_spec 128#usize backend.crt.ZETAS_Q2 backend.crt.Q2_INV
    128#isize 1#isize 8#isize false 5376 (by norm_num) (by norm_num) zetas_q2_centred
    ⟨by omega, by omega⟩ (Or.inr (Or.inl (by scalar_tac))) (Or.inr (Or.inr (Or.inr (Or.inl (by scalar_tac)))))
    (by scalar_tac) (by omega)
    (by intro hh' mm h1 h2; rw [hb, hhs, hms]; omega)
  rw [show backend.avx2.ntt.FWD1_Q2 = ok t from by
    unfold backend.avx2.ntt.FWD1_Q2; exact ht, bind_tc_ok]
  exact ld_tbl_psiOk_pos t h 5376 10753 backend.crt.Q2_INV _ _ _ _ hTbl hAt (by omega)
    (by rw [← q2_val]; exact q2_inv_unit)
    (by omega)

/-! ## The four inverse tables, for each prime

Same construction with `neg` set, so each lane holds `−ζ` rather than `ζ`.  The Gentleman-Sande
butterfly wants exactly that — `State_gs` applies `−ζ(2nb−1−b)` — so the negation the tables
carry is the one the algebra expects, and no sign has to be inserted at the butterfly.

The index walks *downward*: `base` sits at the top of the level's ζ range and both strides are
negative.  That is why `lane_tbl_spec` needs the two-sided `hidx`: the one-sided version could
not see that the walk stays above zero. -/

/-- The shared body of the eight inverse-table lemmas.  Everything below is this at concrete
parameters; the only work per table is checking its index walk stays inside `[0, 256)`. -/
private theorem inv_tbl_ok {N : Usize} (zetas : Array I16 256#usize) (qinv : I16) (Zb Q : ℤ)
    (base h_stride m_stride : Isize) (tbl : Result (backend.avx2.ntt.Tbl N))
    (htbl : tbl = backend.avx2.ntt.lane_tbl N zetas qinv base h_stride m_stride true)
    (hZb : 0 ≤ Zb) (hZb' : Zb ≤ 32767)
    (hzet : ∀ x ∈ zetas.val, |x.val| ≤ Zb)
    (hbase : 0 ≤ base.val ∧ base.val ≤ 255)
    (hhs : h_stride.val = 0 ∨ h_stride.val = 1 ∨ h_stride.val = -1)
    (hms : m_stride.val = 1 ∨ m_stride.val = 2 ∨ m_stride.val = 4 ∨ m_stride.val = 8 ∨
      m_stride.val = -1 ∨ m_stride.val = -2 ∨ m_stride.val = -4 ∨ m_stride.val = -8)
    (hN : N.val ≤ 128) (hNdvd : 16 ∣ N.val)
    (hidx : ∀ hh mm : ℕ, hh < 8 → mm < 16 →
      0 ≤ base.val + hh * h_stride.val + mm * m_stride.val ∧
      base.val + hh * h_stride.val + mm * m_stride.val < 256)
    (hunit : (2 ^ 16 : ℤ) ∣ (qinv.val * Q - 1)) :
    ∀ h : Usize, h.val < 8 → 16 * (h.val + 1) ≤ N.val → ∃ z zq,
      (do let t ← tbl; backend.avx2.ntt.ld_tbl t h) = ok (z, zq) ∧ PsiOk z zq Q Zb ∧
      ∀ k < 16, (lane16 z k).toInt
        = -(zetas.val[(base.val + h.val * h_stride.val + k * m_stride.val).toNat]!).val := by
  intro h hh hlt
  obtain ⟨t, ht, hTbl, hAt⟩ := lane_tbl_spec N zetas qinv base h_stride m_stride true Zb hZb hZb'
    hzet hbase hhs hms hN hNdvd hidx
  obtain ⟨z, zq, h1, h2, h3⟩ :=
    ld_tbl_psiOk t h Zb Q qinv zetas base h_stride m_stride true hTbl hAt hh hunit hlt
  exact ⟨z, zq, by rw [htbl, ht, bind_tc_ok]; exact h1, h2, fun k hk => by simpa using h3 k hk⟩

/-- The `INV1` table for `q1`: lane `k` of group `h` holds `−ζ[255 − h − 8k]`. -/
theorem inv1_q1_ok : ∀ h : Usize, h.val < 8 → ∃ z zq,
    (do let t ← backend.avx2.ntt.INV1_Q1; backend.avx2.ntt.ld_tbl t h) = ok (z, zq) ∧
      PsiOk z zq 7681 3840 ∧
      (∀ k < 16, (lane16 z k).toInt
        = -(backend.crt.ZETAS_Q1.val[((255#isize).val + h.val * ((-1)#isize).val
            + k * ((-8)#isize).val).toNat]!).val) :=
  fun h hh => inv_tbl_ok backend.crt.ZETAS_Q1 backend.crt.Q1_INV 3840 7681 255#isize
    (-1)#isize (-8)#isize backend.avx2.ntt.INV1_Q1
    (by unfold backend.avx2.ntt.INV1_Q1; rfl) (by norm_num) (by norm_num) zetas_q1_centred
    ⟨by scalar_tac, by scalar_tac⟩ (Or.inr (Or.inr (by scalar_tac)))
    (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by scalar_tac))))))))
    (by scalar_tac) (by rw [show ((128#usize) : Usize).val = 128 from by scalar_tac]; omega)
    (by intro hh' mm h1 h2
        have hb : (255#isize).val = 255 := by scalar_tac
        have hs : ((-1)#isize).val = -1 := by scalar_tac
        have hm : ((-8)#isize).val = -8 := by scalar_tac
        rw [hb, hs, hm]; omega)
    (by rw [← q1_val]; exact q1_inv_unit) h hh (by scalar_tac)

/-- The `INV2` table for `q1`: lane `k` of group `h` holds `−ζ[127 − h − 4k]`. -/
theorem inv2_q1_ok : ∀ h : Usize, h.val < 4 → ∃ z zq,
    (do let t ← backend.avx2.ntt.INV2_Q1; backend.avx2.ntt.ld_tbl t h) = ok (z, zq) ∧
      PsiOk z zq 7681 3840 ∧
      (∀ k < 16, (lane16 z k).toInt
        = -(backend.crt.ZETAS_Q1.val[((127#isize).val + h.val * ((-1)#isize).val
            + k * ((-4)#isize).val).toNat]!).val) :=
  fun h hh => inv_tbl_ok backend.crt.ZETAS_Q1 backend.crt.Q1_INV 3840 7681 127#isize
    (-1)#isize (-4)#isize backend.avx2.ntt.INV2_Q1
    (by unfold backend.avx2.ntt.INV2_Q1; rfl) (by norm_num) (by norm_num) zetas_q1_centred
    ⟨by scalar_tac, by scalar_tac⟩ (Or.inr (Or.inr (by scalar_tac)))
    (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by scalar_tac)))))))
    (by scalar_tac) (by rw [show ((64#usize) : Usize).val = 64 from by scalar_tac]; omega)
    (by intro hh' mm h1 h2
        have hb : (127#isize).val = 127 := by scalar_tac
        have hs : ((-1)#isize).val = -1 := by scalar_tac
        have hm : ((-4)#isize).val = -4 := by scalar_tac
        rw [hb, hs, hm]; omega)
    (by rw [← q1_val]; exact q1_inv_unit) h (by omega) (by scalar_tac)

/-- The `INV4` table for `q1`: lane `k` of group `h` holds `−ζ[63 − h − 2k]`. -/
theorem inv4_q1_ok : ∀ h : Usize, h.val < 2 → ∃ z zq,
    (do let t ← backend.avx2.ntt.INV4_Q1; backend.avx2.ntt.ld_tbl t h) = ok (z, zq) ∧
      PsiOk z zq 7681 3840 ∧
      (∀ k < 16, (lane16 z k).toInt
        = -(backend.crt.ZETAS_Q1.val[((63#isize).val + h.val * ((-1)#isize).val
            + k * ((-2)#isize).val).toNat]!).val) :=
  fun h hh => inv_tbl_ok backend.crt.ZETAS_Q1 backend.crt.Q1_INV 3840 7681 63#isize
    (-1)#isize (-2)#isize backend.avx2.ntt.INV4_Q1
    (by unfold backend.avx2.ntt.INV4_Q1; rfl) (by norm_num) (by norm_num) zetas_q1_centred
    ⟨by scalar_tac, by scalar_tac⟩ (Or.inr (Or.inr (by scalar_tac)))
    (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by scalar_tac))))))
    (by scalar_tac) (by rw [show ((32#usize) : Usize).val = 32 from by scalar_tac]; omega)
    (by intro hh' mm h1 h2
        have hb : (63#isize).val = 63 := by scalar_tac
        have hs : ((-1)#isize).val = -1 := by scalar_tac
        have hm : ((-2)#isize).val = -2 := by scalar_tac
        rw [hb, hs, hm]; omega)
    (by rw [← q1_val]; exact q1_inv_unit) h (by omega) (by scalar_tac)

/-- The `INV8` table for `q1`: lane `k` holds `−ζ[31 − k]`; the level has one group. -/
theorem inv8_q1_ok : ∀ h : Usize, h.val < 1 → ∃ z zq,
    (do let t ← backend.avx2.ntt.INV8_Q1; backend.avx2.ntt.ld_tbl t h) = ok (z, zq) ∧
      PsiOk z zq 7681 3840 ∧
      (∀ k < 16, (lane16 z k).toInt
        = -(backend.crt.ZETAS_Q1.val[((31#isize).val + h.val * (0#isize).val
            + k * ((-1)#isize).val).toNat]!).val) :=
  fun h hh => inv_tbl_ok backend.crt.ZETAS_Q1 backend.crt.Q1_INV 3840 7681 31#isize
    0#isize (-1)#isize backend.avx2.ntt.INV8_Q1
    (by unfold backend.avx2.ntt.INV8_Q1; rfl) (by norm_num) (by norm_num) zetas_q1_centred
    ⟨by scalar_tac, by scalar_tac⟩ (Or.inl (by scalar_tac))
    (Or.inr (Or.inr (Or.inr (Or.inr (by scalar_tac)))))
    (by scalar_tac) (by rw [show ((16#usize) : Usize).val = 16 from by scalar_tac])
    (by intro hh' mm h1 h2
        have hb : (31#isize).val = 31 := by scalar_tac
        have hs : (0#isize).val = 0 := by scalar_tac
        have hm : ((-1)#isize).val = -1 := by scalar_tac
        rw [hb, hs, hm]; omega)
    (by rw [← q1_val]; exact q1_inv_unit) h (by omega) (by scalar_tac)

/-- The `INV1` table for `q2`. -/
theorem inv1_q2_ok : ∀ h : Usize, h.val < 8 → ∃ z zq,
    (do let t ← backend.avx2.ntt.INV1_Q2; backend.avx2.ntt.ld_tbl t h) = ok (z, zq) ∧
      PsiOk z zq 10753 5376 ∧
      (∀ k < 16, (lane16 z k).toInt
        = -(backend.crt.ZETAS_Q2.val[((255#isize).val + h.val * ((-1)#isize).val
            + k * ((-8)#isize).val).toNat]!).val) :=
  fun h hh => inv_tbl_ok backend.crt.ZETAS_Q2 backend.crt.Q2_INV 5376 10753 255#isize
    (-1)#isize (-8)#isize backend.avx2.ntt.INV1_Q2
    (by unfold backend.avx2.ntt.INV1_Q2; rfl) (by norm_num) (by norm_num) zetas_q2_centred
    ⟨by scalar_tac, by scalar_tac⟩ (Or.inr (Or.inr (by scalar_tac)))
    (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by scalar_tac))))))))
    (by scalar_tac) (by rw [show ((128#usize) : Usize).val = 128 from by scalar_tac]; omega)
    (by intro hh' mm h1 h2
        have hb : (255#isize).val = 255 := by scalar_tac
        have hs : ((-1)#isize).val = -1 := by scalar_tac
        have hm : ((-8)#isize).val = -8 := by scalar_tac
        rw [hb, hs, hm]; omega)
    (by rw [← q2_val]; exact q2_inv_unit) h hh (by scalar_tac)

/-- The `INV2` table for `q2`. -/
theorem inv2_q2_ok : ∀ h : Usize, h.val < 4 → ∃ z zq,
    (do let t ← backend.avx2.ntt.INV2_Q2; backend.avx2.ntt.ld_tbl t h) = ok (z, zq) ∧
      PsiOk z zq 10753 5376 ∧
      (∀ k < 16, (lane16 z k).toInt
        = -(backend.crt.ZETAS_Q2.val[((127#isize).val + h.val * ((-1)#isize).val
            + k * ((-4)#isize).val).toNat]!).val) :=
  fun h hh => inv_tbl_ok backend.crt.ZETAS_Q2 backend.crt.Q2_INV 5376 10753 127#isize
    (-1)#isize (-4)#isize backend.avx2.ntt.INV2_Q2
    (by unfold backend.avx2.ntt.INV2_Q2; rfl) (by norm_num) (by norm_num) zetas_q2_centred
    ⟨by scalar_tac, by scalar_tac⟩ (Or.inr (Or.inr (by scalar_tac)))
    (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by scalar_tac)))))))
    (by scalar_tac) (by rw [show ((64#usize) : Usize).val = 64 from by scalar_tac]; omega)
    (by intro hh' mm h1 h2
        have hb : (127#isize).val = 127 := by scalar_tac
        have hs : ((-1)#isize).val = -1 := by scalar_tac
        have hm : ((-4)#isize).val = -4 := by scalar_tac
        rw [hb, hs, hm]; omega)
    (by rw [← q2_val]; exact q2_inv_unit) h (by omega) (by scalar_tac)

/-- The `INV4` table for `q2`. -/
theorem inv4_q2_ok : ∀ h : Usize, h.val < 2 → ∃ z zq,
    (do let t ← backend.avx2.ntt.INV4_Q2; backend.avx2.ntt.ld_tbl t h) = ok (z, zq) ∧
      PsiOk z zq 10753 5376 ∧
      (∀ k < 16, (lane16 z k).toInt
        = -(backend.crt.ZETAS_Q2.val[((63#isize).val + h.val * ((-1)#isize).val
            + k * ((-2)#isize).val).toNat]!).val) :=
  fun h hh => inv_tbl_ok backend.crt.ZETAS_Q2 backend.crt.Q2_INV 5376 10753 63#isize
    (-1)#isize (-2)#isize backend.avx2.ntt.INV4_Q2
    (by unfold backend.avx2.ntt.INV4_Q2; rfl) (by norm_num) (by norm_num) zetas_q2_centred
    ⟨by scalar_tac, by scalar_tac⟩ (Or.inr (Or.inr (by scalar_tac)))
    (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by scalar_tac))))))
    (by scalar_tac) (by rw [show ((32#usize) : Usize).val = 32 from by scalar_tac]; omega)
    (by intro hh' mm h1 h2
        have hb : (63#isize).val = 63 := by scalar_tac
        have hs : ((-1)#isize).val = -1 := by scalar_tac
        have hm : ((-2)#isize).val = -2 := by scalar_tac
        rw [hb, hs, hm]; omega)
    (by rw [← q2_val]; exact q2_inv_unit) h (by omega) (by scalar_tac)

/-- The `INV8` table for `q2`. -/
theorem inv8_q2_ok : ∀ h : Usize, h.val < 1 → ∃ z zq,
    (do let t ← backend.avx2.ntt.INV8_Q2; backend.avx2.ntt.ld_tbl t h) = ok (z, zq) ∧
      PsiOk z zq 10753 5376 ∧
      (∀ k < 16, (lane16 z k).toInt
        = -(backend.crt.ZETAS_Q2.val[((31#isize).val + h.val * (0#isize).val
            + k * ((-1)#isize).val).toNat]!).val) :=
  fun h hh => inv_tbl_ok backend.crt.ZETAS_Q2 backend.crt.Q2_INV 5376 10753 31#isize
    0#isize (-1)#isize backend.avx2.ntt.INV8_Q2
    (by unfold backend.avx2.ntt.INV8_Q2; rfl) (by norm_num) (by norm_num) zetas_q2_centred
    ⟨by scalar_tac, by scalar_tac⟩ (Or.inl (by scalar_tac))
    (Or.inr (Or.inr (Or.inr (Or.inr (by scalar_tac)))))
    (by scalar_tac) (by rw [show ((16#usize) : Usize).val = 16 from by scalar_tac])
    (by intro hh' mm h1 h2
        have hb : (31#isize).val = 31 := by scalar_tac
        have hs : (0#isize).val = 0 := by scalar_tac
        have hm : ((-1)#isize).val = -1 := by scalar_tac
        rw [hb, hs, hm]; omega)
    (by rw [← q2_val]; exact q2_inv_unit) h (by omega) (by scalar_tac)

/-! ## The growth bound, unconditionally

With the table hypotheses discharged, phase F3's conclusion stands on its own: the extracted
`ntt_block` leaves every coefficient of a centred block centred, for both primes. -/

/-- **`ntt_block` for `q₁` keeps the block centred** — no hypotheses about the ψ tables. -/
theorem ntt_block_centred_q1 (b : Array I16 256#usize) (hb : BlockBnd b 3840) :
    backend.avx2.ntt.ntt_block false b ⦃ (r : Array I16 256#usize) => BlockBnd r 3840 ⦄ :=
  ntt_block_bnd_q1 b
    (fun kk hkk => by
      obtain ⟨zi, zqi, h1, h2, h3, h4, -⟩ := zeta_table_ok_q1 kk hkk
      exact ⟨zi, zqi, h1, h2, h3, h4⟩)
    (by obtain ⟨z, zq, h1, h2, -⟩ := fwd8_q1_ok 0#usize (by simp); exact ⟨z, zq, h1, h2⟩)
    (fun h hh => by obtain ⟨z, zq, h1, h2, -⟩ := fwd4_q1_ok h hh; exact ⟨z, zq, h1, h2⟩)
    (fun h hh => by obtain ⟨z, zq, h1, h2, -⟩ := fwd2_q1_ok h hh; exact ⟨z, zq, h1, h2⟩)
    (fun h hh => by obtain ⟨z, zq, h1, h2, -⟩ := fwd1_q1_ok h hh; exact ⟨z, zq, h1, h2⟩) hb

/-- **`ntt_block` for `q₂` keeps the block centred** — the binding prime, worst lane 31671 of
32767 along the way. -/
theorem ntt_block_centred_q2 (b : Array I16 256#usize) (hb : BlockBnd b 5376) :
    backend.avx2.ntt.ntt_block true b ⦃ (r : Array I16 256#usize) => BlockBnd r 5376 ⦄ :=
  ntt_block_bnd_q2 b
    (fun kk hkk => by
      obtain ⟨zi, zqi, h1, h2, h3, h4, -⟩ := zeta_table_ok_q2 kk hkk
      exact ⟨zi, zqi, h1, h2, h3, h4⟩)
    (by obtain ⟨z, zq, h1, h2, -⟩ := fwd8_q2_ok 0#usize (by simp); exact ⟨z, zq, h1, h2⟩)
    (fun h hh => by obtain ⟨z, zq, h1, h2, -⟩ := fwd4_q2_ok h hh; exact ⟨z, zq, h1, h2⟩)
    (fun h hh => by obtain ⟨z, zq, h1, h2, -⟩ := fwd2_q2_ok h hh; exact ⟨z, zq, h1, h2⟩)
    (fun h hh => by obtain ⟨z, zq, h1, h2, -⟩ := fwd1_q2_ok h hh; exact ⟨z, zq, h1, h2⟩) hb

end Kopis.Avx2