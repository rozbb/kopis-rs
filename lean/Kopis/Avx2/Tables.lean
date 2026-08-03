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
    |zi.val| ≤ 3840 ∧ (2 ^ 16 : ℤ) ∣ (zqi.val * 7681 - zi.val) := by
  intro kk hkk
  obtain ⟨t, ht, htv⟩ := zetas_qinv_spec backend.crt.ZETAS_Q1 backend.crt.Q1_INV
  obtain ⟨zi, hzi, hziv⟩ := WP.spec_imp_exists
    (Array.index_usize_spec backend.crt.ZETAS_Q1 kk (by simp [Array.length]; omega))
  obtain ⟨zqi, hzqi, hzqiv⟩ := WP.spec_imp_exists
    (Array.index_usize_spec t kk (by simp [Array.length]; omega))
  refine ⟨zi, zqi, ?_, ?_, ?_, ?_⟩
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

/-- **The ζ hypothesis of `ntt_block_bnd_q2`, discharged.** -/
theorem zeta_table_ok_q2 : ∀ kk : Usize, kk.val < 256 → ∃ zi zqi : I16,
    backend.crt.zeta true kk = ok zi ∧ backend.crt.zeta_q true kk = ok zqi ∧
    |zi.val| ≤ 5376 ∧ (2 ^ 16 : ℤ) ∣ (zqi.val * 10753 - zi.val) := by
  intro kk hkk
  obtain ⟨t, ht, htv⟩ := zetas_qinv_spec backend.crt.ZETAS_Q2 backend.crt.Q2_INV
  obtain ⟨zi, hzi, hziv⟩ := WP.spec_imp_exists
    (Array.index_usize_spec backend.crt.ZETAS_Q2 kk (by simp [Array.length]; omega))
  obtain ⟨zqi, hzqi, hzqiv⟩ := WP.spec_imp_exists
    (Array.index_usize_spec t kk (by simp [Array.length]; omega))
  refine ⟨zi, zqi, ?_, ?_, ?_, ?_⟩
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

set_option maxRecDepth 100000 in
theorem lane_tbl_loop0_loop0_spec {N : Usize} (zetas : Array I16 256#usize) (qinv : I16)
    (base h_stride m_stride : Isize) (z zq : Array I16 N) (h m : Usize) (Zb : ℤ)
    (hzet : ∀ x ∈ zetas.val, |x.val| ≤ Zb)
    (hbase : 0 ≤ base.val ∧ base.val ≤ 128)
    (hhs : h_stride.val = 0 ∨ h_stride.val = 1)
    (hms : m_stride.val = 1 ∨ m_stride.val = 2 ∨ m_stride.val = 4 ∨ m_stride.val = 8)
    (hh : h.val ≤ 8) (hm : m.val ≤ 16)
    (hidx : ∀ mm : ℕ, mm < 16 → base.val + h.val * h_stride.val + mm * m_stride.val < 256)
    (hN : 16 * h.val + 16 ≤ N.val)
    (hinv : TblOk Zb qinv z zq) :
    backend.avx2.ntt.lane_tbl_loop0_loop0 zetas qinv base h_stride m_stride false z zq h m
      ⦃ (r : (Array I16 N) × (Array I16 N)) => TblOk Zb qinv r.1 r.2 ⦄ := by
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
      rcases hhs with hs | hs <;> rcases hms with ms | ms | ms | ms <;>
        (have hI := hidx m.val hlt
         simp only [hs, ms, hiv, mul_zero, mul_one] at *
         omega)))
    all_goals (try (
      have hiv : i.val = h.val := by rw [i_post]; exact hcast_usize_isize_val h (by omega)
      have hi3v : i3.val = m.val := by rw [i3_post]; exact hcast_usize_isize_val m (by omega)
      rcases hhs with hs | hs <;> rcases hms with ms | ms | ms | ms <;>
        (have hI := hidx m.val hlt
         simp only [hs, ms, hiv, hi3v, mul_zero, mul_one] at *
         omega)))
    · have hiv : i.val = h.val := by rw [i_post]; exact hcast_usize_isize_val h (by omega)
      have hi3v : i3.val = m.val := by rw [i3_post]; exact hcast_usize_isize_val m (by omega)
      have hi5v : ((i5 : Usize).val : ℤ) = idx.val := by
        rw [i5_post]
        refine hcast_isize_usize_val idx ⟨?_, ?_⟩ <;>
          (rcases hhs with hs | hs <;> rcases hms with ms | ms | ms | ms <;>
            (have hI := hidx m.val hlt
             try simp only [hs, ms, hiv, hi3v, mul_zero, mul_one] at *
             omega))
      have hbound : ((i5 : Usize).val : ℤ) < 256 := by
        have hI := hidx m.val hlt
        rw [hi5v, idx_post, i2_post, i4_post, i1_post, hiv, hi3v]
        linarith [hI]
      rw [hzlen]
      omega
    -- the write: `z[16h+m] := zetas[idx]`, `zq[16h+m] := that · q⁻¹`
    rw [if_neg (by decide), bind_tc_ok]
    have hvz : |value.val| ≤ Zb := by rw [value_post]; exact hzet _ (List.getElem_mem _)
    step*
    have hidxlt : i7.val < N.val := by omega
    have hi9lt : i9.val < N.val := by omega
    all_goals first
      | omega
      | (intro w hw
         rw [a_post, a1_post, Std.Array.set_val_eq, Std.Array.set_val_eq,
           getElem!_list_set _ _ _ _ (by rw [z.property]; simpa using hidxlt),
           getElem!_list_set _ _ _ _ (by rw [zq.property]; simpa using hi9lt)]
         by_cases hwe : w = i7.val
         · rw [if_pos hwe, if_pos (show w = i9.val by omega), i8_post,
             core.num.I16.wrapping_mul, IScalar.wrapping_mul_val_eq]
           exact ⟨hvz, rfl⟩
         · rw [if_neg hwe, if_neg (show ¬ w = i9.val by omega)]
           exact hinv w hw)
  · rw [if_neg (by scalar_tac)]
    simp only [WP.spec_ok]
    exact hinv
termination_by 16 - m.val
decreasing_by scalar_decr_tac

set_option maxRecDepth 100000 in
theorem lane_tbl_loop0_spec {N : Usize} (zetas : Array I16 256#usize) (qinv : I16)
    (base h_stride m_stride : Isize) (z zq : Array I16 N) (h : Usize) (Zb : ℤ)
    (hzet : ∀ x ∈ zetas.val, |x.val| ≤ Zb)
    (hbase : 0 ≤ base.val ∧ base.val ≤ 128)
    (hhs : h_stride.val = 0 ∨ h_stride.val = 1)
    (hms : m_stride.val = 1 ∨ m_stride.val = 2 ∨ m_stride.val = 4 ∨ m_stride.val = 8)
    (hN : N.val ≤ 128) (hNdvd : 16 ∣ N.val) (hh : h.val ≤ 8)
    (hidx : ∀ hh mm : ℕ, hh < 8 → mm < 16 →
      base.val + hh * h_stride.val + mm * m_stride.val < 256)
    (hinv : TblOk Zb qinv z zq) :
    backend.avx2.ntt.lane_tbl_loop0 zetas qinv base h_stride m_stride false z zq h
      ⦃ (r : (Array I16 N) × (Array I16 N)) => TblOk Zb qinv r.1 r.2 ⦄ := by
  unfold backend.avx2.ntt.lane_tbl_loop0
  step*
  · apply WP.spec_bind (lane_tbl_loop0_loop0_spec zetas qinv base h_stride m_stride z zq h 0#usize
      Zb hzet hbase hhs hms (by scalar_tac) (by simp)
      (fun mm hmm => hidx h.val mm (by scalar_tac) hmm) (by scalar_tac) hinv)
    rintro ⟨z1, zq1⟩ hz1
    simp only at hz1
    step*
termination_by N.val - 16 * h.val
decreasing_by scalar_decr_tac

theorem lane_tbl_spec (N : Usize) (zetas : Array I16 256#usize) (qinv : I16)
    (base h_stride m_stride : Isize) (Zb : ℤ) (hZb : 0 ≤ Zb)
    (hzet : ∀ x ∈ zetas.val, |x.val| ≤ Zb)
    (hbase : 0 ≤ base.val ∧ base.val ≤ 128)
    (hhs : h_stride.val = 0 ∨ h_stride.val = 1)
    (hms : m_stride.val = 1 ∨ m_stride.val = 2 ∨ m_stride.val = 4 ∨ m_stride.val = 8)
    (hN : N.val ≤ 128) (hNdvd : 16 ∣ N.val)
    (hidx : ∀ hh mm : ℕ, hh < 8 → mm < 16 →
      base.val + hh * h_stride.val + mm * m_stride.val < 256) :
    ∃ t, backend.avx2.ntt.lane_tbl N zetas qinv base h_stride m_stride false = ok t ∧
      TblOk Zb qinv t.z t.zq := by
  apply WP.spec_imp_exists
  unfold backend.avx2.ntt.lane_tbl
  apply WP.spec_bind (lane_tbl_loop0_spec zetas qinv base h_stride m_stride _ _ 0#usize Zb
    hzet hbase hhs hms hN hNdvd (by simp) hidx ?_)
  · rintro ⟨z1, zq1⟩ hz1
    simp only at hz1
    show (ok ({ z := z1, zq := zq1 } : backend.avx2.ntt.Tbl N))
      ⦃ (t : backend.avx2.ntt.Tbl N) => TblOk Zb qinv t.z t.zq ⦄
    simp only [WP.spec_ok]
    exact hz1
  · intro w hw
    refine ⟨?_, ?_⟩ <;>
      rw [Array.repeat_val, getElem!_pos _ w (by rw [List.length_replicate]; simpa using hw),
        List.getElem_replicate] <;>
      simp [hZb]

/-! ## From a table to a usable ψ pair -/

/-- The Montgomery pairing, once: if `zq ≡ z·q⁻¹` and `q⁻¹·q ≡ 1`, then `zq·q ≡ z`. -/
private theorem mont_pair {zv zqv Q : ℤ} {qinv : I16}
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
    (hTbl : TblOk Zb qinv t.z t.zq) (hunit : (2 ^ 16 : ℤ) ∣ (qinv.val * Q - 1))
    (hlt : 16 * (hh.val + 1) ≤ N.val) :
    ∃ z zq, backend.avx2.ntt.ld_tbl t hh = ok (z, zq) ∧ PsiOk z zq Q Zb := by
  obtain ⟨v, hv, hvl⟩ := load_i16_spec t.z hh hlt
  obtain ⟨v1, hv1, hv1l⟩ := load_i16_spec t.zq hh hlt
  refine ⟨v, v1, ?_, ?_, ?_⟩
  · unfold backend.avx2.ntt.ld_tbl
    rw [hv, bind_tc_ok, hv1, bind_tc_ok]
  · intro k hk
    rw [show (lane16 v k).toInt = (t.z.val[16 * hh.val + k]!).val from by rw [hvl k hk]; rfl]
    exact (hTbl (16 * hh.val + k) (by omega)).1
  · intro k hk
    rw [show (lane16 v1 k).toInt = (t.zq.val[16 * hh.val + k]!).val from by rw [hv1l k hk]; rfl,
      show (lane16 v k).toInt = (t.z.val[16 * hh.val + k]!).val from by rw [hvl k hk]; rfl]
    exact mont_pair (hTbl (16 * hh.val + k) (by omega)).2 hunit

/-! ## The four forward tables, for each prime

Each is `lane_tbl` at concrete strides; the ζ index it reads stays inside `[0, 256)`, which is
what `hidx` records. -/

/-- The `FWD8` table for `q1` is centred and Montgomery-paired. -/
theorem fwd8_q1_ok : ∀ h : Usize, h.val < 1 → ∃ z zq,
    (do let t ← backend.avx2.ntt.FWD8_Q1; backend.avx2.ntt.ld_tbl t h) = ok (z, zq) ∧
      PsiOk z zq 7681 3840 := by
  intro h hh
  have hb : (16#isize).val = 16 := by scalar_tac
  have hhs : (0#isize).val = 0 := by scalar_tac
  have hms : (1#isize).val = 1 := by scalar_tac
  have hNv : ((16#usize) : Usize).val = 16 := by scalar_tac
  obtain ⟨t, ht, hTbl⟩ := lane_tbl_spec 16#usize backend.crt.ZETAS_Q1 backend.crt.Q1_INV
    16#isize 0#isize 1#isize 3840 (by norm_num) zetas_q1_centred
    ⟨by omega, by omega⟩ (Or.inl (by scalar_tac)) (Or.inl (by scalar_tac))
    (by scalar_tac) (by omega)
    (by intro hh' mm h1 h2; rw [hb, hhs, hms]; omega)
  rw [show backend.avx2.ntt.FWD8_Q1 = ok t from by
    unfold backend.avx2.ntt.FWD8_Q1; exact ht, bind_tc_ok]
  exact ld_tbl_psiOk t h 3840 7681 backend.crt.Q1_INV hTbl
    (by rw [← q1_val]; exact q1_inv_unit)
    (by omega)

/-- The `FWD4` table for `q1` is centred and Montgomery-paired. -/
theorem fwd4_q1_ok : ∀ h : Usize, h.val < 2 → ∃ z zq,
    (do let t ← backend.avx2.ntt.FWD4_Q1; backend.avx2.ntt.ld_tbl t h) = ok (z, zq) ∧
      PsiOk z zq 7681 3840 := by
  intro h hh
  have hb : (32#isize).val = 32 := by scalar_tac
  have hhs : (1#isize).val = 1 := by scalar_tac
  have hms : (2#isize).val = 2 := by scalar_tac
  have hNv : ((32#usize) : Usize).val = 32 := by scalar_tac
  obtain ⟨t, ht, hTbl⟩ := lane_tbl_spec 32#usize backend.crt.ZETAS_Q1 backend.crt.Q1_INV
    32#isize 1#isize 2#isize 3840 (by norm_num) zetas_q1_centred
    ⟨by omega, by omega⟩ (Or.inr (by scalar_tac)) (Or.inr (Or.inl (by scalar_tac)))
    (by scalar_tac) (by omega)
    (by intro hh' mm h1 h2; rw [hb, hhs, hms]; omega)
  rw [show backend.avx2.ntt.FWD4_Q1 = ok t from by
    unfold backend.avx2.ntt.FWD4_Q1; exact ht, bind_tc_ok]
  exact ld_tbl_psiOk t h 3840 7681 backend.crt.Q1_INV hTbl
    (by rw [← q1_val]; exact q1_inv_unit)
    (by omega)

/-- The `FWD2` table for `q1` is centred and Montgomery-paired. -/
theorem fwd2_q1_ok : ∀ h : Usize, h.val < 4 → ∃ z zq,
    (do let t ← backend.avx2.ntt.FWD2_Q1; backend.avx2.ntt.ld_tbl t h) = ok (z, zq) ∧
      PsiOk z zq 7681 3840 := by
  intro h hh
  have hb : (64#isize).val = 64 := by scalar_tac
  have hhs : (1#isize).val = 1 := by scalar_tac
  have hms : (4#isize).val = 4 := by scalar_tac
  have hNv : ((64#usize) : Usize).val = 64 := by scalar_tac
  obtain ⟨t, ht, hTbl⟩ := lane_tbl_spec 64#usize backend.crt.ZETAS_Q1 backend.crt.Q1_INV
    64#isize 1#isize 4#isize 3840 (by norm_num) zetas_q1_centred
    ⟨by omega, by omega⟩ (Or.inr (by scalar_tac)) (Or.inr (Or.inr (Or.inl (by scalar_tac))))
    (by scalar_tac) (by omega)
    (by intro hh' mm h1 h2; rw [hb, hhs, hms]; omega)
  rw [show backend.avx2.ntt.FWD2_Q1 = ok t from by
    unfold backend.avx2.ntt.FWD2_Q1; exact ht, bind_tc_ok]
  exact ld_tbl_psiOk t h 3840 7681 backend.crt.Q1_INV hTbl
    (by rw [← q1_val]; exact q1_inv_unit)
    (by omega)

/-- The `FWD1` table for `q1` is centred and Montgomery-paired. -/
theorem fwd1_q1_ok : ∀ h : Usize, h.val < 8 → ∃ z zq,
    (do let t ← backend.avx2.ntt.FWD1_Q1; backend.avx2.ntt.ld_tbl t h) = ok (z, zq) ∧
      PsiOk z zq 7681 3840 := by
  intro h hh
  have hb : (128#isize).val = 128 := by scalar_tac
  have hhs : (1#isize).val = 1 := by scalar_tac
  have hms : (8#isize).val = 8 := by scalar_tac
  have hNv : ((128#usize) : Usize).val = 128 := by scalar_tac
  obtain ⟨t, ht, hTbl⟩ := lane_tbl_spec 128#usize backend.crt.ZETAS_Q1 backend.crt.Q1_INV
    128#isize 1#isize 8#isize 3840 (by norm_num) zetas_q1_centred
    ⟨by omega, by omega⟩ (Or.inr (by scalar_tac)) (Or.inr (Or.inr (Or.inr (by scalar_tac))))
    (by scalar_tac) (by omega)
    (by intro hh' mm h1 h2; rw [hb, hhs, hms]; omega)
  rw [show backend.avx2.ntt.FWD1_Q1 = ok t from by
    unfold backend.avx2.ntt.FWD1_Q1; exact ht, bind_tc_ok]
  exact ld_tbl_psiOk t h 3840 7681 backend.crt.Q1_INV hTbl
    (by rw [← q1_val]; exact q1_inv_unit)
    (by omega)

/-- The `FWD8` table for `q2` is centred and Montgomery-paired. -/
theorem fwd8_q2_ok : ∀ h : Usize, h.val < 1 → ∃ z zq,
    (do let t ← backend.avx2.ntt.FWD8_Q2; backend.avx2.ntt.ld_tbl t h) = ok (z, zq) ∧
      PsiOk z zq 10753 5376 := by
  intro h hh
  have hb : (16#isize).val = 16 := by scalar_tac
  have hhs : (0#isize).val = 0 := by scalar_tac
  have hms : (1#isize).val = 1 := by scalar_tac
  have hNv : ((16#usize) : Usize).val = 16 := by scalar_tac
  obtain ⟨t, ht, hTbl⟩ := lane_tbl_spec 16#usize backend.crt.ZETAS_Q2 backend.crt.Q2_INV
    16#isize 0#isize 1#isize 5376 (by norm_num) zetas_q2_centred
    ⟨by omega, by omega⟩ (Or.inl (by scalar_tac)) (Or.inl (by scalar_tac))
    (by scalar_tac) (by omega)
    (by intro hh' mm h1 h2; rw [hb, hhs, hms]; omega)
  rw [show backend.avx2.ntt.FWD8_Q2 = ok t from by
    unfold backend.avx2.ntt.FWD8_Q2; exact ht, bind_tc_ok]
  exact ld_tbl_psiOk t h 5376 10753 backend.crt.Q2_INV hTbl
    (by rw [← q2_val]; exact q2_inv_unit)
    (by omega)

/-- The `FWD4` table for `q2` is centred and Montgomery-paired. -/
theorem fwd4_q2_ok : ∀ h : Usize, h.val < 2 → ∃ z zq,
    (do let t ← backend.avx2.ntt.FWD4_Q2; backend.avx2.ntt.ld_tbl t h) = ok (z, zq) ∧
      PsiOk z zq 10753 5376 := by
  intro h hh
  have hb : (32#isize).val = 32 := by scalar_tac
  have hhs : (1#isize).val = 1 := by scalar_tac
  have hms : (2#isize).val = 2 := by scalar_tac
  have hNv : ((32#usize) : Usize).val = 32 := by scalar_tac
  obtain ⟨t, ht, hTbl⟩ := lane_tbl_spec 32#usize backend.crt.ZETAS_Q2 backend.crt.Q2_INV
    32#isize 1#isize 2#isize 5376 (by norm_num) zetas_q2_centred
    ⟨by omega, by omega⟩ (Or.inr (by scalar_tac)) (Or.inr (Or.inl (by scalar_tac)))
    (by scalar_tac) (by omega)
    (by intro hh' mm h1 h2; rw [hb, hhs, hms]; omega)
  rw [show backend.avx2.ntt.FWD4_Q2 = ok t from by
    unfold backend.avx2.ntt.FWD4_Q2; exact ht, bind_tc_ok]
  exact ld_tbl_psiOk t h 5376 10753 backend.crt.Q2_INV hTbl
    (by rw [← q2_val]; exact q2_inv_unit)
    (by omega)

/-- The `FWD2` table for `q2` is centred and Montgomery-paired. -/
theorem fwd2_q2_ok : ∀ h : Usize, h.val < 4 → ∃ z zq,
    (do let t ← backend.avx2.ntt.FWD2_Q2; backend.avx2.ntt.ld_tbl t h) = ok (z, zq) ∧
      PsiOk z zq 10753 5376 := by
  intro h hh
  have hb : (64#isize).val = 64 := by scalar_tac
  have hhs : (1#isize).val = 1 := by scalar_tac
  have hms : (4#isize).val = 4 := by scalar_tac
  have hNv : ((64#usize) : Usize).val = 64 := by scalar_tac
  obtain ⟨t, ht, hTbl⟩ := lane_tbl_spec 64#usize backend.crt.ZETAS_Q2 backend.crt.Q2_INV
    64#isize 1#isize 4#isize 5376 (by norm_num) zetas_q2_centred
    ⟨by omega, by omega⟩ (Or.inr (by scalar_tac)) (Or.inr (Or.inr (Or.inl (by scalar_tac))))
    (by scalar_tac) (by omega)
    (by intro hh' mm h1 h2; rw [hb, hhs, hms]; omega)
  rw [show backend.avx2.ntt.FWD2_Q2 = ok t from by
    unfold backend.avx2.ntt.FWD2_Q2; exact ht, bind_tc_ok]
  exact ld_tbl_psiOk t h 5376 10753 backend.crt.Q2_INV hTbl
    (by rw [← q2_val]; exact q2_inv_unit)
    (by omega)

/-- The `FWD1` table for `q2` is centred and Montgomery-paired. -/
theorem fwd1_q2_ok : ∀ h : Usize, h.val < 8 → ∃ z zq,
    (do let t ← backend.avx2.ntt.FWD1_Q2; backend.avx2.ntt.ld_tbl t h) = ok (z, zq) ∧
      PsiOk z zq 10753 5376 := by
  intro h hh
  have hb : (128#isize).val = 128 := by scalar_tac
  have hhs : (1#isize).val = 1 := by scalar_tac
  have hms : (8#isize).val = 8 := by scalar_tac
  have hNv : ((128#usize) : Usize).val = 128 := by scalar_tac
  obtain ⟨t, ht, hTbl⟩ := lane_tbl_spec 128#usize backend.crt.ZETAS_Q2 backend.crt.Q2_INV
    128#isize 1#isize 8#isize 5376 (by norm_num) zetas_q2_centred
    ⟨by omega, by omega⟩ (Or.inr (by scalar_tac)) (Or.inr (Or.inr (Or.inr (by scalar_tac))))
    (by scalar_tac) (by omega)
    (by intro hh' mm h1 h2; rw [hb, hhs, hms]; omega)
  rw [show backend.avx2.ntt.FWD1_Q2 = ok t from by
    unfold backend.avx2.ntt.FWD1_Q2; exact ht, bind_tc_ok]
  exact ld_tbl_psiOk t h 5376 10753 backend.crt.Q2_INV hTbl
    (by rw [← q2_val]; exact q2_inv_unit)
    (by omega)

/-! ## The growth bound, unconditionally

With the table hypotheses discharged, phase F3's conclusion stands on its own: the extracted
`ntt_block` leaves every coefficient of a centred block centred, for both primes. -/

/-- **`ntt_block` for `q₁` keeps the block centred** — no hypotheses about the ψ tables. -/
theorem ntt_block_centred_q1 (b : Array I16 256#usize) (hb : BlockBnd b 3840) :
    backend.avx2.ntt.ntt_block false b ⦃ (r : Array I16 256#usize) => BlockBnd r 3840 ⦄ :=
  ntt_block_bnd_q1 b zeta_table_ok_q1 (fwd8_q1_ok 0#usize (by simp))
    fwd4_q1_ok fwd2_q1_ok fwd1_q1_ok hb

/-- **`ntt_block` for `q₂` keeps the block centred** — the binding prime, worst lane 31671 of
32767 along the way. -/
theorem ntt_block_centred_q2 (b : Array I16 256#usize) (hb : BlockBnd b 5376) :
    backend.avx2.ntt.ntt_block true b ⦃ (r : Array I16 256#usize) => BlockBnd r 5376 ⦄ :=
  ntt_block_bnd_q2 b zeta_table_ok_q2 (fwd8_q2_ok 0#usize (by simp))
    fwd4_q2_ok fwd2_q2_ok fwd1_q2_ok hb

end Kopis.Avx2