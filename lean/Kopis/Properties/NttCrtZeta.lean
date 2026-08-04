/-
  # Kopis/Properties/NttCrtZeta.lean — the portable backend's ψ tables.

  `src/backend/crt.rs` holds the two ψ tables the two-prime transform runs over, and both the
  portable and the vector paths read the same arrays.  `Kopis/CrtZeta.lean` reduces what the
  transform algebra asks of a table to finite checks; this file discharges them by `decide` over
  this extraction's `ZETAS_Q1` / `ZETAS_Q2`, and supplies the two other table facts the code walk
  needs:

  * **centredness** (`|ψ| ≤ q/2`), which is what bounds the growth of a Cooley-Tukey level, and
  * **the Montgomery pairing** `zq·q ≡ z (mod 2¹⁶)`, which is what makes `mont_mul` exact.

  The second is not a property of the literal arrays but of `zetas_qinv`, the `const fn` loop that
  derives `ZETAS_*_QINV` from them — so it is a loop specification, and it needs only
  `q⁻¹·q ≡ 1 (mod 2¹⁶)` about the two `Q*_INV` constants.

  This is the portable twin of `Kopis/Avx2/{Tables,NttZeta}.lean`: same statements, over the other
  extraction's constants.  The proofs are shared where they can be (`Kopis/CrtZeta.lean`); what is
  repeated here is exactly the part that names an extracted array, which no amount of sharing can
  avoid while there are two extractions.
-/
import Kopis.CrtZeta
import ExtractedRustSerial

open Aeneas Aeneas.Std Result
open RustKopisSerial

namespace Kopis.Properties

open Kopis.Avx2.NttAlg Kopis.CrtZeta

set_option maxHeartbeats 1000000
set_option maxRecDepth 40000

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


/-! ## The finite checks, on this extraction's tables -/

unseal backend.crt.ZETAS_Q1 in
theorem rootOK_q1 : rootOKq backend.crt.ZETAS_Q1 7681 4088 = true := by decide

unseal backend.crt.ZETAS_Q1 in
theorem treeOK_q1 : treeOKq backend.crt.ZETAS_Q1 7681 4088 = true := by decide

unseal backend.crt.ZETAS_Q2 in
theorem rootOK_q2 : rootOKq backend.crt.ZETAS_Q2 10753 1018 = true := by decide

unseal backend.crt.ZETAS_Q2 in
theorem treeOK_q2 : treeOKq backend.crt.ZETAS_Q2 10753 1018 = true := by decide

unseal backend.crt.ZETAS_Q1 in
theorem pairOK_q1 : pairOKq backend.crt.ZETAS_Q1 7681 4088 = true := by decide

unseal backend.crt.ZETAS_Q2 in
theorem pairOK_q2 : pairOKq backend.crt.ZETAS_Q2 10753 1018 = true := by decide

/-! ## …instantiated at the two primes -/

/-- The plain `q₁` twiddles. -/
def zeta1 : ℕ → ZMod 7681 := zetaQ backend.crt.ZETAS_Q1 (900 : ZMod 7681)
/-- The plain `q₂` twiddles. -/
def zeta2 : ℕ → ZMod 10753 := zetaQ backend.crt.ZETAS_Q2 (1764 : ZMod 10753)

theorem zeta1_sq : ∀ k, 1 ≤ k → k < 256 → zeta1 k ^ 2 = cst zeta1 k :=
  zetaQ_sq backend.crt.ZETAS_Q1 4088 (900 : ZMod 7681) (by decide) rootOK_q1 treeOK_q1

theorem zeta2_sq : ∀ k, 1 ≤ k → k < 256 → zeta2 k ^ 2 = cst zeta2 k :=
  zetaQ_sq backend.crt.ZETAS_Q2 1018 (1764 : ZMod 10753) (by decide) rootOK_q2 treeOK_q2

/-! ## …so the transform algebra applies at both primes

`State_ct` refines the CRT invariant by one Cooley-Tukey layer, and `State_leaf_mul` says that
once the leaf state is reached, multiplying lanewise multiplies the polynomials.  Those are the
two facts phase F4 needs about each prime; everything else is about the code. -/

theorem zeta1_pair : ∀ nb b : ℕ, (∃ j, j < 8 ∧ nb = 2 ^ j) → b < nb →
    zeta1 (nb + b) * zeta1 (2 * nb - 1 - b) = -1 :=
  zetaQ_pair backend.crt.ZETAS_Q1 4088 (900 : ZMod 7681) (by decide) pairOK_q1

theorem zeta2_pair : ∀ nb b : ℕ, (∃ j, j < 8 ∧ nb = 2 ^ j) → b < nb →
    zeta2 (nb + b) * zeta2 (2 * nb - 1 - b) = -1 :=
  zetaQ_pair backend.crt.ZETAS_Q2 1018 (1764 : ZMod 10753) (by decide) pairOK_q2

/-- One GS layer, at `q₁`. -/
theorem State_gs_q1 {nb m' : ℕ} (hnb1 : 1 ≤ nb) (hnb : 2 * nb ≤ 256)
    (hpow : ∃ j, j < 8 ∧ nb = 2 ^ j) {c : ZMod 7681} {f a a' : ℕ → ZMod 7681}
    (hst : State zeta1 (2 * nb) m' c f a)
    (hbut : ∀ b < nb, ∀ r < m',
      a' (b * (2 * m') + r) = a (b * (2 * m') + r) + a (b * (2 * m') + m' + r) ∧
      a' (b * (2 * m') + m' + r)
        = (-(zeta1 (2 * nb - 1 - b))) * (a (b * (2 * m') + r) - a (b * (2 * m') + m' + r))) :
    State zeta1 nb (2 * m') (2 * c) f a' :=
  State_gs zeta1_sq zeta1_pair hnb1 hnb hpow hst hbut

/-- One GS layer, at `q₂`. -/
theorem State_gs_q2 {nb m' : ℕ} (hnb1 : 1 ≤ nb) (hnb : 2 * nb ≤ 256)
    (hpow : ∃ j, j < 8 ∧ nb = 2 ^ j) {c : ZMod 10753} {f a a' : ℕ → ZMod 10753}
    (hst : State zeta2 (2 * nb) m' c f a)
    (hbut : ∀ b < nb, ∀ r < m',
      a' (b * (2 * m') + r) = a (b * (2 * m') + r) + a (b * (2 * m') + m' + r) ∧
      a' (b * (2 * m') + m' + r)
        = (-(zeta2 (2 * nb - 1 - b))) * (a (b * (2 * m') + r) - a (b * (2 * m') + m' + r))) :
    State zeta2 nb (2 * m') (2 * c) f a' :=
  State_gs zeta2_sq zeta2_pair hnb1 hnb hpow hst hbut

/-- One CT layer, at `q₁`. -/
theorem State_ct_q1 {nb m' : ℕ} (hnb1 : 1 ≤ nb) (hnb : 2 * nb ≤ 256)
    {c : ZMod 7681} {f a a' : ℕ → ZMod 7681}
    (hst : State zeta1 nb (2 * m') c f a)
    (hbut : ∀ b < nb, ∀ r < m',
      a' (b * (2 * m') + r) = a (b * (2 * m') + r) + zeta1 (nb + b) * a (b * (2 * m') + m' + r) ∧
      a' (b * (2 * m') + m' + r)
        = a (b * (2 * m') + r) - zeta1 (nb + b) * a (b * (2 * m') + m' + r)) :
    State zeta1 (2 * nb) m' c f a' :=
  State_ct zeta1_sq hnb1 hnb hst hbut

/-- One CT layer, at `q₂`. -/
theorem State_ct_q2 {nb m' : ℕ} (hnb1 : 1 ≤ nb) (hnb : 2 * nb ≤ 256)
    {c : ZMod 10753} {f a a' : ℕ → ZMod 10753}
    (hst : State zeta2 nb (2 * m') c f a)
    (hbut : ∀ b < nb, ∀ r < m',
      a' (b * (2 * m') + r) = a (b * (2 * m') + r) + zeta2 (nb + b) * a (b * (2 * m') + m' + r) ∧
      a' (b * (2 * m') + m' + r)
        = a (b * (2 * m') + r) - zeta2 (nb + b) * a (b * (2 * m') + m' + r)) :
    State zeta2 (2 * nb) m' c f a' :=
  State_ct zeta2_sq hnb1 hnb hst hbut

/-- **Lanewise product = negacyclic product, at `q₁`.** -/
theorem State_leaf_mul_q1 {f g a b : ℕ → ZMod 7681}
    (ha : State zeta1 256 1 1 f a) (hb : State zeta1 256 1 1 g b) :
    State zeta1 256 1 1 (nconv f g) (fun n => a n * b n) :=
  State_leaf_mul zeta1_sq ha hb

/-- **Lanewise product = negacyclic product, at `q₂`.** -/
theorem State_leaf_mul_q2 {f g a b : ℕ → ZMod 10753}
    (ha : State zeta2 256 1 1 f a) (hb : State zeta2 256 1 1 g b) :
    State zeta2 256 1 1 (nconv f g) (fun n => a n * b n) :=
  State_leaf_mul zeta2_sq ha hb

end Kopis.Properties
