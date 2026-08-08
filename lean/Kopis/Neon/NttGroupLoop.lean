/-
  # Kopis/Neon/NttGroupLoop.lean — the four transposed groups.

  `ntt_block`'s second half runs over `g < 4`, and each iteration is seven proved pieces in a
  row: load the group and transpose it, take the `len = 4` ψ pair, run that level, re-centre the
  whole group, run `len = 2` in its two halves, run `len = 1`, and store the group back.

  The only new plumbing is the round trip the re-centring pass needs — `Array.to_slice_mut`,
  `Slice::iter_mut`, and the two `back` closures that reassemble the array.  It is the same
  pattern `Kopis/Properties/MatrixArith.lean` uses, and it is what lets
  `Kopis/Neon/NttBarrettIter.lean`'s slice-level statement be read back as a statement about the
  group's vectors.

  `BlockBnd` on the block and `VecBnd` on the group's vectors meet at `load_group_spec` /
  `store_group_spec`'s `64g + 8m + k` indexing.
-/
import Kopis.Neon.NttBarrettIter

open Aeneas Aeneas.Std Result
open RustKopisNeon
open RustKopisNeon.backend.neon.intrinsics

namespace Kopis.Neon

set_option maxHeartbeats 2000000

/-- The ψ pair a table accessor hands over, with the two properties every butterfly needs. -/
def PsiOk (z zq : Vec128) (Q Zb : ℤ) : Prop :=
  (∀ i < 8, |(lane16 z i).toInt| ≤ Zb) ∧
  (∀ i < 8, (2 ^ 16 : ℤ) ∣ ((lane16 zq i).toInt * Q - (lane16 z i).toInt))

/-- **The four transposed groups.**  Each is `load_group`, the three short levels with a
re-centring pass after the first, and `store_group`. -/
theorem ntt_group_bnd (SECOND : Bool) (b : Array I16 256#usize) (qv bm round : Vec128)
    (Q Zb M Ain Amid Ar A2 A3 : ℤ)
    (hQ : ∀ i < 8, (lane16 qv i).toInt = Q) (hQpos : 0 < Q) (hQ14 : Q < 2 ^ 14)
    (hQodd : ¬ (2 ∣ Q)) (hZb : Zb ≤ 2 ^ 14)
    (hM : ∀ i < 8, (lane16 bm i).toInt = M) (hMpos : 0 < M) (hMlt : M < 2 ^ 15)
    (hD : |2 ^ 27 - Q * M| ≤ 2047)
    (hRnd : ∀ i < 8, (lane16 round i).toInt = 2 ^ 10)
    (htbl4 : ∀ kk : Usize, kk.val < 4 → ∃ z zq : Vec128,
        backend.neon.ntt.fwd4 SECOND kk = ok (z, zq) ∧ PsiOk z zq Q Zb)
    (htbl2 : ∀ kk : Usize, kk.val < 8 → ∃ z zq : Vec128,
        backend.neon.ntt.fwd2 SECOND kk = ok (z, zq) ∧ PsiOk z zq Q Zb)
    (htbl1 : ∀ kk : Usize, kk.val < 16 → ∃ z zq : Vec128,
        backend.neon.ntt.fwd1 SECOND kk = ok (z, zq) ∧ PsiOk z zq Q Zb)
    (hAin : 0 ≤ Ain) (hAr : 0 ≤ Ar) (hA2 : 0 ≤ A2) (hreset : (Q - 1) / 2 ≤ Ar)
    (hs4 : LevelStep Q Zb Ain (Amid - Ain))
    (hs2 : LevelStep Q Zb Ar (A2 - Ar))
    (hs1 : LevelStep Q Zb A2 (A3 - A2))
    (iter : core.ops.range.Range Usize) (hend : iter.«end».val = 4)
    (hb : ∀ p < 256, 64 * iter.start.val ≤ p → |(b.val[p]!).val| ≤ Ain) :
    backend.neon.ntt.ntt_block_loop1 SECOND iter b qv bm round
      ⦃ (r : Array I16 256#usize) => ∀ p < 256,
          if 64 * iter.start.val ≤ p then |(r.val[p]!).val| ≤ A3
          else (r.val[p]!).val = (b.val[p]!).val ⦄ := by
  unfold backend.neon.ntt.ntt_block_loop1
  by_cases hlt : iter.start.val < iter.«end».val
  · let* ⟨ o, iter1, ho, hstart', hend' ⟩ ← core.iter.range.IteratorRange.next_Usize_some_spec
    rw [ho]
    simp only
    have hg4 : iter.start.val < 4 := by omega
    -- 1. load and transpose
    apply WP.spec_bind (load_group_spec b iter.start hg4)
    intro v hvload
    have hvb : ∀ k (hk : k < 8), VecBnd (vAt v k hk) Ain := by
      intro k hk m hm
      rw [hvload k hk m hm]
      exact hb _ (by omega) (by omega)
    -- 2. the `len = 4` ψ pair, and 3. that level
    obtain ⟨z4, zq4, hz4e, hz4, hzq4⟩ := htbl4 iter.start hg4
    rw [hz4e, bind_tc_ok]
    apply WP.spec_bind (ntt_len4_bnd qv z4 zq4 Q Zb Ain (Amid - Ain) hQ hQpos (by omega)
      hz4 hZb hzq4 hAin hs4.1 hs4.2.1 hs4.2.2 v ⟨0#usize, 4#usize⟩ rfl
      (fun j hj _ => hvb j hj))
    intro v1 hv1
    have hv1b : ∀ j (hj : j < 8), VecBnd (vAt v1 j hj) Amid := by
      intro j hj
      have := hv1 j hj
      rw [if_pos (by unfold pend4; scalar_tac)] at this
      exact this.mono (by omega)
    -- 4. the slice round trip, and 5. the re-centring pass
    let* ⟨ s, to_back, hs_val, hto_back ⟩ ← Array.to_slice_mut_spec
    let* ⟨ iter2, imb, hi2_slice, hi2_zero, hi2_back ⟩ ← iter_mut_spec
    have hs_len : s.val.length = 8 := by rw [hs_val]; have := v1.property; scalar_tac
    have hi2_len : iter2.slice.val.length = 8 := by rw [hi2_slice]; exact hs_len
    apply WP.spec_bind (ntt_barrett_iter_bnd iter2 (fun im1 => im1) bm round qv Q M hQ hM hRnd
      hQpos hQ14 hQodd hMpos hMlt hD hi2_len (by rw [hi2_zero]; omega)
      (fun im him => him)
      (fun im him j hj hbnd => absurd hj (by rw [hi2_zero]; omega))
      (fun im him j _ hbnd hbnd' => rfl))
    rintro ⟨im, bk⟩ ⟨him_len, hbk⟩
    obtain ⟨hbk_len, hbk_bnd⟩ := hbk im him_len
    -- 6. reassemble the array from the slice
    show (do let v2 ← backend.neon.ntt.ntt_block_loop1_loop2 SECOND
                        { start := 0#usize, «end» := 2#usize } qv iter.start
                        (to_back (imb (bk im)))
             let v3 ← backend.neon.ntt.ntt_block_loop1_loop3 SECOND
                        { start := 0#usize, «end» := 4#usize } qv iter.start v2
             let (b1, _) ← backend.neon.ntt.store_group b iter.start v3
             backend.neon.ntt.ntt_block_loop1 SECOND iter1 b1 qv bm round)
        ⦃ (r : Array I16 256#usize) => ∀ p < 256,
            if 64 * iter.start.val ≤ p then |(r.val[p]!).val| ≤ A3
            else (r.val[p]!).val = (b.val[p]!).val ⦄
    set a := to_back (imb (bk im)) with ha_def
    have ha_val : a.val = (bk im).slice.val := by
      rw [ha_def, hi2_back, hto_back]
      exact Std.Array.from_slice_val _ _ (by rw [hbk_len]; simp)
    have hab : ∀ j (hj : j < 8), VecBnd (vAt a j hj) Ar := by
      intro j hj
      have hjb : j < (bk im).slice.val.length := by rw [hbk_len]; omega
      have := hbk_bnd j hjb
      have heq : vAt a j hj = sAt (bk im).slice j hjb := by
        unfold vAt sAt
        exact List.getElem_of_eq ha_val _
      rw [heq]
      exact this.mono hreset
    -- 7. `len = 2` in its two halves
    apply WP.spec_bind (ntt_len2_outer_bnd SECOND qv Q Zb Ar (A2 - Ar) hQ hQpos (by omega) hZb
      hAr hs2.1 hs2.2.1 hs2.2.2 (fun kk hkk => by
        obtain ⟨z, zq, he, hp⟩ := htbl2 kk hkk
        exact ⟨z, zq, he, hp.1, hp.2⟩)
      iter.start hg4 a ⟨0#usize, 2#usize⟩ rfl (fun j hj _ => hab j hj))
    intro v2 hv2
    have hv2b : ∀ j (hj : j < 8), VecBnd (vAt v2 j hj) A2 := by
      intro j hj
      have := hv2 j hj
      rw [if_pos (by scalar_tac)] at this
      exact this.mono (by omega)
    -- 8. `len = 1`
    apply WP.spec_bind (ntt_len1_bnd SECOND qv Q Zb A2 (A3 - A2) hQ hQpos (by omega) hZb
      hA2 hs1.1 hs1.2.1 hs1.2.2 (fun kk hkk => by
        obtain ⟨z, zq, he, hp⟩ := htbl1 kk hkk
        exact ⟨z, zq, he, hp.1, hp.2⟩)
      iter.start hg4 v2 ⟨0#usize, 4#usize⟩ rfl (fun j hj _ => hv2b j hj))
    intro v3 hv3
    have hv3b : ∀ j (hj : j < 8), VecBnd (vAt v3 j hj) A3 := by
      intro j hj
      have := hv3 j hj
      rw [if_pos (by unfold pend1; scalar_tac)] at this
      exact this.mono (by omega)
    -- 9. store the group back
    apply WP.spec_bind (store_group_spec b iter.start hg4 v3)
    rintro ⟨b1, unused⟩ hb1
    show backend.neon.ntt.ntt_block_loop1 SECOND iter1 b1 qv bm round
        ⦃ (r : Array I16 256#usize) => ∀ p < 256,
            if 64 * iter.start.val ≤ p then |(r.val[p]!).val| ≤ A3
            else (r.val[p]!).val = (b.val[p]!).val ⦄
    -- 10. and the remaining groups
    apply WP.spec_mono (ntt_group_bnd SECOND b1 qv bm round Q Zb M Ain Amid Ar A2 A3 hQ hQpos
      hQ14 hQodd hZb hM hMpos hMlt hD hRnd htbl4 htbl2 htbl1 hAin hAr hA2 hreset hs4 hs2 hs1
      iter1 (by rw [hend']; exact hend) (by
        intro p hp hge
        have := hb1 p hp
        rw [if_neg (by scalar_tac)] at this
        rw [this]
        exact hb p hp (by omega)))
    intro r hr p hp
    have hrp := hr p hp
    by_cases hge : 64 * iter.start.val ≤ p
    · rw [if_pos hge]
      by_cases hge1 : 64 * iter1.start.val ≤ p
      · rw [if_pos hge1] at hrp
        exact hrp
      · rw [if_neg hge1] at hrp
        rw [hrp]
        have := hb1 p hp
        rw [if_pos (by scalar_tac)] at this
        rw [this]
        exact hv3b _ (by omega) _ (by omega)
    · rw [if_neg hge]
      rw [if_neg (by omega)] at hrp
      rw [hrp]
      have := hb1 p hp
      rw [if_neg (by scalar_tac)] at this
      exact this
  · let* ⟨ o, iter1, hnone, _ ⟩ ← core.iter.range.IteratorRange.next_Usize_none_spec
    rw [hnone]
    refine (WP.spec_ok _).mpr (fun p hp => ?_)
    rw [if_neg (by scalar_tac)]
termination_by 4 - iter.start.val
decreasing_by scalar_decr_tac

/-! ## The whole forward transform

The constant setup, the five whole-vector levels, the four transposed groups, and the final
re-centring pass.  The result is *centred* — `|a| ≤ (q−1)/2` — which is what the pointwise step
and the CRT combine downstream assume of it.

The chain is threaded through as parameters, and `growth_q1` / `growth_q2` supply it:
`(q−1)/2 → A1 → A2 → A3` (re-centre) `→ A4 → A5` for the whole-vector half, then
`A5 → Amid` (re-centre) `→ A6 → A7` for the transposed half. -/

theorem ntt_block_bnd (SECOND : Bool) (b : Array I16 256#usize) (Q Zb M : ℤ)
    (A1 A2 A3 A4 A5 Amid Ar A6 A7 : ℤ)
    (qc mc rc : I16)
    (hq : backend.crt.q SECOND = ok qc) (hqv : qc.val = Q)
    (hm : backend.crt.barrett_m SECOND = ok mc) (hmv : mc.val = M)
    (hrc : (1#i16 : I16) <<< (10#i32 : Std.I32) = ok rc) (hrcv : rc.val = 2 ^ 10)
    (hQpos : 0 < Q) (hQ14 : Q < 2 ^ 14) (hQodd : ¬ (2 ∣ Q)) (hZb : Zb ≤ 2 ^ 14)
    (hMpos : 0 < M) (hMlt : M < 2 ^ 15) (hD : |2 ^ 27 - Q * M| ≤ 2047)
    (hzeta : ∀ kk : Usize, kk.val < 256 → ∃ zi zqi : I16,
        backend.crt.zeta SECOND kk = ok zi ∧ backend.crt.zeta_q SECOND kk = ok zqi ∧
        |zi.val| ≤ Zb ∧ (2 ^ 16 : ℤ) ∣ (zqi.val * Q - zi.val))
    (htbl4 : ∀ kk : Usize, kk.val < 4 → ∃ z zq : Vec128,
        backend.neon.ntt.fwd4 SECOND kk = ok (z, zq) ∧ PsiOk z zq Q Zb)
    (htbl2 : ∀ kk : Usize, kk.val < 8 → ∃ z zq : Vec128,
        backend.neon.ntt.fwd2 SECOND kk = ok (z, zq) ∧ PsiOk z zq Q Zb)
    (htbl1 : ∀ kk : Usize, kk.val < 16 → ∃ z zq : Vec128,
        backend.neon.ntt.fwd1 SECOND kk = ok (z, zq) ∧ PsiOk z zq Q Zb)
    (hA1 : 0 ≤ A1) (hA2 : 0 ≤ A2) (hA4 : 0 ≤ A4) (hA5 : 0 ≤ A5) (hAr : 0 ≤ Ar)
    (hA6 : 0 ≤ A6)
    (hresetA : (Q - 1) / 2 ≤ (Q - 1) / 2) (hresetR : (Q - 1) / 2 ≤ Ar)
    (hs0 : LevelStep Q Zb ((Q - 1) / 2) (A1 - (Q - 1) / 2))
    (hs1 : LevelStep Q Zb A1 (A2 - A1)) (hs2 : LevelStep Q Zb A2 (A3 - A2))
    (hs3 : LevelStep Q Zb ((Q - 1) / 2) (A4 - (Q - 1) / 2))
    (hs4 : LevelStep Q Zb A4 (A5 - A4))
    (hg4 : LevelStep Q Zb A5 (Amid - A5))
    (hg2 : LevelStep Q Zb Ar (A6 - Ar)) (hg1 : LevelStep Q Zb A6 (A7 - A6))
    (hb : BlockBnd b ((Q - 1) / 2)) :
    backend.neon.ntt.ntt_block SECOND b
      ⦃ (r : Array I16 256#usize) => BlockBnd r ((Q - 1) / 2) ⦄ := by
  have hQ0 : 0 ≤ (Q - 1) / 2 := by omega
  unfold backend.neon.ntt.ntt_block
  rw [hq, bind_tc_ok]
  obtain ⟨qv, hqe, hql⟩ := dup_n_s16_spec qc
  rw [hqe, bind_tc_ok, hm, bind_tc_ok]
  obtain ⟨bm, hbme, hbml⟩ := dup_n_s16_spec mc
  rw [hbme, bind_tc_ok]
  have hsh : backend.crt.BARRETT_SH - (1#i32 : Std.I32) = ok (10#i32 : Std.I32) := by
    simp only [backend.crt.BARRETT_SH]
    rfl
  rw [hsh, bind_tc_ok, hrc, bind_tc_ok]
  obtain ⟨round, hre, hrl⟩ := dup_n_s16_spec rc
  rw [hre, bind_tc_ok]
  have hQv : ∀ i < 8, (lane16 qv i).toInt = Q := by
    intro i hi; rw [hql i hi]; exact hqv
  have hMv : ∀ i < 8, (lane16 bm i).toInt = M := by
    intro i hi; rw [hbml i hi]; exact hmv
  have hRv : ∀ i < 8, (lane16 round i).toInt = 2 ^ 10 := by
    intro i hi; rw [hrl i hi]; exact hrcv
  -- the five whole-vector levels
  apply WP.spec_bind (ntt_horizontal_bnd SECOND b qv bm round Q Zb M ((Q - 1) / 2) A1 A2 A3
    A4 A5 hQv hQpos hQ14 hQodd hZb hMv hMpos hMlt hD hRv hzeta hQ0 hA1 hA2 hA4 hresetA
    hs0 hs1 hs2 hs3 hs4 hb)
  intro b1 hb1
  -- the four transposed groups
  apply WP.spec_bind (ntt_group_bnd SECOND b1 qv bm round Q Zb M A5 Amid Ar A6 A7 hQv hQpos
    hQ14 hQodd hZb hMv hMpos hMlt hD hRv htbl4 htbl2 htbl1 hA5 hAr hA6 hresetR hg4 hg2 hg1
    ⟨0#usize, 4#usize⟩ rfl (fun p hp _ => hb1 p hp))
  intro b2 hb2
  -- and the final re-centring pass
  apply WP.spec_mono (barrett_block_spec b2 bm round qv Q M hQv hMv hRv hQpos hQ14 hQodd
    hMpos hMlt hD)
  rintro r ⟨hrb, -⟩
  exact hrb

/-! ## The table hypotheses, discharged

Each of the three transposed levels wants its ψ pair to be centred and Montgomery-paired.  Both
follow from facts already proved about the *literal* ζ arrays — `zetas_q1_centred_idx` and
`q1_inv_unit` in `Kopis/Neon/Tables.lean` — plus `tblZq_mont`, without touching the 512 entries
again.  The only per-level content is that the index stays inside the array, which is the closed
form `fwd4Idx` / `fwd2Idx` / `fwd1Idx` gives. -/

theorem psiOk_fwd4 (SECOND : Bool) (Q Zb : ℤ)
    (hz : ∀ k < 256, |((zetasOf SECOND).val[k]!).val| ≤ Zb)
    (hinv : (2 ^ 16 : ℤ) ∣ ((qinvOf SECOND).val * Q - 1))
    (kk : Usize) (hkk : kk.val < 4) :
    ∃ z zq : Vec128, backend.neon.ntt.fwd4 SECOND kk = ok (z, zq) ∧ PsiOk z zq Q Zb := by
  obtain ⟨r, hr, hp⟩ := WP.spec_imp_exists (fwd4_spec SECOND kk (by scalar_tac))
  refine ⟨r.1, r.2, by rw [hr], fun i hi => ?_, fun i hi => ?_⟩
  · rw [(hp i hi).1]
    unfold tblZ
    split
    · rw [abs_neg]; exact hz _ (by unfold fwd4Idx; omega)
    · exact hz _ (by unfold fwd4Idx; omega)
  · rw [(hp i hi).1, (hp i hi).2]
    exact tblZq_mont _ _ _ hinv

theorem psiOk_fwd2 (SECOND : Bool) (Q Zb : ℤ)
    (hz : ∀ k < 256, |((zetasOf SECOND).val[k]!).val| ≤ Zb)
    (hinv : (2 ^ 16 : ℤ) ∣ ((qinvOf SECOND).val * Q - 1))
    (kk : Usize) (hkk : kk.val < 8) :
    ∃ z zq : Vec128, backend.neon.ntt.fwd2 SECOND kk = ok (z, zq) ∧ PsiOk z zq Q Zb := by
  obtain ⟨r, hr, hp⟩ := WP.spec_imp_exists (fwd2_spec SECOND kk (by scalar_tac))
  refine ⟨r.1, r.2, by rw [hr], fun i hi => ?_, fun i hi => ?_⟩
  · rw [(hp i hi).1]
    unfold tblZ
    split
    · rw [abs_neg]; exact hz _ (by unfold fwd2Idx; omega)
    · exact hz _ (by unfold fwd2Idx; omega)
  · rw [(hp i hi).1, (hp i hi).2]
    exact tblZq_mont _ _ _ hinv

theorem psiOk_fwd1 (SECOND : Bool) (Q Zb : ℤ)
    (hz : ∀ k < 256, |((zetasOf SECOND).val[k]!).val| ≤ Zb)
    (hinv : (2 ^ 16 : ℤ) ∣ ((qinvOf SECOND).val * Q - 1))
    (kk : Usize) (hkk : kk.val < 16) :
    ∃ z zq : Vec128, backend.neon.ntt.fwd1 SECOND kk = ok (z, zq) ∧ PsiOk z zq Q Zb := by
  obtain ⟨r, hr, hp⟩ := WP.spec_imp_exists (fwd1_spec SECOND kk (by scalar_tac))
  refine ⟨r.1, r.2, by rw [hr], fun i hi => ?_, fun i hi => ?_⟩
  · rw [(hp i hi).1]
    unfold tblZ
    split
    · rw [abs_neg]; exact hz _ (by unfold fwd1Idx; omega)
    · exact hz _ (by unfold fwd1Idx; omega)
  · rw [(hp i hi).1, (hp i hi).2]
    exact tblZq_mont _ _ _ hinv

/-! ## The forward transform at the two primes

`growth_q1` and `growth_q2` supply the chain; everything else is evaluation of the literal
constants.  The runs are `(q−1)/2 → · → · → ·` three long, re-centred, three long again for the
whole-vector half, and then `· → ·` re-centred `→ · → ·` for the transposed half — the
"runs of 3, 3, 2" schedule `ntt.rs` documents. -/

/-- The rounding constant the Barrett pass adds: `1 << (BARRETT_SH − 1)`. -/
theorem round_const : (1#i16 : I16) <<< (10#i32 : Std.I32) = ok 1024#i16 := by
  simp only [HShiftLeft.hShiftLeft, IScalar.shiftLeft_IScalar, IScalar.shiftLeft]
  rw [if_pos (by decide), if_pos (by decide)]
  rfl

/-- **The forward transform on the first prime leaves the block centred.** -/
theorem ntt_block_bnd_q1 (b : Array I16 256#usize) (hb : BlockBnd b 3840) :
    backend.neon.ntt.ntt_block false b
      ⦃ (r : Array I16 256#usize) => BlockBnd r 3840 ⦄ := by
  obtain ⟨s0, s1, s2, -, -⟩ := growth_q1
  have hQ : ((7681 : ℤ) - 1) / 2 = 3840 := by norm_num
  have hzc : ∀ k < 256, |((zetasOf false).val[k]!).val| ≤ 3840 := by
    intro k hk
    simp only [zetasOf, Bool.false_eq_true, if_false]
    exact zetas_q1_centred_idx k hk
  have hinv : (2 ^ 16 : ℤ) ∣ ((qinvOf false).val * 7681 - 1) := by
    simp only [qinvOf, Bool.false_eq_true, if_false]
    rw [← q1_val]
    exact q1_inv_unit
  refine ntt_block_bnd false b 7681 3840 17474 7906 12210 16766 7906 12210 16766 3840 7906
    12210 backend.crt.Q1 backend.crt.Q1_BARRETT_M 1024#i16
    (by simp only [backend.crt.q, Bool.false_eq_true, if_false]) q1_val
    (by simp only [backend.crt.barrett_m, Bool.false_eq_true, if_false]) q1_m_val
    round_const (by decide)
    (by norm_num) (by norm_num) (by decide) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
    (fun kk hkk => zeta_table_ok_q1 kk hkk |>.imp (fun zi h => h.imp (fun zqi h' =>
      ⟨h'.1, h'.2.1, h'.2.2.1, h'.2.2.2.1⟩)))
    (psiOk_fwd4 false 7681 3840 hzc hinv) (psiOk_fwd2 false 7681 3840 hzc hinv)
    (psiOk_fwd1 false 7681 3840 hzc hinv)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (le_refl _) (by norm_num)
    (by simpa using s0) (by simpa using s1) (by simpa using s2)
    (by simpa using s0) (by simpa using s1)
    (by simpa using s2) (by simpa using s0) (by simpa using s1)
    (by simpa using hb)

/-- **The forward transform on the second prime — the binding one leaves the block centred.** -/
theorem ntt_block_bnd_q2 (b : Array I16 256#usize) (hb : BlockBnd b 5376) :
    backend.neon.ntt.ntt_block true b
      ⦃ (r : Array I16 256#usize) => BlockBnd r 5376 ⦄ := by
  obtain ⟨s0, s1, s2, -, -⟩ := growth_q2
  have hQ : ((10753 : ℤ) - 1) / 2 = 5376 := by norm_num
  have hzc : ∀ k < 256, |((zetasOf true).val[k]!).val| ≤ 5376 := by
    intro k hk
    simp only [zetasOf, if_true]
    exact zetas_q2_centred_idx k hk
  have hinv : (2 ^ 16 : ℤ) ∣ ((qinvOf true).val * 10753 - 1) := by
    simp only [qinvOf, if_true]
    rw [← q2_val]
    exact q2_inv_unit
  refine ntt_block_bnd true b 10753 5376 12482 11194 17489 24301 11194 17489 24301 5376 11194
    17489 backend.crt.Q2 backend.crt.Q2_BARRETT_M 1024#i16
    (by simp only [backend.crt.q, if_true]) q2_val
    (by simp only [backend.crt.barrett_m, if_true]) q2_m_val
    round_const (by decide)
    (by norm_num) (by norm_num) (by decide) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
    (fun kk hkk => zeta_table_ok_q2 kk hkk |>.imp (fun zi h => h.imp (fun zqi h' =>
      ⟨h'.1, h'.2.1, h'.2.2.1, h'.2.2.2.1⟩)))
    (psiOk_fwd4 true 10753 5376 hzc hinv) (psiOk_fwd2 true 10753 5376 hzc hinv)
    (psiOk_fwd1 true 10753 5376 hzc hinv)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (le_refl _) (by norm_num)
    (by simpa using s0) (by simpa using s1) (by simpa using s2)
    (by simpa using s0) (by simpa using s1)
    (by simpa using s2) (by simpa using s0) (by simpa using s1)
    (by simpa using hb)

end Kopis.Neon
