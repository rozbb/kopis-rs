/-
  # Kopis/Neon/NttGroupLoop.lean — the four groups, and the whole forward transform.

  `ntt_block`'s second half runs over `g < 4`, and each iteration carries one group of eight
  vectors through *six* levels without touching memory: load the eight vectors in coefficient
  order, run levels 2, 3 and 4 as ordinary vector pairings with a broadcast ζ, transpose, run
  levels 5, 6 and 7 as vertical butterflies with a per-lane ψ, transpose back, and store.  Two
  re-centring passes sit inside that — after level 3 and after level 7 — because both reductions
  the schedule calls for now happen to a group that is already in registers.

  The only unusual plumbing is the round trip each re-centring pass needs — `Array.to_slice_mut`,
  `Slice::iter_mut`, and the two `back` closures that reassemble the array.  It is the same
  pattern `Kopis/Properties/MatrixArith.lean` uses, and it is what lets
  `Kopis/Neon/NttBarrettIter.lean`'s slice-level statement be read back as a statement about the
  group's vectors.

  `fromVec` on the window and `VecBnd` on the group's vectors meet at the load prologue's and
  `store_vecs_spec`'s `8·base + 64g + 8j + m` indexing.
-/
import Kopis.Neon.NttBarrettIter

open Aeneas Aeneas.Std Result
open RustKopisNeon
open RustKopisNeon.backend.neon.intrinsics

namespace Kopis.Neon

set_option maxHeartbeats 4000000
set_option maxRecDepth 4000

/-- The ψ pair a table accessor hands over, with the two properties every butterfly needs. -/
def PsiOk (z zq : Vec128) (Q Zb : ℤ) : Prop :=
  (∀ i < 8, |(lane16 z i).toInt| ≤ Zb) ∧
  (∀ i < 8, (2 ^ 16 : ℤ) ∣ ((lane16 zq i).toInt * Q - (lane16 z i).toInt))

/-- A transpose permutes lanes between vectors, so a bound on every vector of a group survives
it. -/
theorem transpose8_bnd (v : Array Vec128 8#usize) (B : ℤ)
    (hv : ∀ j (hj : j < 8), VecBnd (vAt v j hj) B) :
    backend.neon.ntt.transpose8 v
      ⦃ (r : Array Vec128 8#usize) => ∀ j (hj : j < 8), VecBnd (vAt r j hj) B ⦄ := by
  apply WP.spec_mono (transpose8_spec v)
  intro r hr j hj m hm
  rw [hr j hj m hm]
  exact hv m hm j hj

/-- **The four groups.**  Each is a load, six levels with a re-centring pass after the second and
after the sixth, two transposes, and a store. -/
theorem ntt_group_bnd (SECOND : Bool) {N : Usize} (b : Array I16 N) (base : Usize)
    (qv bm round : Vec128)
    (Q Zb M Ain A3 A4 Ar B1 B2 B3 B4 : ℤ)
    (hQ : ∀ i < 8, (lane16 qv i).toInt = Q) (hQpos : 0 < Q) (hQ14 : Q < 2 ^ 14)
    (hQodd : ¬ (2 ∣ Q)) (hZb : Zb ≤ 2 ^ 14)
    (hM : ∀ i < 8, (lane16 bm i).toInt = M) (hMpos : 0 < M) (hMlt : M < 2 ^ 15)
    (hD : |2 ^ 27 - Q * M| ≤ 2047)
    (hRnd : ∀ i < 8, (lane16 round i).toInt = 2 ^ 10)
    (hN : 8 * base.val + 256 ≤ N.val)
    (hzeta : ∀ kk : Usize, kk.val < 256 → ∃ zi zqi : I16,
        backend.crt.zeta SECOND kk = ok zi ∧ backend.crt.zeta_q SECOND kk = ok zqi ∧
        |zi.val| ≤ Zb ∧ (2 ^ 16 : ℤ) ∣ (zqi.val * Q - zi.val))
    (htbl4 : ∀ kk : Usize, kk.val < 4 → ∃ z zq : Vec128,
        backend.neon.ntt.fwd4 SECOND kk = ok (z, zq) ∧ PsiOk z zq Q Zb)
    (htbl2 : ∀ kk : Usize, kk.val < 8 → ∃ z zq : Vec128,
        backend.neon.ntt.fwd2 SECOND kk = ok (z, zq) ∧ PsiOk z zq Q Zb)
    (htbl1 : ∀ kk : Usize, kk.val < 16 → ∃ z zq : Vec128,
        backend.neon.ntt.fwd1 SECOND kk = ok (z, zq) ∧ PsiOk z zq Q Zb)
    (hAin : 0 ≤ Ain) (hA3 : 0 ≤ A3) (hAr : 0 ≤ Ar)
    (hB1 : 0 ≤ B1) (hB2 : 0 ≤ B2) (hB3 : 0 ≤ B3) (hreset : (Q - 1) / 2 ≤ Ar)
    (hs2 : LevelStep Q Zb Ain (A3 - Ain)) (hs3 : LevelStep Q Zb A3 (A4 - A3))
    (hs4 : LevelStep Q Zb Ar (B1 - Ar)) (hs5 : LevelStep Q Zb B1 (B2 - B1))
    (hs6 : LevelStep Q Zb B2 (B3 - B2)) (hs7 : LevelStep Q Zb B3 (B4 - B3))
    (iter : core.ops.range.Range Usize) (hend : iter.«end».val = 4)
    (hb : ∀ p < N.val, fromVec base.val (8 * iter.start.val) p → |(b.val[p]!).val| ≤ Ain) :
    backend.neon.ntt.ntt_block_loop1 SECOND iter b base qv bm round
      ⦃ (r : Array I16 N) => ∀ p < N.val,
          if fromVec base.val (8 * iter.start.val) p then |(r.val[p]!).val| ≤ (Q - 1) / 2
          else (r.val[p]!).val = (b.val[p]!).val ⦄ := by
  have hNmax : N.val ≤ Usize.max := by scalar_tac
  -- a window fits, so the address space is at least a window wide; `omega` needs to be told
  have hbig : 256 ≤ Usize.max := by omega
  have hQ0 : (0 : ℤ) ≤ (Q - 1) / 2 := by omega
  unfold backend.neon.ntt.ntt_block_loop1
  by_cases hlt : iter.start.val < iter.«end».val
  · let* ⟨ o, iter1, ho, hstart', hend' ⟩ ← core.iter.range.IteratorRange.next_Usize_some_spec
    rw [ho]
    simp only
    have hg4 : iter.start.val < 4 := by omega
    -- 1. the eight vectors of the group, in coefficient order
    let* ⟨ i, hi ⟩ ← Std.Usize.mul_spec (x := 8#usize) (y := iter.start) (by scalar_tac)
    have hiv : i.val = 8 * iter.start.val := by scalar_tac
    let* ⟨ j0, hj0 ⟩ ← Std.Usize.add_spec (x := base) (y := i) (by omega)
    obtain ⟨w0, hw0, hw0l⟩ := load_i16_gen b j0 (by omega)
    rw [hw0, bind_tc_ok]
    let* ⟨ e1, he1 ⟩ ← Std.Usize.add_spec (x := base) (y := i) (by omega)
    let* ⟨ j1, hj1 ⟩ ← Std.Usize.add_spec (x := e1) (y := 1#usize) (by scalar_tac)
    obtain ⟨w1, hw1, hw1l⟩ := load_i16_gen b j1 (by omega)
    rw [hw1, bind_tc_ok]
    let* ⟨ e2, he2 ⟩ ← Std.Usize.add_spec (x := base) (y := i) (by omega)
    let* ⟨ j2, hj2 ⟩ ← Std.Usize.add_spec (x := e2) (y := 2#usize) (by scalar_tac)
    obtain ⟨w2, hw2, hw2l⟩ := load_i16_gen b j2 (by omega)
    rw [hw2, bind_tc_ok]
    let* ⟨ e3, he3 ⟩ ← Std.Usize.add_spec (x := base) (y := i) (by omega)
    let* ⟨ j3, hj3 ⟩ ← Std.Usize.add_spec (x := e3) (y := 3#usize) (by scalar_tac)
    obtain ⟨w3, hw3, hw3l⟩ := load_i16_gen b j3 (by omega)
    rw [hw3, bind_tc_ok]
    let* ⟨ e4, he4 ⟩ ← Std.Usize.add_spec (x := base) (y := i) (by omega)
    let* ⟨ j4, hj4 ⟩ ← Std.Usize.add_spec (x := e4) (y := 4#usize) (by scalar_tac)
    obtain ⟨w4, hw4, hw4l⟩ := load_i16_gen b j4 (by omega)
    rw [hw4, bind_tc_ok]
    let* ⟨ e5, he5 ⟩ ← Std.Usize.add_spec (x := base) (y := i) (by omega)
    let* ⟨ j5, hj5 ⟩ ← Std.Usize.add_spec (x := e5) (y := 5#usize) (by scalar_tac)
    obtain ⟨w5, hw5, hw5l⟩ := load_i16_gen b j5 (by omega)
    rw [hw5, bind_tc_ok]
    let* ⟨ e6, he6 ⟩ ← Std.Usize.add_spec (x := base) (y := i) (by omega)
    let* ⟨ j6, hj6 ⟩ ← Std.Usize.add_spec (x := e6) (y := 6#usize) (by scalar_tac)
    obtain ⟨w6, hw6, hw6l⟩ := load_i16_gen b j6 (by omega)
    rw [hw6, bind_tc_ok]
    let* ⟨ e7, he7 ⟩ ← Std.Usize.add_spec (x := base) (y := i) (by omega)
    let* ⟨ j7, hj7 ⟩ ← Std.Usize.add_spec (x := e7) (y := 7#usize) (by scalar_tac)
    obtain ⟨w7, hw7, hw7l⟩ := load_i16_gen b j7 (by omega)
    rw [hw7, bind_tc_ok]
    set v : Array Vec128 8#usize := Array.make 8#usize [w0, w1, w2, w3, w4, w5, w6, w7] with hvdef
    have hvb : ∀ j (hj : j < 8), VecBnd (vAt v j hj) Ain := by
      intro j hj m hm
      have e0 : ∀ h, vAt v 0 h = w0 := fun _ => rfl
      have e1' : ∀ h, vAt v 1 h = w1 := fun _ => rfl
      have e2' : ∀ h, vAt v 2 h = w2 := fun _ => rfl
      have e3' : ∀ h, vAt v 3 h = w3 := fun _ => rfl
      have e4' : ∀ h, vAt v 4 h = w4 := fun _ => rfl
      have e5' : ∀ h, vAt v 5 h = w5 := fun _ => rfl
      have e6' : ∀ h, vAt v 6 h = w6 := fun _ => rfl
      have e7' : ∀ h, vAt v 7 h = w7 := fun _ => rfl
      rcases show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 from by omega with
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [e0, e1', e2', e3', e4', e5', e6', e7'] <;>
      [ (rw [hw0l m hm]); (rw [hw1l m hm]); (rw [hw2l m hm]); (rw [hw3l m hm]);
        (rw [hw4l m hm]); (rw [hw5l m hm]); (rw [hw6l m hm]); (rw [hw7l m hm]) ] <;>
      exact hb _ (by omega) (by unfold fromVec; omega)
    -- 2. level 2: one broadcast ζ for the whole group, pairing `i` with `i + 4`
    let* ⟨ k2, hk2 ⟩ ← Std.Usize.add_spec (x := 4#usize) (y := iter.start) (by scalar_tac)
    obtain ⟨zi, zqi, hzi, hzqi, hzib, hzqib⟩ := hzeta k2 (by scalar_tac)
    rw [hzi, bind_tc_ok]
    obtain ⟨z2, hz2, hz2l⟩ := dup_n_s16_spec zi
    rw [hz2, bind_tc_ok, hzqi, bind_tc_ok]
    obtain ⟨zq2, hzq2, hzq2l⟩ := dup_n_s16_spec zqi
    rw [hzq2, bind_tc_ok]
    have hz2v : ∀ i < 8, |(lane16 z2 i).toInt| ≤ Zb := by
      intro i hi'; rw [hz2l i hi']; exact hzib
    have hzq2v : ∀ i < 8, (2 ^ 16 : ℤ) ∣ ((lane16 zq2 i).toInt * Q - (lane16 z2 i).toInt) := by
      intro i hi'; rw [hz2l i hi', hzq2l i hi']; exact hzqib
    apply WP.spec_bind (ntt_len4_bnd qv z2 zq2 Q Zb Ain (A3 - Ain) hQ hQpos (by omega)
      hz2v hZb hzq2v hAin hs2.1 hs2.2.1 hs2.2.2 v ⟨0#usize, 4#usize⟩ rfl
      (fun j hj _ => hvb j hj))
    intro v1 hv1
    have hv1b : ∀ j (hj : j < 8), VecBnd (vAt v1 j hj) A3 := by
      intro j hj
      have := hv1 j hj
      rw [if_pos (by unfold pend4; scalar_tac)] at this
      exact this.mono (by omega)
    -- 3. level 3
    apply WP.spec_bind (ntt_lvl3_bnd SECOND qv Q Zb A3 (A4 - A3) hQ hQpos (by omega) hZb
      hA3 hs3.1 hs3.2.1 hs3.2.2 hzeta iter.start hg4 v1 ⟨0#usize, 2#usize⟩ rfl
      (fun j hj _ => hv1b j hj))
    intro v2 hv2
    have hv2b : ∀ j (hj : j < 8), VecBnd (vAt v2 j hj) A4 := by
      intro j hj
      have := hv2 j hj
      rw [if_pos (by scalar_tac)] at this
      exact this.mono (by omega)
    -- 4. the slice round trip, and the first re-centring pass
    let* ⟨ s, to_back, hs_val, hto_back ⟩ ← Array.to_slice_mut_spec
    let* ⟨ iter2, imb, hi2_slice, hi2_zero, hi2_back ⟩ ← iter_mut_spec
    have hs_len : s.val.length = 8 := by rw [hs_val]; have := v2.property; scalar_tac
    have hi2_len : iter2.slice.val.length = 8 := by rw [hi2_slice]; exact hs_len
    apply WP.spec_bind (ntt_barrett_iter_bnd iter2 (fun im1 => im1) bm round qv Q M hQ hM hRnd
      hQpos hQ14 hQodd hMpos hMlt hD hi2_len (by rw [hi2_zero]; omega)
      (fun im him => him)
      (fun im him j hj hbnd => absurd hj (by rw [hi2_zero]; omega))
      (fun im him j _ hbnd hbnd' => rfl))
    rintro ⟨im, bk⟩ ⟨him_len, hbk⟩
    obtain ⟨hbk_len, hbk_bnd⟩ := hbk im him_len
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
    show (do let v3 ← backend.neon.ntt.ntt_block_loop1_loop3 SECOND
                        { start := 0#usize, «end» := 4#usize } qv iter.start a
             let v4 ← backend.neon.ntt.transpose8 v3
             let (z1, zq1) ← backend.neon.ntt.fwd4 SECOND iter.start
             let v5 ← backend.neon.ntt.ntt_block_loop1_loop4
                        { start := 0#usize, «end» := 4#usize } qv v4 z1 zq1
             let v6 ← backend.neon.ntt.ntt_block_loop1_loop5 SECOND
                        { start := 0#usize, «end» := 2#usize } qv iter.start v5
             let v7 ← backend.neon.ntt.ntt_block_loop1_loop6 SECOND
                        { start := 0#usize, «end» := 4#usize } qv iter.start v6
             let (s2, to_slice_mut_back1) ← lift (Array.to_slice_mut v7)
             let (iter3, iter_mut_back1) ← core.slice.Slice.iter_mut s2
             let (im2, back1) ← backend.neon.ntt.ntt_block_loop1_loop7 iter3 (fun im3 => im3) qv
                                  bm round
             let im3 := back1 im2
             let s3 := iter_mut_back1 im3
             let v8 := to_slice_mut_back1 s3
             let v9 ← backend.neon.ntt.transpose8 v8
             let b1 ← backend.neon.ntt.ntt_block_loop1_loop8
                        { start := 0#usize, «end» := 8#usize } b base iter.start v9
             backend.neon.ntt.ntt_block_loop1 SECOND iter1 b1 base qv bm round)
        ⦃ (r : Array I16 N) => ∀ p < N.val,
            if fromVec base.val (8 * iter.start.val) p then |(r.val[p]!).val| ≤ (Q - 1) / 2
            else (r.val[p]!).val = (b.val[p]!).val ⦄
    -- 5. level 4
    apply WP.spec_bind (ntt_lvl4_bnd SECOND qv Q Zb Ar (B1 - Ar) hQ hQpos (by omega) hZb
      hAr hs4.1 hs4.2.1 hs4.2.2 hzeta iter.start hg4 a ⟨0#usize, 4#usize⟩ rfl
      (fun j hj _ => hab j hj))
    intro v3 hv3
    have hv3b : ∀ j (hj : j < 8), VecBnd (vAt v3 j hj) B1 := by
      intro j hj
      have := hv3 j hj
      rw [if_pos (by unfold pend1; scalar_tac)] at this
      exact this.mono (by omega)
    -- 6. into the transposed view
    apply WP.spec_bind (transpose8_bnd v3 B1 hv3b)
    intro v4 hv4b
    -- 7. `len = 4`
    obtain ⟨z4, zq4, hz4e, hz4, hzq4⟩ := htbl4 iter.start hg4
    rw [hz4e, bind_tc_ok, loop1_loop4_eq]
    apply WP.spec_bind (ntt_len4_bnd qv z4 zq4 Q Zb B1 (B2 - B1) hQ hQpos (by omega)
      hz4 hZb hzq4 hB1 hs5.1 hs5.2.1 hs5.2.2 v4 ⟨0#usize, 4#usize⟩ rfl
      (fun j hj _ => hv4b j hj))
    intro v5 hv5
    have hv5b : ∀ j (hj : j < 8), VecBnd (vAt v5 j hj) B2 := by
      intro j hj
      have := hv5 j hj
      rw [if_pos (by unfold pend4; scalar_tac)] at this
      exact this.mono (by omega)
    -- 8. `len = 2` in its two halves
    apply WP.spec_bind (ntt_len2_outer_bnd SECOND qv Q Zb B2 (B3 - B2) hQ hQpos (by omega) hZb
      hB2 hs6.1 hs6.2.1 hs6.2.2 (fun kk hkk => by
        obtain ⟨z, zq, he, hp⟩ := htbl2 kk hkk
        exact ⟨z, zq, he, hp.1, hp.2⟩)
      iter.start hg4 v5 ⟨0#usize, 2#usize⟩ rfl (fun j hj _ => hv5b j hj))
    intro v6 hv6
    have hv6b : ∀ j (hj : j < 8), VecBnd (vAt v6 j hj) B3 := by
      intro j hj
      have := hv6 j hj
      rw [if_pos (by scalar_tac)] at this
      exact this.mono (by omega)
    -- 9. `len = 1`
    apply WP.spec_bind (ntt_len1_bnd SECOND qv Q Zb B3 (B4 - B3) hQ hQpos (by omega) hZb
      hB3 hs7.1 hs7.2.1 hs7.2.2 (fun kk hkk => by
        obtain ⟨z, zq, he, hp⟩ := htbl1 kk hkk
        exact ⟨z, zq, he, hp.1, hp.2⟩)
      iter.start hg4 v6 ⟨0#usize, 4#usize⟩ rfl (fun j hj _ => hv6b j hj))
    intro v7 hv7
    have hv7b : ∀ j (hj : j < 8), VecBnd (vAt v7 j hj) B4 := by
      intro j hj
      have := hv7 j hj
      rw [if_pos (by unfold pend1; scalar_tac)] at this
      exact this.mono (by omega)
    -- 10. the second re-centring pass, which leaves the group centred
    let* ⟨ s2, to_back2, hs2_val, hto_back2 ⟩ ← Array.to_slice_mut_spec
    let* ⟨ iter3, imb3, hi3_slice, hi3_zero, hi3_back ⟩ ← iter_mut_spec
    have hs2_len : s2.val.length = 8 := by rw [hs2_val]; have := v7.property; scalar_tac
    have hi3_len : iter3.slice.val.length = 8 := by rw [hi3_slice]; exact hs2_len
    rw [loop1_loop7_eq]
    apply WP.spec_bind (ntt_barrett_iter_bnd iter3 (fun im1 => im1) bm round qv Q M hQ hM hRnd
      hQpos hQ14 hQodd hMpos hMlt hD hi3_len (by rw [hi3_zero]; omega)
      (fun im him => him)
      (fun im him j hj hbnd => absurd hj (by rw [hi3_zero]; omega))
      (fun im him j _ hbnd hbnd' => rfl))
    rintro ⟨im2, bk2⟩ ⟨him2_len, hbk2⟩
    obtain ⟨hbk2_len, hbk2_bnd⟩ := hbk2 im2 him2_len
    set a2 := to_back2 (imb3 (bk2 im2)) with ha2_def
    have ha2_val : a2.val = (bk2 im2).slice.val := by
      rw [ha2_def, hi3_back, hto_back2]
      exact Std.Array.from_slice_val _ _ (by rw [hbk2_len]; simp)
    have ha2b : ∀ j (hj : j < 8), VecBnd (vAt a2 j hj) ((Q - 1) / 2) := by
      intro j hj
      have hjb : j < (bk2 im2).slice.val.length := by rw [hbk2_len]; omega
      have := hbk2_bnd j hjb
      have heq : vAt a2 j hj = sAt (bk2 im2).slice j hjb := by
        unfold vAt sAt
        exact List.getElem_of_eq ha2_val _
      rw [heq]
      exact this
    -- 11. back to coefficient order, and out to memory
    apply WP.spec_bind (transpose8_bnd a2 ((Q - 1) / 2) ha2b)
    intro v9 hv9b
    apply WP.spec_bind (store_vecs_spec b base iter.start hg4 hN v9)
    intro b1 hb1
    -- 12. and the remaining groups
    apply WP.spec_mono (ntt_group_bnd SECOND b1 base qv bm round Q Zb M Ain A3 A4 Ar B1 B2 B3 B4
      hQ hQpos hQ14 hQodd hZb hM hMpos hMlt hD hRnd hN hzeta htbl4 htbl2 htbl1 hAin hA3 hAr
      hB1 hB2 hB3 hreset hs2 hs3 hs4 hs5 hs6 hs7 iter1 (by rw [hend']; exact hend) (by
        intro p hp hge
        have := hb1 p hp
        rw [if_neg (by unfold fromVec at hge; omega)] at this
        rw [this]
        exact hb p hp (by unfold fromVec at hge ⊢; omega)))
    intro r hr p hp
    have hrp := hr p hp
    by_cases hge : fromVec base.val (8 * iter.start.val) p
    · rw [if_pos hge]
      by_cases hge1 : fromVec base.val (8 * iter1.start.val) p
      · rw [if_pos hge1] at hrp
        exact hrp
      · rw [if_neg hge1] at hrp
        rw [hrp]
        have := hb1 p hp
        rw [if_pos (by unfold fromVec at hge hge1; omega)] at this
        rw [this]
        exact hv9b _ (by omega) _ (by omega)
    · rw [if_neg hge]
      rw [if_neg (by unfold fromVec at hge ⊢; omega)] at hrp
      rw [hrp]
      have := hb1 p hp
      rw [if_neg (by unfold fromVec at hge; omega)] at this
      exact this
  · let* ⟨ o, iter1, hnone, _ ⟩ ← core.iter.range.IteratorRange.next_Usize_none_spec
    rw [hnone]
    refine (WP.spec_ok _).mpr (fun p hp => ?_)
    rw [if_neg (by unfold fromVec; scalar_tac)]
termination_by 4 - iter.start.val
decreasing_by scalar_decr_tac

/-! ## The whole forward transform

The constant setup, the two whole-vector levels, and the four groups.  The result is *centred* —
`|a| ≤ (q−1)/2` — which is what the pointwise step and the CRT combine downstream assume of it,
and everything outside this prime's window is untouched, which is what lets the two halves of an
`NttElem` be transformed one after the other into the same buffer.

The chain is threaded through as parameters, and `growth_q1` / `growth_q2` supply it: it is the
same four-level chain `(q−1)/2 → A1 → A2 → A3 → A4` twice, once for levels 0–3 and once for
levels 4–7, with a re-centring pass between and after. -/

theorem ntt_block_bnd (SECOND : Bool) {N : Usize} (b : Array I16 N) (base : Usize)
    (Q Zb M A1 A2 A3 A4 : ℤ)
    (qc mc rc : I16)
    (hq : backend.crt.q SECOND = ok qc) (hqv : qc.val = Q)
    (hm : backend.crt.barrett_m SECOND = ok mc) (hmv : mc.val = M)
    (hrc : (1#i16 : I16) <<< (10#i32 : Std.I32) = ok rc) (hrcv : rc.val = 2 ^ 10)
    (hQpos : 0 < Q) (hQ14 : Q < 2 ^ 14) (hQodd : ¬ (2 ∣ Q)) (hZb : Zb ≤ 2 ^ 14)
    (hMpos : 0 < M) (hMlt : M < 2 ^ 15) (hD : |2 ^ 27 - Q * M| ≤ 2047)
    (hN : 8 * base.val + 256 ≤ N.val)
    (hzeta : ∀ kk : Usize, kk.val < 256 → ∃ zi zqi : I16,
        backend.crt.zeta SECOND kk = ok zi ∧ backend.crt.zeta_q SECOND kk = ok zqi ∧
        |zi.val| ≤ Zb ∧ (2 ^ 16 : ℤ) ∣ (zqi.val * Q - zi.val))
    (htbl4 : ∀ kk : Usize, kk.val < 4 → ∃ z zq : Vec128,
        backend.neon.ntt.fwd4 SECOND kk = ok (z, zq) ∧ PsiOk z zq Q Zb)
    (htbl2 : ∀ kk : Usize, kk.val < 8 → ∃ z zq : Vec128,
        backend.neon.ntt.fwd2 SECOND kk = ok (z, zq) ∧ PsiOk z zq Q Zb)
    (htbl1 : ∀ kk : Usize, kk.val < 16 → ∃ z zq : Vec128,
        backend.neon.ntt.fwd1 SECOND kk = ok (z, zq) ∧ PsiOk z zq Q Zb)
    (hA1 : 0 ≤ A1) (hA2 : 0 ≤ A2) (hA3 : 0 ≤ A3)
    (hs0 : LevelStep Q Zb ((Q - 1) / 2) (A1 - (Q - 1) / 2))
    (hs1 : LevelStep Q Zb A1 (A2 - A1)) (hs2 : LevelStep Q Zb A2 (A3 - A2))
    (hs3 : LevelStep Q Zb A3 (A4 - A3))
    (hb : ∀ p < N.val, fromVec base.val 0 p → |(b.val[p]!).val| ≤ (Q - 1) / 2) :
    backend.neon.ntt.ntt_block SECOND b base
      ⦃ (r : Array I16 N) => ∀ p < N.val,
          if fromVec base.val 0 p then |(r.val[p]!).val| ≤ (Q - 1) / 2
          else (r.val[p]!).val = (b.val[p]!).val ⦄ := by
  have hQ0 : (0 : ℤ) ≤ (Q - 1) / 2 := by omega
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
  -- levels 0 and 1
  apply WP.spec_bind (ntt_horizontal_bnd SECOND b base qv Q Zb ((Q - 1) / 2) A1 A2
    hQv hQpos hQ14 hZb hN hzeta hQ0 hA1 hs0 hs1 hb)
  intro b1 hb1
  -- levels 2 to 7, a group at a time
  apply WP.spec_mono (ntt_group_bnd SECOND b1 base qv bm round Q Zb M A2 A3 A4 ((Q - 1) / 2)
    A1 A2 A3 A4 hQv hQpos hQ14 hQodd hZb hMv hMpos hMlt hD hRv hN hzeta htbl4 htbl2 htbl1
    hA2 hA3 hQ0 hA1 hA2 hA3 (le_refl _) hs2 hs3 hs0 hs1 hs2 hs3
    ⟨0#usize, 4#usize⟩ rfl (by
      intro p hp hin
      have := hb1 p hp
      rw [if_pos (show fromVec base.val 0 p by unfold fromVec at hin ⊢; scalar_tac)] at this
      exact this))
  intro r hr p hp
  have hrp := hr p hp
  have hb1p := hb1 p hp
  by_cases hin : fromVec base.val 0 p
  · rw [if_pos hin]
    rw [if_pos (show fromVec base.val (8 * (0#usize : Usize).val) p by
      unfold fromVec at hin ⊢; scalar_tac)] at hrp
    exact hrp
  · rw [if_neg hin]
    rw [if_neg (show ¬ fromVec base.val (8 * (0#usize : Usize).val) p by
      unfold fromVec at hin ⊢; scalar_tac)] at hrp
    rw [if_neg hin] at hb1p
    rw [hrp, hb1p]

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
constants.  Both runs are four levels long, from a centred block, re-centred at the end of
each — the "runs of 4, 4" schedule `ntt.rs` documents. -/

/-- The rounding constant the Barrett pass adds: `1 << (BARRETT_SH − 1)`. -/
theorem round_const : (1#i16 : I16) <<< (10#i32 : Std.I32) = ok 1024#i16 := by
  simp only [HShiftLeft.hShiftLeft, IScalar.shiftLeft_IScalar, IScalar.shiftLeft]
  rw [if_pos (by decide), if_pos (by decide)]
  rfl

/-- **The forward transform on the first prime leaves its window centred**, and everything
outside the window untouched. -/
theorem ntt_block_bnd_q1 {N : Usize} (b : Array I16 N) (base : Usize)
    (hN : 8 * base.val + 256 ≤ N.val)
    (hb : ∀ p < N.val, fromVec base.val 0 p → |(b.val[p]!).val| ≤ 3840) :
    backend.neon.ntt.ntt_block false b base
      ⦃ (r : Array I16 N) => ∀ p < N.val,
          if fromVec base.val 0 p then |(r.val[p]!).val| ≤ 3840
          else (r.val[p]!).val = (b.val[p]!).val ⦄ := by
  obtain ⟨s0, s1, s2, s3, -, -⟩ := growth_q1
  have hzc : ∀ k < 256, |((zetasOf false).val[k]!).val| ≤ 3840 := by
    intro k hk
    simp only [zetasOf, Bool.false_eq_true, if_false]
    exact zetas_q1_centred_idx k hk
  have hinv : (2 ^ 16 : ℤ) ∣ ((qinvOf false).val * 7681 - 1) := by
    simp only [qinvOf, Bool.false_eq_true, if_false]
    rw [← q1_val]
    exact q1_inv_unit
  have hQ : ((7681 : ℤ) - 1) / 2 = 3840 := by norm_num
  apply WP.spec_mono (ntt_block_bnd false b base 7681 3840 17474 7906 12210 16766 21589
    backend.crt.Q1 backend.crt.Q1_BARRETT_M 1024#i16
    (by simp only [backend.crt.q, Bool.false_eq_true, if_false]) q1_val
    (by simp only [backend.crt.barrett_m, Bool.false_eq_true, if_false]) q1_m_val
    round_const (by decide)
    (by norm_num) (by norm_num) (by decide) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hN
    (fun kk hkk => zeta_table_ok_q1 kk hkk |>.imp (fun zi h => h.imp (fun zqi h' =>
      ⟨h'.1, h'.2.1, h'.2.2.1, h'.2.2.2.1⟩)))
    (psiOk_fwd4 false 7681 3840 hzc hinv) (psiOk_fwd2 false 7681 3840 hzc hinv)
    (psiOk_fwd1 false 7681 3840 hzc hinv)
    (by norm_num) (by norm_num) (by norm_num)
    (by rw [hQ]; simpa using s0) (by simpa using s1) (by simpa using s2) (by simpa using s3)
    (by rw [hQ]; exact hb))
  intro r hr p hp
  have := hr p hp
  rwa [hQ] at this

/-- **The forward transform on the second prime — the binding one — leaves its window
centred.** -/
theorem ntt_block_bnd_q2 {N : Usize} (b : Array I16 N) (base : Usize)
    (hN : 8 * base.val + 256 ≤ N.val)
    (hb : ∀ p < N.val, fromVec base.val 0 p → |(b.val[p]!).val| ≤ 5376) :
    backend.neon.ntt.ntt_block true b base
      ⦃ (r : Array I16 N) => ∀ p < N.val,
          if fromVec base.val 0 p then |(r.val[p]!).val| ≤ 5376
          else (r.val[p]!).val = (b.val[p]!).val ⦄ := by
  obtain ⟨s0, s1, s2, s3, -, -⟩ := growth_q2
  have hzc : ∀ k < 256, |((zetasOf true).val[k]!).val| ≤ 5376 := by
    intro k hk
    simp only [zetasOf, if_true]
    exact zetas_q2_centred_idx k hk
  have hinv : (2 ^ 16 : ℤ) ∣ ((qinvOf true).val * 10753 - 1) := by
    simp only [qinvOf, if_true]
    rw [← q2_val]
    exact q2_inv_unit
  have hQ : ((10753 : ℤ) - 1) / 2 = 5376 := by norm_num
  apply WP.spec_mono (ntt_block_bnd true b base 10753 5376 12482 11194 17489 24301 31671
    backend.crt.Q2 backend.crt.Q2_BARRETT_M 1024#i16
    (by simp only [backend.crt.q, if_true]) q2_val
    (by simp only [backend.crt.barrett_m, if_true]) q2_m_val
    round_const (by decide)
    (by norm_num) (by norm_num) (by decide) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hN
    (fun kk hkk => zeta_table_ok_q2 kk hkk |>.imp (fun zi h => h.imp (fun zqi h' =>
      ⟨h'.1, h'.2.1, h'.2.2.1, h'.2.2.2.1⟩)))
    (psiOk_fwd4 true 10753 5376 hzc hinv) (psiOk_fwd2 true 10753 5376 hzc hinv)
    (psiOk_fwd1 true 10753 5376 hzc hinv)
    (by norm_num) (by norm_num) (by norm_num)
    (by rw [hQ]; simpa using s0) (by simpa using s1) (by simpa using s2) (by simpa using s3)
    (by rw [hQ]; exact hb))
  intro r hr p hp
  have := hr p hp
  rwa [hQ] at this

end Kopis.Neon
