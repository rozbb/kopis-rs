/-
  # Kopis/Neon/NttBarrettIter.lean — the re-centring pass between the transposed levels.

  Six levels in, `ntt_block` re-centres before the last two.  At that point the group is in
  transposed form, so the pass runs over `v.iter_mut()` rather than over a range of block
  indices — which makes it the one loop in this region that needs the `IterMut` framing rather
  than another instance of `NttTransposed.lean`'s shape.

  ## The framing, and the one place it differs from `CbdGeneric.lean`'s

  `Kopis/Neon/CbdGeneric.lean`'s `cbd_loop3_spec` is the model: an `IterMut` loop is specified by
  three predicates on the accumulated `back` closure — it preserves the length, it has already
  written the entries below `iter.i`, and it leaves the entries at or above `iter.i` alone.  The
  induction threads those three through each step, extending `back` with one more write.

  What does not transfer is the *indexing*.  `cbd_loop3_spec` writes `slice.val[j]!`, which needs
  `Inhabited`, and `Vec128` has none — it is an opaque extracted type and Lean has no proof it is
  inhabited, since every axiom producing a `Vec128` already takes one as an argument.  So the
  predicates below are stated through `sAt`, a bounds-carrying accessor in the style of `vAt`,
  and each carries its bound as an *explicit argument* rather than deriving it in the statement.
  That is not merely neater: a `(by omega)` inside the statement cannot see the length fact,
  which is proved in a sibling conjunct.

  Aeneas supplies `Slice.getElem_Nat_setAtNat_{eq,ne}` without an `Inhabited` constraint, which
  is what makes `sAt_setAtNat` go through; the `getElem!` versions beside them do not apply here.
-/
import Kopis.Neon.NttTransposed
import Kopis.Neon.CbdGeneric

open Aeneas Aeneas.Std Result
open RustKopisNeon
open RustKopisNeon.backend.neon.intrinsics

namespace Kopis.Neon

set_option maxHeartbeats 1000000

/-- `Slice::iter_mut` starts at 0 and hands back the slice.  Replicated here for this
extraction's constants, as `Kopis/Neon/CbdGeneric.lean` replicates the two `next` step specs. -/
theorem iter_mut_spec {T : Type} (s : Slice T) :
    core.slice.Slice.iter_mut s ⦃ p =>
      p.1.slice = s ∧ p.1.i = 0 ∧ ∀ it', p.2 it' = it'.slice ⦄ := by
  simp [core.slice.Slice.iter_mut]

/-- Element `j` of a slice of vectors.  `Vec128` has no `Inhabited` instance and cannot be given
one, so this replaces `getElem!` throughout the `IterMut` framing. -/
def sAt (s : Slice Vec128) (j : ℕ) (h : j < s.val.length) : Vec128 := s.val[j]'h

theorem sAt_congr (s : Slice Vec128) {a b : ℕ} (ha : a < s.val.length) (hb : b < s.val.length)
    (h : a = b) : sAt s a ha = sAt s b hb := by subst h; rfl

/-- Writing element `i` leaves the others alone. -/
theorem sAt_setAtNat (s : Slice Vec128) (i : ℕ) (x : Vec128) (j : ℕ)
    (hj : j < (s.setAtNat i x).val.length) (hj' : j < s.val.length) :
    sAt (s.setAtNat i x) j hj = if j = i then x else sAt s j hj' := by
  unfold sAt
  by_cases h : j = i
  · subst h
    rw [Slice.getElem_Nat_setAtNat_eq s j x (by simpa [Slice.length] using hj'), if_pos rfl]
  · rw [Slice.getElem_Nat_setAtNat_ne s i j x ⟨Ne.symm h, by simpa [Slice.length] using hj'⟩,
      if_neg h]

/-- **The transposed group's re-centring pass.**  Every vector of the group comes out with
`2·|r| < q`, so `|r| ≤ (q−1)/2` — which is the bound the last two levels start from. -/
theorem ntt_barrett_iter_bnd (iter : core.slice.iter.IterMut Vec128)
    (back : core.slice.iter.IterMut Vec128 → core.slice.iter.IterMut Vec128)
    (bm round qv : Vec128) (Q M : ℤ)
    (hQ : ∀ i < 8, (lane16 qv i).toInt = Q) (hM : ∀ i < 8, (lane16 bm i).toInt = M)
    (hRnd : ∀ i < 8, (lane16 round i).toInt = 2 ^ 10)
    (hQpos : 0 < Q) (hQlt : Q < 2 ^ 14) (hQodd : ¬ (2 ∣ Q))
    (hMpos : 0 < M) (hMlt : M < 2 ^ 15) (hD : |2 ^ 27 - Q * M| ≤ 2047)
    (h_len8 : iter.slice.val.length = 8) (h_iter_i : iter.i ≤ 8)
    (hback_len : ∀ (im : core.slice.iter.IterMut Vec128),
      im.slice.val.length = 8 → (back im).slice.val.length = 8)
    (hback_writes : ∀ (im : core.slice.iter.IterMut Vec128)
      (_him : im.slice.val.length = 8) (j : ℕ) (_hj : j < iter.i)
      (hb : j < (back im).slice.val.length),
        VecBnd (sAt (back im).slice j hb) ((Q - 1) / 2))
    (hback_rest : ∀ (im : core.slice.iter.IterMut Vec128)
      (_him : im.slice.val.length = 8) (j : ℕ) (_hge : iter.i ≤ j)
      (hb : j < (back im).slice.val.length) (hb' : j < im.slice.val.length),
        sAt (back im).slice j hb = sAt im.slice j hb') :
    backend.neon.ntt.ntt_block_loop1_loop1 iter back qv bm round
      ⦃ (r : core.slice.iter.IterMut Vec128 ×
             (core.slice.iter.IterMut Vec128 → core.slice.iter.IterMut Vec128)) =>
          r.1.slice.val.length = 8 ∧
          ∀ (im : core.slice.iter.IterMut Vec128), im.slice.val.length = 8 →
            (r.2 im).slice.val.length = 8 ∧
            ∀ (j : ℕ) (hj : j < (r.2 im).slice.val.length),
              VecBnd (sAt (r.2 im).slice j hj) ((Q - 1) / 2) ⦄ := by
  unfold backend.neon.ntt.ntt_block_loop1_loop1
  by_cases hlt : iter.i < iter.slice.len
  · let* ⟨ o, iter1, next_back, h_all ⟩ ← CbdGeneric.iter_mut_next_spec
    obtain ⟨ho, hit2_slice, hit2_i, hnb_none, hnb_some⟩ := h_all
    rw [ho]
    simp only []
    have hii : iter.i < 8 := by
      have h := hlt
      rw [← h_len8]
      simpa [Slice.len, Slice.length] using h
    apply WP.spec_bind (barrett_lane_spec _ bm round qv Q M hQ hM hRnd hQpos hQlt hQodd
      hMpos hMlt hD)
    intro slot1 hslot1
    have hslotb : VecBnd slot1 ((Q - 1) / 2) := by
      intro i hi
      have := (hslot1 i hi).2
      omega
    have hnbs : ∀ im : core.slice.iter.IterMut Vec128,
        (next_back im (some slot1)).slice = im.slice.setAtNat iter.i slot1 := by
      intro im
      rw [hnb_some im slot1]
    have hlen' : ∀ (im : core.slice.iter.IterMut Vec128), im.slice.val.length = 8 →
        (next_back im (some slot1)).slice.val.length = 8 := by
      intro im him
      rw [hnbs im]
      simpa [Slice.setAtNat] using him
    apply WP.spec_mono (ntt_barrett_iter_bnd iter1
      (fun im => back (next_back im (some slot1))) bm round qv Q M hQ hM hRnd hQpos hQlt hQodd
      hMpos hMlt hD (by rw [hit2_slice]; exact h_len8) (by omega)
      (fun im him => hback_len _ (hlen' im him))
      (by
        intro im him j hj hb
        by_cases hje : j = iter.i
        · have hbm : j < (next_back im (some slot1)).slice.val.length := by
            rw [hlen' im him]; omega
          rw [hback_rest (next_back im (some slot1)) (hlen' im him) j (by omega) hb hbm]
          have hset : ∀ (h1 : j < (im.slice.setAtNat iter.i slot1).val.length),
              sAt (next_back im (some slot1)).slice j hbm
                = sAt (im.slice.setAtNat iter.i slot1) j h1 := by
            intro h1
            simp only [hnbs im]
          rw [hset (by rw [← hnbs im]; exact hbm),
            sAt_setAtNat im.slice iter.i slot1 j _ (by omega), if_pos hje]
          exact hslotb
        · exact hback_writes (next_back im (some slot1)) (hlen' im him) j (by omega) hb)
      (by
        intro im him j hge hb hb'
        have hbm : j < (next_back im (some slot1)).slice.val.length := by
          rw [hlen' im him]; omega
        rw [hback_rest (next_back im (some slot1)) (hlen' im him) j (by omega) hb hbm]
        have hset : ∀ (h1 : j < (im.slice.setAtNat iter.i slot1).val.length),
            sAt (next_back im (some slot1)).slice j hbm
              = sAt (im.slice.setAtNat iter.i slot1) j h1 := by
          intro h1
          simp only [hnbs im]
        rw [hset (by rw [← hnbs im]; exact hbm),
          sAt_setAtNat im.slice iter.i slot1 j _ hb', if_neg (by omega)]))
    rintro ⟨r1, r2⟩ hr
    exact hr
  · let* ⟨ o, iter1, next_back, h_all ⟩ ← CbdGeneric.iter_mut_next_spec_none
    obtain ⟨ho, hit_eq, hnb⟩ := h_all
    rw [ho]
    have hi8 : iter.i = 8 := by
      have hnot : ¬ (iter.i < 8) := by
        have h := hlt
        rw [← h_len8]
        simpa [Slice.len, Slice.length] using h
      omega
    refine (WP.spec_ok _).mpr ⟨by rw [hit_eq]; exact h_len8, fun im him => ?_⟩
    simp only [hnb]
    exact ⟨hback_len im him, fun j hj => hback_writes im him j
      (by rw [hback_len im him] at hj; omega) hj⟩

end Kopis.Neon
