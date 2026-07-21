/-
  # Kopis/Properties/MatrixArith.lean — Correspondence proofs for matrix-level
  arithmetic (`Matrix X Y = [[RingElem; Y]; X]`).

  Each matrix op is a *nested* `IterMut` loop (outer over rows, inner over the
  `RingElem`s of a row) that applies the corresponding `RingElem` primitive
  (proved in `RingArith.lean`).  Stated entrywise at the physical `2¹⁶`
  abstraction (`toRingElem`), matching `RingArith`; the logical `2¹³`/`2¹⁰`
  moduli are recovered at composition time via `Polynomial.coerce`.

  The inner loop returns `(iter, back)` unapplied; the outer computes `p.2 p.1`,
  which equals what a directly-applied 1-D loop returns — so the inner spec is a
  `RingElem`-valued copy of the 1-D `IterMut` framing from `RingArith`.
-/
import Kopis.Properties.RingArith
open Aeneas Aeneas.Std Result kopis_kem
namespace Kopis.Properties

set_option maxHeartbeats 2000000
set_option maxRecDepth 4000

/-- Inner loop of `Matrix.shift_right`: shift every `RingElem` of one row.
Returns `(iter, back)` unapplied; the outer computes `p.2 p.1`, which equals what
a directly-applied 1-D loop would return. `!`-indexed to avoid bound-proof blowup
on the deep `RingElem` type. -/
theorem shift_right_loop0_loop0_spec
    (iter : core.slice.iter.IterMut RingElem)
    (back : core.slice.iter.IterMut RingElem → core.slice.iter.IterMut RingElem)
    (shift : Usize) (hshift : shift.val < 16)
    (orig_slice : Slice RingElem)
    (h_slice : iter.slice = orig_slice)
    (h_iter_i : iter.i ≤ orig_slice.length)
    (hback_len : ∀ (im : core.slice.iter.IterMut RingElem),
      im.slice.length = orig_slice.length → (back im).slice.length = orig_slice.length)
    (hback_writes : ∀ (im : core.slice.iter.IterMut RingElem)
      (_him : im.slice.length = orig_slice.length)
      (j : Nat) (_hj : j < iter.i),
        toRingElem ((back im).slice.val[j]!)
          = Spec.Kopis.Polynomial.shiftRight (toRingElem (orig_slice.val[j]!)) shift.val)
    (hback_rest : ∀ (im : core.slice.iter.IterMut RingElem)
      (_him : im.slice.length = orig_slice.length)
      (j : Nat) (_hj_ge : iter.i ≤ j) (_hj_lt : j < orig_slice.length),
        (back im).slice.val[j]! = im.slice.val[j]!) :
    arithmetic.matrix_arith.Matrix.shift_right_loop0_loop0 iter back shift
      ⦃ (p : core.slice.iter.IterMut RingElem ×
              (core.slice.iter.IterMut RingElem → core.slice.iter.IterMut RingElem)) =>
          (p.2 p.1).slice.length = orig_slice.length ∧
            ∀ (j : Nat) (_hj : j < orig_slice.length),
              toRingElem ((p.2 p.1).slice.val[j]!)
                = Spec.Kopis.Polynomial.shiftRight (toRingElem (orig_slice.val[j]!)) shift.val ⦄ := by
  unfold arithmetic.matrix_arith.Matrix.shift_right_loop0_loop0
  by_cases hlt : iter.i < iter.slice.len
  · let* ⟨ o, iter1, next_back, h_all ⟩ ← iter_mut_next_spec
    obtain ⟨ho, hit2_slice, hit2_i, _, hsome_set⟩ := h_all
    rw [ho]
    simp only []
    have hi_pe : iter.slice.length = orig_slice.length := by rw [h_slice]
    have hi_lt : iter.i < orig_slice.length := by rw [← hi_pe]; scalar_tac
    let* ⟨ elem1, helem1 ⟩ ← shift_right_spec
    apply WP.spec_mono
      (shift_right_loop0_loop0_spec iter1 (fun im => back (next_back im (some elem1))) shift hshift
        orig_slice (by rw [hit2_slice, h_slice]) (by rw [hit2_i]; omega) ?len ?writes ?rest)
    case len =>
      intro im him
      have him_set : (next_back im (some elem1)).slice.length = orig_slice.length := by
        rw [hsome_set]; simp only; rw [Slice.setAtNat_length]; exact him
      exact hback_len _ him_set
    case writes =>
      intro im him j hj
      rw [hit2_i] at hj
      have him_set : (next_back im (some elem1)).slice.length = orig_slice.length := by
        rw [hsome_set]; simp only; rw [Slice.setAtNat_length]; exact him
      by_cases hji : j = iter.i
      · subst hji
        have hrest := hback_rest (next_back im (some elem1)) him_set iter.i (le_refl _) hi_lt
        have hkey : (back (next_back im (some elem1))).slice.val[iter.i]! = elem1 := by
          rw [hrest, hsome_set]
          exact Slice.getElem!_Nat_setAtNat_eq _ _ _ (by rw [him]; exact hi_lt)
        rw [hkey, helem1]
        -- toRingElem elem = toRingElem (orig.val[iter.i]!) where elem = iter.slice[iter.i]
        have hvaleq : iter.slice.val = orig_slice.val := by rw [h_slice]
        have hb : iter.i < orig_slice.val.length := hi_lt
        have helem : iter.slice[iter.i] = orig_slice.val[iter.i]! := by
          rw [getElem!_pos orig_slice.val iter.i hb]
          exact List.getElem_of_eq hvaleq _
        exact congrArg (fun x => Spec.Kopis.Polynomial.shiftRight (toRingElem x) shift.val) helem
      · have hjlt : j < iter.i := by omega
        exact hback_writes (next_back im (some elem1)) him_set j hjlt
    case rest =>
      intro im him j hj_ge hj_lt
      rw [hit2_i] at hj_ge
      have him_set : (next_back im (some elem1)).slice.length = orig_slice.length := by
        rw [hsome_set]; simp only; rw [Slice.setAtNat_length]; exact him
      have hrest := hback_rest (next_back im (some elem1)) him_set j (by omega) hj_lt
      rw [hrest, hsome_set]
      exact Slice.getElem!_Nat_setAtNat_ne _ _ _ _ (by omega)
    intro r hpost; exact hpost
  · have hge : iter.i ≥ iter.slice.len := by scalar_tac
    have hi_eq : iter.i = orig_slice.length := by
      have hpe : iter.slice.length = orig_slice.length := by rw [h_slice]
      have : iter.slice.len.val = orig_slice.length := by
        rw [← hpe]; simp [Slice.len, Slice.length]
      scalar_tac
    let* ⟨ o, iter1, next_back, h_all ⟩ ← iter_mut_next_spec_none
    obtain ⟨ho, hit2_eq, hsome_back⟩ := h_all
    rw [ho]
    have hbi : next_back iter1 none = iter := (hsome_back iter1 none).trans hit2_eq
    show (back (next_back iter1 none)).slice.length = orig_slice.length ∧
        ∀ (j : Nat), j < orig_slice.length →
          toRingElem ((back (next_back iter1 none)).slice.val[j]!)
            = Spec.Kopis.Polynomial.shiftRight (toRingElem (orig_slice.val[j]!)) shift.val
    refine ⟨by rw [hbi]; exact hback_len iter (by rw [h_slice]), ?_⟩
    intro j hj
    rw [hbi]
    exact hback_writes iter (by rw [h_slice]) j (hi_eq ▸ hj)
  termination_by iter.slice.len.val - iter.i
  decreasing_by scalar_decr_tac

/-- **Outer loop** of `Matrix.shift_right`: shift every `RingElem` of every row in
`[iter.i, X)`.  Per-row body = `shift_right_loop0_loop0`. -/
theorem shift_right_loop0_spec {Y : Usize}
    (iter : core.slice.iter.IterMut (Array arithmetic.ring_arith.RingElem Y))
    (back : core.slice.iter.IterMut (Array arithmetic.ring_arith.RingElem Y) →
            core.slice.iter.IterMut (Array arithmetic.ring_arith.RingElem Y))
    (shift : Usize) (hshift : shift.val < 16)
    (orig_slice : Slice (Array arithmetic.ring_arith.RingElem Y))
    (h_slice : iter.slice = orig_slice)
    (h_iter_i : iter.i ≤ orig_slice.length)
    (hback_len : ∀ (im : core.slice.iter.IterMut (Array arithmetic.ring_arith.RingElem Y)),
      im.slice.length = orig_slice.length → (back im).slice.length = orig_slice.length)
    (hback_writes : ∀ (im : core.slice.iter.IterMut (Array arithmetic.ring_arith.RingElem Y))
      (_him : im.slice.length = orig_slice.length)
      (i : Nat) (_hi : i < iter.i) (j : Nat) (_hj : j < Y.val),
        toRingElem (((back im).slice.val[i]!).val[j]!)
          = Spec.Kopis.Polynomial.shiftRight (toRingElem ((orig_slice.val[i]!).val[j]!)) shift.val)
    (hback_rest : ∀ (im : core.slice.iter.IterMut (Array arithmetic.ring_arith.RingElem Y))
      (_him : im.slice.length = orig_slice.length)
      (i : Nat) (_hi_ge : iter.i ≤ i) (_hi_lt : i < orig_slice.length),
        (back im).slice.val[i]! = im.slice.val[i]!) :
    arithmetic.matrix_arith.Matrix.shift_right_loop0 iter back shift
      ⦃ (r : core.slice.iter.IterMut (Array arithmetic.ring_arith.RingElem Y)) =>
          r.slice.length = orig_slice.length ∧
            ∀ (i : Nat) (_hi : i < orig_slice.length) (j : Nat) (_hj : j < Y.val),
              toRingElem (((r.slice.val[i]!).val[j]!))
                = Spec.Kopis.Polynomial.shiftRight (toRingElem ((orig_slice.val[i]!).val[j]!)) shift.val ⦄ := by
  unfold arithmetic.matrix_arith.Matrix.shift_right_loop0
  by_cases hlt : iter.i < iter.slice.len
  · let* ⟨ o, iter1, next_back, h_all ⟩ ← iter_mut_next_spec
    obtain ⟨ho, hit2_slice, hit2_i, _, hsome_set⟩ := h_all
    rw [ho]
    simp only []
    have hi_pe : iter.slice.length = orig_slice.length := by rw [h_slice]
    have hi_lt : iter.i < orig_slice.length := by rw [← hi_pe]; scalar_tac
    let* ⟨ s, to_slice_mut_back, hs_val, hto_back ⟩ ← Array.to_slice_mut_spec
    let* ⟨ iter2, iter_mut_back, h_i2_slice, h_i2_zero, h_i2_back ⟩ ← iter_mut_spec
    let* ⟨ inner_im, inner_back, hinner_len, hinner_writes ⟩ ←
      shift_right_loop0_loop0_spec iter2 (fun x => x) shift hshift iter2.slice rfl
        (by rw [h_i2_zero]; exact Nat.zero_le _)
        (fun _ him => him)
        (fun _ _ j hj => by rw [h_i2_zero] at hj; omega)
        (fun _ _ _ _ _ => rfl)
    -- lengths
    have hrow_len : (iter.slice[iter.i]).val.length = Y.val := (iter.slice[iter.i]).property
    have hs_len : s.length = Y.val := by rw [Slice.length, hs_val]; exact hrow_len
    have hi2s_len : iter2.slice.length = Y.val := by rw [h_i2_slice]; exact hs_len
    have hib_len : (inner_back inner_im).slice.length = Y.val := hinner_len.trans hi2s_len
    -- the new row `a`
    set a := to_slice_mut_back (iter_mut_back (inner_back inner_im)) with ha_def
    have ha_val : a.val = (inner_back inner_im).slice.val := by
      rw [ha_def, h_i2_back, hto_back]
      exact Std.Array.from_slice_val _ _ hib_len
    apply WP.spec_mono
      (shift_right_loop0_spec iter1 (fun im1 => back (next_back im1 (some a))) shift hshift
        orig_slice (by rw [hit2_slice, h_slice]) (by rw [hit2_i]; omega) ?len ?writes ?rest)
    case len =>
      intro im him
      have him_set : (next_back im (some a)).slice.length = orig_slice.length := by
        rw [hsome_set]; simp only; rw [Slice.setAtNat_length]; exact him
      exact hback_len _ him_set
    case writes =>
      intro im him i hi j hj
      rw [hit2_i] at hi
      have him_set : (next_back im (some a)).slice.length = orig_slice.length := by
        rw [hsome_set]; simp only; rw [Slice.setAtNat_length]; exact him
      by_cases hii : i = iter.i
      · subst hii
        have hrest := hback_rest (next_back im (some a)) him_set iter.i (le_refl _) hi_lt
        have hkey : (back (next_back im (some a))).slice.val[iter.i]! = a := by
          rw [hrest, hsome_set]
          exact Slice.getElem!_Nat_setAtNat_eq _ _ _ (by rw [him]; exact hi_lt)
        rw [hkey]
        -- toRingElem (a.val[j]!) = shiftRight (toRingElem (orig.val[iter.i]!.val[j]!)) shift
        rw [show a.val[j]! = (inner_back inner_im).slice.val[j]! from
              congrArg (fun l => l[j]!) ha_val]
        rw [hinner_writes j (by rw [hi2s_len]; exact hj)]
        -- iter2.slice.val[j]! = s.val[j]! = row.val[j]! = orig.val[iter.i]!.val[j]!
        have hb : iter.i < orig_slice.val.length := hi_lt
        have hrow_eq : iter.slice[iter.i] = orig_slice.val[iter.i]! := by
          rw [getElem!_pos orig_slice.val iter.i hb]
          exact List.getElem_of_eq (show iter.slice.val = orig_slice.val by rw [h_slice]) _
        have hvaleq : iter2.slice.val = (orig_slice.val[iter.i]!).val := by
          rw [h_i2_slice, hs_val]; exact congrArg (·.val) hrow_eq
        rw [show iter2.slice.val[j]! = (orig_slice.val[iter.i]!).val[j]! from
              congrArg (fun l => l[j]!) hvaleq]
      · have hilt : i < iter.i := by omega
        exact hback_writes (next_back im (some a)) him_set i hilt j hj
    case rest =>
      intro im him i hi_ge hi_lt2
      rw [hit2_i] at hi_ge
      have him_set : (next_back im (some a)).slice.length = orig_slice.length := by
        rw [hsome_set]; simp only; rw [Slice.setAtNat_length]; exact him
      have hrest := hback_rest (next_back im (some a)) him_set i (by omega) hi_lt2
      rw [hrest, hsome_set]
      exact Slice.getElem!_Nat_setAtNat_ne _ _ _ _ (by omega)
    intro r hpost; exact hpost
  · have hge : iter.i ≥ iter.slice.len := by scalar_tac
    have hi_eq : iter.i = orig_slice.length := by
      have hpe : iter.slice.length = orig_slice.length := by rw [h_slice]
      have : iter.slice.len.val = orig_slice.length := by
        rw [← hpe]; simp [Slice.len, Slice.length]
      scalar_tac
    let* ⟨ o, iter1, next_back, h_all ⟩ ← iter_mut_next_spec_none
    obtain ⟨ho, hit2_eq, hsome_back⟩ := h_all
    rw [ho]
    show (back (next_back iter1 none)).slice.length = orig_slice.length ∧
        ∀ (i : Nat), i < orig_slice.length → ∀ (j : Nat), j < Y.val →
          toRingElem (((back (next_back iter1 none)).slice.val[i]!).val[j]!)
            = Spec.Kopis.Polynomial.shiftRight (toRingElem ((orig_slice.val[i]!).val[j]!)) shift.val
    have hbi : next_back iter1 none = iter := (hsome_back iter1 none).trans hit2_eq
    refine ⟨by rw [hbi]; exact hback_len iter (by rw [h_slice]), ?_⟩
    intro i hi j hj
    rw [hbi]
    exact hback_writes iter (by rw [h_slice]) i (hi_eq ▸ hi) j hj
  termination_by iter.slice.len.val - iter.i
  decreasing_by scalar_decr_tac

/-- **Correctness of `Matrix::shift_right`** (for `shift < 16`), entrywise at the
physical `2¹⁶` abstraction: every `RingElem` entry is right-shifted. -/
theorem matrix_shift_right_spec {X Y : Usize}
    (self : arithmetic.matrix_arith.Matrix X Y) (shift : Usize) (hshift : shift.val < 16) :
    arithmetic.matrix_arith.Matrix.shift_right self shift
      ⦃ (r : arithmetic.matrix_arith.Matrix X Y) =>
          ∀ (i : Nat) (_hi : i < X.val) (j : Nat) (_hj : j < Y.val),
            toRingElem ((r.val[i]!).val[j]!)
              = Spec.Kopis.Polynomial.shiftRight (toRingElem ((self.val[i]!).val[j]!)) shift.val ⦄ := by
  unfold arithmetic.matrix_arith.Matrix.shift_right
  let* ⟨ s, to_back, hs_val, hto_back ⟩ ← Array.to_slice_mut_spec
  let* ⟨ it0, it_back, h_it_slice, h_it_zero, h_it_back ⟩ ← iter_mut_spec
  let* ⟨ r_iter, hr_len, hr_writes ⟩ ←
    shift_right_loop0_spec it0 (fun im => im) shift hshift it0.slice rfl
      (by rw [h_it_zero]; exact Nat.zero_le _)
      (fun _ him => him)
      (fun _ _ i hi _ _ => by rw [h_it_zero] at hi; omega)
      (fun _ _ _ _ _ => rfl)
  simp only [h_it_back]
  intro i hi j hj
  have hs_len : s.length = X.val := by rw [Slice.length, hs_val]; exact self.property
  have hit_len : it0.slice.length = X.val := by rw [h_it_slice]; exact hs_len
  have hr_len_X : r_iter.slice.length = X.val := by rw [hr_len]; exact hit_len
  have h_val_eq : (to_back r_iter.slice).val = r_iter.slice.val := by
    rw [hto_back]; exact Std.Array.from_slice_val self r_iter.slice hr_len_X
  have hself_row : it0.slice.val[i]! = self.val[i]! :=
    congrArg (fun l => l[i]!) (show it0.slice.val = self.val by rw [h_it_slice, hs_val])
  rw [show (to_back r_iter.slice).val[i]! = r_iter.slice.val[i]! from congrArg (fun l => l[i]!) h_val_eq]
  rw [hr_writes i (by rw [hit_len]; exact hi) j hj, hself_row]

/-! ## `Matrix::wrapping_add_to_all` — add a fixed `u16` to every coefficient of
every entry.  Same nested `IterMut` skeleton as `shift_right`; per-`RingElem`
body is `RingElem.wrapping_add_to_all`. -/

/-- Abbreviation: add the constant `val` to a physical-`2¹⁶` polynomial. -/
def addC (val : U16) (x : Spec.Kopis.Polynomial (2 ^ 16)) : Spec.Kopis.Polynomial (2 ^ 16) :=
  Spec.Kopis.Polynomial.add x (Spec.Kopis.Polynomial.const (2 ^ 16) ((val.val : ZMod (2 ^ 16))))

/-- Inner loop of `Matrix.wrapping_add_to_all`. -/
theorem wrapping_add_to_all_loop0_loop0_spec
    (iter : core.slice.iter.IterMut RingElem)
    (back : core.slice.iter.IterMut RingElem → core.slice.iter.IterMut RingElem)
    (val : U16)
    (orig_slice : Slice RingElem)
    (h_slice : iter.slice = orig_slice)
    (h_iter_i : iter.i ≤ orig_slice.length)
    (hback_len : ∀ (im : core.slice.iter.IterMut RingElem),
      im.slice.length = orig_slice.length → (back im).slice.length = orig_slice.length)
    (hback_writes : ∀ (im : core.slice.iter.IterMut RingElem)
      (_him : im.slice.length = orig_slice.length)
      (j : Nat) (_hj : j < iter.i),
        toRingElem ((back im).slice.val[j]!) = addC val (toRingElem (orig_slice.val[j]!)))
    (hback_rest : ∀ (im : core.slice.iter.IterMut RingElem)
      (_him : im.slice.length = orig_slice.length)
      (j : Nat) (_hj_ge : iter.i ≤ j) (_hj_lt : j < orig_slice.length),
        (back im).slice.val[j]! = im.slice.val[j]!) :
    arithmetic.matrix_arith.Matrix.wrapping_add_to_all_loop0_loop0 iter back val
      ⦃ (p : core.slice.iter.IterMut RingElem ×
              (core.slice.iter.IterMut RingElem → core.slice.iter.IterMut RingElem)) =>
          (p.2 p.1).slice.length = orig_slice.length ∧
            ∀ (j : Nat) (_hj : j < orig_slice.length),
              toRingElem ((p.2 p.1).slice.val[j]!) = addC val (toRingElem (orig_slice.val[j]!)) ⦄ := by
  unfold arithmetic.matrix_arith.Matrix.wrapping_add_to_all_loop0_loop0
  by_cases hlt : iter.i < iter.slice.len
  · let* ⟨ o, iter1, next_back, h_all ⟩ ← iter_mut_next_spec
    obtain ⟨ho, hit2_slice, hit2_i, _, hsome_set⟩ := h_all
    rw [ho]
    simp only []
    have hi_pe : iter.slice.length = orig_slice.length := by rw [h_slice]
    have hi_lt : iter.i < orig_slice.length := by rw [← hi_pe]; scalar_tac
    let* ⟨ elem1, helem1 ⟩ ← wrapping_add_to_all_spec
    apply WP.spec_mono
      (wrapping_add_to_all_loop0_loop0_spec iter1 (fun im => back (next_back im (some elem1))) val
        orig_slice (by rw [hit2_slice, h_slice]) (by rw [hit2_i]; omega) ?len ?writes ?rest)
    case len =>
      intro im him
      have him_set : (next_back im (some elem1)).slice.length = orig_slice.length := by
        rw [hsome_set]; simp only; rw [Slice.setAtNat_length]; exact him
      exact hback_len _ him_set
    case writes =>
      intro im him j hj
      rw [hit2_i] at hj
      have him_set : (next_back im (some elem1)).slice.length = orig_slice.length := by
        rw [hsome_set]; simp only; rw [Slice.setAtNat_length]; exact him
      by_cases hji : j = iter.i
      · subst hji
        have hrest := hback_rest (next_back im (some elem1)) him_set iter.i (le_refl _) hi_lt
        have hkey : (back (next_back im (some elem1))).slice.val[iter.i]! = elem1 := by
          rw [hrest, hsome_set]
          exact Slice.getElem!_Nat_setAtNat_eq _ _ _ (by rw [him]; exact hi_lt)
        rw [hkey, helem1]
        have hvaleq : iter.slice.val = orig_slice.val := by rw [h_slice]
        have hb : iter.i < orig_slice.val.length := hi_lt
        have helem : iter.slice[iter.i] = orig_slice.val[iter.i]! := by
          rw [getElem!_pos orig_slice.val iter.i hb]
          exact List.getElem_of_eq hvaleq _
        exact congrArg (fun x => addC val (toRingElem x)) helem
      · have hjlt : j < iter.i := by omega
        exact hback_writes (next_back im (some elem1)) him_set j hjlt
    case rest =>
      intro im him j hj_ge hj_lt
      rw [hit2_i] at hj_ge
      have him_set : (next_back im (some elem1)).slice.length = orig_slice.length := by
        rw [hsome_set]; simp only; rw [Slice.setAtNat_length]; exact him
      have hrest := hback_rest (next_back im (some elem1)) him_set j (by omega) hj_lt
      rw [hrest, hsome_set]
      exact Slice.getElem!_Nat_setAtNat_ne _ _ _ _ (by omega)
    intro r hpost; exact hpost
  · have hge : iter.i ≥ iter.slice.len := by scalar_tac
    have hi_eq : iter.i = orig_slice.length := by
      have hpe : iter.slice.length = orig_slice.length := by rw [h_slice]
      have : iter.slice.len.val = orig_slice.length := by
        rw [← hpe]; simp [Slice.len, Slice.length]
      scalar_tac
    let* ⟨ o, iter1, next_back, h_all ⟩ ← iter_mut_next_spec_none
    obtain ⟨ho, hit2_eq, hsome_back⟩ := h_all
    rw [ho]
    have hbi : next_back iter1 none = iter := (hsome_back iter1 none).trans hit2_eq
    show (back (next_back iter1 none)).slice.length = orig_slice.length ∧
        ∀ (j : Nat), j < orig_slice.length →
          toRingElem ((back (next_back iter1 none)).slice.val[j]!) = addC val (toRingElem (orig_slice.val[j]!))
    refine ⟨by rw [hbi]; exact hback_len iter (by rw [h_slice]), ?_⟩
    intro j hj
    rw [hbi]
    exact hback_writes iter (by rw [h_slice]) j (hi_eq ▸ hj)
  termination_by iter.slice.len.val - iter.i
  decreasing_by scalar_decr_tac

/-- Outer loop of `Matrix.wrapping_add_to_all`. -/
theorem wrapping_add_to_all_loop0_spec {Y : Usize}
    (iter : core.slice.iter.IterMut (Array arithmetic.ring_arith.RingElem Y))
    (back : core.slice.iter.IterMut (Array arithmetic.ring_arith.RingElem Y) →
            core.slice.iter.IterMut (Array arithmetic.ring_arith.RingElem Y))
    (val : U16)
    (orig_slice : Slice (Array arithmetic.ring_arith.RingElem Y))
    (h_slice : iter.slice = orig_slice)
    (h_iter_i : iter.i ≤ orig_slice.length)
    (hback_len : ∀ (im : core.slice.iter.IterMut (Array arithmetic.ring_arith.RingElem Y)),
      im.slice.length = orig_slice.length → (back im).slice.length = orig_slice.length)
    (hback_writes : ∀ (im : core.slice.iter.IterMut (Array arithmetic.ring_arith.RingElem Y))
      (_him : im.slice.length = orig_slice.length)
      (i : Nat) (_hi : i < iter.i) (j : Nat) (_hj : j < Y.val),
        toRingElem (((back im).slice.val[i]!).val[j]!) = addC val (toRingElem ((orig_slice.val[i]!).val[j]!)))
    (hback_rest : ∀ (im : core.slice.iter.IterMut (Array arithmetic.ring_arith.RingElem Y))
      (_him : im.slice.length = orig_slice.length)
      (i : Nat) (_hi_ge : iter.i ≤ i) (_hi_lt : i < orig_slice.length),
        (back im).slice.val[i]! = im.slice.val[i]!) :
    arithmetic.matrix_arith.Matrix.wrapping_add_to_all_loop0 iter back val
      ⦃ (r : core.slice.iter.IterMut (Array arithmetic.ring_arith.RingElem Y)) =>
          r.slice.length = orig_slice.length ∧
            ∀ (i : Nat) (_hi : i < orig_slice.length) (j : Nat) (_hj : j < Y.val),
              toRingElem (((r.slice.val[i]!).val[j]!)) = addC val (toRingElem ((orig_slice.val[i]!).val[j]!)) ⦄ := by
  unfold arithmetic.matrix_arith.Matrix.wrapping_add_to_all_loop0
  by_cases hlt : iter.i < iter.slice.len
  · let* ⟨ o, iter1, next_back, h_all ⟩ ← iter_mut_next_spec
    obtain ⟨ho, hit2_slice, hit2_i, _, hsome_set⟩ := h_all
    rw [ho]
    simp only []
    have hi_pe : iter.slice.length = orig_slice.length := by rw [h_slice]
    have hi_lt : iter.i < orig_slice.length := by rw [← hi_pe]; scalar_tac
    let* ⟨ s, to_slice_mut_back, hs_val, hto_back ⟩ ← Array.to_slice_mut_spec
    let* ⟨ iter2, iter_mut_back, h_i2_slice, h_i2_zero, h_i2_back ⟩ ← iter_mut_spec
    let* ⟨ inner_im, inner_back, hinner_len, hinner_writes ⟩ ←
      wrapping_add_to_all_loop0_loop0_spec iter2 (fun x => x) val iter2.slice rfl
        (by rw [h_i2_zero]; exact Nat.zero_le _)
        (fun _ him => him)
        (fun _ _ j hj => by rw [h_i2_zero] at hj; omega)
        (fun _ _ _ _ _ => rfl)
    have hrow_len : (iter.slice[iter.i]).val.length = Y.val := (iter.slice[iter.i]).property
    have hs_len : s.length = Y.val := by rw [Slice.length, hs_val]; exact hrow_len
    have hi2s_len : iter2.slice.length = Y.val := by rw [h_i2_slice]; exact hs_len
    have hib_len : (inner_back inner_im).slice.length = Y.val := hinner_len.trans hi2s_len
    set a := to_slice_mut_back (iter_mut_back (inner_back inner_im)) with ha_def
    have ha_val : a.val = (inner_back inner_im).slice.val := by
      rw [ha_def, h_i2_back, hto_back]
      exact Std.Array.from_slice_val _ _ hib_len
    apply WP.spec_mono
      (wrapping_add_to_all_loop0_spec iter1 (fun im1 => back (next_back im1 (some a))) val
        orig_slice (by rw [hit2_slice, h_slice]) (by rw [hit2_i]; omega) ?len ?writes ?rest)
    case len =>
      intro im him
      have him_set : (next_back im (some a)).slice.length = orig_slice.length := by
        rw [hsome_set]; simp only; rw [Slice.setAtNat_length]; exact him
      exact hback_len _ him_set
    case writes =>
      intro im him i hi j hj
      rw [hit2_i] at hi
      have him_set : (next_back im (some a)).slice.length = orig_slice.length := by
        rw [hsome_set]; simp only; rw [Slice.setAtNat_length]; exact him
      by_cases hii : i = iter.i
      · subst hii
        have hrest := hback_rest (next_back im (some a)) him_set iter.i (le_refl _) hi_lt
        have hkey : (back (next_back im (some a))).slice.val[iter.i]! = a := by
          rw [hrest, hsome_set]
          exact Slice.getElem!_Nat_setAtNat_eq _ _ _ (by rw [him]; exact hi_lt)
        rw [hkey]
        rw [show a.val[j]! = (inner_back inner_im).slice.val[j]! from
              congrArg (fun l => l[j]!) ha_val]
        rw [hinner_writes j (by rw [hi2s_len]; exact hj)]
        have hb : iter.i < orig_slice.val.length := hi_lt
        have hrow_eq : iter.slice[iter.i] = orig_slice.val[iter.i]! := by
          rw [getElem!_pos orig_slice.val iter.i hb]
          exact List.getElem_of_eq (show iter.slice.val = orig_slice.val by rw [h_slice]) _
        have hvaleq : iter2.slice.val = (orig_slice.val[iter.i]!).val := by
          rw [h_i2_slice, hs_val]; exact congrArg (·.val) hrow_eq
        rw [show iter2.slice.val[j]! = (orig_slice.val[iter.i]!).val[j]! from
              congrArg (fun l => l[j]!) hvaleq]
      · have hilt : i < iter.i := by omega
        exact hback_writes (next_back im (some a)) him_set i hilt j hj
    case rest =>
      intro im him i hi_ge hi_lt2
      rw [hit2_i] at hi_ge
      have him_set : (next_back im (some a)).slice.length = orig_slice.length := by
        rw [hsome_set]; simp only; rw [Slice.setAtNat_length]; exact him
      have hrest := hback_rest (next_back im (some a)) him_set i (by omega) hi_lt2
      rw [hrest, hsome_set]
      exact Slice.getElem!_Nat_setAtNat_ne _ _ _ _ (by omega)
    intro r hpost; exact hpost
  · have hge : iter.i ≥ iter.slice.len := by scalar_tac
    have hi_eq : iter.i = orig_slice.length := by
      have hpe : iter.slice.length = orig_slice.length := by rw [h_slice]
      have : iter.slice.len.val = orig_slice.length := by
        rw [← hpe]; simp [Slice.len, Slice.length]
      scalar_tac
    let* ⟨ o, iter1, next_back, h_all ⟩ ← iter_mut_next_spec_none
    obtain ⟨ho, hit2_eq, hsome_back⟩ := h_all
    rw [ho]
    show (back (next_back iter1 none)).slice.length = orig_slice.length ∧
        ∀ (i : Nat), i < orig_slice.length → ∀ (j : Nat), j < Y.val →
          toRingElem (((back (next_back iter1 none)).slice.val[i]!).val[j]!)
            = addC val (toRingElem ((orig_slice.val[i]!).val[j]!))
    have hbi : next_back iter1 none = iter := (hsome_back iter1 none).trans hit2_eq
    refine ⟨by rw [hbi]; exact hback_len iter (by rw [h_slice]), ?_⟩
    intro i hi j hj
    rw [hbi]
    exact hback_writes iter (by rw [h_slice]) i (hi_eq ▸ hi) j hj
  termination_by iter.slice.len.val - iter.i
  decreasing_by scalar_decr_tac

/-- **Correctness of `Matrix::wrapping_add_to_all`**, entrywise at `2¹⁶`: adds the
constant `val` to every coefficient of every entry. -/
theorem matrix_wrapping_add_to_all_spec {X Y : Usize}
    (self : arithmetic.matrix_arith.Matrix X Y) (val : U16) :
    arithmetic.matrix_arith.Matrix.wrapping_add_to_all self val
      ⦃ (r : arithmetic.matrix_arith.Matrix X Y) =>
          ∀ (i : Nat) (_hi : i < X.val) (j : Nat) (_hj : j < Y.val),
            toRingElem ((r.val[i]!).val[j]!) = addC val (toRingElem ((self.val[i]!).val[j]!)) ⦄ := by
  unfold arithmetic.matrix_arith.Matrix.wrapping_add_to_all
  let* ⟨ s, to_back, hs_val, hto_back ⟩ ← Array.to_slice_mut_spec
  let* ⟨ it0, it_back, h_it_slice, h_it_zero, h_it_back ⟩ ← iter_mut_spec
  let* ⟨ r_iter, hr_len, hr_writes ⟩ ←
    wrapping_add_to_all_loop0_spec it0 (fun im => im) val it0.slice rfl
      (by rw [h_it_zero]; exact Nat.zero_le _)
      (fun _ him => him)
      (fun _ _ i hi _ _ => by rw [h_it_zero] at hi; omega)
      (fun _ _ _ _ _ => rfl)
  simp only [h_it_back]
  intro i hi j hj
  have hs_len : s.length = X.val := by rw [Slice.length, hs_val]; exact self.property
  have hit_len : it0.slice.length = X.val := by rw [h_it_slice]; exact hs_len
  have hr_len_X : r_iter.slice.length = X.val := by rw [hr_len]; exact hit_len
  have h_val_eq : (to_back r_iter.slice).val = r_iter.slice.val := by
    rw [hto_back]; exact Std.Array.from_slice_val self r_iter.slice hr_len_X
  have hself_row : it0.slice.val[i]! = self.val[i]! :=
    congrArg (fun l => l[i]!) (show it0.slice.val = self.val by rw [h_it_slice, hs_val])
  rw [show (to_back r_iter.slice).val[i]! = r_iter.slice.val[i]! from congrArg (fun l => l[i]!) h_val_eq]
  rw [hr_writes i (by rw [hit_len]; exact hi) j hj, hself_row]

end Kopis.Properties

