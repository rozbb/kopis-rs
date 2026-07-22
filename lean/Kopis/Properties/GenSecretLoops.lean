import Kopis.Properties.GenSecret
open Aeneas Aeneas.Std Result RustKopis
open scoped BigOperators
namespace Kopis.Properties

set_option maxHeartbeats 2000000
set_option maxRecDepth 4000

/-! ## `Iter`/`Enumerate` step specs (generic; replicated from `Symcrust`'s
`Iterators.lean`, which lives in a different library; these depend only on
Aeneas' `core.slice.iter`/`core.iter.adapters.enumerate`). -/

@[step]
theorem sliceIter_spec {T : Type} (s : Slice T) :
  core.slice.Slice.iter s ⦃ it => it.slice = s ∧ it.i = 0 ⦄ := by
  simp [core.slice.Slice.iter]

@[step]
theorem sliceIter_next_spec {T : Type} (it : core.slice.iter.Iter T) (h : it.i < it.slice.len) :
  core.slice.iter.IteratorSliceIter.next it
  ⦃ p => p.1 = some (it.slice[it.i]) ∧ p.2.slice = it.slice ∧ p.2.i = it.i + 1 ⦄ := by
  simp only [core.slice.iter.IteratorSliceIter.next, h, ↓reduceDIte]; simp

@[step]
theorem sliceIter_next_none {T : Type} (it : core.slice.iter.Iter T) (h : it.i ≥ it.slice.len) :
  core.slice.iter.IteratorSliceIter.next it ⦃ p => p.1 = none ∧ p.2 = it ⦄ := by
  simp only [core.slice.iter.IteratorSliceIter.next]; split
  · agrind
  · simp

@[step]
theorem enumSliceIter_next_some {T : Type}
    (iter : core.iter.adapters.enumerate.Enumerate (core.slice.iter.Iter T))
    (h_lt : iter.iter.i < iter.iter.slice.len)
    (h_no_overflow : iter.count.val + 1 ≤ Usize.max) :
    core.iter.adapters.enumerate.IteratorEnumerate.next
      (core.iter.traits.iterator.IteratorSliceIter T) iter
    ⦃ (o : Option (Usize × T))
      (iter1 : core.iter.adapters.enumerate.Enumerate (core.slice.iter.Iter T)) =>
      o = some (iter.count, iter.iter.slice[iter.iter.i]) ∧
      iter1.iter.slice = iter.iter.slice ∧
      iter1.iter.i = iter.iter.i + 1 ∧
      iter1.count.val = iter.count.val + 1 ⦄ := by
  have h_inner :
      (core.iter.traits.iterator.IteratorSliceIter T).next iter.iter
      ⦃ p => p.1 = some (iter.iter.slice[iter.iter.i]) ∧
             p.2 = { slice := iter.iter.slice, i := iter.iter.i + 1 } ⦄ := by
    apply WP.spec_mono (sliceIter_next_spec iter.iter h_lt)
    rintro ⟨o, it'⟩ ⟨ho, hs, hi⟩
    exact ⟨ho, by cases it'; simp_all⟩
  apply WP.spec_mono
    (core.iter.adapters.enumerate.IteratorEnumerate.next_some_spec
      (core.iter.traits.iterator.IteratorSliceIter T) iter
      (iter.iter.slice[iter.iter.i])
      { slice := iter.iter.slice, i := iter.iter.i + 1 }
      h_inner h_no_overflow)
  rintro ⟨opt, self'⟩ ⟨hopt, hiter, hcount⟩
  exact ⟨hopt, by rw [hiter], by rw [hiter], hcount⟩

@[step]
theorem enumSliceIter_next_none {T : Type}
    (iter : core.iter.adapters.enumerate.Enumerate (core.slice.iter.Iter T))
    (h_ge : iter.iter.i ≥ iter.iter.slice.len) :
    core.iter.adapters.enumerate.IteratorEnumerate.next
      (core.iter.traits.iterator.IteratorSliceIter T) iter
    ⦃ (o : Option (Usize × T))
      (iter1 : core.iter.adapters.enumerate.Enumerate (core.slice.iter.Iter T)) =>
      o = none ∧ iter1 = iter ⦄ := by
  have h_inner :
      (core.iter.traits.iterator.IteratorSliceIter T).next iter.iter
      ⦃ p => p.1 = none ∧ p.2 = iter.iter ⦄ :=
    sliceIter_next_none iter.iter h_ge
  apply WP.spec_mono
    (core.iter.adapters.enumerate.IteratorEnumerate.next_none_spec
      (core.iter.traits.iterator.IteratorSliceIter T) iter iter.iter h_inner)
  rintro ⟨o, iter1⟩ ⟨ho, h_iter, h_count⟩
  refine ⟨ho, ?_⟩
  cases iter1; cases iter
  simp_all

/-- `x` (or `y`) of the CBD sample at stream position `p`: popcount of `half` bits. -/
def cbdX (buf : Slice U8) (half p : ℕ) : ℕ := ∑ i ∈ Finset.range half, streamBit buf (p + i)

theorem cbd_streamBit_le_one (bytes : Slice U8) (m : ℕ) : streamBit bytes m ≤ 1 := by
  unfold streamBit; cases (bytes.val[m / 8]!).val.testBit (m % 8) <;> simp

theorem cbdX_le (buf : Slice U8) (half p : ℕ) : cbdX buf half p ≤ half := by
  unfold cbdX
  calc ∑ i ∈ Finset.range half, streamBit buf (p + i)
      ≤ ∑ _i ∈ Finset.range half, 1 := Finset.sum_le_sum (fun i _ => cbd_streamBit_le_one buf (p + i))
    _ = half := by simp

/-- The CBD coefficient value (in `ZMod 2¹³`) for coefficient index `k`. -/
def cbdVal (buf : Slice U8) (mu half k : ℕ) : ZMod (2 ^ 13) :=
  ((cbdX buf half (mu * k) : ℕ) : ZMod (2 ^ 13))
    - ((cbdX buf half (mu * k + half) : ℕ) : ZMod (2 ^ 13))

/-- **`cbd_loop1` loop spec.**  Coefficients `[0, iter.i)` already hold the CBD
sample; `bit_pos = μ·iter.i`. -/
theorem cbd_loop1_spec (MU : Usize) (iter : core.slice.iter.IterMut U16)
    (back : core.slice.iter.IterMut U16 → core.slice.iter.IterMut U16)
    (buf : Slice U8) (half : Usize) (mask : U32) (bit_pos : Usize)
    (hhalf : half.val = MU.val / 2) (hmask : mask.val = 2 ^ half.val - 1)
    (hMU : 4 ≤ MU.val ∧ MU.val ≤ 10)
    (hlen : buf.val.length = 32 * MU.val)
    (hbp : bit_pos.val = MU.val * iter.i)
    (orig_slice : Slice U16)
    (h_slice : iter.slice = orig_slice)
    (h_len256 : orig_slice.length = 256)
    (h_iter_i : iter.i ≤ 256)
    (hback_len : ∀ (im : core.slice.iter.IterMut U16),
      im.slice.length = orig_slice.length → (back im).slice.length = orig_slice.length)
    (hback_writes : ∀ (im : core.slice.iter.IterMut U16)
      (_him : im.slice.length = orig_slice.length) (j : Nat) (_hj : j < iter.i),
        (((back im).slice.val[j]!).val : ZMod (2 ^ 13)) = cbdVal buf MU.val half.val j)
    (hback_rest : ∀ (im : core.slice.iter.IterMut U16)
      (_him : im.slice.length = orig_slice.length) (j : Nat)
      (_hj_ge : iter.i ≤ j) (_hj_lt : j < orig_slice.length),
        (back im).slice.val[j]! = im.slice.val[j]!) :
    gen.cbd_loop1 MU iter back buf half mask bit_pos
      ⦃ (r : core.slice.iter.IterMut U16) =>
          ∃ (_h_len : r.slice.length = orig_slice.length),
            ∀ (j : Nat) (_hj : j < orig_slice.length),
              (((r.slice.val[j]!).val : ZMod (2 ^ 13))) = cbdVal buf MU.val half.val j ⦄ := by
  unfold gen.cbd_loop1
  by_cases hlt : iter.i < iter.slice.len
  · -- SOME branch
    have hi_pe : iter.slice.length = orig_slice.length := by rw [h_slice]
    have hi_lt256 : iter.i < 256 := by rw [← h_len256, ← hi_pe]; scalar_tac
    have hhalf_le : half.val ≤ 5 := by omega
    have hhalf_lt32 : half.val < 32 := by omega
    let* ⟨ o, iter1, next_back, h_all ⟩ ← iter_mut_next_spec
    obtain ⟨ho, hit2_slice, hit2_i, _, hsome_set⟩ := h_all
    rw [ho]
    simp only []
    -- byte_idx / bit_in_byte
    let* ⟨ byte_idx, hbi ⟩ ← Std.Usize.div_spec
    let* ⟨ bib, hbibv ⟩ ← Std.Usize.rem_spec
    have hbi_val : byte_idx.val = bit_pos.val / 8 := by rw [hbi]
    have hbib_val : bib.val = bit_pos.val % 8 := by rw [hbibv]
    have hbp_lt : bit_pos.val < 8 * buf.val.length := by
      rw [hbp, hlen]
      have h1 : iter.i < 256 := hi_lt256
      have h2 : 4 ≤ MU.val := hMU.1
      nlinarith
    have hbi_lt : byte_idx.val < buf.val.length := by
      rw [hbi_val]; omega
    -- raw1 = cast buf[byte_idx]
    let* ⟨ bt, hbt ⟩ ← Slice.index_usize_spec
    let* ⟨ raw1, hraw1 ⟩ ← UScalar.cast_inBounds_spec
    have hbt_pos : bt.val = (buf.val[byte_idx.val]!).val := by
      rw [hbt, getElem!_pos buf.val byte_idx.val hbi_lt]
    have hraw1v : raw1.val = (buf.val[byte_idx.val]!).val := by rw [hraw1, hbt_pos]
    have hraw1_lt : raw1.val < 2 ^ 8 := by rw [hraw1v]; have := (buf.val[byte_idx.val]!).hBounds; omega
    have hlen_buf : (Slice.len buf).val = buf.val.length := by simp [Slice.len]
    let* ⟨ i1, hi1 ⟩ ← Std.Usize.add_spec
    -- byte value at an OOB index is 0
    have hoob : ∀ p : ℕ, ¬ p < buf.val.length → (buf.val[p]!).val = 0 := by
      intro p hp; rw [getElem!_neg buf.val p hp]; rfl
    -- window `raw2` (byte_idx + 1): value `raw1 + 2⁸·buf[bi+1]`, back = `next_back _ (some _)`
    have hraw2 :
        (if i1 < Slice.len buf then
            (do let i3 ← Slice.index_usize buf i1
                let i4 ← lift (UScalar.cast .U32 i3)
                let i5 ← i4 <<< 8#i32
                let raw3 ← lift (raw1 ||| i5)
                ok (raw3, fun i6 im => next_back im (some i6)))
          else ok (raw1, fun i3 im => next_back im (some i3)))
        ⦃ (p : U32 × (U16 → core.slice.iter.IterMut U16 → core.slice.iter.IterMut U16)) =>
            p.1.val = raw1.val + 2 ^ 8 * (buf.val[byte_idx.val + 1]!).val ∧
            ∀ c im, p.2 c im = next_back im (some c) ⦄ := by
      by_cases hg1 : i1 < Slice.len buf
      · rw [if_pos hg1]
        have hi1_lt : i1.val < buf.val.length := by
          have : i1.val < (Slice.len buf).val := hg1; rw [hlen_buf] at this; exact this
        let* ⟨ i3, hi3 ⟩ ← Slice.index_usize_spec
        let* ⟨ i4, hi4 ⟩ ← UScalar.cast_inBounds_spec .U32 i3 (by scalar_tac)
        let* ⟨ i5, hi5, hi5bv ⟩ ← Std.U32.ShiftLeft_IScalar_spec i4 8#i32 (by decide) (by decide)
        simp only [lift, bind_tc_ok]
        refine ⟨?_, fun c im => rfl⟩
        have hi3v : i3.val = (buf.val[byte_idx.val + 1]!).val := by
          have h : i3.val = (buf.val[i1.val]!).val := by
            rw [hi3]; exact congrArg (·.val) (getElem!_pos buf.val i1.val hi1_lt).symm
          rw [h, hi1]
        have hi4_lt : i4.val < 2 ^ 8 := by
          rw [hi4, hi3v]; have := (buf.val[byte_idx.val + 1]!).hBounds; omega
        have hsz : U32.size = 2 ^ 32 := by simp [Std.U32.size, Std.U32.numBits]
        have hi5v : i5.val = i4.val * 2 ^ 8 := by
          rw [hi5, Nat.shiftLeft_eq, Nat.mod_eq_of_lt (show i4.val * 2 ^ 8 < U32.size from by
            rw [hsz]; omega)]
        simp only []
        rw [UScalar.val_or, hi5v, lor_mul_of_lt hraw1_lt, hi4, hi3v]; ring
      · rw [if_neg hg1]
        simp only [WP.spec_ok]
        refine ⟨?_, fun _ _ => trivial⟩
        rw [hoob (byte_idx.val + 1) (by
          have : ¬ i1.val < (Slice.len buf).val := hg1; rw [hlen_buf] at this; rw [hi1] at this; exact this)]
        ring
    let* ⟨ raw2, back1, hraw2v, hback1 ⟩ ← hraw2
    -- raw3 window (byte_idx + 2)
    let* ⟨ i3', hi3' ⟩ ← Std.Usize.add_spec
    have hbuf1_lt : (buf.val[byte_idx.val + 1]!).val < 2 ^ 8 := by
      have := (buf.val[byte_idx.val + 1]!).hBounds; omega
    have hraw2_lt : raw2.val < 2 ^ 16 := by rw [hraw2v]; omega
    have hraw3 :
        (if i3' < Slice.len buf then
            (do let i5 ← Slice.index_usize buf i3'
                let i6 ← lift (UScalar.cast .U32 i5)
                let i7 ← i6 <<< 16#i32
                ok (raw2 ||| i7))
          else ok raw2)
        ⦃ (r : U32) => r.val = raw2.val + 2 ^ 16 * (buf.val[byte_idx.val + 2]!).val ⦄ := by
      by_cases hg2 : i3' < Slice.len buf
      · rw [if_pos hg2]
        have hi3'_lt : i3'.val < buf.val.length := by
          have : i3'.val < (Slice.len buf).val := hg2; rw [hlen_buf] at this; exact this
        let* ⟨ i5, hi5' ⟩ ← Slice.index_usize_spec
        let* ⟨ i6, hi6' ⟩ ← UScalar.cast_inBounds_spec .U32 i5 (by scalar_tac)
        let* ⟨ i7, hi7, hi7bv ⟩ ← Std.U32.ShiftLeft_IScalar_spec i6 16#i32 (by decide) (by decide)
        have hi5'v : i5.val = (buf.val[byte_idx.val + 2]!).val := by
          have h : i5.val = (buf.val[i3'.val]!).val := by
            rw [hi5']; exact congrArg (·.val) (getElem!_pos buf.val i3'.val hi3'_lt).symm
          rw [h, hi3']
        have hi6_lt : i6.val < 2 ^ 8 := by
          rw [hi6', hi5'v]; have := (buf.val[byte_idx.val + 2]!).hBounds; omega
        have hsz : U32.size = 2 ^ 32 := by simp [Std.U32.size, Std.U32.numBits]
        have hi7v : i7.val = i6.val * 2 ^ 16 := by
          rw [hi7, Nat.shiftLeft_eq, Nat.mod_eq_of_lt (show i6.val * 2 ^ 16 < U32.size from by
            rw [hsz]; omega)]
        rw [UScalar.val_or, hi7v, lor_mul_of_lt hraw2_lt, hi6', hi5'v]; ring
      · rw [if_neg hg2]
        simp only [WP.spec_ok]
        rw [hoob (byte_idx.val + 2) (by
          have : ¬ i3'.val < (Slice.len buf).val := hg2; rw [hlen_buf] at this; rw [hi3'] at this; exact this)]
        ring
    let* ⟨ raw3, hraw3v ⟩ ← hraw3
    -- window value W
    have hwin : raw3.val = (buf.val[byte_idx.val]!).val + 2 ^ 8 * (buf.val[byte_idx.val + 1]!).val
        + 2 ^ 16 * (buf.val[byte_idx.val + 2]!).val := by rw [hraw3v, hraw2v, hraw1v]
    -- raw4 = raw3 >>> bit_in_byte
    let* ⟨ raw4, hraw4, hraw4bv ⟩ ← Std.U32.ShiftRight_spec raw3 bib (by omega)
    have hraw4v : raw4.val = ((buf.val[byte_idx.val]!).val + 2 ^ 8 * (buf.val[byte_idx.val + 1]!).val
        + 2 ^ 16 * (buf.val[byte_idx.val + 2]!).val) >>> bib.val := by rw [hraw4, hwin]
    have hbit_eq : 8 * byte_idx.val + bib.val = bit_pos.val := by rw [hbi_val, hbib_val]; omega
    -- x = popcount(raw4 & mask)
    rw [show lift (raw4 &&& mask) = ok (raw4 &&& mask) from rfl, bind_tc_ok]
    let* ⟨ i6c, hi6c ⟩ ← U32.count_ones_spec
    have hX : i6c.val = cbdX buf half.val bit_pos.val := by
      rw [hi6c, popcount_low_mask raw4 mask half.val (by omega) (mask_getLsbD mask half.val hmask),
        window_popcount buf byte_idx.val bib.val half.val raw4 (by omega) (by omega) hraw4v]
      unfold cbdX; simp_rw [hbit_eq]
    have hX_lt : i6c.val ≤ UScalar.max UScalarTy.U16 := by
      rw [hX]; have := cbdX_le buf half.val bit_pos.val
      simp only [UScalar.max, UScalarTy.numBits]; omega
    let* ⟨ a, ha ⟩ ← UScalar.cast_inBounds_spec .U16 i6c hX_lt
    -- y = popcount((raw4 >>> half) & mask)
    let* ⟨ i7c, hi7c, hi7cbv ⟩ ← Std.U32.ShiftRight_spec raw4 half (by omega)
    rw [show lift (i7c &&& mask) = ok (i7c &&& mask) from rfl, bind_tc_ok]
    let* ⟨ i9c, hi9c ⟩ ← U32.count_ones_spec
    have hi7cv : i7c.val = ((buf.val[byte_idx.val]!).val + 2 ^ 8 * (buf.val[byte_idx.val + 1]!).val
        + 2 ^ 16 * (buf.val[byte_idx.val + 2]!).val) >>> (bib.val + half.val) := by
      rw [hi7c, hraw4v, ← Nat.shiftRight_add]
    have hY : i9c.val = cbdX buf half.val (bit_pos.val + half.val) := by
      rw [hi9c, popcount_low_mask i7c mask half.val (by omega) (mask_getLsbD mask half.val hmask),
        window_popcount buf byte_idx.val (bib.val + half.val) half.val i7c (by omega) (by omega) hi7cv]
      unfold cbdX
      simp_rw [show 8 * byte_idx.val + (bib.val + half.val) = bit_pos.val + half.val from by
        rw [← hbit_eq]; ring]
    have hY_lt : i9c.val ≤ UScalar.max UScalarTy.U16 := by
      rw [hY]; have := cbdX_le buf half.val (bit_pos.val + half.val)
      simp only [UScalar.max, UScalarTy.numBits]; omega
    let* ⟨ b, hb ⟩ ← UScalar.cast_inBounds_spec .U16 i9c hY_lt
    -- coeff = wrapping_sub a b, and its ZMod value
    have hcoeff : ((core.num.U16.wrapping_sub a b).val : ZMod (2 ^ 13)) = cbdVal buf MU.val half.val iter.i := by
      rw [wrapping_sub_toZMod13, ha, hb, hX, hY, hbp]; rfl
    simp only [lift, bind_tc_ok]
    let* ⟨ bit_pos1, hbp1 ⟩ ← Std.Usize.add_spec
    simp only [hback1]
    -- recurse
    apply WP.spec_mono
      (cbd_loop1_spec MU iter1 (fun im => back (next_back im (some (core.num.U16.wrapping_sub a b))))
        buf half mask bit_pos1 hhalf hmask hMU hlen (by rw [hbp1, hit2_i, hbp]; ring)
        orig_slice (by rw [hit2_slice, h_slice]) h_len256 (by rw [hit2_i]; omega) ?len ?writes ?rest)
    case len =>
      intro im him
      have him_set : (next_back im (some (core.num.U16.wrapping_sub a b))).slice.length = orig_slice.length := by
        rw [hsome_set]; simp only; rw [Slice.setAtNat_length]; exact him
      exact hback_len _ him_set
    case writes =>
      intro im him j hj
      rw [hit2_i] at hj
      have him_set : (next_back im (some (core.num.U16.wrapping_sub a b))).slice.length = orig_slice.length := by
        rw [hsome_set]; simp only; rw [Slice.setAtNat_length]; exact him
      by_cases hji : j = iter.i
      · subst hji
        have hbk_len := hback_len _ him_set
        have hrest := hback_rest _ him_set iter.i (le_refl _) (by rw [← hi_pe]; exact hlt)
        have hkey : (back (next_back im (some (core.num.U16.wrapping_sub a b)))).slice.val[iter.i]!
            = core.num.U16.wrapping_sub a b := by
          rw [hrest, hsome_set]
          exact Slice.getElem!_Nat_setAtNat_eq _ _ _ (by rw [him]; rw [← hi_pe]; exact hlt)
        rw [hkey]; exact hcoeff
      · have hjlt : j < iter.i := by omega
        exact hback_writes _ him_set j hjlt
    case rest =>
      intro im him j hj_ge hj_lt
      rw [hit2_i] at hj_ge
      have him_set : (next_back im (some (core.num.U16.wrapping_sub a b))).slice.length = orig_slice.length := by
        rw [hsome_set]; simp only; rw [Slice.setAtNat_length]; exact him
      have hrest := hback_rest _ him_set j (by omega) hj_lt
      rw [hrest, hsome_set]
      exact Slice.getElem!_Nat_setAtNat_ne _ _ _ _ (by omega)
    intro r hpost; exact hpost
  · -- NONE branch
    have hge : iter.i ≥ iter.slice.len := by scalar_tac
    have hi_eq : iter.i = orig_slice.length := by
      have hpe : iter.slice.length = orig_slice.length := by rw [h_slice]
      have : iter.slice.len.val = orig_slice.length := by
        rw [← hpe]; simp [Slice.len]
      scalar_tac
    let* ⟨ o, iter1, next_back, h_all ⟩ ← iter_mut_next_spec_none
    obtain ⟨ho, hit2_eq, hsome_back⟩ := h_all
    rw [ho]
    have hbi : next_back iter1 none = iter := (hsome_back iter1 none).trans hit2_eq
    show ∃ (_h_len : (back (next_back iter1 none)).slice.length = orig_slice.length),
        ∀ (j : Nat), j < orig_slice.length →
          (((back (next_back iter1 none)).slice.val[j]!).val : ZMod (2 ^ 13)) = cbdVal buf MU.val half.val j
    refine ⟨by rw [hbi]; exact hback_len iter (by rw [h_slice]), ?_⟩
    intro j hj
    rw [hbi]
    exact hback_writes iter (by rw [h_slice]) j (hi_eq ▸ hj)
  termination_by iter.slice.len.val - iter.i
  decreasing_by scalar_decr_tac

/-- Popcount of the low nibble `byte & 15` = sum of `byte`'s low 4 bits. -/
theorem cbd_nibble_low (byte : U8) :
    (∑ i ∈ Finset.range 8, ((byte &&& 15#u8).bv.getLsbD i).toNat)
      = ∑ i ∈ Finset.range 4, (byte.val.testBit i).toNat := by
  have hmask : ∀ i, (15#u8).bv.getLsbD i = decide (i < 4) := by
    intro i
    have h : (15#u8).bv.getLsbD i = (15#u8).val.testBit i := by rw [UScalar.val, BitVec.getLsbD]
    rw [h, show (15#u8).val = 2 ^ 4 - 1 from by decide, Nat.testBit_two_pow_sub_one]
  have hstep : ∀ i, ((byte &&& 15#u8).bv.getLsbD i).toNat
      = if i < 4 then (byte.val.testBit i).toNat else 0 := by
    intro i
    rw [show (byte &&& 15#u8).bv = byte.bv &&& (15#u8).bv from rfl, BitVec.getLsbD_and, hmask i,
      show byte.bv.getLsbD i = byte.val.testBit i from by rw [UScalar.val, BitVec.getLsbD]]
    by_cases hi : i < 4 <;> simp [hi]
  rw [Finset.sum_congr rfl (fun i _ => hstep i), ← Finset.sum_filter,
    show (Finset.range 8).filter (· < 4) = Finset.range 4 from by decide]

/-- Popcount of the shifted high nibble `byte >> 4` = sum of `byte`'s high 4 bits. -/
theorem cbd_nibble_high (byte shifted : U8) (hsh : shifted.val = byte.val >>> 4) :
    (∑ i ∈ Finset.range 8, (shifted.bv.getLsbD i).toNat)
      = ∑ i ∈ Finset.range 4, (byte.val.testBit (4 + i)).toNat := by
  have hbyte : byte.val < 2 ^ 8 := by have := byte.hBounds; omega
  have hstep : ∀ i, (shifted.bv.getLsbD i).toNat
      = if i < 4 then (byte.val.testBit (4 + i)).toNat else 0 := by
    intro i
    rw [show shifted.bv.getLsbD i = shifted.val.testBit i from by rw [UScalar.val, BitVec.getLsbD],
      hsh, Nat.testBit_shiftRight]
    by_cases hi : i < 4
    · rw [if_pos hi]
    · rw [if_neg hi]
      have : byte.val.testBit (4 + i) = false := by
        apply Nat.testBit_lt_two_pow
        calc byte.val < 2 ^ 8 := hbyte
          _ ≤ 2 ^ (4 + i) := Nat.pow_le_pow_right (by norm_num) (by omega)
      rw [this]; rfl
  rw [Finset.sum_congr rfl (fun i _ => hstep i), ← Finset.sum_filter,
    show (Finset.range 8).filter (· < 4) = Finset.range 4 from by decide]

/-- **`cbd_loop0` loop spec (μ = 8 nibble path).**  The `Enumerate` cursor
`iter.iter.i` = current coefficient index; coefficients `[0, iter.iter.i)` of
`out` already hold their CBD sample. -/
theorem cbd_loop0_spec
    (iter : core.iter.adapters.enumerate.Enumerate (core.slice.iter.Iter U8))
    (out : RingElem) (buf : Slice U8)
    (hbuf : iter.iter.slice = buf)
    (hlen : buf.val.length = 256)
    (hcount : iter.count.val = iter.iter.i)
    (hi_le : iter.iter.i ≤ 256)
    (hinv : ∀ k, k < iter.iter.i → (((out.val[k]!).val : ZMod (2 ^ 13))) = cbdVal buf 8 4 k) :
    gen.cbd_loop0 iter out
      ⦃ (r : RingElem) => ∀ k, k < 256 → (((r.val[k]!).val : ZMod (2 ^ 13))) = cbdVal buf 8 4 k ⦄ := by
  unfold gen.cbd_loop0
  have hlen_slice : iter.iter.slice.len.val = 256 := by
    rw [hbuf]; simp [Slice.len, hlen]
  by_cases hlt : iter.iter.i < iter.iter.slice.len
  · -- SOME branch
    have hi_lt256 : iter.iter.i < 256 := by
      have : iter.iter.i < iter.iter.slice.len.val := hlt; omega
    let* ⟨ o, iter1, ho, hslice1, hi1, hcount1 ⟩ ←
      enumSliceIter_next_some iter hlt (by rw [hcount]; have := hi_lt256; scalar_tac)
    rw [ho]
    simp only []
    generalize hbdef : iter.iter.slice[iter.iter.i] = byte
    show (do
        let i1 ← lift (byte &&& 15#u8)
        let i2 ← core.num.U8.count_ones i1
        let a ← lift (UScalar.cast UScalarTy.U16 i2)
        let i3 ← byte >>> 4#i32
        let i4 ← core.num.U8.count_ones i3
        let b ← lift (UScalar.cast UScalarTy.U16 i4)
        let i5 ← lift (core.num.U16.wrapping_sub a b)
        let a1 ← Array.update out iter.count i5
        gen.cbd_loop0 iter1 a1)
      ⦃ (r : RingElem) => ∀ k, k < 256 → (((r.val[k]!).val : ZMod (2 ^ 13))) = cbdVal buf 8 4 k ⦄
    have hout_len : out.val.length = 256 := List.Vector.length_val out
    have hb_bound : iter.iter.i < iter.iter.slice.val.length := by rw [hbuf, hlen]; exact hi_lt256
    have hbyte : byte.val = (buf.val[iter.iter.i]!).val := by
      have hbe : byte = iter.iter.slice.val[iter.iter.i]'hb_bound :=
        hbdef.symm.trans (Slice.getElem_Nat_eq iter.iter.slice iter.iter.i hb_bound)
      rw [hbe, ← getElem!_pos iter.iter.slice.val iter.iter.i hb_bound, hbuf]
    -- nibble → cbdX bridges
    have hstream_low : ∑ j ∈ Finset.range 4, (byte.val.testBit j).toNat
        = cbdX buf 4 (8 * iter.iter.i) := by
      unfold cbdX; apply Finset.sum_congr rfl; intro j hj; simp only [Finset.mem_range] at hj
      rw [hbyte]; unfold streamBit
      rw [show (8 * iter.iter.i + j) / 8 = iter.iter.i from by omega,
        show (8 * iter.iter.i + j) % 8 = j from by omega]
    have hstream_high : ∑ j ∈ Finset.range 4, (byte.val.testBit (4 + j)).toNat
        = cbdX buf 4 (8 * iter.iter.i + 4) := by
      unfold cbdX; apply Finset.sum_congr rfl; intro j hj; simp only [Finset.mem_range] at hj
      rw [hbyte]; unfold streamBit
      rw [show (8 * iter.iter.i + 4 + j) / 8 = iter.iter.i from by omega,
        show (8 * iter.iter.i + 4 + j) % 8 = 4 + j from by omega]
    -- x = popcount(byte & 15)
    rw [show lift (byte &&& 15#u8) = ok (byte &&& 15#u8) from rfl, bind_tc_ok]
    let* ⟨ i2, hi2 ⟩ ← U8.count_ones_spec
    have hx : i2.val = cbdX buf 4 (8 * iter.iter.i) := by rw [hi2, cbd_nibble_low, hstream_low]
    have hx_le : i2.val ≤ UScalar.max UScalarTy.U16 := by
      rw [hx]; have := cbdX_le buf 4 (8 * iter.iter.i)
      simp only [UScalar.max, UScalarTy.numBits]; omega
    let* ⟨ a, ha ⟩ ← UScalar.cast_inBounds_spec .U16 i2 hx_le
    -- y = popcount(byte >> 4)
    let* ⟨ i3, hi3, hi3bv ⟩ ← Std.U8.ShiftRight_IScalar_spec byte 4#i32 (by decide) (by decide)
    let* ⟨ i4, hi4 ⟩ ← U8.count_ones_spec
    have hy : i4.val = cbdX buf 4 (8 * iter.iter.i + 4) := by
      rw [hi4, cbd_nibble_high byte i3 hi3, hstream_high]
    have hy_le : i4.val ≤ UScalar.max UScalarTy.U16 := by
      rw [hy]; have := cbdX_le buf 4 (8 * iter.iter.i + 4)
      simp only [UScalar.max, UScalarTy.numBits]; omega
    let* ⟨ b, hb ⟩ ← UScalar.cast_inBounds_spec .U16 i4 hy_le
    rw [show lift (core.num.U16.wrapping_sub a b) = ok (core.num.U16.wrapping_sub a b) from rfl,
      bind_tc_ok]
    -- coefficient value
    have hcoeff : ((core.num.U16.wrapping_sub a b).val : ZMod (2 ^ 13)) = cbdVal buf 8 4 iter.iter.i := by
      rw [wrapping_sub_toZMod13, ha, hb, hx, hy]; unfold cbdVal; norm_num
    -- write out[iter.count] = coeff
    have hcount_lt : iter.count.val < 256 := by rw [hcount]; exact hi_lt256
    let* ⟨ a1, ha1 ⟩ ← Array.update_spec
    have ha1v : a1.val = out.val.set iter.iter.i (core.num.U16.wrapping_sub a b) := by
      rw [ha1, Array.set_val_eq, hcount]
    -- recurse
    apply WP.spec_mono (cbd_loop0_spec iter1 a1 buf (by rw [hslice1, hbuf])
      hlen (by rw [hcount1, hi1, hcount]) (by rw [hi1]; omega) ?inv)
    case inv =>
      intro k hk_lt
      rw [hi1] at hk_lt
      rcases Nat.lt_succ_iff_lt_or_eq.mp hk_lt with hk | hk
      · rw [ha1v, getElem!_pos (out.val.set iter.iter.i _) k (by simpa [hout_len] using (by omega : k < 256)),
          List.getElem_set_ne (by omega),
          ← getElem!_pos out.val k (by simpa [hout_len] using (by omega : k < 256))]
        exact hinv k hk
      · subst hk
        rw [ha1v, getElem!_pos (out.val.set iter.iter.i _) iter.iter.i (by simpa [hout_len] using hi_lt256),
          List.getElem_set_self]
        exact hcoeff
    intro r hr; exact hr
  · -- NONE branch
    have hge : iter.iter.i ≥ iter.iter.slice.len := by
      simp only [not_lt] at hlt; exact hlt
    have hi_eq : iter.iter.i = 256 := by
      have : iter.iter.slice.len.val ≤ iter.iter.i := hge; omega
    let* ⟨ o, iter1, ho, hnone ⟩ ← enumSliceIter_next_none
    rw [ho]
    simp only []
    intro k hk
    exact hinv k (by omega)
  termination_by iter.iter.slice.len.val - iter.iter.i
  decreasing_by scalar_decr_tac

/-! ## `gen.cbd` — dispatch on `MU = 8` (nibble path vs general). -/

theorem cbd_spec (MU : Usize) (buf : Slice U8) (out : RingElem)
    (hMU : MU.val = 6 ∨ MU.val = 8 ∨ MU.val = 10)
    (hlen : buf.val.length = 32 * MU.val) :
    gen.cbd MU buf out
      ⦃ (r : RingElem) => ∀ k, k < 256 →
          (((r.val[k]!).val : ZMod (2 ^ 13))) = cbdVal buf MU.val (MU.val / 2) k ⦄ := by
  unfold gen.cbd
  let* ⟨ half, hhalf ⟩ ← Std.Usize.div_spec
  have hhb : half.val ≤ 5 := by rw [hhalf]; omega
  have hhb4 : 4 ≤ MU.val := by omega
  let* ⟨ ish, hish, hishbv ⟩ ← Std.U32.ShiftLeft_spec 1#u32 half (by omega)
  have hishv : ish.val = 2 ^ half.val := by
    rw [hish, Nat.shiftLeft_eq, one_mul, Nat.mod_eq_of_lt]
    · simp only [Std.U32.size, Std.U32.numBits]
      calc 2 ^ half.val ≤ 2 ^ 5 := Nat.pow_le_pow_right (by norm_num) hhb
        _ < 2 ^ 32 := by norm_num
  let* ⟨ mask, hmask ⟩ ← Std.U32.sub_spec (x := ish) (y := 1#u32)
    (by show (1#u32).val ≤ ish.val
        have e1 : (1#u32).val = 1 := rfl
        have := Nat.one_le_two_pow (n := half.val)
        omega)
  have hmaskv : mask.val = 2 ^ half.val - 1 := by rw [hmask, hishv]
  by_cases h8 : MU = 8#usize
  · -- MU = 8: nibble path via cbd_loop0
    simp only [h8, reduceIte]
    have hMU8 : MU.val = 8 := by scalar_tac
    have hlen256 : buf.val.length = 256 := by rw [hlen, hMU8]
    let* ⟨ i1, hi1s, hi1i ⟩ ← sliceIter_spec
    rw [show core.iter.traits.iterator.Iterator.enumerate.trait_default
          (core.iter.traits.iterator.IteratorSliceIter U8) i1
        = ok { iter := i1, count := 0#usize } from by
      unfold core.iter.traits.iterator.Iterator.enumerate.trait_default
        core.iter.traits.iterator.Iterator.enumerate.default; rfl, bind_tc_ok]
    apply WP.spec_mono (cbd_loop0_spec { iter := i1, count := 0#usize } out buf
      (by show i1.slice = buf; rw [hi1s]) hlen256 (by show (0#usize).val = i1.i; scalar_tac)
      (by show i1.i ≤ 256; scalar_tac)
      (by intro k hk; replace hk : k < i1.i := hk; rw [hi1i] at hk; omega))
    intro r hr k hk
    exact hr k hk
  · -- MU ∈ {6, 10}: general path via cbd_loop1
    simp only [h8, reduceIte]
    have hMUne8 : MU.val ≠ 8 := fun h => h8 (by scalar_tac)
    have hMU6_10 : MU.val = 6 ∨ MU.val = 10 := by omega
    have hMUle : MU.val ≤ 10 := by omega
    have hout_len : out.val.length = 256 := List.Vector.length_val out
    let* ⟨ s, to_back, hs_val, hto_back ⟩ ← Array.to_slice_mut_spec
    let* ⟨ it0, it_back, h_it_slice, h_it_zero, h_it_back ⟩ ← iter_mut_spec
    have hs_len : s.val.length = 256 := by rw [hs_val]; exact hout_len
    have hit_len : it0.slice.length = 256 := by rw [h_it_slice]; exact hs_len
    let* ⟨ r_iter, hri_len, hri_writes ⟩ ←
      cbd_loop1_spec MU it0 (fun im => im) buf half mask 0#usize hhalf hmaskv ⟨hhb4, hMUle⟩ hlen
        (by rw [h_it_zero]; simp) it0.slice rfl hit_len (by rw [h_it_zero]; omega)
        (fun _ him => him)
        (fun _ _ j hj => by rw [h_it_zero] at hj; omega)
        (fun _ _ _ _ _ => rfl)
    simp only [h_it_back]
    intro k hk
    have hri_len256 : r_iter.slice.length = 256 := hri_len.trans hit_len
    have h_val_eq : (to_back r_iter.slice).val = r_iter.slice.val := by
      rw [hto_back]; exact Std.Array.from_slice_val out r_iter.slice hri_len256
    rw [show (to_back r_iter.slice).val[k]! = r_iter.slice.val[k]! from
      congrArg (fun l => l[k]!) h_val_eq]
    rw [hri_writes k (by rw [hit_len]; exact hk), hhalf]

/-! ## Bridge to the spec's `bytesToBits` centered-binomial coefficients. -/

open Spec (bytesToBits)

/-- `cbdX` (a popcount over `cnt` stream bits) equals the spec's `Fin`-sum over the
bridged bit stream `bytesToBits (sliceToBytes …)`. -/
theorem cbdX_eq_specSum (buf1 : Slice U8) (μ p cnt : ℕ) (h : buf1.length = 32 * μ)
    (hbnd : ∀ (j : Fin cnt), p + j.val < 8 * (32 * μ)) :
    cbdX buf1 cnt p
      = ∑ j : Fin cnt,
          ((bytesToBits (sliceToBytes buf1 (32 * μ) h))[p + j.val]'(by simpa using hbnd j)).toNat := by
  unfold cbdX
  rw [← Fin.sum_univ_eq_sum_range (fun i => streamBit buf1 (p + i)) cnt]
  apply Finset.sum_congr rfl
  intro j _
  exact (streamBit_eq_bit buf1 μ (p + j.val) h (hbnd j)).symm

/-- The CBD coefficient (`cbdVal`) computed by the Rust sampler equals the spec's
`(x : ZMod 2¹³) - (y : ZMod 2¹³)` centered-binomial value for coefficient `k`. -/
theorem cbdVal_eq_specCoeff (buf1 : Slice U8) (μ k : ℕ) (h : buf1.length = 32 * μ) (hk : k < 256) :
    cbdVal buf1 μ (μ / 2) k
      = ((∑ j : Fin (μ / 2),
            ((bytesToBits (sliceToBytes buf1 (32 * μ) h))[μ * k + j.val]'(by
              have h2 : μ * k + j.val < μ * (k + 1) := by rw [Nat.mul_succ]; omega
              have h3 : μ * (k + 1) ≤ μ * 256 := Nat.mul_le_mul_left μ (by omega)
              have _h4 : μ * 256 = 8 * (32 * μ) := by ring
              simpa using (by omega : μ * k + j.val < 8 * (32 * μ)))).toNat : ℕ) : ZMod (2 ^ 13))
      - ((∑ j : Fin (μ / 2),
            ((bytesToBits (sliceToBytes buf1 (32 * μ) h))[μ * k + μ / 2 + j.val]'(by
              have h2 : μ * k + μ / 2 + j.val < μ * (k + 1) := by rw [Nat.mul_succ]; omega
              have h3 : μ * (k + 1) ≤ μ * 256 := Nat.mul_le_mul_left μ (by omega)
              have _h4 : μ * 256 = 8 * (32 * μ) := by ring
              simpa using (by omega : μ * k + μ / 2 + j.val < 8 * (32 * μ)))).toNat : ℕ) : ZMod (2 ^ 13)) := by
  unfold cbdVal
  rw [cbdX_eq_specSum buf1 μ (μ * k) (μ / 2) h (fun j => by
        have h2 : μ * k + j.val < μ * (k + 1) := by rw [Nat.mul_succ]; omega
        have h3 : μ * (k + 1) ≤ μ * 256 := Nat.mul_le_mul_left μ (by omega)
        have h4 : μ * 256 = 8 * (32 * μ) := by ring
        omega),
      cbdX_eq_specSum buf1 μ (μ * k + μ / 2) (μ / 2) h (fun j => by
        have h2 : μ * k + μ / 2 + j.val < μ * (k + 1) := by rw [Nat.mul_succ]; omega
        have h3 : μ * (k + 1) ≤ μ * 256 := Nat.mul_le_mul_left μ (by omega)
        have h4 : μ * 256 = 8 * (32 * μ) := by ring
        omega)]

end Kopis.Properties
