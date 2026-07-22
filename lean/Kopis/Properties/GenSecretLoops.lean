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

/-- **`cbd_loop3` (generic fallback) loop spec.**  Coefficients `[0, iter.i)` already hold the CBD
sample; `bit_pos = μ·iter.i`. -/
theorem cbd_loop3_spec (MU : Usize) (iter : core.slice.iter.IterMut U16)
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
    gen.cbd_loop3 MU iter back buf half mask bit_pos
      ⦃ (r : core.slice.iter.IterMut U16) =>
          ∃ (_h_len : r.slice.length = orig_slice.length),
            ∀ (j : Nat) (_hj : j < orig_slice.length),
              (((r.slice.val[j]!).val : ZMod (2 ^ 13))) = cbdVal buf MU.val half.val j ⦄ := by
  unfold gen.cbd_loop3
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
      (cbd_loop3_spec MU iter1 (fun im => back (next_back im (some (core.num.U16.wrapping_sub a b))))
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

/-! ## Bit-window helpers -/

/-- **Popcount of a window equals a sum of stream bits.**  If the low `len` bits of `w`
are the stream bits `[base, base+len)`, then summing them gives `∑ streamBit`.  Stated
via `testBit` so it applies whether `w` was built from one byte or two. -/
theorem popcount_eq_streamBits (buf : Slice U8) (base len : ℕ) (w : U32)
    (hbits : ∀ i, i < len →
      w.val.testBit i = (buf.val[(base + i) / 8]!).val.testBit ((base + i) % 8)) :
    ∑ i ∈ Finset.range len, (w.bv.getLsbD i).toNat
      = ∑ i ∈ Finset.range len, streamBit buf (base + i) := by
  apply Finset.sum_congr rfl
  intro i hi
  simp only [Finset.mem_range] at hi
  have hbridge : w.bv.getLsbD i = w.val.testBit i := by rw [UScalar.val, BitVec.getLsbD]
  rw [hbridge, hbits i hi]
  rfl

/-- Bit `b < 16` of the two-byte little-endian window at `bi` is the corresponding
stream bit.  (The three-byte version is `window_testBit` in `GenSecret.lean`; the fast
paths never need a third byte because a coefficient spans at most 2 bytes here.) -/
theorem window2_testBit (buf : Slice U8) (bi b : ℕ) (hb : b < 16) :
    (((buf.val[bi]!).val) + 2 ^ 8 * (buf.val[bi+1]!).val).testBit b
      = (buf.val[(8*bi+b)/8]!).val.testBit ((8*bi+b)%8) := by
  have h0 : (buf.val[bi]!).val < 2 ^ 8 := by have := (buf.val[bi]!).hBounds; omega
  rw [show ((buf.val[bi]!).val) + 2 ^ 8 * (buf.val[bi+1]!).val
        = 2 ^ 8 * (buf.val[bi+1]!).val + (buf.val[bi]!).val from by ring,
    Nat.testBit_two_pow_mul_add _ h0 b]
  by_cases hb8 : b < 8
  · rw [if_pos hb8, show (8*bi+b)/8 = bi from by omega, show (8*bi+b)%8 = b from by omega]
  · rw [if_neg hb8, show (8*bi+b)/8 = bi+1 from by omega, show (8*bi+b)%8 = b-8 from by omega]

/-- Bit `b < 8` of a single byte is the corresponding stream bit. -/
theorem window1_testBit (buf : Slice U8) (bi b : ℕ) (hb : b < 8) :
    (buf.val[bi]!).val.testBit b = (buf.val[(8*bi+b)/8]!).val.testBit ((8*bi+b)%8) := by
  rw [show (8*bi+b)/8 = bi from by omega, show (8*bi+b)%8 = b from by omega]

/-! ## `cbd_diff` — one coefficient

`cbd_diff raw half mask` is `popcount(raw & mask) - popcount((raw >>> half) & mask)`.
Given that the low `2·half` bits of `raw` are the stream bits `[base, base + 2·half)`,
its result is the CBD value at that position. -/

/-- **Spec for the extracted `gen.cbd_diff`.** -/
theorem cbd_diff_spec (buf : Slice U8) (base : ℕ) (raw : U32) (half : U32) (mask : U32)
    (hhalf : half.val ≤ 8) (hmask : mask.val = 2 ^ half.val - 1)
    (hbits : ∀ i, i < 2 * half.val →
      raw.val.testBit i = (buf.val[(base + i) / 8]!).val.testBit ((base + i) % 8)) :
    gen.cbd_diff raw half mask
      ⦃ (r : U16) => ((r.val : ℕ) : ZMod (2 ^ 13))
          = ((cbdX buf half.val base : ℕ) : ZMod (2 ^ 13))
            - ((cbdX buf half.val (base + half.val) : ℕ) : ZMod (2 ^ 13)) ⦄ := by
  unfold gen.cbd_diff
  -- x = popcount (raw &&& mask)
  rw [show lift (raw &&& mask) = ok (raw &&& mask) from rfl, bind_tc_ok]
  let* ⟨ i1, hi1 ⟩ ← U32.count_ones_spec
  have hx : i1.val = cbdX buf half.val base := by
    rw [hi1, popcount_low_mask raw mask half.val (by omega) (mask_getLsbD mask half.val hmask)]
    unfold cbdX
    exact popcount_eq_streamBits buf base half.val raw (fun i hi => hbits i (by omega))
  have hx_le : i1.val ≤ UScalar.max UScalarTy.U16 := by
    rw [hx]; have := cbdX_le buf half.val base
    simp only [UScalar.max, UScalarTy.numBits]; omega
  let* ⟨ a, ha ⟩ ← UScalar.cast_inBounds_spec .U16 i1 hx_le
  -- y = popcount ((raw >>> half) &&& mask)
  let* ⟨ i2, hi2, hi2bv ⟩ ← Std.U32.ShiftRight_spec raw half (by omega)
  rw [show lift (i2 &&& mask) = ok (i2 &&& mask) from rfl, bind_tc_ok]
  let* ⟨ i4, hi4 ⟩ ← U32.count_ones_spec
  have hy : i4.val = cbdX buf half.val (base + half.val) := by
    rw [hi4, popcount_low_mask i2 mask half.val (by omega) (mask_getLsbD mask half.val hmask)]
    unfold cbdX
    refine popcount_eq_streamBits buf (base + half.val) half.val i2 (fun i hi => ?_)
    rw [show base + half.val + i = base + (half.val + i) from by omega, hi2,
      Nat.testBit_shiftRight]
    exact hbits (half.val + i) (by omega)
  have hy_le : i4.val ≤ UScalar.max UScalarTy.U16 := by
    rw [hy]; have := cbdX_le buf half.val (base + half.val)
    simp only [UScalar.max, UScalarTy.numBits]; omega
  let* ⟨ b, hb ⟩ ← UScalar.cast_inBounds_spec .U16 i4 hy_le
  rw [wrapping_sub_toZMod13, ha, hb, hx, hy]


/-! ## Byte-group helpers for the specialised paths

Each fast path reads a fixed group of bytes and slices four coefficients out of it.
These two lemmas package the two window shapes that occur: a single byte, and two
consecutive bytes combined little-endian. -/

/-- Reading one byte of `buf` as a `U32`. -/
theorem cbd_byte_val {buf : Slice U8} {i : Usize} {b : U32}
    (_hi : i.val < buf.val.length) (hb : b.val = (buf.val[i.val]!).val) :
    b.val = (buf.val[i.val]!).val := hb

/-- Low `len` bits of a single byte, shifted by `sh`, are stream bits from `8·bi + sh`. -/
theorem cbd_bits_of_byte (buf : Slice U8) (bi sh len : ℕ) (w : U32)
    (hsh : sh + len ≤ 8) (hw : w.val = (buf.val[bi]!).val >>> sh) :
    ∀ i, i < len → w.val.testBit i
      = (buf.val[(8 * bi + sh + i) / 8]!).val.testBit ((8 * bi + sh + i) % 8) := by
  intro i hi
  rw [show 8 * bi + sh + i = 8 * bi + (sh + i) from by omega, hw, Nat.testBit_shiftRight]
  exact window1_testBit buf bi (sh + i) (by omega)

/-- Low `len` bits of a two-byte little-endian window, shifted by `sh`. -/
theorem cbd_bits_of_pair (buf : Slice U8) (bi sh len : ℕ) (w : U32)
    (hsh : sh + len ≤ 16) (hw : w.val
      = ((buf.val[bi]!).val + 2 ^ 8 * (buf.val[bi+1]!).val) >>> sh) :
    ∀ i, i < len → w.val.testBit i
      = (buf.val[(8 * bi + sh + i) / 8]!).val.testBit ((8 * bi + sh + i) % 8) := by
  intro i hi
  rw [show 8 * bi + sh + i = 8 * bi + (sh + i) from by omega, hw, Nat.testBit_shiftRight]
  exact window2_testBit buf bi (sh + i) (by omega)


/-- **One coefficient of a fast path.**  Specialises `cbd_diff_spec` to the position
`base = μ·k` used by `cbdVal`, so each of the four coefficients in a group is discharged
by supplying only its bit window. -/
theorem cbd_diff_coeff_spec (buf : Slice U8) (mu half k : ℕ) (raw hf mk : U32)
    (hmu : mu = 2 * half) (hhf : hf.val = half) (hhalf : half ≤ 8)
    (hmk : mk.val = 2 ^ half - 1)
    (hbits : ∀ i, i < mu → raw.val.testBit i
      = (buf.val[(mu * k + i) / 8]!).val.testBit ((mu * k + i) % 8)) :
    gen.cbd_diff raw hf mk
      ⦃ (r : U16) => ((r.val : ℕ) : ZMod (2 ^ 13)) = cbdVal buf mu half k ⦄ := by
  have h := cbd_diff_spec buf (mu * k) raw hf mk (by omega) (by rw [hhf]; exact hmk)
    (by rw [hhf]; intro i hi; exact hbits i (by omega))
  refine WP.spec_mono h ?_
  intro r hr
  rw [hr, hhf]
  unfold cbdVal
  rfl


/-! ## `cbd_loop2` — the `MU = 6` fast path (Kopis-1024)

Four coefficients per 3-byte group.  Coefficient `4g+t` occupies stream bits
`[6(4g+t), 6(4g+t)+6)`, i.e. bits `6t .. 6t+6` of the group, so the four windows are
byte `3g` unshifted, the pair `(3g, 3g+1)` shifted by 6, the pair `(3g+1, 3g+2)` shifted
by 4, and byte `3g+2` shifted by 2. -/

theorem cbd_loop2_spec (iter : core.ops.range.Range Usize) (buf : Slice U8) (out : RingElem)
    (hend : iter.«end».val = 64) (hstart : iter.start.val ≤ 64)
    (hlen : buf.val.length = 32 * 6)
    (hinv : ∀ k, k < 4 * iter.start.val →
      (((out.val[k]!).val : ZMod (2 ^ 13))) = cbdVal buf 6 3 k) :
    gen.cbd_loop2 iter buf out
      ⦃ (r : RingElem) => ∀ k, k < 256 →
          (((r.val[k]!).val : ZMod (2 ^ 13))) = cbdVal buf 6 3 k ⦄ := by
  unfold gen.cbd_loop2
  have hout_len : out.val.length = 256 := List.Vector.length_val out
  by_cases hlt : iter.start.val < iter.«end».val
  · let* ⟨ g, iter1, ho, hstart', hend' ⟩ ← core.iter.range.IteratorRange.next_Usize_some_spec
    rw [ho]; simp only
    have hg : iter.start.val < 64 := by omega
    -- the three bytes of the group
    let* ⟨ i, hi ⟩ ← Std.Usize.mul_spec (x := 3#usize) (y := iter.start) (by scalar_tac)
    have hiv : i.val = 3 * iter.start.val := by rw [hi]
    have hb0lt : i.val < buf.val.length := by rw [hiv, hlen]; omega
    let* ⟨ i1, hi1 ⟩ ← Slice.index_usize_spec
    let* ⟨ b0, hb0 ⟩ ← UScalar.cast_inBounds_spec .U32 i1 (by scalar_tac)
    let* ⟨ i2, hi2 ⟩ ← Std.Usize.add_spec (x := i) (y := 1#usize) (by scalar_tac)
    have hb1lt : i2.val < buf.val.length := by rw [hi2, hiv, hlen]; omega
    let* ⟨ i3, hi3 ⟩ ← Slice.index_usize_spec
    let* ⟨ b1, hb1 ⟩ ← UScalar.cast_inBounds_spec .U32 i3 (by scalar_tac)
    let* ⟨ i4, hi4 ⟩ ← Std.Usize.add_spec (x := i) (y := 2#usize) (by scalar_tac)
    have hb2lt : i4.val < buf.val.length := by rw [hi4, hiv, hlen]; omega
    let* ⟨ i5, hi5 ⟩ ← Slice.index_usize_spec
    let* ⟨ b2, hb2 ⟩ ← UScalar.cast_inBounds_spec .U32 i5 (by scalar_tac)
    -- byte values
    have hb0v : b0.val = (buf.val[3 * iter.start.val]!).val := by
      rw [hb0, hi1, ← getElem!_pos buf.val i.val hb0lt, hiv]
    have hb1v : b1.val = (buf.val[3 * iter.start.val + 1]!).val := by
      rw [hb1, hi3, ← getElem!_pos buf.val i2.val hb1lt, hi2, hiv]
    have hb2v : b2.val = (buf.val[3 * iter.start.val + 2]!).val := by
      rw [hb2, hi5, ← getElem!_pos buf.val i4.val hb2lt, hi4, hiv]
    let* ⟨ o1, ho1 ⟩ ← Std.Usize.mul_spec (x := 4#usize) (y := iter.start) (by scalar_tac)
    have ho1v : o1.val = 4 * iter.start.val := by rw [ho1]
    have hb0lt8 : b0.val < 2 ^ 8 := by rw [hb0v]; have := (buf.val[3 * iter.start.val]!).hBounds; omega
    have hb1lt8 : b1.val < 2 ^ 8 := by
      rw [hb1v]; have := (buf.val[3 * iter.start.val + 1]!).hBounds; omega
    have hb2lt8 : b2.val < 2 ^ 8 := by
      rw [hb2v]; have := (buf.val[3 * iter.start.val + 2]!).hBounds; omega
    have hsz : U32.size = 2 ^ 32 := by simp [Std.U32.size, Std.U32.numBits]
    -- coefficient 4g+0 : byte 3g, unshifted
    have hbits0 : ∀ i, i < 6 → b0.val.testBit i
        = (buf.val[(6 * (4 * iter.start.val) + i) / 8]!).val.testBit
            ((6 * (4 * iter.start.val) + i) % 8) := by
      have h := cbd_bits_of_byte buf (3 * iter.start.val) 0 6 b0 (by omega) (by rw [hb0v]; simp)
      intro i hi
      rw [show 6 * (4 * iter.start.val) + i = 8 * (3 * iter.start.val) + 0 + i from by ring]
      exact h i hi
    let* ⟨ i6, hi6 ⟩ ← cbd_diff_coeff_spec buf 6 3 (4 * iter.start.val) b0 3#u32 7#u32
      rfl rfl (by omega) (by decide) hbits0
    let* ⟨ a, ha ⟩ ← Array.update_spec
    -- coefficient 4g+1 : pair (3g, 3g+1) shifted by 6
    let* ⟨ i7, hi7, hi7bv ⟩ ← Std.U32.ShiftLeft_IScalar_spec b1 8#i32 (by decide) (by decide)
    have hi7v : i7.val = b1.val * 2 ^ 8 := by
      rw [hi7, Nat.shiftLeft_eq, Nat.mod_eq_of_lt (show b1.val * 2 ^ 8 < U32.size from by
        rw [hsz]; omega)]
    rw [show lift (b0 ||| i7) = ok (b0 ||| i7) from rfl, bind_tc_ok]
    have hi8v : (b0 ||| i7).val = (buf.val[3 * iter.start.val]!).val
        + 2 ^ 8 * (buf.val[3 * iter.start.val + 1]!).val := by
      rw [UScalar.val_or, hi7v, lor_mul_of_lt hb0lt8, hb0v, hb1v]; ring
    let* ⟨ i9, hi9, hi9bv ⟩ ← Std.U32.ShiftRight_IScalar_spec (b0 ||| i7) 6#i32 (by decide) (by decide)
    have hbits1 : ∀ i, i < 6 → i9.val.testBit i
        = (buf.val[(6 * (4 * iter.start.val + 1) + i) / 8]!).val.testBit
            ((6 * (4 * iter.start.val + 1) + i) % 8) := by
      have h := cbd_bits_of_pair buf (3 * iter.start.val) 6 6 i9 (by omega)
        (by rw [hi9, hi8v])
      intro i hi
      rw [show 6 * (4 * iter.start.val + 1) + i = 8 * (3 * iter.start.val) + 6 + i from by ring]
      exact h i hi
    let* ⟨ i10, hi10 ⟩ ← cbd_diff_coeff_spec buf 6 3 (4 * iter.start.val + 1) i9 3#u32 7#u32
      rfl rfl (by omega) (by decide) hbits1
    let* ⟨ i11, hi11 ⟩ ← Std.Usize.add_spec (x := o1) (y := 1#usize) (by scalar_tac)
    let* ⟨ a1, ha1 ⟩ ← Array.update_spec
    -- coefficient 4g+2 : pair (3g+1, 3g+2) shifted by 4
    let* ⟨ i12, hi12, hi12bv ⟩ ← Std.U32.ShiftLeft_IScalar_spec b2 8#i32 (by decide) (by decide)
    have hi12v : i12.val = b2.val * 2 ^ 8 := by
      rw [hi12, Nat.shiftLeft_eq, Nat.mod_eq_of_lt (show b2.val * 2 ^ 8 < U32.size from by
        rw [hsz]; omega)]
    rw [show lift (b1 ||| i12) = ok (b1 ||| i12) from rfl, bind_tc_ok]
    have hi13v : (b1 ||| i12).val = (buf.val[3 * iter.start.val + 1]!).val
        + 2 ^ 8 * (buf.val[3 * iter.start.val + 1 + 1]!).val := by
      rw [UScalar.val_or, hi12v, lor_mul_of_lt hb1lt8, hb1v, hb2v,
        show 3 * iter.start.val + 1 + 1 = 3 * iter.start.val + 2 from by ring]; ring
    let* ⟨ i14, hi14, hi14bv ⟩ ←
      Std.U32.ShiftRight_IScalar_spec (b1 ||| i12) 4#i32 (by decide) (by decide)
    have hbits2 : ∀ i, i < 6 → i14.val.testBit i
        = (buf.val[(6 * (4 * iter.start.val + 2) + i) / 8]!).val.testBit
            ((6 * (4 * iter.start.val + 2) + i) % 8) := by
      have h := cbd_bits_of_pair buf (3 * iter.start.val + 1) 4 6 i14 (by omega)
        (by rw [hi14, hi13v])
      intro i hi
      rw [show 6 * (4 * iter.start.val + 2) + i = 8 * (3 * iter.start.val + 1) + 4 + i from by ring]
      exact h i hi
    let* ⟨ i15, hi15 ⟩ ← cbd_diff_coeff_spec buf 6 3 (4 * iter.start.val + 2) i14 3#u32 7#u32
      rfl rfl (by omega) (by decide) hbits2
    let* ⟨ i16, hi16 ⟩ ← Std.Usize.add_spec (x := o1) (y := 2#usize) (by scalar_tac)
    let* ⟨ a2, ha2 ⟩ ← Array.update_spec
    -- coefficient 4g+3 : byte 3g+2 shifted by 2
    let* ⟨ i17, hi17, hi17bv ⟩ ← Std.U32.ShiftRight_IScalar_spec b2 2#i32 (by decide) (by decide)
    have hbits3 : ∀ i, i < 6 → i17.val.testBit i
        = (buf.val[(6 * (4 * iter.start.val + 3) + i) / 8]!).val.testBit
            ((6 * (4 * iter.start.val + 3) + i) % 8) := by
      have h := cbd_bits_of_byte buf (3 * iter.start.val + 2) 2 6 i17 (by omega)
        (by rw [hi17, hb2v])
      intro i hi
      rw [show 6 * (4 * iter.start.val + 3) + i = 8 * (3 * iter.start.val + 2) + 2 + i from by ring]
      exact h i hi
    let* ⟨ i18, hi18 ⟩ ← cbd_diff_coeff_spec buf 6 3 (4 * iter.start.val + 3) i17 3#u32 7#u32
      rfl rfl (by omega) (by decide) hbits3
    let* ⟨ i19, hi19 ⟩ ← Std.Usize.add_spec (x := o1) (y := 3#usize) (by scalar_tac)
    let* ⟨ a3, ha3 ⟩ ← Array.update_spec
    -- the four writes, as a list update
    have hav : a.val = out.val.set (4 * iter.start.val) i6 := by rw [ha, Array.set_val_eq, ho1v]
    have ha1v : a1.val = a.val.set (4 * iter.start.val + 1) i10 := by
      rw [ha1, Array.set_val_eq, hi11, ho1v]
    have ha2v : a2.val = a1.val.set (4 * iter.start.val + 2) i15 := by
      rw [ha2, Array.set_val_eq, hi16, ho1v]
    have ha3v : a3.val = a2.val.set (4 * iter.start.val + 3) i18 := by
      rw [ha3, Array.set_val_eq, hi19, ho1v]
    have hlen_a : a.val.length = 256 := by rw [hav, List.length_set, hout_len]
    have hlen_a1 : a1.val.length = 256 := by rw [ha1v, List.length_set, hlen_a]
    have hlen_a2 : a2.val.length = 256 := by rw [ha2v, List.length_set, hlen_a1]
    -- recurse
    apply WP.spec_mono (cbd_loop2_spec iter1 buf a3 (by rw [hend']; exact hend)
      (by rw [hstart']; omega) hlen ?inv)
    case inv =>
      intro k hk
      rw [hstart'] at hk
      have hk256 : k < 256 := by omega
      have hget : ∀ (l : List U16) (n : ℕ) (v : U16), l.length = 256 → k < 256 → n < 256 →
          (l.set n v)[k]! = if n = k then v else l[k]! := by
        intro l n v hl hk' hn
        rw [getElem!_pos (l.set n v) k (by simpa [hl] using hk'), List.getElem_set,
          ← getElem!_pos l k (by simpa [hl] using hk')]
      rw [ha3v, hget a2.val _ _ hlen_a2 hk256 (by omega),
        ha2v, hget a1.val _ _ hlen_a1 hk256 (by omega),
        ha1v, hget a.val _ _ hlen_a hk256 (by omega),
        hav, hget out.val _ _ hout_len hk256 (by omega)]
      by_cases h3 : 4 * iter.start.val + 3 = k
      · rw [if_pos h3, ← h3]; exact hi18
      · rw [if_neg h3]
        by_cases h2 : 4 * iter.start.val + 2 = k
        · rw [if_pos h2, ← h2]; exact hi15
        · rw [if_neg h2]
          by_cases h1 : 4 * iter.start.val + 1 = k
          · rw [if_pos h1, ← h1]; exact hi10
          · rw [if_neg h1]
            by_cases h0 : 4 * iter.start.val = k
            · rw [if_pos h0, ← h0]; exact hi6
            · rw [if_neg h0]; exact hinv k (by omega)
    intro r hr; exact hr
  · let* ⟨ o, iter1, ho, hiter1 ⟩ ← core.iter.range.IteratorRange.next_Usize_none_spec
    rw [ho]; simp only
    intro k hk
    exact hinv k (by omega)
  termination_by iter.«end».val - iter.start.val
  decreasing_by scalar_decr_tac


/-! ## `cbd_loop1` — the `MU = 10` fast path (Kopis-512)

Four coefficients per 5-byte group.  Coefficient `4g+t` occupies stream bits
`[10(4g+t), +10)`, so each window is a *pair* of consecutive bytes: `(5g+t, 5g+t+1)`
shifted by `2t`. -/

theorem cbd_loop1_spec (iter : core.ops.range.Range Usize) (buf : Slice U8) (out : RingElem)
    (hend : iter.«end».val = 64) (hstart : iter.start.val ≤ 64)
    (hlen : buf.val.length = 32 * 10)
    (hinv : ∀ k, k < 4 * iter.start.val →
      (((out.val[k]!).val : ZMod (2 ^ 13))) = cbdVal buf 10 5 k) :
    gen.cbd_loop1 iter buf out
      ⦃ (r : RingElem) => ∀ k, k < 256 →
          (((r.val[k]!).val : ZMod (2 ^ 13))) = cbdVal buf 10 5 k ⦄ := by
  unfold gen.cbd_loop1
  have hout_len : out.val.length = 256 := List.Vector.length_val out
  by_cases hlt : iter.start.val < iter.«end».val
  · let* ⟨ g, iter1, ho, hstart', hend' ⟩ ← core.iter.range.IteratorRange.next_Usize_some_spec
    rw [ho]; simp only
    have hg : iter.start.val < 64 := by omega
    have hsz : U32.size = 2 ^ 32 := by simp [Std.U32.size, Std.U32.numBits]
    -- the five bytes of the group
    let* ⟨ i, hi ⟩ ← Std.Usize.mul_spec (x := 5#usize) (y := iter.start) (by scalar_tac)
    have hiv : i.val = 5 * iter.start.val := by rw [hi]
    have hlt0 : i.val < buf.val.length := by rw [hiv, hlen]; omega
    let* ⟨ i1, hi1 ⟩ ← Slice.index_usize_spec
    let* ⟨ b0, hb0 ⟩ ← UScalar.cast_inBounds_spec .U32 i1 (by scalar_tac)
    let* ⟨ i2, hi2 ⟩ ← Std.Usize.add_spec (x := i) (y := 1#usize) (by scalar_tac)
    have hlt1 : i2.val < buf.val.length := by rw [hi2, hiv, hlen]; omega
    let* ⟨ i3, hi3 ⟩ ← Slice.index_usize_spec
    let* ⟨ b1, hb1 ⟩ ← UScalar.cast_inBounds_spec .U32 i3 (by scalar_tac)
    let* ⟨ i4, hi4 ⟩ ← Std.Usize.add_spec (x := i) (y := 2#usize) (by scalar_tac)
    have hlt2 : i4.val < buf.val.length := by rw [hi4, hiv, hlen]; omega
    let* ⟨ i5, hi5 ⟩ ← Slice.index_usize_spec
    let* ⟨ b2, hb2 ⟩ ← UScalar.cast_inBounds_spec .U32 i5 (by scalar_tac)
    let* ⟨ i6, hi6 ⟩ ← Std.Usize.add_spec (x := i) (y := 3#usize) (by scalar_tac)
    have hlt3 : i6.val < buf.val.length := by rw [hi6, hiv, hlen]; omega
    let* ⟨ i7, hi7 ⟩ ← Slice.index_usize_spec
    let* ⟨ b3, hb3 ⟩ ← UScalar.cast_inBounds_spec .U32 i7 (by scalar_tac)
    let* ⟨ i8, hi8 ⟩ ← Std.Usize.add_spec (x := i) (y := 4#usize) (by scalar_tac)
    have hlt4 : i8.val < buf.val.length := by rw [hi8, hiv, hlen]; omega
    let* ⟨ i9, hi9 ⟩ ← Slice.index_usize_spec
    let* ⟨ b4, hb4 ⟩ ← UScalar.cast_inBounds_spec .U32 i9 (by scalar_tac)
    -- byte values
    have hb0v : b0.val = (buf.val[5 * iter.start.val]!).val := by
      rw [hb0, hi1, ← getElem!_pos buf.val i.val hlt0, hiv]
    have hb1v : b1.val = (buf.val[5 * iter.start.val + 1]!).val := by
      rw [hb1, hi3, ← getElem!_pos buf.val i2.val hlt1, hi2, hiv]
    have hb2v : b2.val = (buf.val[5 * iter.start.val + 2]!).val := by
      rw [hb2, hi5, ← getElem!_pos buf.val i4.val hlt2, hi4, hiv]
    have hb3v : b3.val = (buf.val[5 * iter.start.val + 3]!).val := by
      rw [hb3, hi7, ← getElem!_pos buf.val i6.val hlt3, hi6, hiv]
    have hb4v : b4.val = (buf.val[5 * iter.start.val + 4]!).val := by
      rw [hb4, hi9, ← getElem!_pos buf.val i8.val hlt4, hi8, hiv]
    have hb0lt : b0.val < 2 ^ 8 := by
      rw [hb0v]; have := (buf.val[5 * iter.start.val]!).hBounds; omega
    have hb1lt : b1.val < 2 ^ 8 := by
      rw [hb1v]; have := (buf.val[5 * iter.start.val + 1]!).hBounds; omega
    have hb2lt : b2.val < 2 ^ 8 := by
      rw [hb2v]; have := (buf.val[5 * iter.start.val + 2]!).hBounds; omega
    have hb3lt : b3.val < 2 ^ 8 := by
      rw [hb3v]; have := (buf.val[5 * iter.start.val + 3]!).hBounds; omega
    have hb4lt : b4.val < 2 ^ 8 := by
      rw [hb4v]; have := (buf.val[5 * iter.start.val + 4]!).hBounds; omega
    let* ⟨ o1, ho1 ⟩ ← Std.Usize.mul_spec (x := 4#usize) (y := iter.start) (by scalar_tac)
    have ho1v : o1.val = 4 * iter.start.val := by rw [ho1]
    -- coefficient 4g+0 : pair (5g, 5g+1), no shift
    let* ⟨ i10, hi10, hi10bv ⟩ ← Std.U32.ShiftLeft_IScalar_spec b1 8#i32 (by decide) (by decide)
    have hi10v : i10.val = b1.val * 2 ^ 8 := by
      rw [hi10, Nat.shiftLeft_eq, Nat.mod_eq_of_lt (show b1.val * 2 ^ 8 < U32.size from by
        rw [hsz]; omega)]
    rw [show lift (b0 ||| i10) = ok (b0 ||| i10) from rfl, bind_tc_ok]
    have hi11v : (b0 ||| i10).val = (buf.val[5 * iter.start.val]!).val
        + 2 ^ 8 * (buf.val[5 * iter.start.val + 1]!).val := by
      rw [UScalar.val_or, hi10v, lor_mul_of_lt hb0lt, hb0v, hb1v]; ring
    have hbits0 : ∀ i', i' < 10 → (b0 ||| i10).val.testBit i'
        = (buf.val[(10 * (4 * iter.start.val) + i') / 8]!).val.testBit
            ((10 * (4 * iter.start.val) + i') % 8) := by
      have h := cbd_bits_of_pair buf (5 * iter.start.val) 0 10 (b0 ||| i10) (by omega)
        (by rw [hi11v]; simp)
      intro i' hi'
      rw [show 10 * (4 * iter.start.val) + i' = 8 * (5 * iter.start.val) + 0 + i' from by ring]
      exact h i' hi'
    let* ⟨ i12, hi12 ⟩ ← cbd_diff_coeff_spec buf 10 5 (4 * iter.start.val) (b0 ||| i10)
      5#u32 31#u32 rfl rfl (by omega) (by decide) hbits0
    let* ⟨ a, ha ⟩ ← Array.update_spec
    -- coefficient 4g+1 : pair (5g+1, 5g+2) shifted by 2
    let* ⟨ i13, hi13, hi13bv ⟩ ← Std.U32.ShiftLeft_IScalar_spec b2 8#i32 (by decide) (by decide)
    have hi13v : i13.val = b2.val * 2 ^ 8 := by
      rw [hi13, Nat.shiftLeft_eq, Nat.mod_eq_of_lt (show b2.val * 2 ^ 8 < U32.size from by
        rw [hsz]; omega)]
    rw [show lift (b1 ||| i13) = ok (b1 ||| i13) from rfl, bind_tc_ok]
    have hi14v : (b1 ||| i13).val = (buf.val[5 * iter.start.val + 1]!).val
        + 2 ^ 8 * (buf.val[5 * iter.start.val + 1 + 1]!).val := by
      rw [UScalar.val_or, hi13v, lor_mul_of_lt hb1lt, hb1v, hb2v,
        show 5 * iter.start.val + 1 + 1 = 5 * iter.start.val + 2 from by ring]; ring
    let* ⟨ i15, hi15, hi15bv ⟩ ←
      Std.U32.ShiftRight_IScalar_spec (b1 ||| i13) 2#i32 (by decide) (by decide)
    have hbits1 : ∀ i', i' < 10 → i15.val.testBit i'
        = (buf.val[(10 * (4 * iter.start.val + 1) + i') / 8]!).val.testBit
            ((10 * (4 * iter.start.val + 1) + i') % 8) := by
      have h := cbd_bits_of_pair buf (5 * iter.start.val + 1) 2 10 i15 (by omega)
        (by rw [hi15, hi14v])
      intro i' hi'
      rw [show 10 * (4 * iter.start.val + 1) + i'
            = 8 * (5 * iter.start.val + 1) + 2 + i' from by ring]
      exact h i' hi'
    let* ⟨ i16, hi16 ⟩ ← cbd_diff_coeff_spec buf 10 5 (4 * iter.start.val + 1) i15
      5#u32 31#u32 rfl rfl (by omega) (by decide) hbits1
    let* ⟨ i17, hi17 ⟩ ← Std.Usize.add_spec (x := o1) (y := 1#usize) (by scalar_tac)
    let* ⟨ a1, ha1 ⟩ ← Array.update_spec
    -- coefficient 4g+2 : pair (5g+2, 5g+3) shifted by 4
    let* ⟨ i18, hi18, hi18bv ⟩ ← Std.U32.ShiftLeft_IScalar_spec b3 8#i32 (by decide) (by decide)
    have hi18v : i18.val = b3.val * 2 ^ 8 := by
      rw [hi18, Nat.shiftLeft_eq, Nat.mod_eq_of_lt (show b3.val * 2 ^ 8 < U32.size from by
        rw [hsz]; omega)]
    rw [show lift (b2 ||| i18) = ok (b2 ||| i18) from rfl, bind_tc_ok]
    have hi19v : (b2 ||| i18).val = (buf.val[5 * iter.start.val + 2]!).val
        + 2 ^ 8 * (buf.val[5 * iter.start.val + 2 + 1]!).val := by
      rw [UScalar.val_or, hi18v, lor_mul_of_lt hb2lt, hb2v, hb3v,
        show 5 * iter.start.val + 2 + 1 = 5 * iter.start.val + 3 from by ring]; ring
    let* ⟨ i20, hi20, hi20bv ⟩ ←
      Std.U32.ShiftRight_IScalar_spec (b2 ||| i18) 4#i32 (by decide) (by decide)
    have hbits2 : ∀ i', i' < 10 → i20.val.testBit i'
        = (buf.val[(10 * (4 * iter.start.val + 2) + i') / 8]!).val.testBit
            ((10 * (4 * iter.start.val + 2) + i') % 8) := by
      have h := cbd_bits_of_pair buf (5 * iter.start.val + 2) 4 10 i20 (by omega)
        (by rw [hi20, hi19v])
      intro i' hi'
      rw [show 10 * (4 * iter.start.val + 2) + i'
            = 8 * (5 * iter.start.val + 2) + 4 + i' from by ring]
      exact h i' hi'
    let* ⟨ i21, hi21 ⟩ ← cbd_diff_coeff_spec buf 10 5 (4 * iter.start.val + 2) i20
      5#u32 31#u32 rfl rfl (by omega) (by decide) hbits2
    let* ⟨ i22, hi22 ⟩ ← Std.Usize.add_spec (x := o1) (y := 2#usize) (by scalar_tac)
    let* ⟨ a2, ha2 ⟩ ← Array.update_spec
    -- coefficient 4g+3 : pair (5g+3, 5g+4) shifted by 6
    let* ⟨ i23, hi23, hi23bv ⟩ ← Std.U32.ShiftLeft_IScalar_spec b4 8#i32 (by decide) (by decide)
    have hi23v : i23.val = b4.val * 2 ^ 8 := by
      rw [hi23, Nat.shiftLeft_eq, Nat.mod_eq_of_lt (show b4.val * 2 ^ 8 < U32.size from by
        rw [hsz]; omega)]
    rw [show lift (b3 ||| i23) = ok (b3 ||| i23) from rfl, bind_tc_ok]
    have hi24v : (b3 ||| i23).val = (buf.val[5 * iter.start.val + 3]!).val
        + 2 ^ 8 * (buf.val[5 * iter.start.val + 3 + 1]!).val := by
      rw [UScalar.val_or, hi23v, lor_mul_of_lt hb3lt, hb3v, hb4v,
        show 5 * iter.start.val + 3 + 1 = 5 * iter.start.val + 4 from by ring]; ring
    let* ⟨ i25, hi25, hi25bv ⟩ ←
      Std.U32.ShiftRight_IScalar_spec (b3 ||| i23) 6#i32 (by decide) (by decide)
    have hbits3 : ∀ i', i' < 10 → i25.val.testBit i'
        = (buf.val[(10 * (4 * iter.start.val + 3) + i') / 8]!).val.testBit
            ((10 * (4 * iter.start.val + 3) + i') % 8) := by
      have h := cbd_bits_of_pair buf (5 * iter.start.val + 3) 6 10 i25 (by omega)
        (by rw [hi25, hi24v])
      intro i' hi'
      rw [show 10 * (4 * iter.start.val + 3) + i'
            = 8 * (5 * iter.start.val + 3) + 6 + i' from by ring]
      exact h i' hi'
    let* ⟨ i26, hi26 ⟩ ← cbd_diff_coeff_spec buf 10 5 (4 * iter.start.val + 3) i25
      5#u32 31#u32 rfl rfl (by omega) (by decide) hbits3
    let* ⟨ i27, hi27 ⟩ ← Std.Usize.add_spec (x := o1) (y := 3#usize) (by scalar_tac)
    let* ⟨ a3, ha3 ⟩ ← Array.update_spec
    have hav : a.val = out.val.set (4 * iter.start.val) i12 := by rw [ha, Array.set_val_eq, ho1v]
    have ha1v : a1.val = a.val.set (4 * iter.start.val + 1) i16 := by
      rw [ha1, Array.set_val_eq, hi17, ho1v]
    have ha2v : a2.val = a1.val.set (4 * iter.start.val + 2) i21 := by
      rw [ha2, Array.set_val_eq, hi22, ho1v]
    have ha3v : a3.val = a2.val.set (4 * iter.start.val + 3) i26 := by
      rw [ha3, Array.set_val_eq, hi27, ho1v]
    have hlen_a : a.val.length = 256 := by rw [hav, List.length_set, hout_len]
    have hlen_a1 : a1.val.length = 256 := by rw [ha1v, List.length_set, hlen_a]
    have hlen_a2 : a2.val.length = 256 := by rw [ha2v, List.length_set, hlen_a1]
    apply WP.spec_mono (cbd_loop1_spec iter1 buf a3 (by rw [hend']; exact hend)
      (by rw [hstart']; omega) hlen ?inv)
    case inv =>
      intro k hk
      rw [hstart'] at hk
      have hk256 : k < 256 := by omega
      have hget : ∀ (l : List U16) (n : ℕ) (v : U16), l.length = 256 → k < 256 → n < 256 →
          (l.set n v)[k]! = if n = k then v else l[k]! := by
        intro l n v hl hk' hn
        rw [getElem!_pos (l.set n v) k (by simpa [hl] using hk'), List.getElem_set,
          ← getElem!_pos l k (by simpa [hl] using hk')]
      rw [ha3v, hget a2.val _ _ hlen_a2 hk256 (by omega),
        ha2v, hget a1.val _ _ hlen_a1 hk256 (by omega),
        ha1v, hget a.val _ _ hlen_a hk256 (by omega),
        hav, hget out.val _ _ hout_len hk256 (by omega)]
      by_cases h3 : 4 * iter.start.val + 3 = k
      · rw [if_pos h3, ← h3]; exact hi26
      · rw [if_neg h3]
        by_cases h2 : 4 * iter.start.val + 2 = k
        · rw [if_pos h2, ← h2]; exact hi21
        · rw [if_neg h2]
          by_cases h1 : 4 * iter.start.val + 1 = k
          · rw [if_pos h1, ← h1]; exact hi16
          · rw [if_neg h1]
            by_cases h0 : 4 * iter.start.val = k
            · rw [if_pos h0, ← h0]; exact hi12
            · rw [if_neg h0]; exact hinv k (by omega)
    intro r hr; exact hr
  · let* ⟨ o, iter1, ho, hiter1 ⟩ ← core.iter.range.IteratorRange.next_Usize_none_spec
    rw [ho]; simp only
    intro k hk
    exact hinv k (by omega)
  termination_by iter.«end».val - iter.start.val
  decreasing_by scalar_decr_tac

/-! ## `gen.cbd` — dispatch on `MU = 8` (nibble path vs general). -/

theorem cbd_spec (MU : Usize) (buf : Slice U8) (out : RingElem)
    (hMU : MU.val = 6 ∨ MU.val = 8 ∨ MU.val = 10)
    (hlen : buf.val.length = 32 * MU.val) :
    gen.cbd MU buf out
      ⦃ (r : RingElem) => ∀ k, k < 256 →
          (((r.val[k]!).val : ZMod (2 ^ 13))) = cbdVal buf MU.val (MU.val / 2) k ⦄ := by
  unfold gen.cbd
  -- the `assert_eq!(buf.len(), RING_DEG * MU / 8)` prologue
  have hMUle10' : MU.val ≤ 10 := by omega
  have hRD : (consts.RING_DEG).val = 256 := by simp [consts.RING_DEG]
  have hsz : ∀ x : ℕ, x ≤ Usize.max → x < UScalar.size .Usize := by
    intro x hx
    have h1 : UScalar.size .Usize = 2 ^ System.Platform.numBits := by
      simp only [UScalar.size, UScalarTy.Usize_numBits_eq]
    have h2 : (Usize.max : ℕ) = 2 ^ System.Platform.numBits - 1 := by
      simp only [Usize.max, Usize.numBits, UScalarTy.Usize_numBits_eq]
    have h3 : 0 < 2 ^ System.Platform.numBits := by positivity
    omega
  have hprod : 256 * MU.val ≤ Usize.max := by
    have : (256 : ℕ) * MU.val ≤ 256 * 10 := Nat.mul_le_mul_left _ hMUle10'
    have hmax : (2560 : ℕ) ≤ Usize.max := by scalar_tac
    omega
  let* ⟨ _mm, _hmm ⟩ ← Std.Usize.mul_spec (x := consts.RING_DEG) (y := MU) (by rw [hRD]; exact hprod)
  simp only [lift, bind_tc_ok]
  let* ⟨ right_val, hrv ⟩ ← Std.Usize.div_spec
  have hrvv : right_val.val = 32 * MU.val := by
    rw [hrv, Std.Usize.wrapping_mul_val_eq, hRD, Nat.mod_eq_of_lt (hsz _ hprod),
      show 256 * MU.val = 32 * MU.val * 8 from by ring, Nat.mul_div_cancel _ (by norm_num)]
  have hmeq : Slice.len buf = right_val :=
    UScalar.eq_of_val_eq (by rw [Slice.len_val, hrvv]; exact hlen)
  rw [show massert (Slice.len buf = right_val) = ok () from by
    simp only [massert, if_pos hmeq], bind_tc_ok]
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
  · -- MU ∈ {6, 10}: the two specialised group paths.  (`cbd_loop3_spec` above still
    -- proves the generic fallback, which is now unreachable for the shipped parameter
    -- sets but is kept for any future `MU`.)
    simp only [h8, reduceIte]
    have hMUne8 : MU.val ≠ 8 := fun h => h8 (by scalar_tac)
    have hMU6_10 : MU.val = 6 ∨ MU.val = 10 := by omega
    by_cases h10 : MU = 10#usize
    · -- Kopis-512: 4 coefficients per 5-byte group
      simp only [h10, reduceIte]
      have hMU10 : MU.val = 10 := by scalar_tac
      let* ⟨ i1, hi1 ⟩ ← Std.Usize.div_spec
      have hi1v : i1.val = 64 := by rw [hi1]; simp [consts.RING_DEG]
      apply WP.spec_mono (cbd_loop1_spec { start := 0#usize, «end» := i1 } buf out
        hi1v (by show (0#usize).val ≤ 64; scalar_tac) (by rw [hlen, hMU10])
        (by intro k hk; simp at hk))
      intro r hr k hk
      exact hr k hk
    · simp only [h10, reduceIte]
      by_cases h6 : MU = 6#usize
      · -- Kopis-1024: 4 coefficients per 3-byte group
        simp only [h6, reduceIte]
        have hMU6 : MU.val = 6 := by scalar_tac
        let* ⟨ i1, hi1 ⟩ ← Std.Usize.div_spec
        have hi1v : i1.val = 64 := by rw [hi1]; simp [consts.RING_DEG]
        apply WP.spec_mono (cbd_loop2_spec { start := 0#usize, «end» := i1 } buf out
          hi1v (by show (0#usize).val ≤ 64; scalar_tac) (by rw [hlen, hMU6])
          (by intro k hk; simp at hk))
        intro r hr k hk
        exact hr k hk
      · -- unreachable: `hMU` restricts `MU` to 6, 8 or 10
        exfalso
        rcases hMU6_10 with h | h
        · exact h6 (by scalar_tac)
        · exact h10 (by scalar_tac)

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
