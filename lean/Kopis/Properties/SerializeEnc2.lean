import Kopis.Properties.SerializeEnc
open Aeneas Aeneas.Std Result RustKopisSerial
open scoped BigOperators
namespace Kopis.Properties

set_option maxHeartbeats 2000000
set_option maxRecDepth 4000

/-- The little-endian value of the first `m` bytes of `buf`. -/
def byteVal (buf : Slice U8) (m : ℕ) : ℕ := ∑ p ∈ Finset.range m, (buf.val[p]!).val * 256 ^ p

/-- Packed value of the first `k` coefficients of `data`, each masked to `n` bits. -/
def packedVal (data : Slice U16) (n k : ℕ) : ℕ :=
  ∑ i ∈ Finset.range k, (data.val[i]!.val % 2 ^ n) * 2 ^ (n * i)

theorem byteVal_succ (buf : Slice U8) (m : ℕ) :
    byteVal buf (m + 1) = byteVal buf m + (buf.val[m]!).val * 256 ^ m := by
  unfold byteVal; rw [Finset.sum_range_succ]

theorem packedVal_succ (data : Slice U16) (n k : ℕ) :
    packedVal data n (k + 1) = packedVal data n k + (data.val[k]!.val % 2 ^ n) * 2 ^ (n * k) := by
  unfold packedVal; rw [Finset.sum_range_succ]

/-- Base-256 decomposition: `x = (low f bytes) + (x >>> 8f) · 256^f`. -/
theorem natByteDecomp (x f : ℕ) :
    x = (∑ t ∈ Finset.range f, ((x >>> (8 * t)) % 256) * 256 ^ t) + (x >>> (8 * f)) * 256 ^ f := by
  induction f with
  | zero => simp
  | succ f ih =>
    rw [Finset.sum_range_succ]
    have h1 : x >>> (8 * (f + 1)) = (x >>> (8 * f)) / 2 ^ 8 := by
      rw [show 8 * (f + 1) = 8 * f + 8 from by ring, Nat.shiftRight_add, Nat.shiftRight_eq_div_pow]
    have hstep : (x >>> (8 * f)) * 256 ^ f
        = ((x >>> (8 * f)) % 256) * 256 ^ f + (x >>> (8 * (f + 1))) * 256 ^ (f + 1) := by
      rw [h1, pow_succ]
      have hdm : x >>> (8 * f) = (x >>> (8 * f)) % 256 + (x >>> (8 * f)) / 2 ^ 8 * 256 := by omega
      conv_lhs => rw [hdm]
      ring
    rw [show (∑ t ∈ Finset.range f, ((x >>> (8 * t)) % 256) * 256 ^ t)
          + ((x >>> (8 * f)) % 256) * 256 ^ f + (x >>> (8 * (f + 1))) * 256 ^ (f + 1)
        = (∑ t ∈ Finset.range f, ((x >>> (8 * t)) % 256) * 256 ^ t)
          + ((x >>> (8 * f)) % 256 * 256 ^ f + (x >>> (8 * (f + 1))) * 256 ^ (f + 1)) from by ring,
      ← hstep]
    exact ih

theorem byteVal_lt (buf : Slice U8) (m : ℕ) : byteVal buf m < 256 ^ m := by
  induction m with
  | zero => simp [byteVal]
  | succ m ih =>
    rw [byteVal_succ, pow_succ]
    have hb : (buf.val[m]!).val ≤ 255 := by have := U8.lt_succ_max (buf.val[m]!); omega
    have hp : (0 : ℕ) < 256 ^ m := by positivity
    nlinarith [ih, hb, hp]

theorem byteVal_split (buf : Slice U8) (k m : ℕ) (h : k ≤ m) :
    byteVal buf m
      = byteVal buf k + 256 ^ k * (∑ q ∈ Finset.range (m - k), (buf.val[k + q]!).val * 256 ^ q) := by
  unfold byteVal
  rw [← Finset.sum_range_add_sum_Ico _ h, Finset.mul_sum]
  congr 1
  rw [Finset.sum_Ico_eq_sum_range]
  apply Finset.sum_congr rfl
  intro q _; rw [pow_add]; ring

theorem byteVal_getByte (buf : Slice U8) (m p : ℕ) (hp : p < m) :
    byteVal buf m / 256 ^ p % 256 = (buf.val[p]!).val := by
  have hb : (buf.val[p]!).val < 256 := by have := U8.lt_succ_max (buf.val[p]!); omega
  have fact1 : byteVal buf m % 256 ^ (p + 1) = byteVal buf (p + 1) := by
    rw [byteVal_split buf (p + 1) m hp, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (byteVal_lt buf (p + 1))]
  have fact2 : byteVal buf (p + 1) / 256 ^ p = (buf.val[p]!).val := by
    rw [byteVal_succ, Nat.add_mul_div_right _ _ (by positivity : 0 < 256 ^ p),
      Nat.div_eq_of_lt (byteVal_lt buf p), Nat.zero_add]
  rw [← fact2, ← fact1, pow_succ, Nat.mod_mul_right_div_self]

@[step]
theorem sliceIter_spec' {T : Type} (s : Slice T) :
  core.slice.Slice.iter s ⦃ it => it.slice = s ∧ it.i = 0 ⦄ := by
  simp [core.slice.Slice.iter]

@[step]
theorem sliceIter_next_spec' {T : Type} (it : core.slice.iter.Iter T) (h : it.i < it.slice.len) :
  core.slice.iter.IteratorSliceIter.next it
  ⦃ p => p.1 = some (it.slice[it.i]) ∧ p.2.slice = it.slice ∧ p.2.i = it.i + 1 ⦄ := by
  simp only [core.slice.iter.IteratorSliceIter.next, h, ↓reduceDIte]; simp

@[step]
theorem sliceIter_next_none' {T : Type} (it : core.slice.iter.Iter T) (h : it.i ≥ it.slice.len) :
  core.slice.iter.IteratorSliceIter.next it ⦃ p => p.1 = none ∧ p.2 = it ⦄ := by
  simp only [core.slice.iter.IteratorSliceIter.next]; split
  · agrind
  · simp

theorem byteVal_congr (a b : Slice U8) (m : ℕ) (h : ∀ p, p < m → a.val[p]! = b.val[p]!) :
    byteVal a m = byteVal b m := by
  unfold byteVal; apply Finset.sum_congr rfl; intro p hp; rw [h p (Finset.mem_range.mp hp)]

/-- `byteVal` after the inner flush: the first `byte_pos` bytes are untouched, and the
next `f` bytes are the low-`f` bytes of `window1`. -/
theorem byteVal_after_flush (out_buf out_buf1 : Slice U8) (byte_pos f : ℕ) (window1 : ℕ)
    (hunch : ∀ q, q < byte_pos → out_buf1.val[q]! = out_buf.val[q]!)
    (hbytes : ∀ t, t < f → (out_buf1.val[byte_pos + t]!).val = (window1 >>> (8 * t)) % 256) :
    byteVal out_buf1 (byte_pos + f)
      = byteVal out_buf byte_pos
        + (∑ t ∈ Finset.range f, ((window1 >>> (8 * t)) % 256) * 256 ^ t) * 256 ^ byte_pos := by
  unfold byteVal
  rw [Finset.sum_range_add, Finset.sum_mul]
  congr 1
  · apply Finset.sum_congr rfl; intro p hp
    rw [hunch p (Finset.mem_range.mp hp)]
  · apply Finset.sum_congr rfl; intro t ht
    rw [hbytes t (Finset.mem_range.mp ht), pow_add]; ring

/-- **Outer packing loop.**  Processes elements `[iter.i, 256)`; maintains that the
written bytes plus the window encode the packed bit-stream of processed coefficients. -/
theorem serialize_loop0_spec (iter : core.slice.iter.Iter U16) (out_buf : Slice U8)
    (bits_per_elem : Usize) (bitmask window : U32) (bits_in_window byte_pos : Usize)
    (n : ℕ) (orig : Slice U16)
    (hslice : iter.slice = orig) (horiglen : orig.val.length = 256)
    (hn : bits_per_elem.val = n) (hn_rng : 1 ≤ n ∧ n ≤ 13)
    (hmask : bitmask.val = 2 ^ n - 1)
    (hbuflen : out_buf.val.length = 32 * n)
    (hbiw8 : bits_in_window.val < 8)
    (hwin : window.val < 2 ^ bits_in_window.val)
    (hbits : 8 * byte_pos.val + bits_in_window.val = n * iter.i)
    (hval : byteVal out_buf byte_pos.val + window.val * 256 ^ byte_pos.val = packedVal orig n iter.i)
    (hi_le : iter.i ≤ 256) :
    ser.serialize_loop0 iter out_buf bits_per_elem bitmask window bits_in_window byte_pos
      ⦃ (r : Slice U8 × Usize) =>
          r.1.val.length = 32 * n ∧ r.2.val = 0 ∧ byteVal r.1 (32 * n) = packedVal orig n 256 ⦄ := by
  unfold ser.serialize_loop0
  have hlen256 : iter.slice.len.val = 256 := by
    rw [hslice]; simp [Slice.len, horiglen]
  by_cases hlt : iter.i < iter.slice.len
  · have hi_lt256 : iter.i < 256 := by have : iter.i < iter.slice.len.val := hlt; omega
    let* ⟨ o, iter1, ho, hslice1, hi1 ⟩ ← sliceIter_next_spec'
    rw [ho]; simp only []
    generalize hedef : iter.slice[iter.i] = elem
    -- element value
    have helemv : elem.val = (orig.val[iter.i]!).val := by
      have hb : iter.i < iter.slice.val.length := by rw [hslice, horiglen]; exact hi_lt256
      have : elem = iter.slice.val[iter.i]'hb :=
        hedef.symm.trans (Slice.getElem_Nat_eq iter.slice iter.i hb)
      rw [this, ← getElem!_pos iter.slice.val iter.i hb, hslice]
    have helem_lt : elem.val < 2 ^ 16 := by have := elem.hBounds; omega
    -- i = cast .U32 elem
    rw [show lift (UScalar.cast .U32 elem) = ok (UScalar.cast .U32 elem) from rfl, bind_tc_ok]
    have hiv : (UScalar.cast UScalarTy.U32 elem).val = elem.val := by
      rw [UScalar.cast_val_eq]; simp only [UScalarTy.numBits]; omega
    -- i1 = i & bitmask
    rw [show lift (UScalar.cast .U32 elem &&& bitmask) = ok (UScalar.cast .U32 elem &&& bitmask) from rfl,
      bind_tc_ok]
    have hi1v : (UScalar.cast .U32 elem &&& bitmask).val = elem.val % 2 ^ n := by
      rw [UScalar.val_and, hiv, hmask, Nat.and_two_pow_sub_one_eq_mod]
    have hi1_lt : (UScalar.cast .U32 elem &&& bitmask).val < 2 ^ n := by
      rw [hi1v]; exact Nat.mod_lt _ (by positivity)
    -- i2 = i1 <<< bits_in_window
    let* ⟨ i2, hi2, hi2bv ⟩ ← Std.U32.ShiftLeft_spec (UScalar.cast .U32 elem &&& bitmask) bits_in_window (by omega)
    have hbound : (elem.val % 2 ^ n) * 2 ^ bits_in_window.val < U32.size := by
      have h1 : elem.val % 2 ^ n < 2 ^ n := Nat.mod_lt _ (by positivity)
      have h3 : 2 ^ n ≤ 2 ^ 13 := Nat.pow_le_pow_right (by norm_num) (by omega)
      have h2 : 2 ^ bits_in_window.val ≤ 2 ^ 8 := Nat.pow_le_pow_right (by norm_num) (by omega)
      have key : (elem.val % 2 ^ n) * 2 ^ bits_in_window.val ≤ 2 ^ 13 * 2 ^ 8 :=
        Nat.mul_le_mul (by omega) h2
      have e1 : (2 : ℕ) ^ 13 * 2 ^ 8 = 2097152 := by norm_num
      have e2 : U32.size = 4294967296 := by simp [Std.U32.size, Std.U32.numBits]
      omega
    have hi2v : i2.val = (elem.val % 2 ^ n) * 2 ^ bits_in_window.val := by
      rw [hi2, hi1v, Nat.shiftLeft_eq, Nat.mod_eq_of_lt hbound]
    -- window1 = window ||| i2
    rw [show lift (window ||| i2) = ok (window ||| i2) from rfl, bind_tc_ok]
    have hwin1v : (window ||| i2).val = window.val + (elem.val % 2 ^ n) * 2 ^ bits_in_window.val := by
      rw [UScalar.val_or, hi2v, lor_mul_of_lt hwin]
    -- window1 fits in `bits_in_window + n` bits
    have hwin1_lt : (window ||| i2).val < 2 ^ (bits_in_window.val + n) := by
      rw [hwin1v, pow_add]
      have hlt2 : (elem.val % 2 ^ n) * 2 ^ bits_in_window.val + 2 ^ bits_in_window.val
          ≤ 2 ^ n * 2 ^ bits_in_window.val := by
        rw [← Nat.succ_mul]
        apply Nat.mul_le_mul_right
        have := Nat.mod_lt elem.val (show 0 < 2 ^ n by positivity); omega
      have : 2 ^ n * 2 ^ bits_in_window.val = 2 ^ bits_in_window.val * 2 ^ n := by ring
      omega
    -- bits_in_window1 = bits_in_window + n
    let* ⟨ biw1, hbiw1 ⟩ ← Std.Usize.add_spec (show bits_in_window.val + bits_per_elem.val ≤ Usize.max by
      have hmax : (21 : ℕ) ≤ Usize.max := by scalar_tac
      have := hn; omega)
    have hbiw1v : biw1.val = bits_in_window.val + n := by rw [hbiw1, hn]
    have hf_bnd : byte_pos.val + biw1.val / 8 ≤ out_buf.length := by
      rw [Slice.length, hbuflen, hbiw1v]
      have h2 : 8 * byte_pos.val + (bits_in_window.val + n) = n * (iter.i + 1) := by
        rw [Nat.mul_succ]; omega
      have h3 : n * (iter.i + 1) ≤ n * 256 := Nat.mul_le_mul_left n (by omega)
      omega
    have hbiw1_le32 : biw1.val ≤ 32 := by rw [hbiw1v]; omega
    let* ⟨ o1, w2, b2, bp1, hpb, hpp, hpw, hplen, hpbytes, hpunch ⟩ ←
      serialize_loop0_loop0_spec out_buf (window ||| i2) biw1 byte_pos hf_bnd hbiw1_le32
    -- window2 fits in `b2` bits
    have hw2_lt : w2.val < 2 ^ b2.val := by
      rw [hpw, hpb, Nat.shiftRight_eq_div_pow, Nat.div_lt_iff_lt_mul (by positivity), ← pow_add,
        show biw1.val % 8 + 8 * (biw1.val / 8) = biw1.val from by omega, hbiw1v]
      exact hwin1_lt
    -- new value invariant
    have hpp' : bp1.val = byte_pos.val + biw1.val / 8 := hpp
    have hval' : byteVal o1 bp1.val + w2.val * 256 ^ bp1.val = packedVal orig n (iter.i + 1) := by
      set f := biw1.val / 8 with hf_def
      set S := ∑ t ∈ Finset.range f, (((window ||| i2).val >>> (8 * t)) % 256) * 256 ^ t with hS_def
      have hbv : byteVal o1 bp1.val = byteVal out_buf byte_pos.val + S * 256 ^ byte_pos.val := by
        rw [hpp']
        exact byteVal_after_flush out_buf o1 byte_pos.val f (window ||| i2).val
          (fun q hq => hpunch q (Or.inl hq)) (fun t ht => hpbytes t ht)
      have hsum : S + w2.val * 256 ^ f = (window ||| i2).val := by
        rw [hS_def, hpw]; exact (natByteDecomp (window ||| i2).val f).symm
      have h256 : (256 : ℕ) ^ byte_pos.val = 2 ^ (8 * byte_pos.val) := by
        rw [show (256 : ℕ) = 2 ^ 8 from by norm_num, ← pow_mul]
      have hcombine : byteVal o1 bp1.val + w2.val * 256 ^ bp1.val
          = byteVal out_buf byte_pos.val + (window ||| i2).val * 256 ^ byte_pos.val := by
        rw [hbv, hpp', pow_add]
        have : S * 256 ^ byte_pos.val + w2.val * (256 ^ byte_pos.val * 256 ^ f)
            = (window ||| i2).val * 256 ^ byte_pos.val := by
          rw [show w2.val * (256 ^ byte_pos.val * 256 ^ f)
                = w2.val * 256 ^ f * 256 ^ byte_pos.val from by ring, ← add_mul, hsum]
        omega
      have hprod : (elem.val % 2 ^ n) * 2 ^ bits_in_window.val * 256 ^ byte_pos.val
          = (elem.val % 2 ^ n) * 2 ^ (n * iter.i) := by
        rw [mul_assoc, h256, ← pow_add, show bits_in_window.val + 8 * byte_pos.val = n * iter.i from by omega]
      rw [hcombine, hwin1v, packedVal_succ, add_mul, hprod, ← hval, ← helemv]; ring
    -- recursion
    have hbits' : 8 * bp1.val + b2.val = n * iter1.i := by
      rw [hpp', hpb, hi1, hbiw1v, Nat.mul_succ]; omega
    apply WP.spec_mono (serialize_loop0_spec iter1 o1 bits_per_elem bitmask w2 b2 bp1 n orig
      (by rw [hslice1, hslice]) horiglen hn hn_rng hmask
      (by simp only [Slice.length] at hplen; omega)
      (by rw [hpb]; omega) hw2_lt hbits' (by rw [hi1]; exact hval') (by rw [hi1]; omega))
    rintro r hr; exact hr
  · -- NONE: iter exhausted at 256; window/bits flushed to zero
    have hge : iter.i ≥ iter.slice.len := by simp only [not_lt] at hlt; exact hlt
    have hi_eq : iter.i = 256 := by
      have : iter.slice.len.val ≤ iter.i := hge; omega
    let* ⟨ o, iter1, ho, hnone ⟩ ← sliceIter_next_none'
    rw [ho]; simp only []
    -- from the invariant: byte_pos = 32n, bits = 0, window = 0
    have hb0 : bits_in_window.val = 0 := by
      have h1 : 8 * byte_pos.val + bits_in_window.val = n * 256 := by rw [← hi_eq]; exact hbits
      have h2 : n * 256 = 8 * (32 * n) := by ring
      omega
    have hw0 : window.val = 0 := by
      have : window.val < 2 ^ 0 := by rw [← hb0]; exact hwin
      simpa using this
    have hbp : byte_pos.val = 32 * n := by
      have h1 : 8 * byte_pos.val + bits_in_window.val = n * 256 := by rw [← hi_eq]; exact hbits
      have h2 : n * 256 = 8 * (32 * n) := by ring
      omega
    refine ⟨hbuflen, hb0, ?_⟩
    rw [← hbp, ← hi_eq, ← hval, hw0]; ring

/-- **`ser.serialize` correctness (byte-value form).**  The output's little-endian
value is the packed bit-stream of `data`. -/
theorem ser_serialize_spec (data : Slice U16) (out_buf : Slice U8) (bits_per_elem : Usize) (n : ℕ)
    (hn : bits_per_elem.val = n) (hn_rng : 1 ≤ n ∧ n ≤ 13)
    (hdata : data.val.length = 256) (hbuflen : out_buf.val.length = 32 * n) :
    ser.serialize data out_buf bits_per_elem
      ⦃ (r : Slice U8) => r.val.length = 32 * n ∧ byteVal r (32 * n) = packedVal data n 256 ⦄ := by
  unfold ser.serialize
  have hdlen : (Slice.len data).val = 256 := by simp [Slice.len, hdata]
  have holen : (Slice.len out_buf).val = 32 * n := by simp [Slice.len, hbuflen]
  let* ⟨ i1, hi1 ⟩ ← Std.Usize.mul_spec (show bits_per_elem.val * (Slice.len data).val ≤ Usize.max by
    rw [hn, hdlen]; have : (n * 256 : ℕ) ≤ 3328 := by omega
    have : (3328 : ℕ) ≤ Usize.max := by scalar_tac
    omega)
  have hi1v : i1.val = n * 256 := by rw [hi1, hn, hdlen]
  let* ⟨ right_val, hrv ⟩ ← Std.Usize.div_spec
  have hrvv : right_val.val = 32 * n := by rw [hrv, hi1v]; omega
  rw [show massert (Slice.len out_buf = right_val) = ok () from by
    have : Slice.len out_buf = right_val := by scalar_tac
    simp only [massert, if_pos this], bind_tc_ok]
  let* ⟨ i2, hi2, hi2bv ⟩ ← Std.U32.ShiftLeft_spec 1#u32 bits_per_elem (by omega)
  have hi2v : i2.val = 2 ^ n := by
    rw [hi2, hn, Nat.shiftLeft_eq, one_mul, Nat.mod_eq_of_lt]
    calc 2 ^ n ≤ 2 ^ 13 := Nat.pow_le_pow_right (by norm_num) (by omega)
      _ < U32.size := by simp [Std.U32.size, Std.U32.numBits]
  let* ⟨ bitmask, hbm ⟩ ← Std.U32.sub_spec (x := i2) (y := 1#u32) (by
    rw [hi2v]; have : 1 ≤ 2 ^ n := Nat.one_le_two_pow; simp)
  have hbmv : bitmask.val = 2 ^ n - 1 := by rw [hbm, hi2v]
  let* ⟨ iter, hit_slice, hit_i ⟩ ← sliceIter_spec'
  let* ⟨ out_buf1, biw, hlen, hzero, hbv ⟩ ← serialize_loop0_spec iter out_buf bits_per_elem bitmask
    0#u32 0#usize 0#usize n data (by rw [hit_slice]) hdata hn hn_rng hbmv hbuflen (by simp)
    (by simp) (by rw [hit_i]; simp) (by rw [hit_i]; simp [byteVal, packedVal]) (by rw [hit_i]; omega)
  rw [show massert (biw = 0#usize) = ok () from by
    have : biw = 0#usize := by scalar_tac
    simp only [massert, if_pos this], bind_tc_ok]
  exact ⟨hlen, hbv⟩

end Kopis.Properties
