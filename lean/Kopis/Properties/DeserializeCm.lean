/-
  # Kopis/Properties/DeserializeCm.lean — `deserialize_generic` at a general bit-width `n`.

  In PKE decryption the ciphertext `cm` element is decoded with a compression width
  `t ∈ {3, 4, 6}` bits per coefficient.  This routes through the *generic* sliding-window
  bit-unpacker `ser::deserialize_generic` (the `bits_per_elem ∉ {13, 10}` else-branch of
  `RingElem::deserialize`).  We prove that path computes the audited `Spec.Kopis.deserialize n`
  for any `1 ≤ n ≤ 12`, so it instantiates at `n = 3, 4, 6`.

  The three layers mirror the width-1 proofs in `DeserializeMsg.lean`
  (`deserialize_refill_spec_1` / `deserialize_outer_spec_1` / `deserialize_msg_spec`),
  with the concrete width replaced by a symbolic `n` carrying the bound `1 ≤ n ≤ 12`.

  Structural facts, derived from the loop body (not guessed):
    * Refill invariant: with byte loads of 8 bits and target width `n`, the window enters
      `< n` bits and exits `[n, n+7]`, i.e. `n ≤ bits_in_window ≤ n + 7`.
    * Outer invariant: after extracting `n` bits from a window that held `[n, n+7]` bits,
      the drained window holds `[0, 7]` bits, so between slots `bits_in_window < 8`.
-/
import Kopis.Properties.SerializeTop

open Aeneas Aeneas.Std Result
open RustKopis
open Spec (𝔹 bytesToBits)
open scoped BigOperators

namespace Kopis.Properties

set_option maxHeartbeats 1000000
set_option maxRecDepth 4000

/-! ## Spec-bridge helpers (local copies of the `private` versions in `Serialize.lean`) -/

private theorem deser_idx_lt' {n i j : ℕ} (hi : i < 256) (hj : j < n) :
    n * i + j < 8 * (32 * n) := by
  calc n * i + j < n * i + n := by omega
    _ = n * (i + 1) := by ring
    _ ≤ n * 256 := Nat.mul_le_mul_left n (by omega)
    _ = 8 * (32 * n) := by ring

private theorem streamNat_eq_sum' (bytes : Slice U8) (n j : ℕ) (h : bytes.length = 32 * n)
    (hj : j < 256) :
    streamNat bytes (n * j) n
      = ∑ k : Fin n, ((bytesToBits (sliceToBytes bytes (32 * n) h))[n * j + k.val]'(deser_idx_lt' hj k.isLt)).toNat
          * 2 ^ k.val := by
  unfold streamNat
  rw [← Fin.sum_univ_eq_sum_range (fun b => streamBit bytes (n * j + b) * 2 ^ b) n]
  apply Finset.sum_congr rfl
  intro k _
  congr 1
  exact (streamBit_eq_bit bytes n (n * j + k.val) h (deser_idx_lt' hj k.isLt)).symm

/-! ## Layer 1 — refill loop (general width `n`) -/

/-- **Refill-loop spec at width `n`.**  `deserialize_generic_loop0_loop0 … n#usize` loads
whole bytes into `window` until it holds ≥ `n` bits.  Entering with `< n` bits (in fact
`≤ n + 7`), it loads bytes of 8 bits each until the window holds `[n, n+7]` bits.
Invariant: the window's value is exactly the stream bits `[lo, lo + bits_in_window)`, and
`8·byte_pos = lo + bits_in_window`. -/
theorem deserialize_refill_spec_gen (n : ℕ) (hn : 1 ≤ n ∧ n ≤ 12)
    (bytes : Slice U8) (window : U32) (biw bp : Usize) (lo : ℕ)
    (hbiwub : biw.val ≤ n + 7)
    (hlo : 8 * bp.val = lo + biw.val)
    (hwin : window.val = streamNat bytes lo biw.val)
    (hbytes : lo + n ≤ 8 * bytes.length) :
    ser.deserialize_generic_loop0_loop0 bytes n#usize window biw bp
      ⦃ (r : U32 × Usize × Usize) =>
          n ≤ r.2.1.val ∧ r.2.1.val ≤ n + 7 ∧ 8 * r.2.2.val = lo + r.2.1.val ∧
          r.1.val = streamNat bytes lo r.2.1.val ⦄ := by
  obtain ⟨hn1, hn2⟩ := hn
  unfold ser.deserialize_generic_loop0_loop0
  by_cases hlt : biw < n#usize
  · rw [if_pos hlt]
    have hlt' : biw.val < n := by scalar_tac
    have hbp : bp.val < bytes.length := by omega
    have hwlt : window.val < 2 ^ biw.val := hwin ▸ streamNat_lt bytes lo biw.val
    let* ⟨ i, hi ⟩ ← Slice.index_usize_spec
    have hi_lt : i.val < 256 := by rw [hi]; scalar_tac
    let* ⟨ i1, hi1 ⟩ ← UScalar.cast_inBounds_spec
    let* ⟨ i2, hi2, hi2bv ⟩ ← Std.U32.ShiftLeft_spec
    have hi1_lt : i1.val < 256 := by rw [hi1]; exact hi_lt
    have hbound : i1.val * 2 ^ biw.val < 2 ^ 32 := by
      calc i1.val * 2 ^ biw.val ≤ 255 * 2 ^ 11 :=
            Nat.mul_le_mul (by omega) (Nat.pow_le_pow_right (by norm_num) (by omega))
        _ < 2 ^ 32 := by norm_num
    have hsz : Std.U32.size = 2 ^ 32 := by simp [Std.U32.size, Std.U32.numBits]
    have hi2' : i2.val = i1.val * 2 ^ biw.val := by
      rw [hi2, Nat.shiftLeft_eq]
      apply Nat.mod_eq_of_lt
      rw [hsz]; exact hbound
    have hbyte : (bytes.val[bp.val]!).val = i1.val := by
      rw [getElem!_pos bytes.val bp.val hbp, hi1, hi]
    simp only [lift, bind_tc_ok]
    let* ⟨ bp1, hbp1 ⟩ ← Std.Usize.add_spec
    let* ⟨ biw1, hbiw1 ⟩ ← Std.Usize.add_spec
    have hbiw1' : biw1.val = biw.val + 8 := by scalar_tac
    have hlo' : 8 * bp1.val = lo + biw1.val := by scalar_tac
    have hwin' : (window ||| i2).val = streamNat bytes lo biw1.val := by
      rw [hbiw1', UScalar.val_or, hi2',
        show i1.val * 2 ^ biw.val = i1.val <<< biw.val from by rw [Nat.shiftLeft_eq],
        lor_add_of_lt hwlt, Nat.shiftLeft_eq, hwin, streamNat_split]
      congr 1
      rw [show lo + biw.val = 8 * bp.val from hlo.symm, streamNat_byte, hbyte]
      ring
    exact deserialize_refill_spec_gen n ⟨hn1, hn2⟩ bytes (window ||| i2) biw1 bp1 lo (by omega) hlo' hwin' hbytes
  · rw [if_neg hlt]
    simp only [WP.spec_ok]
    exact ⟨by scalar_tac, hbiwub, hlo, hwin⟩
termination_by n - biw.val
decreasing_by scalar_tac

/-! ## Layer 2 — outer 256-element loop (general width `n`) -/

/-- **Outer-loop spec at width `n`.**  Processing indices `[iter.start, 256)` writes
coefficient `j = streamNat (n·j) n` (the `n`-bit stream window at `j`) into each output
slot; the window enters slot `k` holding the stream bits `[n·k, n·k + bits_in_window)`
with `bits_in_window < 8`. -/
theorem deserialize_outer_spec_gen (n : ℕ) (hn : 1 ≤ n ∧ n ≤ 12) {N : Usize} (hN : N.val = 256)
    (iter : core.ops.range.Range Usize) (bytes : Slice U8) (out : Array U16 N)
    (bitmask window : U32) (biw bp : Usize)
    (hmask : bitmask.val = 2 ^ n - 1)
    (hstart : iter.start.val ≤ 256) (hend : iter.«end».val = 256)
    (hbiwlt : biw.val < 8)
    (hlo : 8 * bp.val = n * iter.start.val + biw.val)
    (hwin : window.val = streamNat bytes (n * iter.start.val) biw.val)
    (hbytes : n * 256 ≤ 8 * bytes.length) :
    ser.deserialize_generic_loop0 iter bytes n#usize out bitmask window biw bp
      ⦃ (r : Array U16 N) =>
          ∀ j (hj : j < 256),
            (r.val[j]'(by have := r.property; grind)).val
              = if j < iter.start.val then (out.val[j]'(by have := out.property; grind)).val
                else streamNat bytes (n * j) n ⦄ := by
  obtain ⟨hn1, hn2⟩ := hn
  unfold ser.deserialize_generic_loop0
  by_cases hlt : iter.start.val < iter.«end».val
  · let* ⟨ o, iter1, ho, hstart', hend' ⟩ ← core.iter.range.IteratorRange.next_Usize_some_spec
    rw [ho]; simp only
    have hk_lt : iter.start.val < 256 := by scalar_tac
    have hbytes_step : n * iter.start.val + n ≤ 8 * bytes.length := by
      have h1 : n * iter.start.val + n = n * (iter.start.val + 1) := by ring
      rw [h1]
      calc n * (iter.start.val + 1) ≤ n * 256 := Nat.mul_le_mul_left n (by omega)
        _ ≤ 8 * bytes.length := hbytes
    -- refill
    let* ⟨ window1, biw1, bp1, hbiw1, hbiw1ub, hlo1, hwin1 ⟩ ←
      deserialize_refill_spec_gen n ⟨hn1, hn2⟩ bytes window biw bp (n * iter.start.val)
        (by omega) hlo hwin hbytes_step
    -- extract element = low `n` bits
    have hsplit : streamNat bytes (n * iter.start.val) biw1.val
        = streamNat bytes (n * iter.start.val) n
          + 2 ^ n * streamNat bytes (n * iter.start.val + n) (biw1.val - n) := by
      conv_lhs => rw [show biw1.val = n + (biw1.val - n) from by omega]
      rw [streamNat_split]
    have helem_lt : streamNat bytes (n * iter.start.val) n < 2 ^ n := streamNat_lt _ _ _
    rw [show (lift (window1 &&& bitmask) : Result U32) = ok (window1 &&& bitmask) from rfl, bind_tc_ok]
    have hi_val : (window1 &&& bitmask).val = streamNat bytes (n * iter.start.val) n := by
      rw [UScalar.val_and, hmask, Nat.and_two_pow_sub_one_eq_mod, hwin1, hsplit,
        Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt helem_lt]
    have hi1bound : (window1 &&& bitmask).val ≤ UScalar.max .U16 := by
      rw [hi_val]; simp only [UScalar.max_UScalarTy_U16_eq, U16.max_eq]
      have hle : (2:ℕ) ^ n ≤ 2 ^ 12 := Nat.pow_le_pow_right (by norm_num) (by omega)
      have h12 : (2:ℕ) ^ 12 = 4096 := by norm_num
      have := helem_lt; omega
    let* ⟨ i1, hi1 ⟩ ← UScalar.cast_inBounds_spec .U16 (window1 &&& bitmask) hi1bound
    have hi1_val : i1.val = streamNat bytes (n * iter.start.val) n := by rw [hi1, hi_val]
    let* ⟨ a, ha ⟩ ← Array.update_spec
    let* ⟨ window2, hw2, hw2bv ⟩ ← Std.U32.ShiftRight_spec
    let* ⟨ biw2, hbiw2 ⟩ ← Std.Usize.sub_spec
    have hbiw2' : biw2.val = biw1.val - n := by scalar_tac
    have hw2' : window2.val = streamNat bytes (n * iter1.start.val) biw2.val := by
      rw [hstart', show n * (iter.start.val + 1) = n * iter.start.val + n from by ring,
        hw2, hwin1, hsplit, hbiw2', Nat.shiftRight_eq_div_pow,
        Nat.add_mul_div_left _ _ (by positivity : 0 < 2 ^ n), Nat.div_eq_of_lt helem_lt,
        Nat.zero_add]
    have hlo' : 8 * bp1.val = n * iter1.start.val + biw2.val := by
      rw [hstart', show n * (iter.start.val + 1) = n * iter.start.val + n from by ring, hbiw2']
      omega
    have hbiw2lt : biw2.val < 8 := by omega
    -- recurse
    apply WP.spec_mono
      (deserialize_outer_spec_gen n ⟨hn1, hn2⟩ hN iter1 bytes a bitmask window2 biw2 bp1 hmask
        (by rw [hstart']; scalar_tac) (by rw [hend']; exact hend) hbiw2lt hlo' hw2' hbytes)
    intro r hr j hj
    have ihj := hr j hj
    rw [hstart'] at ihj
    by_cases hjk : j < iter.start.val
    · rw [if_pos hjk, ihj, if_pos (by omega)]
      rw [ha]; simp only [Array.set_val_eq]
      rw [List.getElem_set_ne (by omega)]
    · rw [if_neg hjk]
      by_cases hjeq : j = iter.start.val
      · subst hjeq
        rw [ihj, if_pos (by omega), ha]
        simp only [Array.set_val_eq, List.getElem_set_self, hi1_val]
      · rw [ihj, if_neg (by omega)]
  · let* ⟨ o, iter1, hnone, _ ⟩ ← core.iter.range.IteratorRange.next_Usize_none_spec
    rw [hnone]; simp only [WP.spec_ok]
    intro j hj
    rw [if_pos (by scalar_tac)]
termination_by iter.«end».val - iter.start.val
decreasing_by scalar_decr_tac

/-! ## Layer 3a — the generic decoder at width `n` -/

/-- **Correctness of the generic decoder at width `n`.**  Decoding a `32·n`-byte buffer with
`bits_per_elem = n` yields the spec ring element `deserialize n`. -/
theorem deserialize_generic_gen_spec (bytes : Slice U8) (n : ℕ) (hn : 1 ≤ n ∧ n ≤ 12)
    (hlen : bytes.length = 32 * n) :
    ser.deserialize_generic 256#usize bytes n#usize
      ⦃ (r : Array U16 256#usize) =>
          toPolyN n r = Spec.Kopis.deserialize n (sliceToBytes bytes (32 * n) hlen) ⦄ := by
  obtain ⟨hn1, hn2⟩ := hn
  have hnv : (n#usize).val = n := by simp
  unfold ser.deserialize_generic
  -- i = n * 256
  let* ⟨ i, hi ⟩ ← Std.Usize.mul_spec
  have hiv : i.val = n * 256 := hi
  -- left_val = i % 8 = 0, discharge first massert
  let* ⟨ lv, hlv ⟩ ← Std.Usize.rem_spec
  have hlvv : lv.val = 0 := by rw [hlv, hiv]; omega
  rw [show massert (lv = 0#usize) = ok () from by
    have : lv = 0#usize := UScalar.eq_of_val_eq (by rw [hlvv]; rfl)
    simp only [massert, if_pos this], bind_tc_ok]
  -- right_val = i / 8 = 32·n, discharge second massert
  let* ⟨ rv, hrv ⟩ ← Std.Usize.div_spec
  have hrvv : rv.val = 32 * n := by rw [hrv, hiv]; omega
  have hmeq : Slice.len bytes = rv := UScalar.eq_of_val_eq (by rw [Slice.len_val, hrvv]; exact hlen)
  rw [show massert (Slice.len bytes = rv) = ok () from by
    simp only [massert, if_pos hmeq], bind_tc_ok]
  -- bitmask = (1 <<< n) - 1 = 2ⁿ - 1
  have hszU : Std.U32.size = 2 ^ 32 := by simp [Std.U32.size, Std.U32.numBits]
  have h2n : (2:ℕ) ^ n < 2 ^ 32 := by
    calc (2:ℕ) ^ n ≤ 2 ^ 12 := Nat.pow_le_pow_right (by norm_num) (by omega)
      _ < 2 ^ 32 := by norm_num
  let* ⟨ i1, hi1, hi1bv ⟩ ← Std.U32.ShiftLeft_spec
  have hi1v : i1.val = 2 ^ n := by
    rw [hi1, hszU, Nat.shiftLeft_eq, one_mul, Nat.mod_eq_of_lt h2n]
  let* ⟨ bitmask, hbm ⟩ ← Std.U32.sub_spec (show (1#u32).val ≤ i1.val by
    rw [hi1v]; exact Nat.one_le_two_pow)
  have hbmv : bitmask.val = 2 ^ n - 1 := by rw [hbm, hi1v]
  -- run the outer loop from index 0 with an empty window
  apply WP.spec_mono
    (deserialize_outer_spec_gen n ⟨hn1, hn2⟩ (N := 256#usize) (by simp)
      { start := 0#usize, «end» := 256#usize }
      bytes (Array.repeat 256#usize 0#u16) bitmask 0#u32 0#usize 0#usize
      hbmv (by simp) rfl (by scalar_tac) (by simp) (by simp) (by rw [hlen]; omega))
  intro r hr
  apply Vector.ext
  intro jj hjj
  simp only [toPolyN, Vector.getElem_ofFn]
  rw [deserialize_get n (sliceToBytes bytes (32 * n) hlen) jj hjj]
  have hval := hr jj hjj
  rw [if_neg (by simp)] at hval
  rw [hval, streamNat_eq_sum' bytes n jj hlen hjj]

/-! ## Layer 3 — `RingElem.deserialize` correspondence at width `n` (else-branch) -/

/-- **`RingElem.deserialize` correctness at a general width `n ∉ {10, 13}`.**  For the `cm`
decode width `t ∈ {3, 4, 6}` (all `≤ 12` and `≠ 10, 13`), `RingElem::deserialize` takes the
generic else-branch and computes the audited `Spec.Kopis.deserialize n`. -/
theorem ringElem_deserialize_gen_spec (bytes : Slice U8) (n : ℕ) (hn : 1 ≤ n ∧ n ≤ 12)
    (hne13 : n ≠ 13) (hne10 : n ≠ 10) (hlen : bytes.length = 32 * n) :
    arithmetic.ring_arith.RingElem.deserialize bytes n#usize
      ⦃ (r : arithmetic.ring_arith.RingElem) =>
          toPolyN n r = Spec.Kopis.deserialize n (sliceToBytes bytes (32 * n) hlen) ⦄ := by
  obtain ⟨hn1, hn2⟩ := hn
  have hnv : (n#usize).val = n := by simp
  unfold arithmetic.ring_arith.RingElem.deserialize
  simp only [consts.RING_DEG]
  -- i = n * 256, right_val = 32·n, discharge the length massert
  let* ⟨ i, hi ⟩ ← Std.Usize.mul_spec
  have hiv : i.val = n * 256 := hi
  let* ⟨ rv, hrv ⟩ ← Std.Usize.div_spec
  have hrvv : rv.val = 32 * n := by rw [hrv, hiv]; omega
  have hmeq : Slice.len bytes = rv := UScalar.eq_of_val_eq (by rw [Slice.len_val, hrvv]; exact hlen)
  rw [show massert (Slice.len bytes = rv) = ok () from by
    simp only [massert, if_pos hmeq], bind_tc_ok]
  -- neither the 13-bit nor the 10-bit fast path: take the generic else-branch
  have hne13' : n#usize ≠ consts.MODULUS_Q_BITS := by
    simp only [consts.MODULUS_Q_BITS]
    intro h; exact hne13 (by have := congrArg UScalar.val h; simpa using this)
  have hne10' : n#usize ≠ consts.MODULUS_P_BITS := by
    simp only [consts.MODULUS_P_BITS]
    intro h; exact hne10 (by have := congrArg UScalar.val h; simpa using this)
  rw [if_neg hne13', if_neg hne10']
  -- delegate to the generic decoder and thread the postcondition through `ok a`
  let* ⟨ a, ha ⟩ ← deserialize_generic_gen_spec bytes n ⟨hn1, hn2⟩ hlen
  exact ha

/-- **`RingElem::deserialize` at a `Usize` width `bits` (generic branch).**  Usize-parameterised
wrapper around `ringElem_deserialize_gen_spec`, so callers with a runtime width `bits : Usize`
(e.g. `pke.decrypt`'s `t`) can apply it directly. -/
theorem ringElem_deserialize_gen_spec' (bytes : Slice U8) (bits : Usize) (n : ℕ)
    (hbn : bits.val = n) (hn : 1 ≤ n ∧ n ≤ 12) (hne13 : n ≠ 13) (hne10 : n ≠ 10)
    (hlen : bytes.length = 32 * n) :
    arithmetic.ring_arith.RingElem.deserialize bytes bits
      ⦃ (r : arithmetic.ring_arith.RingElem) =>
          toPolyN n r = Spec.Kopis.deserialize n (sliceToBytes bytes (32 * n) hlen) ⦄ := by
  have hbeq : bits = n#usize := UScalar.eq_of_val_eq (by rw [hbn]; simp)
  rw [hbeq]
  exact ringElem_deserialize_gen_spec bytes n hn hne13 hne10 hlen

end Kopis.Properties
