/-
  # Kopis/Properties/DeserializeMsg.lean — `deserialize_generic` at bit-width 1.

  In PKE encryption the 32-byte message is decoded into a bit-per-coefficient ring
  element via the *generic* sliding-window bit-unpacker `ser::deserialize_generic`
  with `bits_per_elem = 1`.  We prove this path computes the audited
  `Spec.Kopis.deserialize 1`.

  The three layers mirror the 13-bit proofs in `Serialize.lean`
  (`deserialize_refill_spec` / `deserialize_outer_spec`), with `13` replaced by `1`.
  The one structural difference: with `bits_per_elem = 1` the window drains a single
  bit per element, so after a refill-from-empty (which loads a whole byte) it holds
  up to 8 bits.  Hence the outer-loop invariant is `bits_in_window < 8` (not `< 1`),
  and the refill loop only ever loads one byte, keeping `1 ≤ bits_in_window ≤ 8`.
-/
import Kopis.Properties.SerializeTop

open Aeneas Aeneas.Std Result
open kopis_kem
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

/-! ## Layer 1 — refill loop (`bits_per_elem = 1`) -/

/-- **Refill-loop spec at width 1.**  `deserialize_generic_loop0_loop0 … 1#usize` loads
whole bytes into `window` until it holds ≥ 1 bit.  With one bit per element the window
enters with `< 8` bits, so at most one byte is loaded, leaving `1 ≤ bits_in_window ≤ 8`.
Invariant: the window's value is exactly the stream bits `[lo, lo + bits_in_window)`, and
`8·byte_pos = lo + bits_in_window`. -/
theorem deserialize_refill_spec_1 (bytes : Slice U8) (window : U32) (biw bp : Usize) (lo : ℕ)
    (hbiw8 : biw.val ≤ 8)
    (hlo : 8 * bp.val = lo + biw.val)
    (hwin : window.val = streamNat bytes lo biw.val)
    (hbytes : lo + 1 ≤ 8 * bytes.length) :
    ser.deserialize_generic_loop0_loop0 bytes 1#usize window biw bp
      ⦃ (r : U32 × Usize × Usize) =>
          1 ≤ r.2.1.val ∧ r.2.1.val ≤ 8 ∧ 8 * r.2.2.val = lo + r.2.1.val ∧
          r.1.val = streamNat bytes lo r.2.1.val ⦄ := by
  unfold ser.deserialize_generic_loop0_loop0
  by_cases hlt : biw < 1#usize
  · rw [if_pos hlt]
    have hlt' : biw.val < 1 := by scalar_tac
    have hbp : bp.val < bytes.length := by scalar_tac
    have hwlt : window.val < 2 ^ biw.val := hwin ▸ streamNat_lt bytes lo biw.val
    let* ⟨ i, hi ⟩ ← Slice.index_usize_spec
    have hi_lt : i.val < 256 := by rw [hi]; scalar_tac
    let* ⟨ i1, hi1 ⟩ ← UScalar.cast_inBounds_spec
    let* ⟨ i2, hi2, hi2bv ⟩ ← Std.U32.ShiftLeft_spec
    have hi1_lt : i1.val < 256 := by rw [hi1]; exact hi_lt
    have hbound : i1.val * 2 ^ biw.val < 2 ^ 32 := by
      calc i1.val * 2 ^ biw.val ≤ 255 * 2 ^ 0 :=
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
    exact deserialize_refill_spec_1 bytes (window ||| i2) biw1 bp1 lo (by omega) hlo' hwin' hbytes
  · rw [if_neg hlt]
    simp only [WP.spec_ok]
    exact ⟨by scalar_tac, hbiw8, hlo, hwin⟩
termination_by 1 - biw.val
decreasing_by scalar_tac

/-! ## Layer 2 — outer 256-element loop (`bits_per_elem = 1`) -/

/-- **Outer-loop spec at width 1.**  Processing indices `[iter.start, 256)` writes
coefficient `j = streamNat (1·j) 1` (the single stream bit `j`) into each output slot;
the window enters slot `k` holding the stream bits `[k, k + bits_in_window)` with
`bits_in_window < 8`. -/
theorem deserialize_outer_spec_1 {N : Usize} (hN : N.val = 256)
    (iter : core.ops.range.Range Usize) (bytes : Slice U8) (out : Array U16 N)
    (bitmask window : U32) (biw bp : Usize)
    (hmask : bitmask.val = 2 ^ 1 - 1)
    (hstart : iter.start.val ≤ 256) (hend : iter.«end».val = 256)
    (hbiwlt : biw.val < 8)
    (hlo : 8 * bp.val = 1 * iter.start.val + biw.val)
    (hwin : window.val = streamNat bytes (1 * iter.start.val) biw.val)
    (hbytes : 1 * 256 ≤ 8 * bytes.length) :
    ser.deserialize_generic_loop0 iter bytes 1#usize out bitmask window biw bp
      ⦃ (r : Array U16 N) =>
          ∀ j (hj : j < 256),
            (r.val[j]'(by have := r.property; grind)).val
              = if j < iter.start.val then (out.val[j]'(by have := out.property; grind)).val
                else streamNat bytes (1 * j) 1 ⦄ := by
  unfold ser.deserialize_generic_loop0
  by_cases hlt : iter.start.val < iter.«end».val
  · let* ⟨ o, iter1, ho, hstart', hend' ⟩ ← core.iter.range.IteratorRange.next_Usize_some_spec
    rw [ho]; simp only
    have hk_lt : iter.start.val < 256 := by scalar_tac
    -- refill
    let* ⟨ window1, biw1, bp1, hbiw1, hbiw1ub, hlo1, hwin1 ⟩ ←
      deserialize_refill_spec_1 bytes window biw bp (1 * iter.start.val) (by omega) hlo hwin (by omega)
    -- extract element = low 1 bit
    have hsplit : streamNat bytes (1 * iter.start.val) biw1.val
        = streamNat bytes (1 * iter.start.val) 1
          + 2 ^ 1 * streamNat bytes (1 * iter.start.val + 1) (biw1.val - 1) := by
      conv_lhs => rw [show biw1.val = 1 + (biw1.val - 1) from by omega]
      rw [streamNat_split]
    have helem_lt : streamNat bytes (1 * iter.start.val) 1 < 2 ^ 1 := streamNat_lt _ _ _
    rw [show (lift (window1 &&& bitmask) : Result U32) = ok (window1 &&& bitmask) from rfl, bind_tc_ok]
    have hi_val : (window1 &&& bitmask).val = streamNat bytes (1 * iter.start.val) 1 := by
      rw [UScalar.val_and, hmask, Nat.and_two_pow_sub_one_eq_mod, hwin1, hsplit,
        Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt helem_lt]
    have hi1bound : (window1 &&& bitmask).val ≤ UScalar.max .U16 := by
      have h1 : (2:ℕ) ^ 1 = 2 := by norm_num
      rw [hi_val]; simp only [UScalar.max_UScalarTy_U16_eq, U16.max_eq]
      have := helem_lt; omega
    let* ⟨ i1, hi1 ⟩ ← UScalar.cast_inBounds_spec .U16 (window1 &&& bitmask) hi1bound
    have hi1_val : i1.val = streamNat bytes (1 * iter.start.val) 1 := by rw [hi1, hi_val]
    let* ⟨ a, ha ⟩ ← Array.update_spec
    let* ⟨ window2, hw2, hw2bv ⟩ ← Std.U32.ShiftRight_spec
    let* ⟨ biw2, hbiw2 ⟩ ← Std.Usize.sub_spec
    have hbiw2' : biw2.val = biw1.val - 1 := by scalar_tac
    have hw2' : window2.val = streamNat bytes (1 * iter1.start.val) biw2.val := by
      rw [hstart', show 1 * (iter.start.val + 1) = 1 * iter.start.val + 1 from by ring,
        hw2, hwin1, hsplit, hbiw2', Nat.shiftRight_eq_div_pow,
        Nat.add_mul_div_left _ _ (by positivity : 0 < 2 ^ 1), Nat.div_eq_of_lt helem_lt,
        Nat.zero_add]
    have hlo' : 8 * bp1.val = 1 * iter1.start.val + biw2.val := by
      rw [hstart', hbiw2']; omega
    have hbiw2lt : biw2.val < 8 := by omega
    -- recurse
    apply WP.spec_mono
      (deserialize_outer_spec_1 hN iter1 bytes a bitmask window2 biw2 bp1 hmask
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

/-! ## Layer 3 — top-level correspondence -/

/-- **Correctness of the generic decoder at 1 bit.**  Decoding a 32-byte buffer with
`bits_per_elem = 1` yields the spec ring element `deserialize 1` (the PKE message,
one bit per coefficient). -/
theorem deserialize_msg_spec (bytes : Slice U8) (hlen : bytes.length = 32) :
    ser.deserialize_generic 256#usize bytes 1#usize
      ⦃ (r : Array U16 256#usize) =>
          toPolyN 1 r = Spec.Kopis.deserialize 1 (sliceToBytes bytes (32 * 1) hlen) ⦄ := by
  unfold ser.deserialize_generic
  -- i = 1 * 256 = 256
  let* ⟨ i, hi ⟩ ← Std.Usize.mul_spec
  have hiv : i.val = 256 := by rw [hi]
  -- left_val = i % 8 = 0, discharge first massert
  let* ⟨ lv, hlv ⟩ ← Std.Usize.rem_spec
  have hlvv : lv.val = 0 := by rw [hlv, hiv]
  rw [show massert (lv = 0#usize) = ok () from by
    have : lv = 0#usize := UScalar.eq_of_val_eq (by rw [hlvv]; rfl)
    simp only [massert, if_pos this], bind_tc_ok]
  -- right_val = i / 8 = 32, discharge second massert
  let* ⟨ rv, hrv ⟩ ← Std.Usize.div_spec
  have hrvv : rv.val = 32 := by rw [hrv, hiv]
  have hmeq : Slice.len bytes = rv := UScalar.eq_of_val_eq (by rw [Slice.len_val, hrvv]; exact hlen)
  rw [show massert (Slice.len bytes = rv) = ok () from by
    simp only [massert, if_pos hmeq], bind_tc_ok]
  -- bitmask = (1 <<< 1) - 1 = 1 = 2^1 - 1
  let* ⟨ i1, hi1, hi1bv ⟩ ← Std.U32.ShiftLeft_spec
  have hi1v : i1.val = 2 := by rw [hi1]; simp [Std.U32.size, Std.U32.numBits]
  let* ⟨ bitmask, hbm ⟩ ← Std.U32.sub_spec
  have hbmv : bitmask.val = 2 ^ 1 - 1 := by rw [hbm, hi1v]; norm_num
  -- run the outer loop from index 0 with an empty window
  apply WP.spec_mono
    (deserialize_outer_spec_1 (N := 256#usize) (by simp) { start := 0#usize, «end» := 256#usize }
      bytes (Array.repeat 256#usize 0#u16) bitmask 0#u32 0#usize 0#usize
      hbmv (by simp) rfl (by scalar_tac) (by simp) (by simp) (by omega))
  intro r hr
  apply Vector.ext
  intro jj hjj
  simp only [toPolyN, Vector.getElem_ofFn]
  rw [deserialize_get 1 (sliceToBytes bytes (32 * 1) hlen) jj hjj]
  have hval := hr jj hjj
  rw [if_neg (by simp)] at hval
  rw [hval, streamNat_eq_sum' bytes 1 jj hlen hjj]

end Kopis.Properties
