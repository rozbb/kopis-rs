import Kopis.Properties.Serialize
open Aeneas Aeneas.Std Result kopis
open scoped BigOperators
namespace Kopis.Properties

set_option maxHeartbeats 2000000
set_option maxRecDepth 4000

/-- **Inner flush loop.**  While `bits_in_window ≥ 8`, write the low byte of `window`
to `out_buf[byte_pos]`, shift the window down 8, advance.  Flushes `bits/8` whole bytes. -/
theorem serialize_loop0_loop0_spec (out_buf : Slice U8) (window : U32)
    (bits_in_window byte_pos : Usize)
    (hbnd : byte_pos.val + bits_in_window.val / 8 ≤ out_buf.length)
    (hbiw : bits_in_window.val ≤ 32) :
    ser.serialize_loop0_loop0 out_buf window bits_in_window byte_pos
      ⦃ (r : Slice U8 × U32 × Usize × Usize) =>
          r.2.2.1.val = bits_in_window.val % 8 ∧
          r.2.2.2.val = byte_pos.val + bits_in_window.val / 8 ∧
          r.2.1.val = window.val >>> (8 * (bits_in_window.val / 8)) ∧
          r.1.length = out_buf.length ∧
          (∀ t, t < bits_in_window.val / 8 →
             (r.1.val[byte_pos.val + t]!).val = (window.val >>> (8 * t)) % 256) ∧
          (∀ q, (q < byte_pos.val ∨ byte_pos.val + bits_in_window.val / 8 ≤ q) →
             r.1.val[q]! = out_buf.val[q]!) ⦄ := by
  unfold ser.serialize_loop0_loop0
  by_cases h8 : bits_in_window.val ≥ 8
  · rw [if_pos (by scalar_tac)]
    have hlen : out_buf.length = out_buf.val.length := by simp [Slice.length]
    have hf1 : 1 ≤ bits_in_window.val / 8 := by omega
    have hbp_lt : byte_pos.val < out_buf.length := by omega
    have hbp_lt' : byte_pos.val < out_buf.val.length := by rw [← hlen]; exact hbp_lt
    rw [show lift (UScalar.cast .U8 window) = ok (UScalar.cast .U8 window) from rfl, bind_tc_ok]
    let* ⟨ s, hs ⟩ ← Slice.update_spec out_buf byte_pos (UScalar.cast .U8 window) hbp_lt
    let* ⟨ window1, hw1, hw1bv ⟩ ← Std.U32.ShiftRight_IScalar_spec window 8#i32 (by decide) (by decide)
    let* ⟨ biw1, hbiw1, _ ⟩ ← Std.Usize.sub_spec (show (8#usize).val ≤ bits_in_window.val by scalar_tac)
    let* ⟨ bp1, hbp1 ⟩ ← Std.Usize.add_spec (show byte_pos.val + (1#usize).val ≤ Usize.max by scalar_tac)
    have hcastv : (UScalar.cast UScalarTy.U8 window).val = window.val % 256 := by
      rw [UScalar.cast_val_eq]; rfl
    have hw1v : window1.val = window.val >>> 8 := by rw [hw1]
    have hslen : s.length = out_buf.length := by rw [hs, Slice.set_length]
    have hbiw1v : biw1.val = bits_in_window.val - 8 := by rw [hbiw1]
    have hbp1v : bp1.val = byte_pos.val + 1 := by rw [hbp1]
    have hbnd' : bp1.val + biw1.val / 8 ≤ s.length := by rw [hslen, hbp1v, hbiw1v]; omega
    have hbiw' : biw1.val ≤ 32 := by omega
    -- `s.val[q]!` in terms of `out_buf`
    have hsget_self : s.val[byte_pos.val]!.val = window.val % 256 := by
      rw [hs, Slice.set_val_eq, getElem!_pos _ byte_pos.val (by rw [List.length_set]; exact hbp_lt'),
        List.getElem_set_self, hcastv]
    have hsget_ne : ∀ q, q ≠ byte_pos.val → s.val[q]! = out_buf.val[q]! := by
      intro q hq
      by_cases hqb : q < out_buf.val.length
      · rw [hs, Slice.set_val_eq, getElem!_pos _ q (by simpa using hqb), getElem!_pos _ q hqb,
          List.getElem_set_of_ne (Ne.symm hq)]
      · rw [hs, Slice.set_val_eq, getElem!_neg _ q (by simpa using hqb), getElem!_neg _ q hqb]
    apply WP.spec_mono (serialize_loop0_loop0_spec s window1 biw1 bp1 hbnd' hbiw')
    rintro ⟨s', w', b', p'⟩ ⟨hb', hp', hw', hslen', hbytes', hunch'⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hb', hbiw1v]; omega
    · rw [hp', hbp1v, hbiw1v]; omega
    · rw [hw', hw1v, hbiw1v, ← Nat.shiftRight_add]
      congr 1; omega
    · rw [hslen', hslen]
    · intro t ht
      by_cases ht0 : t = 0
      · subst ht0
        rw [Nat.add_zero, hunch' byte_pos.val (Or.inl (by omega)), hsget_self, Nat.mul_zero,
          Nat.shiftRight_zero]
      · have : byte_pos.val + t = bp1.val + (t - 1) := by rw [hbp1v]; omega
        rw [this, hbytes' (t - 1) (by rw [hbiw1v]; omega), hw1v, ← Nat.shiftRight_add]
        congr 2; omega
    · intro q hq
      have hqne : q ≠ byte_pos.val := by rcases hq with h | h <;> omega
      by_cases hqcase : q < bp1.val
      · rw [hunch' q (Or.inl hqcase), hsget_ne q hqne]
      · have hq' : bp1.val + biw1.val / 8 ≤ q := by rcases hq with h | h <;> omega
        rw [hunch' q (Or.inr hq'), hsget_ne q hqne]
  · rw [if_neg (by scalar_tac)]
    simp only [WP.spec_ok]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · omega
    · omega
    · rw [show bits_in_window.val / 8 = 0 from by omega]; simp
    · first | rfl | trivial
    · intro t ht; rw [show bits_in_window.val / 8 = 0 from by omega] at ht; omega
    · intro q _; trivial

end Kopis.Properties
