import Kopis.Properties.SerializeSpec2
import Kopis.Properties.Serialize
import Kopis.Properties.Serialize10
open Aeneas Aeneas.Std Result RustKopisSerial
open Spec (𝔹)
open scoped BigOperators
namespace Kopis.Properties

open arithmetic.plain_arith (RingElem)

set_option maxHeartbeats 2000000
set_option maxRecDepth 4000

/-- Interpret a Rust `RingElem` (`Array U16 256`) as a spec `n`-bit ring element:
each physical `u16` coefficient reduced mod `2ⁿ`. -/
def toPolyN (n : ℕ) (re : RingElem) : Spec.Kopis.Polynomial (2 ^ n) :=
  Vector.ofFn fun (i : Fin 256) => ((re.val[i.val]'(by have := re.property; grind)).val : ZMod (2 ^ n))

theorem toPolyN_val (n : ℕ) (re : RingElem) (i : ℕ) (hi : i < 256) :
    ((toPolyN n re)[i]!).val = (re.val[i]!).val % 2 ^ n := by
  haveI : NeZero (2 ^ n) := ⟨by positivity⟩
  rw [getElem!_pos (toPolyN n re) i hi]
  simp only [toPolyN, Vector.getElem_ofFn]
  rw [ZMod.val_natCast, getElem!_pos re.val i (by have := re.property; grind)]

/-- The packed value of the physical slice equals the packed value of the `n`-bit
canonical polynomial `toPolyN n re`. -/
theorem packedVal_toPolyN (n : ℕ) (re : RingElem) :
    packedVal (Array.to_slice re) n 256 = ∑ i ∈ Finset.range 256, ((toPolyN n re)[i]!).val * 2 ^ (n * i) := by
  unfold packedVal
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mem_range] at hi
  rw [toPolyN_val n re i hi, Array.val_to_slice]

/-- The shared tail of both serialization paths: from "the output bytes are the packed
coefficients" to "the output is the spec's `serialize`". -/
theorem serialize_conclusion (re : RingElem) (n : ℕ) (hrng : 1 ≤ n ∧ n ≤ 13) (r : Slice U8)
    (hrlen : r.val.length = 32 * n)
    (hbv : byteVal r (32 * n) = packedVal (Array.to_slice re) n 256) :
    ∃ h : r.length = 32 * n, sliceToBytes r (32 * n) h
      = Spec.Kopis.serialize n (toPolyN n re) := by
  have hrlen' : r.length = 32 * n := by rw [Slice.length]; exact hrlen
  refine ⟨hrlen', ?_⟩
  apply Vector.ext
  intro p hp
  simp only [sliceToBytes, Vector.getElem_ofFn]
  apply BitVec.eq_of_toNat_eq
  have hp' : p < 32 * n := by simpa using hp
  have hbyte_p : (r.val[p]'(by simp only [Slice.length] at hrlen'; omega)).bv.toNat
      = (r.val[p]!).val := by
    rw [getElem!_pos r.val p (by simp only [Slice.length] at hrlen'; omega)]; rfl
  rw [hbyte_p, ← byteVal_getByte r (32 * n) p hp', hbv, packedVal_toPolyN,
    ← serialize_byteVal n (toPolyN n re) p hp' (by omega)]

/-- **`RingElem.serialize` correctness.**  Serializing a `RingElem` with `n`-bit
coefficients produces the spec `serialize n (toPolyN n re)`. -/
theorem ring_serialize_spec (re : RingElem) (out : Slice U8) (bits : Usize) (n : ℕ)
    (hn : bits.val = n) (hrng : 1 ≤ n ∧ n ≤ 13) (hlen : out.val.length = 32 * n) :
    RingElem.serialize bits re out
      ⦃ (r : Slice U8) => ∃ h : r.length = 32 * n, sliceToBytes r (32 * n) h = Spec.Kopis.serialize n (toPolyN n re) ⦄ := by
  unfold RingElem.serialize
  simp only [consts.RING_DEG]
  -- the width guard `debug_assert!((1..=13).contains(&BITS_PER_ELEM))`, now a `massert`
  let* ⟨ ri, hri1, hri2, hri3 ⟩ ← core.ops.range.RangeInclusive.new_spec
  have hin : ri.start.val ≤ bits.val ∧ bits.val ≤ ri.«end».val := by
    rw [hri1, hri2]; constructor <;> scalar_tac
  rw [rangeInclusive_contains_usize_eq, bind_tc_ok]
  rw [show massert (decide (ri.start.val ≤ bits.val ∧ bits.val ≤ ri.«end».val) = true) = ok ()
        from by simp only [massert, decide_eq_true_eq, if_pos hin], bind_tc_ok]
  -- `BITS_PER_ELEM * RING_DEG` is an overflow check whose value the body discards; the product
  -- is then recomputed as a wrapping multiply, which `mul_spec` says does not wrap
  let* ⟨ chk, hchk ⟩ ← Std.Usize.mul_spec (show bits.val * (256#usize).val ≤ Usize.max by
    rw [hn, show (256#usize).val = 256 from rfl]
    have : n * 256 ≤ 13 * 256 := by omega
    have : (13 * 256 : ℕ) ≤ Usize.max := by scalar_tac
    omega)
  have h256 : (256#usize).val = 256 := by simp
  have hlt : bits.val * (256#usize).val < UScalar.size UScalarTy.Usize := by
    rw [h256, UScalar.size_def]
    have := UScalar.hBounds chk
    omega
  have hiv : (Std.Usize.wrapping_mul bits 256#usize).val = n * 256 := by
    rw [Std.Usize.wrapping_mul_val_eq, Nat.mod_eq_of_lt hlt, h256, hn]
  rw [show lift (Std.Usize.wrapping_mul bits 256#usize)
        = ok (Std.Usize.wrapping_mul bits 256#usize) from rfl, bind_tc_ok]
  let* ⟨ i1, hi1 ⟩ ← Std.Usize.div_spec
  have hi1v : i1.val = 32 * n := by rw [hi1, hiv]; omega
  rw [show massert (Slice.len out = i1) = ok () from by
    have : Slice.len out = i1 := by scalar_tac
    simp only [massert, if_pos this], bind_tc_ok]
  have hslen : (Array.to_slice re).val.length = 256 := by rw [Array.val_to_slice]; exact re.property
  split
  · -- the branchless 10-bit fast path
    rename_i hd
    have hn10 : n = 10 := by rw [← hn]; exact hd
    have houtlen : out.val.length = 320 := by rw [hlen, hn10]
    have hlenu : Slice.len out = 320#usize :=
      UScalar.eq_of_val_eq (by rw [Slice.len_val]; exact houtlen)
    simp only [core.array.TryFromMutArraySlice.try_from, dif_pos hlenu, bind_tc_ok,
      core.result.Result.unwrap.mut]
    let* ⟨ arr1, hbv ⟩ ← serialize_10_spec re ⟨out.val, by rw [houtlen]; scalar_tac⟩
    have harrlen : arr1.val.length = 320 := arr1.property
    rw [if_pos (show arr1.length = out.length from by
      show arr1.val.length = out.val.length
      rw [harrlen, houtlen])]
    refine serialize_conclusion re n hrng _ (by rw [hn10]; exact harrlen) ?_
    rw [hn10]
    refine Eq.trans ?_ hbv
    exact byteVal_congr _ _ _ (fun q _ => by simp [Array.val_to_slice])
  · -- the generic sliding-window path
    rename_i hd
    rw [show (lift (Array.to_slice re) : Result (Slice U16)) = ok (Array.to_slice re) from rfl,
      bind_tc_ok]
    apply WP.spec_mono (ser_serialize_spec (Array.to_slice re) out bits n hn hrng hslen hlen)
    intro r ⟨hrlen, hbv⟩
    exact serialize_conclusion re n hrng r hrlen hbv

end Kopis.Properties
