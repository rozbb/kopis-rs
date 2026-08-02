/-
  # Kopis/Properties/NttReduceWrap.lean — the `to_wrapping_u16` value spec.

  `to_wrapping_u16 x` canonicalises `x` into `[0, p)` and then conditionally subtracts `p` to
  land in the centered range `(-p/2, p/2]`, returning the result reduced mod `2¹⁶`.  The spec
  therefore exhibits the centered representative `x2` explicitly: it is congruent to `x` mod `p`,
  lies in `[-⌊p/2⌋, ⌊p/2⌋]`, and agrees with the returned `u16` mod `2¹⁶`.  That last clause is
  what lets the caller match it against `signedOfU16`.

  The conditional subtraction is branch-free — `x - (P & (P_HALF - x) >> 31)` — so the proof
  splits on the sign of `P_HALF - x` and evaluates the mask to `0` or `allOnes` in each branch.

  As in the sibling files, `clear_value` retires the `set` abbreviations as soon as their value
  equations are known, which keeps the kernel from zeta-expanding `BitVec` terms inside every
  later side condition.
-/
import Kopis.Properties.Ntt

open Aeneas Aeneas.Std Result RustKopisSerial

namespace Kopis.Properties

/-- **`to_wrapping_u16` value spec.**  The returned `u16` denotes the centered residue `x2` of
`x` in `[-P_HALF, P_HALF]` (which determines it uniquely since `2·P_HALF < p`), agreeing with it
mod `2¹⁶` — i.e. matching the `signedOfU16` reading. -/
theorem to_wrapping_u16_spec (x : I32) (hlo : -pNtt < (x.val:ℤ)) (hhi : (x.val:ℤ) < pNtt) :
    arithmetic.ntt.to_wrapping_u16 x
      ⦃ (r : U16) => ∃ x2 : ℤ, x2 ≡ (x.val:ℤ) [ZMOD pNtt]
                       ∧ -25165056 ≤ x2 ∧ x2 ≤ 25165056
                       ∧ (r.val : ℤ) % 65536 = x2 % 65536 ⦄ := by
  have hP : arithmetic.ntt.P.val = 50330113 := by simp only [arithmetic.ntt.P]; rfl
  have hPH : arithmetic.ntt.P_HALF.val = 25165056 := by simp only [arithmetic.ntt.P_HALF]; rfl
  unfold arithmetic.ntt.to_wrapping_u16
  apply WP.spec_bind (to_canonical_spec x hlo hhi)
  intro x1 hx1
  obtain ⟨hx1mod, hx1lo, hx1hi⟩ := hx1
  have hx1hi' : (x1.val:ℤ) < 50330113 := by unfold pNtt at hx1hi; exact hx1hi
  simp only [lift, bind_tc_ok, WP.spec_ok]
  -- the branch-free conditional subtraction: `msk` is all-zeros or all-ones
  set d : I32 := core.num.I32.wrapping_sub arithmetic.ntt.P_HALF x1 with hd_def
  set msk : I32 := core.num.I32.wrapping_shr d 31#u32 with hmsk_def
  have e_d : (d.val:ℤ) = 25165056 - (x1.val:ℤ) := by
    rw [hd_def, I32_wrapping_sub_exact _ _ (by rw [hPH]; linarith) (by rw [hPH]; linarith), hPH]
  have hshift31 : ∀ z : ℤ, z >>> (31 : ℕ) = z / 2147483648 := by
    intro z
    rw [Int.shiftRight_eq_div_pow]
    norm_num
  have e_msk : (msk.val:ℤ) = (25165056 - (x1.val:ℤ)) / 2147483648 := by
    have hstep : (msk.val:ℤ) = (d.val:ℤ) >>> (31 : ℕ) := by
      rw [hmsk_def]
      simp only [core.num.I32.wrapping_shr, IScalar.wrapping_shr, IScalar.val]
      rw [show (31#u32).val % IScalarTy.I32.numBits = 31 from rfl, BitVec.toInt_sshiftRight]
    rw [hstep, e_d, hshift31]
  clear_value msk d
  clear hmsk_def hd_def
  by_cases hc : (x1.val:ℤ) ≤ 25165056
  · -- mask = 0: the value is already centered, `x2 = x1`
    have hmv : (msk.val:ℤ) = 0 := by
      rw [e_msk]
      have h1 : (0:ℤ) ≤ 25165056 - (x1.val:ℤ) := by linarith
      have h2 : 25165056 - (x1.val:ℤ) < 2147483648 := by linarith
      omega
    have hand : (arithmetic.ntt.P &&& msk).val = 0 := by
      have hbv : msk.bv = 0#32 := by
        apply BitVec.eq_of_toInt_eq
        show _ = (0#32).toInt
        rw [show (0#32).toInt = (0:ℤ) from rfl]
        exact hmv
      show (arithmetic.ntt.P.bv &&& msk.bv).toInt = 0
      rw [hbv, BitVec.and_zero]
      rfl
    have e_x2 : (core.num.I32.wrapping_sub x1 (arithmetic.ntt.P &&& msk)).val = (x1.val:ℤ) := by
      rw [I32_wrapping_sub_exact _ _ (by rw [hand]; linarith) (by rw [hand]; linarith), hand]
      ring
    refine ⟨(x1.val:ℤ), hx1mod, by linarith, hc, ?_⟩
    rw [IScalar.hcast_val_eq, e_x2, show (2:ℤ)^UScalarTy.U16.numBits = 65536 from rfl,
      Int.toNat_of_nonneg (Int.emod_nonneg _ (by norm_num))]
    exact Int.emod_emod_of_dvd _ (dvd_refl _)
  · -- mask = all ones: subtract `p` to centre, `x2 = x1 - p`
    have hmv : (msk.val:ℤ) = -1 := by
      rw [e_msk]
      have h1 : (-2147483648 : ℤ) ≤ 25165056 - (x1.val:ℤ) := by linarith
      have h2 : 25165056 - (x1.val:ℤ) < 0 := by linarith
      omega
    have hand : (arithmetic.ntt.P &&& msk).val = 50330113 := by
      have hbv : msk.bv = BitVec.allOnes 32 := by
        apply BitVec.eq_of_toInt_eq
        show _ = (BitVec.allOnes 32).toInt
        rw [show (BitVec.allOnes 32).toInt = (-1:ℤ) from rfl]
        exact hmv
      show (arithmetic.ntt.P.bv &&& msk.bv).toInt = 50330113
      rw [hbv, BitVec.and_allOnes]
      exact hP
    have e_x2 : (core.num.I32.wrapping_sub x1 (arithmetic.ntt.P &&& msk)).val
        = (x1.val:ℤ) - 50330113 := by
      rw [I32_wrapping_sub_exact _ _ (by rw [hand]; linarith) (by rw [hand]; linarith), hand]
    refine ⟨(x1.val:ℤ) - 50330113, ?_, by linarith, by linarith, ?_⟩
    · have h1 : ((x1.val:ℤ) - 50330113) ≡ (x1.val:ℤ) [ZMOD pNtt] := by
        have h0 : ((x1.val:ℤ) - 50330113) ≡ (x1.val:ℤ) - 0 [ZMOD pNtt] :=
          (Int.ModEq.refl _).sub (Int.modEq_zero_iff_dvd.mpr (by unfold pNtt; norm_num))
        simpa using h0
      exact h1.trans hx1mod
    · rw [IScalar.hcast_val_eq, e_x2, show (2:ℤ)^UScalarTy.U16.numBits = 65536 from rfl,
        Int.toNat_of_nonneg (Int.emod_nonneg _ (by norm_num))]
      exact Int.emod_emod_of_dvd _ (dvd_refl _)

end Kopis.Properties
