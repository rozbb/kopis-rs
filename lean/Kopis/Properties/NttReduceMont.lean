/-
  # Kopis/Properties/NttReduceMont.lean — the `mont_reduce` value spec.

  Signed Montgomery reduction (`src/arithmetic/ntt.rs`): for `|a| < 2³¹·p`,
  `mont_reduce a` returns `t ≡ a · 2⁻³² (mod p)` with `|t| < p`.  The four steps are

  1. `p · P_INV ≡ 1 (mod 2³²)` (checked in Rust by `literal_constants_are_correct`), so
     `t·p ≡ a (mod 2³²)` and hence `2³² ∣ a - t·p`;
  2. therefore the arithmetic shift by 32 is exact division: `result · 2³² = a - t·p`;
  3. `t·p ≡ 0 (mod p)`, so `result · 2³² ≡ a (mod p)` — the Montgomery property;
  4. `|a| < 2³¹·p` and `|t| ≤ 2³¹` give `|a - t·p| < 2³²·p`, hence `|result| < p`; this also
     keeps the `i64` operations in range and makes the final `i64 → i32` truncation exact.

  Step 1 is the fiddly one: it goes through the `u32`/`i32` casts, whose value semantics are
  `Int.bmod`/`Int.emod` rather than plain arithmetic.

  As in `NttReduceBarrett`, `clear_value` is applied as soon as the value equations are
  established: leaving the `set` abbreviations let-bound makes the kernel zeta-expand them and
  reduce `BitVec` operations on 64-bit literals inside every later side condition, which is what
  made this proof cost ~15 GB and many minutes before.
-/
import Kopis.Properties.Ntt

open Aeneas Aeneas.Std Result RustKopisSerial

namespace Kopis.Properties

/-- **`mont_reduce` value spec.**  Montgomery reduction: `result · 2³² ≡ a (mod p)`, and the
result is centered in `(-p, p)`.  Given `|a| < 2³¹·p`.  (The Montgomery factor `2³²` is
cancelled later by `INVNTT_SCALE` at the end of `invntt`.) -/
theorem mont_reduce_spec (a : I64)
    (hlo : -(2^31 * pNtt) ≤ (a.val:ℤ)) (hhi : (a.val:ℤ) < 2^31 * pNtt) :
    arithmetic.ntt.mont_reduce a
      ⦃ (t : I32) => ((t.val:ℤ) * 2^32) % pNtt = (a.val:ℤ) % pNtt
                     ∧ -pNtt < (t.val:ℤ) ∧ (t.val:ℤ) < pNtt ⦄ := by
  have hP : arithmetic.ntt.P.val = 50330113 := by simp only [arithmetic.ntt.P]; rfl
  have hPI : arithmetic.ntt.P_INV.val = 3575907841 := by simp only [arithmetic.ntt.P_INV]; rfl
  have halo : -108083094669492224 ≤ (a.val:ℤ) := by
    have h : (2:ℤ)^31 * pNtt = 108083094669492224 := by unfold pNtt; norm_num
    rw [h] at hlo; exact hlo
  have hahi : (a.val:ℤ) < 108083094669492224 := by
    have h : (2:ℤ)^31 * pNtt = 108083094669492224 := by unfold pNtt; norm_num
    rw [h] at hhi; exact hhi
  rw [show pNtt = 50330113 from rfl] at ⊢
  unfold arithmetic.ntt.mont_reduce
  simp only [lift, bind_tc_ok, WP.spec_ok]
  set i : U32 := IScalar.hcast .U32 a with hi_def
  set i1 : U32 := core.num.U32.wrapping_mul i arithmetic.ntt.P_INV with hi1_def
  set i2 : I32 := UScalar.hcast .I32 i1 with hi2_def
  set t : I64 := IScalar.cast .I64 i2 with ht_def
  set i3 : I64 := IScalar.cast .I64 arithmetic.ntt.P with hi3_def
  set i4 : I64 := core.num.I64.wrapping_mul t i3 with hi4_def
  set i5 : I64 := core.num.I64.wrapping_sub a i4 with hi5_def
  set i6 : I64 := core.num.I64.wrapping_shr i5 32#u32 with hi6_def
  -- ## Step 1: the multiplier `t` and its congruence mod 2³²
  have e_i : (i.val : ℤ) = (a.val) % 2^32 := by
    rw [hi_def, IScalar.hcast_val_eq]
    exact Int.toNat_of_nonneg (Int.emod_nonneg _ (by norm_num))
  have e_i1 : (i1.val : ℤ) = ((i.val : ℤ) * 3575907841) % 2^32 := by
    rw [hi1_def, core.num.U32.wrapping_mul, UScalar.wrapping_mul_val_eq]
    push_cast [hPI]
    rw [show UScalar.size UScalarTy.U32 = 2^32 from by simp only [UScalar.size]; rfl]; norm_num
  have e_i2 : (i2.val : ℤ) = Int.bmod (i1.val) (2^32) := by rw [hi2_def, UScalar.hcast_val_eq]; rfl
  have i2_lo : -2147483648 ≤ (i2.val:ℤ) := by scalar_tac
  have i2_hi : (i2.val:ℤ) < 2147483648 := by scalar_tac
  have e_t : (t.val : ℤ) = (i2.val:ℤ) := by
    rw [ht_def, IScalar.cast_val_eq,
      show Min.min IScalarTy.I64.numBits IScalarTy.I32.numBits = 32 from rfl]
    exact bmod_i32_exact i2_lo i2_hi
  have ht_lo : -2147483648 ≤ (t.val:ℤ) := by rw [e_t]; exact i2_lo
  have ht_hi : (t.val:ℤ) < 2147483648 := by rw [e_t]; exact i2_hi
  -- `2³² ∣ a - t·p`, via `p · P_INV ≡ 1 (mod 2³²)`
  have emq : ∀ (b n : ℤ), b % n ≡ b [ZMOD n] := fun b n => Int.emod_emod_of_dvd b (dvd_refl n)
  have bbridge : ∀ z : ℤ, Int.bmod z (2^32) ≡ z [ZMOD (2^32)] := by
    intro z; unfold Int.ModEq
    have h := @Int.bmod_emod z (2^32); norm_num at h ⊢; exact h
  have m_t : (t.val:ℤ) ≡ (a.val:ℤ) * 3575907841 [ZMOD (2^32)] := by
    rw [e_t, e_i2]
    refine (bbridge i1.val).trans ?_
    rw [e_i1]
    refine (emq _ _).trans ?_
    exact Int.ModEq.mul_right _ (by rw [e_i]; exact emq (a.val:ℤ) _)
  have m_final : (t.val:ℤ) * 50330113 ≡ (a.val:ℤ) [ZMOD (2^32)] := by
    refine (m_t.mul_right 50330113).trans ?_
    calc (a.val:ℤ) * 3575907841 * 50330113
        = (a.val:ℤ) * (3575907841 * 50330113) := by ring
      _ ≡ (a.val:ℤ) * 1 [ZMOD (2^32)] :=
          Int.ModEq.mul_left _ (by unfold Int.ModEq; norm_num)
      _ = (a.val:ℤ) := by ring
  have hdvd : ((a.val:ℤ) - (t.val:ℤ) * 50330113) % (2^32:ℤ) = 0 := by
    have hz : ((a.val:ℤ) - (t.val:ℤ) * 50330113) ≡ 0 [ZMOD (2^32)] := by
      have h := (Int.ModEq.refl (a.val:ℤ)).sub m_final; simpa using h
    have h0 : ((a.val:ℤ) - (t.val:ℤ) * 50330113) % (2^32:ℤ) = 0 % (2^32:ℤ) := hz
    simpa using h0
  -- ## Step 2: the exact arithmetic, and the exact shift
  have e_i3 : (i3.val:ℤ) = 50330113 := by
    rw [hi3_def, IScalar.cast_val_eq,
      show Min.min IScalarTy.I64.numBits IScalarTy.I32.numBits = 32 from rfl, hP]
    exact bmod_i32_exact (by norm_num) (by norm_num)
  have i4p_lo : (-2147483648:ℤ) * 50330113 ≤ (t.val:ℤ) * 50330113 :=
    mul_le_mul_of_nonneg_right ht_lo (by norm_num)
  have i4p_hi : (t.val:ℤ) * 50330113 ≤ (2147483647:ℤ) * 50330113 :=
    mul_le_mul_of_nonneg_right (by linarith) (by norm_num)
  have e_i4 : (i4.val:ℤ) = (t.val:ℤ) * 50330113 := by
    rw [hi4_def, I64_wrapping_mul_exact t i3 (by rw [e_i3]; linarith) (by rw [e_i3]; linarith),
      e_i3]
  have e_i5 : (i5.val:ℤ) = (a.val:ℤ) - (t.val:ℤ) * 50330113 := by
    rw [hi5_def, I64_wrapping_sub_exact a i4 (by rw [e_i4]; linarith) (by rw [e_i4]; linarith),
      e_i4]
  have e_i6 : (i6.val:ℤ) * 4294967296 = (i5.val:ℤ) := by
    have hsh : (i6.val:ℤ) = (i5.val:ℤ) >>> (32:ℕ) := by
      rw [hi6_def]
      simp only [core.num.I64.wrapping_shr, IScalar.wrapping_shr, IScalar.val]
      rw [show (32#u32).val % IScalarTy.I64.numBits = 32 from rfl, BitVec.toInt_sshiftRight]
    rw [hsh, Int.shiftRight_eq_div_pow]
    have hmod : ((i5.val:ℤ)) % 2^32 = 0 := by rw [e_i5]; exact hdvd
    have hdvd32 : (2^32:ℤ) ∣ (i5.val:ℤ) := by rw [Int.dvd_iff_emod_eq_zero]; simpa using hmod
    have hcan := Int.ediv_mul_cancel hdvd32
    push_cast
    push_cast at hcan
    linarith
  -- ## Step 3: forget the definitions — everything below is plain integer arithmetic
  clear_value i6 i5 i4 i3 t i2 i1 i
  clear hi6_def hi5_def hi4_def hi3_def ht_def hi2_def hi1_def hi_def
    e_i e_i1 e_i2 m_t bbridge emq
  have hi6_lo : -50330113 < (i6.val:ℤ) := by linarith
  have hi6_hi : (i6.val:ℤ) < 50330113 := by linarith
  have hr : (IScalar.cast .I32 i6).val = (i6.val:ℤ) := by
    simp only [IScalar.cast_val_eq,
      show Min.min IScalarTy.I32.numBits IScalarTy.I64.numBits = 32 from rfl]
    exact bmod_i32_exact (by linarith) (by linarith)
  rw [hr]
  refine ⟨?_, hi6_lo, hi6_hi⟩
  have h32 : (i6.val:ℤ) * 2^32 = (a.val:ℤ) - (t.val:ℤ) * 50330113 := by
    rw [show ((2:ℤ)^32) = 4294967296 from by norm_num, e_i6, e_i5]
  rw [h32]
  have hcong : (a.val:ℤ) - (t.val:ℤ) * 50330113 ≡ (a.val:ℤ) [ZMOD 50330113] := by
    have hmul : (t.val:ℤ) * 50330113 ≡ 0 [ZMOD 50330113] :=
      (Int.modEq_zero_iff_dvd).mpr ⟨(t.val:ℤ), by ring⟩
    have h := (Int.ModEq.refl (a.val:ℤ)).sub hmul; simpa using h
  exact hcong

end Kopis.Properties
