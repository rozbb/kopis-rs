/-
  # Kopis/Properties/NttReduce.lean — the remaining NTT reduction-function value specs.

  ┌───────────────────────────────────────────────────────────────────────────────────────┐
  │  RESUME NOTE (paused 2026-07-24, waiting on more host RAM).                             │
  │                                                                                         │
  │  This file is NOT imported by `Kopis.lean`, so `make prove-kopis` does not build it and  │
  │  stays green.  It holds THREE fully-proven, `sorry`-free reduction value-specs           │
  │  (`mont_reduce_spec`, `to_wrapping_u16_spec`, `barrett_reduce_spec`) that could not be    │
  │  committed into the verified build on the 4 GB host: each proof's elaborated WP-monadic  │
  │  term is memory-heavy, and this host OOMs (exit 137) whenever TWO of them — or even one   │
  │  alongside `Ntt.lean`'s butterfly-loop proofs — co-elaborate.  Every proof reaches full   │
  │  elaboration with NO errors; `mont_reduce_spec` was confirmed to compile to `exit 0` as   │
  │  a standalone file.  The blocker is RAM, not mathematics.                                │
  │                                                                                         │
  │  TO BRING THESE INTO THE VERIFIED BUILD on a machine with more RAM (≥ ~16 GB):            │
  │    1. Add `import Kopis.Properties.NttReduce` to `Kopis.lean`.                            │
  │    2. `LEAN_NUM_THREADS=2 lake build Kopis TopLevelTheorems` (= `make prove-kopis`).      │
  │       (`to_canonical_spec` already lives, committed and verified, in `Ntt.lean`.)         │
  │    If even a big host struggles, split each theorem into its own file importing `Ntt`.    │
  └───────────────────────────────────────────────────────────────────────────────────────┘

  These four scalar reductions (`to_canonical` in `Ntt.lean`, the three below) are the
  documented foundation for the eventual transform-correctness proof (`ntt_mul_spec` et al.
  in `Ntt.lean`).  They are real, `sorry`-free proofs and introduce no new axioms.
-/
import Kopis.Properties.Ntt

open Aeneas Aeneas.Std Result RustKopis

namespace Kopis.Properties

set_option maxHeartbeats 1000000

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
  rw [show pNtt = 50330113 from rfl] at hlo hhi ⊢
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
  -- value facts
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
  -- divisibility 2^32 | a - t*50330113
  have emq : ∀ (b n : ℤ), b % n ≡ b [ZMOD n] := fun b n => Int.emod_emod_of_dvd b (dvd_refl n)
  have bbridge : ∀ x : ℤ, Int.bmod x (2^32) ≡ x [ZMOD (2^32)] := by
    intro x; unfold Int.ModEq
    have := @Int.bmod_emod x (2^32); norm_num at this ⊢; exact this
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
  -- exact arithmetic
  have e_i3 : (i3.val:ℤ) = 50330113 := by
    rw [hi3_def, IScalar.cast_val_eq,
      show Min.min IScalarTy.I64.numBits IScalarTy.I32.numBits = 32 from rfl, hP]
    exact bmod_i32_exact (by norm_num) (by norm_num)
  have i4p_lo : (-2147483648:ℤ) * 50330113 ≤ (t.val:ℤ) * 50330113 :=
    mul_le_mul_of_nonneg_right ht_lo (by norm_num)
  have i4p_hi : (t.val:ℤ) * 50330113 ≤ (2147483647:ℤ) * 50330113 :=
    mul_le_mul_of_nonneg_right (by omega) (by norm_num)
  have e_i4 : (i4.val:ℤ) = (t.val:ℤ) * 50330113 := by
    rw [hi4_def, I64_wrapping_mul_exact t i3 (by rw [e_i3]; omega) (by rw [e_i3]; omega), e_i3]
  have e_i5 : (i5.val:ℤ) = (a.val:ℤ) - (t.val:ℤ) * 50330113 := by
    rw [hi5_def, I64_wrapping_sub_exact a i4 (by rw [e_i4]; omega) (by rw [e_i4]; omega), e_i4]
  have e_i6 : (i6.val:ℤ) * 2^32 = (i5.val:ℤ) := by
    have hsh : (i6.val:ℤ) = (i5.val:ℤ) >>> (32:ℕ) := by
      rw [hi6_def]
      simp only [core.num.I64.wrapping_shr, IScalar.wrapping_shr, IScalar.val]
      rw [show (32#u32).val % IScalarTy.I64.numBits = 32 from rfl, BitVec.toInt_sshiftRight]
    rw [hsh, Int.shiftRight_eq_div_pow]
    have hmod : ((i5.val:ℤ)) % 2^32 = 0 := by rw [e_i5]; exact hdvd
    have hdvd32 : (2^32:ℤ) ∣ (i5.val:ℤ) := by rw [Int.dvd_iff_emod_eq_zero]; simpa using hmod
    push_cast
    exact Int.ediv_mul_cancel hdvd32
  have hi6_lo : -50330113 < (i6.val:ℤ) := by omega
  have hi6_hi : (i6.val:ℤ) < 50330113 := by omega
  -- result value
  have hr : (IScalar.cast .I32 i6).val = (i6.val:ℤ) := by
    simp only [IScalar.cast_val_eq,
      show Min.min IScalarTy.I32.numBits IScalarTy.I64.numBits = 32 from rfl]
    exact bmod_i32_exact (by omega) (by omega)
  rw [hr]
  refine ⟨?_, hi6_lo, hi6_hi⟩
  rw [e_i6, e_i5]
  have hcong : (a.val:ℤ) - (t.val:ℤ) * 50330113 ≡ (a.val:ℤ) [ZMOD 50330113] := by
    have hmul : (t.val:ℤ) * 50330113 ≡ 0 [ZMOD 50330113] :=
      (Int.modEq_zero_iff_dvd).mpr ⟨(t.val:ℤ), by ring⟩
    have h := (Int.ModEq.refl (a.val:ℤ)).sub hmul; simpa using h
  exact hcong

/-- **`to_wrapping_u16` value spec.**  The returned `u16` denotes the centered residue `x2` of
`x` in `[-P_HALF, P_HALF]` (which uniquely determines it since `2·P_HALF < p`), agreeing with it
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
  -- i = P_HALF - x1
  have e_i : (core.num.I32.wrapping_sub arithmetic.ntt.P_HALF x1).val = 25165056 - x1.val := by
    rw [I32_wrapping_sub_exact _ _ (by rw [hPH]; omega) (by rw [hPH]; omega), hPH]
  -- the mask
  have hshift : (core.num.I32.wrapping_shr (core.num.I32.wrapping_sub arithmetic.ntt.P_HALF x1)
      31#u32).val = (25165056 - x1.val) >>> (31:ℕ) := by
    simp only [core.num.I32.wrapping_shr, IScalar.wrapping_shr, IScalar.val]
    rw [show (31#u32).val % IScalarTy.I32.numBits = 31 from rfl, BitVec.toInt_sshiftRight,
      ← IScalar.val, e_i]
  set msk : I32 := core.num.I32.wrapping_shr (core.num.I32.wrapping_sub arithmetic.ntt.P_HALF x1)
    31#u32 with hmsk_def
  by_cases hc : (x1.val:ℤ) ≤ 25165056
  · -- mask = 0, i2 = 0, x2 = x1
    have hmv : (msk.val:ℤ) = 0 := by rw [hshift, Int.shiftRight_eq_div_pow]; omega
    have hand : (arithmetic.ntt.P &&& msk).val = 0 := by
      have hbv : msk.bv = 0#32 := by
        apply BitVec.eq_of_toInt_eq
        show _ = (0#32).toInt
        rw [show (0#32).toInt = (0:ℤ) from rfl]; exact hmv
      simp only [IScalar.val, IScalar.bv_and, hbv]
      rw [BitVec.and_zero]; rfl
    have e_x2 : (core.num.I32.wrapping_sub x1 (arithmetic.ntt.P &&& msk)).val = x1.val := by
      rw [I32_wrapping_sub_exact _ _ (by rw [hand]; omega) (by rw [hand]; omega), hand]; ring
    refine ⟨x1.val, hx1mod, by omega, by omega, ?_⟩
    rw [IScalar.hcast_val_eq, e_x2, show (2:ℤ)^UScalarTy.U16.numBits = 65536 from rfl,
      Int.toNat_of_nonneg (Int.emod_nonneg _ (by norm_num))]
    exact Int.emod_emod_of_dvd _ (dvd_refl _)
  · have hmv : (msk.val:ℤ) = -1 := by rw [hshift, Int.shiftRight_eq_div_pow]; omega
    have hand : (arithmetic.ntt.P &&& msk).val = 50330113 := by
      have hbv : msk.bv = BitVec.allOnes 32 := by
        apply BitVec.eq_of_toInt_eq
        show _ = (BitVec.allOnes 32).toInt
        rw [show (BitVec.allOnes 32).toInt = (-1:ℤ) from rfl]; exact hmv
      simp only [IScalar.val, IScalar.bv_and, hbv, BitVec.and_allOnes]; exact hP
    have e_x2 : (core.num.I32.wrapping_sub x1 (arithmetic.ntt.P &&& msk)).val
        = x1.val - 50330113 := by
      rw [I32_wrapping_sub_exact _ _ (by rw [hand]; omega) (by rw [hand]; omega), hand]
    refine ⟨x1.val - 50330113, ?_, by omega, by omega, ?_⟩
    · have h1 : (x1.val - 50330113 : ℤ) ≡ x1.val [ZMOD pNtt] := by
        have h0 : (x1.val - 50330113 : ℤ) ≡ x1.val - 0 [ZMOD pNtt] :=
          (Int.ModEq.refl _).sub (Int.modEq_zero_iff_dvd.mpr (by unfold pNtt; norm_num))
        simpa using h0
      exact h1.trans hx1mod
    · rw [IScalar.hcast_val_eq, e_x2, show (2:ℤ)^UScalarTy.U16.numBits = 65536 from rfl,
        Int.toNat_of_nonneg (Int.emod_nonneg _ (by norm_num))]
      exact Int.emod_emod_of_dvd _ (dvd_refl _)

private theorem ntt_barrett_qbound (x : ℤ) (hlo : -2113864746 ≤ x) (hhi : x ≤ 2113864746) :
    -42 ≤ (x * 5592576 + 140737488355328) / 2^48
      ∧ (x * 5592576 + 140737488355328) / 2^48 ≤ 42 := by omega

private theorem ntt_barrett_resbound (x q : ℤ) (hlo : -2113864746 ≤ x) (hhi : x ≤ 2113864746)
    (hq : q = (x * 5592576 + 140737488355328) / 2^48) :
    -50330113 < x - q * 50330113 ∧ x - q * 50330113 < 50330113 := by subst hq; omega

/-- **`barrett_reduce` value spec.**  `result ≡ x (mod p)` and centered in `(-p, p)`, given the
input bound `|x| ≤ 42·p` (which keeps the estimate `q ∈ [-42, 42]` so the `i32` `q·P` does not
overflow). -/
theorem barrett_reduce_spec (x : I32)
    (hlo : -(42 * pNtt) ≤ (x.val:ℤ)) (hhi : (x.val:ℤ) ≤ 42 * pNtt) :
    arithmetic.ntt.barrett_reduce x
      ⦃ (r : I32) => (r.val:ℤ) ≡ (x.val:ℤ) [ZMOD pNtt]
                     ∧ -pNtt < (r.val:ℤ) ∧ (r.val:ℤ) < pNtt ⦄ := by
  have hP : arithmetic.ntt.P.val = 50330113 := by simp only [arithmetic.ntt.P]; rfl
  have hBM : arithmetic.ntt.BARRETT_M.val = 5592576 := by simp only [arithmetic.ntt.BARRETT_M]; rfl
  have hBR : arithmetic.ntt.BARRETT_ROUND.val = 140737488355328 := by
    simp only [arithmetic.ntt.BARRETT_ROUND]; rfl
  have hxlo : -2113864746 ≤ (x.val:ℤ) := by unfold pNtt at hlo; omega
  have hxhi : (x.val:ℤ) ≤ 2113864746 := by unfold pNtt at hhi; omega
  have hxm_lo : (-2113864746:ℤ) * 5592576 ≤ (x.val:ℤ) * 5592576 :=
    mul_le_mul_of_nonneg_right hxlo (by norm_num)
  have hxm_hi : (x.val:ℤ) * 5592576 ≤ (2113864746:ℤ) * 5592576 :=
    mul_le_mul_of_nonneg_right hxhi (by norm_num)
  unfold arithmetic.ntt.barrett_reduce
  simp only [lift, bind_tc_ok, WP.spec_ok]
  set i : I64 := IScalar.cast .I64 x with hi_def
  set i1 : I64 := core.num.I64.wrapping_mul i arithmetic.ntt.BARRETT_M with hi1_def
  set i2 : I64 := core.num.I64.wrapping_add i1 arithmetic.ntt.BARRETT_ROUND with hi2_def
  set i3 : I64 := core.num.I64.wrapping_shr i2 48#u32 with hi3_def
  set q : I32 := IScalar.cast .I32 i3 with hq_def
  have e_i : (i.val:ℤ) = (x.val:ℤ) := by
    rw [hi_def, IScalar.cast_val_eq,
      show Min.min IScalarTy.I64.numBits IScalarTy.I32.numBits = 32 from rfl]
    exact bmod_i32_exact (by omega) (by omega)
  have e_i1 : (i1.val:ℤ) = (x.val:ℤ) * 5592576 := by
    rw [hi1_def, I64_wrapping_mul_exact i arithmetic.ntt.BARRETT_M
      (by rw [e_i, hBM]; omega) (by rw [e_i, hBM]; omega), e_i, hBM]
  have e_i2 : (i2.val:ℤ) = (x.val:ℤ) * 5592576 + 140737488355328 := by
    rw [hi2_def, I64_wrapping_add_exact i1 arithmetic.ntt.BARRETT_ROUND
      (by rw [e_i1, hBR]; omega) (by rw [e_i1, hBR]; omega), e_i1, hBR]
  have e_i3 : (i3.val:ℤ) = ((x.val:ℤ) * 5592576 + 140737488355328) / 2^48 := by
    have hsh : (i3.val:ℤ) = (i2.val:ℤ) >>> (48:ℕ) := by
      rw [hi3_def]
      simp only [core.num.I64.wrapping_shr, IScalar.wrapping_shr, IScalar.val]
      rw [show (48#u32).val % IScalarTy.I64.numBits = 48 from rfl, BitVec.toInt_sshiftRight]
    rw [hsh, Int.shiftRight_eq_div_pow, e_i2]; push_cast; ring
  obtain ⟨hq_lo, hq_hi⟩ : -42 ≤ (i3.val:ℤ) ∧ (i3.val:ℤ) ≤ 42 := by
    rw [e_i3]; exact ntt_barrett_qbound _ hxlo hxhi
  have e_q : (q.val:ℤ) = (i3.val:ℤ) := by
    rw [hq_def, IScalar.cast_val_eq,
      show Min.min IScalarTy.I32.numBits IScalarTy.I64.numBits = 32 from rfl]
    exact bmod_i32_exact (by omega) (by omega)
  have hqlo' : -42 ≤ (q.val:ℤ) := by rw [e_q]; exact hq_lo
  have hqhi' : (q.val:ℤ) ≤ 42 := by rw [e_q]; exact hq_hi
  have hqp_lo : (-42:ℤ) * 50330113 ≤ (q.val:ℤ) * 50330113 :=
    mul_le_mul_of_nonneg_right hqlo' (by norm_num)
  have hqp_hi : (q.val:ℤ) * 50330113 ≤ (42:ℤ) * 50330113 :=
    mul_le_mul_of_nonneg_right hqhi' (by norm_num)
  have e_i4 : (core.num.I32.wrapping_mul q arithmetic.ntt.P).val = (q.val:ℤ) * 50330113 := by
    rw [core.num.I32.wrapping_mul, IScalar.wrapping_mul_val_eq, hP]
    exact bmod_i32_exact (by omega) (by omega)
  have e_res : (core.num.I32.wrapping_sub x (core.num.I32.wrapping_mul q arithmetic.ntt.P)).val
      = (x.val:ℤ) - (q.val:ℤ) * 50330113 := by
    rw [I32_wrapping_sub_exact x _ (by rw [e_i4]; omega) (by rw [e_i4]; omega), e_i4]
  have hqx : (q.val:ℤ) = ((x.val:ℤ) * 5592576 + 140737488355328) / 2^48 := by rw [e_q, e_i3]
  obtain ⟨hrl, hrh⟩ := ntt_barrett_resbound (x.val:ℤ) (q.val:ℤ) hxlo hxhi hqx
  rw [e_res]
  refine ⟨?_, ?_, ?_⟩
  · have hmul : (q.val:ℤ) * 50330113 ≡ 0 [ZMOD pNtt] :=
      (Int.modEq_zero_iff_dvd).mpr ⟨(q.val:ℤ), by unfold pNtt; ring⟩
    have h := (Int.ModEq.refl (x.val:ℤ)).sub hmul; simpa using h
  · show -pNtt < (x.val:ℤ) - (q.val:ℤ) * 50330113; unfold pNtt; exact hrl
  · show (x.val:ℤ) - (q.val:ℤ) * 50330113 < pNtt; unfold pNtt; exact hrh

end Kopis.Properties
