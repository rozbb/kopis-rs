/-
  # Kopis/Properties/NttCrtLane.lean — the two scalar routines the portable transform is built of.

  `src/arithmetic/ntt_crt.rs` has exactly two pieces of arithmetic: `mont_mul`, the signed
  Montgomery multiply every butterfly is made of, and `barrett`, the centred reduction that
  re-centres a block between runs of levels.  Both are four or five wrapping 16-bit operations
  with a `>> 16` in the middle, and both are *exactly* what the vector backends compute in
  sixteen lanes at a time.

  So the mathematics is not here — it is in `Kopis/CrtArith.lean`, shared with the AVX2 proof.
  What is here is the bridge from aeneas's value semantics to the integers those lemmas talk
  about: `IScalar.cast` is `Int.bmod`, `wrapping_mul` is `Int.bmod` of the product, and the two
  checked shifts are `Int.shiftRight` once their shift amounts are seen to be in range.

  The one place to read carefully is where a wrapping operation is claimed *exact*.  Each is
  discharged by `bmod16_eq_self` from a magnitude bound, and every such bound is a hypothesis of
  the enclosing spec rather than something established in passing — because in `mont_mul` the
  intermediate products genuinely do overflow and wrap, and only the final answer is small.
-/
import Kopis.CrtArith
import Kopis.Properties.NttCrtZeta

open Aeneas Aeneas.Std Result
open RustKopisSerial

namespace Kopis.Properties

open Kopis.CrtArith

set_option maxHeartbeats 1000000

/-! ## The checked shifts

`>>>` on two `IScalar`s fails when the shift amount is negative or too wide.  Both uses here have
a literal amount, so the guard is decided once and the value is an ordinary `Int.shiftRight`. -/

/-- `x >>> 16` on an `i32`. -/
theorem I32_shr16 (x : I32) :
    ∃ y : I32, (x >>> (16#i32) : Result I32) = ok y ∧ y.val = x.val >>> (16 : ℕ) := by
  refine ⟨⟨x.bv.sshiftRight 16⟩, ?_, ?_⟩
  · show IScalar.shiftRight_IScalar x (16#i32) = _
    unfold IScalar.shiftRight_IScalar IScalar.shiftRight
    rw [if_pos (by decide), if_pos (by decide)]
    rfl
  · show (x.bv.sshiftRight 16).toInt = _
    rw [BitVec.toInt_sshiftRight]
    rfl

/-- `x >>> 11` on an `i16`, the Barrett shift. -/
theorem I16_shr11 (x : I16) :
    ∃ y : I16, (x >>> backend.crt.BARRETT_SH : Result I16) = ok y ∧
      y.val = x.val >>> (11 : ℕ) := by
  have hsh : backend.crt.BARRETT_SH = 11#i32 := by
    simp only [backend.crt.BARRETT_SH]
  rw [hsh]
  refine ⟨⟨x.bv.sshiftRight 11⟩, ?_, ?_⟩
  · show IScalar.shiftRight_IScalar x (11#i32) = _
    unfold IScalar.shiftRight_IScalar IScalar.shiftRight
    rw [if_pos (by decide), if_pos (by decide)]
    rfl
  · show (x.bv.sshiftRight 11).toInt = _
    rw [BitVec.toInt_sshiftRight]
    rfl

/-! ## Widening and narrowing casts -/

/-- `i16 → i32` is exact: the `bmod` is by `2¹⁶` and the value is already inside it. -/
theorem cast_i16_i32 (x : I16) : (IScalar.cast .I32 x).val = x.val := by
  rw [IScalar.cast_val_eq, show Min.min IScalarTy.I32.numBits IScalarTy.I16.numBits = 16 from rfl]
  exact bmod16_eq_self (by scalar_tac) (by scalar_tac)

/-- `i32 → i16` truncates, which is `Int.bmod` by `2¹⁶`. -/
theorem cast_i32_i16 (x : I32) : (IScalar.cast .I16 x).val = (x.val).bmod (2 ^ 16) := by
  rw [IScalar.cast_val_eq, show Min.min IScalarTy.I16.numBits IScalarTy.I32.numBits = 16 from rfl]

/-! ## `mont_mul`

`a·z·2⁻¹⁶ mod q`, centred.  The bound hypothesis `|a·z| < 2¹⁵·q` is the growth schedule's job to
maintain; the Montgomery pairing `zq·q ≡ z (mod 2¹⁶)` is the table's, and comes from
`zeta_table_ok_q1` / `_q2`. -/

theorem mont_mul_spec (a z zq q : I16) (Q : ℤ)
    (hQ : q.val = Q) (hQpos : 0 < Q) (hQlt : Q ≤ 2 ^ 15)
    (hzq : (2 ^ 16 : ℤ) ∣ (zq.val * Q - z.val))
    (hbnd : |a.val * z.val| < 2 ^ 15 * Q) :
    arithmetic.ntt_crt.mont_mul a z zq q
      ⦃ (c : I16) => Q ∣ (c.val * 2 ^ 16 - a.val * z.val) ∧
          -Q < c.val ∧ c.val < Q ∧
          2 ^ 16 * |c.val| ≤ |a.val| * |z.val| + 2 ^ 15 * Q ⦄ := by
  obtain ⟨R, hRdef, hRlo, hRhi, hRdvd, hRsharp⟩ :=
    mont_mul_core (A := a.val) (Z := z.val) (ZQ := zq.val) (Q := Q) hQpos hQlt hzq hbnd
  have hAZ := abs_lt.mp hbnd
  have hTb := bmod16_bounds (a.val * zq.val)
  set T : ℤ := (a.val * zq.val).bmod (2 ^ 16) with hTdef
  -- the Montgomery quotient, as an `i16`
  have hTeq : (core.num.I16.wrapping_mul a zq).val = T := by
    rw [core.num.I16.wrapping_mul, IScalar.wrapping_mul_val_eq]
    rfl
  -- the two 32-bit products, exact because both are below `2³⁰`
  have hprod1 :
      (core.num.I32.wrapping_mul (IScalar.cast .I32 a) (IScalar.cast .I32 z)).val
        = a.val * z.val := by
    rw [core.num.I32.wrapping_mul, IScalar.wrapping_mul_val_eq, cast_i16_i32, cast_i16_i32,
      show (2 : ℕ) ^ IScalarTy.I32.numBits = 2 ^ 32 from rfl]
    exact bmod32_eq_self (by norm_num at hAZ ⊢; omega) (by norm_num at hAZ ⊢; omega)
  have hprod2 :
      (core.num.I32.wrapping_mul (IScalar.cast .I32 (core.num.I16.wrapping_mul a zq))
          (IScalar.cast .I32 q)).val = T * Q := by
    rw [core.num.I32.wrapping_mul, IScalar.wrapping_mul_val_eq, cast_i16_i32, cast_i16_i32,
      hTeq, hQ, show (2 : ℕ) ^ IScalarTy.I32.numBits = 2 ^ 32 from rfl]
    have h1 : -(2 ^ 30 : ℤ) ≤ T * Q ∧ T * Q ≤ 2 ^ 30 := by
      constructor <;> nlinarith [hTb.1, hTb.2, hQpos, hQlt]
    exact bmod32_eq_self (by norm_num at h1 ⊢; omega) (by norm_num at h1 ⊢; omega)
  unfold arithmetic.ntt_crt.mont_mul
  simp only [lift, bind_tc_ok]
  obtain ⟨y1, hy1, hy1v⟩ :=
    I32_shr16 (core.num.I32.wrapping_mul (IScalar.cast .I32 a) (IScalar.cast .I32 z))
  rw [hy1, bind_tc_ok]
  obtain ⟨y2, hy2, hy2v⟩ :=
    I32_shr16 (core.num.I32.wrapping_mul (IScalar.cast .I32 (core.num.I16.wrapping_mul a zq))
      (IScalar.cast .I32 q))
  rw [hy2, bind_tc_ok]
  simp only [WP.spec_ok]
  rw [hprod1] at hy1v
  rw [hprod2] at hy2v
  -- the final wrapping subtraction of the two truncated halves is exact
  have hres : (core.num.I16.wrapping_sub (IScalar.cast .I16 y1) (IScalar.cast .I16 y2)).val = R := by
    rw [core.num.I16.wrapping_sub, IScalar.wrapping_sub_val_eq, cast_i32_i16, cast_i32_i16,
      show (2 : ℕ) ^ IScalarTy.I16.numBits = 2 ^ 16 from rfl]
    have hc : ((y1.val).bmod (2 ^ 16) - (y2.val).bmod (2 ^ 16))
        ≡ (y1.val - y2.val) [ZMOD (((2 ^ 16 : ℕ)) : ℤ)] :=
      Int.ModEq.sub Int.bmod_emod Int.bmod_emod
    rw [bmod_congr hc, hy1v, hy2v, hRdef]
    exact bmod16_eq_self (by omega) (by omega)
  rw [hres]
  exact ⟨hRdvd, hRlo, hRhi, hRsharp⟩

/-! ## `barrett`

`r ≡ x (mod q)` with `2·|r| < q`, for any `i16` input.  Unlike `mont_mul` this needs nothing of
the caller: the rounding addend `2^(SH−1)` is what makes the result centred rather than merely
bounded, and `hD` — the accuracy of the Barrett multiplier — is a fact about the two constants. -/

theorem barrett_spec (x m q : I16) (Q M : ℤ)
    (hQ : q.val = Q) (hM : m.val = M)
    (hQpos : 0 < Q) (hQlt : Q < 2 ^ 14) (hQodd : ¬ (2 ∣ Q))
    (hMpos : 0 < M) (hMlt : M < 2 ^ 15)
    (hD : |2 ^ 27 - Q * M| ≤ 2047) :
    arithmetic.ntt_crt.barrett x m q
      ⦃ (c : I16) => Q ∣ (c.val - x.val) ∧ 2 * |c.val| < Q ⦄ := by
  have hxlo : -(2 ^ 15 : ℤ) ≤ x.val := by scalar_tac
  have hxhi : x.val < 2 ^ 15 := by scalar_tac
  set V : ℤ := (x.val * M) >>> (16 : ℕ) with hVdef
  set T : ℤ := (V + 2 ^ 10) >>> (11 : ℕ) with hTdef
  have hVb := barrett_hi_bound hxlo hxhi hMpos hMlt hVdef
  have hRb := barrett_core hxlo hxhi hQpos hQlt hQodd hMpos hMlt hD hVdef hTdef
  have hRabs : -(2 ^ 15 : ℤ) ≤ x.val - T * Q ∧ x.val - T * Q < 2 ^ 15 := by
    rcases abs_cases (x.val - T * Q) with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h] at hRb <;> omega
  -- the 32-bit product is exact, and its high half fits an `i16`
  have hprod : (core.num.I32.wrapping_mul (IScalar.cast .I32 x) (IScalar.cast .I32 m)).val
      = x.val * M := by
    rw [core.num.I32.wrapping_mul, IScalar.wrapping_mul_val_eq, cast_i16_i32, cast_i16_i32, hM,
      show (2 : ℕ) ^ IScalarTy.I32.numBits = 2 ^ 32 from rfl]
    have h1 : -(2 ^ 30 : ℤ) ≤ x.val * M ∧ x.val * M < 2 ^ 30 := by
      constructor <;> nlinarith [hxlo, hxhi, hMpos, hMlt]
    exact bmod32_eq_self (by norm_num at h1 ⊢; omega) (by norm_num at h1 ⊢; omega)
  unfold arithmetic.ntt_crt.barrett
  simp only [lift, bind_tc_ok]
  obtain ⟨y1, hy1, hy1v⟩ :=
    I32_shr16 (core.num.I32.wrapping_mul (IScalar.cast .I32 x) (IScalar.cast .I32 m))
  rw [hprod] at hy1v
  rw [hy1, bind_tc_ok]
  -- the rounding addend, and the shift that forms `t ≈ round(x/q)`
  have hsub : (backend.crt.BARRETT_SH - 1#i32 : Result I32) = ok 10#i32 := by
    have hsh : backend.crt.BARRETT_SH = 11#i32 := by simp only [backend.crt.BARRETT_SH]
    rw [hsh]; rfl
  rw [hsub, bind_tc_ok]
  have hshl : ((1#i16) <<< (10#i32) : Result I16) = ok 1024#i16 := by
    show IScalar.shiftLeft_IScalar (1#i16) (10#i32) = _
    unfold IScalar.shiftLeft_IScalar IScalar.shiftLeft
    rw [if_pos (by decide), if_pos (by decide)]
    rfl
  rw [hshl, bind_tc_ok]
  -- `t = V`, so `t + 1024` is exact
  have hy1V : y1.val = V := by rw [hy1v, hVdef]
  have hcastV : (IScalar.cast .I16 y1).val = V := by
    rw [cast_i32_i16, hy1V]; exact bmod16_eq_self (by omega) (by omega)
  have hadd : (core.num.I16.wrapping_add (IScalar.cast .I16 y1) 1024#i16).val = V + 2 ^ 10 := by
    rw [core.num.I16.wrapping_add, IScalar.wrapping_add_val_eq, hcastV,
      show (1024#i16).val = 1024 from rfl,
      show (2 : ℕ) ^ IScalarTy.I16.numBits = 2 ^ 16 from rfl]
    exact bmod16_eq_self (by norm_num; omega) (by norm_num; omega)
  obtain ⟨y2, hy2, hy2v⟩ := I16_shr11 (core.num.I16.wrapping_add (IScalar.cast .I16 y1) 1024#i16)
  rw [hy2, bind_tc_ok]
  simp only [WP.spec_ok]
  rw [hadd] at hy2v
  have hy2T : y2.val = T := by rw [hy2v, hTdef]
  -- and the final wrapping subtraction is exact because the answer is centred
  have hres : (core.num.I16.wrapping_sub x (core.num.I16.wrapping_mul y2 q)).val
      = x.val - T * Q := by
    rw [core.num.I16.wrapping_sub, IScalar.wrapping_sub_val_eq, core.num.I16.wrapping_mul,
      IScalar.wrapping_mul_val_eq, hy2T, hQ,
      show (2 : ℕ) ^ IScalarTy.I16.numBits = 2 ^ 16 from rfl]
    have hc : (x.val - (T * Q).bmod (2 ^ 16)) ≡ (x.val - T * Q) [ZMOD (((2 ^ 16 : ℕ)) : ℤ)] :=
      Int.ModEq.sub (Int.ModEq.refl _) Int.bmod_emod
    rw [bmod_congr hc]
    exact bmod16_eq_self hRabs.1 hRabs.2
  rw [hres]
  exact ⟨⟨-T, by ring⟩, hRb⟩

end Kopis.Properties
