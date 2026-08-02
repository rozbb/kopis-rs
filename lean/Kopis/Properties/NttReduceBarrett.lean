/-
  # Kopis/Properties/NttReduceBarrett.lean — the `barrett_reduce` value spec.

  One of the four scalar reductions of `src/arithmetic/ntt.rs`.  Split into its own file
  (alongside `NttReduceMont` / `NttReduceWrap`) so the three memory-heavy WP-monadic proofs
  elaborate independently.

  ## The shape of the argument

  `barrett_reduce x` computes `q := (x·M + 2⁴⁷) >> 48` (in `i64`) and returns `x - q·p`, where
  `M = 5592576 ≈ 2⁴⁸/p`.  Correctness needs two numeric facts:

  * `|q| ≤ 42`, so the `i32` product `q·P` does not overflow; and
  * `|x - q·p| < p`, i.e. `q` really is the rounded quotient.

  Both are stated over the *euclidean decomposition* of the shift — `x·M + 2⁴⁷ = q·2⁴⁸ + r` with
  `0 ≤ r < 2⁴⁸` — which turns them into plain linear-arithmetic facts that `linarith`
  discharges in milliseconds.  Asking `omega` to reason about `/ 2⁴⁸` directly (as an earlier
  draft did) makes it eliminate a division by a 2⁴⁸-sized constant against 2⁶³-sized bounds.

  The margin is enormous: `2⁴⁸ - p·M = -5330432`, so over `|x| ≤ 42p` the error term
  `x·(2⁴⁸ - p·M)` is at most `1.13·10¹⁶` against a budget of `p·2⁴⁷ ≈ 7.08·10²¹`.

  ## Why `clear_value`

  `set` introduces its abbreviations as *let-bound* locals.  Left that way, the kernel
  zeta-expands them while checking the finished term and then has to reduce `BitVec` operations
  on 64-bit literals inside every arithmetic side condition — which is where this file's former
  ~15 GB / 14 min elaboration and its `(kernel) deep recursion` failures came from.  Once the
  five value equations `e_i … e_q` have been established, `clear_value` (and dropping the
  definitional hypotheses) makes the abbreviations opaque, and everything downstream is ordinary
  integer arithmetic over five unknowns.
-/
import Kopis.Properties.Ntt

open Aeneas Aeneas.Std Result RustKopisSerial

namespace Kopis.Properties

/-- The Barrett quotient estimate lies in `[-42, 42]`, so `q · P` stays inside `i32`.  Stated
over the euclidean decomposition of the arithmetic shift rather than over `/ 2⁴⁸`. -/
private theorem ntt_barrett_qbound (x q r : ℤ)
    (hdec : x * 5592576 + 140737488355328 = q * 281474976710656 + r)
    (hr0 : 0 ≤ r) (hr1 : r < 281474976710656)
    (hlo : -2113864746 ≤ x) (hhi : x ≤ 2113864746) :
    -42 ≤ q ∧ q ≤ 42 := by
  constructor <;> linarith

/-- The Barrett remainder is centered: `|x - q·p| < p`. -/
private theorem ntt_barrett_resbound (x q r : ℤ)
    (hdec : x * 5592576 + 140737488355328 = q * 281474976710656 + r)
    (hr0 : 0 ≤ r) (hr1 : r < 281474976710656)
    (hlo : -2113864746 ≤ x) (hhi : x ≤ 2113864746) :
    -50330113 < x - q * 50330113 ∧ x - q * 50330113 < 50330113 := by
  constructor <;> linarith

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
  unfold arithmetic.ntt.barrett_reduce
  simp only [lift, bind_tc_ok, WP.spec_ok]
  set i : I64 := IScalar.cast .I64 x with hi_def
  set i1 : I64 := core.num.I64.wrapping_mul i arithmetic.ntt.BARRETT_M with hi1_def
  set i2 : I64 := core.num.I64.wrapping_add i1 arithmetic.ntt.BARRETT_ROUND with hi2_def
  set i3 : I64 := core.num.I64.wrapping_shr i2 48#u32 with hi3_def
  set q : I32 := IScalar.cast .I32 i3 with hq_def
  -- ## Step 1: the five value equations (these are the only steps that need the definitions)
  have e_i : (i.val:ℤ) = (x.val:ℤ) := by
    rw [hi_def, IScalar.cast_val_eq,
      show Min.min IScalarTy.I64.numBits IScalarTy.I32.numBits = 32 from rfl]
    exact bmod_i32_exact (by omega) (by omega)
  have e_i1 : (i1.val:ℤ) = (x.val:ℤ) * 5592576 := by
    rw [hi1_def, I64_wrapping_mul_exact i arithmetic.ntt.BARRETT_M
      (by rw [e_i, hBM]; nlinarith) (by rw [e_i, hBM]; nlinarith), e_i, hBM]
  have e_i2 : (i2.val:ℤ) = (x.val:ℤ) * 5592576 + 140737488355328 := by
    rw [hi2_def, I64_wrapping_add_exact i1 arithmetic.ntt.BARRETT_ROUND
      (by rw [e_i1, hBR]; nlinarith) (by rw [e_i1, hBR]; nlinarith), e_i1, hBR]
  have e_i3 : (i3.val:ℤ) = ((x.val:ℤ) * 5592576 + 140737488355328) / 281474976710656 := by
    have hsh : (i3.val:ℤ) = (i2.val:ℤ) >>> (48:ℕ) := by
      rw [hi3_def]
      simp only [core.num.I64.wrapping_shr, IScalar.wrapping_shr, IScalar.val]
      rw [show (48#u32).val % IScalarTy.I64.numBits = 48 from rfl, BitVec.toInt_sshiftRight]
    rw [hsh, Int.shiftRight_eq_div_pow, e_i2]
    norm_num
  -- the euclidean decomposition, which is what keeps every later bound linear
  have hr0 : 0 ≤ ((x.val:ℤ) * 5592576 + 140737488355328) % 281474976710656 :=
    Int.emod_nonneg _ (by norm_num)
  have hr1 : ((x.val:ℤ) * 5592576 + 140737488355328) % 281474976710656 < 281474976710656 :=
    Int.emod_lt_of_pos _ (by norm_num)
  have hea := Int.mul_ediv_add_emod ((x.val:ℤ) * 5592576 + 140737488355328) 281474976710656
  have hdec : (x.val:ℤ) * 5592576 + 140737488355328
      = (i3.val:ℤ) * 281474976710656
        + ((x.val:ℤ) * 5592576 + 140737488355328) % 281474976710656 := by
    rw [e_i3]; linarith
  obtain ⟨hq3_lo, hq3_hi⟩ := ntt_barrett_qbound (x.val:ℤ) (i3.val:ℤ) _ hdec hr0 hr1 hxlo hxhi
  have e_q : (q.val:ℤ) = (i3.val:ℤ) := by
    rw [hq_def, IScalar.cast_val_eq,
      show Min.min IScalarTy.I32.numBits IScalarTy.I64.numBits = 32 from rfl]
    exact bmod_i32_exact (by omega) (by omega)
  -- ## Step 2: forget the definitions — everything below is plain integer arithmetic
  clear_value q i3 i2 i1 i
  clear hq_def hi3_def hi2_def hi1_def hi_def hea
  have hq_lo : -42 ≤ (q.val:ℤ) := by rw [e_q]; exact hq3_lo
  have hq_hi : (q.val:ℤ) ≤ 42 := by rw [e_q]; exact hq3_hi
  have hqp_lo : (-2113864746:ℤ) ≤ (q.val:ℤ) * 50330113 := by nlinarith
  have hqp_hi : (q.val:ℤ) * 50330113 ≤ 2113864746 := by nlinarith
  have e_i4 : (core.num.I32.wrapping_mul q arithmetic.ntt.P).val = (q.val:ℤ) * 50330113 := by
    rw [core.num.I32.wrapping_mul, IScalar.wrapping_mul_val_eq, hP]
    exact bmod_i32_exact (by linarith) (by linarith)
  have e_res : (core.num.I32.wrapping_sub x (core.num.I32.wrapping_mul q arithmetic.ntt.P)).val
      = (x.val:ℤ) - (q.val:ℤ) * 50330113 := by
    rw [I32_wrapping_sub_exact x _ (by rw [e_i4]; linarith) (by rw [e_i4]; linarith), e_i4]
  obtain ⟨hrl, hrh⟩ :=
    ntt_barrett_resbound (x.val:ℤ) (q.val:ℤ) _ (by rw [e_q]; exact hdec) hr0 hr1 hxlo hxhi
  rw [e_res]
  refine ⟨?_, ?_, ?_⟩
  · have hmul : (q.val:ℤ) * 50330113 ≡ 0 [ZMOD pNtt] :=
      (Int.modEq_zero_iff_dvd).mpr ⟨(q.val:ℤ), by unfold pNtt; ring⟩
    have h := (Int.ModEq.refl (x.val:ℤ)).sub hmul; simpa using h
  · show -pNtt < (x.val:ℤ) - (q.val:ℤ) * 50330113; unfold pNtt; exact hrl
  · show (x.val:ℤ) - (q.val:ℤ) * 50330113 < pNtt; unfold pNtt; exact hrh

end Kopis.Properties
