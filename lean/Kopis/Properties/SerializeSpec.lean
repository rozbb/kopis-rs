import Kopis.Properties.SerializeEnc2
open Aeneas Aeneas.Std Result kopis
open scoped BigOperators
namespace Kopis.Properties

set_option maxHeartbeats 2000000
set_option maxRecDepth 4000

theorem byte_testBit (x p j : ℕ) (hj : j < 8) :
    (x / 256 ^ p % 256).testBit j = x.testBit (8 * p + j) := by
  rw [show (256 : ℕ) = 2 ^ 8 from by norm_num, ← pow_mul, Nat.testBit_mod_two_pow]
  simp only [hj, decide_true, Bool.true_and, Nat.testBit_div_two_pow]
  congr 1; omega

theorem byte_eq (x y : ℕ) (hx : x < 256) (hy : y < 256) (h : ∀ j, j < 8 → x.testBit j = y.testBit j) :
    x = y := by
  apply Nat.eq_of_testBit_eq; intro j
  by_cases hj : j < 8
  · exact h j hj
  · have hpow : (2 : ℕ) ^ 8 ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h256 : (256 : ℕ) = 2 ^ 8 := by norm_num
    rw [Nat.testBit_lt_two_pow (by omega), Nat.testBit_lt_two_pow (by omega)]

/-- Byte `p` of a Nat as a sum of its 8 bits. -/
theorem sum_bit_byte (x p : ℕ) :
    ∑ j ∈ Finset.range 8, (x.testBit (8 * p + j)).toNat * 2 ^ j = x / 256 ^ p % 256 := by
  have hbit : ∀ j, x.testBit (8 * p + j) = (x >>> (8 * p)).testBit j := fun j => by
    rw [Nat.testBit_shiftRight]
  simp_rw [hbit]
  rw [sum_testBit_eq_mod, show (2 : ℕ) ^ 8 = 256 from by norm_num, Nat.shiftRight_eq_div_pow,
    show (2 : ℕ) ^ (8 * p) = 256 ^ p from by rw [pow_mul]; norm_num]

theorem packedSum_lt (a : ℕ → ℕ) (n q : ℕ) (ha : ∀ i, a i < 2 ^ n) :
    (∑ i ∈ Finset.range q, a i * 2 ^ (n * i)) < 2 ^ (n * q) := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [Finset.sum_range_succ]
    have hle : a q * 2 ^ (n * q) + 2 ^ (n * q) ≤ 2 ^ n * 2 ^ (n * q) := by
      have := ha q; rw [← Nat.succ_mul]; gcongr; omega
    have hpow : 2 ^ n * 2 ^ (n * q) = 2 ^ (n * (q + 1)) := by rw [← pow_add]; congr 1; ring
    omega

/-- Disjoint `n`-bit packing: bit `n·q + s` (with `s < n`, `q < K`) of `∑ aᵢ·2^(n·i)`
(each `aᵢ < 2^n`) is bit `s` of `a q`. -/
theorem packed_testBit (a : ℕ → ℕ) (n K : ℕ) (ha : ∀ i, a i < 2 ^ n) (q s : ℕ)
    (hs : s < n) (hq : q < K) :
    (∑ i ∈ Finset.range K, a i * 2 ^ (n * i)).testBit (n * q + s) = (a q).testBit s := by
  set L := ∑ i ∈ Finset.range q, a i * 2 ^ (n * i) with hL_def
  set H := ∑ t ∈ Finset.range (K - (q + 1)), a (q + 1 + t) * 2 ^ (n * t) with hH_def
  have hsplit : (∑ i ∈ Finset.range K, a i * 2 ^ (n * i)) = 2 ^ (n * q) * (a q + 2 ^ n * H) + L := by
    rw [hL_def, ← Finset.sum_range_add_sum_Ico _ (show q ≤ K by omega), add_comm]
    congr 1
    have e1 : ∀ i ∈ Finset.Ico q K, a i * 2 ^ (n * i) = 2 ^ (n * q) * (a i * 2 ^ (n * (i - q))) := by
      intro i hi; rw [Finset.mem_Ico] at hi
      rw [show 2 ^ (n * q) * (a i * 2 ^ (n * (i - q))) = a i * (2 ^ (n * q) * 2 ^ (n * (i - q))) from by ring,
        ← pow_add, show n * q + n * (i - q) = n * i from by rw [← Nat.mul_add]; congr 1; omega]
    rw [Finset.sum_congr rfl e1, ← Finset.mul_sum]
    congr 1
    rw [Finset.sum_Ico_eq_sum_range]
    have reix : ∀ t ∈ Finset.range (K - q),
        a (q + t) * 2 ^ (n * (q + t - q)) = a (q + t) * 2 ^ (n * t) := by
      intro t _; rw [show q + t - q = t from by omega]
    rw [Finset.sum_congr rfl reix, show K - q = (K - (q + 1)) + 1 from by omega, Finset.sum_range_succ',
      hH_def, Finset.mul_sum]
    simp only [Nat.add_zero, Nat.mul_zero, pow_zero, mul_one]
    rw [add_comm]
    congr 1
    apply Finset.sum_congr rfl; intro t _
    rw [show q + (t + 1) = q + 1 + t from by ring, show n * (t + 1) = n + n * t from by ring, pow_add]
    ring
  have hL_lt : L < 2 ^ (n * q) := packedSum_lt a n q ha
  rw [hsplit, Nat.testBit_two_pow_mul_add _ hL_lt, if_neg (by omega),
    show n * q + s - n * q = s from by omega,
    show a q + 2 ^ n * H = 2 ^ n * H + a q from by ring, Nat.testBit_two_pow_mul_add _ (ha q), if_pos hs]

end Kopis.Properties
