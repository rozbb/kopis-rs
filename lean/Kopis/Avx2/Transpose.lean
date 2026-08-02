/-
  # Kopis/Avx2/Transpose.lean — `transpose16` is a permutation (plan phase F2).

  `backend::avx2::ntt::transpose16` reads a 256-coefficient block as a 16×16 matrix of `i16` and
  transposes it, so that afterwards vector `k` lane `m` holds coefficient `16m + k`.  That is what
  turns the four innermost transform levels into vertical butterflies, and applying it twice is
  how the transform gets back into coefficient order.

  There is no prior art for this: libcrux does not model the `vpunpck`/`vperm2i128` family at all.
  So it is done here from the lane algebra of `Kopis/Avx2/Lanes.lean`, in two steps that mirror
  the Rust:

  * `inlane8` — three interleave levels (`wd`, `dq`, `qdq`) transpose an 8×8 `i16` matrix inside
    each 128-bit half.  This is `inlane_transpose8`.
  * the `vperm2i128` pass then swaps the off-diagonal 8×8 blocks.

  Everything here is about *bits*: no value ever changes, only which lane holds it, so the whole
  file is index bookkeeping over `laneOf`.
-/
import Kopis.Avx2.Model

open Aeneas Aeneas.Std Result
open RustKopisAvx2

namespace Kopis.Avx2

set_option maxHeartbeats 1000000

/-! ## Reading a wide lane back at 16-bit granularity

Each interleave is specified at its own width — `vpunpckldq` on 32-bit lanes, `vpunpcklqdq` on
64-bit ones — but the matrix being transposed is 16-bit.  These two say a `w`-bit lane's 16-bit
sub-lanes are the 16-bit lanes of the whole word, which is what lets the three levels compose. -/

theorem lane16_of_lane32 {n : ℕ} (x : BitVec n) (m k : ℕ) (hk : k < 2) :
    laneOf 16 (laneOf 32 x m) k = laneOf 16 x (2 * m + k) := by
  have h := laneOf_laneOf 16 2 x (2 * m + k) (by omega)
  rw [show 16 * 2 = 32 from rfl, show (2 * m + k) / 2 = m by omega,
    show (2 * m + k) % 2 = k by omega] at h
  exact h.symm

theorem lane16_of_lane64 {n : ℕ} (x : BitVec n) (m k : ℕ) (hk : k < 4) :
    laneOf 16 (laneOf 64 x m) k = laneOf 16 x (4 * m + k) := by
  have h := laneOf_laneOf 16 4 x (4 * m + k) (by omega)
  rw [show 16 * 4 = 64 from rfl, show (4 * m + k) / 4 = m by omega,
    show (4 * m + k) % 4 = k by omega] at h
  exact h.symm

/-! ## The six interleaves, all at 16-bit granularity

Each is the model's own index formula, read through the two lemmas above.  The indices are left
in raw `/`-and-`%` form deliberately: every use below is at a literal lane, where `norm_num`
evaluates them, and a "simplified" closed form would only be another thing to get wrong. -/

theorem lane16_unpackloEpi16 (a b : BitVec 256) (i : ℕ) (hi : i < 16) :
    laneOf 16 (Model.unpackloEpi16 a b) i =
      laneOf 16 (if i % 2 = 0 then a else b) (8 * (i / 8) + i % 8 / 2) := by
  rw [Model.unpackloEpi16, laneOf_ofLanes16 _ hi]
  split <;> rfl

theorem lane16_unpackhiEpi16 (a b : BitVec 256) (i : ℕ) (hi : i < 16) :
    laneOf 16 (Model.unpackhiEpi16 a b) i =
      laneOf 16 (if i % 2 = 0 then a else b) (8 * (i / 8) + 4 + i % 8 / 2) := by
  rw [Model.unpackhiEpi16, laneOf_ofLanes16 _ hi]
  split <;> rfl

theorem lane16_unpackloEpi32 (a b : BitVec 256) (i : ℕ) (hi : i < 16) :
    laneOf 16 (Model.unpackloEpi32 a b) i =
      laneOf 16 (if i / 2 % 2 = 0 then a else b)
        (2 * (4 * (i / 2 / 4) + i / 2 % 4 / 2) + i % 2) := by
  rw [laneOf_laneOf 16 2 (Model.unpackloEpi32 a b) i (by omega),
    show 16 * 2 = 32 from rfl, Model.unpackloEpi32, laneOf_ofLanes32 _ (by omega)]
  split <;> rw [lane16_of_lane32 _ _ _ (by omega)]

theorem lane16_unpackhiEpi32 (a b : BitVec 256) (i : ℕ) (hi : i < 16) :
    laneOf 16 (Model.unpackhiEpi32 a b) i =
      laneOf 16 (if i / 2 % 2 = 0 then a else b)
        (2 * (4 * (i / 2 / 4) + 2 + i / 2 % 4 / 2) + i % 2) := by
  rw [laneOf_laneOf 16 2 (Model.unpackhiEpi32 a b) i (by omega),
    show 16 * 2 = 32 from rfl, Model.unpackhiEpi32, laneOf_ofLanes32 _ (by omega)]
  split <;> rw [lane16_of_lane32 _ _ _ (by omega)]

theorem lane16_unpackloEpi64 (a b : BitVec 256) (i : ℕ) (hi : i < 16) :
    laneOf 16 (Model.unpackloEpi64 a b) i =
      laneOf 16 (if i / 4 % 2 = 0 then a else b) (4 * (2 * (i / 4 / 2)) + i % 4) := by
  rw [laneOf_laneOf 16 4 (Model.unpackloEpi64 a b) i (by omega),
    show 16 * 4 = 64 from rfl, Model.unpackloEpi64, laneOf_ofLanes64 _ (by omega)]
  split <;> rw [lane16_of_lane64 _ _ _ (by omega)]

theorem lane16_unpackhiEpi64 (a b : BitVec 256) (i : ℕ) (hi : i < 16) :
    laneOf 16 (Model.unpackhiEpi64 a b) i =
      laneOf 16 (if i / 4 % 2 = 0 then a else b) (4 * (2 * (i / 4 / 2) + 1) + i % 4) := by
  rw [laneOf_laneOf 16 4 (Model.unpackhiEpi64 a b) i (by omega),
    show 16 * 4 = 64 from rfl, Model.unpackhiEpi64, laneOf_ofLanes64 _ (by omega)]
  split <;> rw [lane16_of_lane64 _ _ _ (by omega)]

/-! ## `inlane_transpose8`

The bit-level model of the Rust function: three interleave levels, written exactly as the source
writes them so the correspondence is checkable by eye. -/

/-- Output vector `r` of `inlane_transpose8` applied to `v 0 … v 7`. -/
def inlane8 (v : ℕ → BitVec 256) (r : ℕ) : BitVec 256 :=
  let a0 := Model.unpackloEpi16 (v 0) (v 1)
  let a1 := Model.unpackhiEpi16 (v 0) (v 1)
  let a2 := Model.unpackloEpi16 (v 2) (v 3)
  let a3 := Model.unpackhiEpi16 (v 2) (v 3)
  let a4 := Model.unpackloEpi16 (v 4) (v 5)
  let a5 := Model.unpackhiEpi16 (v 4) (v 5)
  let a6 := Model.unpackloEpi16 (v 6) (v 7)
  let a7 := Model.unpackhiEpi16 (v 6) (v 7)
  let b0 := Model.unpackloEpi32 a0 a2
  let b1 := Model.unpackhiEpi32 a0 a2
  let b2 := Model.unpackloEpi32 a1 a3
  let b3 := Model.unpackhiEpi32 a1 a3
  let b4 := Model.unpackloEpi32 a4 a6
  let b5 := Model.unpackhiEpi32 a4 a6
  let b6 := Model.unpackloEpi32 a5 a7
  let b7 := Model.unpackhiEpi32 a5 a7
  match r with
  | 0 => Model.unpackloEpi64 b0 b4
  | 1 => Model.unpackhiEpi64 b0 b4
  | 2 => Model.unpackloEpi64 b1 b5
  | 3 => Model.unpackhiEpi64 b1 b5
  | 4 => Model.unpackloEpi64 b2 b6
  | 5 => Model.unpackhiEpi64 b2 b6
  | 6 => Model.unpackloEpi64 b3 b7
  | _ => Model.unpackhiEpi64 b3 b7

/-- **`inlane_transpose8` transposes each 128-bit half as an 8×8 `i16` matrix.**  Writing the
lane index as `8h + c` with `h` the 128-bit half: output vector `r` lane `c` of half `h` holds
what was vector `c` lane `r` of that same half. -/
theorem laneOf_inlane8 (v : ℕ → BitVec 256) (r i : ℕ) (hr : r < 8) (hi : i < 16) :
    laneOf 16 (inlane8 v r) i = laneOf 16 (v (i % 8)) (8 * (i / 8) + r) := by
  have hrs : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 ∨ r = 4 ∨ r = 5 ∨ r = 6 ∨ r = 7 := by omega
  have his : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9
      ∨ i = 10 ∨ i = 11 ∨ i = 12 ∨ i = 13 ∨ i = 14 ∨ i = 15 := by omega
  rcases hrs with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
    rcases his with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
    norm_num [inlane8, lane16_unpackloEpi64, lane16_unpackhiEpi64, lane16_unpackloEpi32,
      lane16_unpackhiEpi32, lane16_unpackloEpi16, lane16_unpackhiEpi16]

/-! ## The `vperm2i128` pass

`inlane_transpose8` transposes all four 8×8 blocks of the 16×16 matrix in place; what remains is
to swap the two off-diagonal ones, which is one `vperm2i128` per output pair. -/

theorem lane16_of_lane128 {n : ℕ} (x : BitVec n) (m k : ℕ) (hk : k < 8) :
    laneOf 16 (laneOf 128 x m) k = laneOf 16 x (8 * m + k) := by
  have h := laneOf_laneOf 16 8 x (8 * m + k) (by omega)
  rw [show 16 * 8 = 128 from rfl, show (8 * m + k) / 8 = m by omega,
    show (8 * m + k) % 8 = k by omega] at h
  exact h.symm

/-- `vperm2i128` at 16-bit granularity, for whichever half its immediate selects. -/
theorem lane16_perm2x128 (imm : BitVec 32) (a b : BitVec 256) (i : ℕ) (hi : i < 16) (s : ℕ)
    (hz : ((imm >>> (4 * (i / 8))) &&& 8#32) = 0#32)
    (hs : ((imm >>> (4 * (i / 8))) &&& 3#32).toNat = s) :
    laneOf 16 (Model.permute2x128Si256 imm a b) i =
      laneOf 16 (Model.selectHalfBV a b s) (i % 8) := by
  have hsplit := laneOf_laneOf 16 8 (Model.permute2x128Si256 imm a b) i (by omega)
  rw [show 16 * 8 = 128 from rfl] at hsplit
  rw [hsplit, Model.permute2x128Si256, laneOf_ofLanes128 _ (by omega), if_neg (by rw [hz]; simp),
    hs]

/-- `vperm2i128` with `0x20`: the low half of each operand, in order. -/
theorem lane16_perm2x128_20 (a b : BitVec 256) (i : ℕ) (hi : i < 16) :
    laneOf 16 (Model.permute2x128Si256 0x20#32 a b) i =
      laneOf 16 (if i / 8 = 0 then a else b) (i % 8) := by
  rcases (show i / 8 = 0 ∨ i / 8 = 1 from by omega) with h | h
  · rw [lane16_perm2x128 _ a b i hi 0 (by rw [h]; decide) (by rw [h]; decide), h, if_pos rfl]
    simp only [Model.selectHalfBV]
    rw [lane16_of_lane128 a 0 (i % 8) (by omega)]
    norm_num
  · rw [lane16_perm2x128 _ a b i hi 2 (by rw [h]; decide) (by rw [h]; decide), h,
      if_neg (by decide)]
    simp only [Model.selectHalfBV]
    rw [lane16_of_lane128 b 0 (i % 8) (by omega)]
    norm_num

/-- `vperm2i128` with `0x31`: the high half of each operand, in order. -/
theorem lane16_perm2x128_31 (a b : BitVec 256) (i : ℕ) (hi : i < 16) :
    laneOf 16 (Model.permute2x128Si256 0x31#32 a b) i =
      laneOf 16 (if i / 8 = 0 then a else b) (8 + i % 8) := by
  rcases (show i / 8 = 0 ∨ i / 8 = 1 from by omega) with h | h
  · rw [lane16_perm2x128 _ a b i hi 1 (by rw [h]; decide) (by rw [h]; decide), h, if_pos rfl]
    simp only [Model.selectHalfBV]
    rw [lane16_of_lane128 a 1 (i % 8) (by omega)]
  · rw [lane16_perm2x128 _ a b i hi 3 (by rw [h]; decide) (by rw [h]; decide), h,
      if_neg (by decide)]
    simp only [Model.selectHalfBV]
    rw [lane16_of_lane128 b 1 (i % 8) (by omega)]

/-- The bit-level model of `transpose16`, on a block read as sixteen 16-lane vectors. -/
def transpose16Model (B : ℕ → BitVec 256) (k : ℕ) : BitVec 256 :=
  if k < 8 then
    Model.permute2x128Si256 0x20#32 (inlane8 B k) (inlane8 (fun j => B (8 + j)) k)
  else
    Model.permute2x128Si256 0x31#32 (inlane8 B (k - 8)) (inlane8 (fun j => B (8 + j)) (k - 8))

/-- **`transpose16` is the 16×16 transpose.**  Vector `k` lane `m` of the result is vector `m`
lane `k` of the input — equivalently, it holds coefficient `16m + k`.  Being a transpose, it is
its own inverse, which is `transpose16Model_involutive` below. -/
theorem laneOf_transpose16Model (B : ℕ → BitVec 256) (k m : ℕ) (hk : k < 16) (hm : m < 16) :
    laneOf 16 (transpose16Model B k) m = laneOf 16 (B m) k := by
  rw [transpose16Model]
  by_cases hk8 : k < 8
  · rw [if_pos hk8, lane16_perm2x128_20 _ _ _ hm]
    by_cases hm8 : m < 8
    · rw [if_pos (by omega : m / 8 = 0), laneOf_inlane8 _ _ _ hk8 (by omega)]
      simp only [show m % 8 % 8 = m from by omega, show m % 8 / 8 = 0 from by omega,
        Nat.mul_zero, Nat.zero_add]
    · rw [if_neg (by omega : ¬ m / 8 = 0), laneOf_inlane8 _ _ _ hk8 (by omega)]
      simp only [show m % 8 % 8 = m % 8 from by omega, show m % 8 / 8 = 0 from by omega,
        Nat.mul_zero, Nat.zero_add, show 8 + m % 8 = m from by omega]
  · rw [if_neg hk8, lane16_perm2x128_31 _ _ _ hm]
    by_cases hm8 : m < 8
    · rw [if_pos (by omega : m / 8 = 0), laneOf_inlane8 _ _ _ (by omega) (by omega)]
      simp only [show (8 + m % 8) % 8 = m from by omega, show (8 + m % 8) / 8 = 1 from by omega,
        Nat.mul_one, show 8 + (k - 8) = k from by omega]
    · rw [if_neg (by omega : ¬ m / 8 = 0), laneOf_inlane8 _ _ _ (by omega) (by omega)]
      simp only [show 8 + m % 8 = m from by omega, show m / 8 = 1 from by omega, Nat.mul_one,
        show 8 + (k - 8) = k from by omega]

/-- **Applied twice, `transpose16` is the identity** — which is how the transform, having done
its four innermost levels vertically, gets back into coefficient order. -/
theorem transpose16Model_involutive (B : ℕ → BitVec 256) (k : ℕ) (hk : k < 16) :
    transpose16Model (transpose16Model B) k = B k := by
  apply eq_of_lane16_bv
  intro m hm
  rw [laneOf_transpose16Model _ k m hk hm, laneOf_transpose16Model _ m k hm hk]

end Kopis.Avx2
