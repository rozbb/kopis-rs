/-
  # Kopis/Avx2/Lanes.lean — the lane algebra.

  `Kopis/Avx2/Intrinsics.lean` states every AVX2 axiom through `laneOf w x i`, the `w`-bit lane
  `i` of a 256- (or 128-) bit word.  Two things are needed before those axioms can be composed
  into anything, and both are proved here rather than assumed:

  * **Lanes determine the word.**  An axiom that fixes all 16 of a result's 16-bit lanes must be
    usable where a whole-register fact is needed, and vice versa.  `eq_of_laneOf_eq` and the
    `Vec256`/`Vec128` corollaries below are that bridge.  libcrux `admit()`s the corresponding
    step; this is the one place it costs anything to prove it, and it costs one induction.
  * **A word can be built from its lanes.**  `ofLanes*` constructs the word whose lane `i` is
    `f i`, and `laneOf_ofLanes*` reads it back.  Every computable model in
    `Kopis/Avx2/Model.lean` is phrased with it, which is what lets a model be checked against an
    axiom lane by lane and evaluated by `#eval` on a test vector.

  Everything here is about `BitVec`; nothing in this file mentions an extracted constant except
  the four `Vec256`/`Vec128` corollaries at the end, which go through `bits_inj`.
-/
import Kopis.Avx2.Intrinsics

namespace Kopis.Avx2

/-! ## Bits of a lane -/

/-- Bit `j` of lane `i` is bit `w * i + j` of the word — the defining property of `laneOf`,
which every proof below is ultimately a rearrangement of. -/
@[simp] theorem getLsbD_laneOf {n : Nat} (w : Nat) (x : BitVec n) (i j : Nat) :
    (laneOf w x i).getLsbD j = (decide (j < w) && x.getLsbD (w * i + j)) := by
  simp [laneOf]

theorem getElem_laneOf {n : Nat} (w : Nat) (x : BitVec n) (i j : Nat) (hj : j < w) :
    (laneOf w x i)[j] = x.getLsbD (w * i + j) := by
  rw [← BitVec.getLsbD_eq_getElem, getLsbD_laneOf]
  simp [hj]

/-! ## Building a word from its lanes

`concatLanes w f n` is the `w * n`-bit word holding lanes `f 0, …, f (n-1)`, least significant
first.  The recursion appends the *new, most significant* lane on the left, so the induction
below never has to reason about division by `w`. -/

/-- The `w * n`-bit word whose lane `i` is `f i`, for `i < n`. -/
def concatLanes (w : Nat) (f : Nat → BitVec w) : (n : Nat) → BitVec (w * n)
  | 0 => 0#(w * 0)
  | n + 1 => (f n ++ concatLanes w f n).cast (by rw [Nat.mul_succ, Nat.add_comm])

theorem laneOf_concatLanes (w : Nat) (f : Nat → BitVec w) :
    ∀ (n i : Nat), i < n → laneOf w (concatLanes w f n) i = f i := by
  intro n
  induction n with
  | zero => intro i hi; omega
  | succ n ih =>
    intro i hi
    ext j hj
    rw [getElem_laneOf w _ i j hj]
    show (BitVec.cast _ (f n ++ concatLanes w f n)).getLsbD (w * i + j) = _
    rw [BitVec.getLsbD_cast, BitVec.getLsbD_append]
    rcases Nat.lt_or_ge i n with h | h
    · -- an earlier lane: it is entirely inside the low `w * n` bits
      have hlt : w * i + j < w * n := by
        have : w * (i + 1) ≤ w * n := Nat.mul_le_mul_left w (by omega)
        rw [Nat.mul_succ] at this; omega
      rw [if_pos hlt]
      rw [← getElem_laneOf w _ i j hj, ih i h]
    · -- the top lane: `i = n`, and the bit index lands in the appended `f n`
      have hi' : i = n := by omega
      subst hi'
      rw [if_neg (by omega), show w * i + j - w * i = j by omega,
        BitVec.getLsbD_eq_getElem hj]

/-! ## The lane views at the widths the backend uses -/

/-- The 256-bit word whose 8-bit lane `i` is `f i`. -/
def ofLanes8 (f : Nat → BitVec 8) : BitVec 256 := concatLanes 8 f 32
/-- The 256-bit word whose 16-bit lane `i` is `f i`. -/
def ofLanes16 (f : Nat → BitVec 16) : BitVec 256 := concatLanes 16 f 16
/-- The 256-bit word whose 32-bit lane `i` is `f i`. -/
def ofLanes32 (f : Nat → BitVec 32) : BitVec 256 := concatLanes 32 f 8
/-- The 256-bit word whose 64-bit lane `i` is `f i`. -/
def ofLanes64 (f : Nat → BitVec 64) : BitVec 256 := concatLanes 64 f 4
/-- The 256-bit word whose 128-bit half `i` is `f i`. -/
def ofLanes128 (f : Nat → BitVec 128) : BitVec 256 := concatLanes 128 f 2
/-- The 128-bit word whose 8-bit lane `i` is `f i`. -/
def ofLanes8' (f : Nat → BitVec 8) : BitVec 128 := concatLanes 8 f 16
/-- The 128-bit word whose 16-bit lane `i` is `f i`. -/
def ofLanes16' (f : Nat → BitVec 16) : BitVec 128 := concatLanes 16 f 8

@[simp] theorem laneOf_ofLanes8 (f : Nat → BitVec 8) {i : Nat} (h : i < 32) :
    laneOf 8 (ofLanes8 f) i = f i := laneOf_concatLanes 8 f 32 i h
@[simp] theorem laneOf_ofLanes16 (f : Nat → BitVec 16) {i : Nat} (h : i < 16) :
    laneOf 16 (ofLanes16 f) i = f i := laneOf_concatLanes 16 f 16 i h
@[simp] theorem laneOf_ofLanes32 (f : Nat → BitVec 32) {i : Nat} (h : i < 8) :
    laneOf 32 (ofLanes32 f) i = f i := laneOf_concatLanes 32 f 8 i h
@[simp] theorem laneOf_ofLanes64 (f : Nat → BitVec 64) {i : Nat} (h : i < 4) :
    laneOf 64 (ofLanes64 f) i = f i := laneOf_concatLanes 64 f 4 i h
@[simp] theorem laneOf_ofLanes128 (f : Nat → BitVec 128) {i : Nat} (h : i < 2) :
    laneOf 128 (ofLanes128 f) i = f i := laneOf_concatLanes 128 f 2 i h
@[simp] theorem laneOf_ofLanes8' (f : Nat → BitVec 8) {i : Nat} (h : i < 16) :
    laneOf 8 (ofLanes8' f) i = f i := laneOf_concatLanes 8 f 16 i h
@[simp] theorem laneOf_ofLanes16' (f : Nat → BitVec 16) {i : Nat} (h : i < 8) :
    laneOf 16 (ofLanes16' f) i = f i := laneOf_concatLanes 16 f 8 i h

/-! ## Lanes determine the word

This is the bridge the whole development rests on: a fact stated about every lane of a width is
a fact about the register, so a 16-bit-lane axiom and a 32-bit-lane axiom constrain the same
object.  Stated for an arbitrary factorisation `N = w * n` and then specialised. -/

theorem eq_of_laneOf_eq {N : Nat} (w n : Nat) (hN : N = w * n) {x y : BitVec N}
    (h : ∀ i < n, laneOf w x i = laneOf w y i) : x = y := by
  ext k hk
  have hw : 0 < w := by
    rcases Nat.eq_zero_or_pos w with rfl | hw
    · omega
    · exact hw
  have hkn : k / w < n := by
    apply Nat.div_lt_of_lt_mul; omega
  have hjw : k % w < w := Nat.mod_lt _ hw
  have hsplit : w * (k / w) + k % w = k := Nat.div_add_mod k w
  have := congrArg (fun z => z.getLsbD (k % w)) (h (k / w) hkn)
  simp only [getLsbD_laneOf, hjw, decide_true, Bool.true_and, hsplit] at this
  rw [← BitVec.getLsbD_eq_getElem, ← BitVec.getLsbD_eq_getElem]
  exact this

theorem eq_of_lane8_bv {x y : BitVec 256} (h : ∀ i < 32, laneOf 8 x i = laneOf 8 y i) : x = y :=
  eq_of_laneOf_eq 8 32 rfl h
theorem eq_of_lane16_bv {x y : BitVec 256} (h : ∀ i < 16, laneOf 16 x i = laneOf 16 y i) : x = y :=
  eq_of_laneOf_eq 16 16 rfl h
theorem eq_of_lane32_bv {x y : BitVec 256} (h : ∀ i < 8, laneOf 32 x i = laneOf 32 y i) : x = y :=
  eq_of_laneOf_eq 32 8 rfl h
theorem eq_of_lane64_bv {x y : BitVec 256} (h : ∀ i < 4, laneOf 64 x i = laneOf 64 y i) : x = y :=
  eq_of_laneOf_eq 64 4 rfl h
theorem eq_of_lane128_bv {x y : BitVec 256} (h : ∀ i < 2, laneOf 128 x i = laneOf 128 y i) :
    x = y := eq_of_laneOf_eq 128 2 rfl h
theorem eq_of_lane8'_bv {x y : BitVec 128} (h : ∀ i < 16, laneOf 8 x i = laneOf 8 y i) : x = y :=
  eq_of_laneOf_eq 8 16 rfl h
theorem eq_of_lane16'_bv {x y : BitVec 128} (h : ∀ i < 8, laneOf 16 x i = laneOf 16 y i) : x = y :=
  eq_of_laneOf_eq 16 8 rfl h

/-! ## …and hence determine the register

`bits_inj` says a `Vec256` is nothing but its 256 bits, so agreeing on every lane of any one
width is enough to be the same vector. -/

open RustKopisAvx2.backend.avx2.intrinsics in
theorem vec_eq_of_lane8 {a b : Vec256} (h : ∀ i < 32, lane8 a i = lane8 b i) : a = b :=
  bits_inj (eq_of_lane8_bv h)

open RustKopisAvx2.backend.avx2.intrinsics in
theorem vec_eq_of_lane16 {a b : Vec256} (h : ∀ i < 16, lane16 a i = lane16 b i) : a = b :=
  bits_inj (eq_of_lane16_bv h)

open RustKopisAvx2.backend.avx2.intrinsics in
theorem vec_eq_of_lane32 {a b : Vec256} (h : ∀ i < 8, lane32 a i = lane32 b i) : a = b :=
  bits_inj (eq_of_lane32_bv h)

open RustKopisAvx2.backend.avx2.intrinsics in
theorem vec_eq_of_lane64 {a b : Vec256} (h : ∀ i < 4, lane64 a i = lane64 b i) : a = b :=
  bits_inj (eq_of_lane64_bv h)

open RustKopisAvx2.backend.avx2.intrinsics in
theorem vec_eq_of_half {a b : Vec256} (h : ∀ i < 2, half a i = half b i) : a = b :=
  bits_inj (eq_of_lane128_bv h)

open RustKopisAvx2.backend.avx2.intrinsics in
theorem vec128_eq_of_lane8' {a b : Vec128} (h : ∀ i < 16, lane8' a i = lane8' b i) : a = b :=
  bits'_inj (eq_of_lane8'_bv h)

open RustKopisAvx2.backend.avx2.intrinsics in
theorem vec128_eq_of_lane16' {a b : Vec128} (h : ∀ i < 8, lane16' a i = lane16' b i) : a = b :=
  bits'_inj (eq_of_lane16'_bv h)

/-! ## Crossing widths

A 16-bit lane is two 8-bit lanes, a 32-bit lane is two 16-bit lanes, and so on.  These are what
the transpose and pack sequences need: `vpunpckldq` is stated on 32-bit lanes and its input came
from a 16-bit-lane fact. -/

theorem laneOf_split {n : Nat} (w : Nat) (x : BitVec n) (i : Nat) :
    laneOf (2 * w) x i =
      BitVec.cast (by omega) (laneOf w x (2 * i + 1) ++ laneOf w x (2 * i)) := by
  ext j hj
  rw [getElem_laneOf _ _ _ _ hj, BitVec.getElem_cast, BitVec.getElem_append]
  by_cases h : j < w
  · rw [dif_pos h, ← BitVec.getLsbD_eq_getElem, getLsbD_laneOf]
    simp only [h, decide_true, Bool.true_and]
    congr 1
    ring
  · rw [dif_neg h, ← BitVec.getLsbD_eq_getElem, getLsbD_laneOf]
    have hjw : j - w < w := by omega
    have hlin : w * (2 * i + 1) = 2 * w * i + w := by ring
    simp only [hjw, decide_true, Bool.true_and]
    congr 1
    omega

/-- A lane of a lane: the `i`th `w`-bit lane is lane `i % q` of the `(w·q)`-bit lane `i / q`.
This is what lets a fact about a 128-bit half be read off byte by byte — the shape every
`vbroadcasti128` argument arrives in. -/
theorem laneOf_laneOf {n : ℕ} (w q : ℕ) (x : BitVec n) (i : ℕ) (hq : 0 < q) :
    laneOf w x i = laneOf w (laneOf (w * q) x (i / q)) (i % q) := by
  ext j hj
  rw [getElem_laneOf _ _ _ _ hj, getElem_laneOf _ _ _ _ hj, getLsbD_laneOf]
  have hmod : i % q < q := Nat.mod_lt _ hq
  have hmul : w * (i % q + 1) ≤ w * q := Nat.mul_le_mul_left w (by omega)
  rw [Nat.mul_succ] at hmul
  have hlt : w * (i % q) + j < w * q := by omega
  simp only [hlt, decide_true, Bool.true_and]
  congr 1
  have hdm : q * (i / q) + i % q = i := Nat.div_add_mod i q
  calc w * i + j = w * (q * (i / q) + i % q) + j := by rw [hdm]
    _ = w * q * (i / q) + (w * (i % q) + j) := by ring

/-- Bitwise operations act lane by lane. -/
theorem laneOf_and {n : ℕ} (w : ℕ) (x y : BitVec n) (i : ℕ) :
    laneOf w (x &&& y) i = laneOf w x i &&& laneOf w y i := by
  ext j hj
  simp only [← BitVec.getLsbD_eq_getElem, BitVec.getLsbD_and, getLsbD_laneOf, hj, decide_true,
    Bool.true_and]

/-- The 16-bit lane `i` of a word, in terms of its bytes. -/
theorem lane16_eq_bytes {n : Nat} (x : BitVec n) (i : Nat) :
    laneOf 16 x i = laneOf 8 x (2 * i + 1) ++ laneOf 8 x (2 * i) :=
  laneOf_split 8 x i

/-- The 32-bit lane `i` of a word, in terms of its 16-bit lanes. -/
theorem lane32_eq_lane16 {n : Nat} (x : BitVec n) (i : Nat) :
    laneOf 32 x i = laneOf 16 x (2 * i + 1) ++ laneOf 16 x (2 * i) :=
  laneOf_split 16 x i

/-- The 64-bit lane `i` of a word, in terms of its 32-bit lanes. -/
theorem lane64_eq_lane32 {n : Nat} (x : BitVec n) (i : Nat) :
    laneOf 64 x i = laneOf 32 x (2 * i + 1) ++ laneOf 32 x (2 * i) :=
  laneOf_split 32 x i

/-- A 128-bit half, in terms of its 64-bit lanes. -/
theorem half_eq_lane64 {n : Nat} (x : BitVec n) (i : Nat) :
    laneOf 128 x i = laneOf 64 x (2 * i + 1) ++ laneOf 64 x (2 * i) :=
  laneOf_split 64 x i

end Kopis.Avx2
