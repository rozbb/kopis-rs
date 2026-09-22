/-
  # Kopis/Avx2/Lanes.lean — the lane algebra at AVX2's widths.

  The generic part — `laneOf`, `concatLanes`, `eq_of_laneOf_eq`, `laneOf_split`, `laneOf_laneOf`,
  `laneOf_and` — is about `BitVec` and mentions no register width, so it lives in
  `Kopis/Bits/Lanes.lean` and is shared with the NEON stack; this file re-exports it under
  `Kopis.Avx2` so that every proof below `Kopis/Avx2/` sees one vocabulary.

  What is left here is what genuinely is AVX2's: the seven `ofLanes*` widths a 256-bit register
  (and the 128-bit halves the shuffles produce) decomposes into.

  There used to be a second half — `vec_eq_of_lane*`, turning "agrees on every lane" into "is
  the same register" through the `bits_inj` axiom in `Kopis/Avx2/Intrinsics.lean`.  Both are
  gone.  Nothing used them: a register is only ever observed through `bits`, so every goal that
  looked like it wanted them is really an equality of `BitVec`s, which `eq_of_laneOf_eq` below
  discharges with no assumption at all.  This file now mentions no extracted constant.
-/
import Kopis.Avx2.Intrinsics

namespace Kopis.Avx2

/-! ## The generic lane algebra, shared with the NEON backend

Re-exported rather than re-proved.  See `Kopis/Bits/Lanes.lean`. -/

export Kopis.Bits (concatLanes laneOf_concatLanes getLsbD_laneOf getElem_laneOf eq_of_laneOf_eq
  laneOf_split laneOf_laneOf laneOf_and laneOf_xor lane16_eq_bytes lane32_eq_lane16
  lane64_eq_lane32 half_eq_lane64)

open Kopis.Bits

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

theorem laneOf_ofLanes8 (f : Nat → BitVec 8) {i : Nat} (h : i < 32) :
    laneOf 8 (ofLanes8 f) i = f i := laneOf_concatLanes 8 f 32 i h
theorem laneOf_ofLanes16 (f : Nat → BitVec 16) {i : Nat} (h : i < 16) :
    laneOf 16 (ofLanes16 f) i = f i := laneOf_concatLanes 16 f 16 i h
theorem laneOf_ofLanes32 (f : Nat → BitVec 32) {i : Nat} (h : i < 8) :
    laneOf 32 (ofLanes32 f) i = f i := laneOf_concatLanes 32 f 8 i h
theorem laneOf_ofLanes64 (f : Nat → BitVec 64) {i : Nat} (h : i < 4) :
    laneOf 64 (ofLanes64 f) i = f i := laneOf_concatLanes 64 f 4 i h
theorem laneOf_ofLanes128 (f : Nat → BitVec 128) {i : Nat} (h : i < 2) :
    laneOf 128 (ofLanes128 f) i = f i := laneOf_concatLanes 128 f 2 i h

/-! ## Lanes determine the word

`eq_of_laneOf_eq` at the six factorisations of 256 and 128 that arise. -/

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
end Kopis.Avx2
