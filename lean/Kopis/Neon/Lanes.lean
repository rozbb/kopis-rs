/-
  # Kopis/Neon/Lanes.lean — the lane algebra at NEON's widths.

  The generic part — `laneOf`, `concatLanes`, `eq_of_laneOf_eq`, `laneOf_split`, `laneOf_laneOf`,
  `laneOf_and` — is about `BitVec` and mentions no register width, so it lives in
  `Kopis/Bits/Lanes.lean` and is shared with the AVX2 stack; this file re-exports it under
  `Kopis.Neon` so that every proof below `Kopis/Neon/` sees one vocabulary.

  What is left is what is NEON's: a register is 128 bits, so there are four widths rather than
  AVX2's seven and no 128-bit-half view at all — which is the whole reason the permute proofs
  here are shorter than their AVX2 counterparts.  `vec_eq_of_lane*` turn "agrees on every lane"
  into "is the same register", through `bits_inj`.
-/
import Kopis.Neon.Intrinsics

namespace Kopis.Neon

/-! ## The generic lane algebra, shared with the AVX2 backend

Re-exported rather than re-proved.  See `Kopis/Bits/Lanes.lean`. -/

export Kopis.Bits (concatLanes laneOf_concatLanes getLsbD_laneOf getElem_laneOf eq_of_laneOf_eq
  laneOf_split laneOf_laneOf laneOf_and laneOf_xor lane16_eq_bytes lane32_eq_lane16
  lane64_eq_lane32)

open Kopis.Bits

/-! ## The lane views at the widths the backend uses

One register, 128 bits, in four arrangements: `.16b`, `.8h`, `.4s`, `.2d`. -/

/-- The 128-bit word whose 8-bit lane `i` is `f i` — a `.16b` register. -/
def ofLanes8 (f : Nat → BitVec 8) : BitVec 128 := concatLanes 8 f 16
/-- The 128-bit word whose 16-bit lane `i` is `f i` — a `.8h` register. -/
def ofLanes16 (f : Nat → BitVec 16) : BitVec 128 := concatLanes 16 f 8
/-- The 128-bit word whose 32-bit lane `i` is `f i` — a `.4s` register. -/
def ofLanes32 (f : Nat → BitVec 32) : BitVec 128 := concatLanes 32 f 4
/-- The 128-bit word whose 64-bit lane `i` is `f i` — a `.2d` register. -/
def ofLanes64 (f : Nat → BitVec 64) : BitVec 128 := concatLanes 64 f 2

theorem laneOf_ofLanes8 (f : Nat → BitVec 8) {i : Nat} (h : i < 16) :
    laneOf 8 (ofLanes8 f) i = f i := laneOf_concatLanes 8 f 16 i h
theorem laneOf_ofLanes16 (f : Nat → BitVec 16) {i : Nat} (h : i < 8) :
    laneOf 16 (ofLanes16 f) i = f i := laneOf_concatLanes 16 f 8 i h
theorem laneOf_ofLanes32 (f : Nat → BitVec 32) {i : Nat} (h : i < 4) :
    laneOf 32 (ofLanes32 f) i = f i := laneOf_concatLanes 32 f 4 i h
theorem laneOf_ofLanes64 (f : Nat → BitVec 64) {i : Nat} (h : i < 2) :
    laneOf 64 (ofLanes64 f) i = f i := laneOf_concatLanes 64 f 2 i h

/-! ## Lanes determine the word -/

theorem eq_of_lane8_bv {x y : BitVec 128} (h : ∀ i < 16, laneOf 8 x i = laneOf 8 y i) : x = y :=
  eq_of_laneOf_eq 8 16 rfl h
theorem eq_of_lane16_bv {x y : BitVec 128} (h : ∀ i < 8, laneOf 16 x i = laneOf 16 y i) : x = y :=
  eq_of_laneOf_eq 16 8 rfl h
theorem eq_of_lane32_bv {x y : BitVec 128} (h : ∀ i < 4, laneOf 32 x i = laneOf 32 y i) : x = y :=
  eq_of_laneOf_eq 32 4 rfl h
theorem eq_of_lane64_bv {x y : BitVec 128} (h : ∀ i < 2, laneOf 64 x i = laneOf 64 y i) : x = y :=
  eq_of_laneOf_eq 64 2 rfl h

/-! ## …and hence determine the register

`bits_inj` says a `Vec128` is nothing but its 128 bits, so agreeing on every lane of any one
width is enough to be the same vector.  These are the only statements in the lane algebra that
mention an extracted constant. -/

open RustKopisNeon.backend.neon.intrinsics in
theorem vec_eq_of_lane8 {a b : Vec128} (h : ∀ i < 16, lane8 a i = lane8 b i) : a = b :=
  bits_inj (eq_of_lane8_bv h)

open RustKopisNeon.backend.neon.intrinsics in
theorem vec_eq_of_lane16 {a b : Vec128} (h : ∀ i < 8, lane16 a i = lane16 b i) : a = b :=
  bits_inj (eq_of_lane16_bv h)

open RustKopisNeon.backend.neon.intrinsics in
theorem vec_eq_of_lane32 {a b : Vec128} (h : ∀ i < 4, lane32 a i = lane32 b i) : a = b :=
  bits_inj (eq_of_lane32_bv h)

open RustKopisNeon.backend.neon.intrinsics in
theorem vec_eq_of_lane64 {a b : Vec128} (h : ∀ i < 2, lane64 a i = lane64 b i) : a = b :=
  bits_inj (eq_of_lane64_bv h)

end Kopis.Neon
