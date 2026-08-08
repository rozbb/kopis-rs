/-
  # Kopis/Avx2/Lanes.lean — the lane algebra at AVX2's widths.

  The generic part — `laneOf`, `concatLanes`, `eq_of_laneOf_eq`, `laneOf_split`, `laneOf_laneOf`,
  `laneOf_and` — is about `BitVec` and mentions no register width, so it lives in
  `Kopis/Bits/Lanes.lean` and is shared with the NEON stack; this file re-exports it under
  `Kopis.Avx2` so that every proof below `Kopis/Avx2/` sees one vocabulary.

  What is left here is what genuinely is AVX2's: the seven `ofLanes*` widths a 256-bit register
  (and the 128-bit halves the shuffles produce) decomposes into, and the `bits_inj` corollaries
  that turn "agrees on every lane" into "is the same register".
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
/-- The 128-bit word whose 16-bit lane `i` is `f i`. -/
def ofLanes16' (f : Nat → BitVec 16) : BitVec 128 := concatLanes 16 f 8

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
theorem laneOf_ofLanes8' (f : Nat → BitVec 8) {i : Nat} (h : i < 16) :
    laneOf 8 (ofLanes8' f) i = f i := laneOf_concatLanes 8 f 16 i h
theorem laneOf_ofLanes16' (f : Nat → BitVec 16) {i : Nat} (h : i < 8) :
    laneOf 16 (ofLanes16' f) i = f i := laneOf_concatLanes 16 f 8 i h

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
theorem eq_of_lane8'_bv {x y : BitVec 128} (h : ∀ i < 16, laneOf 8 x i = laneOf 8 y i) : x = y :=
  eq_of_laneOf_eq 8 16 rfl h
theorem eq_of_lane16'_bv {x y : BitVec 128} (h : ∀ i < 8, laneOf 16 x i = laneOf 16 y i) : x = y :=
  eq_of_laneOf_eq 16 8 rfl h

/-! ## …and hence determine the register

`bits_inj` says a `Vec256` is nothing but its 256 bits, so agreeing on every lane of any one
width is enough to be the same vector.  These are the only statements in the lane algebra that
mention an extracted constant. -/

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

end Kopis.Avx2
