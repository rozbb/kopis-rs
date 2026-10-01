import Mathlib.Data.ZMod.Defs
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.LinearAlgebra.Matrix.RowCol
import Mathlib.Algebra.BigOperators.Fin
import Aeneas
import Spec.Defs
import Spec.TurboSHAKE.Spec

namespace Spec.Kopis

open Aeneas.Notations.SRRange
open scoped Spec.Notations
open Spec.Notations (srrange_lt)
open Spec.TurboSHAKE (turboSHAKE128 turboSHAKE256)

/-- The spec's argument order, `TurboSHAKE128(M, L, D)`. -/
local notation "TurboSHAKE128" M:max L:max D:max => turboSHAKE128 M D L
/-- The spec's argument order, `TurboSHAKE256(M, L, D)`. -/
local notation "TurboSHAKE256" M:max L:max D:max => turboSHAKE256 M D L

/-! ## Helper theorems -/

/-- The `i`-th length-`n` chunk of a `k·n`-element sequence is in bounds. -/
theorem chunk_bound {n k i : ℕ} (hi : i < k) : n * i + n ≤ n * k := by
  rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left n hi

/-! ## Spec §"Mathematical Definitions" -/

/-- An element of `ℤ_m[X]/(X²⁵⁶ + 1)`, represented by its 256 coefficients, lowest degree first.
Kopis uses `m = 2ⁿ`. `RingIso.lean` proves this is the quotient ring. -/
abbrev Poly (m : ℕ) := Vector (ZMod m) 256

/-- `Rn` — the ring `R/2ⁿR` of ring elements with `n`-bit coefficients. -/
abbrev R (n : ℕ) := Poly (2 ^ n)

/-- `make_rn`: the natural morphism from `[un; 256]` to `Rn`. We model `un` as `ZMod (2ⁿ)`, which
is exactly `n`-bit integers with wrapping arithmetic, so this is the identity. -/
def make_rn (n : ℕ) (coeffs : Vector (ZMod (2 ^ n)) 256) : R n := coeffs

/-- `canonical_coeffs(r)`: the canonical representatives in `[0, 2ⁿ)` of the coefficients of `r`. -/
def canonical_coeffs {n : ℕ} (r : R n) : Vector ℕ 256 := r.map (·.val)

/-- `to_bits_le(n, k)`: the `n` low bits of `k`, least significant first. -/
def to_bits_le (n k : ℕ) : Vector Bool n := Vector.ofFn fun i => k.testBit i

/-- `from_bits_le(n, bits)`: the integer whose `i`-th bit is `bits[i]`. -/
def from_bits_le (n : ℕ) (bits : Vector Bool n) : ℕ := ∑ i : Fin n, bits[i].toNat * 2 ^ i.val

/-- The zero polynomial. -/
def Poly.zero (m : ℕ) : Poly m := Vector.replicate 256 0

/-- Polynomial addition -/
def Poly.add (f g : Poly m) : Poly m := Vector.zipWith (· + ·) f g

/-- Polynomial subtraction (spec says `uN` subtraction is wrapping, which this satisfies). -/
def Poly.sub (f g : Poly m) : Poly m := Vector.zipWith (· - ·) f g

instance {m} : Sub (Poly m) where sub := Poly.sub

/-- `Poly m` is an additive commutative monoid under pointwise addition. This makes
`Finset.sum` (`∑`) available for matrix products / inner products. -/
noncomputable instance polyAddCommMonoid {m} : AddCommMonoid (Poly m) where
  add := Poly.add
  zero := Poly.zero m
  nsmul := nsmulRec
  add_assoc a b c := by
    show Poly.add (Poly.add a b) c = Poly.add a (Poly.add b c)
    apply Vector.ext; intro p hp
    simp only [Poly.add, Vector.getElem_zipWith]; ring
  zero_add a := by
    show Poly.add (Poly.zero m) a = a
    apply Vector.ext; intro p hp
    simp only [Poly.add, Poly.zero, Vector.getElem_zipWith, Vector.getElem_replicate]
    ring
  add_zero a := by
    show Poly.add a (Poly.zero m) = a
    apply Vector.ext; intro p hp
    simp only [Poly.add, Poly.zero, Vector.getElem_zipWith, Vector.getElem_replicate]
    ring
  add_comm a b := by
    show Poly.add a b = Poly.add b a
    apply Vector.ext; intro p hp
    simp only [Poly.add, Vector.getElem_zipWith]; ring

/-- The `Add`-instance addition is definitionally the spec's `Poly.add`. -/
theorem Poly.add_def {m} (f g : Poly m) : f + g = Poly.add f g := rfl

/-- Schoolbook multiplication in `ℤ_m[X]/(X²⁵⁶ + 1)`. -/
def Poly.mul {m : ℕ} (a b : Poly m) : Poly m := Id.run do
  let mut c := Poly.zero m
  for hi : i in [0:256] do
    for hj : j in [0:256] do
      let k := (i + j) % 256
      have hk : k < 256 := Nat.mod_lt _ (by decide)
      if i + j < 256 then
        c := c.set k (c[k] + a[i] * b[j])
      else
        c := c.set k (c[k] - a[i] * b[j])
  pure c

instance {m} : Mul (Poly m) where mul := Poly.mul

/-- Coefficient-wise right shift on canonical representatives, denoted `r >> N` in the spec -/
def Poly.shiftRight (r : Poly m) (N : ℕ) : Poly m :=
  -- .val is in Fin m, so this is the canonical representative
  r.map (fun a => ((a.val >>> N : ℕ) : ZMod m))

/-- Coefficient-wise left shift on canonical representatives, reduced mod `2ⁿ`. This is denoted
`r << N` in the spec -/
def Poly.shiftLeft (r : Poly m) (N : ℕ) : Poly m :=
  r.map (fun a => ((a.val <<< N : ℕ) : ZMod m))

instance {m} : HShiftRight (Poly m) ℕ (Poly m) where hShiftRight := Poly.shiftRight
instance {m} : HShiftLeft (Poly m) ℕ (Poly m) where hShiftLeft := Poly.shiftLeft

theorem Poly.shiftRight_def {m} (r : Poly m) (N : ℕ) : r >>> N = r.shiftRight N := rfl
theorem Poly.shiftLeft_def {m} (r : Poly m) (N : ℕ) : r <<< N = r.shiftLeft N := rfl

/-- Coercion, denoted `r as Rn'` in the spec. This the natural injection/projection between residue
rings. Reduces each canonical coefficient mod the new modulus `m'`. -/
def Poly.coerce (r : Poly m) (m' : ℕ) : Poly m' :=
  r.map (fun a => (a.val : ZMod m'))

/-- `VecRn` in the spec. We represent it with `PolyVector m ℓ`, i.e., a length-`ℓ` vector of ring
elements. -/
abbrev PolyVector (m ℓ : ℕ) := Vector (Poly m) ℓ

/-- `MatRn` in the spec. We represent it as an `ℓ × ℓ` matrix of ring elements. -/
abbrev PolyMatrix (m ℓ : ℕ) := Matrix (Fin ℓ) (Fin ℓ) (Poly m)

/-- `VecRn`, for dimension `ℓ`. -/
abbrev VecR (n ℓ : ℕ) := PolyVector (2 ^ n) ℓ

/-- `MatRn`, for dimension `ℓ`. -/
abbrev MatR (n ℓ : ℕ) := PolyMatrix (2 ^ n) ℓ

def PolyVector.zero (m ℓ : ℕ) : PolyVector m ℓ := Vector.replicate ℓ (Poly.zero m)

/-- Set polynomial `i` in `v: PolyVector` to `f` -/
def PolyVector.set {m ℓ : ℕ} (v : PolyVector m ℓ) (i : ℕ) (f : Poly m)
    (_ : i < ℓ := by get_elem_tactic) : PolyVector m ℓ := Vector.set v i f

/-- Element-wise vector addition. -/
instance {m ℓ : ℕ} : Add (PolyVector m ℓ) where
  add v w := Vector.ofFn fun i => v[i] + w[i]

/-- Element-wise vector subtraction. -/
instance {m ℓ : ℕ} : Sub (PolyVector m ℓ) where
  sub v w := Vector.ofFn fun i => v[i] - w[i]

/-- Element-wise right-shift -/
def PolyVector.shiftRight {m ℓ : ℕ} (v : PolyVector m ℓ) (N : ℕ) : PolyVector m ℓ :=
  v.map (·.shiftRight N)

instance {m ℓ} : HShiftRight (PolyVector m ℓ) ℕ (PolyVector m ℓ) where
  hShiftRight := PolyVector.shiftRight

theorem PolyVector.shiftRight_def {m ℓ} (v : PolyVector m ℓ) (N : ℕ) :
    v >>> N = v.shiftRight N := rfl

/-- Element-wise coercion -/
def PolyVector.coerce {m ℓ : ℕ} (v : PolyVector m ℓ) (m' : ℕ) : PolyVector m' ℓ :=
  v.map (·.coerce m')

def PolyMatrix.zero (m ℓ : ℕ) : PolyMatrix m ℓ := Matrix.of (fun _ _ => Poly.zero m)

/-- Set entry `(i, j)` in `M: PolyMatrix` to `val` -/
def PolyMatrix.update {m ℓ : ℕ} (M : PolyMatrix m ℓ) (i j : ℕ) (val : Poly m)
    (hi : i < ℓ := by get_elem_tactic) (_ : j < ℓ := by get_elem_tactic) : PolyMatrix m ℓ :=
  Matrix.updateRow M ⟨i, hi⟩ (fun col => if col = j then val else M ⟨i, hi⟩ col)

/-- Matrix–vector product `A · v` -/
def matVecMul {m ℓ : ℕ} (A : PolyMatrix m ℓ) (v : PolyVector m ℓ) : PolyVector m ℓ := Id.run do
  let mut w := PolyVector.zero m ℓ
  for hi : i in [0:ℓ] do
    for hj : j in [0:ℓ] do
      w := w.set i (w[i] + A ⟨i, by grind⟩ ⟨j, by grind⟩ * v[j])
  pure w

/-- Inner product of two vectors of ring elements, `transpose(v) * w = Σᵢ vᵢ·wᵢ`. -/
def innerProduct {m ℓ : ℕ} (v w : PolyVector m ℓ) : Poly m := Id.run do
  let mut a := Poly.zero m
  for hi : i in [0:ℓ] do
    a := a + v[i] * w[i]
  pure a

instance {m ℓ} : HMul (PolyMatrix m ℓ) (PolyVector m ℓ) (PolyVector m ℓ) where hMul := matVecMul

theorem PolyMatrix.mul_def {m ℓ} (A : PolyMatrix m ℓ) (v : PolyVector m ℓ) :
    A * v = matVecMul A v := rfl

/-- `transpose(v)` for a column vector `v`. It exists only to be multiplied by another vector. -/
structure PolyRowVector (m ℓ : ℕ) where
  col : PolyVector m ℓ

/-- `transpose` of a vector. -/
def PolyVector.transpose {m ℓ : ℕ} (v : PolyVector m ℓ) : PolyRowVector m ℓ := ⟨v⟩

-- `transpose` applies to both matrices and vectors, as in the spec
export Matrix (transpose)
export PolyVector (transpose)

instance {m ℓ} : HMul (PolyRowVector m ℓ) (PolyVector m ℓ) (Poly m) where
  hMul v w := innerProduct v.col w

theorem PolyVector.transpose_mul {m ℓ} (v w : PolyVector m ℓ) :
    transpose v * w = innerProduct v w := rfl

/-! ## Serialization (§"Auxiliary Functions") -/

/-- From the spec:
```
# Serializes an element of Rn (for any choice n=13,10,1,t)
fn serialize_elem(n: ℤ, r: Rn) -> [u8; n*256/8]:
  let a = canonical_coeffs(r)

  let all_bits: [bool; n*256]
  for i in 0..256:
    all_bits[n*i..n*(i+1)] = to_bits_le(n, a[i])

  let out: [u8; 32*n]
  for i in 0..32*n:
    out[i] = from_bits_le(8, all_bits[8*i..8*(i+1)])
  return out
```
-/
def serialize_elem (n : ℕ) (r : R n) : 𝔹 (32 * n) :=
  let a := canonical_coeffs r
  let all_bits : Vector Bool (256 * n) := (Vector.ofFn fun i : Fin 256 => to_bits_le n a[i]).flatten
  Vector.ofFn fun i : Fin (32 * n) =>
    (from_bits_le 8 (slice all_bits (8 * i) 8 (by have := i.isLt; omega)) : Byte)

/-- From the spec:
```
# Deserializes an element of Rn (for any choice n=13,10,1,t)
fn deserialize_elem(n: ℤ, bytes: [u8; n*256/8]) -> Rn:
  let all_bits: [bool; n*256]
  for i in 0..n*32:
    all_bits[8*i..8*(i+1)] = to_bits_le(8, bytes[i])

  let coeffs: [un; 256]
  for i in 0..256:
    coeffs[i] = from_bits_le(n, all_bits[n*i..n*(i+1)])
  return make_rn(coeffs)
```
-/
def deserialize_elem (n : ℕ) (bytes : 𝔹 (32 * n)) : R n :=
  let all_bits : Vector Bool (32 * n * 8) :=
    (Vector.ofFn fun i : Fin (32 * n) => to_bits_le 8 bytes[i].toNat).flatten
  let coeffs : Vector (ZMod (2 ^ n)) 256 := Vector.ofFn fun i : Fin 256 =>
    from_bits_le n (slice all_bits (n * i) n (by have := chunk_bound (n := n) i.isLt; omega))
  make_rn n coeffs

/-- From the spec:
```
# Serializes an element of VecRn (for any choice n=13,10,1,t)
fn serialize_vec(n: ℤ, v: VecRn) -> [u8; ℓ*n*256/8]:
  let out: [u8; ℓ*n*32]
  for i in 0..ℓ:
    out[n*32*i..n*32*(i+1)] = serialize_elem(n, v[i])
  return out
```
-/
def serialize_vec {ℓ : ℕ} (n : ℕ) (v : VecR n ℓ) : 𝔹 (ℓ * (32 * n)) :=
  (v.map (serialize_elem n)).flatten

/-- From the spec:
```
# Deserializes an element of VecRn (for any choice n=13,10,1,t)
fn deserialize_vec(n: ℤ, bytes: [u8; ℓ*n*256/8]) -> VecRn:
  let elems: [Rn; ℓ]
  for i in 0..ℓ:
    elems[i] = deserialize_elem(n, bytes[n*32*i..n*32*(i+1)])
  return make_vecn(elems)
```
-/
def deserialize_vec {ℓ : ℕ} (n : ℕ) (bytes : 𝔹 (32 * n * ℓ)) : VecR n ℓ :=
  Vector.ofFn fun i =>
    deserialize_elem n (slice bytes (32 * n * i) (32 * n) (chunk_bound i.isLt))

/-- The byte lengths above agree with the spec's: `32·n = n·256/8`, and both vector lengths are
`ℓ·n·256/8`. -/
theorem serialize_lengths (n ℓ : ℕ) :
    32 * n = n * 256 / 8 ∧ ℓ * (32 * n) = ℓ * n * 256 / 8 ∧ 32 * n * ℓ = ℓ * n * 256 / 8 := by
  rw [show ℓ * n * 256 = ℓ * (32 * n) * 8 by ring, Nat.mul_div_cancel _ (by decide)]
  exact ⟨by omega, rfl, by ring⟩

/-! ## Parameters (spec §"Parameters", §"Constants", §"Parameter Sets") -/

/-- The three Kopis security levels. -/
inductive ParameterSet where
  | Kopis_512
  | Kopis_768
  | Kopis_1024

/-- `ℓ` — the public matrix dimension (2 / 3 / 4). -/
@[reducible] def ℓ : ParameterSet → ℕ
  | .Kopis_512  => 2
  | .Kopis_768  => 3
  | .Kopis_1024 => 4

/-- `t` — the base-2 logarithm of the compressed-element modulus (3 / 4 / 6). -/
@[reducible] def t : ParameterSet → ℕ
  | .Kopis_512  => 3
  | .Kopis_768  => 4
  | .Kopis_1024 => 6

/-- `μ` — the binomial parameter for secret generation (10 / 8 / 6). -/
@[reducible] def μ : ParameterSet → ℕ
  | .Kopis_512  => 10
  | .Kopis_768  => 8
  | .Kopis_1024 => 6

/-- "`μ` ... is always even." -/
theorem μ_even (p : ParameterSet) : 2 ∣ μ p := by cases p <;> decide

/-- Secret-key size (bytes): `SK_SIZE = 32`. -/
abbrev skSize : ℕ := 32

/-- Public-key size (bytes): `PK_SIZE = 256·ℓ·10/8 + 32 = 320·ℓ + 32`. -/
abbrev pkSize (p : ParameterSet) : ℕ := 320 * ℓ p + 32

/-- Ciphertext size (bytes): `CT_SIZE = 256·t/8 + 256·ℓ·10/8 = 32·t + 320·ℓ`. -/
abbrev ctSize (p : ParameterSet) : ℕ := 320 * ℓ p + 32 * t p

theorem pkSize_eq (p : ParameterSet) : pkSize p = 256 * ℓ p * 10 / 8 + 32 := by unfold pkSize; omega
theorem ctSize_eq (p : ParameterSet) : ctSize p = 256 * t p / 8 + 256 * ℓ p * 10 / 8 := by
  unfold ctSize; omega

/-! ### Parameter table (spec §"Parameter Sets") -/

example : (ℓ .Kopis_512, t .Kopis_512, μ .Kopis_512) = (2, 3, 10) := rfl
example : (ℓ .Kopis_768, t .Kopis_768, μ .Kopis_768) = (3, 4, 8) := rfl
example : (ℓ .Kopis_1024, t .Kopis_1024, μ .Kopis_1024) = (4, 6, 6) := rfl
example : (pkSize .Kopis_512, ctSize .Kopis_512, skSize) = (672, 736, 32) := rfl
example : (pkSize .Kopis_768, ctSize .Kopis_768, skSize) = (992, 1088, 32) := rfl
example : (pkSize .Kopis_1024, ctSize .Kopis_1024, skSize) = (1312, 1472, 32) := rfl

/-! ### Domain separators (spec §"Constants") -/

def DOMSEP_KGEXPAND : Byte := 0x01
def DOMSEP_GENMAT   : Byte := 0x02
def DOMSEP_GENSEC   : Byte := 0x03
def DOMSEP_PKHASH   : Byte := 0x04
def DOMSEP_FO       : Byte := 0x05
def DOMSEP_NOREJECT : Byte := 0x06

/-! ## Sampling (spec §"Auxiliary Functions") -/

/-- From the spec:
```
fn GenMat(seed: [u8; 32]) -> MatR13:
  let A: [[R13; ℓ]; ℓ]
  for i in 0u8..ℓ:
    for j in 0u8..ℓ:
      let buf = TurboSHAKE128(seed || i || j, 256*13/8, DOMSEP_GENMAT)
      A[i][j] = deserialize_elem(13, buf)
  return make_mat13(A)
```
This takes `ℓ` rather than a `ParameterSet` so that proofs can instantiate it with the Rust const
generic. The spec only ever passes `ℓ p`. -/
def GenMat (ℓ : ℕ) (seed : 𝔹 32) : MatR 13 ℓ := Id.run do
  let mut A := PolyMatrix.zero (2 ^ 13) ℓ
  for hi : i in [0:ℓ] do
    for hj : j in [0:ℓ] do
      let buf := TurboSHAKE128 (seed ‖ #v[(i : Byte)] ‖ #v[(j : Byte)]) (32 * 13) DOMSEP_GENMAT
      A := A.update i j (deserialize_elem 13 buf)
  pure A

/-- From the spec:
```
# Reinterprets a bytestring as a sequence of bitstrings of length μ/2
fn bit_slices(bytes: [u8; μ*256/8]) -> [[bool; μ/2]; 512]:
  let all_bits: [bool; μ*256]
  for i in 0..μ*32:
    all_bits[8*i..8*(i+1)] = to_bits_le(8, bytes[i])

  let out: [[bool; μ/2]; 512]
  for i in 0..512:
    out[i] = all_bits[i*μ/2..(i+1)*μ/2]
  return out
```
-/
def bit_slices (μ : ℕ) (bytes : 𝔹 (32 * μ)) : Vector (Vector Bool (μ / 2)) 512 :=
  let all_bits : Vector Bool (32 * μ * 8) :=
    (Vector.ofFn fun i : Fin (32 * μ) => to_bits_le 8 bytes[i].toNat).flatten
  Vector.ofFn fun i : Fin 512 => slice all_bits (i * μ / 2) (μ / 2) (by
    have := Nat.mul_le_mul_right μ (Nat.succ_le_of_lt i.isLt); rw [Nat.succ_mul] at this; omega)

/-- From the spec:
```
# Returns the number of set bits in b
fn hamming(b: [bool; μ/2]) -> u13:
  let mut weight = 0u13
  for i in 0..μ/2:
    if b[i]:
      weight += 1
  return weight
```
-/
def hamming {k : ℕ} (b : Vector Bool k) : ℕ := ∑ i : Fin k, b[i].toNat

/-- From the spec:
```
fn GenSecret(seed: [u8; 32]) -> VecR13:
  let s: [R13; ℓ]
  for i in 0u8..ℓ:
    let buf = TurboSHAKE256(seed || i, μ*256/8, DOMSEP_GENSEC)
    let vals = bit_slices(buf)
    let r: [u13; 256]
    for k in 0..256:
      # Recall subtraction is wrapping
      r[k] = hamming(vals[2*k]) - hamming(vals[2*k+1])
    s[i] = make_r13(r)
  return make_vec13(s)
```
This takes `ℓ` and `μ` rather than a `ParameterSet` so that proofs can instantiate them with the
Rust const generics. The spec only ever passes `ℓ p` and `μ p`. -/
def GenSecret (ℓ μ : ℕ) (seed : 𝔹 32) : VecR 13 ℓ := Id.run do
  let mut s := PolyVector.zero (2 ^ 13) ℓ
  for hi : i in [0:ℓ] do
    let buf := TurboSHAKE256 (seed ‖ #v[(i : Byte)]) (32 * μ) DOMSEP_GENSEC
    let vals := bit_slices μ buf
    let mut r : Vector (ZMod (2 ^ 13)) 256 := Vector.replicate 256 0
    for hk : k in [0:256] do
      -- Recall subtraction is wrapping
      r := r.set k ((hamming vals[2 * k] : ZMod (2 ^ 13)) - hamming vals[2 * k + 1])
    s := s.set i (make_rn 13 r)
  pure s

/-! ## Compression and message decoding (spec §"Auxiliary Functions") -/

/-- From the spec:
```
fn CompressToR10(v: VecR13) -> VecR10:
  let h1 = make_r13([4u13; 256])
  let h = make_vec13([h1; ℓ])
  let s = (v + h) >> 3
  return (s as VecR10)
```
This takes `ℓ` rather than a `ParameterSet`; see `GenMat`. -/
def CompressToR10 (ℓ : ℕ) (v : VecR 13 ℓ) : VecR 10 ℓ :=
  let h1 := make_rn 13 (Vector.replicate 256 4)
  let h : VecR 13 ℓ := Vector.replicate ℓ h1
  let s := (v + h) >>> 3
  s.coerce (2 ^ 10)

/-- From the spec:
```
fn CompressToRt(r: R10) -> Rt:
  let h1 = make_r10([4u10; 256])
  let s = (r + h1) >> (10 - t)
  return (s as Rt)
```
-/
def CompressToRt (t : ℕ) (r : R 10) : R t :=
  let h1 := make_rn 10 (Vector.replicate 256 4)
  let s := (r + h1) >>> (10 - t)
  s.coerce (2 ^ t)

/-- From the spec:
```
fn DecodeMsg(r: R10) -> R1:
  let h2 = make_r10([2^8 - 2^(10-t-1) + 4; 256])
  let s = (r + h2) >> 9
  return (s as R1)
```
-/
def DecodeMsg (t : ℕ) (r : R 10) : R 1 :=
  let h2 := make_rn 10 (Vector.replicate 256 ((2 ^ 8 - 2 ^ (10 - t - 1) + 4 : ℕ) : ZMod (2 ^ 10)))
  let s := (r + h2) >>> 9
  s.coerce (2 ^ 1)

/-- `DecodeMsg`'s constant is computed in `ℕ`, where subtraction truncates. That is only a
problem when `t = 0` or `t > 9`, which no parameter set does. -/
theorem DecodeMsg_const_eq (p : ParameterSet) :
    ((2 ^ 8 - 2 ^ (10 - t p - 1) + 4 : ℕ) : ℤ) = 2 ^ 8 - 2 ^ (10 - t p - 1) + 4 := by
  cases p <;> decide

/-! ## Key expansion (spec §"Auxiliary Functions") -/

/-- From the spec:
```
fn ExpandSecretKey(
  sk: [u8; 32]
) -> (VecR13, [u8; 32], [u8; PK_SIZE], [u8; 32]):
  let randomness = TurboSHAKE256(sk || (ℓ as u8), 96, DOMSEP_KGEXPAND)
  let mat_seed = randomness[..32]
  let secret_seed = randomness[32..64]
  let z = randomness[64..]

  let mat_A = GenMat(mat_seed)
  let vec_s = GenSecret(secret_seed)
  let vec_b = CompressToR10(transpose(mat_A) * vec_s)
  let pk = serialize_vec(10, vec_b) || mat_seed
  let pkh = TurboSHAKE256(pk, 32, DOMSEP_PKHASH)

  return (vec_s, z, pk, pkh)
```
-/
def ExpandSecretKey (p : ParameterSet) (sk : 𝔹 32) :
    VecR 13 (ℓ p) × 𝔹 32 × 𝔹 (pkSize p) × 𝔹 32 :=
  let randomness := TurboSHAKE256 (sk ‖ #v[(ℓ p : Byte)]) 96 DOMSEP_KGEXPAND
  let mat_seed := slice randomness 0 32
  let secret_seed := slice randomness 32 32
  let z := slice randomness 64 32
  let mat_A := GenMat (ℓ p) mat_seed
  let vec_s := GenSecret (ℓ p) (μ p) secret_seed
  let vec_b := CompressToR10 (ℓ p) (transpose mat_A * vec_s)
  let pk : 𝔹 (pkSize p) := (serialize_vec 10 vec_b ‖ mat_seed).cast (by simp [pkSize]; ring)
  let pkh := TurboSHAKE256 pk 32 DOMSEP_PKHASH
  (vec_s, z, pk, pkh)

/-! ## Public-key encryption (spec §"PKE") -/

/-- From the spec:
```
fn SkToPk(sk: [u8; 32]) -> [u8; PK_SIZE]:
  let (_, _, pk, _) = ExpandSecretKey(sk)
  return pk
```
-/
def SkToPk (p : ParameterSet) (sk : 𝔹 32) : 𝔹 (pkSize p) :=
  let (_, _, pk, _) := ExpandSecretKey p sk
  pk

/-- From the spec:
```
fn PkeEncrypt(
  randomness: [u8; 32],
  pk: [u8; PK_SIZE],
  msg: [u8; 32]
) -> [u8; CT_SIZE]:
  let vec_b = deserialize_vec(10, pk[..256*ℓ*10/8])
  let mat_seed = pk[256*ℓ*10/8..]
  let m = deserialize_elem(1, msg)

  let mat_A = GenMat(mat_seed)
  let vec_sprime = GenSecret(randomness)
  let vec_bprime = CompressToR10(mat_A * vec_sprime)
  let vprime = transpose(vec_b) * (vec_sprime as VecR10)
  let cm = CompressToRt(vprime - ((m as R10) << 9))

  let ct = serialize_vec(10, vec_bprime) || serialize_elem(t, cm)
  return ct
```
Here `256*ℓ*10/8` is written `32*10*ℓ`. -/
def PkeEncrypt (p : ParameterSet) (randomness : 𝔹 32) (pk : 𝔹 (pkSize p)) (msg : 𝔹 32) :
    𝔹 (ctSize p) :=
  let vec_b := deserialize_vec (ℓ := ℓ p) 10 (slice pk 0 (32 * 10 * ℓ p) (by simp [pkSize]))
  let mat_seed := slice pk (32 * 10 * ℓ p) 32 (by simp [pkSize])
  let m := deserialize_elem 1 msg
  let mat_A := GenMat (ℓ p) mat_seed
  let vec_sprime := GenSecret (ℓ p) (μ p) randomness
  let vec_bprime := CompressToR10 (ℓ p) (mat_A * vec_sprime)
  let vprime := transpose vec_b * vec_sprime.coerce (2 ^ 10)
  let cm := CompressToRt (t p) (vprime - (m.coerce (2 ^ 10) <<< 9))
  let ct := serialize_vec 10 vec_bprime ‖ serialize_elem (t p) cm
  ct.cast (by simp [ctSize]; ring)

/-- From the spec:
```
fn PkeDecrypt(sk: [u8; 32], ct: [u8; CT_SIZE]) -> [u8; 32]:
  let (vec_s, ...) = ExpandSecretKey(sk)
  let vec_bprime = deserialize_vec(10, ct[..256*ℓ*10/8])
  let cm = deserialize_elem(t, ct[256*ℓ*10/8..])
  let v = transpose(vec_bprime) * (vec_s as VecR10)
  let cm10 = (cm as R10) << (10 - t)
  let mprime = DecodeMsg(v - cm10)
  return serialize_elem(1, mprime)
```
Here `256*ℓ*10/8` is written `32*10*ℓ`. -/
def PkeDecrypt (p : ParameterSet) (sk : 𝔹 32) (ct : 𝔹 (ctSize p)) : 𝔹 32 :=
  let (vec_s, _, _, _) := ExpandSecretKey p sk
  let vec_bprime := deserialize_vec (ℓ := ℓ p) 10 (slice ct 0 (32 * 10 * ℓ p) (by simp [ctSize]))
  let cm := deserialize_elem (t p) (slice ct (32 * 10 * ℓ p) (32 * t p) (by simp [ctSize]))
  let v := transpose vec_bprime * vec_s.coerce (2 ^ 10)
  let cm10 := cm.coerce (2 ^ 10) <<< (10 - t p)
  let mprime := DecodeMsg (t p) (v - cm10)
  serialize_elem 1 mprime

/-! ## Key encapsulation (spec §"KEM") -/

/-- From the spec:
```
fn KemEncap(
  randomness: [u8; 32],
  pk: [u8; PK_SIZE]
) -> ([u8; 32], [u8; CT_SIZE]):
  # Derive the output key and encryption randomness
  let pkh = TurboSHAKE256(pk, 32, DOMSEP_PKHASH)
  let b = TurboSHAKE256(randomness || pkh, 64, DOMSEP_FO)
  let (k, r) = (b[..32], b[32..])

  # Encrypt to pk. `randomness` is itself the message
  let ct = PkeEncrypt(r, pk, randomness)

  return (k, ct)
```
-/
def KemEncap (p : ParameterSet) (randomness : 𝔹 32) (pk : 𝔹 (pkSize p)) :
    𝔹 32 × 𝔹 (ctSize p) :=
  let pkh := TurboSHAKE256 pk 32 DOMSEP_PKHASH
  let b := TurboSHAKE256 (randomness ‖ pkh) 64 DOMSEP_FO
  let k := slice b 0 32
  let r := slice b 32 32
  let ct := PkeEncrypt p r pk randomness
  (k, ct)

/-- From the spec:
```
fn KemDecap(sk: [u8; 32], ct: [u8; CT_SIZE]) -> [u8; 32]:
  let (_, z, pk, pkh) = ExpandSecretKey(sk)

  let randomness = PkeDecrypt(sk, ct)
  let b = TurboSHAKE256(randomness || pkh, 64, DOMSEP_FO)
  let (k, rprime) = (b[..32], b[32..])
  let cprime = PkeEncrypt(rprime, pk, randomness)

  if ct == cprime:
    return k
  else:
    return TurboSHAKE256(z || ct, 32, DOMSEP_NOREJECT)
```
-/
def KemDecap (p : ParameterSet) (sk : 𝔹 32) (ct : 𝔹 (ctSize p)) : 𝔹 32 :=
  let (_, z, pk, pkh) := ExpandSecretKey p sk
  let randomness := PkeDecrypt p sk ct
  let b := TurboSHAKE256 (randomness ‖ pkh) 64 DOMSEP_FO
  let k := slice b 0 32
  let rprime := slice b 32 32
  let cprime := PkeEncrypt p rprime pk randomness
  if ct = cprime then k
  else TurboSHAKE256 (z ‖ ct) 32 DOMSEP_NOREJECT

end Spec.Kopis
