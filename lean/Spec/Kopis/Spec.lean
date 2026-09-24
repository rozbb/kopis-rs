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

/-! ## Helper defs and theorems -/

abbrev 𝔹 := Vector Byte

/-- Interprets the given bitvector as a bytestring, where each group of 8 bits is a little-endian
representation of a byte. -/
def bitsToBytesLe {ℓ : Nat} (b : Vector Bool (8 * ℓ)) : 𝔹 ℓ :=
  Vector.ofFn fun ⟨i, _⟩ =>
    Fin.foldl 8 (fun (acc : Byte) (j : Fin 8) =>
      acc + b[8 * i + j.val].toNat * (2 ^ j.val)) 0

/-- Serilizes the given bytestring as a bitstring, where each byte is serialized little-endian -/
def bytesToBitsLe {ℓ : Nat} (B : 𝔹 ℓ) : Vector Bool (8 * ℓ) :=
  Vector.ofFn fun ⟨i, _⟩ => B[i / 8].toNat.testBit (i % 8)

/-- Extract `len` elements from `v` starting at offset `off`.
    Works uniformly for `𝔹 n` (byte vectors) and `Vector Bool n` (bit vectors). -/
def slice {n : ℕ} (v : Vector α n) (off len : ℕ) (h : off + len ≤ n := by grind) : Vector α len :=
  Vector.ofFn fun i => v[off + i]


/-- Bit index into a `256·n`-bit stream: `n·i + j < 8·(32·n)` for `i < 256`,
`j < n`. -/
private theorem serialize_idx_lt {n i j : Nat} (hi : i < 256) (hj : j < n) :
    n * i + j < 8 * (32 * n) := by
  calc n * i + j < n * i + n := by omega
    _ = n * (i + 1) := by ring
    _ ≤ n * 256 := Nat.mul_le_mul_left n (by omega)
    _ = 8 * (32 * n) := by ring

/-- Bit index into a `256·μ`-bit stream for CBD sampling:
`μ·k + μ/2 + j < 8·(32·μ)` for `k < 256`, `j < μ/2`. -/
private theorem gensec_idx_lt {μ k j : Nat} (hk : k < 256) (hj : j < μ / 2) :
    μ * k + μ / 2 + j < 8 * (32 * μ) := by
  calc μ * k + μ / 2 + j < μ * k + μ := by omega
    _ = μ * (k + 1) := by ring
    _ ≤ μ * 256 := Nat.mul_le_mul_left μ (by omega)
    _ = 8 * (32 * μ) := by ring

/-! ## Spec §"Mathematical Definitions" -/

/-- An element of `ℤ_m[X]/(X²⁵⁶ + 1)`, i.e. `Vector (ZMod m) 256`. Kopis uses
`m = 2ⁿ`. -/
abbrev Polynomial (m : ℕ) := Vector (ZMod m) 256

/-- `Rn` — the ring `R/2ⁿR` of ring elements with `n`-bit coefficients. -/
abbrev R (n : ℕ) := Polynomial (2 ^ n)

/-- The zero polynomial. -/
def Polynomial.zero (m : ℕ) : Polynomial m := Vector.replicate 256 0

/-- The constant polynomial `c` (all 256 coefficients equal to `c`); models the
spec's `make_rn([cuN; 256])`. -/
def Polynomial.const (m : ℕ) (c : ZMod m) : Polynomial m := Vector.replicate 256 c

/-- Polynomial addition -/
def Polynomial.add (f g : Polynomial m) : Polynomial m := Vector.zipWith (· + ·) f g

/-- Polynomial subtraction (spec says `uN` subtraction is wrapping, which this satisfies). -/
def Polynomial.sub (f g : Polynomial m) : Polynomial m := Vector.zipWith (· - ·) f g

instance {m} : Sub (Polynomial m) where sub := Polynomial.sub

/-- `Polynomial m` is an additive commutative monoid under pointwise addition. This makes
`Finset.sum` (`∑`) available for matrix products / inner products. -/
noncomputable instance polyAddCommMonoid {m} : AddCommMonoid (Polynomial m) where
  add := Polynomial.add
  zero := Polynomial.zero m
  nsmul := nsmulRec
  add_assoc a b c := by
    show Polynomial.add (Polynomial.add a b) c = Polynomial.add a (Polynomial.add b c)
    apply Vector.ext; intro p hp
    simp only [Polynomial.add, Vector.getElem_zipWith]; ring
  zero_add a := by
    show Polynomial.add (Polynomial.zero m) a = a
    apply Vector.ext; intro p hp
    simp only [Polynomial.add, Polynomial.zero, Vector.getElem_zipWith, Vector.getElem_replicate]
    ring
  add_zero a := by
    show Polynomial.add a (Polynomial.zero m) = a
    apply Vector.ext; intro p hp
    simp only [Polynomial.add, Polynomial.zero, Vector.getElem_zipWith, Vector.getElem_replicate]
    ring
  add_comm a b := by
    show Polynomial.add a b = Polynomial.add b a
    apply Vector.ext; intro p hp
    simp only [Polynomial.add, Vector.getElem_zipWith]; ring

/-- The `Add`-instance addition is definitionally the spec's `Polynomial.add`. -/
theorem Polynomial.add_def {m} (f g : Polynomial m) : f + g = Polynomial.add f g := rfl

/-- Schoolbook multiplication in `ℤ_m[X]/(X²⁵⁶ + 1)`. -/
def Polynomial.mul {m : ℕ} (a b : Polynomial m) : Polynomial m := Id.run do
  let mut c := Polynomial.zero m
  for hi : i in [0:256] do
    for hj : j in [0:256] do
      let k := (i + j) % 256
      have hk : k < 256 := Nat.mod_lt _ (by decide)
      if i + j < 256 then
        c := c.set k (c[k] + a[i] * b[j])
      else
        c := c.set k (c[k] - a[i] * b[j])
  pure c

instance {m} : Mul (Polynomial m) where mul := Polynomial.mul

/-- Coefficient-wise right shift on canonical representatives, denoted `r >> N` in the spec -/
def Polynomial.shiftRight (r : Polynomial m) (N : ℕ) : Polynomial m :=
  -- .val is in Fin m, so this is the canonical representative
  r.map (fun a => ((a.val >>> N : ℕ) : ZMod m))

/-- Coefficient-wise left shift on canonical representatives, reduced mod `2ⁿ`. This is denoted `r >> N` in the spec -/
def Polynomial.shiftLeft (r : Polynomial m) (N : ℕ) : Polynomial m :=
  r.map (fun a => ((a.val <<< N : ℕ) : ZMod m))

/-- Coercion, denoted `r as Rn'` in the spec. This the natural injection/projection between residue
rings. Reduces each canonical coefficient mod the new modulus `m'`. -/
def Polynomial.coerce (r : Polynomial m) (m' : ℕ) : Polynomial m' :=
  r.map (fun a => (a.val : ZMod m'))

/-- `VecRn` in the spec. We represent it with `PolyVector m ℓ`, i.e., a length-`ℓ` vector of ring
elements. -/
abbrev PolyVector (m ℓ : ℕ) := Vector (Polynomial m) ℓ

/-- `MatRn` in the spec. We represent it as an `ℓ × ℓ` matrix of ring elements. -/
abbrev PolyMatrix (m ℓ : ℕ) := Matrix (Fin ℓ) (Fin ℓ) (Polynomial m)

def PolyVector.zero (m ℓ : ℕ) : PolyVector m ℓ := Vector.replicate ℓ (Polynomial.zero m)

/-- Set polynomial `i` in `v: PolyVector` to `f` -/
def PolyVector.set {m ℓ : ℕ} (v : PolyVector m ℓ) (i : ℕ) (f : Polynomial m)
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

/-- Element-wise coercion -/
def PolyVector.coerce {m ℓ : ℕ} (v : PolyVector m ℓ) (m' : ℕ) : PolyVector m' ℓ :=
  v.map (·.coerce m')

def PolyMatrix.zero (m ℓ : ℕ) : PolyMatrix m ℓ := Matrix.of (fun _ _ => Polynomial.zero m)

/-- Set entry `(i, j)` in `M: PolyMatrix` to `val` -/
def PolyMatrix.update {m ℓ : ℕ} (M : PolyMatrix m ℓ) (i j : ℕ) (val : Polynomial m)
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
def innerProduct {m ℓ : ℕ} (v w : PolyVector m ℓ) : Polynomial m := Id.run do
  let mut a := Polynomial.zero m
  for hi : i in [0:ℓ] do
    a := a + v[i] * w[i]
  pure a

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
def serialize (n : ℕ) (r : Polynomial (2 ^ n)) : 𝔹 (32 * n) := Id.run do
  let mut b := Vector.replicate (8 * (32 * n)) false
  -- Serialize each coefficient
  for hi : i in [0:256] do
    let mut a := r[i].val
    -- Serialize each bit of each coefficient
    for hj : j in [0:n] do
      have := serialize_idx_lt (srrange_lt hi) (srrange_lt hj)
      b := b.set (n * i + j) (Bool.ofNat (a % 2))
      a := a / 2
  -- Convert the bitstring to a bytestring
  pure (bitsToBytesLe b)

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
def deserialize (n : ℕ) (B : 𝔹 (32 * n)) : Polynomial (2 ^ n) := Id.run do
  -- Serialize to bits
  let b := bytesToBitsLe B
  let mut F := Polynomial.zero (2 ^ n)
  for hi : i in [0:256] do
    -- Interpret each chunk of n bits as an integer mod 2^n
    F := F.set i (∑ j : Fin n, (b[n * i + j.val]'(serialize_idx_lt (srrange_lt hi) j.isLt)).toNat * 2 ^ j.val)
  pure F

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
def PolyVector.serialize {ℓ : ℕ} (n : ℕ) (v : PolyVector (2 ^ n) ℓ) : 𝔹 (ℓ * (32 * n)) :=
  (v.map (Kopis.serialize n)).flatten

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
def PolyVector.deserialize {ℓ : ℕ} (n : ℕ) (bytes : 𝔹 (32 * n * ℓ)) : PolyVector (2 ^ n) ℓ :=
  Vector.ofFn fun i =>
    Kopis.deserialize n (slice bytes (32 * n * i) (32 * n) (by
      have h : 32 * n * i.val + 32 * n ≤ 32 * n * ℓ := by
        calc 32 * n * i.val + 32 * n = 32 * n * (i.val + 1) := by ring
          _ ≤ 32 * n * ℓ := Nat.mul_le_mul_left _ i.isLt
      omega))

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

/-- Secret-key size (bytes): `SK_SIZE = 32`. -/
abbrev skSize : ℕ := 32

/-- Public-key size (bytes): `PK_SIZE = 256·ℓ·10/8 + 32 = 320·ℓ + 32`. -/
abbrev pkSize (p : ParameterSet) : ℕ := 320 * ℓ p + 32

/-- Ciphertext size (bytes): `CT_SIZE = 256·t/8 + 256·ℓ·10/8 = 32·t + 320·ℓ`. -/
abbrev ctSize (p : ParameterSet) : ℕ := 320 * ℓ p + 32 * t p

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
-/
def GenMat (ℓ : ℕ) (seed : 𝔹 32) : PolyMatrix (2 ^ 13) ℓ := Id.run do
  let mut A := PolyMatrix.zero (2 ^ 13) ℓ
  for hi : i in [0:ℓ] do
    for hj : j in [0:ℓ] do
      let buf := turboSHAKE128 (seed ‖ #v[(i : Byte)] ‖ #v[(j : Byte)]) DOMSEP_GENMAT (32 * 13)
      A := A.update i j (deserialize 13 buf)
  pure A

/-- From the spec
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
-/
def GenSecret (ℓ μ : ℕ) (seed : 𝔹 32) : PolyVector (2 ^ 13) ℓ := Id.run do
  let mut s := PolyVector.zero (2 ^ 13) ℓ
  for hi : i in [0:ℓ] do
    let buf := turboSHAKE256 (seed ‖ #v[(i : Byte)]) DOMSEP_GENSEC (32 * μ)
    let bits := bytesToBits buf
    let mut r := Polynomial.zero (2 ^ 13)
    for hk : k in [0:256] do
      -- vals[2k]   = bits[k·μ       .. k·μ + μ/2)
      -- vals[2k+1] = bits[k·μ + μ/2 .. k·μ + μ)
      let x : ℕ := ∑ j : Fin (μ / 2),
        (bits[μ * k + j.val]'(by
          have := gensec_idx_lt (srrange_lt hk) j.isLt; omega)).toNat
      let y : ℕ := ∑ j : Fin (μ / 2),
        (bits[μ * k + μ / 2 + j.val]'(gensec_idx_lt (srrange_lt hk) j.isLt)).toNat
      r := r.set k ((x : ZMod (2 ^ 13)) - (y : ZMod (2 ^ 13)))
    s := s.set i r
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
-/
def CompressToR10 (ℓ : ℕ) (v : PolyVector (2 ^ 13) ℓ) : PolyVector (2 ^ 10) ℓ :=
  let h : PolyVector (2 ^ 13) ℓ := Vector.replicate ℓ (Polynomial.const (2 ^ 13) 4)
  ((v + h).shiftRight 3).coerce (2 ^ 10)

/-- From the spec:
```
fn CompressToRt(r: R10) -> Rt:
  let h1 = make_r10([4u10; 256])
  let s = (r + h1) >> (10 - t)
  return (s as Rt)
```
-/
def CompressToRt (t : ℕ) (r : Polynomial (2 ^ 10)) : Polynomial (2 ^ t) :=
  let h := Polynomial.const (2 ^ 10) 4
  ((r + h).shiftRight (10 - t)).coerce (2 ^ t)

/-- From the spec:
```
fn DecodeMsg(r: R10) -> R1:
  let h2 = make_r10([2^8 - 2^(10-t-1) + 4; 256])
  let s = (r + h2) >> 9
  return (s as R1)
def DecodeMsg (t : ℕ) (r : Polynomial (2 ^ 10)) : Polynomial (2 ^ 1) :=
  let c : ZMod (2 ^ 10) := ((2 ^ 8 - 2 ^ (10 - t - 1) + 4 : ℕ) : ZMod (2 ^ 10))
  let h := Polynomial.const (2 ^ 10) c
  ((r + h).shiftRight 9).coerce (2 ^ 1)
```
-/
def DecodeMsg (t : ℕ) (r : Polynomial (2 ^ 10)) : Polynomial (2 ^ 1) :=
  let c : ZMod (2 ^ 10) := ((2 ^ 8 - 2 ^ (10 - t - 1) + 4 : ℕ) : ZMod (2 ^ 10))
  let h := Polynomial.const (2 ^ 10) c
  ((r + h).shiftRight 9).coerce (2 ^ 1)

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
    PolyVector (2 ^ 13) (ℓ p) × 𝔹 32 × 𝔹 (pkSize p) × 𝔹 32 :=
  let randomness := turboSHAKE256 (sk ‖ #v[(ℓ p : Byte)]) DOMSEP_KGEXPAND 96
  let mat_seed := slice randomness 0 32
  let secret_seed := slice randomness 32 32
  let z := slice randomness 64 32
  let mat_A := GenMat (ℓ p) mat_seed
  let vec_s := GenSecret (ℓ p) (μ p) secret_seed
  let vec_b := CompressToR10 (ℓ p) (matVecMul (Matrix.transpose mat_A) vec_s)
  let pk : 𝔹 (pkSize p) := (PolyVector.serialize 10 vec_b ‖ mat_seed).cast (by simp [pkSize]; ring)
  let pkh := turboSHAKE256 pk DOMSEP_PKHASH 32
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
-/
def PkeEncrypt (p : ParameterSet) (randomness : 𝔹 32) (pk : 𝔹 (pkSize p)) (msg : 𝔹 32) :
    𝔹 (ctSize p) :=
  let vec_b := PolyVector.deserialize (ℓ := ℓ p) 10 (slice pk 0 (32 * 10 * ℓ p) (by simp [pkSize]))
  let mat_seed := slice pk (32 * 10 * ℓ p) 32 (by simp [pkSize])
  let m := deserialize 1 msg
  let mat_A := GenMat (ℓ p) mat_seed
  let vec_sprime := GenSecret (ℓ p) (μ p) randomness
  let vec_bprime := CompressToR10 (ℓ p) (matVecMul mat_A vec_sprime)
  let vprime := innerProduct vec_b (vec_sprime.coerce (2 ^ 10))
  let cm := CompressToRt (t p) (vprime - ((m.coerce (2 ^ 10)).shiftLeft 9))
  (PolyVector.serialize 10 vec_bprime ‖ serialize (t p) cm).cast (by simp [ctSize]; ring)

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
-/
def PkeDecrypt (p : ParameterSet) (sk : 𝔹 32) (c : 𝔹 (ctSize p)) : 𝔹 32 :=
  let (vec_s, _, _, _) := ExpandSecretKey p sk
  let vec_bprime := PolyVector.deserialize (ℓ := ℓ p) 10 (slice c 0 (32 * 10 * ℓ p) (by simp [ctSize]))
  let cm := deserialize (t p) (slice c (32 * 10 * ℓ p) (32 * t p) (by simp [ctSize]))
  let v := innerProduct vec_bprime (vec_s.coerce (2 ^ 10))
  let cm10 := (cm.coerce (2 ^ 10)).shiftLeft (10 - t p)
  let mprime := DecodeMsg (t p) (v - cm10)
  serialize 1 mprime

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
  let pkh := turboSHAKE256 pk DOMSEP_PKHASH 32
  let b := turboSHAKE256 (randomness ‖ pkh) DOMSEP_FO 64
  let k := slice b 0 32
  let r := slice b 32 32
  let c := PkeEncrypt p r pk randomness
  (k, c)

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
def KemDecap (p : ParameterSet) (sk : 𝔹 32) (c : 𝔹 (ctSize p)) : 𝔹 32 :=
  let (_, z, pk, pkh) := ExpandSecretKey p sk
  let randomness := PkeDecrypt p sk c
  let b := turboSHAKE256 (randomness ‖ pkh) DOMSEP_FO 64
  let k := slice b 0 32
  let rprime := slice b 32 32
  let cprime := PkeEncrypt p rprime pk randomness
  if c = cprime then k
  else turboSHAKE256 (z ‖ c) DOMSEP_NOREJECT 32

end Spec.Kopis
