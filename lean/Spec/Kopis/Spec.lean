import Mathlib.Data.ZMod.Defs
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.LinearAlgebra.Matrix.RowCol
import Mathlib.Algebra.BigOperators.Fin
import Aeneas
import Spec.Defs
import Spec.TurboSHAKE.Spec

/-!
# Kopis (a Module-LWR Key-Encapsulation Mechanism)

Based on: `kopis-spec.md` (the Kopis KEM specification bundled in this branch).

Kopis strongly resembles ML-KEM (FIPS 203), but with three deliberate departures,
each of which is reflected in this mechanization:

1. **No NTT.** Kopis works over `R = ℤ[X]/(X²⁵⁶ + 1)` and its residue rings
   `Rn = R/2ⁿR` directly. Polynomial multiplication is the schoolbook negacyclic
   convolution (`Polynomial.mul`), not a pointwise product in an NTT domain.
2. **TurboSHAKE everywhere.** Every symmetric primitive (key expansion, matrix
   generation, secret generation, the public-key hash, and the Fujisaki–Okamoto
   hash) is a TurboSHAKE128/256 call (RFC 9861), replacing ML-KEM's SHA-3/SHAKE.
3. **Rounding, not noise.** Kopis is a Learning-With-Rounding scheme: instead of
   adding a sampled error polynomial to a lattice point, it deterministically
   rounds (`RoundToR10`, `RoundToRt`, `RoundToR1`), i.e. adds a fixed rounding
   constant and right-shifts.

## Mechanization notes

- **Ring elements.** `Rn` (coefficients mod `2ⁿ`) is `Polynomial (2^n)` =
  `Vector (ZMod (2^n)) 256`. The coefficient at index `i` is the coefficient of
  `Xⁱ`. `.val` on a `ZMod (2^n)` gives the canonical representative in `[0, 2ⁿ)`,
  matching the spec's "canonical coefficients".
- **Negacyclic multiplication.** `X²⁵⁶ = -1`, so a product `aᵢ·bⱼ` lands in
  coefficient `(i+j) mod 256` with sign `-1` exactly when `i + j ≥ 256`.
- **Shifts.** `Polynomial.shiftRight`/`shiftLeft` act coefficient-wise on the
  canonical representatives; left shift wraps mod `2ⁿ` (spec §"Mathematical
  Definitions").
- **`as`.** The spec's `r as Rn'` (natural injection/projection) is
  `Polynomial.coerce`: take each canonical coefficient and reduce it mod `2ⁿ'`.
  When `n' > n` this is exact (injection); when `n' < n` it quotients (projection).
- **`serialize`/`deserialize`** are the bit-packing of `d`-bit coefficients,
  identical in structure to ML-KEM's ByteEncode/ByteDecode but with modulus `2ᵈ`
  for any `d` (Kopis needs `d = 13 > 12`, outside ML-KEM's range).
- **`GenSecret`** implements the spec's `bit_slice`/`hamming` centered-binomial
  sampling; with `η = μ/2` this is exactly ML-KEM's SamplePolyCBD_η.
- **TurboSHAKE argument order.** The Lean `turboSHAKE*` takes `(msg, D, outLen)`;
  the spec writes `TurboSHAKE(M, L, D)`. Calls below pass them in Lean order.
- **Parameters** are carried by a `ParameterSet` (Kopis-512/768/1024).
-/

namespace Spec.Kopis

open Aeneas.Notations.SRRange
open scoped Spec.Notations
open Spec.Notations (srrange_lt)
open Spec (𝔹 slice bitsToBytes bytesToBits)
open Spec.TurboSHAKE (turboSHAKE128 turboSHAKE256)

/-! ## Index-bound helpers

Nonlinear bounds arising from the bit-packing / sampling loops.  These are kept
local; each is stated in exactly the shape `get_elem_tactic` (= `grind`) needs. -/

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

/-! ## Ring elements `Rn = R / 2ⁿR` (spec §"Mathematical Definitions")

`R = ℤ[X]/(X²⁵⁶ + 1)` and `Rn = R/2ⁿR`.  A ring element is 256 coefficients in
`ZMod (2^n)`, coefficient `i` being that of `Xⁱ`. -/

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

/-- Pointwise addition.  Uses `Vector.zipWith` for the same `grind`-`whnf`
robustness reason documented in `Spec.MLKEM.Polynomial.add`. -/
def Polynomial.add (f g : Polynomial m) : Polynomial m := Vector.zipWith (· + ·) f g

/-- Pointwise subtraction (over `uN`, subtraction is wrapping — automatic in
`ZMod (2^n)`). -/
def Polynomial.sub (f g : Polynomial m) : Polynomial m := Vector.zipWith (· - ·) f g

instance {m} : Sub (Polynomial m) where sub := Polynomial.sub

/-- `Polynomial m` is an additive commutative monoid under pointwise addition.
This is the **sole** `Add` instance (there is one canonical `+`), and it makes
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

/-- Negacyclic (schoolbook) multiplication in `ℤ_m[X]/(X²⁵⁶ + 1)`.

`X²⁵⁶ = -1`, so `aᵢ · bⱼ` contributes to coefficient `(i + j) mod 256`, with a
sign flip precisely when `i + j ≥ 256`.  This replaces ML-KEM's NTT-domain
pointwise product. -/
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

/-- Coefficient-wise right shift on canonical representatives: `r >> N` (spec
§"Mathematical Definitions"). -/
def Polynomial.shiftRight (r : Polynomial m) (N : ℕ) : Polynomial m :=
  r.map (fun a => ((a.val >>> N : ℕ) : ZMod m))

/-- Coefficient-wise left shift on canonical representatives, reduced mod `2ⁿ`:
`r << N` (the cast back into `ZMod m` performs the reduction). -/
def Polynomial.shiftLeft (r : Polynomial m) (N : ℕ) : Polynomial m :=
  r.map (fun a => ((a.val <<< N : ℕ) : ZMod m))

/-- The spec's `r as Rn'` — the natural injection/projection between residue
rings.  Reduces each canonical coefficient mod the new modulus `m'`. -/
def Polynomial.coerce (r : Polynomial m) (m' : ℕ) : Polynomial m' :=
  r.map (fun a => (a.val : ZMod m'))

/-! ## Vectors and matrices of ring elements (spec §"Mathematical Definitions") -/

/-- `VecRn` as `PolyVector m ℓ` — a length-`ℓ` vector of ring elements. -/
abbrev PolyVector (m ℓ : ℕ) := Vector (Polynomial m) ℓ

/-- `MatRn` as an `ℓ × ℓ` matrix of ring elements. -/
abbrev PolyMatrix (m ℓ : ℕ) := Matrix (Fin ℓ) (Fin ℓ) (Polynomial m)

def PolyVector.zero (m ℓ : ℕ) : PolyVector m ℓ := Vector.replicate ℓ (Polynomial.zero m)

def PolyVector.set {m ℓ : ℕ} (v : PolyVector m ℓ) (i : ℕ) (f : Polynomial m)
    (_ : i < ℓ := by get_elem_tactic) : PolyVector m ℓ := Vector.set v i f

/-- Element-wise vector addition. -/
instance {m ℓ : ℕ} : Add (PolyVector m ℓ) where
  add v w := Vector.ofFn fun i => v[i] + w[i]

/-- Element-wise vector subtraction. -/
instance {m ℓ : ℕ} : Sub (PolyVector m ℓ) where
  sub v w := Vector.ofFn fun i => v[i] - w[i]

def PolyVector.shiftRight {m ℓ : ℕ} (v : PolyVector m ℓ) (N : ℕ) : PolyVector m ℓ :=
  v.map (·.shiftRight N)

def PolyVector.coerce {m ℓ : ℕ} (v : PolyVector m ℓ) (m' : ℕ) : PolyVector m' ℓ :=
  v.map (·.coerce m')

def PolyMatrix.zero (m ℓ : ℕ) : PolyMatrix m ℓ := Matrix.of (fun _ _ => Polynomial.zero m)

/-- Element-wise matrix update: `M.update i j val` sets entry `(i, j)` to `val`. -/
def PolyMatrix.update {m ℓ : ℕ} (M : PolyMatrix m ℓ) (i j : ℕ) (val : Polynomial m)
    (hi : i < ℓ := by get_elem_tactic) (_ : j < ℓ := by get_elem_tactic) : PolyMatrix m ℓ :=
  Matrix.updateRow M ⟨i, hi⟩ (fun col => if col = j then val else M ⟨i, hi⟩ col)

/-- Matrix–vector product `A · v` using negacyclic polynomial multiplication
(no NTT). -/
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

/-! ## Serialization (spec §"Auxiliary Functions")

`serialize(n, r)` packs the `n`-bit canonical coefficients of `r`, LSB-first,
into `32·n` bytes; `deserialize` inverts it.  Structurally identical to ML-KEM's
ByteEncode/ByteDecode, but for arbitrary bit-width `n` (Kopis uses `n = 13`). -/

/-- `serialize(n, r) : [u8; 32·n]`. -/
def serialize (n : ℕ) (r : Polynomial (2 ^ n)) : 𝔹 (32 * n) := Id.run do
  let mut b := Vector.replicate (8 * (32 * n)) false
  for hi : i in [0:256] do
    let mut a := r[i].val
    for hj : j in [0:n] do
      have := serialize_idx_lt (srrange_lt hi) (srrange_lt hj)
      b := b.set (n * i + j) (Bool.ofNat (a % 2))
      a := a / 2
  pure (bitsToBytes b)

/-- `deserialize(n, bytes) : Rn`. -/
def deserialize (n : ℕ) (B : 𝔹 (32 * n)) : Polynomial (2 ^ n) := Id.run do
  let b := bytesToBits B
  let mut F := Polynomial.zero (2 ^ n)
  for hi : i in [0:256] do
    F := F.set i (∑ j : Fin n, (b[n * i + j.val]'(serialize_idx_lt (srrange_lt hi) j.isLt)).toNat * 2 ^ j.val)
  pure F

/-- `serialize` on a vector: concatenate the per-element serializations. -/
def PolyVector.serialize {ℓ : ℕ} (n : ℕ) (v : PolyVector (2 ^ n) ℓ) : 𝔹 (ℓ * (32 * n)) :=
  (v.map (Kopis.serialize n)).flatten

/-- `deserialize` on a vector: deserialize each `32·n`-byte block. -/
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

/-- `GenMat(seed) : MatR13`.  Each entry is deserialized from a fresh
TurboSHAKE128 stream keyed by the row/column indices. -/
def GenMat (ℓ : ℕ) (seed : 𝔹 32) : PolyMatrix (2 ^ 13) ℓ := Id.run do
  let mut A := PolyMatrix.zero (2 ^ 13) ℓ
  for hi : i in [0:ℓ] do
    for hj : j in [0:ℓ] do
      let buf := turboSHAKE128 (seed ‖ #v[(i : Byte)] ‖ #v[(j : Byte)]) DOMSEP_GENMAT (32 * 13)
      A := A.update i j (deserialize 13 buf)
  pure A

/-- `GenSecret(seed) : VecR13`.  Centered-binomial sampling: for each coefficient
`k`, `hamming(vals[2k]) - hamming(vals[2k+1])`, where `vals` splits the
TurboSHAKE256 stream into `μ/2`-bit chunks (spec's `bit_slice`).  Concretely,
coefficient `k` is `(Σ of μ/2 bits) - (Σ of μ/2 bits)` — i.e. CBD with `η = μ/2`. -/
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

/-! ## Rounding (spec §"Auxiliary Functions")

Kopis' Learning-With-Rounding step: add a fixed rounding constant, then
right-shift and reinterpret in the coarser ring. -/

/-- `RoundToR10(v : R13^ℓ) : R10^ℓ` — add 4, shift right by 3, project to `R10`. -/
def RoundToR10 (ℓ : ℕ) (v : PolyVector (2 ^ 13) ℓ) : PolyVector (2 ^ 10) ℓ :=
  let h : PolyVector (2 ^ 13) ℓ := Vector.replicate ℓ (Polynomial.const (2 ^ 13) 4)
  ((v + h).shiftRight 3).coerce (2 ^ 10)

/-- `RoundToRt(r : R10) : Rt` — add 4, shift right by `10 - t`, project to `Rt`. -/
def RoundToRt (t : ℕ) (r : Polynomial (2 ^ 10)) : Polynomial (2 ^ t) :=
  let h := Polynomial.const (2 ^ 10) 4
  ((r + h).shiftRight (10 - t)).coerce (2 ^ t)

/-- `RoundToR1(r : R10) : R1` — add `2⁸ - 2⁹⁻ᵗ + 4`, shift right by 9, project to
`R1` (spec: `h2 = 2⁸ - 2^(10-t-1) + 4`, and `10 - t - 1 = 9 - t`). -/
def RoundToR1 (t : ℕ) (r : Polynomial (2 ^ 10)) : Polynomial (2 ^ 1) :=
  let c : ZMod (2 ^ 10) := ((2 ^ 8 - 2 ^ (9 - t) + 4 : ℕ) : ZMod (2 ^ 10))
  let h := Polynomial.const (2 ^ 10) c
  ((r + h).shiftRight 9).coerce (2 ^ 1)

/-! ## Key expansion (spec §"Auxiliary Functions") -/

/-- `ExpandDecapKey(sk) : (VecR13, [u8;32], [u8; PK_SIZE], [u8;32])`.
Derives the matrix/secret seeds and rejection seed `z` from `sk`, regenerates the
secret vector and public key, and hashes the public key. -/
def ExpandDecapKey (p : ParameterSet) (sk : 𝔹 32) :
    PolyVector (2 ^ 13) (ℓ p) × 𝔹 32 × 𝔹 (pkSize p) × 𝔹 32 :=
  let randomness := turboSHAKE256 (sk ‖ #v[(ℓ p : Byte)]) DOMSEP_KGEXPAND 96
  let mat_seed    := slice randomness 0 32
  let secret_seed := slice randomness 32 32
  let z           := slice randomness 64 32
  let mat_A := GenMat (ℓ p) mat_seed
  let vec_s := GenSecret (ℓ p) (μ p) secret_seed
  let vec_b := RoundToR10 (ℓ p) (matVecMul (Matrix.transpose mat_A) vec_s)
  let pk : 𝔹 (pkSize p) := (PolyVector.serialize 10 vec_b ‖ mat_seed).cast (by simp [pkSize]; ring)
  let pkh := turboSHAKE256 pk DOMSEP_PKHASH 32
  (vec_s, z, pk, pkh)

/-! ## Public-key encryption (spec §"PKE") -/

/-- `SkToPk(sk) : [u8; PK_SIZE]`. -/
def SkToPk (p : ParameterSet) (sk : 𝔹 32) : 𝔹 (pkSize p) :=
  let (_, _, pk, _) := ExpandDecapKey p sk
  pk

/-- `PkeEncrypt(seed, pk, msg) : [u8; CT_SIZE]`. IND-CPA encryption of the 32-byte
`msg` (decoded to an `R1` element) under `pk`, with LWR rounding. -/
def PkeEncrypt (p : ParameterSet) (seed : 𝔹 32) (pk : 𝔹 (pkSize p)) (msg : 𝔹 32) :
    𝔹 (ctSize p) :=
  let vec_b := PolyVector.deserialize (ℓ := ℓ p) 10 (slice pk 0 (32 * 10 * ℓ p) (by simp [pkSize]))
  let mat_seed := slice pk (32 * 10 * ℓ p) 32 (by simp [pkSize])
  let m := deserialize 1 msg
  let mat_A := GenMat (ℓ p) mat_seed
  let vec_sprime := GenSecret (ℓ p) (μ p) seed
  let vec_bprime := RoundToR10 (ℓ p) (matVecMul mat_A vec_sprime)
  let vprime := innerProduct vec_b (vec_sprime.coerce (2 ^ 10))
  let cm := RoundToRt (t p) (vprime - ((m.coerce (2 ^ 10)).shiftLeft 9))
  (PolyVector.serialize 10 vec_bprime ‖ serialize (t p) cm).cast (by simp [ctSize]; ring)

/-- `PkeDecrypt(sk, c) : [u8; 32]`. Unconditionally recovers a 32-byte message. -/
def PkeDecrypt (p : ParameterSet) (sk : 𝔹 32) (c : 𝔹 (ctSize p)) : 𝔹 32 :=
  let (vec_s, _, _, _) := ExpandDecapKey p sk
  let vec_bprime := PolyVector.deserialize (ℓ := ℓ p) 10 (slice c 0 (32 * 10 * ℓ p) (by simp [ctSize]))
  let cm := deserialize (t p) (slice c (32 * 10 * ℓ p) (32 * t p) (by simp [ctSize]))
  let v := innerProduct vec_bprime (vec_s.coerce (2 ^ 10))
  let cm10 := (cm.coerce (2 ^ 10)).shiftLeft (10 - t p)
  let mprime := RoundToR1 (t p) (v - cm10)
  serialize 1 mprime

/-! ## Key encapsulation (spec §"KEM")

The IND-CCA KEM via the Fujisaki–Okamoto transform. `SkToPk` is shared with the
PKE above. -/

/-- `KemEncap(randomness, pk) : ([u8;32], [u8; CT_SIZE])`. -/
def KemEncap (p : ParameterSet) (randomness : 𝔹 32) (pk : 𝔹 (pkSize p)) :
    𝔹 32 × 𝔹 (ctSize p) :=
  let pkh := turboSHAKE256 pk DOMSEP_PKHASH 32
  let b := turboSHAKE256 (randomness ‖ pkh) DOMSEP_FO 64
  let k := slice b 0 32
  let r := slice b 32 32
  let c := PkeEncrypt p r pk randomness
  (k, c)

/-- `KemDecap(sk, c) : [u8; 32]`.

The final branch on `c == c'` (implicit rejection) MUST be evaluated in constant
time by any implementation; the spec value is unaffected by the timing. -/
def KemDecap (p : ParameterSet) (sk : 𝔹 32) (c : 𝔹 (ctSize p)) : 𝔹 32 :=
  let (_, z, pk, pkh) := ExpandDecapKey p sk
  let randomness := PkeDecrypt p sk c
  let b := turboSHAKE256 (randomness ‖ pkh) DOMSEP_FO 64
  let k := slice b 0 32
  let rprime := slice b 32 32
  let cprime := PkeEncrypt p rprime pk randomness
  if c = cprime then k
  else turboSHAKE256 (z ‖ c) DOMSEP_NOREJECT 32

end Spec.Kopis
