import Mathlib.LinearAlgebra.Matrix.RowCol
import Spec.Kopis.Spec

/-! # The Kopis spec, with explicit parameters

The definitions `Spec.lean` had before it was rewritten to follow `kopis.py` line by line. Here the
helper functions take `ℓ`, `μ` and `t` as arguments rather than a `ParameterSet`, so that the
correspondence proofs can instantiate them with the Rust const generics, and they are written in the
pure `Vector.ofFn` style those proofs are built on. `Equiv.lean` proves they agree with `Spec.lean`.
-/

namespace Spec.Kopis.Explicit

open Aeneas.Notations.SRRange
open scoped Spec.Notations
open Spec.Notations (srrange_lt)
open Spec.TurboSHAKE (turboSHAKE128 turboSHAKE256)

/-- The spec's argument order, `TurboSHAKE128(M, L, D)`. -/
local notation "TurboSHAKE128" M:max L:max D:max => turboSHAKE128 M D L
/-- The spec's argument order, `TurboSHAKE256(M, L, D)`. -/
local notation "TurboSHAKE256" M:max L:max D:max => turboSHAKE256 M D L

/-- The `i`-th length-`n` chunk of a `k·n`-element sequence is in bounds. -/
theorem chunk_bound {n k i : ℕ} (hi : i < k) : n * i + n ≤ n * k := by
  rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left n hi

/-- `make_rn`, with coefficients already in `ZMod (2ⁿ)`. -/
def make_rn (n : ℕ) (coeffs : Vector (ZMod (2 ^ n)) 256) : R n := coeffs

def PolyVector.zero (m ℓ : ℕ) : PolyVector m ℓ := Vector.replicate ℓ (Poly.zero m)

/-- Set polynomial `i` in `v: PolyVector` to `f` -/
def PolyVector.set {m ℓ : ℕ} (v : PolyVector m ℓ) (i : ℕ) (f : Poly m)
    (_ : i < ℓ := by get_elem_tactic) : PolyVector m ℓ := Vector.set v i f


def PolyMatrix.zero (m ℓ : ℕ) : PolyMatrix m ℓ := Matrix.of (fun _ _ => Poly.zero m)

/-- Set entry `(i, j)` in `M: PolyMatrix` to `val` -/
def PolyMatrix.update {m ℓ : ℕ} (M : PolyMatrix m ℓ) (i j : ℕ) (val : Poly m)
    (hi : i < ℓ := by get_elem_tactic) (_ : j < ℓ := by get_elem_tactic) : PolyMatrix m ℓ :=
  Matrix.updateRow M ⟨i, hi⟩ (fun col => if col = j then val else M ⟨i, hi⟩ col)


/-! ## Serialization (§"Auxiliary Functions") -/


def serialize_elem (n : ℕ) (r : R n) : 𝔹 (32 * n) :=
  let a := canonical_coeffs r
  let all_bits : Vector Bool (256 * n) := (Vector.ofFn fun i : Fin 256 => to_bits_le n a[i]).flatten
  Vector.ofFn fun i : Fin (32 * n) =>
    (from_bits_le 8 (Spec.slice all_bits (8 * i) 8 (by have := i.isLt; omega)) : Byte)


def deserialize_elem (n : ℕ) (bytes : 𝔹 (32 * n)) : R n :=
  let all_bits : Vector Bool (32 * n * 8) :=
    (Vector.ofFn fun i : Fin (32 * n) => to_bits_le 8 bytes[i].toNat).flatten
  let coeffs : Vector (ZMod (2 ^ n)) 256 := Vector.ofFn fun i : Fin 256 =>
    from_bits_le n (Spec.slice all_bits (n * i) n (by have := chunk_bound (n := n) i.isLt; omega))
  make_rn n coeffs


def serialize_vec {ℓ : ℕ} (n : ℕ) (v : VecR n ℓ) : 𝔹 (ℓ * (32 * n)) :=
  (v.map (serialize_elem n)).flatten


def deserialize_vec {ℓ : ℕ} (n : ℕ) (bytes : 𝔹 (32 * n * ℓ)) : VecR n ℓ :=
  Vector.ofFn fun i =>
    deserialize_elem n (Spec.slice bytes (32 * n * i) (32 * n) (chunk_bound i.isLt))

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

/-! ## Sampling (spec §"Auxiliary Functions") -/

/-- This takes `ℓ` rather than a `ParameterSet` so that proofs can instantiate it with the Rust const
generic. The spec only ever passes `ℓ p`. -/
def GenMat (ℓ : ℕ) (seed : 𝔹 32) : MatR 13 ℓ := Id.run do
  let mut A := PolyMatrix.zero (2 ^ 13) ℓ
  for hi : i in [0:ℓ] do
    for hj : j in [0:ℓ] do
      let buf := TurboSHAKE128 (seed ‖ #v[(i : Byte)] ‖ #v[(j : Byte)]) (32 * 13) DOMSEP_GENMAT
      A := PolyMatrix.update A i j (deserialize_elem 13 buf)
  pure A


def bit_slices (μ : ℕ) (bytes : 𝔹 (32 * μ)) : Vector (Vector Bool (μ / 2)) 512 :=
  let all_bits : Vector Bool (32 * μ * 8) :=
    (Vector.ofFn fun i : Fin (32 * μ) => to_bits_le 8 bytes[i].toNat).flatten
  Vector.ofFn fun i : Fin 512 => Spec.slice all_bits (i * μ / 2) (μ / 2) (by
    have := Nat.mul_le_mul_right μ (Nat.succ_le_of_lt i.isLt); rw [Nat.succ_mul] at this; omega)


def hamming {k : ℕ} (b : Vector Bool k) : ℕ := ∑ i : Fin k, b[i].toNat

/-- This takes `ℓ` and `μ` rather than a `ParameterSet` so that proofs can instantiate them with the
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
    s := PolyVector.set s i (make_rn 13 r)
  pure s

/-! ## Compression and message decoding (spec §"Auxiliary Functions") -/

/-- This takes `ℓ` rather than a `ParameterSet`; see `GenMat`. -/
def CompressToR10 (ℓ : ℕ) (v : VecR 13 ℓ) : VecR 10 ℓ :=
  let h1 := make_rn 13 (Vector.replicate 256 4)
  let h : VecR 13 ℓ := Vector.replicate ℓ h1
  let s := (v + h) >>> 3
  s.coerce (2 ^ 10)


def CompressToRt (t : ℕ) (r : R 10) : R t :=
  let h1 := make_rn 10 (Vector.replicate 256 4)
  let s := (r + h1) >>> (10 - t)
  s.coerce (2 ^ t)


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


def ExpandSecretKey (p : ParameterSet) (sk : 𝔹 32) :
    VecR 13 (ℓ p) × 𝔹 32 × 𝔹 (pkSize p) × 𝔹 32 :=
  let randomness := TurboSHAKE256 (sk ‖ #v[(ℓ p : Byte)]) 96 DOMSEP_KGEXPAND
  let mat_seed := Spec.slice randomness 0 32
  let secret_seed := Spec.slice randomness 32 32
  let z := Spec.slice randomness 64 32
  let mat_A := GenMat (ℓ p) mat_seed
  let vec_s := GenSecret (ℓ p) (μ p) secret_seed
  let vec_b := CompressToR10 (ℓ p) (transpose mat_A * vec_s)
  let pk : 𝔹 (pkSize p) := (serialize_vec 10 vec_b ‖ mat_seed).cast (by simp [pkSize]; ring)
  let pkh := TurboSHAKE256 pk 32 DOMSEP_PKHASH
  (vec_s, z, pk, pkh)

/-! ## Public-key encryption (spec §"PKE") -/


def SkToPk (p : ParameterSet) (sk : 𝔹 32) : 𝔹 (pkSize p) :=
  let (_, _, pk, _) := ExpandSecretKey p sk
  pk

def PkeEncrypt (p : ParameterSet) (randomness : 𝔹 32) (pk : 𝔹 (pkSize p)) (msg : 𝔹 32) :
    𝔹 (ctSize p) :=
  let vec_b := deserialize_vec (ℓ := ℓ p) 10 (Spec.slice pk 0 (32 * 10 * ℓ p) (by simp [pkSize]))
  let mat_seed := Spec.slice pk (32 * 10 * ℓ p) 32 (by simp [pkSize])
  let m := deserialize_elem 1 msg
  let mat_A := GenMat (ℓ p) mat_seed
  let vec_sprime := GenSecret (ℓ p) (μ p) randomness
  let vec_bprime := CompressToR10 (ℓ p) (mat_A * vec_sprime)
  let vprime := transpose vec_b * vec_sprime.coerce (2 ^ 10)
  let cm := CompressToRt (t p) (vprime - (m.coerce (2 ^ 10) <<< 9))
  let ct := serialize_vec 10 vec_bprime ‖ serialize_elem (t p) cm
  ct.cast (by simp [ctSize]; ring)

def PkeDecrypt (p : ParameterSet) (sk : 𝔹 32) (ct : 𝔹 (ctSize p)) : 𝔹 32 :=
  let (vec_s, _, _, _) := ExpandSecretKey p sk
  let vec_bprime := deserialize_vec (ℓ := ℓ p) 10 (Spec.slice ct 0 (32 * 10 * ℓ p) (by simp [ctSize]))
  let cm := deserialize_elem (t p) (Spec.slice ct (32 * 10 * ℓ p) (32 * t p) (by simp [ctSize]))
  let v := transpose vec_bprime * vec_s.coerce (2 ^ 10)
  let cm10 := cm.coerce (2 ^ 10) <<< (10 - t p)
  let mprime := DecodeMsg (t p) (v - cm10)
  serialize_elem 1 mprime

/-! ## Key encapsulation (spec §"KEM") -/


def KemEncap (p : ParameterSet) (randomness : 𝔹 32) (pk : 𝔹 (pkSize p)) :
    𝔹 32 × 𝔹 (ctSize p) :=
  let pkh := TurboSHAKE256 pk 32 DOMSEP_PKHASH
  let b := TurboSHAKE256 (randomness ‖ pkh) 64 DOMSEP_FO
  let k := Spec.slice b 0 32
  let r := Spec.slice b 32 32
  let ct := PkeEncrypt p r pk randomness
  (k, ct)


def KemDecap (p : ParameterSet) (sk : 𝔹 32) (ct : 𝔹 (ctSize p)) : 𝔹 32 :=
  let (_, z, pk, pkh) := ExpandSecretKey p sk
  let randomness := PkeDecrypt p sk ct
  let b := TurboSHAKE256 (randomness ‖ pkh) 64 DOMSEP_FO
  let k := Spec.slice b 0 32
  let rprime := Spec.slice b 32 32
  let cprime := PkeEncrypt p rprime pk randomness
  if ct = cprime then k
  else TurboSHAKE256 (z ‖ ct) 32 DOMSEP_NOREJECT


/-- The `Spec.lean` parameter set with this name. -/
def ParameterSet.toSpec : ParameterSet → Spec.Kopis.ParameterSet
  | .Kopis_512  => .Kopis_512
  | .Kopis_768  => .Kopis_768
  | .Kopis_1024 => .Kopis_1024

end Spec.Kopis.Explicit
