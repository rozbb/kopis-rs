import Spec.Kopis.Spec
import SpecTests.TestUtils

/-!
# Kopis spec tests

These tests are of three kinds:

- **Fast `#guard` unit tests** exercising the pure ring layer (negacyclic
  multiplication, shifts, serialization round-trips, rounding). These run during
  `lake build SpecTests`.
- **A native round-trip runner** (`lake exe kopisTests`) that checks end-to-end
  KEM correctness — `KemDecap(sk, KemEncap(r, SkToPk(sk))) = k` — for every
  parameter set. This exercises the TurboSHAKE-heavy path, which is far too slow
  to evaluate at `#guard` time under the reference spec.
- **Known-answer tests** from the `SpecTests/Kopis/vectors/*.jsonl` files (see
  the section below), also run by `lake exe kopisTests`. These are the same
  vector files the Rust crate's `tests/ref_kat.rs` consumes, so passing both
  runners cross-validates the Rust implementation against this spec.
-/

namespace Spec.Kopis.Test

open Spec.Kopis
open Spec (𝔹)

/-! ## Fast unit tests (`#guard`) — pure ring layer, no TurboSHAKE -/

/-- The monomial `c · Xⁱ` in `ℤ_m[X]/(X²⁵⁶+1)`. -/
private def mono (m i : ℕ) (c : ZMod m) (h : i < 256 := by omega) : Polynomial m :=
  (Polynomial.zero m).set i c

/-- A dense sample polynomial in `R13` with coefficient `i` at index `i`. -/
private def sample13 : Polynomial (2 ^ 13) := Vector.ofFn fun i => (i.val : ZMod (2 ^ 13))

/-! ### Serialization round-trips -/

-- Coefficients are canonical (`< 2¹³`), so packing 13 bits each is lossless.
#guard deserialize 13 (serialize 13 sample13) = sample13

-- n = 1: a bit-packed message round-trips.
#guard deserialize 1 (serialize 1 (mono (2 ^ 1) 0 1)) = mono (2 ^ 1) 0 1

/-! ### Negacyclic multiplication (`X²⁵⁶ = -1`) -/

-- `1 · p = p` (multiplicative identity is the constant `1 = 1·X⁰`).
#guard mono (2 ^ 13) 0 1 * sample13 = sample13

-- `X · X²⁵⁵ = X²⁵⁶ = -1`, i.e. the constant `-1` and zero elsewhere.
#guard mono (2 ^ 13) 1 1 * mono (2 ^ 13) 255 1 = mono (2 ^ 13) 0 (-1)

-- `X · X = X²` (no wrap yet).
#guard mono (2 ^ 13) 1 1 * mono (2 ^ 13) 1 1 = mono (2 ^ 13) 2 1

/-! ### Shifts on canonical coefficients -/

-- Right shift divides each coefficient; left shift multiplies (mod 2ⁿ).
#guard (mono (2 ^ 13) 3 8).shiftRight 3 = mono (2 ^ 13) 3 1
#guard (mono (2 ^ 10) 5 1).shiftLeft 9 = mono (2 ^ 10) 5 512

/-! ### Coercion (the spec's `as`) -/

-- Injection R1 ↪ R10 then a left shift by 9 lifts a message bit to the high bit.
#guard ((mono (2 ^ 1) 7 1).coerce (2 ^ 10)).shiftLeft 9 = mono (2 ^ 10) 7 512

/-! ### Rounding -/

-- `RoundToRt` on the all-zero element is zero (adding 4 then `>> (10-t)` clears).
#guard RoundToRt 3 (Polynomial.zero (2 ^ 10)) = Polynomial.zero (2 ^ 3)
#guard RoundToR1 3 (Polynomial.zero (2 ^ 10)) = Polynomial.zero (2 ^ 1)

-- Parameter constants match the spec table.
#guard (ℓ .Kopis_512, t .Kopis_512, μ .Kopis_512) = (2, 3, 10)
#guard (ℓ .Kopis_768, t .Kopis_768, μ .Kopis_768) = (3, 4, 8)
#guard (ℓ .Kopis_1024, t .Kopis_1024, μ .Kopis_1024) = (4, 6, 6)
#guard (pkSize .Kopis_512, ctSize .Kopis_512) = (672, 736)
#guard (pkSize .Kopis_768, ctSize .Kopis_768) = (992, 1088)
#guard (pkSize .Kopis_1024, ctSize .Kopis_1024) = (1312, 1472)

/-! ## Native round-trip runner (`lake exe kopisTests`)

End-to-end KEM correctness: encapsulating to `SkToPk(sk)` and decapsulating with
`sk` must recover the same shared secret. -/

open Spec.Utils

/-- A deterministic pseudo-random 32-byte value derived from a `seed` byte. -/
private def bytes32 (seed : Byte) : 𝔹 32 := Vector.ofFn fun i => (seed + 7 * (i.val : Byte))

/-- One KeyGen → Encap → Decap round-trip for parameter set `p`. -/
private def roundTrip (label : String) (p : ParameterSet) (skSeed rSeed : Byte) : IO Unit := do
  let t0 ← IO.monoMsNow
  let sk := bytes32 skSeed
  let pk := SkToPk p sk
  let (k, c) := KemEncap p (bytes32 rSeed) pk
  let k' := KemDecap p sk c
  let t1 ← IO.monoMsNow
  if k != k' then
    throw (IO.userError s!"{label}: shared-secret mismatch\n  encap: {k}\n  decap: {k'}")
  IO.println s!"  {label} round-trip: {t1 - t0} ms  ss: OK"

def runKopisTests : IO Unit := do
  IO.println "=== Kopis KEM round-trip tests ==="
  roundTrip "Kopis-512 " .Kopis_512  0x11 0x22
  roundTrip "Kopis-768 " .Kopis_768  0x33 0x44
  roundTrip "Kopis-1024" .Kopis_1024 0x55 0x66
  IO.println "ALL OK"

/-! ## Known-answer tests from external `.jsonl` vectors

Reads the `SpecTests/Kopis/vectors/*.jsonl` files at runtime (one JSON object per
line) so the vectors can be regenerated/updated without touching Lean source.
Paths are relative to the package root, i.e. run from `lean/`:
`lake exe kopisTests`. -/

open Lean (Json fromJson?)

/-- One line of a Kopis `.jsonl` test-vector file. All byte fields are hex. -/
structure KopisVector where
  description : String
  sk : String
  pk : String
  encap_randomness : String
  encapper_ct : String
  decapper_ct : String
  encapper_ss : String
  decapper_ss : String
  malformed : Bool
  deriving Lean.FromJson, Repr

/-- Decode a hex field to a fixed-length byte vector, or fail with context. -/
private def need {n : ℕ} (label : String) (o : Option (𝔹 n)) : IO (𝔹 n) :=
  match o with
  | some v => pure v
  | none   => throw (IO.userError s!"{label}: hex parse or length error")

/-- Run every vector in one `.jsonl` file against parameter set `p`. -/
private def runKAT (p : ParameterSet) (path : System.FilePath) : IO Unit := do
  IO.println s!"  {path}"
  let mut good := 0
  let mut rejected := 0
  for line in (← IO.FS.lines path) do
    if line.trimAscii.isEmpty then continue
    let j ← IO.ofExcept (Json.parse line)
    let v : KopisVector ← IO.ofExcept (fromJson? j)
    if v.malformed then
      -- Every malformed vector is a length violation; the spec's fixed-width
      -- interface types reject it, modeled here by a failed sized hex decode.
      let accepted :=
        (Hex.toVector? v.sk 32).isSome &&
        (Hex.toVector? v.pk (pkSize p)).isSome &&
        (Hex.toVector? v.encap_randomness 32).isSome &&
        (Hex.toVector? v.decapper_ct (ctSize p)).isSome
      if accepted then
        throw (IO.userError s!"{v.description}: malformed vector accepted at valid sizes")
      rejected := rejected + 1
    else
      let sk  ← need s!"{v.description}: sk"  (Hex.toVector? v.sk 32)
      let pk  ← need s!"{v.description}: pk"  (Hex.toVector? v.pk (pkSize p))
      let er  ← need s!"{v.description}: encap_randomness" (Hex.toVector? v.encap_randomness 32)
      let ect ← need s!"{v.description}: encapper_ct" (Hex.toVector? v.encapper_ct (ctSize p))
      let dct ← need s!"{v.description}: decapper_ct" (Hex.toVector? v.decapper_ct (ctSize p))
      let ess ← need s!"{v.description}: encapper_ss" (Hex.toVector? v.encapper_ss 32)
      let dss ← need s!"{v.description}: decapper_ss" (Hex.toVector? v.decapper_ss 32)
      -- Public-key derivation.
      if SkToPk p sk != pk then
        throw (IO.userError s!"{v.description}: SkToPk(sk) ≠ pk")
      -- Encapsulation matches both the shared secret and the ciphertext.
      let (k, c) := KemEncap p er pk
      if k != ess then throw (IO.userError s!"{v.description}: encapper_ss mismatch")
      if c != ect then throw (IO.userError s!"{v.description}: encapper_ct mismatch")
      -- Decapsulation (mauled ciphertexts exercise implicit rejection).
      if KemDecap p sk dct != dss then
        throw (IO.userError s!"{v.description}: decapper_ss mismatch")
      good := good + 1
  IO.println s!"    {good} good vectors OK, {rejected} malformed vectors rejected"

def runKopisKAT : IO Unit := do
  IO.println "=== Kopis known-answer tests (external vectors) ==="
  runKAT .Kopis_512  "SpecTests/Kopis/vectors/test_vectors-kopis512.jsonl"
  runKAT .Kopis_768  "SpecTests/Kopis/vectors/test_vectors-kopis768.jsonl"
  runKAT .Kopis_1024 "SpecTests/Kopis/vectors/test_vectors-kopis1024.jsonl"
  IO.println "ALL KAT OK"

end Spec.Kopis.Test
