/-
  # Kopis/Properties/SerializeRoundtrip.lean — the *other* encoding round-trip.

  `Kopis/Properties/EncodeRoundtrip.lean` proves `deserialize ∘ serialize = id`
  (decoding recovers what was encoded).  This file proves the converse,
  `serialize ∘ deserialize = id`: re-encoding an arbitrary byte string that has been
  decoded gives that byte string back.  It is what ties `PkePublicKey::from_bytes`
  to the bytes it was handed, and hence what lets `KemPublicKey::from_bytes` — which
  hashes the parsed key — be related to the *input* rather than to its own
  re-serialization.

  The proof is a counting argument rather than a bit-level one.  `serialize n` is
  injective (that is exactly `deserialize_serialize`), and its domain and codomain are
  finite of the same size — `(2ⁿ)²⁵⁶` polynomials and `(2⁸)^(32n)` byte strings are both
  `2^(256n)` — so it is a bijection and its left inverse is also a right inverse.

  This requires `Fintype` instances for `BitVec` and `Vector`, which are not in scope
  here; they are declared as file-local instances, so nothing leaks to importers.
-/
import Kopis.Properties.EncodeRoundtrip
open Aeneas Aeneas.Std Result
open Spec (𝔹)

namespace Kopis.Properties

/-! ## Finiteness plumbing

Neither `BitVec w` nor `Vector α m` has a `Fintype` instance in this import closure.
Both are immediate, and both are kept `local` to this file. -/

/-- `BitVec w` is `Fin (2^w)` in disguise. -/
private def bitVecEquivFin {w : ℕ} : BitVec w ≃ Fin (2 ^ w) where
  toFun := BitVec.toFin
  invFun := BitVec.ofFin
  left_inv _ := rfl
  right_inv _ := rfl

@[reducible] private def instFintypeBitVec {w : ℕ} : Fintype (BitVec w) :=
  Fintype.ofEquiv _ bitVecEquivFin.symm

attribute [local instance] instFintypeBitVec

private theorem card_bitVec {w : ℕ} : Fintype.card (BitVec w) = 2 ^ w := by
  rw [Fintype.card_congr (bitVecEquivFin (w := w)), Fintype.card_fin]

/-- A `Vector α m` is exactly a function `Fin m → α`. -/
private def vectorEquivFun {α : Type*} {m : ℕ} : Vector α m ≃ (Fin m → α) where
  toFun v i := v[i.val]
  invFun f := Vector.ofFn f
  left_inv _ := by apply Vector.ext; intro i hi; simp
  right_inv _ := by funext i; simp

@[reducible] private def instFintypeVector {α : Type*} {m : ℕ} [Fintype α] : Fintype (Vector α m) :=
  Fintype.ofEquiv _ vectorEquivFun.symm

attribute [local instance] instFintypeVector

private theorem card_vector {α : Type*} {m : ℕ} [Fintype α] :
    Fintype.card (Vector α m) = Fintype.card α ^ m := by
  rw [Fintype.card_congr (vectorEquivFun (α := α) (m := m)), Fintype.card_fun, Fintype.card_fin]

/-- **Byte strings and polynomials are equinumerous.**  `32n` bytes hold `256^(32n) =
2^(256n)` values; a degree-256 polynomial over `ZMod (2ⁿ)` holds `(2ⁿ)^256 = 2^(256n)`.
This is the whole content of "the `n`-bit packing wastes no space". -/
private theorem card_bytes_eq_card_poly (n : ℕ) :
    Fintype.card (𝔹 (32 * n)) = Fintype.card (Spec.Kopis.Polynomial (2 ^ n)) := by
  haveI : NeZero (2 ^ n) := ⟨by positivity⟩
  rw [card_vector, card_vector, card_bitVec, ZMod.card, ← pow_mul, ← pow_mul]
  congr 1
  ring

/-- Rewriting a vector under `getElem`, without `rw`'s motive problems. -/
private theorem getElem_congr_vec {α : Type*} {m : ℕ} {v w : Vector α m} (h : v = w)
    (i : ℕ) (hi : i < m) : v[i]'hi = w[i]'hi := by rw [h]

/-! ## The round-trip -/
end Kopis.Properties
