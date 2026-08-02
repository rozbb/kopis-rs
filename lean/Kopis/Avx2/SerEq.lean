/-
  # Kopis/Avx2/SerEq.lean — Phase C's target.

  The AVX2 bit-unpacker and the portable one produce the same array, for every coefficient width
  the crate uses:

      backend::avx2::ser::deserialize bytes bits  =  ser::deserialize_generic bytes bits

  Both sides are constants of the *same* extraction, so this is a self-contained equality: no
  specification, and nothing about the serial backend, enters it.  It is proved by showing each
  side computes coefficient `j` of the little-endian bit stream —
  `deserialize_streamNat` for the vector path, `Generic.generic_streamNat` for the sliding-window
  one — and then that two `Array U16 256`s agreeing elementwise are equal.

  This is what makes the AVX2 deserializer covered by the portable proofs: anything already
  proved about `ser::deserialize_generic` transfers to `backend::avx2::ser::deserialize` by
  rewriting with this.
-/
import Kopis.Avx2.Ser
import Kopis.Avx2.SerGeneric

open Aeneas Aeneas.Std Result
open RustKopisAvx2

namespace Kopis.Avx2

open Kopis.Properties (streamNat)

/-- **Phase C.**  The vector unpacker is bit-identical to the portable one, for every width the
crate uses (`1 ≤ bits ≤ 13`) and every correctly-sized input. -/
theorem avx2_deserialize_eq (bytes : Slice U8) (n : ℕ) (hn1 : 1 ≤ n) (hn13 : n ≤ 13)
    (hlen : bytes.length = 32 * n) (bitsU : Usize) (hbitsU : bitsU.val = n) :
    backend.avx2.ser.deserialize bytes bitsU = ser.deserialize_generic 256#usize bytes bitsU := by
  have hbeq : bitsU = n#usize := UScalar.eq_of_val_eq (by rw [hbitsU]; simp)
  obtain ⟨r1, hr1, hp1⟩ :=
    WP.spec_imp_exists (deserialize_streamNat bytes n hn1 hn13 hlen bitsU hbitsU)
  have hgen : ser.deserialize_generic 256#usize bytes bitsU
      ⦃ (r : Array U16 256#usize) => ∀ j < 256,
          (r.val[j]!).val = streamNat bytes (n * j) n ⦄ := by
    rw [hbeq]
    exact Generic.generic_streamNat bytes n hn1 hn13 hlen
  obtain ⟨r2, hr2, hp2⟩ := WP.spec_imp_exists hgen
  rw [hr1, hr2]
  congr 1
  apply Subtype.ext
  apply List.ext_getElem
  · have h1 := r1.property
    have h2 := r2.property
    scalar_tac
  · intro k hk1 hk2
    have hk : k < 256 := by have := r1.property; scalar_tac
    apply UScalar.eq_of_val_eq
    rw [← getElem!_pos r1.val k hk1, ← getElem!_pos r2.val k hk2, hp1 k hk, hp2 k hk]

end Kopis.Avx2
