import Kopis.Properties.GenMatrix
open Aeneas Aeneas.Std Result kopis
open Spec (𝔹)
open Spec.TurboSHAKE (turboSHAKE256)
namespace Kopis.Properties
set_option maxHeartbeats 2000000
set_option maxRecDepth 4000

/-- Reusable spec for the generic two-input turboSHAKE256 hash: absorbing `input0`
then `input1` under domain separator `DS` and squeezing 32 bytes yields exactly
`turboSHAKE256` applied to the concatenated inputs. -/
theorem turboshake256_hash_spec (DS : Std.U8) (input0 input1 : Slice U8) :
    turboshake256_hash DS input0 input1
      ⦃ (r : Array U8 32#usize) =>
          arrayToBytes r = turboSHAKE256
            (u8ListToBytes (input0.val ++ input1.val)) DS.bv 32 ⦄ := by
  have e32 : (32#usize).val = 32 := rfl
  unfold turboshake256_hash
  step*
  have habs : hasherAbsorbed hasher2 = input0.val ++ input1.val := by
    rw [hasher2_post, hasher1_post, hasher_post]; simp
  have hslen : s.length = 32 := by
    rw [Slice.length, s_post1]; exact (Array.repeat 32#usize 0#u8).property
  have hs1len : s1.length = 32 := by rw [__post1, hslen]
  rw [reader_post1, reader_post2] at __post2
  dsimp only at __post2
  rw [Nat.zero_add, hslen] at __post2
  rw [habs] at __post2
  rw [s_post2]
  apply Vector.toList_inj.mp
  rw [arrayToBytes_toList, Array.from_slice_val _ s1 (by rw [← Slice.length, hs1len]; exact e32.symm)]
  exact __post2

end Kopis.Properties
