/-
  # Kopis/Avx2/SerTail.lean — where each group's sixteen bytes come from.

  The vector deserializer reads a whole 16 bytes from every group's first byte, but a group is
  only `bits` bytes long, so the last `⌊15/bits⌋` groups would read past the end of a
  `32·bits`-byte buffer.  `src/backend/avx2/ser.rs` copies that short remainder into a
  zero-padded 32-byte scratch buffer and reads those groups from there.

  Both paths are made to say the same thing here:

      byte `m` of the group's load  =  streamByte bytes (group·bits + m)

  and `streamByte` reads out of range as zero, which is exactly what the scratch buffer holds
  there.  That is what collapses the head/tail case split into a single hypothesis for the lane
  lemma, rather than propagating two cases through every later proof.

  This file is also where the two bounds live that an off-by-one would hide in: that the head
  load stays inside `bytes` (`group·bits + 16 ≤ 32·bits`, which is tight — it holds exactly
  because `⌊15/bits⌋·bits ≥ 16 - bits`), and that the tail load stays inside the 32-byte
  scratch buffer.
-/
import Kopis.Avx2.SerPlan

open Aeneas Aeneas.Std Result
open RustKopisAvx2

namespace Kopis.Avx2

open Kopis.Properties (streamByte)

set_option maxHeartbeats 1000000

/-! ## The group geometry

`tailGroups w = ⌊15/w⌋` groups are read from the scratch buffer and the other `headGroups w`
directly.  Every bound the two loads need is an inequality between these. -/

/-- Groups read from the zero-padded scratch buffer. -/
def tailGroups (w : ℕ) : ℕ := 15 / w

/-- Groups read directly from `bytes`. -/
def headGroups (w : ℕ) : ℕ := 32 - tailGroups w

/-- Byte offset at which the scratch buffer's copy begins. -/
def tailStart (w : ℕ) : ℕ := headGroups w * w

/-- At most fifteen bytes are copied — the scratch buffer is 32 bytes, so this is what keeps
its 16-byte loads in range. -/
theorem tailGroups_lt (w : ℕ) : tailGroups w ≤ 15 := by
  unfold tailGroups
  exact Nat.div_le_self 15 w

theorem tailGroups_mul (w : ℕ) : tailGroups w < 32 := by
  unfold tailGroups
  have : 15 / w ≤ 15 := Nat.div_le_self 15 w
  omega

/-- **The head bound, and it is tight.**  A group in the head can be loaded whole from `bytes`:
`group·w + 16 ≤ 32·w`.  This holds because `⌊15/w⌋·w > 15 - w`, i.e. the tail was chosen to
start exactly early enough. -/
theorem head_load_in_bounds (w group : ℕ) (hw : 1 ≤ w) (hg : group < headGroups w) :
    group * w + 16 ≤ 32 * w := by
  unfold headGroups tailGroups at hg
  have hdm : w * (15 / w) + 15 % w = 15 := Nat.div_add_mod 15 w
  have hmod : 15 % w < w := Nat.mod_lt _ (by omega)
  have hle : group + 1 ≤ 32 - 15 / w := by omega
  have hmul : (group + 1) * w ≤ (32 - 15 / w) * w := Nat.mul_le_mul_right w hle
  have hexp : (32 - 15 / w) * w = 32 * w - (15 / w) * w := by
    rw [Nat.sub_mul]
  have h15 : (15 / w) * w + 15 % w = 15 := by rw [Nat.mul_comm]; exact hdm
  have hdiv_le : (15 / w) * w ≤ 15 := by omega
  have : group * w + w ≤ 32 * w - (15 / w) * w := by
    rw [← hexp]; rw [Nat.succ_mul] at hmul; exact hmul
  omega

/-- The tail offset of a tail group, and that its 16-byte load fits in the 32-byte buffer. -/
theorem tail_load_in_bounds (w group : ℕ) (hw : 1 ≤ w) (hg32 : group < 32) :
    group * w - tailStart w + 16 ≤ 32 := by
  unfold tailStart headGroups tailGroups at *
  have hdm : w * (15 / w) + 15 % w = 15 := Nat.div_add_mod 15 w
  have hmod : 15 % w < w := Nat.mod_lt _ (by omega)
  have hdvle : 15 / w ≤ 15 := Nat.div_le_self 15 w
  have hmul : group * w ≤ 31 * w := Nat.mul_le_mul_right w (by omega)
  have hhead : (32 - 15 / w) * w = 32 * w - (15 / w) * w := by rw [Nat.sub_mul]
  have h15 : (15 / w) * w + 15 % w = 15 := by rw [Nat.mul_comm]; exact hdm
  omega

/-- The scratch buffer's copy is `⌊15/w⌋·w` bytes — at most fifteen, which is why 32 bytes of
scratch are enough and why the `copy_from_slice` bound cannot overrun. -/
theorem copy_len_le (w : ℕ) (hw : 1 ≤ w) : 32 * w - tailStart w ≤ 15 := by
  unfold tailStart headGroups tailGroups
  have hdm : w * (15 / w) + 15 % w = 15 := Nat.div_add_mod 15 w
  have hdvle : 15 / w ≤ 15 := Nat.div_le_self 15 w
  have hexp : (32 - 15 / w) * w = 32 * w - (15 / w) * w := by rw [Nat.sub_mul]
  have h15 : (15 / w) * w + 15 % w = 15 := by rw [Nat.mul_comm]; exact hdm
  have hmul : (15 / w) * w ≤ 32 * w := Nat.mul_le_mul_right w (by omega)
  omega

/-! ## The broadcast

`vbroadcasti128` puts the same 16 bytes in both halves, so byte `i` of the 256-bit register is
byte `i % 16` of the loaded half — which is why the shuffle control, whose indices are taken
mod 16 within each half, may name any of the group's bytes from any lane. -/

open RustKopisAvx2.backend.avx2.intrinsics in
theorem broadcast_bytes (bytes : Slice U8) (base : ℕ) (v : Vec128) (raw : Vec256)
    (hv : ∀ m < 16, (lane8' v m).toNat = streamByte bytes (base + m))
    (hraw : bits raw = Model.broadcastsi128Si256 (bits' v)) :
    ∀ i < 32, (lane8 raw i).toNat = streamByte bytes (base + i % 16) := by
  intro i hi
  have hhalf : laneOf 128 (bits raw) (i / 16) = bits' v := by
    rw [hraw]
    simp only [Model.broadcastsi128Si256]
    exact laneOf_ofLanes128 _ (by omega)
  have : lane8 raw i = lane8' v (i % 16) := by
    show laneOf 8 (bits raw) i = laneOf 8 (bits' v) (i % 16)
    rw [laneOf_laneOf 8 16 (bits raw) i (by omega), hhalf]
  rw [this, hv _ (by omega)]

end Kopis.Avx2
