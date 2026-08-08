/-
  # Kopis/Keccak/Const.lean — the round constants are the ones in the table.

  FIPS 202 does not hand you the round constants; it *derives* them.  `ι.RC iᵣ` sets bit `2^j - 1`
  of a zero lane to `rc(j + 7iᵣ)` for `j = 0..6`, and `rc t` is an 8-bit LFSR run `t mod 255`
  times (§3.2.5, Algorithms 5 and 6).  `each backend's `keccak.rs`` instead hard-codes the
  familiar 24-entry `RC` table and indexes it.

  Nothing checks that those agree, and a single wrong hex digit would produce a permutation that
  is wrong for every input while still looking exactly like Keccak.  This file checks it, for the
  twelve constants Keccak-p[1600, 12] actually uses.

  ## Which twelve

  `KECCAK_p nr` runs `iᵣ` over `[12 + 2ℓ - nr, 12 + 2ℓ)`, which at `ℓ = 6`, `nr = 12` is
  `[12, 24)` — the *last* twelve of Keccak-f's rounds, per FIPS 202 §3.4.  `keccak::round_const`
  computes `RC[24 - ROUNDS + round] = RC[12 + round]` for `round = 0..11`, so the Rust's `round`
  and the spec's `iᵣ` are related by `iᵣ = 12 + round`, and the two agree entry for entry.

  ## Why `decide +kernel`

  `ι.RC` and `rc` are both `Id.run do` with `for` loops, which the ordinary whnf-based
  `Decidable` evaluator does not reduce — plain `decide` gets stuck.  Kernel reduction handles
  them, and unlike `native_decide` it introduces no axiom: each theorem below has the standard
  `propext`/`Classical.choice`/`Quot.sound` footprint.  It costs about 2.5 s per constant.
-/
import Kopis.Keccak.Round

namespace Kopis.Keccak

set_option maxHeartbeats 4000000

/-- The twelve constants `keccak.rs` reaches, as `RC[12 + round]` — transcribed from the second
half of the `RC` table in `each backend's `keccak.rs``. -/
def rustRC : Vector (BitVec 64) 12 :=
  #v[0x000000008000808b#64, 0x800000000000008b#64, 0x8000000000008089#64, 0x8000000000008003#64,
     0x8000000000008002#64, 0x8000000000000080#64, 0x000000000000800a#64, 0x800000008000000a#64,
     0x8000000080008081#64, 0x8000000000008080#64, 0x0000000080000001#64, 0x8000000080008008#64]

/-! ## Each constant, one theorem each

Stated singly rather than as one `∀ r < 12` so that a failure names the round it is in, and so
that the twelve kernel reductions are twelve independent elaboration steps rather than one. -/

theorem rcWord_12 : rcWord 12 = rustRC[0] := by decide +kernel
theorem rcWord_13 : rcWord 13 = rustRC[1] := by decide +kernel
theorem rcWord_14 : rcWord 14 = rustRC[2] := by decide +kernel
theorem rcWord_15 : rcWord 15 = rustRC[3] := by decide +kernel
theorem rcWord_16 : rcWord 16 = rustRC[4] := by decide +kernel
theorem rcWord_17 : rcWord 17 = rustRC[5] := by decide +kernel
theorem rcWord_18 : rcWord 18 = rustRC[6] := by decide +kernel
theorem rcWord_19 : rcWord 19 = rustRC[7] := by decide +kernel
theorem rcWord_20 : rcWord 20 = rustRC[8] := by decide +kernel
theorem rcWord_21 : rcWord 21 = rustRC[9] := by decide +kernel
theorem rcWord_22 : rcWord 22 = rustRC[10] := by decide +kernel
theorem rcWord_23 : rcWord 23 = rustRC[11] := by decide +kernel

/-- **The hard-coded table is the derived one.**  For each of the twelve rounds Keccak-p[1600,12]
runs, the constant `keccak::round_const` broadcasts is the one FIPS 202's LFSR produces. -/
theorem rcWord_eq_rustRC (round : ℕ) (h : round < 12) :
    rcWord (12 + round) = rustRC[round]'h := by
  match round, h with
  | 0, _ => exact rcWord_12
  | 1, _ => exact rcWord_13
  | 2, _ => exact rcWord_14
  | 3, _ => exact rcWord_15
  | 4, _ => exact rcWord_16
  | 5, _ => exact rcWord_17
  | 6, _ => exact rcWord_18
  | 7, _ => exact rcWord_19
  | 8, _ => exact rcWord_20
  | 9, _ => exact rcWord_21
  | 10, _ => exact rcWord_22
  | 11, _ => exact rcWord_23

end Kopis.Keccak
