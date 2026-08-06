/-
  # Kopis/Avx2/Keccak/Xof4.lean — the four-way XOF, end to end.

  Everything below this file proves one piece of `keccak.rs`: `RoundSpec.lean` the round,
  `Permute.lean` the twelve of them, `Absorb.lean` getting a padded block into the registers,
  `Squeeze.lean` getting bytes back out.  This file is the assembly, and its statement is the one
  the rest of the AVX2 stack wants: lane `l` of `xof4`'s output is the squeeze stream of the
  sponge that absorbed `prefix ‖ suffix_l`, padded to a single block.

  The four sponges never interact, so the whole file is stated at a fixed lane `l < 4`.

  One block is all `xof4` ever absorbs: the Rust `const`-asserts `32 + S < RATE`, so the prefix,
  suffix and domain separator always fit, and `pad_block` produces RFC 9861's `pad10*1` directly.
  That is why there is no absorb *loop* here — only the transpose that gets the block into the
  registers, and the capacity above `RATE` which stays zero from the initial `setzero`.
-/
import Kopis.Avx2.Keccak.Squeeze

open Aeneas Aeneas.Std Result
open RustKopisAvx2
open RustKopisAvx2.backend.avx2.intrinsics
open Kopis.Avx2
open Spec.SHA3

namespace Kopis.Avx2.Keccak

set_option maxHeartbeats 4000000

noncomputable section

/-- **`keccak::xof4` is four independent sponges.**  Lane `l`'s output is the squeeze stream of
the sponge that absorbed `prefix ‖ suffix_l` padded to one block. -/
theorem xof4_spec (RATE : Std.Usize) (DS : Std.U8) {S N : Std.Usize}
    (prefix1 : Std.Array Std.U8 32#usize)
    (suffixes : Std.Array (Std.Array Std.U8 S) 4#usize)
    (out : Std.Array (Std.Array Std.U8 N) 4#usize)
    (l : ℕ) (hl : l < 4)
    (hR : RATE.val = 168 ∨ RATE.val = 136)
    (hDS1 : 1 ≤ DS.val) (hDS2 : DS.val ≤ 127)
    (hS : 32 + S.val + 1 < RATE.val)
    (hNmax : N.val + 232 ≤ Std.Usize.max) :
    backend.avx2.keccak.xof4 RATE DS prefix1 suffixes out
      ⦃ (o : Std.Array (Std.Array Std.U8 N) 4#usize) => ∀ j < N.val,
          ((o.val[l]!).val[j]!).bv
            = squeezeByte (absorbed RATE.val DS prefix1.val (suffixes.val[l]!).val) RATE.val j ⦄
      := by
  unfold backend.avx2.keccak.xof4
  have hRv : RATE.val = 168 ∨ RATE.val = 136 := hR
  -- the four `massert`s
  rw [show (if RATE = 168#usize then ok () else massert (RATE = 136#usize)) = ok () from by
        by_cases h : RATE = 168#usize
        · rw [if_pos h]
        · rw [if_neg h]
          simp only [massert, if_pos (show RATE = 136#usize by scalar_tac)],
      bind_tc_ok,
      show massert (DS ≥ 1#u8) = ok () from by
        simp only [massert, if_pos (show DS ≥ 1#u8 by scalar_tac)],
      bind_tc_ok,
      show massert (DS ≤ 127#u8) = ok () from by
        simp only [massert, if_pos (show DS ≤ 127#u8 by scalar_tac)],
      bind_tc_ok]
  let* ⟨ i, hi ⟩ ← Std.Usize.add_spec (x := 32#usize) (y := S) (by scalar_tac)
  rw [show massert (i < RATE) = ok () from by
        simp only [massert, if_pos (show i < RATE by scalar_tac)], bind_tc_ok]
  have hsl : (suffixes.val : List (Std.Array Std.U8 S)).length = 4 := suffixes.property
  let* ⟨ s0, hs0 ⟩ ← Array.index_usize_spec suffixes 0#usize (by scalar_tac)
  let* ⟨ s1, hs1 ⟩ ← Array.index_usize_spec suffixes 1#usize (by scalar_tac)
  let* ⟨ s2, hs2 ⟩ ← Array.index_usize_spec suffixes 2#usize (by scalar_tac)
  let* ⟨ s3, hs3 ⟩ ← Array.index_usize_spec suffixes 3#usize (by scalar_tac)
  let* ⟨ b0, hb0 ⟩ ← pad_block_spec RATE DS prefix1 s0 hS
  let* ⟨ b1, hb1 ⟩ ← pad_block_spec RATE DS prefix1 s1 hS
  let* ⟨ b2, hb2 ⟩ ← pad_block_spec RATE DS prefix1 s2 hS
  let* ⟨ b3, hb3 ⟩ ← pad_block_spec RATE DS prefix1 s3 hS
  obtain ⟨z, hz, hzb⟩ := setzero_si256_spec
  rw [hz, bind_tc_ok]
  let* ⟨ words, hwords ⟩ ← Std.Usize.div_spec
  have hwv : words.val = RATE.val / 8 := hwords
  have h8w : 8 * words.val = RATE.val := by omega
  have hw25 : words.val ≤ 25 := by omega
  -- the padded block of each lane, pointwise
  have hblk : ∀ l' < 4, ∀ j < RATE.val,
      (inBlk b0 b1 b2 b3 l').val[j]!
        = padByte RATE.val DS prefix1.val (suffixes.val[l']!).val j := by
    intro l' hl' j hj
    have es : ∀ (u : Std.Array Std.U8 S) (k : ℕ) (hk : k < 4),
        u = suffixes.val[k]'(by rw [hsl]; exact hk) → u = suffixes.val[k]! := by
      intro u k hk hu; rw [hu, getElem!_pos]
    rcases (show l' = 0 ∨ l' = 1 ∨ l' = 2 ∨ l' = 3 by omega) with rfl | rfl | rfl | rfl
    · rw [show inBlk b0 b1 b2 b3 0 = b0 from rfl, hb0 j hj,
        ← es s0 0 (by omega) hs0, padByte, s0.property]
    · rw [show inBlk b0 b1 b2 b3 1 = b1 from rfl, hb1 j hj,
        ← es s1 1 (by omega) hs1, padByte, s1.property]
    · rw [show inBlk b0 b1 b2 b3 2 = b2 from rfl, hb2 j hj,
        ← es s2 2 (by omega) hs2, padByte, s2.property]
    · rw [show inBlk b0 b1 b2 b3 3 = b3 from rfl, hb3 j hj,
        ← es s3 3 (by omega) hs3, padByte, s3.property]
  have hrate : 8 * words.val ≤ RATE.val := by omega
  let* ⟨ st1, word, hL1, hL2, hL3, hL4, hL5 ⟩ ← xof4_loop0_spec b0 b1 b2 b3
    (Std.Array.repeat 25#usize z) words 0#usize l hl hw25 hrate (by simp)
    (by intro k hk; simp at hk)
  let* ⟨ st2, hM1, hM2 ⟩ ← xof4_loop1_spec b0 b1 b2 b3 st1 words word l hl hw25 hrate hL3 hL4
  -- the absorbed state
  have hzero : ∀ k, words.val ≤ k → k < 25 → lane64 (st2.val[k]!) l = 0 := by
    intro k hk hk25
    rw [hM2 k hk hk25, hL5 k (by omega) hk25]
    have : (Std.Array.repeat 25#usize z).val[k]! = z := by
      rw [Std.Array.repeat_val,
        getElem!_pos _ k (by rw [List.length_replicate]; exact hk25), List.getElem_replicate]
    rw [this, lane64, hzb]
    simp [laneOf]
  have habs : stateWords st2 l = absorbed RATE.val DS prefix1.val (suffixes.val[l]!).val := by
    funext x y
    rw [stateWords_apply, absorbed]
    by_cases hk : 8 * idx x y < RATE.val
    · rw [if_pos hk, hM1 (idx x y) (by omega)]
      refine leWord64_eq_leWordOf _ _ _ (fun m hm => ?_)
      rw [hblk l hl (8 * idx x y + m) (by omega)]
    · rw [if_neg hk, hzero (idx x y) (by omega) (idx_lt x y)]
  apply WP.spec_mono (xof4_loop2_spec RATE out st2 0#usize l hl (by omega) (by omega)
    (by simp) hNmax)
  rintro r ⟨hrA, hrB⟩ j hj
  rw [hrA j hj (by simp), habs]
  simp

end
end Kopis.Avx2.Keccak
