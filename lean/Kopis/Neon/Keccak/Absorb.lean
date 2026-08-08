/-
  # Kopis/Neon/Keccak/Absorb.lean — getting a padded block into the two sponges.

  `xof2` absorbs one `RATE`-byte block per lane.  The state is 25 registers, register `k` holding
  word `k` of both sponges, one per 64-bit field.

  Two loops do it.  The first takes words *two at a time*: one `ld1` per sponge fetches sixteen
  bytes — words `w` and `w+1` — and `trn1.2d` / `trn2.2d` transpose the pair into registers `w`
  and `w+1`.  The second is the tail, one word at a time through `read8` and `from_le_bytes`,
  for the odd word `RATE / 8` may leave over.
-/
import Kopis.Neon.Keccak.Permute
import Kopis.Keccak.Bytes

open Aeneas Aeneas.Std Result
open RustKopisNeon
open RustKopisNeon.backend.neon.intrinsics
open Kopis.Bits

namespace Kopis.Neon.Keccak

open Kopis.Keccak
open Spec.SHA3

set_option maxHeartbeats 1000000

noncomputable section

/-- **A register lane is the little-endian word of the eight bytes it covers.** -/
theorem lane64_of_bytes (c : Vec128) (bs : List Std.U8) (off j : ℕ) (_hj : j < 2)
    (h : ∀ m < 8, lane8 c (8 * j + m) = (bs[off + m]!).bv) :
    lane64 c j = leWord64 bs off := by
  apply BitVec.eq_of_getLsbD_eq
  intro z hz
  rw [getLsbD_leWord64 _ _ _ hz]
  have hbyte := h (z / 8) (by omega)
  have hlane : (lane64 c j).getLsbD z = (bits c).getLsbD (64 * j + z) := by
    rw [lane64, getLsbD_laneOf]; simp [hz]
  rw [hlane]
  have h2 : (bits c).getLsbD (64 * j + z)
      = (laneOf 8 (bits c) (8 * j + z / 8)).getLsbD (z % 8) := by
    rw [getLsbD_laneOf]
    have : 8 * (8 * j + z / 8) + z % 8 = 64 * j + z := by omega
    simp [this, Nat.mod_lt _ (by norm_num : 0 < 8)]
  rw [h2, show laneOf 8 (bits c) (8 * j + z / 8) = lane8 c (8 * j + z / 8) from rfl, hbyte]

/-- **A register loaded by `load_words` holds two consecutive little-endian words.** -/
theorem lane64_of_load_words {RATE : Std.Usize} (block : Std.Array Std.U8 RATE)
    (word : Std.Usize) (h : 8 * word.val + 16 ≤ RATE.val) :
    ∃ c, backend.neon.keccak.load_words block word = ok c ∧
      ∀ j < 2, lane64 c j = leWord64 block.val (8 * (word.val + j)) := by
  unfold backend.neon.keccak.load_words
  have hlen : block.val.length = RATE.val := block.property
  simp only [lift, bind_tc_ok]
  obtain ⟨i, hi, hiv⟩ := WP.spec_imp_exists
    (Std.Usize.mul_spec (x := 8#usize) (y := word) (by scalar_tac))
  rw [hi, bind_tc_ok]
  have hiv' : i.val = 8 * word.val := by scalar_tac
  have hsv : (Array.to_slice block).val = block.val := rfl
  obtain ⟨c, hc, hcl⟩ := load_u8x16_spec (Array.to_slice block) i (by rw [hsv, hlen]; omega)
  refine ⟨c, by rw [hc], fun j hj => ?_⟩
  refine lane64_of_bytes c block.val (8 * (word.val + j)) j hj (fun m hm => ?_)
  rw [hcl (8 * j + m) (by omega), hsv, hiv']
  congr 2
  omega

/-- The two input blocks, indexed by sponge. -/
def inBlk {RATE : Std.Usize} (b0 b1 : Std.Array Std.U8 RATE) : ℕ → Std.Array Std.U8 RATE :=
  fun l => if l = 0 then b0 else b1

/-! ## The paired loop

Two words per iteration.  `trn1.2d` puts sponge 0's word `w` beside sponge 1's, and `trn2.2d`
does the same for word `w+1`, so one load per sponge fills two registers. -/

theorem xof2_loop0_spec {RATE : Std.Usize} (b0 b1 : Std.Array Std.U8 RATE)
    (state : Std.Array Vec128 25#usize) (words word : Std.Usize) (l : ℕ) (hl : l < 2)
    (hw25 : words.val ≤ 25) (hrate : 8 * words.val ≤ RATE.val) (hword : word.val ≤ words.val) :
    backend.neon.keccak.xof2_loop0 b0 b1 state words word
      ⦃ (p : Std.Array Vec128 25#usize × Std.Usize) =>
          word.val ≤ p.2.val ∧ p.2.val ≤ words.val ∧ words.val < p.2.val + 2 ∧
          (∀ k, word.val ≤ k → k < p.2.val →
            lane64 (p.1.val[k]!) l = leWord64 (inBlk b0 b1 l).val (8 * k)) ∧
          (∀ k < 25, (k < word.val ∨ p.2.val ≤ k) → p.1.val[k]! = state.val[k]!) ⦄ := by
  unfold backend.neon.keccak.xof2_loop0
  have hslen : state.val.length = 25 := state.property
  let* ⟨ i, hi ⟩ ← Std.Usize.add_spec (x := word) (y := 2#usize) (by scalar_tac)
  have hiv : i.val = word.val + 2 := by scalar_tac
  by_cases hle : i ≤ words
  · rw [if_pos hle]
    have hiw : word.val + 2 ≤ words.val := by scalar_tac
    obtain ⟨v0, hv0, hv0l⟩ := lane64_of_load_words b0 word (by omega)
    rw [hv0, bind_tc_ok]
    obtain ⟨v1, hv1, hv1l⟩ := lane64_of_load_words b1 word (by omega)
    rw [hv1, bind_tc_ok]
    obtain ⟨v, hv, hvl0, hvl1⟩ := trn1_64_spec v0 v1
    rw [hv, bind_tc_ok]
    obtain ⟨st1, hst1, hst1v⟩ := WP.spec_imp_exists
      (Std.Array.update_spec state word v (by have := state.property; scalar_tac))
    rw [hst1, bind_tc_ok]
    obtain ⟨v2, hv2, hv2l0, hv2l1⟩ := trn2_64_spec v0 v1
    rw [hv2, bind_tc_ok]
    let* ⟨ i1, hi1 ⟩ ← Std.Usize.add_spec (x := word) (y := 1#usize) (by scalar_tac)
    have hi1v : i1.val = word.val + 1 := by scalar_tac
    obtain ⟨st2, hst2, hst2v⟩ := WP.spec_imp_exists
      (Std.Array.update_spec st1 i1 v2 (by have := st1.property; scalar_tac))
    rw [hst2, bind_tc_ok]
    -- the two registers this iteration wrote
    have hval : ∀ k < 25, st2.val[k]! =
        if k = word.val + 1 then v2 else if k = word.val then v else state.val[k]! := by
      intro k hk
      rw [hst2v, hst1v]
      simp only [Std.Array.set_val_eq]
      rw [getElem!_list_set _ i1.val v2 k (by simp only [List.length_set, hslen]; omega),
        getElem!_list_set _ word.val v k (by rw [hslen]; omega), hi1v]
    have hw0 : lane64 v l = leWord64 (inBlk b0 b1 l).val (8 * word.val) := by
      rcases (show l = 0 ∨ l = 1 from by omega) with rfl | rfl
      · rw [hvl0, hv0l 0 (by omega)]
        simp [inBlk]
      · rw [hvl1, hv1l 0 (by omega)]
        simp [inBlk]
    have hw1 : lane64 v2 l = leWord64 (inBlk b0 b1 l).val (8 * (word.val + 1)) := by
      rcases (show l = 0 ∨ l = 1 from by omega) with rfl | rfl
      · rw [hv2l0, hv0l 1 (by omega)]
        simp [inBlk]
      · rw [hv2l1, hv1l 1 (by omega)]
        simp [inBlk]
    apply WP.spec_mono (xof2_loop0_spec b0 b1 st2 words i l hl hw25 hrate (by omega))
    rintro ⟨r, w'⟩ ⟨h1, h2, h3, h4, h5⟩
    refine ⟨by omega, h2, h3, fun k hk1 hk2 => ?_, fun k hk hout => ?_⟩
    · by_cases hin : word.val + 2 ≤ k
      · exact h4 k (by omega) hk2
      · rw [h5 k (by omega) (Or.inl (by omega)), hval k (by omega)]
        by_cases he : k = word.val + 1
        · subst he; rw [if_pos rfl]; exact hw1
        · have hk0 : k = word.val := by omega
          subst hk0; rw [if_neg he, if_pos rfl]; exact hw0
    · rw [h5 k hk (by omega), hval k hk, if_neg (by omega), if_neg (by omega)]
  · rw [if_neg hle]
    have hgt : words.val < word.val + 2 := by scalar_tac
    refine (WP.spec_ok _).mpr ⟨le_refl _, hword, ?_, ?_, fun k hk hout => rfl⟩
    · show words.val < word.val + 2
      exact hgt
    · intro k hk1 hk2
      exact absurd (show k < word.val from hk2) (by omega)
termination_by words.val - word.val
decreasing_by scalar_decr_tac

/-! ## The tail

`RATE / 8` is odd for both rates Kopis uses (21 and 17), so the paired loop always leaves exactly
one word over.  That one goes through a general-register path: eight bytes copied out, assembled
by `from_le_bytes`, and the two sponges' words joined by `set_u64x2`. -/

/-- **`read8` copies eight consecutive bytes.** -/
theorem read8_spec {RATE : Std.Usize} (block : Std.Array Std.U8 RATE) (offset : Std.Usize)
    (h : offset.val + 8 ≤ RATE.val) :
    backend.neon.keccak.read8 block offset
      ⦃ (a : Std.Array Std.U8 8#usize) => ∀ m < 8, a.val[m]! = block.val[offset.val + m]! ⦄ := by
  unfold backend.neon.keccak.read8
  have hlen : block.val.length = RATE.val := block.property
  step*
  · simp only [Slice.length, s_post1, s1_post2, i_post, Std.Array.repeat_val,
      List.length_replicate]
    scalar_tac
  · intro m hm
    rw [s2_post, s_post2, Std.Array.from_slice_val _ _ (by simp only [s1_post2] at *; scalar_tac),
      s1_post1, show (block.to_slice).val = block.val from rfl,
      List.getElem!_slice offset.val i.val m block.val (by rw [hlen]; scalar_tac)]

/-- **Eight bytes read and reassembled are the little-endian word they spell.** -/
theorem read8_le_val {RATE : Std.Usize} (block : Std.Array Std.U8 RATE) (offset : Std.Usize)
    (h : offset.val + 8 ≤ RATE.val) :
    ∃ a, backend.neon.keccak.read8 block offset = ok a ∧
      (core.num.U64.from_le_bytes a).bv = leWord64 block.val offset.val := by
  obtain ⟨a, hok, ha⟩ := WP.spec_imp_exists (read8_spec block offset h)
  refine ⟨a, hok, ?_⟩
  apply BitVec.eq_of_getLsbD_eq
  intro z hz
  rw [getLsbD_leWord64 _ _ _ hz]
  show (BitVec.fromLEBytes (List.map Std.U8.bv a.val)).getLsbD z = _
  have hL : (List.map Std.U8.bv a.val).length = 8 := by simp
  rw [BitVec.getLsbD_eq_getElem (by rw [hL]; omega), ← BitVec.getElem!_eq_getElem,
    BitVec.fromLEBytes_getElem!,
    show (List.map Std.U8.bv a.val)[z / 8]! = Std.U8.bv (a.val[z / 8]!) from by simp_lists,
    ha (z / 8) (by omega), Byte.testBit, BitVec.getLsbD]

/-- **The tail absorb.**  One word per iteration; afterwards every register below `words` holds
its sponge's little-endian word, and the capacity registers are untouched. -/
theorem xof2_loop1_spec {RATE : Std.Usize} (b0 b1 : Std.Array Std.U8 RATE)
    (state : Std.Array Vec128 25#usize) (words word : Std.Usize) (l : ℕ) (hl : l < 2)
    (hw25 : words.val ≤ 25) (hrate : 8 * words.val ≤ RATE.val) (hword : word.val ≤ words.val)
    (hinv : ∀ k < word.val, lane64 (state.val[k]!) l = leWord64 (inBlk b0 b1 l).val (8 * k)) :
    backend.neon.keccak.xof2_loop1 b0 b1 state words word
      ⦃ (s : Std.Array Vec128 25#usize) =>
          (∀ k < words.val, lane64 (s.val[k]!) l = leWord64 (inBlk b0 b1 l).val (8 * k)) ∧
          (∀ k, words.val ≤ k → k < 25 → s.val[k]! = state.val[k]!) ⦄ := by
  unfold backend.neon.keccak.xof2_loop1
  have hslen : (state.val : List Vec128).length = 25 := state.property
  by_cases hlt : word < words
  · rw [if_pos hlt]
    have hwv : word.val < words.val := by scalar_tac
    let* ⟨ i, hi ⟩ ← Std.Usize.mul_spec (x := 8#usize) (y := word) (by scalar_tac)
    have hiv : i.val = 8 * word.val := by scalar_tac
    obtain ⟨a, ha, hav⟩ := read8_le_val b0 i (by omega)
    rw [ha, bind_tc_ok, show lift (core.num.U64.from_le_bytes a)
      = ok (core.num.U64.from_le_bytes a) from rfl, bind_tc_ok]
    obtain ⟨a1, ha1, ha1v⟩ := read8_le_val b1 i (by omega)
    rw [ha1, bind_tc_ok, show lift (core.num.U64.from_le_bytes a1)
      = ok (core.num.U64.from_le_bytes a1) from rfl, bind_tc_ok]
    obtain ⟨v, hv, hv0, hv1⟩ := set_u64x2_spec (core.num.U64.from_le_bytes a)
      (core.num.U64.from_le_bytes a1)
    rw [hv, bind_tc_ok]
    have hvlane : lane64 v l = leWord64 (inBlk b0 b1 l).val (8 * word.val) := by
      rcases (show l = 0 ∨ l = 1 from by omega) with rfl | rfl
      · rw [hv0, hav, hiv]; simp [inBlk]
      · rw [hv1, ha1v, hiv]; simp [inBlk]
    obtain ⟨st1, hst1, hst1v⟩ := WP.spec_imp_exists
      (Std.Array.update_spec state word v (by have := state.property; scalar_tac))
    rw [hst1, bind_tc_ok]
    let* ⟨ word1, hword1 ⟩ ← Std.Usize.add_spec (x := word) (y := 1#usize) (by scalar_tac)
    have hval : ∀ k < 25, st1.val[k]! = if k = word.val then v else state.val[k]! := by
      intro k hk
      rw [hst1v, Std.Array.set_val_eq,
        getElem!_list_set state.val word.val v k (by rw [hslen]; omega)]
    have hinv' : ∀ k < word1.val,
        lane64 (st1.val[k]!) l = leWord64 (inBlk b0 b1 l).val (8 * k) := by
      intro k hk
      have hk' : k < word.val + 1 := by scalar_tac
      rw [hval k (by omega)]
      rcases (show k < word.val ∨ k = word.val from by omega) with hk2 | rfl
      · rw [if_neg (by omega)]; exact hinv k hk2
      · rw [if_pos rfl]; exact hvlane
    apply WP.spec_mono
      (xof2_loop1_spec b0 b1 st1 words word1 l hl hw25 hrate (by scalar_tac) hinv')
    rintro r ⟨hr1, hr2⟩
    refine ⟨hr1, fun k hk hk25 => ?_⟩
    rw [hr2 k hk hk25, hval k hk25, if_neg (by omega)]
  · rw [if_neg hlt]
    exact (WP.spec_ok _).mpr ⟨fun k hk => hinv k (by scalar_tac), fun k _ _ => rfl⟩
termination_by words.val - word.val
decreasing_by scalar_decr_tac

end

end Kopis.Neon.Keccak
