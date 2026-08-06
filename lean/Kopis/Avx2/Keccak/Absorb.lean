/-
  # Kopis/Avx2/Keccak/Absorb.lean — getting a padded block into the four sponges.

  `xof4` absorbs one `RATE`-byte block per lane.  The state is 25 registers, register `k` holding
  lane `k` of all four sponges, so absorbing means transposing: the four blocks are read
  *along* the byte axis and written *across* the lane axis.

  `keccak.rs` does that four words at a time — `load_words` pulls 32 bytes (four 64-bit words)
  from each block, `transpose4x64` turns those four registers into four registers each holding
  one word of all four blocks — and then finishes whatever words are left one at a time, packing
  them by hand.  This file proves the four-at-a-time part; the tail is in the same shape.

  The bridge to FIPS 202 is `leWord64`.  §B.1 lays a byte string out LSB-first, and §3.1.2 puts
  bit `z` of state word `k` at position `64k + z` of the 1600-bit string, so state word `k` is
  exactly the little-endian 64-bit word at byte offset `8k` — no byte reversal anywhere, which is
  worth stating explicitly because it is the step where an endianness slip would hide.
-/
import Kopis.Avx2.Keccak.Permute

open Aeneas Aeneas.Std Result
open RustKopisAvx2
open RustKopisAvx2.backend.avx2.intrinsics
open Kopis.Avx2
open Spec.SHA3

namespace Kopis.Avx2.Keccak

set_option maxHeartbeats 1000000

noncomputable section

/-- The little-endian 64-bit word at byte offset `off` of a byte list.  This is FIPS 202 §B.1's
byte-to-bit-string convention: byte `i` contributes bits `8i … 8i+7`, LSB first. -/
def leWord64 (bs : List Std.U8) (off : ℕ) : BitVec 64 :=
  BitVec.ofFn fun z => ((bs[off + z.val / 8]!).bv).getLsbD (z.val % 8)

theorem getLsbD_leWord64 (bs : List Std.U8) (off z : ℕ) (hz : z < 64) :
    (leWord64 bs off).getLsbD z = ((bs[off + z / 8]!).bv).getLsbD (z % 8) := by
  rw [BitVec.getLsbD_eq_getElem hz, leWord64, BitVec.getElem_ofFn]

/-- **A register lane is the little-endian word of the eight bytes it covers.**  Lane `j` of a
256-bit register occupies bytes `8j … 8j+7`, so if those bytes are `bs[off …]` then the lane is
`leWord64 bs off`. -/
theorem lane64_of_bytes (c : Vec256) (bs : List Std.U8) (off j : ℕ) (_hj : j < 4)
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

/-- **A register loaded by `load_words` holds four consecutive little-endian words.**  Lane `j`
is the word at byte offset `8 * (word + j)`. -/
theorem lane64_of_load_words {RATE : Std.Usize} (block : Std.Array Std.U8 RATE)
    (word : Std.Usize) (c : Vec256)
    (h : ∀ k < 32, lane8 c k = (block.val[8 * word.val + k]!).bv) (j : ℕ) (hj : j < 4) :
    lane64 c j = leWord64 block.val (8 * (word.val + j)) := by
  refine lane64_of_bytes c block.val _ j hj (fun m hm => ?_)
  rw [h (8 * j + m) (by omega),
    show 8 * word.val + (8 * j + m) = 8 * (word.val + j) + m from by ring]

/-- The four padded input blocks, by lane index — the byte-level companion of `inReg`. -/
def inBlk {RATE : Std.Usize} (b0 b1 b2 b3 : Std.Array Std.U8 RATE) : ℕ → Std.Array Std.U8 RATE
  | 0 => b0
  | 1 => b1
  | 2 => b2
  | _ => b3

/-- **`xof4_loop0` absorbs four words at a time.**  It consumes `word` in steps of four while a
whole group fits, and leaves every register it wrote holding the corresponding little-endian word
of that lane's block. -/
theorem xof4_loop0_spec {RATE : Std.Usize} (b0 b1 b2 b3 : Std.Array Std.U8 RATE)
    (state : Std.Array Vec256 25#usize) (words word : Std.Usize) (l : ℕ) (hl : l < 4)
    (hw : words.val ≤ 25) (hrate : 8 * words.val ≤ RATE.val) (hword : word.val ≤ words.val)
    (hinv : ∀ k < word.val, lane64 (state.val[k]!) l = leWord64 (inBlk b0 b1 b2 b3 l).val (8 * k)) :
    backend.avx2.keccak.xof4_loop0 b0 b1 b2 b3 state words word
      ⦃ ((s : Std.Array Vec256 25#usize), (w : Std.Usize)) =>
          word.val ≤ w.val ∧ words.val < w.val + 4 ∧ w.val ≤ words.val ∧
          (∀ k < w.val, lane64 (s.val[k]!) l = leWord64 (inBlk b0 b1 b2 b3 l).val (8 * k)) ∧
          (∀ k, w.val ≤ k → k < 25 → s.val[k]! = state.val[k]!) ⦄ := by
  unfold backend.avx2.keccak.xof4_loop0
  let* ⟨ i, hi ⟩ ← Std.Usize.add_spec (x := word) (y := 4#usize) (by scalar_tac)
  by_cases hle : i ≤ words
  · rw [if_pos hle]
    have hiv : i.val = word.val + 4 := hi
    have hlev : word.val + 4 ≤ words.val := by scalar_tac
    have hwl : 8 * word.val + 32 ≤ RATE.val := by omega
    let* ⟨ v, hv ⟩ ← load_words_spec b0 word hwl
    let* ⟨ v1, hv1 ⟩ ← load_words_spec b1 word hwl
    let* ⟨ v2, hv2 ⟩ ← load_words_spec b2 word hwl
    let* ⟨ v3, hv3 ⟩ ← load_words_spec b3 word hwl
    obtain ⟨r0, r1, r2, r3, htr, htrl⟩ := transpose4x64_spec v v1 v2 v3
    rw [htr, bind_tc_ok]
    have hlane : ∀ k, k < 4 →
        lane64 (inReg v v1 v2 v3 l) k
          = leWord64 (inBlk b0 b1 b2 b3 l).val (8 * (word.val + k)) := by
      intro k hk
      rcases (show l = 0 ∨ l = 1 ∨ l = 2 ∨ l = 3 by omega) with rfl | rfl | rfl | rfl
      · exact lane64_of_load_words b0 word v hv k hk
      · exact lane64_of_load_words b1 word v1 hv1 k hk
      · exact lane64_of_load_words b2 word v2 hv2 k hk
      · exact lane64_of_load_words b3 word v3 hv3 k hk
    let* ⟨ state1, hst1 ⟩ ← Array.update_spec
    let* ⟨ i1, hi1 ⟩ ← Std.Usize.add_spec (x := word) (y := 1#usize) (by scalar_tac)
    let* ⟨ state2, hst2 ⟩ ← Array.update_spec
    let* ⟨ i2, hi2 ⟩ ← Std.Usize.add_spec (x := word) (y := 2#usize) (by scalar_tac)
    let* ⟨ state3, hst3 ⟩ ← Array.update_spec
    let* ⟨ i3, hi3 ⟩ ← Std.Usize.add_spec (x := word) (y := 3#usize) (by scalar_tac)
    let* ⟨ a, hst4 ⟩ ← Array.update_spec
    have hslen : (state.val : List Vec256).length = 25 := state.property
    have l1 : (state1.val : List Vec256).length = 25 := state1.property
    have l2 : (state2.val : List Vec256).length = 25 := state2.property
    have l3 : (state3.val : List Vec256).length = 25 := state3.property
    have hinv' : ∀ k < i.val, lane64 (a.val[k]!) l
        = leWord64 (inBlk b0 b1 b2 b3 l).val (8 * k) := by
      intro k hk
      rw [hiv] at hk
      rw [hst4, Std.Array.set_val_eq,
        getElem!_list_set state3.val i3.val r3 k (by rw [l3, hi3]; omega), hi3,
        hst3, Std.Array.set_val_eq,
        getElem!_list_set state2.val i2.val r2 k (by rw [l2, hi2]; omega), hi2,
        hst2, Std.Array.set_val_eq,
        getElem!_list_set state1.val i1.val r1 k (by rw [l1, hi1]; omega), hi1,
        hst1, Std.Array.set_val_eq,
        getElem!_list_set state.val word.val r0 k (by rw [hslen]; omega)]
      rcases (show k < word.val ∨ k = word.val ∨ k = word.val + 1 ∨ k = word.val + 2
                ∨ k = word.val + 3 by omega) with h | h | h | h | h
      · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
        exact hinv k h
      · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos h, h,
          (htrl l hl).1, hlane 0 (by norm_num), Nat.add_zero]
      · rw [if_neg (by omega), if_neg (by omega), if_pos h, h,
          (htrl l hl).2.1, hlane 1 (by norm_num)]
      · rw [if_neg (by omega), if_pos h, h,
          (htrl l hl).2.2.1, hlane 2 (by norm_num)]
      · rw [if_pos h, h, (htrl l hl).2.2.2, hlane 3 (by norm_num)]
    have hkeep : ∀ k, word.val + 4 ≤ k → k < 25 → a.val[k]! = state.val[k]! := by
      intro k hk hk25
      rw [hst4, Std.Array.set_val_eq,
        getElem!_list_set state3.val i3.val r3 k (by rw [l3, hi3]; omega), hi3, if_neg (by omega),
        hst3, Std.Array.set_val_eq,
        getElem!_list_set state2.val i2.val r2 k (by rw [l2, hi2]; omega), hi2, if_neg (by omega),
        hst2, Std.Array.set_val_eq,
        getElem!_list_set state1.val i1.val r1 k (by rw [l1, hi1]; omega), hi1, if_neg (by omega),
        hst1, Std.Array.set_val_eq,
        getElem!_list_set state.val word.val r0 k (by rw [hslen]; omega), if_neg (by omega)]
    apply WP.spec_mono
      (xof4_loop0_spec b0 b1 b2 b3 a words i l hl hw hrate (by omega) hinv')
    rintro ⟨s, w⟩ ⟨h1, h2, h3, h4, h5⟩
    exact ⟨by omega, h2, h3, h4, fun k hk hk25 => (h5 k hk hk25).trans (hkeep k (by omega) hk25)⟩
  · rw [if_neg hle]
    simp only [WP.spec_ok]
    exact ⟨le_refl _, by scalar_tac, by scalar_tac, hinv, fun k _ _ => rfl⟩

/-! ## The tail

Whatever words are left after the four-at-a-time pass are absorbed one at a time.  `keccak.rs`
packs the eight bytes of that word from each of the four blocks into a 32-byte buffer — lane `l`
gets bytes `8l … 8l+7` — and loads the buffer in one go, which is the transpose done by hand for
a single word. -/

/-- **The packing loop.**  Byte `8l + i` of the buffer is byte `8·word + i` of block `l`. -/
theorem xof4_loop1_loop0_spec {RATE : Std.Usize} (iter : core.ops.range.Range Std.Usize)
    (b0 b1 b2 b3 : Std.Array Std.U8 RATE) (word : Std.Usize)
    (packed : Std.Array Std.U8 32#usize)
    (hstart : iter.start.val ≤ 8) (hend : iter.«end».val = 8)
    (hbound : 8 * word.val + 8 ≤ RATE.val)
    (hpre : ∀ l < 4, ∀ i < iter.start.val,
      packed.val[8 * l + i]! = (inBlk b0 b1 b2 b3 l).val[8 * word.val + i]!) :
    backend.avx2.keccak.xof4_loop1_loop0 iter b0 b1 b2 b3 word packed
      ⦃ (p : Std.Array Std.U8 32#usize) => ∀ l < 4, ∀ i < 8,
          p.val[8 * l + i]! = (inBlk b0 b1 b2 b3 l).val[8 * word.val + i]! ⦄ := by
  unfold backend.avx2.keccak.xof4_loop1_loop0
  by_cases hlt : iter.start.val < iter.«end».val
  · let* ⟨ o, iter1, ho, hstart', hend' ⟩ ← core.iter.range.IteratorRange.next_Usize_some_spec
    rw [ho]; simp only
    have hi8 : iter.start.val < 8 := by scalar_tac
    have hrlen : ∀ (b : Std.Array Std.U8 RATE), (b.val : List Std.U8).length = RATE.val :=
      fun b => b.property
    let* ⟨ j1, hj1 ⟩ ← Std.Usize.mul_spec (x := 8#usize) (y := word) (by scalar_tac)
    have hj1v : j1.val = 8 * word.val := hj1
    let* ⟨ j2, hj2 ⟩ ← Std.Usize.add_spec (x := j1) (y := iter.start) (by scalar_tac)
    let* ⟨ c0, hc0 ⟩ ← Array.index_usize_spec b0 j2 (by scalar_tac)
    let* ⟨ p1, hp1 ⟩ ← Array.update_spec
    let* ⟨ j4, hj4 ⟩ ← Std.Usize.add_spec (x := j1) (y := iter.start) (by scalar_tac)
    let* ⟨ c1, hc1 ⟩ ← Array.index_usize_spec b1 j4 (by scalar_tac)
    let* ⟨ j6, hj6 ⟩ ← Std.Usize.add_spec (x := 8#usize) (y := iter.start) (by scalar_tac)
    let* ⟨ p2, hp2 ⟩ ← Array.update_spec
    let* ⟨ j7, hj7 ⟩ ← Std.Usize.add_spec (x := j1) (y := iter.start) (by scalar_tac)
    let* ⟨ c2, hc2 ⟩ ← Array.index_usize_spec b2 j7 (by scalar_tac)
    let* ⟨ j9, hj9 ⟩ ← Std.Usize.add_spec (x := 16#usize) (y := iter.start) (by scalar_tac)
    let* ⟨ p3, hp3 ⟩ ← Array.update_spec
    let* ⟨ j10, hj10 ⟩ ← Std.Usize.add_spec (x := j1) (y := iter.start) (by scalar_tac)
    let* ⟨ c3, hc3 ⟩ ← Array.index_usize_spec b3 j10 (by scalar_tac)
    let* ⟨ j12, hj12 ⟩ ← Std.Usize.add_spec (x := 24#usize) (y := iter.start) (by scalar_tac)
    let* ⟨ a, hp4 ⟩ ← Array.update_spec
    have plen : ∀ (q : Std.Array Std.U8 32#usize), (q.val : List Std.U8).length = 32 :=
      fun q => q.property
    have hread : ∀ n < 32, a.val[n]! =
        if n = 24 + iter.start.val then c3
        else if n = 16 + iter.start.val then c2
        else if n = 8 + iter.start.val then c1
        else if n = iter.start.val then c0
        else packed.val[n]! := by
      intro n hn
      rw [hp4, Std.Array.set_val_eq,
        getElem!_list_set p3.val j12.val c3 n (by rw [plen, hj12]; omega), hj12,
        hp3, Std.Array.set_val_eq,
        getElem!_list_set p2.val j9.val c2 n (by rw [plen, hj9]; omega), hj9,
        hp2, Std.Array.set_val_eq,
        getElem!_list_set p1.val j6.val c1 n (by rw [plen, hj6]; omega), hj6,
        hp1, Std.Array.set_val_eq,
        getElem!_list_set packed.val iter.start.val c0 n (by rw [plen]; omega)]
    have hbn : 8 * word.val + iter.start.val < RATE.val := by omega
    -- move the four block reads to `getElem!` so the index can be rewritten without a
    -- dependent motive (the `getElem` form carries its bound proof in the term)
    have e0 : c0 = b0.val[8 * word.val + iter.start.val]! := by
      have h := hc0.trans (getElem!_pos b0.val j2.val (by scalar_tac)).symm
      rwa [hj2, hj1v] at h
    have e1 : c1 = b1.val[8 * word.val + iter.start.val]! := by
      have h := hc1.trans (getElem!_pos b1.val j4.val (by scalar_tac)).symm
      rwa [hj4, hj1v] at h
    have e2 : c2 = b2.val[8 * word.val + iter.start.val]! := by
      have h := hc2.trans (getElem!_pos b2.val j7.val (by scalar_tac)).symm
      rwa [hj7, hj1v] at h
    have e3 : c3 = b3.val[8 * word.val + iter.start.val]! := by
      have h := hc3.trans (getElem!_pos b3.val j10.val (by scalar_tac)).symm
      rwa [hj10, hj1v] at h
    have hpre' : ∀ l < 4, ∀ m < iter1.start.val,
        a.val[8 * l + m]! = (inBlk b0 b1 b2 b3 l).val[8 * word.val + m]! := by
      intro l hl m hm
      rw [hstart'] at hm
      rw [hread (8 * l + m) (by omega)]
      rcases (show m < iter.start.val ∨ m = iter.start.val by omega) with h | h
      · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
        exact hpre l hl m h
      · subst h
        rcases (show l = 0 ∨ l = 1 ∨ l = 2 ∨ l = 3 by omega) with rfl | rfl | rfl | rfl
        · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega),
            e0, inBlk]
        · rw [if_neg (by omega), if_neg (by omega), if_pos (by omega),
            e1, inBlk]
        · rw [if_neg (by omega), if_pos (by omega),
            e2, inBlk]
        · rw [if_pos (by omega), e3]
          rfl
    apply WP.spec_mono
      (xof4_loop1_loop0_spec iter1 b0 b1 b2 b3 word a
        (by rw [hstart']; scalar_tac) (by rw [hend']; exact hend) hbound hpre')
    intro r hr
    exact hr
  · let* ⟨ o, iter1, hnone, _ ⟩ ← core.iter.range.IteratorRange.next_Usize_none_spec
    rw [hnone]; simp only [WP.spec_ok]
    have hge : iter.start.val = 8 := by scalar_tac
    intro l hl i hi
    exact hpre l hl i (by omega)

/-- **The tail absorb.**  One word per iteration, packed by hand and loaded in one go; after it
every register below `words` holds its lane's little-endian word. -/
theorem xof4_loop1_spec {RATE : Std.Usize} (b0 b1 b2 b3 : Std.Array Std.U8 RATE)
    (state : Std.Array Vec256 25#usize) (words word : Std.Usize) (l : ℕ) (hl : l < 4)
    (hw : words.val ≤ 25) (hrate : 8 * words.val ≤ RATE.val) (hword : word.val ≤ words.val)
    (hinv : ∀ k < word.val, lane64 (state.val[k]!) l = leWord64 (inBlk b0 b1 b2 b3 l).val (8 * k)) :
    backend.avx2.keccak.xof4_loop1 b0 b1 b2 b3 state words word
      ⦃ (s : Std.Array Vec256 25#usize) =>
          (∀ k < words.val, lane64 (s.val[k]!) l = leWord64 (inBlk b0 b1 b2 b3 l).val (8 * k)) ∧
          (∀ k, words.val ≤ k → k < 25 → s.val[k]! = state.val[k]!) ⦄ := by
  unfold backend.avx2.keccak.xof4_loop1
  by_cases hlt : word < words
  · rw [if_pos hlt]
    have hwv : word.val < words.val := by scalar_tac
    let* ⟨ packed1, hpk ⟩ ← xof4_loop1_loop0_spec { start := 0#usize, «end» := 8#usize }
      b0 b1 b2 b3 word (Std.Array.repeat 32#usize 0#u8) (by simp) rfl (by omega)
      (by intro l' hl' i hi; simp at hi)
    obtain ⟨v, hv, hvl⟩ := load_u8x32_spec packed1 0#usize (by simp)
    rw [hv, bind_tc_ok]
    have hvlane : lane64 v l = leWord64 (inBlk b0 b1 b2 b3 l).val (8 * word.val) := by
      refine lane64_of_bytes v _ _ l hl (fun m hm => ?_)
      rw [hvl (8 * l + m) (by omega), show ((0#usize : Std.Usize) : ℕ) + (8 * l + m)
        = 8 * l + m from by simp, hpk l hl m hm]
    let* ⟨ a, ha ⟩ ← Array.update_spec
    let* ⟨ word1, hword1 ⟩ ← Std.Usize.add_spec (x := word) (y := 1#usize) (by scalar_tac)
    have hslen : (state.val : List Vec256).length = 25 := state.property
    have hinv' : ∀ k < word1.val,
        lane64 (a.val[k]!) l = leWord64 (inBlk b0 b1 b2 b3 l).val (8 * k) := by
      intro k hk
      rw [hword1] at hk
      rw [ha, Std.Array.set_val_eq,
        getElem!_list_set state.val word.val v k (by rw [hslen]; omega)]
      rcases (show k < word.val ∨ k = word.val by omega) with h | h
      · rw [if_neg (by omega)]; exact hinv k h
      · rw [if_pos h, h, hvlane]
    have hkeep : ∀ k, words.val ≤ k → k < 25 → a.val[k]! = state.val[k]! := by
      intro k hk hk25
      rw [ha, Std.Array.set_val_eq,
        getElem!_list_set state.val word.val v k (by rw [hslen]; omega), if_neg (by omega)]
    apply WP.spec_mono
      (xof4_loop1_spec b0 b1 b2 b3 a words word1 l hl hw hrate (by scalar_tac) hinv')
    rintro r ⟨hr1, hr2⟩
    exact ⟨hr1, fun k hk hk25 => (hr2 k hk hk25).trans (hkeep k hk hk25)⟩
  · rw [if_neg hlt]
    simp only [WP.spec_ok]
    exact ⟨fun k hk => hinv k (by scalar_tac), fun k _ _ => trivial⟩
  termination_by words.val - word.val
  decreasing_by scalar_decr_tac

/-! ## The padded block, and the state it absorbs to -/

/-- Byte `j` of the padded block, exactly as `pad_block_spec` describes it: the 32-byte prefix,
the suffix, the domain separator, zeros, and `0x80` in the last byte — RFC 9861's one-block
`pad10*1`. -/
def padByte (RATE : ℕ) (DS : Std.U8) (pre suf : List Std.U8) (j : ℕ) : Std.U8 :=
  if j < 32 then pre[j]!
  else if j < 32 + suf.length then suf[j - 32]!
  else if j = 32 + suf.length then DS
  else if j = RATE - 1 then 128#u8
  else 0#u8

/-- The little-endian 64-bit word at byte offset `off` of a byte *function* — the same reading as
`leWord64`, but of something described pointwise rather than stored in a list. -/
def leWordOf (f : ℕ → Std.U8) (off : ℕ) : BitVec 64 :=
  BitVec.ofFn fun z => ((f (off + z.val / 8)).bv).getLsbD (z.val % 8)

theorem leWord64_eq_leWordOf (bs : List Std.U8) (f : ℕ → Std.U8) (off : ℕ)
    (h : ∀ m < 8, bs[off + m]! = f (off + m)) :
    leWord64 bs off = leWordOf f off := by
  apply BitVec.eq_of_getLsbD_eq
  intro z hz
  rw [getLsbD_leWord64 _ _ _ hz, leWordOf, BitVec.getLsbD_eq_getElem hz, BitVec.getElem_ofFn,
    h (z / 8) (by omega)]

/-- **The state after absorbing one padded block.**  Register `k` is the little-endian word at
byte offset `8k` of the block for `8k < RATE`, and zero above that — the capacity, which the
sponge never touches on absorb. -/
def absorbed (RATE : ℕ) (DS : Std.U8) (pre suf : List Std.U8) : Words :=
  fun x y => if 8 * idx x y < RATE then leWordOf (padByte RATE DS pre suf) (8 * idx x y) else 0

end
end Kopis.Avx2.Keccak
