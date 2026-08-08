/-
  # Kopis/Neon/Keccak/Squeeze.lean — getting the permuted state back out.

  The squeeze is the absorb run backwards.  `keccak.rs` reads two registers, transposes them with
  `trn1.2d` / `trn2.2d` so each output register carries two consecutive words of one sponge, and
  stores sixteen bytes into that sponge's output array; whatever is left over, or would run past
  the end of the output, is written eight bytes at a time and clipped.

  `stateByte` is the squeeze's view of the state — byte `k` of sponge `l` is byte `k % 8` of the
  word in register `k / 8` — and it is the mirror of `Bytes.lean`'s `leWord64`.  The two agree
  because `Kopis/Keccak/SpecState.lean` identifies both with the spec's byte-level sponge state.
-/
import Kopis.Neon.Keccak.Absorb
import Kopis.Keccak.SpecState
import Kopis.Keccak.Squeeze

open Aeneas Aeneas.Std Result
open RustKopisNeon
open RustKopisNeon.backend.neon.intrinsics
open Kopis.Bits

namespace Kopis.Neon.Keccak

open Kopis.Keccak
open Spec.SHA3

set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

noncomputable section

/-- Byte `k` of sponge `l`'s state: byte `k % 8` of the word held in register `k / 8`.  This is
the squeeze's view of the state, and the mirror of `leWord64`'s absorb view. -/
def stateByte (state : Std.Array Vec128 25#usize) (l k : ℕ) : BitVec 8 :=
  laneOf 8 (lane64 (state.val[k / 8]!) l) (k % 8)

/-- The two output buffers, indexed by sponge — the squeeze's `inBlk`. -/
def outOf {N : Std.Usize} (o0 o1 : Std.Array Std.U8 N) : ℕ → Std.Array Std.U8 N :=
  fun l => if l = 0 then o0 else o1

/-- **A register's bytes are its lanes' bytes.**  `lane8 c k` is byte `k % 8` of lane `k / 8` —
the decomposition every store in the squeeze goes through. -/
theorem lane8_eq_lane64_byte (c : Vec128) (k : ℕ) :
    lane8 c k = laneOf 8 (lane64 c (k / 8)) (k % 8) := by
  simp only [lane8, lane64]
  exact laneOf_laneOf 8 8 (bits c) k (by norm_num)

/-- The bytes a transposed register contributes to the output stream.  `trn1.2d` and `trn2.2d`
each put words `word` and `word + 1` of one sponge into lanes 0 and 1, so the register's sixteen
bytes are state bytes `8·word … 8·word + 15` of that sponge. -/
theorem lane8_trn (state : Std.Array Vec128 25#usize) (t : Vec128) (word l : ℕ)
    (h0 : lane64 t 0 = lane64 (state.val[word]!) l)
    (h1 : lane64 t 1 = lane64 (state.val[word + 1]!) l)
    (k : ℕ) (hk : k < 16) :
    lane8 t k = stateByte state l (8 * word + k) := by
  rw [lane8_eq_lane64_byte, stateByte]
  by_cases hk8 : k < 8
  · rw [show k / 8 = 0 from by omega, h0, show (8 * word + k) / 8 = word from by omega,
      show (8 * word + k) % 8 = k % 8 from by omega]
  · rw [show k / 8 = 1 from by omega, h1, show (8 * word + k) / 8 = word + 1 from by omega,
      show (8 * word + k) % 8 = k % 8 from by omega]

/-- **The sixteen-byte squeeze store.**  Reads two registers, transposes them so each output
register carries one sponge's words `word` and `word + 1`, and stores those sixteen bytes into
that sponge's output at `done + 8·word`.  Stops when either the register pair or the output
window runs out; the tail loop picks up from the word it stopped at. -/
theorem xof2_loop2_loop0_spec {N : Std.Usize} (state : Std.Array Vec128 25#usize)
    (out0 out1 : Std.Array Std.U8 N) (done words word : Std.Usize)
    (hw : words.val ≤ 25) (hword : word.val ≤ words.val)
    (hmax : done.val + 8 * words.val + 16 ≤ Std.Usize.max) :
    backend.neon.keccak.xof2_loop2_loop0 state out0 out1 done words word
      ⦃ (p : Std.Array Std.U8 N × Std.Array Std.U8 N × Std.Usize) =>
          word.val ≤ p.2.2.val ∧ p.2.2.val ≤ words.val ∧
          ∀ l < 2, ∀ j < N.val,
            ((outOf p.1 p.2.1 l).val[j]!).bv =
              if done.val + 8 * word.val ≤ j ∧ j < done.val + 8 * p.2.2.val
              then stateByte state l (j - done.val)
              else ((outOf out0 out1 l).val[j]!).bv ⦄ := by
  unfold backend.neon.keccak.xof2_loop2_loop0
  have h0len : (out0.val : List Std.U8).length = N.val := out0.property
  have h1len : (out1.val : List Std.U8).length = N.val := out1.property
  have hslen : (state.val : List Vec128).length = 25 := state.property
  let* ⟨ i, hi ⟩ ← Std.Usize.add_spec (x := word) (y := 2#usize) (by scalar_tac)
  by_cases hle : i ≤ words
  · rw [if_pos hle]
    have hiw : word.val + 2 ≤ words.val := by scalar_tac
    let* ⟨ i1, hi1 ⟩ ← Std.Usize.mul_spec (x := 8#usize) (y := word) (by scalar_tac)
    let* ⟨ i2, hi2 ⟩ ← Std.Usize.add_spec (x := done) (y := i1) (by scalar_tac)
    let* ⟨ i3, hi3 ⟩ ← Std.Usize.add_spec (x := i2) (y := 16#usize) (by scalar_tac)
    by_cases hfit : i3 ≤ N
    · rw [if_pos hfit]
      have hfitv : done.val + 8 * word.val + 16 ≤ N.val := by scalar_tac
      let* ⟨ v, hv ⟩ ← Array.index_usize_spec state word (by scalar_tac)
      let* ⟨ i4, hi4 ⟩ ← Std.Usize.add_spec (x := word) (y := 1#usize) (by scalar_tac)
      let* ⟨ v1, hv1 ⟩ ← Array.index_usize_spec state i4 (by scalar_tac)
      obtain ⟨v0, hv0, hv0a, hv0b⟩ := trn1_64_spec v v1
      rw [hv0, bind_tc_ok]
      let* ⟨ v2, hv2 ⟩ ← Array.index_usize_spec state i4 (by scalar_tac)
      obtain ⟨v11, hv11, hv11a, hv11b⟩ := trn2_64_spec v v2
      rw [hv11, bind_tc_ok]
      let* ⟨ start, hstart ⟩ ← Std.Usize.add_spec (x := done) (y := i1) (by scalar_tac)
      -- the two lane reads, as state registers
      have hvs : v = state.val[word.val]! := by rw [hv, getElem!_pos _ _ (by rw [hslen]; scalar_tac)]
      have hi4v : i4.val = word.val + 1 := by scalar_tac
      have hv1s : v1 = state.val[word.val + 1]! := by
        rw [hv1, ← getElem!_pos state.val i4.val (by rw [hslen]; scalar_tac), hi4v]
      have hv2s : v2 = state.val[word.val + 1]! := by
        rw [hv2, ← getElem!_pos state.val i4.val (by rw [hslen]; scalar_tac), hi4v]
      have hbyte0 : ∀ k < 16, lane8 v0 k = stateByte state 0 (8 * word.val + k) :=
        fun k hk => lane8_trn state v0 word.val 0 (by rw [hv0a, hvs])
          (by rw [hv0b, hv1s]) k hk
      have hbyte1 : ∀ k < 16, lane8 v11 k = stateByte state 1 (8 * word.val + k) :=
        fun k hk => lane8_trn state v11 word.val 1 (by rw [hv11a, hvs])
          (by rw [hv11b, hv2s]) k hk
      -- store into sponge 0
      let* ⟨ d0, b0, hd0, hb0 ⟩ ← Std.Array.to_slice_mut_spec out0
      obtain ⟨s1, hs1, hs1len, hs1v⟩ := store_u8x16_spec d0 start v0
        (by rw [hd0, h0len]; scalar_tac)
      rw [hs1, bind_tc_ok]
      let* ⟨ d1, b1, hd1, hb1 ⟩ ← Std.Array.to_slice_mut_spec out1
      obtain ⟨s3, hs3, hs3len, hs3v⟩ := store_u8x16_spec d1 start v11
        (by rw [hd1, h1len]; scalar_tac)
      rw [hs3, bind_tc_ok]
      -- the two updated arrays
      have hout0 : ∀ j < N.val, (((b0 s1).val)[j]!).bv =
          if done.val + 8 * word.val ≤ j ∧ j < done.val + 8 * word.val + 16
          then stateByte state 0 (j - done.val) else ((out0.val)[j]!).bv := by
        intro j hj
        rw [hb0, Std.Array.from_slice_val _ _ (by rw [hs1len, hd0]; exact h0len),
          hs1v j (by rw [hd0, h0len]; omega)]
        by_cases hin : start.val ≤ j ∧ j < start.val + 16
        · rw [if_pos hin, if_pos (by scalar_tac),
            hbyte0 (j - start.val) (by omega)]
          congr 1
          scalar_tac
        · rw [if_neg hin, if_neg (by scalar_tac), hd0]
      have hout1 : ∀ j < N.val, (((b1 s3).val)[j]!).bv =
          if done.val + 8 * word.val ≤ j ∧ j < done.val + 8 * word.val + 16
          then stateByte state 1 (j - done.val) else ((out1.val)[j]!).bv := by
        intro j hj
        rw [hb1, Std.Array.from_slice_val _ _ (by rw [hs3len, hd1]; exact h1len),
          hs3v j (by rw [hd1, h1len]; omega)]
        by_cases hin : start.val ≤ j ∧ j < start.val + 16
        · rw [if_pos hin, if_pos (by scalar_tac),
            hbyte1 (j - start.val) (by omega)]
          congr 1
          scalar_tac
        · rw [if_neg hin, if_neg (by scalar_tac), hd1]
      apply WP.spec_mono (xof2_loop2_loop0_spec state (b0 s1) (b1 s3) done words i hw
        (by scalar_tac) hmax)
      rintro ⟨r0, r1, w'⟩ ⟨hr1, hr2, hr3⟩
      refine ⟨by scalar_tac, hr2, fun l hl j hj => ?_⟩
      rw [hr3 l hl j hj]
      have hstep : ((outOf (b0 s1) (b1 s3) l).val[j]!).bv
          = if done.val + 8 * word.val ≤ j ∧ j < done.val + 8 * word.val + 16
            then stateByte state l (j - done.val) else ((outOf out0 out1 l).val[j]!).bv := by
        rcases (show l = 0 ∨ l = 1 from by omega) with rfl | rfl
        · simpa [outOf] using hout0 j hj
        · simpa [outOf] using hout1 j hj
      by_cases hnew : done.val + 8 * i.val ≤ j ∧ j < done.val + 8 * w'.val
      · rw [if_pos hnew, if_pos (show done.val + 8 * word.val ≤ j
          ∧ j < done.val + 8 * w'.val from ⟨by scalar_tac, hnew.2⟩)]
      · rw [if_neg hnew, hstep]
        by_cases hold : done.val + 8 * word.val ≤ j ∧ j < done.val + 8 * word.val + 16
        · rw [if_pos hold, if_pos (by scalar_tac)]
        · rw [if_neg hold, if_neg (by scalar_tac)]
    · rw [if_neg hfit]
      refine (WP.spec_ok _).mpr ⟨le_refl _, hword, fun l hl j hj => ?_⟩
      show ((outOf out0 out1 l).val[j]!).bv
        = if done.val + 8 * word.val ≤ j ∧ j < done.val + 8 * word.val then _ else _
      rw [if_neg (by omega)]
  · rw [if_neg hle]
    refine (WP.spec_ok _).mpr ⟨le_refl _, hword, fun l hl j hj => ?_⟩
    show ((outOf out0 out1 l).val[j]!).bv
      = if done.val + 8 * word.val ≤ j ∧ j < done.val + 8 * word.val then _ else _
    rw [if_neg (by omega)]
termination_by words.val - word.val
decreasing_by scalar_decr_tac

/-- `core.cmp.min` at `Usize` is the plain conditional. -/
theorem min_usize_eq (a b : Std.Usize) :
    core.cmp.min core.cmp.OrdUsize a b = ok (if a.val < b.val then a else b) := by
  unfold core.cmp.min core.cmp.OrdUsize
  simp only [liftFun2, core.cmp.impls.OrdUsize.min]
  rfl

/-- **The tail word loop.**  One state register per iteration: stored to a sixteen-byte buffer,
whose two halves are the two sponges' words, then clipped to what is left of each output. -/
theorem xof2_loop2_loop1_spec {N : Std.Usize} (state : Std.Array Vec128 25#usize)
    (out0 out1 : Std.Array Std.U8 N) (done words word : Std.Usize)
    (hw : words.val ≤ 25) (hword : word.val ≤ words.val)
    (hfit : ∀ w, w < words.val → done.val + 8 * w < N.val) :
    backend.neon.keccak.xof2_loop2_loop1 state out0 out1 done words word
      ⦃ (p : Std.Array Std.U8 N × Std.Array Std.U8 N) =>
          ∀ l < 2, ∀ j < N.val,
            ((outOf p.1 p.2 l).val[j]!).bv =
              if done.val + 8 * word.val ≤ j ∧ j < done.val + 8 * words.val
              then stateByte state l (j - done.val)
              else ((outOf out0 out1 l).val[j]!).bv ⦄ := by
  unfold backend.neon.keccak.xof2_loop2_loop1
  by_cases hlt : word < words
  · rw [if_pos hlt]
    have hwv : word.val < words.val := by scalar_tac
    have hstN : done.val + 8 * word.val < N.val := hfit word.val hwv
    step*
    -- the sixteen-byte buffer holds register `word`: sponge 0's word low, sponge 1's high
    obtain ⟨pk, hpk, hpklen, hpkv⟩ := store_u8x16_spec s 0#usize v (by simp [s_post1])
    rw [hpk, bind_tc_ok]
    have hpkl16 : pk.val.length = 16 := by rw [hpklen, s_post1]; simp
    have hpackv : (to_slice_mut_back pk).val = pk.val := by
      rw [s_post2]; exact Std.Array.from_slice_val _ _ hpkl16
    have hvv : v = state.val[word.val]! := by
      rw [v_post, ← getElem!_pos _ _ (by have := state.property; scalar_tac)]
    have hpkstate : ∀ l < 2, ∀ m < 8,
        ((to_slice_mut_back pk).val[8 * l + m]!).bv = stateByte state l (8 * word.val + m) := by
      intro l hl m hm
      rw [hpackv, hpkv (8 * l + m) (by rw [s_post1]; simp; omega)]
      simp only [show ((0#usize : Std.Usize) : ℕ) = 0 from rfl, Nat.zero_add, Nat.sub_zero,
        if_pos (show (0:ℕ) ≤ 8 * l + m ∧ 8 * l + m < 0 + 16 by omega)]
      rw [lane8_eq_lane64_byte, stateByte,
        show (8 * l + m) / 8 = l from by omega, show (8 * l + m) % 8 = m from by omega,
        show (8 * word.val + m) / 8 = word.val from by omega,
        show (8 * word.val + m) % 8 = m from by omega, hvv]
    have hpktl : (Std.Array.to_slice (to_slice_mut_back pk)).length = 16 := by
      simp only [Std.Slice.length,
        show (Std.Array.to_slice (to_slice_mut_back pk)).val = (to_slice_mut_back pk).val from rfl,
        hpackv, hpkl16]
    step*
    rw [min_usize_eq, bind_tc_ok]
    step*
    · split <;> scalar_tac
    · split_ifs at i2_post <;> scalar_tac
    · rw [hpktl]; split <;> scalar_tac
    · scalar_tac
    · scalar_tac
    · rw [hpktl]; split_ifs at i3_post <;> scalar_tac
    · scalar_tac
    · -- what this iteration wrote
      rename_i l' j'
      have hout0len : out0.val.length = N.val := out0.property
      have hout1len : out1.val.length = N.val := out1.property
      have hpkval : (Std.Array.to_slice (to_slice_mut_back pk)).val = pk.val := by
        rw [show (Std.Array.to_slice (to_slice_mut_back pk)).val
          = (to_slice_mut_back pk).val from rfl, hpackv]
      have hpkb : ∀ l < 2, ∀ m < 8,
          ((pk.val)[8 * l + m]!).bv = stateByte state l (8 * word.val + m) := by
        intro l hl m hm; have h := hpkstate l hl m hm; rwa [hpackv] at h
      have h3len : s3.val.length = i3.val - 8 := by
        have h := s3_post2; simp only [Std.Slice.length] at h
        have h' := i3_post; have h'' := i2_post; omega
      have h6len : s6.val.length = i3.val - 8 := by
        have h := s6_post2; simp only [Std.Slice.length] at h; omega
      have h3v : s3.val = List.slice 0 (i3.val - 8) pk.val := by
        rw [s3_post1, hpkval]; congr 1; have h' := i3_post; omega
      have h6v : s6.val = List.slice 8 (8 + (i3.val - 8)) pk.val := by
        rw [s6_post1, hpkval]; congr 1; omega
      have hi2 : i2.val = start.val + (i3.val - 8) := by
        have h' := i3_post; have h'' := i2_post; omega
      have e8 : ((8#usize : Std.Usize) : ℕ) = 8 := rfl
      have hub : i3.val ≤ 16 := by split_ifs at i3_post <;> omega
      have hub2 : i2.val ≤ start.val + 8 := by omega
      have hcov : ∀ k, k < N.val → start.val ≤ k → k < start.val + 8 → k < i2.val := by
        intro k hk1 hk2 hk3; split_ifs at i2_post <;> omega
      have hw0 : ∀ k < N.val, (((index_mut_back s4).val)[k]!).bv =
          if start.val ≤ k ∧ k < i2.val then stateByte state 0 (k - done.val)
          else ((out0.val)[k]!).bv := by
        intro k hk
        rw [s2_post3 s4, s4_post]
        by_cases hin : start.val ≤ k ∧ k < i2.val
        · rw [if_pos hin, List.getElem!_setSlice!_middle out0.val s3.val start.val k
            ⟨hin.1, by rw [h3len]; omega, by omega⟩, h3v,
            List.getElem!_slice 0 (i3.val - 8) (k - start.val) pk.val
              ⟨by rw [hpkl16]; omega, by omega⟩]
          have h := hpkb 0 (by omega) (k - start.val) (by omega)
          simp only [Nat.mul_zero, Nat.zero_add] at h ⊢
          rw [h]
          congr 1
          have h' := start_post; have h'' := i_post
          omega
        · rw [if_neg hin, List.getElem!_setSlice!_same out0.val s3.val start.val k
            (by rw [h3len]; omega)]
      have hw1 : ∀ k < N.val, (((index_mut_back1 s7).val)[k]!).bv =
          if start.val ≤ k ∧ k < i2.val then stateByte state 1 (k - done.val)
          else ((out1.val)[k]!).bv := by
        intro k hk
        rw [s5_post3 s7, s7_post]
        by_cases hin : start.val ≤ k ∧ k < i2.val
        · rw [if_pos hin, List.getElem!_setSlice!_middle out1.val s6.val start.val k
            ⟨hin.1, by rw [h6len]; omega, by omega⟩, h6v,
            List.getElem!_slice 8 (8 + (i3.val - 8)) (k - start.val) pk.val
              ⟨by rw [hpkl16]; omega, by omega⟩]
          have h := hpkb 1 (by omega) (k - start.val) (by omega)
          simp only [Nat.mul_one] at h ⊢
          rw [h]
          congr 1
          have h' := start_post; have h'' := i_post
          omega
        · rw [if_neg hin, List.getElem!_setSlice!_same out1.val s6.val start.val k
            (by rw [h6len]; omega)]
      rw [p_post1 l' p_post2 j' p_post3]
      have hstep : ((outOf (index_mut_back s4) (index_mut_back1 s7) l').val[j']!).bv
          = if start.val ≤ j' ∧ j' < i2.val then stateByte state l' (j' - done.val)
            else ((outOf out0 out1 l').val[j']!).bv := by
        rcases (show l' = 0 ∨ l' = 1 from by omega) with rfl | rfl
        · simpa [outOf] using hw0 j' p_post3
        · simpa [outOf] using hw1 j' p_post3
      have hstartv : start.val = done.val + 8 * word.val := by
        have h' := start_post; have h'' := i_post; omega
      have hword1v : word1.val = word.val + 1 := word1_post
      by_cases hnew : done.val + 8 * word1.val ≤ j' ∧ j' < done.val + 8 * words.val
      · rw [if_pos hnew, if_pos ⟨by omega, hnew.2⟩]
      · rw [if_neg hnew, hstep]
        by_cases hin : start.val ≤ j' ∧ j' < i2.val
        · rw [if_pos hin, if_pos ⟨by omega, by omega⟩]
        · rw [if_neg hin, if_neg (fun hc =>
            hin ⟨by omega, hcov j' p_post3 (by omega) (by omega)⟩)]
  · rw [if_neg hlt]
    refine (WP.spec_ok _).mpr (fun l hl j hj => ?_)
    show ((outOf out0 out1 l).val[j]!).bv
      = if done.val + 8 * word.val ≤ j ∧ j < done.val + 8 * words.val then _ else _
    rw [if_neg (by scalar_tac)]
termination_by words.val - word.val
decreasing_by scalar_decr_tac

/-! ## The sponge squeeze

The outer loop permutes at the top of each output block.  The spec's `absorb` likewise ends with
a permutation before `squeeze` emits anything, so the two agree on the first block as well as on
the ones after it — `squeezeByte` below is that shared indexing. -/

/-- `usize::div_ceil` is a compiler intrinsic; charon does not translate its body, so aeneas
leaves it opaque.  This is its meaning.  Kopis calls it once, to turn a byte count into a word
count, so the assumption is exactly `⌈take / 8⌉`. -/
@[step] axiom Usize.div_ceil_spec (x y : Std.Usize) (h : 0 < y.val) :
    core.num.Usize.div_ceil x y ⦃ (r : Std.Usize) => r.val = (x.val + y.val - 1) / y.val ⦄

/-- The two byte views agree: reading the register array at lane `l` is reading that lane's
`Words`. -/
theorem stateByte_eq_wordByte (state : Std.Array Vec128 25#usize) (l k : ℕ) (hk : k < 200) :
    stateByte state l k = wordByte (stateWords state l) k := by
  rw [stateByte, wordByte, stateWords_apply, idx_coord (k / 8) (by omega)]

/-- **The sponge squeeze.**  Permute, emit `min RATE (N - done)` bytes per sponge, repeat.

Two clauses, because the recursion needs both: every byte from `done` on is the corresponding
byte of the squeeze stream, and every byte before `done` is left alone. -/
theorem xof2_loop2_spec (RATE : Std.Usize) {N : Std.Usize} (state : Std.Array Vec128 25#usize)
    (out0 out1 : Std.Array Std.U8 N) (done : Std.Usize) (l : ℕ) (hl : l < 2)
    (hR : 0 < RATE.val) (hR200 : RATE.val ≤ 200)
    (hdone : done.val ≤ N.val) (hNmax : N.val + 232 ≤ Std.Usize.max) :
    backend.neon.keccak.xof2_loop2 RATE state out0 out1 done
      ⦃ (p : Std.Array Std.U8 N × Std.Array Std.U8 N) =>
          (∀ j < N.val, done.val ≤ j →
            ((outOf p.1 p.2 l).val[j]!).bv
              = squeezeByte (stateWords state l) RATE.val (j - done.val)) ∧
          (∀ j < N.val, j < done.val →
            ((outOf p.1 p.2 l).val[j]!).bv = ((outOf out0 out1 l).val[j]!).bv) ⦄ := by
  unfold backend.neon.keccak.xof2_loop2
  by_cases hlt : done < N
  · rw [if_pos hlt]
    have hdv : done.val < N.val := by scalar_tac
    let* ⟨ state1, hst1 ⟩ ← permute_spec state l hl
    let* ⟨ i, hi ⟩ ← Std.Usize.sub_spec (x := N) (y := done) (by scalar_tac)
    have hiv : i.val = N.val - done.val := hi
    rw [min_usize_eq, bind_tc_ok]
    set take := (if RATE.val < i.val then RATE else i) with htake
    have htv : take.val = min RATE.val (N.val - done.val) := by rw [htake]; split <;> omega
    have htpos : 0 < take.val := by omega
    have htN : done.val + take.val ≤ N.val := by omega
    let* ⟨ words, hwords ⟩ ← Usize.div_ceil_spec take 8#usize (by scalar_tac)
    have hwv : words.val = (take.val + 7) / 8 := by rw [hwords, ← htake]; norm_num
    have hw25 : words.val ≤ 25 := by omega
    have hwtake : take.val ≤ 8 * words.val := by omega
    have hfit : ∀ w, w < words.val → done.val + 8 * w < N.val := by intro w hw; omega
    let* ⟨ q0, q1, word, hp1, hp2, hp3 ⟩ ← xof2_loop2_loop0_spec state1 out0 out1 done words
      0#usize hw25 (by simp) (by omega)
    let* ⟨ r0, r1, hq ⟩ ← xof2_loop2_loop1_spec state1 q0 q1 done words word hw25 hp2 hfit
    let* ⟨ done2, hdone2 ⟩ ← Std.Usize.add_spec (x := done) (y := take) (by scalar_tac)
    have hd2v : done2.val = done.val + take.val := hdone2
    -- what this block wrote, and what it left alone
    have hblock : ∀ j < N.val, done.val ≤ j → j < done.val + take.val →
        ((outOf r0 r1 l).val[j]!).bv = stateByte state1 l (j - done.val) := by
      intro j hj hj1 hj2
      rw [hq l hl j hj]
      by_cases hc : done.val + 8 * word.val ≤ j
      · rw [if_pos ⟨hc, by omega⟩]
      · rw [if_neg (by tauto), hp3 l hl j hj]
        simp only [Nat.mul_zero, Nat.add_zero]
        rw [if_pos ⟨by omega, by omega⟩]
    have hkeep : ∀ j < N.val, j < done.val →
        ((outOf r0 r1 l).val[j]!).bv = ((outOf out0 out1 l).val[j]!).bv := by
      intro j hj hj1
      rw [hq l hl j hj, if_neg (by omega), hp3 l hl j hj, if_neg (by omega)]
    apply WP.spec_mono
      (xof2_loop2_spec RATE state1 r0 r1 done2 l hl hR hR200 (by omega) hNmax)
    rintro ⟨t0, t1⟩ ⟨hrA, hrB⟩
    refine ⟨fun j hj hj1 => ?_, fun j hj hj1 => ?_⟩
    · by_cases hin : j < done2.val
      · rw [hrB j hj hin, hblock j hj hj1 (by omega),
          stateByte_eq_wordByte state1 l (j - done.val) (by omega), hst1,
          squeezeByte, Nat.div_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega),
          sqState_succ, sqState_zero]
      · rw [hrA j hj (by omega), hd2v, squeezeByte, squeezeByte, hst1]
        have hmR : RATE.val ≤ j - done.val := by omega
        have htR : take.val = RATE.val := by omega
        rw [show j - (done.val + take.val) = (j - done.val) - RATE.val from by omega,
          show ((j - done.val) - RATE.val) % RATE.val = (j - done.val) % RATE.val from
            (Nat.mod_eq_sub_mod hmR).symm,
          show ((j - done.val) - RATE.val) / RATE.val + 1 = (j - done.val) / RATE.val from
            (Nat.div_eq_sub_div hR hmR).symm,
          ← sqState_succ']
    · rw [hrB j hj (by omega), hkeep j hj hj1]
  · rw [if_neg hlt]
    refine (WP.spec_ok _).mpr ⟨fun j hj hj1 => by exfalso; scalar_tac, fun j hj hj1 => rfl⟩
termination_by N.val - done.val
decreasing_by scalar_decr_tac

end

end Kopis.Neon.Keccak
