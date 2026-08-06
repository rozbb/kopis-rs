/-
  # Kopis/Avx2/Keccak/Squeeze.lean — getting the permuted state back out.

  The squeeze is the absorb run backwards.  `keccak.rs` reads four registers, transposes them so
  each output register carries four consecutive words of one sponge, and stores 32 bytes into
  that sponge's output array; whatever is left over, or would run past the end of the output, is
  written a byte at a time.

  `stateByte` is the squeeze's view of the state — byte `k` of sponge `l` is byte `k % 8` of the
  word in register `k / 8` — and it is the mirror of `Absorb.lean`'s `leWord64`.  The two agree
  because `SpecState.lean` identifies both with the spec's byte-level sponge state.
-/
import Kopis.Avx2.Keccak.SpecState

open Aeneas Aeneas.Std Result
open RustKopisAvx2
open RustKopisAvx2.backend.avx2.intrinsics
open Kopis.Avx2
open Spec.SHA3

namespace Kopis.Avx2.Keccak

set_option maxHeartbeats 4000000

noncomputable section

/-- Byte `k` of sponge `l`'s state: byte `k % 8` of the word held in register `k / 8`.  This is
the squeeze's view of the state, and the mirror of `leWord64`'s absorb view. -/
def stateByte (state : Std.Array Vec256 25#usize) (l k : ℕ) : BitVec 8 :=
  laneOf 8 (lane64 (state.val[k / 8]!) l) (k % 8)

/-- **A register's bytes are its lanes' bytes.**  `lane8 c k` is byte `k % 8` of lane `k / 8` —
the decomposition every store in the squeeze goes through. -/
theorem lane8_eq_lane64_byte (c : Vec256) (k : ℕ) :
    lane8 c k = laneOf 8 (lane64 c (k / 8)) (k % 8) := by
  simp only [lane8, lane64]
  exact laneOf_laneOf 8 8 (bits c) k (by norm_num)

/-- The byte a transposed register contributes to the output stream.  `transpose4x64` puts word
`word + m` of sponge `l` into lane `m` of output register `l`, so output register `l`'s byte `k`
is state byte `8·word + k` of sponge `l`. -/
theorem lane8_transposed (state : Std.Array Vec256 25#usize) (v v1 v2 v3 t : Vec256)
    (word : ℕ) (l : ℕ) (_hl : l < 4)
    (hv : ∀ m, m < 4 → lane64 (inReg v v1 v2 v3 m) l = lane64 (state.val[word + m]!) l)
    (ht : ∀ m, m < 4 → lane64 t m = lane64 (inReg v v1 v2 v3 m) l)
    (k : ℕ) (hk : k < 32) :
    lane8 t k = stateByte state l (8 * word + k) := by
  rw [lane8_eq_lane64_byte, ht (k / 8) (by omega), hv (k / 8) (by omega), stateByte,
    show (8 * word + k) / 8 = word + k / 8 from by omega,
    show (8 * word + k) % 8 = k % 8 from by omega]

/-- **The innermost tail store.**  Copies `packed[8·lane + i]` to `out[lane][start + i]` for the
remaining `i`, leaving every other lane and every byte outside the window alone.  Stated as a
complete description of the result so the callers can compose it across lanes. -/
theorem xof4_loop2_loop1_loop0_loop0_spec {N : Std.Usize}
    (iter : core.ops.range.Range Std.Usize) (out : Std.Array (Std.Array Std.U8 N) 4#usize)
    (packed : Std.Array Std.U8 32#usize) (lane start : Std.Usize)
    (hlane : lane.val < 4) (hlen : iter.«end».val ≤ 8) (hstart : iter.start.val ≤ iter.«end».val)
    (hbound : start.val + iter.«end».val ≤ N.val) :
    backend.avx2.keccak.xof4_loop2_loop1_loop0_loop0 iter out packed lane start
      ⦃ (o : Std.Array (Std.Array Std.U8 N) 4#usize) => ∀ l' < 4, ∀ j < N.val,
          (o.val[l']!).val[j]! =
            if l' = lane.val ∧ start.val + iter.start.val ≤ j ∧ j < start.val + iter.«end».val
            then packed.val[8 * l' + (j - start.val)]!
            else (out.val[l']!).val[j]! ⦄ := by
  unfold backend.avx2.keccak.xof4_loop2_loop1_loop0_loop0
  by_cases hlt : iter.start.val < iter.«end».val
  · let* ⟨ o, iter1, ho, hstart', hend' ⟩ ← core.iter.range.IteratorRange.next_Usize_some_spec
    rw [ho]; simp only
    let* ⟨ k1, hk1 ⟩ ← Std.Usize.mul_spec (x := 8#usize) (y := lane) (by scalar_tac)
    let* ⟨ k2, hk2 ⟩ ← Std.Usize.add_spec (x := k1) (y := iter.start) (by scalar_tac)
    let* ⟨ byt, hbyt ⟩ ← Array.index_usize_spec packed k2 (by scalar_tac)
    let* ⟨ k4, hk4 ⟩ ← Std.Usize.add_spec (x := start) (y := iter.start) (by scalar_tac)
    let* ⟨ row, back, hrow, hback ⟩ ← Array.index_mut_usize_spec out lane (by scalar_tac)
    let* ⟨ row1, hrow1 ⟩ ← Array.update_spec
    have holen : (out.val : List (Std.Array Std.U8 N)).length = 4 := out.property
    have hrlen : ∀ (r : Std.Array Std.U8 N), (r.val : List Std.U8).length = N.val :=
      fun r => r.property
    -- the byte written, with its index moved to `getElem!` so it can be rewritten
    have hbytv : byt = packed.val[8 * lane.val + iter.start.val]! := by
      have h := hbyt.trans (getElem!_pos packed.val k2.val (by scalar_tac)).symm
      rwa [hk2, hk1] at h
    have hrowv : row = out.val[lane.val]! := by
      have h := hrow.trans (getElem!_pos out.val lane.val (by rw [holen]; omega)).symm
      exact h
    have hnew : ∀ l' < 4, ∀ j < N.val,
        ((back row1).val[l']!).val[j]! =
          if l' = lane.val ∧ j = start.val + iter.start.val then byt
          else (out.val[l']!).val[j]! := by
      intro l' hl' j hj
      rw [hback, Std.Array.set_val_eq,
        getElem!_list_set out.val lane.val row1 l' (by rw [holen]; omega)]
      by_cases hll : l' = lane.val
      · rw [if_pos hll, hrow1, Std.Array.set_val_eq,
          getElem!_list_set row.val k4.val byt j (by rw [hrlen]; scalar_tac), hk4, hrowv, hll]
        by_cases hjj : j = start.val + iter.start.val
        · rw [if_pos hjj, if_pos ⟨rfl, hjj⟩]
        · rw [if_neg hjj, if_neg (by tauto)]
      · rw [if_neg hll, if_neg (by tauto)]
    apply WP.spec_mono
      (xof4_loop2_loop1_loop0_loop0_spec iter1 (back row1) packed lane start hlane
        (by rw [hend']; exact hlen) (by rw [hstart', hend']; scalar_tac)
        (by rw [hend']; exact hbound))
    intro r hr l' hl' j hj
    rw [hr l' hl' j hj, hnew l' hl' j hj, hstart', hend']
    by_cases hll : l' = lane.val
    · subst hll
      by_cases h1 : start.val + (iter.start.val + 1) ≤ j ∧ j < start.val + iter.«end».val
      · rw [if_pos ⟨rfl, h1.1, h1.2⟩, if_pos ⟨rfl, by omega, h1.2⟩]
      · rw [if_neg (by tauto)]
        by_cases h2 : j = start.val + iter.start.val
        · rw [if_pos ⟨rfl, h2⟩, if_pos ⟨rfl, by omega, by omega⟩, h2, hbytv]
          congr 2
          omega
        · rw [if_neg (by tauto), if_neg (by omega)]
    · rw [if_neg (by tauto), if_neg (by tauto), if_neg (by tauto)]
  · let* ⟨ o, iter1, hnone, _ ⟩ ← core.iter.range.IteratorRange.next_Usize_none_spec
    rw [hnone]; simp only [WP.spec_ok]
    intro l' hl' j hj
    rw [if_neg (by scalar_tac)]
  termination_by iter.«end».val - iter.start.val
  decreasing_by scalar_decr_tac

/-- `core.cmp.min` at `Usize` is the plain conditional. -/
theorem min_usize_eq (a b : Std.Usize) :
    core.cmp.min core.cmp.OrdUsize a b = ok (if a.val < b.val then a else b) := by
  unfold core.cmp.min core.cmp.OrdUsize
  simp only [liftFun2, core.cmp.impls.OrdUsize.min]
  rfl

/-- **The per-lane tail store.**  For each lane still to do, copies the `min 8 (N - start)` bytes
of that lane's word out of `packed` into that lane's output array at `start`. -/
theorem xof4_loop2_loop1_loop0_spec {N : Std.Usize}
    (iter : core.ops.range.Range Std.Usize) (out : Std.Array (Std.Array Std.U8 N) 4#usize)
    (done1 word : Std.Usize) (packed : Std.Array Std.U8 32#usize)
    (hend : iter.«end».val = 4) (hstart : iter.start.val ≤ 4)
    (hst : done1.val + 8 * word.val ≤ N.val) :
    backend.avx2.keccak.xof4_loop2_loop1_loop0 iter out done1 word packed
      ⦃ (o : Std.Array (Std.Array Std.U8 N) 4#usize) => ∀ l' < 4, ∀ j < N.val,
          (o.val[l']!).val[j]! =
            if iter.start.val ≤ l' ∧ done1.val + 8 * word.val ≤ j
                ∧ j < done1.val + 8 * word.val + min 8 (N.val - (done1.val + 8 * word.val))
            then packed.val[8 * l' + (j - (done1.val + 8 * word.val))]!
            else (out.val[l']!).val[j]! ⦄ := by
  unfold backend.avx2.keccak.xof4_loop2_loop1_loop0
  by_cases hlt : iter.start.val < iter.«end».val
  · let* ⟨ o, iter1, ho, hstart', hend' ⟩ ← core.iter.range.IteratorRange.next_Usize_some_spec
    rw [ho]; simp only
    let* ⟨ i, hi ⟩ ← Std.Usize.mul_spec (x := 8#usize) (y := word) (by scalar_tac)
    let* ⟨ st, hstv ⟩ ← Std.Usize.add_spec (x := done1) (y := i) (by scalar_tac)
    let* ⟨ rem, hrem ⟩ ← Std.Usize.sub_spec (x := N) (y := st) (by scalar_tac)
    have h8 : ((8#usize : Std.Usize) : ℕ) = 8 := rfl
    rw [min_usize_eq, bind_tc_ok]
    simp only [h8]
    have hstw : st.val = done1.val + 8 * word.val := by rw [hstv, hi]
    have hr8 : rem.val = N.val - (done1.val + 8 * word.val) := by rw [hrem, hstw]
    have hlenv : ((if (8 : ℕ) < rem.val then (8#usize : Std.Usize) else rem) : Std.Usize).val
        = min 8 (N.val - (done1.val + 8 * word.val)) := by
      split <;> omega
    let* ⟨ r, hr ⟩ ← xof4_loop2_loop1_loop0_loop0_spec { start := 0#usize, «end» := _ } out packed
      iter.start st (by scalar_tac) (by rw [hlenv]; omega) (by simp) (by rw [hlenv, hstw]; omega)
    apply WP.spec_mono
      (xof4_loop2_loop1_loop0_spec iter1 r done1 word packed
        (by rw [hend']; exact hend) (by rw [hstart']; scalar_tac) hst)
    intro r2 hr2 l' hl' j hj
    rw [hr2 l' hl' j hj, hr l' hl' j hj, hstart', hstw, hlenv]
    simp only [Nat.add_zero]
    by_cases hwin : done1.val + 8 * word.val ≤ j
        ∧ j < done1.val + 8 * word.val + min 8 (N.val - (done1.val + 8 * word.val))
    · rcases (show iter.start.val + 1 ≤ l' ∨ l' = iter.start.val ∨ l' < iter.start.val
                by omega) with h | h | h
      · rw [if_pos ⟨h, hwin.1, hwin.2⟩, if_pos ⟨by omega, hwin.1, hwin.2⟩]
      · rw [if_neg (by omega), if_pos ⟨h, hwin.1, hwin.2⟩,
          if_pos ⟨by omega, hwin.1, hwin.2⟩]
      · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
    · rw [if_neg (by tauto), if_neg (by tauto), if_neg (by tauto)]
  · let* ⟨ o, iter1, hnone, _ ⟩ ← core.iter.range.IteratorRange.next_Usize_none_spec
    rw [hnone]; simp only [WP.spec_ok]
    intro l' hl' j hj
    rw [if_neg (by scalar_tac)]
  termination_by iter.«end».val - iter.start.val
  decreasing_by scalar_decr_tac

/-- **The tail word loop.**  One state register per iteration: store it to a 32-byte buffer, then
hand each lane's eight bytes to that lane's output array.  `hfit` is what makes every iteration's
`N - start` subtraction safe — the caller picks `words` so the last word starts before `N`. -/
theorem xof4_loop2_loop1_spec {N : Std.Usize} (out : Std.Array (Std.Array Std.U8 N) 4#usize)
    (state : Std.Array Vec256 25#usize) (done1 words word : Std.Usize)
    (hwords : words.val ≤ 25) (hword : word.val ≤ words.val)
    (hfit : ∀ w, w < words.val → done1.val + 8 * w < N.val) :
    backend.avx2.keccak.xof4_loop2_loop1 out state done1 words word
      ⦃ (o : Std.Array (Std.Array Std.U8 N) 4#usize) => ∀ l' < 4, ∀ j < N.val,
          ((o.val[l']!).val[j]!).bv =
            if done1.val + 8 * word.val ≤ j ∧ j < done1.val + 8 * words.val
            then stateByte state l' (j - done1.val)
            else ((out.val[l']!).val[j]!).bv ⦄ := by
  unfold backend.avx2.keccak.xof4_loop2_loop1
  by_cases hlt : word < words
  · rw [if_pos hlt]
    have hwv : word.val < words.val := by scalar_tac
    have hstN : done1.val + 8 * word.val < N.val := hfit word.val hwv
    let* ⟨ v, hv ⟩ ← Array.index_usize_spec state word (by scalar_tac)
    obtain ⟨packed1, hpk, hpkl⟩ :=
      store_u8x32_spec (Std.Array.repeat 32#usize (0#u8)) 0#usize v (by simp)
    rw [hpk, bind_tc_ok]
    have hvv : v = state.val[word.val]! := by
      have h := hv.trans (getElem!_pos state.val word.val (by scalar_tac)).symm
      exact h
    -- the buffer holds the register's bytes
    have hpkb : ∀ l' < 4, ∀ m < 8,
        (packed1.val[8 * l' + m]!).bv = stateByte state l' (8 * word.val + m) := by
      intro l' hl' m hm
      rw [hpkl (8 * l' + m) (by simp; omega)]
      simp only [show ((0#usize : Std.Usize) : ℕ) = 0 from rfl, Nat.zero_add, Nat.sub_zero,
        if_pos (show (0:ℕ) ≤ 8 * l' + m ∧ 8 * l' + m < 0 + 32 by omega)]
      rw [lane8_eq_lane64_byte, stateByte,
        show (8 * l' + m) / 8 = l' from by omega, show (8 * l' + m) % 8 = m from by omega,
        show (8 * word.val + m) / 8 = word.val from by omega,
        show (8 * word.val + m) % 8 = m from by omega, hvv]
    let* ⟨ out1, hout1 ⟩ ← xof4_loop2_loop1_loop0_spec { start := 0#usize, «end» := 4#usize }
      out done1 word packed1 rfl (by simp) (by omega)
    let* ⟨ word1, hword1 ⟩ ← Std.Usize.add_spec (x := word) (y := 1#usize) (by scalar_tac)
    apply WP.spec_mono
      (xof4_loop2_loop1_spec out1 state done1 words word1 hwords (by scalar_tac) hfit)
    intro r hr l' hl' j hj
    rw [hr l' hl' j hj, hword1]
    by_cases h1 : done1.val + 8 * (word.val + 1) ≤ j ∧ j < done1.val + 8 * words.val
    · rw [if_pos h1, if_pos ⟨by omega, h1.2⟩]
    · rw [if_neg h1, hout1 l' hl' j hj]
      simp only [Nat.zero_le, true_and]
      by_cases h2 : done1.val + 8 * word.val ≤ j
          ∧ j < done1.val + 8 * word.val + min 8 (N.val - (done1.val + 8 * word.val))
      · rw [if_pos h2, if_pos ⟨h2.1, by omega⟩,
          hpkb l' hl' (j - (done1.val + 8 * word.val)) (by omega),
          show 8 * word.val + (j - (done1.val + 8 * word.val)) = j - done1.val from by omega]
      · rw [if_neg h2, if_neg (by omega)]
  · rw [if_neg hlt]
    simp only [WP.spec_ok]
    intro l' hl' j hj
    rw [if_neg (by scalar_tac)]
  termination_by words.val - word.val
  decreasing_by scalar_decr_tac

/-- **The four-at-a-time squeeze store.**  Reads four registers, transposes so each output
register carries four consecutive words of one sponge, and stores 32 bytes into each sponge's
output array.  Stops when a whole group of four no longer fits, either in `words` or in `N`. -/
theorem xof4_loop2_loop0_spec {N : Std.Usize} (out : Std.Array (Std.Array Std.U8 N) 4#usize)
    (state : Std.Array Vec256 25#usize) (done1 words word : Std.Usize)
    (hwords : words.val ≤ 25) (hword : word.val ≤ words.val)
    (hmax : done1.val + 8 * words.val + 32 ≤ Std.Usize.max) :
    backend.avx2.keccak.xof4_loop2_loop0 out state done1 words word
      ⦃ ((o : Std.Array (Std.Array Std.U8 N) 4#usize), (w : Std.Usize)) =>
          word.val ≤ w.val ∧ w.val ≤ words.val ∧
          (∀ l' < 4, ∀ j < N.val,
            ((o.val[l']!).val[j]!).bv =
              if done1.val + 8 * word.val ≤ j ∧ j < done1.val + 8 * w.val
              then stateByte state l' (j - done1.val)
              else ((out.val[l']!).val[j]!).bv) ⦄ := by
  unfold backend.avx2.keccak.xof4_loop2_loop0
  let* ⟨ i, hi ⟩ ← Std.Usize.add_spec (x := word) (y := 4#usize) (by scalar_tac)
  by_cases hle : i ≤ words
  · rw [if_pos hle]
    have hiv : i.val = word.val + 4 := hi
    have hlev : word.val + 4 ≤ words.val := by scalar_tac
    let* ⟨ i1, hi1 ⟩ ← Std.Usize.mul_spec (x := 8#usize) (y := word) (by scalar_tac)
    let* ⟨ i2, hi2 ⟩ ← Std.Usize.add_spec (x := done1) (y := i1) (by scalar_tac)
    let* ⟨ i3, hi3 ⟩ ← Std.Usize.add_spec (x := i2) (y := 32#usize) (by scalar_tac)
    have hi1v : i1.val = 8 * word.val := hi1
    have hi2v : i2.val = done1.val + 8 * word.val := by rw [hi2, hi1v]
    have hi3v : i3.val = done1.val + 8 * word.val + 32 := by rw [hi3, hi2v]
    by_cases hfit : i3 ≤ N
    · rw [if_pos hfit]
      have hfitv : done1.val + 8 * word.val + 32 ≤ N.val := by scalar_tac
      let* ⟨ v, hv ⟩ ← Array.index_usize_spec state word (by scalar_tac)
      let* ⟨ m1, hm1 ⟩ ← Std.Usize.add_spec (x := word) (y := 1#usize) (by scalar_tac)
      let* ⟨ v1, hv1 ⟩ ← Array.index_usize_spec state m1 (by scalar_tac)
      let* ⟨ m2, hm2 ⟩ ← Std.Usize.add_spec (x := word) (y := 2#usize) (by scalar_tac)
      let* ⟨ v2, hv2 ⟩ ← Array.index_usize_spec state m2 (by scalar_tac)
      let* ⟨ m3, hm3 ⟩ ← Std.Usize.add_spec (x := word) (y := 3#usize) (by scalar_tac)
      let* ⟨ v3, hv3 ⟩ ← Array.index_usize_spec state m3 (by scalar_tac)
      obtain ⟨r0, r1, r2, r3, htr, htrl⟩ := transpose4x64_spec v v1 v2 v3
      rw [htr, bind_tc_ok]
      let* ⟨ start, hstart ⟩ ← Std.Usize.add_spec (x := done1) (y := i1) (by scalar_tac)
      have hstv : start.val = done1.val + 8 * word.val := by rw [hstart, hi1v]
      -- the four source registers, by lane index
      have ev : v = state.val[word.val]! :=
        hv.trans (getElem!_pos state.val word.val (by scalar_tac)).symm
      have ev1 : v1 = state.val[m1.val]! :=
        hv1.trans (getElem!_pos state.val m1.val (by scalar_tac)).symm
      have ev2 : v2 = state.val[m2.val]! :=
        hv2.trans (getElem!_pos state.val m2.val (by scalar_tac)).symm
      have ev3 : v3 = state.val[m3.val]! :=
        hv3.trans (getElem!_pos state.val m3.val (by scalar_tac)).symm
      have hsrc : ∀ m, m < 4 → inReg v v1 v2 v3 m = state.val[word.val + m]! := by
        intro m hm
        rcases (show m = 0 ∨ m = 1 ∨ m = 2 ∨ m = 3 by omega) with rfl | rfl | rfl | rfl
        · rw [show word.val + 0 = word.val from by omega]; exact ev
        · rw [show word.val + 1 = m1.val from by scalar_tac]; exact ev1
        · rw [show word.val + 2 = m2.val from by scalar_tac]; exact ev2
        · rw [show word.val + 3 = m3.val from by scalar_tac]; exact ev3
      -- each output register's bytes are that lane's state bytes
      have hbyte : ∀ l' < 4, ∀ k < 32,
          lane8 (inReg r0 r1 r2 r3 l') k = stateByte state l' (8 * word.val + k) := by
        intro l' hl' k hk
        refine lane8_transposed state v v1 v2 v3 (inReg r0 r1 r2 r3 l') word.val l' hl'
          (fun m hm => by rw [hsrc m hm]) (fun m hm => ?_) k hk
        rcases (show l' = 0 ∨ l' = 1 ∨ l' = 2 ∨ l' = 3 by omega) with rfl | rfl | rfl | rfl
        · exact (htrl m hm).1
        · exact (htrl m hm).2.1
        · exact (htrl m hm).2.2.1
        · exact (htrl m hm).2.2.2
      let* ⟨ q0, back0, hq0, hb0 ⟩ ← Array.index_mut_usize_spec out 0#usize (by scalar_tac)
      obtain ⟨s0, hs0, hs0l⟩ := store_u8x32_spec q0 start r0 (by scalar_tac)
      rw [hs0, bind_tc_ok]
      let* ⟨ q1, back1, hq1, hb1 ⟩ ← Array.index_mut_usize_spec (back0 s0) 1#usize (by scalar_tac)
      obtain ⟨s1, hs1, hs1l⟩ := store_u8x32_spec q1 start r1 (by scalar_tac)
      rw [hs1, bind_tc_ok]
      let* ⟨ q2, back2, hq2, hb2 ⟩ ← Array.index_mut_usize_spec (back1 s1) 2#usize (by scalar_tac)
      obtain ⟨s2, hs2, hs2l⟩ := store_u8x32_spec q2 start r2 (by scalar_tac)
      rw [hs2, bind_tc_ok]
      let* ⟨ q3, back3, hq3, hb3 ⟩ ← Array.index_mut_usize_spec (back2 s2) 3#usize (by scalar_tac)
      obtain ⟨s3, hs3, hs3l⟩ := store_u8x32_spec q3 start r3 (by scalar_tac)
      rw [hs3, bind_tc_ok]
      have u0 : ((0#usize : Std.Usize) : ℕ) = 0 := rfl
      have u1 : ((1#usize : Std.Usize) : ℕ) = 1 := rfl
      have u2 : ((2#usize : Std.Usize) : ℕ) = 2 := rfl
      have u3 : ((3#usize : Std.Usize) : ℕ) = 3 := rfl
      have holen : (out.val : List (Std.Array Std.U8 N)).length = 4 := out.property
      have hset : ∀ (A : Std.Array (Std.Array Std.U8 N) 4#usize) (k : Std.Usize)
          (x : Std.Array Std.U8 N) (l' : ℕ), l' < 4 → k.val < 4 →
          (A.set k x).val[l']! = if l' = k.val then x else A.val[l']! := by
        intro A k x l' hl' hk
        rw [Std.Array.set_val_eq,
          getElem!_list_set A.val k.val x l' (by rw [A.property]; exact hk)]
      have hrow : ∀ l' < 4, ((back3 s3).val[l']!)
          = if l' = 3 then s3 else if l' = 2 then s2 else if l' = 1 then s1
            else if l' = 0 then s0 else out.val[l']! := by
        intro l' hl'
        rw [hb3, hset _ 3#usize s3 l' hl' (by simp), hb2, hset _ 2#usize s2 l' hl' (by simp),
          hb1, hset _ 1#usize s1 l' hl' (by simp), hb0, hset _ 0#usize s0 l' hl' (by simp),
          u0, u1, u2, u3]
      have eq0 : q0 = out.val[0]! := hq0.trans (getElem!_pos _ 0 (by rw [holen]; omega)).symm
      have eq1 : q1 = out.val[1]! := by
        rw [hq1.trans (getElem!_pos (back0 s0).val 1
              (by rw [(back0 s0).property]; decide)).symm,
          hb0, hset out 0#usize s0 1 (by omega) (by simp), if_neg (by omega)]
      have eq2 : q2 = out.val[2]! := by
        rw [hq2.trans (getElem!_pos (back1 s1).val 2
              (by rw [(back1 s1).property]; decide)).symm,
          hb1, hset _ 1#usize s1 2 (by omega) (by simp), if_neg (by omega),
          hb0, hset out 0#usize s0 2 (by omega) (by simp), if_neg (by omega)]
      have eq3 : q3 = out.val[3]! := by
        rw [hq3.trans (getElem!_pos (back2 s2).val 3
              (by rw [(back2 s2).property]; decide)).symm,
          hb2, hset _ 2#usize s2 3 (by omega) (by simp), if_neg (by omega),
          hb1, hset _ 1#usize s1 3 (by omega) (by simp), if_neg (by omega),
          hb0, hset out 0#usize s0 3 (by omega) (by simp), if_neg (by omega)]
      have hfinal : ∀ l' < 4, ∀ j < N.val,
          (((back3 s3).val[l']!).val[j]!).bv =
            if start.val ≤ j ∧ j < start.val + 32
            then stateByte state l' (j - done1.val)
            else ((out.val[l']!).val[j]!).bv := by
        intro l' hl' j hj
        rw [hrow l' hl']
        rcases (show l' = 0 ∨ l' = 1 ∨ l' = 2 ∨ l' = 3 by omega) with rfl | rfl | rfl | rfl
        · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos rfl, hs0l j hj, eq0]
          by_cases hw : start.val ≤ j ∧ j < start.val + 32
          · rw [if_pos hw, if_pos hw,
              show lane8 r0 (j - start.val)
                = lane8 (inReg r0 r1 r2 r3 0) (j - start.val) from rfl,
              hbyte 0 (by omega) (j - start.val) (by omega),
              show 8 * word.val + (j - start.val) = j - done1.val from by omega]
          · rw [if_neg hw, if_neg hw]
        · rw [if_neg (by omega), if_neg (by omega), if_pos rfl, hs1l j hj, eq1]
          by_cases hw : start.val ≤ j ∧ j < start.val + 32
          · rw [if_pos hw, if_pos hw,
              show lane8 r1 (j - start.val)
                = lane8 (inReg r0 r1 r2 r3 1) (j - start.val) from rfl,
              hbyte 1 (by omega) (j - start.val) (by omega),
              show 8 * word.val + (j - start.val) = j - done1.val from by omega]
          · rw [if_neg hw, if_neg hw]
        · rw [if_neg (by omega), if_pos rfl, hs2l j hj, eq2]
          by_cases hw : start.val ≤ j ∧ j < start.val + 32
          · rw [if_pos hw, if_pos hw,
              show lane8 r2 (j - start.val)
                = lane8 (inReg r0 r1 r2 r3 2) (j - start.val) from rfl,
              hbyte 2 (by omega) (j - start.val) (by omega),
              show 8 * word.val + (j - start.val) = j - done1.val from by omega]
          · rw [if_neg hw, if_neg hw]
        · rw [if_pos rfl, hs3l j hj, eq3]
          by_cases hw : start.val ≤ j ∧ j < start.val + 32
          · rw [if_pos hw, if_pos hw,
              show lane8 r3 (j - start.val)
                = lane8 (inReg r0 r1 r2 r3 3) (j - start.val) from rfl,
              hbyte 3 (by omega) (j - start.val) (by omega),
              show 8 * word.val + (j - start.val) = j - done1.val from by omega]
          · rw [if_neg hw, if_neg hw]
      apply WP.spec_mono
        (xof4_loop2_loop0_spec (back3 s3) state done1 words i hwords (by omega) hmax)
      rintro ⟨o, w⟩ ⟨hw1, hw2, hw3⟩
      refine ⟨by omega, hw2, fun l' hl' j hj => ?_⟩
      rw [hw3 l' hl' j hj, hfinal l' hl' j hj, hiv, hstv]
      by_cases h1 : done1.val + 8 * (word.val + 4) ≤ j ∧ j < done1.val + 8 * w.val
      · rw [if_pos h1, if_pos ⟨by omega, h1.2⟩]
      · rw [if_neg h1]
        by_cases h2 : done1.val + 8 * word.val ≤ j ∧ j < done1.val + 8 * word.val + 32
        · rw [if_pos h2, if_pos ⟨h2.1, by omega⟩]
        · rw [if_neg h2, if_neg (by omega)]
    · rw [if_neg hfit]
      simp only [WP.spec_ok]
      exact ⟨le_refl _, hword, fun l' hl' j hj => by rw [if_neg (by omega)]⟩
  · rw [if_neg hle]
    simp only [WP.spec_ok]
    exact ⟨le_refl _, hword, fun l' hl' j hj => by rw [if_neg (by omega)]⟩

/-! ## The squeeze stream

The outer loop permutes at the top of each output block.  The spec's `absorb` likewise ends with
a permutation before `squeeze` emits anything, so the two agree on the first block as well as on
the ones after it — `squeezeByte` below is that shared indexing. -/

/-- Byte `k` of a `Words` state: byte `k % 8` of lane `k / 8`, with the flat index read back to
coordinates by `coordX`/`coordY`.  The `Words`-level twin of `stateByte`. -/
def wordByte (W : Words) (k : ℕ) : BitVec 8 :=
  laneOf 8 (W (coordX (k / 8)) (coordY (k / 8))) (k % 8)

/-- The two byte views agree: reading the register array at lane `l` is reading that lane's
`Words`. -/
theorem stateByte_eq_wordByte (state : Std.Array Vec256 25#usize) (l k : ℕ) (hk : k < 200) :
    stateByte state l k = wordByte (stateWords state l) k := by
  rw [stateByte, wordByte, stateWords_apply, idx_coord (k / 8) (by omega)]

/-- The sponge state after `n` squeeze permutations. -/
def sqState (W : Words) : ℕ → Words
  | 0 => W
  | n + 1 => rounds (sqState W n) 12 12

@[simp] theorem sqState_zero (W : Words) : sqState W 0 = W := rfl

theorem sqState_succ (W : Words) (n : ℕ) :
    sqState W (n + 1) = rounds (sqState W n) 12 12 := rfl

/-- Squeezing `n+1` times from `W` is squeezing `n` times from the once-permuted state — the
form the outer loop's induction needs, since it permutes and then recurses. -/
theorem sqState_succ' (W : Words) (n : ℕ) :
    sqState W (n + 1) = sqState (rounds W 12 12) n := by
  induction n with
  | zero => rfl
  | succ m ih => rw [sqState_succ, ih, sqState_succ]

/-- **Byte `k` of the squeeze stream.**  Block `k / RATE` comes from the state permuted
`k / RATE + 1` times — the Rust permutes at the top of each output block, and the spec's `absorb`
ends with a permutation before `squeeze` emits, so the two agree on the first block too. -/
def squeezeByte (W : Words) (RATE k : ℕ) : BitVec 8 :=
  wordByte (sqState W (k / RATE + 1)) (k % RATE)

/-- **The sponge squeeze.**  Permute, emit `min RATE (N - done)` bytes per lane, repeat.

Two clauses, because the recursion needs both: every byte from `done1` on is the corresponding
byte of the squeeze stream, and every byte before `done1` is left alone.  Without the second, the
bytes this call writes could not be read back after the recursive call. -/
theorem xof4_loop2_spec (RATE : Std.Usize) {N : Std.Usize}
    (out : Std.Array (Std.Array Std.U8 N) 4#usize) (state : Std.Array Vec256 25#usize)
    (done1 : Std.Usize) (l : ℕ) (hl : l < 4)
    (hR : 0 < RATE.val) (hR200 : RATE.val ≤ 200)
    (hdone : done1.val ≤ N.val) (hNmax : N.val + 232 ≤ Std.Usize.max) :
    backend.avx2.keccak.xof4_loop2 RATE out state done1
      ⦃ (o : Std.Array (Std.Array Std.U8 N) 4#usize) =>
          (∀ j < N.val, done1.val ≤ j →
            ((o.val[l]!).val[j]!).bv
              = squeezeByte (stateWords state l) RATE.val (j - done1.val)) ∧
          (∀ j < N.val, j < done1.val →
            ((o.val[l]!).val[j]!).bv = ((out.val[l]!).val[j]!).bv) ⦄ := by
  unfold backend.avx2.keccak.xof4_loop2
  by_cases hlt : done1 < N
  · rw [if_pos hlt]
    have hdv : done1.val < N.val := by scalar_tac
    let* ⟨ state1, hst1 ⟩ ← permute_spec state l hl
    let* ⟨ i, hi ⟩ ← Std.Usize.sub_spec (x := N) (y := done1) (by scalar_tac)
    have hiv : i.val = N.val - done1.val := hi
    rw [min_usize_eq, bind_tc_ok]
    set take := (if RATE.val < i.val then RATE else i) with htake
    have htv : take.val = min RATE.val (N.val - done1.val) := by rw [htake]; split <;> omega
    have htpos : 0 < take.val := by omega
    have htN : done1.val + take.val ≤ N.val := by omega
    let* ⟨ i1, hi1 ⟩ ← Std.Usize.add_spec (x := take) (y := 7#usize) (by scalar_tac)
    let* ⟨ words, hwords ⟩ ← Std.Usize.div_spec
    have hwv : words.val = (take.val + 7) / 8 := by rw [hwords, hi1]
    have hw25 : words.val ≤ 25 := by omega
    have hwtake : take.val ≤ 8 * words.val := by omega
    have hfit : ∀ w, w < words.val → done1.val + 8 * w < N.val := by intro w hw; omega
    let* ⟨ p, word, hp1, hp2, hp3 ⟩ ← xof4_loop2_loop0_spec out state1 done1 words 0#usize
      hw25 (by simp) (by omega)
    let* ⟨ q, hq ⟩ ← xof4_loop2_loop1_spec p state1 done1 words word hw25 hp2 hfit
    let* ⟨ done2, hdone2 ⟩ ← Std.Usize.add_spec (x := done1) (y := take) (by scalar_tac)
    have hd2v : done2.val = done1.val + take.val := hdone2
    -- what this block wrote, and what it left alone
    have hblock : ∀ j < N.val, done1.val ≤ j → j < done1.val + take.val →
        ((q.val[l]!).val[j]!).bv = stateByte state1 l (j - done1.val) := by
      intro j hj hj1 hj2
      rw [hq l hl j hj]
      by_cases hc : done1.val + 8 * word.val ≤ j
      · rw [if_pos ⟨hc, by omega⟩]
      · rw [if_neg (by tauto), hp3 l hl j hj]
        simp only [Nat.mul_zero, Nat.add_zero]
        rw [if_pos ⟨by omega, by omega⟩]
    have hkeep : ∀ j < N.val, j < done1.val → ((q.val[l]!).val[j]!).bv
        = ((out.val[l]!).val[j]!).bv := by
      intro j hj hj1
      rw [hq l hl j hj, if_neg (by omega), hp3 l hl j hj, if_neg (by omega)]
    apply WP.spec_mono
      (xof4_loop2_spec RATE q state1 done2 l hl hR hR200 (by omega) hNmax)
    rintro r ⟨hrA, hrB⟩
    refine ⟨fun j hj hj1 => ?_, fun j hj hj1 => ?_⟩
    · by_cases hin : j < done2.val
      · -- this block's own bytes: the recursive call left them alone
        rw [hrB j hj hin, hblock j hj hj1 (by omega),
          stateByte_eq_wordByte state1 l (j - done1.val) (by omega), hst1,
          squeezeByte, Nat.div_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega),
          sqState_succ, sqState_zero]
      · -- a later block: reindex the stream past this one
        rw [hrA j hj (by omega), hd2v, squeezeByte, squeezeByte, hst1]
        have hmR : RATE.val ≤ j - done1.val := by omega
        have htR : take.val = RATE.val := by omega
        rw [show j - (done1.val + take.val) = (j - done1.val) - RATE.val from by omega,
          show ((j - done1.val) - RATE.val) % RATE.val = (j - done1.val) % RATE.val from
            (Nat.mod_eq_sub_mod hmR).symm,
          show ((j - done1.val) - RATE.val) / RATE.val + 1 = (j - done1.val) / RATE.val from
            (Nat.div_eq_sub_div hR hmR).symm,
          ← sqState_succ']
    · rw [hrB j hj (by omega), hkeep j hj hj1]
  · rw [if_neg hlt]
    simp only [WP.spec_ok]
    refine ⟨fun j hj hj1 => by exfalso; scalar_tac, fun j hj hj1 => trivial⟩
  termination_by N.val - done1.val
  decreasing_by scalar_decr_tac

end
end Kopis.Avx2.Keccak
