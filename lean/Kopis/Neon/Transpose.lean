/-
  # Kopis/Neon/Transpose.lean — `transpose8` is the 8×8 transpose.

  The last three NTT levels have `len < 8`, so their butterflies live *inside* a vector.  The
  backend deals with that the same way both vector backends do: transpose a group of 8 vectors as
  an 8×8 `i16` matrix, so that lane `m` of vector `k` owns coefficient block `8g + m`, run the
  three levels as ordinary vertical butterflies with a per-lane ψ, and transpose back.

  So the claim is exactly

      lane `m` of the result's vector `k`  =  lane `k` of the input's vector `m`

  and applying it twice is the identity, which is what gets the transform back to coefficient
  order.  The Rust test `transpose8_permutes_as_documented` states the same property.

  ## Why this is so much shorter than `Kopis/Avx2/Transpose.lean`

  §1(b) of `NEON_VERIFICATION_PLAN.md` predicted it and the mechanism is visible below.  AArch64
  vectors are 128 bits and `TRN1`/`TRN2` act across the whole register, so each of the three
  stages is exactly "swap one bit of the vector index with one bit of the lane index":

  * `trn.8h` swaps bit 0,
  * `trn.4s` swaps bit 1,
  * `trn.2d` swaps bit 2,

  and three stages later the two three-bit indices have been exchanged outright.  AVX2's network
  is `unpack` at three widths *plus* a `vperm2i128` pass to cross the 128-bit half boundary its
  shuffles cannot see past, and every stage of its proof carries the "acts within each half"
  quantifier that makes the classic AVX2 transpose error possible.  That quantifier has no
  counterpart here: there is no half.

  The three `*_lane` lemmas below are where that shows up.  Each states a `trn` at *16-bit* lane
  granularity — including the ones the code issues at 32 and 64 bits — so all three stages speak
  one vocabulary and the composition is index arithmetic rather than a change of view.
-/
import Kopis.Neon.LaneArith

open Aeneas Aeneas.Std Result
open RustKopisNeon

namespace Kopis.Neon

open RustKopisNeon.backend.neon.intrinsics

set_option maxHeartbeats 1000000

/-! ## Reading a group

`Vec128` is an opaque extracted type with no `Inhabited` instance, so the group is read with a
bounds proof rather than `getElem!`.  `vAt` is that read, named to keep the statements legible;
it is the exact counterpart of `wAt` in `Kopis/Avx2/Ser.lean`. -/

/-- Vector `k` of a group of eight. -/
def vAt (r : Array RustKopisNeon.backend.neon.intrinsics.Vec128 8#usize) (k : ℕ) (hk : k < 8) :
    RustKopisNeon.backend.neon.intrinsics.Vec128 :=
  r[k]'(by have := r.property; scalar_tac)

/-- Writing vector `i` of a group leaves the others alone. -/
theorem vAt_set (arr : Array Vec128 8#usize) (i : Usize) (x : Vec128) (k : ℕ) (hk : k < 8) :
    vAt (Std.Array.set arr i x) k hk = if k = i.val then x else vAt arr k hk := by
  have hlen : arr.val.length = 8 := by have := arr.property; scalar_tac
  by_cases h : k = i.val
  · subst h
    rw [if_pos rfl]
    unfold vAt
    grind
  · rw [if_neg h]
    unfold vAt
    grind

/-! ## The three stages, all at 16-bit lanes

`trn1`/`trn2` at a width `w` interleave the even / odd `w`-bit lanes of their two sources.  Read
at 16-bit granularity that says: the result's lane `j` comes from the first source when the
relevant bit of `j` is clear and from the second when it is set, with that bit of `j` cleared.
Three widths, three bits. -/

/-- `trn1.8h` / `trn2.8h`, at bit 0 of the lane index. -/
theorem trn1_16_lane (a b c : Vec128) (hc : bits c = Model.trn1L16 (bits a) (bits b)) :
    ∀ j < 8, lane16 c j = if j % 2 = 0 then lane16 a j else lane16 b (j - 1) := by
  intro j hj
  show laneOf 16 (bits c) j = _
  rw [hc]
  simp only [Model.trn1L16]
  exact laneOf_ofLanes16 _ hj

theorem trn2_16_lane (a b c : Vec128) (hc : bits c = Model.trn2L16 (bits a) (bits b)) :
    ∀ j < 8, lane16 c j = if j % 2 = 0 then lane16 a (j + 1) else lane16 b j := by
  intro j hj
  show laneOf 16 (bits c) j = _
  rw [hc]
  simp only [Model.trn2L16]
  exact laneOf_ofLanes16 _ hj

/-- A 16-bit lane is half of a 32-bit one. -/
private theorem lane16_of_lane32 (x : Vec128) (n : ℕ) :
    lane16 x n = laneOf 16 (lane32 x (n / 2)) (n % 2) :=
  laneOf_laneOf 16 2 (bits x) n (by omega)

/-- A 16-bit lane is a quarter of a 64-bit one. -/
private theorem lane16_of_lane64 (x : Vec128) (n : ℕ) :
    lane16 x n = laneOf 16 (lane64 x (n / 4)) (n % 4) :=
  laneOf_laneOf 16 4 (bits x) n (by omega)

/-- `trn1.4s`, at bit 1 of the lane index. -/
theorem trn1_32_lane (a b c : Vec128) (hc : bits c = Model.trn1L32 (bits a) (bits b)) :
    ∀ j < 8, lane16 c j = if j / 2 % 2 = 0 then lane16 a j else lane16 b (j - 2) := by
  intro j hj
  have h32 : lane32 c (j / 2)
      = if j / 2 % 2 = 0 then lane32 a (j / 2) else lane32 b (j / 2 - 1) := by
    show laneOf 32 (bits c) (j / 2) = _
    rw [hc]
    simp only [Model.trn1L32]
    exact laneOf_ofLanes32 _ (by omega)
  rw [lane16_of_lane32 c j, h32]
  by_cases he : j / 2 % 2 = 0
  · rw [if_pos he, if_pos he, ← lane16_of_lane32 a j]
  · rw [if_neg he, if_neg he, lane16_of_lane32 b (j - 2),
      show (j - 2) / 2 = j / 2 - 1 from by omega, show (j - 2) % 2 = j % 2 from by omega]

/-- `trn2.4s`, at bit 1 of the lane index. -/
theorem trn2_32_lane (a b c : Vec128) (hc : bits c = Model.trn2L32 (bits a) (bits b)) :
    ∀ j < 8, lane16 c j = if j / 2 % 2 = 0 then lane16 a (j + 2) else lane16 b j := by
  intro j hj
  have h32 : lane32 c (j / 2)
      = if j / 2 % 2 = 0 then lane32 a (j / 2 + 1) else lane32 b (j / 2) := by
    show laneOf 32 (bits c) (j / 2) = _
    rw [hc]
    simp only [Model.trn2L32]
    exact laneOf_ofLanes32 _ (by omega)
  rw [lane16_of_lane32 c j, h32]
  by_cases he : j / 2 % 2 = 0
  · rw [if_pos he, if_pos he, lane16_of_lane32 a (j + 2),
      show (j + 2) / 2 = j / 2 + 1 from by omega, show (j + 2) % 2 = j % 2 from by omega]
  · rw [if_neg he, if_neg he, ← lane16_of_lane32 b j]

/-- `trn1.2d`, at bit 2 of the lane index. -/
theorem trn1_64_lane (a b c : Vec128) (hc : bits c = Model.trn1L64 (bits a) (bits b)) :
    ∀ j < 8, lane16 c j = if j < 4 then lane16 a j else lane16 b (j - 4) := by
  intro j hj
  have h64 : lane64 c (j / 4) = if j < 4 then lane64 a 0 else lane64 b 0 := by
    show laneOf 64 (bits c) (j / 4) = _
    rw [hc]
    simp only [Model.trn1L64]
    rw [laneOf_ofLanes64 _ (by omega)]
    by_cases h : j < 4
    · rw [if_pos h, if_pos (show j / 4 % 2 = 0 from by omega),
        show j / 4 = 0 from by omega]
    · rw [if_neg h, if_neg (show ¬ j / 4 % 2 = 0 from by omega),
        show j / 4 - 1 = 0 from by omega]
  rw [lane16_of_lane64 c j, h64]
  by_cases h : j < 4
  · rw [if_pos h, if_pos h, lane16_of_lane64 a j, show j / 4 = 0 from by omega]
  · rw [if_neg h, if_neg h, lane16_of_lane64 b (j - 4),
      show (j - 4) / 4 = 0 from by omega, show (j - 4) % 4 = j % 4 from by omega]

/-- `trn2.2d`, at bit 2 of the lane index. -/
theorem trn2_64_lane (a b c : Vec128) (hc : bits c = Model.trn2L64 (bits a) (bits b)) :
    ∀ j < 8, lane16 c j = if j < 4 then lane16 a (j + 4) else lane16 b j := by
  intro j hj
  have h64 : lane64 c (j / 4) = if j < 4 then lane64 a 1 else lane64 b 1 := by
    show laneOf 64 (bits c) (j / 4) = _
    rw [hc]
    simp only [Model.trn2L64]
    rw [laneOf_ofLanes64 _ (by omega)]
    by_cases h : j < 4
    · rw [if_pos h, if_pos (show j / 4 % 2 = 0 from by omega),
        show j / 4 + 1 = 1 from by omega]
    · rw [if_neg h, if_neg (show ¬ j / 4 % 2 = 0 from by omega),
        show j / 4 = 1 from by omega]
  rw [lane16_of_lane64 c j, h64]
  by_cases h : j < 4
  · rw [if_pos h, if_pos h, lane16_of_lane64 a (j + 4),
      show (j + 4) / 4 = 1 from by omega, show (j + 4) % 4 = j % 4 from by omega]
  · rw [if_neg h, if_neg h, lane16_of_lane64 b j, show j / 4 = 1 from by omega]

/-! ## The network

Three stages, and the composition swaps the vector index with the lane index. -/

open RustKopisNeon.backend.neon.intrinsics in
/-- **`transpose8` transposes.**  Lane `m` of the result's vector `k` is lane `k` of the input's
vector `m`, which is the property the Rust test `transpose8_permutes_as_documented` asserts and
the one the last three NTT levels rest on. -/
theorem transpose8_spec (v : Array Vec128 8#usize) :
    backend.neon.ntt.transpose8 v
      ⦃ (r : Array Vec128 8#usize) => ∀ k (hk : k < 8) m (hm : m < 8),
          lane16 (vAt r k hk) m = lane16 (vAt v m hm) k ⦄ := by
  have hvlen : v.val.length = 8 := by have := v.property; scalar_tac
  unfold backend.neon.ntt.transpose8
  -- the eight inputs
  let* ⟨ a0, ha0 ⟩ ← Array.index_usize_spec v 0#usize (by scalar_tac)
  let* ⟨ a1, ha1 ⟩ ← Array.index_usize_spec v 1#usize (by scalar_tac)
  obtain ⟨b0, hb0e, hb0b⟩ := trn1_16_model a0 a1
  obtain ⟨b1, hb1e, hb1b⟩ := trn2_16_model a0 a1
  rw [hb0e, bind_tc_ok, hb1e, bind_tc_ok]
  let* ⟨ a2, ha2 ⟩ ← Array.index_usize_spec v 2#usize (by scalar_tac)
  let* ⟨ a3, ha3 ⟩ ← Array.index_usize_spec v 3#usize (by scalar_tac)
  obtain ⟨b2, hb2e, hb2b⟩ := trn1_16_model a2 a3
  obtain ⟨b3, hb3e, hb3b⟩ := trn2_16_model a2 a3
  rw [hb2e, bind_tc_ok, hb3e, bind_tc_ok]
  let* ⟨ a4, ha4 ⟩ ← Array.index_usize_spec v 4#usize (by scalar_tac)
  let* ⟨ a5, ha5 ⟩ ← Array.index_usize_spec v 5#usize (by scalar_tac)
  obtain ⟨b4, hb4e, hb4b⟩ := trn1_16_model a4 a5
  obtain ⟨b5, hb5e, hb5b⟩ := trn2_16_model a4 a5
  rw [hb4e, bind_tc_ok, hb5e, bind_tc_ok]
  let* ⟨ a6, ha6 ⟩ ← Array.index_usize_spec v 6#usize (by scalar_tac)
  let* ⟨ a7, ha7 ⟩ ← Array.index_usize_spec v 7#usize (by scalar_tac)
  obtain ⟨b6, hb6e, hb6b⟩ := trn1_16_model a6 a7
  obtain ⟨b7, hb7e, hb7b⟩ := trn2_16_model a6 a7
  rw [hb6e, bind_tc_ok, hb7e, bind_tc_ok]
  -- stage two
  obtain ⟨c0, hc0e, hc0b⟩ := trn1_32_model b0 b2
  obtain ⟨c2, hc2e, hc2b⟩ := trn2_32_model b0 b2
  obtain ⟨c1, hc1e, hc1b⟩ := trn1_32_model b1 b3
  obtain ⟨c3, hc3e, hc3b⟩ := trn2_32_model b1 b3
  obtain ⟨c4, hc4e, hc4b⟩ := trn1_32_model b4 b6
  obtain ⟨c6, hc6e, hc6b⟩ := trn2_32_model b4 b6
  obtain ⟨c5, hc5e, hc5b⟩ := trn1_32_model b5 b7
  obtain ⟨c7, hc7e, hc7b⟩ := trn2_32_model b5 b7
  rw [hc0e, bind_tc_ok, hc2e, bind_tc_ok, hc1e, bind_tc_ok, hc3e, bind_tc_ok,
    hc4e, bind_tc_ok, hc6e, bind_tc_ok, hc5e, bind_tc_ok, hc7e, bind_tc_ok]
  -- stage three, interleaved with the write-backs
  obtain ⟨d0, hd0e, hd0b⟩ := trn1_64_model c0 c4
  rw [hd0e, bind_tc_ok]
  let* ⟨ u0, hu0 ⟩ ← Array.update_spec
  obtain ⟨d4, hd4e, hd4b⟩ := trn2_64_model c0 c4
  rw [hd4e, bind_tc_ok]
  let* ⟨ u1, hu1 ⟩ ← Array.update_spec
  obtain ⟨d1, hd1e, hd1b⟩ := trn1_64_model c1 c5
  rw [hd1e, bind_tc_ok]
  let* ⟨ u2, hu2 ⟩ ← Array.update_spec
  obtain ⟨d5, hd5e, hd5b⟩ := trn2_64_model c1 c5
  rw [hd5e, bind_tc_ok]
  let* ⟨ u3, hu3 ⟩ ← Array.update_spec
  obtain ⟨d2, hd2e, hd2b⟩ := trn1_64_model c2 c6
  rw [hd2e, bind_tc_ok]
  let* ⟨ u4, hu4 ⟩ ← Array.update_spec
  obtain ⟨d6, hd6e, hd6b⟩ := trn2_64_model c2 c6
  rw [hd6e, bind_tc_ok]
  let* ⟨ u5, hu5 ⟩ ← Array.update_spec
  obtain ⟨d3, hd3e, hd3b⟩ := trn1_64_model c3 c7
  rw [hd3e, bind_tc_ok]
  let* ⟨ u6, hu6 ⟩ ← Array.update_spec
  obtain ⟨d7, hd7e, hd7b⟩ := trn2_64_model c3 c7
  rw [hd7e, bind_tc_ok]
  let* ⟨ u7, hu7 ⟩ ← Array.update_spec
  rename_i k hk m hm
  -- the group's eight vectors, and the result's, resolved through the eight write-backs
  have hstep : ∀ (k : ℕ) (h : k < 8), vAt u7 k h
      = if k = 7 then d7 else if k = 3 then d3 else if k = 6 then d6 else if k = 2 then d2
        else if k = 5 then d5 else if k = 1 then d1 else if k = 4 then d4
        else if k = 0 then d0 else vAt v k h := by
    intro k h
    rw [hu7, vAt_set, hu6, vAt_set, hu5, vAt_set, hu4, vAt_set, hu3, vAt_set, hu2, vAt_set,
      hu1, vAt_set, hu0, vAt_set]
    norm_num
  have o0 : ∀ (h : (0:ℕ) < 8), vAt u7 0 h = d0 := fun h => by rw [hstep 0 h]; norm_num
  have o1 : ∀ (h : (1:ℕ) < 8), vAt u7 1 h = d1 := fun h => by rw [hstep 1 h]; norm_num
  have o2 : ∀ (h : (2:ℕ) < 8), vAt u7 2 h = d2 := fun h => by rw [hstep 2 h]; norm_num
  have o3 : ∀ (h : (3:ℕ) < 8), vAt u7 3 h = d3 := fun h => by rw [hstep 3 h]; norm_num
  have o4 : ∀ (h : (4:ℕ) < 8), vAt u7 4 h = d4 := fun h => by rw [hstep 4 h]; norm_num
  have o5 : ∀ (h : (5:ℕ) < 8), vAt u7 5 h = d5 := fun h => by rw [hstep 5 h]; norm_num
  have o6 : ∀ (h : (6:ℕ) < 8), vAt u7 6 h = d6 := fun h => by rw [hstep 6 h]; norm_num
  have o7 : ∀ (h : (7:ℕ) < 8), vAt u7 7 h = d7 := fun h => by rw [hstep 7 h]; norm_num
  have i0 : ∀ (h : (0:ℕ) < 8), vAt v 0 h = a0 := fun _ => by rw [ha0]; rfl
  have i1 : ∀ (h : (1:ℕ) < 8), vAt v 1 h = a1 := fun _ => by rw [ha1]; rfl
  have i2 : ∀ (h : (2:ℕ) < 8), vAt v 2 h = a2 := fun _ => by rw [ha2]; rfl
  have i3 : ∀ (h : (3:ℕ) < 8), vAt v 3 h = a3 := fun _ => by rw [ha3]; rfl
  have i4 : ∀ (h : (4:ℕ) < 8), vAt v 4 h = a4 := fun _ => by rw [ha4]; rfl
  have i5 : ∀ (h : (5:ℕ) < 8), vAt v 5 h = a5 := fun _ => by rw [ha5]; rfl
  have i6 : ∀ (h : (6:ℕ) < 8), vAt v 6 h = a6 := fun _ => by rw [ha6]; rfl
  have i7 : ∀ (h : (7:ℕ) < 8), vAt v 7 h = a7 := fun _ => by rw [ha7]; rfl
  -- the three stages, each at 16-bit lanes
  have e0 := trn1_16_lane a0 a1 b0 hb0b
  have e1 := trn2_16_lane a0 a1 b1 hb1b
  have e2 := trn1_16_lane a2 a3 b2 hb2b
  have e3 := trn2_16_lane a2 a3 b3 hb3b
  have e4 := trn1_16_lane a4 a5 b4 hb4b
  have e5 := trn2_16_lane a4 a5 b5 hb5b
  have e6 := trn1_16_lane a6 a7 b6 hb6b
  have e7 := trn2_16_lane a6 a7 b7 hb7b
  have f0 := trn1_32_lane b0 b2 c0 hc0b
  have f2 := trn2_32_lane b0 b2 c2 hc2b
  have f1 := trn1_32_lane b1 b3 c1 hc1b
  have f3 := trn2_32_lane b1 b3 c3 hc3b
  have f4 := trn1_32_lane b4 b6 c4 hc4b
  have f6 := trn2_32_lane b4 b6 c6 hc6b
  have f5 := trn1_32_lane b5 b7 c5 hc5b
  have f7 := trn2_32_lane b5 b7 c7 hc7b
  have g0 := trn1_64_lane c0 c4 d0 hd0b
  have g4 := trn2_64_lane c0 c4 d4 hd4b
  have g1 := trn1_64_lane c1 c5 d1 hd1b
  have g5 := trn2_64_lane c1 c5 d5 hd5b
  have g2 := trn1_64_lane c2 c6 d2 hd2b
  have g6 := trn2_64_lane c2 c6 d6 hd6b
  have g3 := trn1_64_lane c3 c7 d3 hd3b
  have g7 := trn2_64_lane c3 c7 d7 hd7b
  -- and now sixty-four lane equations, each three rewrites deep
  rcases show k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 from by omega with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  rcases show m = 0 ∨ m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 4 ∨ m = 5 ∨ m = 6 ∨ m = 7 from by omega with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [o0, o1, o2, o3, o4, o5, o6, o7, i0, i1, i2, i3, i4, i5, i6, i7] <;>
    norm_num [g0, g1, g2, g3, g4, g5, g6, g7, f0, f1, f2, f3, f4, f5, f6, f7,
      e0, e1, e2, e3, e4, e5, e6, e7]

open RustKopisNeon.backend.neon.intrinsics in
/-- **…and doing it twice is the identity.**  This is what gets the transform back to
coefficient order after the three transposed levels, and it is the second half of what the Rust
test asserts. -/
theorem transpose8_involutive (v : Array Vec128 8#usize) :
    (do let w ← backend.neon.ntt.transpose8 v
        backend.neon.ntt.transpose8 w)
      ⦃ (r : Array Vec128 8#usize) => ∀ k (hk : k < 8), vAt r k hk = vAt v k hk ⦄ := by
  apply WP.spec_bind (transpose8_spec v)
  intro w hw
  apply WP.spec_mono (transpose8_spec w)
  intro r hr k hk
  refine vec_eq_of_lane16 (fun m hm => ?_)
  rw [hr k hk m hm, hw m hm k hk]

end Kopis.Neon
