/-
  # Kopis/Avx2/Reduce.lean — `reduce_block`, the inverse NTT's entry point.

  `reduce_invntt` starts by Montgomery-reducing the `i64` accumulator down to two `i16` blocks,
  one per prime.  That is `reduce_block`, and it is where 32-bit lane algebra meets the 16-bit
  algebra the rest of the AVX2 NTT is written in.

  The splitting is the interesting part.  `vpslld`/`vpsrad` by 16 take the low and high halves of
  each `i32`; both already fit an `i16`, so `vpackssdw`'s *signed* saturation is exact, and the
  `vpermq` after it only repairs the lane interleaving the pack introduces.  From there the four
  remaining instructions are the same Montgomery reduction `mont_mul` performs, which is why
  `mont_reduce32` is stated on a bare `i32` rather than on a product.
-/
import Kopis.Avx2.InvWalk
import Kopis.Avx2.NttMulLane
import Kopis.Avx2.SerLane
import Kopis.Avx2.Crt

open Aeneas Aeneas.Std Result
open RustKopisAvx2
open RustKopisAvx2.backend.avx2.intrinsics

namespace Kopis.Avx2

set_option maxHeartbeats 2000000

/-! ## Splitting an `i32` into two `i16` halves

Both halves land inside the `i16` range, so `vpackssdw` never actually saturates. -/

/-- Shifting left 16 then arithmetically right 16 sign-extends the low half. -/
private theorem shl_sar_eq (x : BitVec 32) :
    (x <<< (16 : ℕ)).sshiftRight 16 = (BitVec.extractLsb' 0 16 x).signExtend 32 := by bv_decide

/-- Shifting arithmetically right 16 sign-extends the high half. -/
private theorem sar_eq (x : BitVec 32) :
    x.sshiftRight 16 = (BitVec.extractLsb' 16 16 x).signExtend 32 := by bv_decide

private theorem setWidth_signExtend (y : BitVec 16) :
    BitVec.setWidth 16 (y.signExtend 32) = y := by bv_decide

/-- Signed saturation is the identity on a value that came from an `i16`. -/
theorem satS_signExtend (y : BitVec 16) : satS (y.signExtend 32) = y := by
  have hv : (y.signExtend 32).toInt = y.toInt := by
    have hb := toInt_bounds y
    rw [BitVec.toInt_signExtend]
    rw [show min 32 16 = 16 from by norm_num]
    exact bmod16_eq_self (by omega) (by omega)
  have hb := toInt_bounds y
  unfold satS
  rw [if_neg (by omega), if_neg (by omega)]
  exact setWidth_signExtend y

/-! ## The reduction, lane by lane -/

/-- The `i32` accumulator entry, as a residue. -/
noncomputable def accZ32 (q : ℕ) (a : Array I64 256#usize) (t : ℕ) : ZMod q :=
  (((i32View a t).toInt : ℤ) : ZMod q)

/-- **One vector of `reduce_block`.**  `a0` and `a1` supply the sixteen `i32` at
`8·base + 16·i`; the output vector holds their Montgomery reductions. -/
theorem reduce_vec (a0 a1 v1 v3 v4 lo v5 v6 v7 hi t v8 v9 qv qinvv : Vec256)
    (q : ℕ) (QINV : ℤ) (X : ℕ → ℤ)
    (hq0 : 0 < (q : ℤ)) (hqlt : (q : ℤ) ≤ 2 ^ 15)
    (hu : (2 ^ 16 : ℤ) ∣ (QINV * (q : ℤ) - 1))
    (hQ : ∀ j < 16, (lane16 qv j).toInt = (q : ℤ))
    (hQI : ∀ j < 16, (lane16 qinvv j).toInt = QINV)
    (hX0 : ∀ m < 8, (laneOf 32 (bits a0) m).toInt = X m)
    (hX1 : ∀ m < 8, (laneOf 32 (bits a1) m).toInt = X (8 + m))
    (Xb Rb : ℤ) (hXb : ∀ k < 16, |X k| ≤ Xb) (hXlt : Xb < 2 ^ 15 * (q : ℤ))
    (hRb : Xb + 2 ^ 15 * (q : ℤ) ≤ 2 ^ 16 * Rb)
    (hv1 : bits v1 = Model.sraiEpi32 16 (Model.slliEpi32 16 (bits a0)))
    (hv3 : bits v3 = Model.sraiEpi32 16 (Model.slliEpi32 16 (bits a1)))
    (hv4 : bits v4 = Model.packsEpi32 (bits v1) (bits v3))
    (hlo : bits lo = Model.permute4x64Epi64 (216#i32).bv (bits v4))
    (hv5 : bits v5 = Model.sraiEpi32 16 (bits a0))
    (hv6 : bits v6 = Model.sraiEpi32 16 (bits a1))
    (hv7 : bits v7 = Model.packsEpi32 (bits v5) (bits v6))
    (hhi : bits hi = Model.permute4x64Epi64 (216#i32).bv (bits v7))
    (ht : bits t = Model.mulloEpi16 (bits lo) (bits qinvv))
    (hv8 : bits v8 = Model.mulhiEpi16 (bits t) (bits qv))
    (hv9 : bits v9 = Model.subEpi16 (bits hi) (bits v8)) :
    ∀ k < 16, |(lane16 v9 k).toInt| ≤ Rb ∧
      (q : ℤ) ∣ ((lane16 v9 k).toInt * 2 ^ 16 - X k) := by
  intro k hk
  -- the two halves, from the pack and the permute
  have hlok : (lane16 lo k).toInt = (X k).bmod (2 ^ 16) := by
    rw [pack_permute_lane satS v1 v3 v4 lo (by rw [hv4]; rfl) hlo k hk]
    by_cases hlt : k < 8
    · rw [if_pos hlt, show lane32 v1 k = (BitVec.extractLsb' 0 16 (laneOf 32 (bits a0) k)).signExtend 32 from by
        show laneOf 32 (bits v1) k = _
        rw [hv1]
        simp only [Model.sraiEpi32, Model.slliEpi32]
        rw [laneOf_ofLanes32 _ (by omega), laneOf_ofLanes32 _ (by omega), shl_sar_eq],
        satS_signExtend, toInt_extractLsb'_low, hX0 k hlt]
    · rw [if_neg hlt,
        show lane32 v3 (k - 8)
            = (BitVec.extractLsb' 0 16 (laneOf 32 (bits a1) (k - 8))).signExtend 32 from by
          show laneOf 32 (bits v3) (k - 8) = _
          rw [hv3]
          simp only [Model.sraiEpi32, Model.slliEpi32]
          rw [laneOf_ofLanes32 _ (by omega), laneOf_ofLanes32 _ (by omega), shl_sar_eq],
        satS_signExtend, toInt_extractLsb'_low, hX1 (k - 8) (by omega),
        show 8 + (k - 8) = k from by omega]
  have hhik : (lane16 hi k).toInt = (X k) >>> (16 : ℕ) := by
    rw [pack_permute_lane satS v5 v6 v7 hi (by rw [hv7]; rfl) hhi k hk]
    by_cases hlt : k < 8
    · rw [if_pos hlt,
        show lane32 v5 k = (BitVec.extractLsb' 16 16 (laneOf 32 (bits a0) k)).signExtend 32 from by
          show laneOf 32 (bits v5) k = _
          rw [hv5]
          simp only [Model.sraiEpi32]
          rw [laneOf_ofLanes32 _ (by omega), sar_eq],
        satS_signExtend, toInt_extractLsb'_high, hX0 k hlt]
    · rw [if_neg hlt,
        show lane32 v6 (k - 8)
            = (BitVec.extractLsb' 16 16 (laneOf 32 (bits a1) (k - 8))).signExtend 32 from by
          show laneOf 32 (bits v6) (k - 8) = _
          rw [hv6]
          simp only [Model.sraiEpi32]
          rw [laneOf_ofLanes32 _ (by omega), sar_eq],
        satS_signExtend, toInt_extractLsb'_high, hX1 (k - 8) (by omega),
        show 8 + (k - 8) = k from by omega]
  -- the four Montgomery instructions
  have htk : (lane16 t k).toInt = ((X k).bmod (2 ^ 16) * QINV).bmod (2 ^ 16) := by
    rw [mullo_lane_toInt lo qinvv t ht k hk, hlok, hQI k hk]
  have hv8k : (lane16 v8 k).toInt
      = (((X k).bmod (2 ^ 16) * QINV).bmod (2 ^ 16) * (q : ℤ)) >>> (16 : ℕ) := by
    rw [mulhi_lane_toInt t qv v8 hv8 k hk, htk, hQ k hk]
  obtain ⟨R, hR, hRlo, hRhi, hRdvd, hRsharp⟩ :=
    mont_reduce32 (X := X k) hq0 hqlt hu (lt_of_le_of_lt (hXb k hk) hXlt)
  have hv9k : (lane16 v9 k).toInt = R := by
    rw [sub_lane_toInt hi v8 v9 hv9 k hk, hhik, hv8k, hR]
    exact bmod16_eq_self (by omega) (by omega)
  refine ⟨?_, by rw [hv9k]; exact hRdvd⟩
  rw [hv9k]
  have : (2:ℤ) ^ 16 * |R| ≤ 2 ^ 16 * Rb := by linarith [hRsharp, hXb k hk]
  exact le_of_mul_le_mul_left this (by norm_num)

/-! ## The loop

Output position `c` of the block comes from `i32` position `8·base + c` of the accumulator, so
the postcondition is stated position-wise rather than vector-wise. -/

theorem reduce_block_loop_walk (iter : core.ops.range.Range Usize) (acc : Array I64 256#usize)
    (base : Usize) (b : Array I16 256#usize) (qv qinvv : Vec256) (q : ℕ) (QINV : ℤ)
    (hq0 : 0 < (q : ℤ)) (hqlt : (q : ℤ) ≤ 2 ^ 15)
    (hu : (2 ^ 16 : ℤ) ∣ (QINV * (q : ℤ) - 1))
    (hQ : ∀ j < 16, (lane16 qv j).toInt = (q : ℤ))
    (hQI : ∀ j < 16, (lane16 qinvv j).toInt = QINV)
    (hbase : base.val = 0 ∨ base.val = 32)
    (Xb Rb : ℤ) (hXb : ∀ t < 512, |(i32View acc t).toInt| ≤ Xb)
    (hXlt : Xb < 2 ^ 15 * (q : ℤ)) (hRb : Xb + 2 ^ 15 * (q : ℤ) ≤ 2 ^ 16 * Rb)
    (hend : iter.«end».val = 16)
    (hpre : ∀ c < 256, c / 16 < iter.start.val →
      |(b.val[c]!).val| ≤ Rb ∧
      (q : ℤ) ∣ ((b.val[c]!).val * 2 ^ 16 - (i32View acc (8 * base.val + c)).toInt)) :
    backend.avx2.ntt.reduce_block_loop iter acc base b qv qinvv
      ⦃ (r : Array I16 256#usize) => ∀ c < 256,
          |(r.val[c]!).val| ≤ Rb ∧
          (q : ℤ) ∣ ((r.val[c]!).val * 2 ^ 16 - (i32View acc (8 * base.val + c)).toInt) ⦄ := by
  unfold backend.avx2.ntt.reduce_block_loop
  by_cases hlt : iter.start.val < iter.«end».val
  · let* ⟨ o, iter1, ho, hstart', hend' ⟩ ← core.iter.range.IteratorRange.next_Usize_some_spec
    rw [ho]; simp only
    have hb64 : base.val ≤ 32 := by omega
    step*
    obtain ⟨a0, ha0, ha0b⟩ := load_i32_view acc i2 (by omega)
    rw [ha0, bind_tc_ok]
    step*
    obtain ⟨a1, ha1, ha1b⟩ := load_i32_view acc i4 (by omega)
    rw [ha1, bind_tc_ok]
    obtain ⟨v, hv, hvb⟩ := slli_epi32_model 16#i32 a0 (by scalar_tac)
    rw [hv, bind_tc_ok]
    obtain ⟨v1, hv1, hv1b⟩ := srai_epi32_model 16#i32 v (by scalar_tac)
    rw [hv1, bind_tc_ok]
    obtain ⟨v2, hv2, hv2b⟩ := slli_epi32_model 16#i32 a1 (by scalar_tac)
    rw [hv2, bind_tc_ok]
    obtain ⟨v3, hv3, hv3b⟩ := srai_epi32_model 16#i32 v2 (by scalar_tac)
    rw [hv3, bind_tc_ok]
    obtain ⟨v4, hv4, hv4b⟩ := packs_epi32_model v1 v3
    rw [hv4, bind_tc_ok]
    obtain ⟨lo, hlo, hlob⟩ := permute4x64_epi64_model 216#i32 v4
    rw [hlo, bind_tc_ok]
    obtain ⟨v5, hv5, hv5b⟩ := srai_epi32_model 16#i32 a0 (by scalar_tac)
    rw [hv5, bind_tc_ok]
    obtain ⟨v6, hv6, hv6b⟩ := srai_epi32_model 16#i32 a1 (by scalar_tac)
    rw [hv6, bind_tc_ok]
    obtain ⟨v7, hv7, hv7b⟩ := packs_epi32_model v5 v6
    rw [hv7, bind_tc_ok]
    obtain ⟨hi, hhi, hhib⟩ := permute4x64_epi64_model 216#i32 v7
    rw [hhi, bind_tc_ok]
    obtain ⟨t, ht, htb⟩ := mullo_epi16_model lo qinvv
    rw [ht, bind_tc_ok]
    obtain ⟨v8, hv8, hv8b⟩ := mulhi_epi16_model t qv
    rw [hv8, bind_tc_ok]
    obtain ⟨v9, hv9, hv9b⟩ := sub_epi16_model hi v8
    rw [hv9, bind_tc_ok]
    have himm : (16#i32).val.toNat = 16 := by scalar_tac
    have hi2v : i2.val = base.val + 2 * iter.start.val := by scalar_tac
    have hi4v : i4.val = base.val + 2 * iter.start.val + 1 := by scalar_tac
    have hres := reduce_vec a0 a1 v1 v3 v4 lo v5 v6 v7 hi t v8 v9 qv qinvv q QINV
      (fun k => (i32View acc (8 * base.val + 16 * iter.start.val + k)).toInt)
      hq0 hqlt hu hQ hQI
      (by intro m hm
          rw [show laneOf 32 (bits a0) m = i32View acc (8 * base.val + 16 * iter.start.val + m)
            from by rw [ha0b, accVec, laneOf_ofLanes32 _ hm, hi2v]; congr 1; omega])
      (by intro m hm
          rw [show laneOf 32 (bits a1) m
            = i32View acc (8 * base.val + 16 * iter.start.val + (8 + m))
            from by rw [ha1b, accVec, laneOf_ofLanes32 _ hm, hi4v]; congr 1; omega])
      Xb Rb (by intro k hk; exact hXb _ (by omega)) hXlt hRb
      (by rw [hv1b, hvb, himm]) (by rw [hv3b, hv2b, himm]) hv4b hlob
      (by rw [hv5b, himm]) (by rw [hv6b, himm]) hv7b hhib htb hv8b hv9b
    obtain ⟨b1, hb1, hb1at, hb1oth⟩ := store_i16_at b iter.start v9 (by omega)
    rw [hb1, bind_tc_ok]
    apply reduce_block_loop_walk iter1 acc base b1 qv qinvv q QINV hq0 hqlt hu hQ hQI hbase
      Xb Rb hXb hXlt hRb (by rw [hend']; exact hend)
    intro c hc hcs
    by_cases hthis : c / 16 = iter.start.val
    · rw [show c = 16 * iter.start.val + c % 16 from by omega, hb1at (c % 16) (by omega)]
      have := hres (c % 16) (by omega)
      rw [show 8 * base.val + 16 * iter.start.val + c % 16
        = 8 * base.val + (16 * iter.start.val + c % 16) from by omega] at this
      exact this
    · rw [show c = 16 * (c / 16) + c % 16 from by omega,
        hb1oth (c / 16) (by omega) (by omega) (c % 16) (by omega)]
      have := hpre c hc (by omega)
      rwa [show 16 * (c / 16) + c % 16 = c from by omega]
  · let* ⟨ o, iter1, hnone, _ ⟩ ← core.iter.range.IteratorRange.next_Usize_none_spec
    rw [hnone]; simp only [WP.spec_ok]
    intro c hc
    exact hpre c hc (by omega)
termination_by iter.«end».val - iter.start.val
decreasing_by scalar_decr_tac

/-! ## `reduce_block`

Sets up the two broadcast constants, runs the loop, and hands the result straight to
`invntt_block` — so this is the whole inverse path from the `i64` accumulator to a block of
coefficients, at one prime. -/

/-- Turning the loop's divisibility into the residue identity `b = X·R⁻¹`. -/
theorem reduce_posZ {q : ℕ} {b : Array I16 256#usize} {acc : Array I64 256#usize} {base : ℕ}
    (Rinv : ZMod q) (hR : ((2 ^ 16 : ℤ) : ZMod q) * Rinv = 1)
    (h : ∀ c < 256, (q : ℤ) ∣ ((b.val[c]!).val * 2 ^ 16 - (i32View acc (base + c)).toInt)) :
    ∀ c < 256, posZ q b c = accZ32 q acc (base + c) * Rinv := by
  intro c hc
  obtain ⟨k, hk⟩ := h c hc
  have hcast : (((b.val[c]!).val * 2 ^ 16 - (i32View acc (base + c)).toInt : ℤ) : ZMod q) = 0 := by
    rw [(ZMod.intCast_zmod_eq_zero_iff_dvd _ q)]
    exact ⟨k, hk⟩
  push_cast at hcast
  have hmul : posZ q b c * ((2 ^ 16 : ℤ) : ZMod q) = accZ32 q acc (base + c) := by
    unfold posZ accZ32
    push_cast
    linear_combination hcast
  calc posZ q b c = posZ q b c * (((2 ^ 16 : ℤ) : ZMod q) * Rinv) := by rw [hR]; ring
    _ = (posZ q b c * ((2 ^ 16 : ℤ) : ZMod q)) * Rinv := by ring
    _ = accZ32 q acc (base + c) * Rinv := by rw [hmul]

/-- **`reduce_block` at `q₂`.**  From the `i64` accumulator to the inverse transform's output. -/
theorem reduce_block_q2 (acc : Array I64 256#usize) (b : Array I16 256#usize)
    (hXb : ∀ t < 512, |(i32View acc t).toInt| ≤ 115605504)
    (cst : ZMod 10753) (f : ℕ → ZMod 10753)
    (hst : NttAlg.State zeta2 256 1 cst f
      (fun cc => accZ32 10753 acc (256 + cc) * (1764 : ZMod 10753))) :
    backend.avx2.ntt.reduce_block true acc 32#usize b
      ⦃ (r : Array I16 256#usize) =>
          BlockBnd r 7141 ∧ ∀ cc < 256, posZ 10753 r cc
            = (((2536 : ℤ) : ZMod 10753) * (1764 : ZMod 10753)) * (256 * cst) * f cc ⦄ := by
  unfold backend.avx2.ntt.reduce_block
  rw [show backend.crt.q true = ok backend.crt.Q2 from by simp [backend.crt.q], bind_tc_ok]
  obtain ⟨qv, hqv, hqvl⟩ := set1_epi16_spec backend.crt.Q2
  rw [hqv, bind_tc_ok,
    show backend.crt.qinv true = ok backend.crt.Q2_INV from by simp [backend.crt.qinv],
    bind_tc_ok]
  obtain ⟨qiv, hqiv, hqivl⟩ := set1_epi16_spec backend.crt.Q2_INV
  rw [hqiv, bind_tc_ok]
  have hQ : ∀ j < 16, (lane16 qv j).toInt = ((10753 : ℕ) : ℤ) := fun j hj => by
    rw [hqvl j hj, show (backend.crt.Q2 : I16).bv.toInt = backend.crt.Q2.val from rfl, q2_val]
    norm_num
  have hQI : ∀ j < 16, (lane16 qiv j).toInt = backend.crt.Q2_INV.val := fun j hj => by
    rw [hqivl j hj]; rfl
  apply WP.spec_bind (reduce_block_loop_walk { start := 0#usize, «end» := 16#usize } acc 32#usize
    b qv qiv 10753 backend.crt.Q2_INV.val (by norm_num) (by norm_num)
    (by rw [show (((10753 : ℕ) : ℤ)) = backend.crt.Q2.val from by rw [q2_val]; norm_num]
        exact q2_inv_unit)
    hQ hQI (Or.inr (by scalar_tac)) 115605504 7141
    hXb
    (by norm_num) (by norm_num) rfl (by intro c hc hcs; simp at hcs))
  intro b1 hb1
  simp only [show (32#usize : Usize).val = 32 from by scalar_tac] at hb1
  have hbnd : BlockBnd b1 7141 := fun j hj => (hb1 j hj).1
  have hval : ∀ cc < 256, posZ 10753 b1 cc
      = accZ32 10753 acc (256 + cc) * (1764 : ZMod 10753) :=
    reduce_posZ (1764 : ZMod 10753) (by decide)
      (fun c hc => by have := (hb1 c hc).2; rwa [show 8 * 32 = 256 from by norm_num] at this)
  exact invntt_block_State_q2 b1 cst f _ hst hbnd hval

/-- **`reduce_block` at `q₁`.** -/
theorem reduce_block_q1 (acc : Array I64 256#usize) (b : Array I16 256#usize)
    (hXb : ∀ t < 512, |(i32View acc t).toInt| ≤ 58982400)
    (cst : ZMod 7681) (f : ℕ → ZMod 7681)
    (hst : NttAlg.State zeta1 256 1 cst f
      (fun cc => accZ32 7681 acc (0 + cc) * (900 : ZMod 7681))) :
    backend.avx2.ntt.reduce_block false acc 0#usize b
      ⦃ (r : Array I16 256#usize) =>
          BlockBnd r 4741 ∧ ∀ cc < 256, posZ 7681 r cc
            = (((1912 : ℤ) : ZMod 7681) * (900 : ZMod 7681)) * (256 * cst) * f cc ⦄ := by
  unfold backend.avx2.ntt.reduce_block
  rw [show backend.crt.q false = ok backend.crt.Q1 from by simp [backend.crt.q], bind_tc_ok]
  obtain ⟨qv, hqv, hqvl⟩ := set1_epi16_spec backend.crt.Q1
  rw [hqv, bind_tc_ok,
    show backend.crt.qinv false = ok backend.crt.Q1_INV from by simp [backend.crt.qinv],
    bind_tc_ok]
  obtain ⟨qiv, hqiv, hqivl⟩ := set1_epi16_spec backend.crt.Q1_INV
  rw [hqiv, bind_tc_ok]
  have hQ : ∀ j < 16, (lane16 qv j).toInt = ((7681 : ℕ) : ℤ) := fun j hj => by
    rw [hqvl j hj, show (backend.crt.Q1 : I16).bv.toInt = backend.crt.Q1.val from rfl, q1_val]
    norm_num
  have hQI : ∀ j < 16, (lane16 qiv j).toInt = backend.crt.Q1_INV.val := fun j hj => by
    rw [hqivl j hj]; rfl
  apply WP.spec_bind (reduce_block_loop_walk { start := 0#usize, «end» := 16#usize } acc 0#usize
    b qv qiv 7681 backend.crt.Q1_INV.val (by norm_num) (by norm_num)
    (by rw [show (((7681 : ℕ) : ℤ)) = backend.crt.Q1.val from by rw [q1_val]; norm_num]
        exact q1_inv_unit)
    hQ hQI (Or.inl (by scalar_tac)) 58982400 4741
    hXb
    (by norm_num) (by norm_num) rfl (by intro c hc hcs; simp at hcs))
  intro b1 hb1
  simp only [show (0#usize : Usize).val = 0 from by scalar_tac] at hb1
  have hbnd : BlockBnd b1 4741 := fun j hj => (hb1 j hj).1
  have hval : ∀ cc < 256, posZ 7681 b1 cc = accZ32 7681 acc (0 + cc) * (900 : ZMod 7681) :=
    reduce_posZ (900 : ZMod 7681) (by decide)
      (fun c hc => by have := (hb1 c hc).2; rwa [show 8 * 0 = 0 from by norm_num] at this)
  exact invntt_block_State_q1 b1 cst f _ hst hbnd hval

/-! ## Canonicalising a centred residue

`add(r, and(srai<15>(r), q))` adds `q` exactly to the negative lanes, which moves a centred
residue into `[0, q)`.  It appears three times in the Garner combine — twice on the two residues
and once on the multiplier — and Garner needs canonical representatives, not centred ones. -/

private theorem toInt_eq_zero_or_neg_one (x : BitVec 16) :
    x.toInt >>> (15 : ℕ) = 0 ∨ x.toInt >>> (15 : ℕ) = -1 := by
  have hb := toInt_bounds x
  rw [Int.shiftRight_eq_div_pow]
  norm_num
  omega

private theorem and_zero16 (y : BitVec 16) : (0#16) &&& y = 0#16 := by bv_decide
private theorem and_neg_one16 (y : BitVec 16) : (-1#16) &&& y = y := by bv_decide

/-- **One canonicalisation lane.**  `hQlt` is what keeps the wrapping addition exact: `r + q`
stays inside an `i16` because `2q` does. -/
theorem canon_lane (r qv mask andv out : Vec256) (Q : ℤ) (k : ℕ) (hk : k < 16)
    (hQ : ∀ j < 16, (lane16 qv j).toInt = Q) (hQ0 : 0 < Q) (hQlt : 2 * Q ≤ 2 ^ 15)
    (hr : |(lane16 r k).toInt| < Q)
    (hmask : bits mask = Model.sraiEpi16 15 (bits r))
    (handv : bits andv = Model.andSi256 (bits mask) (bits qv))
    (hout : bits out = Model.addEpi16 (bits r) (bits andv)) :
    (lane16 out k).toInt
        = (if (lane16 r k).toInt < 0 then (lane16 r k).toInt + Q else (lane16 r k).toInt) ∧
      0 ≤ (lane16 out k).toInt ∧ (lane16 out k).toInt < Q ∧
      (Q : ℤ) ∣ ((lane16 out k).toInt - (lane16 r k).toInt) := by
  have hmv : (lane16 mask k).toInt = (lane16 r k).toInt >>> (15 : ℕ) :=
    srai_lane_toInt 15 r mask hmask k hk
  have hrb := toInt_bounds (lane16 r k)
  -- the mask is all zeros or all ones, so the `and` selects `q` or `0`
  have hand : lane16 andv k = lane16 mask k &&& lane16 qv k := by
    show laneOf 16 (bits andv) k = _
    rw [handv]
    simp only [Model.andSi256]
    exact laneOf_and 16 _ _ k
  have haddv : (lane16 out k).toInt
      = ((lane16 r k).toInt + (lane16 andv k).toInt).bmod (2 ^ 16) :=
    add_lane_toInt r andv out hout k hk
  have hcases : (lane16 andv k).toInt = if (lane16 r k).toInt < 0 then Q else 0 := by
    rcases toInt_eq_zero_or_neg_one (lane16 r k) with hz | hn
    · have hnn : ¬ ((lane16 r k).toInt < 0) := by
        rw [Int.shiftRight_eq_div_pow] at hz; norm_num at hz; omega
      have hm0 : lane16 mask k = 0#16 := by
        apply BitVec.eq_of_toInt_eq; rw [hmv, hz]; rfl
      rw [hand, hm0, and_zero16, if_neg hnn]
      rfl
    · have hng : (lane16 r k).toInt < 0 := by
        rw [Int.shiftRight_eq_div_pow] at hn; norm_num at hn; omega
      have hm1 : lane16 mask k = -1#16 := by
        apply BitVec.eq_of_toInt_eq; rw [hmv, hn]; rfl
      rw [hand, hm1, and_neg_one16, hQ k hk, if_pos hng]
  have hval : (lane16 out k).toInt
      = (if (lane16 r k).toInt < 0 then (lane16 r k).toInt + Q else (lane16 r k).toInt) := by
    rw [haddv, hcases]
    split
    · exact bmod16_eq_self (by rw [abs_lt] at hr; omega) (by rw [abs_lt] at hr; omega)
    · rw [add_zero]
      exact bmod16_eq_self (by omega) (by omega)
  refine ⟨hval, ?_, ?_, ?_⟩
  · rw [hval]; split <;> rw [abs_lt] at hr <;> omega
  · rw [hval]; split <;> rw [abs_lt] at hr <;> omega
  · rw [hval]; split
    · exact ⟨1, by ring⟩
    · exact ⟨0, by ring⟩

/-! ## 32-bit lane arithmetic

The 16-bit versions live in `LaneArith.lean`; the Garner combine needs the same three at 32-bit
width, where — unlike the NTT proper — nothing ever wraps, because `a₁ + q₁·t < q₁q₂ < 2³¹`. -/

theorem add32_lane_toInt (a b c : Vec256) (hc : bits c = Model.addEpi32 (bits a) (bits b)) :
    ∀ i < 8, (lane32 c i).toInt = ((lane32 a i).toInt + (lane32 b i).toInt).bmod (2 ^ 32) := by
  intro i hi
  have hl : lane32 c i = lane32 a i + lane32 b i := by
    show laneOf 32 (bits c) i = _
    rw [hc]; simp only [Model.addEpi32]; exact laneOf_ofLanes32 _ hi
  rw [hl, BitVec.toInt_add]

theorem sub32_lane_toInt (a b c : Vec256) (hc : bits c = Model.subEpi32 (bits a) (bits b)) :
    ∀ i < 8, (lane32 c i).toInt = ((lane32 a i).toInt - (lane32 b i).toInt).bmod (2 ^ 32) := by
  intro i hi
  have hl : lane32 c i = lane32 a i - lane32 b i := by
    show laneOf 32 (bits c) i = _
    rw [hc]; simp only [Model.subEpi32]; exact laneOf_ofLanes32 _ hi
  rw [hl, BitVec.toInt_sub]

theorem mullo32_lane_toInt (a b c : Vec256) (hc : bits c = Model.mulloEpi32 (bits a) (bits b)) :
    ∀ i < 8, (lane32 c i).toInt = ((lane32 a i).toInt * (lane32 b i).toInt).bmod (2 ^ 32) := by
  intro i hi
  have hl : lane32 c i = lane32 a i * lane32 b i := by
    show laneOf 32 (bits c) i = _
    rw [hc]; simp only [Model.mulloEpi32]; exact laneOf_ofLanes32 _ hi
  rw [hl, BitVec.toInt_mul]

/-- `vpcmpgtd` lane `i`: all ones exactly where the comparison holds. -/
theorem cmpgt32_lane (a b c : Vec256) (hc : bits c = Model.cmpgtEpi32 (bits a) (bits b)) :
    ∀ i < 8, lane32 c i
      = if (lane32 b i).toInt < (lane32 a i).toInt then BitVec.allOnes 32 else 0#32 := by
  intro i hi
  have hl : lane32 c i
      = if BitVec.slt (lane32 b i) (lane32 a i) then BitVec.allOnes 32 else 0#32 := by
    show laneOf 32 (bits c) i = _
    rw [hc]; simp only [Model.cmpgtEpi32]; exact laneOf_ofLanes32 _ hi
  rw [hl, BitVec.slt_eq_decide]
  split <;> rename_i h <;> simp only [decide_eq_true_eq] at h <;> [rw [if_pos h]; rw [if_neg h]]

private theorem and32_zero (y : BitVec 32) : (0#32) &&& y = 0#32 := by bv_decide
private theorem and32_allOnes (y : BitVec 32) : y &&& (BitVec.allOnes 32) = y := by bv_decide
private theorem and_low16 (v : BitVec 32) :
    v &&& 0xFFFF#32 = BitVec.setWidth 32 (BitVec.setWidth 16 v) := by bv_decide

/-! ## The combine

`x = a₁ + q₁·t`, centred by subtracting `q₁q₂` above the midpoint, then masked to 16 bits.  With
`a₁ < q₁` and `t < q₂` the sum is below `q₁q₂ < 2³¹`, so every 32-bit step is exact. -/

/-- **One lane of the Garner combine.** -/
theorem combine_lane (a1w t1w q1w crtq crtqh low16 v13 x ovm v14 v15 fstv : Vec256)
    (A1 T1 : ℕ → ℤ) (m : ℕ) (hm : m < 8)
    (hA1 : ∀ j < 8, (lane32 a1w j).toInt = A1 j) (hA1r : ∀ j < 8, 0 ≤ A1 j ∧ A1 j < 7681)
    (hT1 : ∀ j < 8, (lane32 t1w j).toInt = T1 j) (hT1r : ∀ j < 8, 0 ≤ T1 j ∧ T1 j < 10753)
    (hq1w : ∀ j < 8, (lane32 q1w j).toInt = 7681)
    (hcq : ∀ j < 8, (lane32 crtq j).toInt = 82593793)
    (hcqh : ∀ j < 8, (lane32 crtqh j).toInt = 41296896)
    (hlow : ∀ j < 8, lane32 low16 j = 0xFFFF#32)
    (hv13 : bits v13 = Model.mulloEpi32 (bits t1w) (bits q1w))
    (hx : bits x = Model.addEpi32 (bits a1w) (bits v13))
    (hover : bits ovm = Model.cmpgtEpi32 (bits x) (bits crtqh))
    (hv14 : bits v14 = Model.andSi256 (bits crtq) (bits ovm))
    (hv15 : bits v15 = Model.subEpi32 (bits x) (bits v14))
    (hfirst : bits fstv = Model.andSi256 (bits v15) (bits low16)) :
    (lane32 fstv m).toNat
        = ((if 41296896 < A1 m + 7681 * T1 m then A1 m + 7681 * T1 m - 82593793
            else A1 m + 7681 * T1 m) % 2 ^ 16).toNat ∧
      (lane32 fstv m).toNat < 2 ^ 16 := by
  obtain ⟨hA0, hA1lt⟩ := hA1r m hm
  obtain ⟨hT0, hT1lt⟩ := hT1r m hm
  have hprod : 0 ≤ 7681 * T1 m ∧ 7681 * T1 m ≤ 82586112 := by
    constructor <;> nlinarith
  -- `t·q₁` and then `a₁ + q₁·t`, both exact
  have h13 : (lane32 v13 m).toInt = T1 m * 7681 := by
    rw [mullo32_lane_toInt t1w q1w v13 hv13 m hm, hT1 m hm, hq1w m hm]
    exact bmod32_eq_self (by omega) (by omega)
  have hxv : (lane32 x m).toInt = A1 m + T1 m * 7681 := by
    rw [add32_lane_toInt a1w v13 x hx m hm, hA1 m hm, h13]
    exact bmod32_eq_self (by omega) (by omega)
  -- the conditional subtraction
  have hovv : lane32 ovm m
      = if 41296896 < A1 m + T1 m * 7681 then BitVec.allOnes 32 else 0#32 := by
    rw [cmpgt32_lane x crtqh ovm hover m hm, hcqh m hm, hxv]
  have h14 : (lane32 v14 m).toInt = if 41296896 < A1 m + T1 m * 7681 then 82593793 else 0 := by
    have hl : lane32 v14 m = lane32 crtq m &&& lane32 ovm m := by
      show laneOf 32 (bits v14) m = _
      rw [hv14]; simp only [Model.andSi256]; exact laneOf_and 32 _ _ m
    rw [hl, hovv]
    split
    · rw [and32_allOnes]; exact hcq m hm
    · rw [BitVec.and_zero]; rfl
  have h15 : (lane32 v15 m).toInt
      = if 41296896 < A1 m + 7681 * T1 m then A1 m + 7681 * T1 m - 82593793
        else A1 m + 7681 * T1 m := by
    rw [sub32_lane_toInt x v14 v15 hv15 m hm, hxv, h14,
      show A1 m + T1 m * 7681 = A1 m + 7681 * T1 m from by ring]
    split
    · refine bmod32_eq_self ?_ ?_ <;> omega
    · rw [sub_zero]; refine bmod32_eq_self ?_ ?_ <;> omega
  -- the mask
  have hfl : lane32 fstv m = BitVec.setWidth 32 (BitVec.setWidth 16 (lane32 v15 m)) := by
    have hl : lane32 fstv m = lane32 v15 m &&& lane32 low16 m := by
      show laneOf 32 (bits fstv) m = _
      rw [hfirst]; simp only [Model.andSi256]; exact laneOf_and 32 _ _ m
    rw [hl, hlow m hm, and_low16]
  have hy : (BitVec.setWidth 16 (lane32 v15 m)).toNat = (lane32 v15 m).toNat % 2 ^ 16 :=
    BitVec.toNat_setWidth _ _
  have hnat : (lane32 fstv m).toNat = (lane32 v15 m).toNat % 2 ^ 16 := by
    rw [hfl, BitVec.toNat_setWidth, hy, Nat.mod_eq_of_lt (by omega)]
  refine ⟨?_, by rw [hnat]; omega⟩
  rw [hnat, ← h15, BitVec.toInt_eq_toNat_bmod]
  have hlt := (lane32 v15 m).isLt
  unfold Int.bmod
  norm_num
  split <;> omega

/-! ## Widening the two halves

`vpmovzxwd` over `vextracti128` reads eight `i16` lanes of a register as eight 32-bit lanes.  Both
inputs are canonical — non-negative and below their prime — so the *zero* extension is right. -/

private theorem toInt_setWidth32 (y : BitVec 16) :
    ((y.setWidth 32).toInt) = (y.toNat : ℤ) := by
  have hy := y.isLt
  rw [BitVec.toInt_eq_toNat_bmod, BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)]
  exact bmod32_eq_self (by omega) (by omega)

theorem widen_lo (a w : Vec256)
    (hw : bits w = Model.cvtepu16Epi32 (Model.castsi256Si128 (bits a))) :
    ∀ m < 8, (lane32 w m).toInt = ((lane16 a m).toNat : ℤ) := by
  intro m hm
  have hl : lane32 w m = (lane16 a m).setWidth 32 := by
    show laneOf 32 (bits w) m = _
    rw [hw]
    simp only [Model.cvtepu16Epi32, Model.castsi256Si128]
    rw [laneOf_ofLanes32 _ hm]
    congr 1
    show laneOf 16 (laneOf 128 (bits a) 0) m = laneOf 16 (bits a) m
    rw [laneOf_laneOf 16 8 (bits a) m (by norm_num),
      show m / 8 = 0 from by omega, show m % 8 = m from by omega]
  rw [hl, toInt_setWidth32]

theorem widen_hi (a w : Vec256)
    (hw : bits w = Model.cvtepu16Epi32 (Model.extracti128Si256 1 (bits a))) :
    ∀ m < 8, (lane32 w m).toInt = ((lane16 a (8 + m)).toNat : ℤ) := by
  intro m hm
  have hl : lane32 w m = (lane16 a (8 + m)).setWidth 32 := by
    show laneOf 32 (bits w) m = _
    rw [hw]
    simp only [Model.cvtepu16Epi32, Model.extracti128Si256]
    rw [laneOf_ofLanes32 _ hm]
    congr 1
    show laneOf 16 (laneOf 128 (bits a) 1) m = laneOf 16 (bits a) (8 + m)
    rw [laneOf_laneOf 16 8 (bits a) (8 + m) (by norm_num),
      show (8 + m) / 8 = 1 from by omega, show (8 + m) % 8 = m from by omega]
  rw [hl, toInt_setWidth32]

/-! ## One vector of the combine

The thirty intrinsic steps of `reduce_invntt_loop`'s body, as one lemma about the vector it
produces.  Everything it needs is proved above; this only threads it together. -/

private theorem toNat_eq_toInt16 (x : BitVec 16) (h : 0 ≤ x.toInt) :
    ((x.toNat : ℤ)) = x.toInt := by
  have hlt := x.isLt
  rw [BitVec.toInt_eq_toNat_bmod] at h ⊢
  unfold Int.bmod at h ⊢
  norm_num at h ⊢
  split at h <;> split <;> omega

/-- **One vector of the Garner combine.**  Sixteen coefficients, from their two centred residues
to the wrapping `u16` the caller wants. -/
theorem combine_vec (r1 r2 q1v q2v qim qimq q1w crtq crtqh low16 : Vec256)
    (mk1 an1 ca1 mk2 an2 ca2 dv tv mk3 an3 ct1 : Vec256)
    (w10 w12 v13 xv ovv v14 v15 fstv : Vec256)
    (w17 w19 v20 xv1 ovv1 v21 v22 sndv v23 packed : Vec256) (Xv : ℕ → ℤ)
    (hq1 : ∀ j < 16, (lane16 q1v j).toInt = 7681)
    (hq2 : ∀ j < 16, (lane16 q2v j).toInt = 10753)
    (hqim : ∀ j < 16, (lane16 qim j).toInt = 3563)
    (hq1w : ∀ j < 8, (lane32 q1w j).toInt = 7681)
    (hcq : ∀ j < 8, (lane32 crtq j).toInt = 82593793)
    (hcqh : ∀ j < 8, (lane32 crtqh j).toInt = 41296896)
    (hlow : ∀ j < 8, lane32 low16 j = 0xFFFF#32)
    (hr1b : ∀ k < 16, |(lane16 r1 k).toInt| < 7681)
    (hr2b : ∀ k < 16, |(lane16 r2 k).toInt| < 10753)
    (hX1 : ∀ k < 16, Xv k ≡ (lane16 r1 k).toInt [ZMOD q1])
    (hX2 : ∀ k < 16, Xv k ≡ (lane16 r2 k).toInt [ZMOD q2])
    (hXb : ∀ k < 16, |Xv k| ≤ 25162752)
    (hmk1 : bits mk1 = Model.sraiEpi16 15 (bits r1))
    (han1 : bits an1 = Model.andSi256 (bits mk1) (bits q1v))
    (hca1 : bits ca1 = Model.addEpi16 (bits r1) (bits an1))
    (hmk2 : bits mk2 = Model.sraiEpi16 15 (bits r2))
    (han2 : bits an2 = Model.andSi256 (bits mk2) (bits q2v))
    (hca2 : bits ca2 = Model.addEpi16 (bits r2) (bits an2))
    (hdv : bits dv = Model.subEpi16 (bits ca2) (bits ca1))
    (htv : ∀ k < 16, (10753 : ℤ) ∣ ((lane16 tv k).toInt * 2 ^ 16
        - (lane16 dv k).toInt * (lane16 qim k).toInt) ∧
      -(10753 : ℤ) < (lane16 tv k).toInt ∧ (lane16 tv k).toInt < 10753)
    (hmk3 : bits mk3 = Model.sraiEpi16 15 (bits tv))
    (han3 : bits an3 = Model.andSi256 (bits mk3) (bits q2v))
    (hct1 : bits ct1 = Model.addEpi16 (bits tv) (bits an3))
    (hw10 : bits w10 = Model.cvtepu16Epi32 (Model.castsi256Si128 (bits ca1)))
    (hw12 : bits w12 = Model.cvtepu16Epi32 (Model.castsi256Si128 (bits ct1)))
    (hv13 : bits v13 = Model.mulloEpi32 (bits w12) (bits q1w))
    (hxv : bits xv = Model.addEpi32 (bits w10) (bits v13))
    (hovv : bits ovv = Model.cmpgtEpi32 (bits xv) (bits crtqh))
    (hv14 : bits v14 = Model.andSi256 (bits crtq) (bits ovv))
    (hv15 : bits v15 = Model.subEpi32 (bits xv) (bits v14))
    (hfstv : bits fstv = Model.andSi256 (bits v15) (bits low16))
    (hw17 : bits w17 = Model.cvtepu16Epi32 (Model.extracti128Si256 1 (bits ca1)))
    (hw19 : bits w19 = Model.cvtepu16Epi32 (Model.extracti128Si256 1 (bits ct1)))
    (hv20 : bits v20 = Model.mulloEpi32 (bits w19) (bits q1w))
    (hxv1 : bits xv1 = Model.addEpi32 (bits w17) (bits v20))
    (hovv1 : bits ovv1 = Model.cmpgtEpi32 (bits xv1) (bits crtqh))
    (hv21 : bits v21 = Model.andSi256 (bits crtq) (bits ovv1))
    (hv22 : bits v22 = Model.subEpi32 (bits xv1) (bits v21))
    (hsndv : bits sndv = Model.andSi256 (bits v22) (bits low16))
    (hv23 : bits v23 = Model.packusEpi32 (bits fstv) (bits sndv))
    (hpacked : bits packed = Model.permute4x64Epi64 (216#i32).bv (bits v23)) :
    ∀ k < 16, ((lane16 packed k).toNat : ℤ) = Xv k % 2 ^ 16 := by
  -- the three canonicalisations
  have hA1 := fun k hk => canon_lane r1 q1v mk1 an1 ca1 7681 k hk hq1 (by norm_num) (by norm_num)
    (hr1b k hk) hmk1 han1 hca1
  have hA2 := fun k hk => canon_lane r2 q2v mk2 an2 ca2 10753 k hk hq2 (by norm_num) (by norm_num)
    (hr2b k hk) hmk2 han2 hca2
  have hTb : ∀ k < 16, |(lane16 tv k).toInt| < 10753 := fun k hk => by
    have := (htv k hk).2; rw [abs_lt]; omega
  have hT1 := fun k hk => canon_lane tv q2v mk3 an3 ct1 10753 k hk hq2 (by norm_num) (by norm_num)
    (hTb k hk) hmk3 han3 hct1
  -- `a₂ − a₁` is exact
  have hdvv : ∀ k < 16, (lane16 dv k).toInt = (lane16 ca2 k).toInt - (lane16 ca1 k).toInt := by
    intro k hk
    obtain ⟨-, h1l, h1h, -⟩ := hA1 k hk
    obtain ⟨-, h2l, h2h, -⟩ := hA2 k hk
    rw [sub_lane_toInt ca2 ca1 dv hdv k hk]
    exact bmod16_eq_self (by omega) (by omega)
  -- Garner's condition
  have hmult : ∀ k < 16, (7681 : ℤ) * (lane16 ct1 k).toInt
      ≡ (lane16 ca2 k).toInt - (lane16 ca1 k).toInt [ZMOD 10753] := by
    intro k hk
    obtain ⟨-, -, -, hd3⟩ := hT1 k hk
    have hbase := garner_mult (d := (lane16 dv k).toInt) (t := (lane16 tv k).toInt)
      (by have := (htv k hk).1; rwa [hqim k hk] at this)
    have hshift : (7681 : ℤ) * (lane16 ct1 k).toInt
        ≡ 7681 * (lane16 tv k).toInt [ZMOD 10753] := by
      obtain ⟨c, hc⟩ := hd3
      rw [Int.modEq_iff_dvd]
      exact ⟨-7681 * c, by linarith [hc]⟩
    rw [← hdvv k hk]
    exact hshift.trans hbase
  -- the reconstruction, per coefficient
  have hgar : ∀ k < 16,
      (if 41296896 < (lane16 ca1 k).toInt + 7681 * (lane16 ct1 k).toInt
       then (lane16 ca1 k).toInt + 7681 * (lane16 ct1 k).toInt - 82593793
       else (lane16 ca1 k).toInt + 7681 * (lane16 ct1 k).toInt) = Xv k := by
    intro k hk
    obtain ⟨-, h1l, h1h, h1d⟩ := hA1 k hk
    obtain ⟨-, h2l, h2h, h2d⟩ := hA2 k hk
    obtain ⟨-, h3l, h3h, -⟩ := hT1 k hk
    refine garner_value (r1 := (lane16 r1 k).toInt) (r2 := (lane16 r2 k).toInt)
      (hX1 k hk) (hX2 k hk) ?_ ⟨h1l, by unfold q1; omega⟩ ?_
      ⟨h2l, by unfold q2; omega⟩ ?_ ⟨h3l, by unfold q2; omega⟩ (hXb k hk)
    · obtain ⟨c, hc⟩ := h1d
      rw [Int.modEq_iff_dvd]
      exact ⟨-c, by unfold q1; linarith [hc]⟩
    · obtain ⟨c, hc⟩ := h2d
      rw [Int.modEq_iff_dvd]
      exact ⟨-c, by unfold q2; linarith [hc]⟩
    · unfold q1 q2
      exact hmult k hk
  -- the widened lanes agree with the canonical residues
  have hlo1 : ∀ j < 8, (lane32 w10 j).toInt = (lane16 ca1 j).toInt := fun j hj => by
    rw [widen_lo ca1 w10 hw10 j hj]
    exact toNat_eq_toInt16 _ (hA1 j (by omega)).2.1
  have hlo2 : ∀ j < 8, (lane32 w12 j).toInt = (lane16 ct1 j).toInt := fun j hj => by
    rw [widen_lo ct1 w12 hw12 j hj]
    exact toNat_eq_toInt16 _ (hT1 j (by omega)).2.1
  have hhi1 : ∀ j < 8, (lane32 w17 j).toInt = (lane16 ca1 (8 + j)).toInt := fun j hj => by
    rw [widen_hi ca1 w17 hw17 j hj]
    exact toNat_eq_toInt16 _ (hA1 (8 + j) (by omega)).2.1
  have hhi2 : ∀ j < 8, (lane32 w19 j).toInt = (lane16 ct1 (8 + j)).toInt := fun j hj => by
    rw [widen_hi ct1 w19 hw19 j hj]
    exact toNat_eq_toInt16 _ (hT1 (8 + j) (by omega)).2.1
  -- the two halves
  have hfst := fun m hm => combine_lane w10 w12 q1w crtq crtqh low16 v13 xv ovv v14 v15 fstv
    (fun j => (lane16 ca1 j).toInt) (fun j => (lane16 ct1 j).toInt) m hm hlo1
    (fun j hj => ⟨(hA1 j (by omega)).2.1, (hA1 j (by omega)).2.2.1⟩) hlo2
    (fun j hj => ⟨(hT1 j (by omega)).2.1, (hT1 j (by omega)).2.2.1⟩)
    hq1w hcq hcqh hlow hv13 hxv hovv hv14 hv15 hfstv
  have hsnd := fun m hm => combine_lane w17 w19 q1w crtq crtqh low16 v20 xv1 ovv1 v21 v22 sndv
    (fun j => (lane16 ca1 (8 + j)).toInt) (fun j => (lane16 ct1 (8 + j)).toInt) m hm hhi1
    (fun j hj => ⟨(hA1 (8 + j) (by omega)).2.1, (hA1 (8 + j) (by omega)).2.2.1⟩) hhi2
    (fun j hj => ⟨(hT1 (8 + j) (by omega)).2.1, (hT1 (8 + j) (by omega)).2.2.1⟩)
    hq1w hcq hcqh hlow hv20 hxv1 hovv1 hv21 hv22 hsndv
  -- the pack is exact
  have hpk := pack_permute_u16 fstv sndv v23 packed (fun m hm => (hfst m hm).2)
    (fun m hm => (hsnd m hm).2) hv23 hpacked
  intro k hk
  rw [hpk k hk]
  by_cases hlt : k < 8
  · rw [if_pos hlt, (hfst k hlt).1, hgar k hk]
    exact Int.toNat_of_nonneg (Int.emod_nonneg _ (by norm_num))
  · rw [if_neg hlt, (hsnd (k - 8) (by omega)).1,
      show 8 + (k - 8) = k from by omega, hgar k hk]
    exact Int.toNat_of_nonneg (Int.emod_nonneg _ (by norm_num))

/-! ## The loop -/

theorem reduce_invntt_loop_walk (iter : core.ops.range.Range Usize)
    (v1 v2 : Array I16 256#usize) (q1v q2v qim qimq q1w crtq crtqh low16 : Vec256)
    (out : Array U16 256#usize) (X : ℕ → ℤ)
    (hq1 : ∀ j < 16, (lane16 q1v j).toInt = 7681)
    (hq2 : ∀ j < 16, (lane16 q2v j).toInt = 10753)
    (hqim : ∀ j < 16, (lane16 qim j).toInt = 3563)
    (hqimq : ∀ j < 16, (2 ^ 16 : ℤ) ∣ ((lane16 qimq j).toInt * 10753 - (lane16 qim j).toInt))
    (hq1w : ∀ j < 8, (lane32 q1w j).toInt = 7681)
    (hcq : ∀ j < 8, (lane32 crtq j).toInt = 82593793)
    (hcqh : ∀ j < 8, (lane32 crtqh j).toInt = 41296896)
    (hlow : ∀ j < 8, lane32 low16 j = 0xFFFF#32)
    (hr1b : ∀ c < 256, |(v1.val[c]!).val| < 7681)
    (hr2b : ∀ c < 256, |(v2.val[c]!).val| < 10753)
    (hX1 : ∀ c < 256, X c ≡ (v1.val[c]!).val [ZMOD q1])
    (hX2 : ∀ c < 256, X c ≡ (v2.val[c]!).val [ZMOD q2])
    (hXb : ∀ c < 256, |X c| ≤ 25162752)
    (hend : iter.«end».val = 16)
    (hpre : ∀ c < 256, c / 16 < iter.start.val → ((out.val[c]!).val : ℤ) = X c % 2 ^ 16) :
    backend.avx2.ntt.reduce_invntt_loop iter v1 v2 q1v q2v qim qimq q1w crtq crtqh low16 out
      ⦃ (r : Array U16 256#usize) => ∀ c < 256, ((r.val[c]!).val : ℤ) = X c % 2 ^ 16 ⦄ := by
  unfold backend.avx2.ntt.reduce_invntt_loop
  by_cases hlt : iter.start.val < iter.«end».val
  · let* ⟨ o, iter1, ho, hstart', hend' ⟩ ← core.iter.range.IteratorRange.next_Usize_some_spec
    rw [ho]; simp only
    obtain ⟨r1, hr1, hr1v⟩ := load_i16_val v1 iter.start (by omega)
    rw [hr1, bind_tc_ok]
    obtain ⟨r2, hr2, hr2v⟩ := load_i16_val v2 iter.start (by omega)
    rw [hr2, bind_tc_ok]
    have hr1bnd : ∀ k < 16, |(lane16 r1 k).toInt| < 7681 := fun k hk => by
      rw [hr1v k hk]; exact hr1b _ (by omega)
    have hr2bnd : ∀ k < 16, |(lane16 r2 k).toInt| < 10753 := fun k hk => by
      rw [hr2v k hk]; exact hr2b _ (by omega)
    -- canonicalise the first residue
    obtain ⟨mk1, hmk1, hmk1b⟩ := srai_epi16_model 15#i32 r1 (by scalar_tac)
    rw [hmk1, bind_tc_ok]
    obtain ⟨an1, han1, han1b⟩ := and_si256_model mk1 q1v
    rw [han1, bind_tc_ok]
    obtain ⟨ca1, hca1, hca1b⟩ := add_epi16_model r1 an1
    rw [hca1, bind_tc_ok]
    have himm : (15#i32).val.toNat = 15 := by scalar_tac
    have hA1 := fun k hk => canon_lane r1 q1v mk1 an1 ca1 7681 k hk hq1 (by norm_num)
      (by norm_num) (hr1bnd k hk) (by rw [hmk1b, himm]) han1b hca1b
    -- and the second
    obtain ⟨mk2, hmk2, hmk2b⟩ := srai_epi16_model 15#i32 r2 (by scalar_tac)
    rw [hmk2, bind_tc_ok]
    obtain ⟨an2, han2, han2b⟩ := and_si256_model mk2 q2v
    rw [han2, bind_tc_ok]
    obtain ⟨ca2, hca2, hca2b⟩ := add_epi16_model r2 an2
    rw [hca2, bind_tc_ok]
    have hA2 := fun k hk => canon_lane r2 q2v mk2 an2 ca2 10753 k hk hq2 (by norm_num)
      (by norm_num) (hr2bnd k hk) (by rw [hmk2b, himm]) han2b hca2b
    -- the difference, and the Montgomery solve
    obtain ⟨dv, hdv, hdvb⟩ := sub_epi16_model ca2 ca1
    rw [hdv, bind_tc_ok]
    have hdvv : ∀ k < 16, (lane16 dv k).toInt
        = (lane16 ca2 k).toInt - (lane16 ca1 k).toInt := by
      intro k hk
      obtain ⟨-, h1l, h1h, -⟩ := hA1 k hk
      obtain ⟨-, h2l, h2h, -⟩ := hA2 k hk
      rw [sub_lane_toInt ca2 ca1 dv hdvb k hk]
      exact bmod16_eq_self (by omega) (by omega)
    apply WP.spec_bind (mont_mul_lane_spec dv qim qimq q2v 10753 hq2 (by norm_num) (by norm_num)
      hqimq (by
        intro k hk
        obtain ⟨-, h1l, h1h, -⟩ := hA1 k hk
        obtain ⟨-, h2l, h2h, -⟩ := hA2 k hk
        rw [abs_mul, hqim k hk, hdvv k hk]
        have : |(lane16 ca2 k).toInt - (lane16 ca1 k).toInt| ≤ 10752 := by
          rw [abs_le]; omega
        have h3563 : |(3563 : ℤ)| = 3563 := by norm_num
        rw [h3563]
        nlinarith [abs_nonneg ((lane16 ca2 k).toInt - (lane16 ca1 k).toInt)]))
    intro tv htvspec
    -- canonicalise the multiplier
    obtain ⟨mk3, hmk3, hmk3b⟩ := srai_epi16_model 15#i32 tv (by scalar_tac)
    rw [hmk3, bind_tc_ok]
    obtain ⟨an3, han3, han3b⟩ := and_si256_model mk3 q2v
    rw [han3, bind_tc_ok]
    obtain ⟨ct1, hct1, hct1b⟩ := add_epi16_model tv an3
    rw [hct1, bind_tc_ok]
    -- widen, combine, widen, combine
    obtain ⟨h9, hh9, hh9b⟩ := castsi256_si128_model ca1
    rw [hh9, bind_tc_ok]
    obtain ⟨w10, hw10, hw10b⟩ := cvtepu16_epi32_model h9
    rw [hw10, bind_tc_ok]
    obtain ⟨h11, hh11, hh11b⟩ := castsi256_si128_model ct1
    rw [hh11, bind_tc_ok]
    obtain ⟨w12, hw12, hw12b⟩ := cvtepu16_epi32_model h11
    rw [hw12, bind_tc_ok]
    obtain ⟨v13, hv13, hv13b⟩ := mullo_epi32_model w12 q1w
    rw [hv13, bind_tc_ok]
    obtain ⟨xv, hxv, hxvb⟩ := add_epi32_model w10 v13
    rw [hxv, bind_tc_ok]
    obtain ⟨ovv, hovv, hovvb⟩ := cmpgt_epi32_model xv crtqh
    rw [hovv, bind_tc_ok]
    obtain ⟨v14, hv14, hv14b⟩ := and_si256_model crtq ovv
    rw [hv14, bind_tc_ok]
    obtain ⟨v15, hv15, hv15b⟩ := sub_epi32_model xv v14
    rw [hv15, bind_tc_ok]
    obtain ⟨fstv, hfstv, hfstvb⟩ := and_si256_model v15 low16
    rw [hfstv, bind_tc_ok]
    obtain ⟨h16, hh16, hh16b⟩ := extracti128_si256_model 1#i32 ca1 (by scalar_tac)
    rw [hh16, bind_tc_ok]
    obtain ⟨w17, hw17, hw17b⟩ := cvtepu16_epi32_model h16
    rw [hw17, bind_tc_ok]
    obtain ⟨h18, hh18, hh18b⟩ := extracti128_si256_model 1#i32 ct1 (by scalar_tac)
    rw [hh18, bind_tc_ok]
    obtain ⟨w19, hw19, hw19b⟩ := cvtepu16_epi32_model h18
    rw [hw19, bind_tc_ok]
    obtain ⟨v20, hv20, hv20b⟩ := mullo_epi32_model w19 q1w
    rw [hv20, bind_tc_ok]
    obtain ⟨xv1, hxv1, hxv1b⟩ := add_epi32_model w17 v20
    rw [hxv1, bind_tc_ok]
    obtain ⟨ovv1, hovv1, hovv1b⟩ := cmpgt_epi32_model xv1 crtqh
    rw [hovv1, bind_tc_ok]
    obtain ⟨v21, hv21, hv21b⟩ := and_si256_model crtq ovv1
    rw [hv21, bind_tc_ok]
    obtain ⟨v22, hv22, hv22b⟩ := sub_epi32_model xv1 v21
    rw [hv22, bind_tc_ok]
    obtain ⟨sndv, hsndv, hsndvb⟩ := and_si256_model v22 low16
    rw [hsndv, bind_tc_ok]
    obtain ⟨v23, hv23, hv23b⟩ := packus_epi32_model fstv sndv
    rw [hv23, bind_tc_ok]
    obtain ⟨packed, hpacked, hpackedb⟩ := permute4x64_epi64_model 216#i32 v23
    rw [hpacked, bind_tc_ok]
    have himm1 : (1#i32).val.toNat = 1 := by scalar_tac
    have hcomb := combine_vec r1 r2 q1v q2v qim qimq q1w crtq crtqh low16 mk1 an1 ca1 mk2 an2 ca2
      dv tv mk3 an3 ct1 w10 w12 v13 xv ovv v14 v15 fstv w17 w19 v20 xv1 ovv1 v21 v22 sndv v23
      packed (fun k => X (16 * iter.start.val + k))
      hq1 hq2 hqim hq1w hcq hcqh hlow hr1bnd hr2bnd
      (fun k hk => by rw [hr1v k hk]; exact hX1 _ (by omega))
      (fun k hk => by rw [hr2v k hk]; exact hX2 _ (by omega))
      (fun k hk => hXb _ (by omega))
      (by rw [hmk1b, himm]) han1b hca1b (by rw [hmk2b, himm]) han2b hca2b hdvb
      (fun k hk => ⟨(htvspec k hk).1, (htvspec k hk).2.1, (htvspec k hk).2.2.1⟩)
      (by rw [hmk3b, himm]) han3b hct1b
      (by rw [hw10b, hh9b]) (by rw [hw12b, hh11b]) hv13b hxvb hovvb hv14b hv15b hfstvb
      (by rw [hw17b, hh16b, himm1]) (by rw [hw19b, hh18b, himm1]) hv20b hxv1b hovv1b hv21b hv22b
      hsndvb hv23b hpackedb
    obtain ⟨out1, hout1, hout1v⟩ := store_u16_spec out iter.start packed (by scalar_tac)
    rw [hout1, bind_tc_ok]
    apply reduce_invntt_loop_walk iter1 v1 v2 q1v q2v qim qimq q1w crtq crtqh low16 out1 X
      hq1 hq2 hqim hqimq hq1w hcq hcqh hlow hr1b hr2b hX1 hX2 hXb (by rw [hend']; exact hend)
    intro c hc hcs
    have hstore := hout1v c (by simpa using hc)
    have hcast : ∀ (a : Array U16 256#usize) (j : ℕ),
        ((a.val[j]!).val : ℤ) = ((a.val[j]!).bv.toNat : ℤ) := fun _ _ => rfl
    by_cases hthis : c / 16 = iter.start.val
    · rw [hcast out1 c, hstore, if_pos (by omega),
        hcomb (c - 16 * iter.start.val) (by omega),
        show 16 * iter.start.val + (c - 16 * iter.start.val) = c from by omega]
    · rw [hcast out1 c, hstore, if_neg (by omega), ← hcast out c]
      exact hpre c hc (by omega)
  · let* ⟨ o, iter1, hnone, _ ⟩ ← core.iter.range.IteratorRange.next_Usize_none_spec
    rw [hnone]; simp only [WP.spec_ok]
    intro c hc
    exact hpre c hc (by omega)
termination_by iter.«end».val - iter.start.val
decreasing_by scalar_decr_tac

/-! ## The CRT constants -/

unseal backend.crt.CRT_Q in
theorem crt_q_val : backend.crt.CRT_Q.val = 82593793 := by decide

unseal backend.crt.CRT_Q_HALF in
theorem crt_q_half_val : backend.crt.CRT_Q_HALF.val = 41296896 := by decide

unseal backend.crt.CRT_Q1_INV_MONT in
theorem crt_q1_inv_mont_val : backend.crt.CRT_Q1_INV_MONT.val = 3563 := by decide

/-! ## `reduce_invntt`

Two `reduce_block` calls, one per prime, then the combine.  The output is the wrapping `u16` of
each coefficient — the same convention the single-prime backend's `to_wrapping_u16` uses. -/

theorem reduce_invntt_walk (acc : Array I64 256#usize) (X : ℕ → ℤ)
    (hXb : ∀ c < 256, |X c| ≤ 25162752)
    (hacc1 : ∀ t < 512, |(i32View acc t).toInt| ≤ 58982400)
    (hacc2 : ∀ t < 512, |(i32View acc t).toInt| ≤ 115605504)
    (c1 : ZMod 7681) (f1 : ℕ → ZMod 7681)
    (hst1 : NttAlg.State zeta1 256 1 c1 f1
      (fun cc => accZ32 7681 acc (0 + cc) * (900 : ZMod 7681)))
    (c2 : ZMod 10753) (f2 : ℕ → ZMod 10753)
    (hst2 : NttAlg.State zeta2 256 1 c2 f2
      (fun cc => accZ32 10753 acc (256 + cc) * (1764 : ZMod 10753)))
    (hres1 : ∀ c < 256, ((X c : ℤ) : ZMod 7681)
      = (((1912 : ℤ) : ZMod 7681) * (900 : ZMod 7681)) * (256 * c1) * f1 c)
    (hres2 : ∀ c < 256, ((X c : ℤ) : ZMod 10753)
      = (((2536 : ℤ) : ZMod 10753) * (1764 : ZMod 10753)) * (256 * c2) * f2 c) :
    backend.avx2.ntt.reduce_invntt acc
      ⦃ (r : Array U16 256#usize) => ∀ c < 256, ((r.val[c]!).val : ℤ) = X c % 2 ^ 16 ⦄ := by
  unfold backend.avx2.ntt.reduce_invntt
  apply WP.spec_bind (reduce_block_q1 acc _ hacc1 c1 f1 hst1)
  rintro v11 ⟨hb1, hv1⟩
  apply WP.spec_bind (reduce_block_q2 acc _ hacc2 c2 f2 hst2)
  rintro v21 ⟨hb2, hv2⟩
  -- the eight broadcast constants
  obtain ⟨q1v, hq1v, hq1vl⟩ := set1_epi16_spec backend.crt.Q1
  rw [hq1v, bind_tc_ok]
  obtain ⟨q2v, hq2v, hq2vl⟩ := set1_epi16_spec backend.crt.Q2
  rw [hq2v, bind_tc_ok]
  obtain ⟨qim, hqim, hqiml⟩ := set1_epi16_spec backend.crt.CRT_Q1_INV_MONT
  rw [hqim, bind_tc_ok]
  simp only [core.num.I16.wrapping_mul, lift, bind_tc_ok]
  obtain ⟨qimq, hqimq, hqimql⟩ :=
    set1_epi16_spec (IScalar.wrapping_mul backend.crt.CRT_Q1_INV_MONT backend.crt.Q2_INV)
  rw [hqimq, bind_tc_ok]
  have hcastv : (IScalar.cast IScalarTy.I32 backend.crt.Q1).val = 7681 := by
    obtain ⟨y, hy, hyv⟩ := WP.spec_imp_exists
      (Std.IScalar.cast_inBounds_spec IScalarTy.I32 backend.crt.Q1
        (by rw [q1_val]; constructor <;> scalar_tac))
    have he : (ok (IScalar.cast IScalarTy.I32 backend.crt.Q1) : Result I32) = ok y := by
      simpa [lift] using hy
    injection he with he'
    rw [he', hyv, q1_val]
  obtain ⟨q1w, hq1w, hq1wl⟩ := set1_epi32_spec (IScalar.cast IScalarTy.I32 backend.crt.Q1)
  rw [hq1w, bind_tc_ok]
  obtain ⟨crtq, hcrtq, hcrtql⟩ := set1_epi32_spec backend.crt.CRT_Q
  rw [hcrtq, bind_tc_ok]
  obtain ⟨crtqh, hcrtqh, hcrtqhl⟩ := set1_epi32_spec backend.crt.CRT_Q_HALF
  rw [hcrtqh, bind_tc_ok]
  obtain ⟨low16, hlow16, hlow16l⟩ := set1_epi32_spec 65535#i32
  rw [hlow16, bind_tc_ok]
  -- their lane values
  have hq1 : ∀ j < 16, (lane16 q1v j).toInt = 7681 := fun j hj => by
    rw [hq1vl j hj]; exact q1_val
  have hq2 : ∀ j < 16, (lane16 q2v j).toInt = 10753 := fun j hj => by
    rw [hq2vl j hj]; exact q2_val
  have hqimv : ∀ j < 16, (lane16 qim j).toInt = 3563 := fun j hj => by
    rw [hqiml j hj]; exact crt_q1_inv_mont_val
  have hqimqv : ∀ j < 16,
      (2 ^ 16 : ℤ) ∣ ((lane16 qimq j).toInt * 10753 - (lane16 qim j).toInt) := by
    intro j hj
    rw [show (lane16 qimq j).toInt
        = (IScalar.wrapping_mul backend.crt.CRT_Q1_INV_MONT backend.crt.Q2_INV).val from by
          rw [hqimql j hj]; rfl,
      show (lane16 qim j).toInt = (backend.crt.CRT_Q1_INV_MONT : I16).val from by
        rw [hqiml j hj]; rfl,
      IScalar.wrapping_mul_val_eq]
    refine mont_pair rfl ?_
    rw [show (10753 : ℤ) = backend.crt.Q2.val from q2_val.symm]
    exact q2_inv_unit
  have hq1wv : ∀ j < 8, (lane32 q1w j).toInt = 7681 := fun j hj => by
    rw [hq1wl j hj,
      show ((IScalar.cast IScalarTy.I32 backend.crt.Q1) : I32).bv.toInt
        = (IScalar.cast IScalarTy.I32 backend.crt.Q1).val from rfl, hcastv]
  have hcqv : ∀ j < 8, (lane32 crtq j).toInt = 82593793 := fun j hj => by
    rw [hcrtql j hj]; exact crt_q_val
  have hcqhv : ∀ j < 8, (lane32 crtqh j).toInt = 41296896 := fun j hj => by
    rw [hcrtqhl j hj]; exact crt_q_half_val
  have hlowv : ∀ j < 8, lane32 low16 j = 0xFFFF#32 := fun j hj => by
    rw [hlow16l j hj]; rfl
  -- the two residue congruences
  have hX1 : ∀ c < 256, X c ≡ (v11.val[c]!).val [ZMOD q1] := by
    intro c hc
    have hz : ((X c : ℤ) : ZMod 7681) = (((v11.val[c]!).val : ℤ) : ZMod 7681) := by
      rw [hres1 c hc, ← hv1 c hc]; rfl
    have h2 := (ZMod.intCast_eq_intCast_iff _ _ _).mp hz
    unfold q1
    exact_mod_cast h2
  have hX2 : ∀ c < 256, X c ≡ (v21.val[c]!).val [ZMOD q2] := by
    intro c hc
    have hz : ((X c : ℤ) : ZMod 10753) = (((v21.val[c]!).val : ℤ) : ZMod 10753) := by
      rw [hres2 c hc, ← hv2 c hc]; rfl
    have h2 := (ZMod.intCast_eq_intCast_iff _ _ _).mp hz
    unfold q2
    exact_mod_cast h2
  apply WP.spec_mono (reduce_invntt_loop_walk { start := 0#usize, «end» := 16#usize } v11 v21
    q1v q2v qim qimq q1w crtq crtqh low16 _ X hq1 hq2 hqimv hqimqv hq1wv hcqv hcqhv hlowv
    (fun c hc => lt_of_le_of_lt (hb1 c hc) (by norm_num))
    (fun c hc => lt_of_le_of_lt (hb2 c hc) (by norm_num))
    hX1 hX2 hXb rfl (by intro c hc hcs; simp at hcs))
  exact fun r hr => hr

end Kopis.Avx2
