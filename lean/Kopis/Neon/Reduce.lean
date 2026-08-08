/-
  # Kopis/Neon/Reduce.lean — `reduce_block`, the inverse NTT's entry point (plan phase F4).

  `reduce_invntt` starts by Montgomery-reducing the `i32` accumulator down to two `i16` blocks,
  one per prime.  That is `reduce_block`, and it is where 32-bit lane algebra meets the 16-bit
  algebra the rest of the NEON NTT is written in.

  ## The split is exact, and the carry cancels

  `xtn`/`xtn2` take the low halves of eight `i32` lanes and `shrn`/`shrn2 #16` the high halves.
  Read as signed `i16`s neither half is `x`'s quotient and remainder: the low half is `x` centred
  mod `2¹⁶`, and when that is *negative* the high half is one short.  `split32` says exactly that

      x = 2¹⁶·(hi + c) + lo        with c = 1 exactly when lo < 0

  and the `c` is not a nuisance — it is the same `c` the Montgomery step introduces when it
  replaces `lo` by `lo mod 2¹⁶`, so the two cancel and

      r = hi − ⌊t·q / 2¹⁶⌋        with        r·2¹⁶ = x − t·q

  *exactly*, with no correction term.  That is `mont32_lane`, and it is the 32-bit twin of
  `Kopis/Neon/LaneArith.lean`'s `mont_mul_lane`.
-/
import Kopis.Neon.InvWalk
import Kopis.Crt.Scheme

open Aeneas Aeneas.Std Result
open RustKopisNeon
open RustKopisNeon.backend.neon.intrinsics

namespace Kopis.Neon

set_option maxHeartbeats 1000000

/-! ## Splitting an `i32` into two `i16` halves -/

/-- **The split, with its carry.**  Reading both halves as signed `i16`s, the low half is `x`
centred mod `2¹⁶` and the high half is one short exactly when that is negative. -/
theorem split32 (x : BitVec 32) :
    x.toInt = 2 ^ 16 * ((BitVec.extractLsb' 16 16 x).toInt
        + (if (BitVec.setWidth 16 x).toInt < 0 then 1 else 0))
      + (BitVec.setWidth 16 x).toInt := by
  have hx : x.toNat < 2 ^ 32 := x.isLt
  have h1 : (BitVec.setWidth 16 x).toNat = x.toNat % 2 ^ 16 := by
    simp [BitVec.toNat_setWidth]
  have h2 : (BitVec.extractLsb' 16 16 x).toNat = x.toNat / 2 ^ 16 := by
    simp [BitVec.extractLsb', Nat.shiftRight_eq_div_pow]
    omega
  rw [BitVec.toInt_eq_toNat_bmod, BitVec.toInt_eq_toNat_bmod, BitVec.toInt_eq_toNat_bmod,
    h1, h2]
  unfold Int.bmod
  norm_num
  split <;> split <;> split <;> omega

/-- Lane `j` of `xtn`/`xtn2`, as a signed value. -/
theorem xtn_pair_lane (lo hi res : Vec128)
    (hres : bits res = Model.xtnPair32 (bits lo) (bits hi)) (j : ℕ) (hj : j < 8) :
    lane16 res j =
      if j < 4 then BitVec.setWidth 16 (lane32 lo j)
      else BitVec.setWidth 16 (lane32 hi (j - 4)) := by
  show laneOf 16 (bits res) j = _
  rw [hres]
  simp only [Model.xtnPair32]
  exact laneOf_ofLanes16 _ hj

/-- Lane `j` of `shrn`/`shrn2 #16`. -/
theorem shrn_pair_lane (lo hi res : Vec128)
    (hres : bits res = Model.shrn16PairS32 (bits lo) (bits hi)) (j : ℕ) (hj : j < 8) :
    lane16 res j =
      if j < 4 then BitVec.extractLsb' 16 16 (lane32 lo j)
      else BitVec.extractLsb' 16 16 (lane32 hi (j - 4)) := by
  show laneOf 16 (bits res) j = _
  rw [hres]
  simp only [Model.shrn16PairS32]
  exact laneOf_ofLanes16 _ hj

/-! ## The Montgomery reduction of a 32-bit lane -/

/-- **`reduce_block`'s lane step is exact.**  `r · 2¹⁶ = X − t·q`, with no correction term: the
carry `split32` exposes is precisely the one the centred `lo` introduces, and they cancel. -/
theorem mont32_core (X L H V T Q r : ℤ)
    (hsplit : X = 2 ^ 16 * (H + (if L < 0 then 1 else 0)) + L)
    (hLb : -32768 ≤ L) (hLb' : L < 32768)
    (hTQ : T * Q % 65536 = L % 65536)
    (hV : V = T * Q / 65536)
    (hr : r = H - V) :
    r * 65536 = X - T * Q := by
  subst hr hV hsplit
  split <;> omega

/-! ## One vector of the reduction

The eight 32-bit lanes of the pair `(a0, a1)` reduced into one `i16` vector.  `Xof` names the
lane's 32-bit value; the pair's arrangement is `xtn`'s, so lane `j` of the output comes from
`a0`'s lane `j` when `j < 4` and `a1`'s lane `j − 4` otherwise. -/

/-- The 32-bit value lane `j` of the pair carries. -/
noncomputable def Xof (a0 a1 : Vec128) (j : ℕ) : ℤ :=
  if j < 4 then (lane32 a0 j).toInt else (lane32 a1 (j - 4)).toInt

theorem reduce_vec (a0 a1 lo hi t v v1 qv qinvv : Vec128) (q : ℕ) (B32 Bt : ℤ)
    (hlo : bits lo = Model.xtnPair32 (bits a0) (bits a1))
    (hhi : bits hi = Model.shrn16PairS32 (bits a0) (bits a1))
    (ht : bits t = Model.mul16 (bits lo) (bits qinvv))
    (hv : ∀ i < 8, (lane16 v i).toInt = (lane16 t i).toInt * (lane16 qv i).toInt / 65536)
    (hv1 : bits v1 = Model.sub16 (bits hi) (bits v))
    (hQ : ∀ i < 8, (lane16 qv i).toInt = (q : ℤ)) (hQpos : 0 < (q : ℤ)) (hQlt : (q : ℤ) ≤ 2 ^ 14)
    (hqinv : ∀ i < 8, (2 ^ 16 : ℤ) ∣ ((lane16 qinvv i).toInt * (q : ℤ) - 1))
    (hX : ∀ j < 8, |Xof a0 a1 j| ≤ B32) (hB32 : 0 ≤ B32)
    (hBt : B32 + 2 ^ 15 * (q : ℤ) ≤ 2 ^ 16 * Bt) (hBtlt : Bt ≤ 32767) :
    ∀ j < 8, (lane16 v1 j).toInt * 2 ^ 16
        = Xof a0 a1 j - (lane16 t j).toInt * (q : ℤ) ∧ |(lane16 v1 j).toInt| ≤ Bt := by
  intro j hj
  -- the two halves of the lane, read as signed `i16`s
  have hlol : lane16 lo j =
      if j < 4 then BitVec.setWidth 16 (lane32 a0 j)
      else BitVec.setWidth 16 (lane32 a1 (j - 4)) := xtn_pair_lane a0 a1 lo hlo j hj
  have hhil : lane16 hi j =
      if j < 4 then BitVec.extractLsb' 16 16 (lane32 a0 j)
      else BitVec.extractLsb' 16 16 (lane32 a1 (j - 4)) := shrn_pair_lane a0 a1 hi hhi j hj
  have hsplit : Xof a0 a1 j
      = 2 ^ 16 * ((lane16 hi j).toInt + (if (lane16 lo j).toInt < 0 then 1 else 0))
        + (lane16 lo j).toInt := by
    unfold Xof
    rw [hlol, hhil]
    split
    · exact split32 (lane32 a0 j)
    · exact split32 (lane32 a1 (j - 4))
  -- the Montgomery step
  have hTv : (lane16 t j).toInt
      = ((lane16 lo j).toInt * (lane16 qinvv j).toInt).bmod (2 ^ 16) :=
    mul_lane_toInt lo qinvv t ht j hj
  have hTQ : (lane16 t j).toInt * (q : ℤ) % 65536 = (lane16 lo j).toInt % 65536 := by
    obtain ⟨d, hd⟩ := hqinv j hj
    rw [show ((2 : ℤ) ^ 16) = 65536 from by norm_num] at hd
    have hqq : (lane16 qinvv j).toInt * (q : ℤ) = 1 + 65536 * d := by omega
    have h1 : ((lane16 lo j).toInt * (lane16 qinvv j).toInt).bmod (2 ^ 16) % 65536
        = ((lane16 lo j).toInt * (lane16 qinvv j).toInt) % 65536 := bmod_emod _
    rw [hTv, Int.mul_emod, h1, ← Int.mul_emod]
    have h3 : (lane16 lo j).toInt * (lane16 qinvv j).toInt * (q : ℤ)
        = (lane16 lo j).toInt + 65536 * ((lane16 lo j).toInt * d) := by
      rw [mul_assoc, hqq]; ring
    rw [h3, Int.add_mul_emod_self_left]
  have hVv : (lane16 v j).toInt = (lane16 t j).toInt * (q : ℤ) / 65536 := by
    rw [hv j hj, hQ j hj]
  -- the bounds that make the wrapping subtraction exact
  have hTb := toInt_bounds (lane16 t j)
  have hlob := toInt_bounds (lane16 lo j)
  have hhib := toInt_bounds (lane16 hi j)
  have hRb : |(lane16 hi j).toInt - (lane16 v j).toInt| ≤ Bt := by
    have hcore := mont32_core (Xof a0 a1 j) ((lane16 lo j).toInt) ((lane16 hi j).toInt)
      ((lane16 v j).toInt) ((lane16 t j).toInt) (q : ℤ)
      ((lane16 hi j).toInt - (lane16 v j).toInt) hsplit (by omega) (by omega) hTQ hVv rfl
    have hXb := abs_le.mp (hX j hj)
    have hTQb : |(lane16 t j).toInt * (q : ℤ)| ≤ 2 ^ 15 * (q : ℤ) := by
      rw [abs_mul, abs_of_pos hQpos]
      have : |(lane16 t j).toInt| ≤ 2 ^ 15 := by rw [abs_le]; omega
      nlinarith
    rw [abs_le] at hTQb ⊢
    omega
  have hexact : (lane16 v1 j).toInt
      = (lane16 hi j).toInt - (lane16 v j).toInt := by
    rw [sub_lane_toInt hi v v1 hv1 j hj]
    rw [abs_le] at hRb
    exact bmod16_eq_self (by omega) (by omega)
  refine ⟨?_, ?_⟩
  · rw [hexact]
    exact mont32_core (Xof a0 a1 j) ((lane16 lo j).toInt) ((lane16 hi j).toInt)
      ((lane16 v j).toInt) ((lane16 t j).toInt) (q : ℤ)
      ((lane16 hi j).toInt - (lane16 v j).toInt) hsplit (by omega) (by omega) hTQ hVv rfl
  · rw [hexact]; exact hRb

/-! ## The loop

Thirty-two iterations, each reducing two `i32` vectors into one `i16` vector.  The arrangement
lines up exactly: output position `8i + j` comes from accumulator index `4·base + 8i + j`,
whichever half of the pair `j` falls in. -/

/-- Accumulator entry `t`, as a residue. -/
noncomputable def accZ32 (q : ℕ) (acc : Array I32 512#usize) (t : ℕ) : ZMod q :=
  (((acc.val[t]!).val : ℤ) : ZMod q)

theorem reduce_block_loop_walk (iter : core.ops.range.Range Usize) (acc : Array I32 512#usize)
    (base : Usize) (b : Array I16 256#usize) (qv qinvv : Vec128)
    (q : ℕ) (Rinv : ZMod q) (B32 Bt : ℤ)
    (hR : ((2 ^ 16 : ℤ) : ZMod q) * Rinv = 1)
    (hQ : ∀ i < 8, (lane16 qv i).toInt = (q : ℤ)) (hQpos : 0 < (q : ℤ)) (hQlt : (q : ℤ) ≤ 2 ^ 14)
    (hqinv : ∀ i < 8, (2 ^ 16 : ℤ) ∣ ((lane16 qinvv i).toInt * (q : ℤ) - 1))
    (hbase : 4 * base.val + 256 ≤ 512)
    (hacc : ∀ t < 256, |(acc.val[4 * base.val + t]!).val| ≤ B32) (hB32 : 0 ≤ B32)
    (hBt : B32 + 2 ^ 15 * (q : ℤ) ≤ 2 ^ 16 * Bt) (hBtlt : Bt ≤ 32767)
    (hend : iter.«end».val = 32) :
    backend.neon.ntt.reduce_block_loop iter acc base b qv qinvv
      ⦃ (r : Array I16 256#usize) => ∀ p < 256,
          if 8 * iter.start.val ≤ p then
            |(r.val[p]!).val| ≤ Bt ∧ posZ q r p = Rinv * accZ32 q acc (4 * base.val + p)
          else (r.val[p]!).val = (b.val[p]!).val ⦄ := by
  unfold backend.neon.ntt.reduce_block_loop
  by_cases hlt : iter.start.val < iter.«end».val
  · let* ⟨ o, iter1, ho, hstart', hend' ⟩ ← core.iter.range.IteratorRange.next_Usize_some_spec
    rw [ho]
    simp only
    have hi32 : iter.start.val < 32 := by omega
    let* ⟨ i1, hi1 ⟩ ← Std.Usize.mul_spec (x := 2#usize) (y := iter.start) (by scalar_tac)
    let* ⟨ i2, hi2 ⟩ ← Std.Usize.add_spec (x := base) (y := i1) (by scalar_tac)
    have hi2v : i2.val = base.val + 2 * iter.start.val := by scalar_tac
    obtain ⟨a0, ha0, ha0l⟩ := load_i32_spec acc i2 (by scalar_tac)
    rw [ha0, bind_tc_ok]
    let* ⟨ i3, hi3 ⟩ ← Std.Usize.add_spec (x := base) (y := i1) (by scalar_tac)
    let* ⟨ i4, hi4 ⟩ ← Std.Usize.add_spec (x := i3) (y := 1#usize) (by scalar_tac)
    have hi4v : i4.val = base.val + 2 * iter.start.val + 1 := by scalar_tac
    obtain ⟨a1, ha1, ha1l⟩ := load_i32_spec acc i4 (by scalar_tac)
    rw [ha1, bind_tc_ok]
    -- the eight 32-bit values this iteration reduces
    have hXv : ∀ j < 8, Xof a0 a1 j
        = (acc.val[4 * base.val + 8 * iter.start.val + j]!).val := by
      intro j hj
      unfold Xof
      by_cases h4 : j < 4
      · rw [if_pos h4, ha0l j h4,
          show 4 * i2.val + j = 4 * base.val + 8 * iter.start.val + j from by omega]
        rfl
      · rw [if_neg h4, ha1l (j - 4) (by omega),
          show 4 * i4.val + (j - 4) = 4 * base.val + 8 * iter.start.val + j from by omega]
        rfl
    obtain ⟨lo, hloe, hlob⟩ := xtn_pair_32_model a0 a1
    rw [hloe, bind_tc_ok]
    obtain ⟨hi, hhie, hhib⟩ := shrn16_pair_s32_model a0 a1
    rw [hhie, bind_tc_ok]
    obtain ⟨t, hte, htb⟩ := mul_16_model lo qinvv
    rw [hte, bind_tc_ok]
    apply WP.spec_bind (mulhi_spec t qv (fun i hi' => by rw [hQ i hi']; omega))
    intro v hvl
    obtain ⟨v1, hv1e, hv1b⟩ := sub_16_model hi v
    rw [hv1e, bind_tc_ok]
    have hstep := reduce_vec a0 a1 lo hi t v v1 qv qinvv q B32 Bt hlob hhib htb hvl hv1b
      hQ hQpos hQlt hqinv
      (by
        intro j hj
        rw [hXv j hj, show 4 * base.val + 8 * iter.start.val + j
            = 4 * base.val + (8 * iter.start.val + j) from by omega]
        exact hacc _ (by omega)) hB32 hBt hBtlt
    obtain ⟨b1, hb1, hb1v⟩ := store_i16_val b iter.start v1 (by omega)
    rw [hb1, bind_tc_ok]
    apply WP.spec_mono (reduce_block_loop_walk iter1 acc base b1 qv qinvv q Rinv B32 Bt hR hQ
      hQpos hQlt hqinv hbase hacc hB32 hBt hBtlt (by rw [hend']; exact hend))
    intro r hr p hp
    have hrp := hr p hp
    by_cases hge : 8 * iter.start.val ≤ p
    · rw [if_pos hge]
      by_cases hge1 : 8 * iter1.start.val ≤ p
      · rw [if_pos hge1] at hrp
        exact hrp
      · rw [if_neg hge1] at hrp
        obtain ⟨hid, hbnd⟩ := hstep (p - 8 * iter.start.val) (by omega)
        rw [hXv (p - 8 * iter.start.val) (by omega),
          show 4 * base.val + 8 * iter.start.val + (p - 8 * iter.start.val)
            = 4 * base.val + p from by omega] at hid
        have hval : (r.val[p]!).val = (lane16 v1 (p - 8 * iter.start.val)).toInt := by
          rw [hrp, hb1v p hp, if_pos (by omega)]
        refine ⟨by rw [hval]; exact hbnd, ?_⟩
        show posZ q r p = _
        unfold posZ accZ32
        rw [hval]
        have := mont_resZ q Rinv hR ((lane16 v1 (p - 8 * iter.start.val)).toInt)
          ((acc.val[4 * base.val + p]!).val) 1
          ⟨-(lane16 t (p - 8 * iter.start.val)).toInt, by linear_combination hid⟩
        rw [this]
        push_cast
        ring
    · rw [if_neg hge]
      rw [if_neg (by omega)] at hrp
      rw [hrp, hb1v p hp, if_neg (by omega)]
  · let* ⟨ o, iter1, hnone, _ ⟩ ← core.iter.range.IteratorRange.next_Usize_none_spec
    rw [hnone]
    refine (WP.spec_ok _).mpr (fun p hp => ?_)
    rw [if_neg (by scalar_tac)]
termination_by 32 - iter.start.val
decreasing_by scalar_decr_tac

/-! ## `reduce_block`

The constants, the loop, and the inverse transform.  The bound the loop leaves —
`B32/2¹⁶ + q/2`, rounded up — is *exactly* the inverse transform's input bound: `4741` at `q₁`
and `7141` at `q₂`.  That is not a coincidence and it is why `invntt_block`'s chain starts from
those rather than from `(q−1)/2`. -/

open Kopis.CrtZeta in
unseal backend.crt.INVNTT_SCALE_1 in
/-- **`reduce_block` at `q₁`.** -/
theorem reduce_block_val_q1 (acc : Array I32 512#usize) (base : Usize)
    (b : Array I16 256#usize) (a0 : ℕ → ZMod 7681)
    (hbase : 4 * base.val + 256 ≤ 512)
    (hacc : ∀ t < 256, |(acc.val[4 * base.val + t]!).val| ≤ 58982400)
    (ha0 : ∀ c < 256, a0 c = (900 : ZMod 7681) * accZ32 7681 acc (4 * base.val + c)) :
    backend.neon.ntt.reduce_block false acc base b
      ⦃ (r : Array I16 256#usize) => BlockBnd r 4741 ∧ ∀ c < 256,
          posZ 7681 r c
            = (((backend.crt.INVNTT_SCALE_1.val : ℤ) : ZMod 7681) * (900 : ZMod 7681))
                * invAllRaw 7681 zeta1 a0 c ⦄ := by
  unfold backend.neon.ntt.reduce_block
  rw [show backend.crt.q false = ok backend.crt.Q1 from by
      simp only [backend.crt.q, Bool.false_eq_true, if_false], bind_tc_ok]
  obtain ⟨qv, hqv, hqvl⟩ := dup_n_s16_spec backend.crt.Q1
  rw [hqv, bind_tc_ok,
    show backend.crt.qinv false = ok backend.crt.Q1_INV from by
      simp only [backend.crt.qinv, Bool.false_eq_true, if_false], bind_tc_ok]
  obtain ⟨qiv, hqiv, hqivl⟩ := dup_n_s16_spec backend.crt.Q1_INV
  rw [hqiv, bind_tc_ok]
  have hvecs : backend.neon.ntt.VECS = ok 32#usize := by
    simp only [backend.neon.ntt.VECS, consts.RING_DEG]; rfl
  rw [hvecs, bind_tc_ok]
  have hQ : ∀ j < 8, (lane16 qv j).toInt = ((7681 : ℕ) : ℤ) := by
    intro j hj
    rw [hqvl j hj, show (backend.crt.Q1 : I16).bv.toInt = backend.crt.Q1.val from rfl, q1_val]
    norm_num
  have hQI : ∀ j < 8, (2 ^ 16 : ℤ) ∣ ((lane16 qiv j).toInt * ((7681 : ℕ) : ℤ) - 1) := by
    intro j hj
    rw [hqivl j hj, show (backend.crt.Q1_INV : I16).bv.toInt = backend.crt.Q1_INV.val from rfl,
      show (((7681 : ℕ) : ℤ)) = backend.crt.Q1.val from by rw [q1_val]; norm_num]
    exact q1_inv_unit
  apply WP.spec_bind (reduce_block_loop_walk ⟨0#usize, 32#usize⟩ acc base b qv qiv 7681
    (900 : ZMod 7681) 58982400 4741 (by decide) hQ (by norm_num) (by norm_num) hQI hbase hacc
    (by norm_num) (by norm_num) (by norm_num) rfl)
  intro b1 hb1
  apply WP.spec_mono (WP.spec_both (invntt_block_bnd_q1 b1 (fun p hp => (hb1 p hp).1))
    (invntt_block_val_q1 b1 a0 (fun p hp => (hb1 p hp).1)
      (fun c hc => by rw [(hb1 c hc).2, ha0 c hc])))
  exact fun r hr => hr

open Kopis.CrtZeta in
unseal backend.crt.INVNTT_SCALE_2 in
/-- **`reduce_block` at `q₂`.** -/
theorem reduce_block_val_q2 (acc : Array I32 512#usize) (base : Usize)
    (b : Array I16 256#usize) (a0 : ℕ → ZMod 10753)
    (hbase : 4 * base.val + 256 ≤ 512)
    (hacc : ∀ t < 256, |(acc.val[4 * base.val + t]!).val| ≤ 115605504)
    (ha0 : ∀ c < 256, a0 c = (1764 : ZMod 10753) * accZ32 10753 acc (4 * base.val + c)) :
    backend.neon.ntt.reduce_block true acc base b
      ⦃ (r : Array I16 256#usize) => BlockBnd r 7141 ∧ ∀ c < 256,
          posZ 10753 r c
            = (((backend.crt.INVNTT_SCALE_2.val : ℤ) : ZMod 10753) * (1764 : ZMod 10753))
                * invAllRaw 10753 zeta2 a0 c ⦄ := by
  unfold backend.neon.ntt.reduce_block
  rw [show backend.crt.q true = ok backend.crt.Q2 from by
      simp only [backend.crt.q, if_true], bind_tc_ok]
  obtain ⟨qv, hqv, hqvl⟩ := dup_n_s16_spec backend.crt.Q2
  rw [hqv, bind_tc_ok,
    show backend.crt.qinv true = ok backend.crt.Q2_INV from by
      simp only [backend.crt.qinv, if_true], bind_tc_ok]
  obtain ⟨qiv, hqiv, hqivl⟩ := dup_n_s16_spec backend.crt.Q2_INV
  rw [hqiv, bind_tc_ok]
  have hvecs : backend.neon.ntt.VECS = ok 32#usize := by
    simp only [backend.neon.ntt.VECS, consts.RING_DEG]; rfl
  rw [hvecs, bind_tc_ok]
  have hQ : ∀ j < 8, (lane16 qv j).toInt = ((10753 : ℕ) : ℤ) := by
    intro j hj
    rw [hqvl j hj, show (backend.crt.Q2 : I16).bv.toInt = backend.crt.Q2.val from rfl, q2_val]
    norm_num
  have hQI : ∀ j < 8, (2 ^ 16 : ℤ) ∣ ((lane16 qiv j).toInt * ((10753 : ℕ) : ℤ) - 1) := by
    intro j hj
    rw [hqivl j hj, show (backend.crt.Q2_INV : I16).bv.toInt = backend.crt.Q2_INV.val from rfl,
      show (((10753 : ℕ) : ℤ)) = backend.crt.Q2.val from by rw [q2_val]; norm_num]
    exact q2_inv_unit
  apply WP.spec_bind (reduce_block_loop_walk ⟨0#usize, 32#usize⟩ acc base b qv qiv 10753
    (1764 : ZMod 10753) 115605504 7141 (by decide) hQ (by norm_num) (by norm_num) hQI hbase hacc
    (by norm_num) (by norm_num) (by norm_num) rfl)
  intro b1 hb1
  apply WP.spec_mono (WP.spec_both (invntt_block_bnd_q2 b1 (fun p hp => (hb1 p hp).1))
    (invntt_block_val_q2 b1 a0 (fun p hp => (hb1 p hp).1)
      (fun c hc => by rw [(hb1 c hc).2, ha0 c hc])))
  exact fun r hr => hr

/-! ## `split_and_transform`

The forward entry point: read a `RingElem`'s `u16` coefficients as `i16`s, optionally Barrett
them into the centred range, and run the forward transform.  Nothing needs to be assumed about
the coefficients' size: `g` is the *signed* reading of the stored bit pattern, and the Barrett
pass centres whatever that is. -/

theorem split_and_transform_loop_red (iter : core.ops.range.Range Usize)
    (elem : Array U16 256#usize) (out : Array I16 512#usize) (base : Usize)
    (hbase : 8 * base.val + 256 ≤ 512) (qv bm round : Vec128)
    (q : ℕ) (M : ℤ) (g : ℕ → ℤ)
    (hQ : ∀ i < 8, (lane16 qv i).toInt = (q : ℤ)) (hM : ∀ i < 8, (lane16 bm i).toInt = M)
    (hRnd : ∀ i < 8, (lane16 round i).toInt = 2 ^ 10)
    (hQpos : 0 < (q : ℤ)) (hQlt : (q : ℤ) < 2 ^ 14) (hQodd : ¬ (2 ∣ (q : ℤ)))
    (hMpos : 0 < M) (hMlt : M < 2 ^ 15) (hD : |2 ^ 27 - (q : ℤ) * M| ≤ 2047)
    (hg : ∀ c < 256, (elem.val[c]!).bv.toInt = g c)
    (hend : iter.«end».val = 32) :
    backend.neon.ntt.split_and_transform_loop true iter elem out base qv bm round
      ⦃ (r : Array I16 512#usize) => ∀ p < 512,
          if fromVec base.val iter.start.val p then
            2 * |(r.val[p]!).val| < (q : ℤ) ∧
              posZ q r p = ((g (p - 8 * base.val) : ℤ) : ZMod q)
          else (r.val[p]!).val = (out.val[p]!).val ⦄ := by
  unfold backend.neon.ntt.split_and_transform_loop
  by_cases hlt : iter.start.val < iter.«end».val
  · let* ⟨ o, iter1, ho, hstart', hend' ⟩ ← core.iter.range.IteratorRange.next_Usize_some_spec
    rw [ho]
    simp only
    have hi32 : iter.start.val < 32 := by omega
    obtain ⟨x, hx, hxl⟩ := load_u16_spec elem iter.start (by scalar_tac)
    rw [hx, bind_tc_ok, if_pos trivial]
    apply WP.spec_bind (barrett_lane_spec x bm round qv (q : ℤ) M hQ hM hRnd hQpos hQlt hQodd
      hMpos hMlt hD)
    intro x1 hx1
    let* ⟨ i1, hi1 ⟩ ← Std.Usize.add_spec (x := base) (y := iter.start) (by scalar_tac)
    have hi1v : i1.val = base.val + iter.start.val := by scalar_tac
    obtain ⟨b1, hb1, hb1v⟩ := store_i16_gen out i1 x1 (by scalar_tac)
    rw [hb1, bind_tc_ok]
    apply WP.spec_mono (split_and_transform_loop_red iter1 elem b1 base hbase qv bm round q M g
      hQ hM hRnd hQpos hQlt hQodd hMpos hMlt hD hg (by rw [hend']; exact hend))
    intro r hr p hp
    have hrp := hr p hp
    by_cases hge : fromVec base.val iter.start.val p
    · rw [if_pos hge]
      by_cases hge1 : fromVec base.val iter1.start.val p
      · rw [if_pos hge1] at hrp
        exact hrp
      · rw [if_neg hge1] at hrp
        have hp' : p < 512 := by scalar_tac
        have hs1 : iter1.start.val = iter.start.val + 1 := by scalar_tac
        unfold fromVec at hge
        have hlt8 : p < 8 * i1.val + 8 := by
          by_contra hc
          apply hge1
          unfold fromVec
          exact ⟨by omega, by omega⟩
        have hval : (r.val[p]!).val = (lane16 x1 (p - 8 * i1.val)).toInt := by
          rw [hrp, hb1v p hp, if_pos (by omega)]
        obtain ⟨hdvd, hbnd⟩ := hx1 (p - 8 * i1.val) (by omega)
        refine ⟨by rw [hval]; exact hbnd, ?_⟩
        show posZ q r p = _
        unfold posZ
        rw [hval, ← hg (p - 8 * base.val) (by omega),
          show (elem.val[p - 8 * base.val]!).bv.toInt
            = (lane16 x (p - 8 * i1.val)).toInt from by
              rw [hxl (p - 8 * i1.val) (by omega),
                show 8 * iter.start.val + (p - 8 * i1.val)
                  = p - 8 * base.val from by omega]]
        have hcast : (((lane16 x1 (p - 8 * i1.val)).toInt
            - (lane16 x (p - 8 * i1.val)).toInt : ℤ) : ZMod q) = 0 :=
          (ZMod.intCast_zmod_eq_zero_iff_dvd _ q).mpr hdvd
        push_cast at hcast
        linear_combination hcast
    · rw [if_neg hge]
      have hp' : p < 512 := by scalar_tac
      unfold fromVec at hge
      rw [if_neg (by unfold fromVec; omega)] at hrp
      rw [hrp, hb1v p hp, if_neg (by omega)]
  · let* ⟨ o, iter1, hnone, _ ⟩ ← core.iter.range.IteratorRange.next_Usize_none_spec
    rw [hnone]
    refine (WP.spec_ok _).mpr (fun p hp => ?_)
    rw [if_neg (by unfold fromVec; scalar_tac)]
termination_by 32 - iter.start.val
decreasing_by scalar_decr_tac

theorem split_and_transform_loop_nored (iter : core.ops.range.Range Usize)
    (elem : Array U16 256#usize) (out : Array I16 512#usize) (base : Usize)
    (hbase : 8 * base.val + 256 ≤ 512) (qv bm round : Vec128)
    (g : ℕ → ℤ) (hg : ∀ c < 256, (elem.val[c]!).bv.toInt = g c)
    (hend : iter.«end».val = 32) :
    backend.neon.ntt.split_and_transform_loop false iter elem out base qv bm round
      ⦃ (r : Array I16 512#usize) => ∀ p < 512,
          if fromVec base.val iter.start.val p then (r.val[p]!).val = g (p - 8 * base.val)
          else (r.val[p]!).val = (out.val[p]!).val ⦄ := by
  unfold backend.neon.ntt.split_and_transform_loop
  by_cases hlt : iter.start.val < iter.«end».val
  · let* ⟨ o, iter1, ho, hstart', hend' ⟩ ← core.iter.range.IteratorRange.next_Usize_some_spec
    rw [ho]
    simp only
    have hi32 : iter.start.val < 32 := by omega
    obtain ⟨x, hx, hxl⟩ := load_u16_spec elem iter.start (by scalar_tac)
    rw [hx, bind_tc_ok, if_neg (by simp), bind_tc_ok]
    let* ⟨ i1, hi1 ⟩ ← Std.Usize.add_spec (x := base) (y := iter.start) (by scalar_tac)
    have hi1v : i1.val = base.val + iter.start.val := by scalar_tac
    obtain ⟨b1, hb1, hb1v⟩ := store_i16_gen out i1 x (by scalar_tac)
    rw [hb1, bind_tc_ok]
    apply WP.spec_mono (split_and_transform_loop_nored iter1 elem b1 base hbase qv bm round g hg
      (by rw [hend']; exact hend))
    intro r hr p hp
    have hrp := hr p hp
    have hp' : p < 512 := by scalar_tac
    have hs1 : iter1.start.val = iter.start.val + 1 := by scalar_tac
    by_cases hge : fromVec base.val iter.start.val p
    · rw [if_pos hge]
      by_cases hge1 : fromVec base.val iter1.start.val p
      · rw [if_pos hge1] at hrp
        exact hrp
      · rw [if_neg hge1] at hrp
        unfold fromVec at hge
        have hlt8 : p < 8 * i1.val + 8 := by
          by_contra hc
          apply hge1
          unfold fromVec
          exact ⟨by omega, by omega⟩
        rw [hrp, hb1v p hp, if_pos (by omega), ← hg (p - 8 * base.val) (by omega),
          hxl (p - 8 * i1.val) (by omega),
          show 8 * iter.start.val + (p - 8 * i1.val) = p - 8 * base.val from by omega]
    · rw [if_neg hge]
      unfold fromVec at hge
      rw [if_neg (by unfold fromVec; omega)] at hrp
      rw [hrp, hb1v p hp, if_neg (by omega)]
  · let* ⟨ o, iter1, hnone, _ ⟩ ← core.iter.range.IteratorRange.next_Usize_none_spec
    rw [hnone]
    refine (WP.spec_ok _).mpr (fun p hp => ?_)
    rw [if_neg (by unfold fromVec; scalar_tac)]
termination_by 32 - iter.start.val
decreasing_by scalar_decr_tac

/-- **`split_and_transform`, with the reduction.**  The continuation `P` is whatever the caller
wants of `ntt_block`'s result, so this serves both primes and both `NttOK` directions. -/
theorem split_and_transform_walk (SECOND : Bool) (elem : Array U16 256#usize)
    (out : Array I16 512#usize) (base : Usize) (hbase : 8 * base.val + 256 ≤ 512)
    (g : ℕ → ℤ) (q : ℕ) (M A0 : ℤ) (qc mc : I16)
    (hg : ∀ c < 256, (elem.val[c]!).bv.toInt = g c)
    (hqc : backend.crt.q SECOND = ok qc) (hqcv : qc.val = (q : ℤ))
    (hmc : backend.crt.barrett_m SECOND = ok mc) (hmcv : mc.val = M)
    (hQpos : 0 < (q : ℤ)) (hQlt : (q : ℤ) < 2 ^ 14) (hQodd : ¬ (2 ∣ (q : ℤ)))
    (hMpos : 0 < M) (hMlt : M < 2 ^ 15) (hD : |2 ^ 27 - (q : ℤ) * M| ≤ 2047)
    (hA0 : 2 * A0 + 1 ≥ (q : ℤ)) (P : Array I16 512#usize → Prop)
    (hnext : ∀ (bb : Array I16 512#usize),
      (∀ p < 512, fromVec base.val 0 p → |(bb.val[p]!).val| ≤ A0) →
      (∀ p < 512, ¬ fromVec base.val 0 p → (bb.val[p]!).val = (out.val[p]!).val) →
      (∀ c < 256, posZ q bb (8 * base.val + c) = ((g c : ℤ) : ZMod q)) →
      backend.neon.ntt.ntt_block SECOND bb base ⦃ (r : Array I16 512#usize) => P r ⦄) :
    backend.neon.ntt.split_and_transform SECOND true elem out base
      ⦃ (r : Array I16 512#usize) => P r ⦄ := by
  unfold backend.neon.ntt.split_and_transform
  rw [hqc, bind_tc_ok]
  obtain ⟨qv, hqv, hqvl⟩ := dup_n_s16_spec qc
  rw [hqv, bind_tc_ok, hmc, bind_tc_ok]
  obtain ⟨bm, hbm, hbml⟩ := dup_n_s16_spec mc
  rw [hbm, bind_tc_ok]
  have hsh : backend.crt.BARRETT_SH - (1#i32 : Std.I32) = ok (10#i32 : Std.I32) := by
    simp only [backend.crt.BARRETT_SH]
    rfl
  rw [hsh, bind_tc_ok, round_const, bind_tc_ok]
  obtain ⟨rnd, hrnd, hrndl⟩ := dup_n_s16_spec 1024#i16
  rw [hrnd, bind_tc_ok]
  have hvecs : backend.neon.ntt.VECS = ok 32#usize := by
    simp only [backend.neon.ntt.VECS, consts.RING_DEG]; rfl
  rw [hvecs, bind_tc_ok]
  have hQ : ∀ j < 8, (lane16 qv j).toInt = (q : ℤ) := fun j hj => by
    rw [hqvl j hj]; exact hqcv
  have hM : ∀ j < 8, (lane16 bm j).toInt = M := fun j hj => by rw [hbml j hj]; exact hmcv
  have hRnd : ∀ j < 8, (lane16 rnd j).toInt = 2 ^ 10 := fun j hj => by
    rw [hrndl j hj]; decide
  apply WP.spec_bind (split_and_transform_loop_red ⟨0#usize, 32#usize⟩ elem out base hbase
    qv bm rnd q M g hQ hM hRnd hQpos hQlt hQodd hMpos hMlt hD hg rfl)
  intro b1 hb1
  refine hnext b1 (fun p hp hin => ?_) (fun p hp hout => ?_) (fun c hc => ?_)
  · have := hb1 p hp
    rw [if_pos (by unfold fromVec at hin ⊢; scalar_tac)] at this
    have := this.1
    omega
  · have := hb1 p hp
    rw [if_neg (by unfold fromVec at hout ⊢; scalar_tac)] at this
    exact this
  · have := hb1 (8 * base.val + c) (by scalar_tac)
    rw [if_pos (by unfold fromVec; scalar_tac)] at this
    have h2 := this.2
    rwa [show 8 * base.val + c - 8 * base.val = c from by omega] at h2

/-- What one `split_and_transform` call leaves in the window at `base`: centred, congruent to
the eight-layer forward transform of the input view, and outside the window untouched. -/
def HalfOK (q : ℕ) (A : ℤ) (ψ : ℕ → ZMod q) (g : ℕ → ℤ) (base : Usize)
    (out r : Array I16 512#usize) : Prop :=
  (∀ p < 512, fromVec base.val 0 p → |(r.val[p]!).val| ≤ A) ∧
  (∀ p < 512, ¬ fromVec base.val 0 p → (r.val[p]!).val = (out.val[p]!).val) ∧
  (∀ c < 256, posZ q r (8 * base.val + c)
    = fwdAll q ψ (fun c => ((g c : ℤ) : ZMod q)) c) ∧
  Kopis.CrtScheme.NttAlg.State ψ 256 1 1 (fun c => ((g c : ℤ) : ZMod q))
    (fwdAll q ψ (fun c => ((g c : ℤ) : ZMod q)))

open Kopis.CrtScheme.NttAlg in
/-- `split_and_transform` at `q₁`, with the reduction. -/
theorem split_and_transform_q1 (elem : Array U16 256#usize) (out : Array I16 512#usize)
    (base : Usize) (hbase : 8 * base.val + 256 ≤ 512)
    (g : ℕ → ℤ) (hg : ∀ c < 256, (elem.val[c]!).bv.toInt = g c) :
    backend.neon.ntt.split_and_transform false true elem out base
      ⦃ (r : Array I16 512#usize) => HalfOK 7681 3840 zeta1 g base out r ⦄ :=
  split_and_transform_walk false elem out base hbase g 7681 17474 3840 backend.crt.Q1
    backend.crt.Q1_BARRETT_M hg
    (by simp only [backend.crt.q, Bool.false_eq_true, if_false]) (by rw [q1_val]; norm_num)
    (by simp only [backend.crt.barrett_m, Bool.false_eq_true, if_false]) q1_m_val
    (by norm_num) (by norm_num) (by decide) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) _ (fun bb hb hrest hv => by
      apply WP.spec_mono (ntt_block_State_q1 bb base _
        (show 8 * base.val + 256 ≤ (512#usize : Usize).val from hbase)
        (fun p hp hin => hb p hp hin) hv)
      rintro r ⟨hr1, hr2, hr3⟩
      refine ⟨fun p hp hin => ?_, fun p hp hout => ?_, hr2, hr3⟩
      · have := hr1 p hp
        rwa [if_pos hin] at this
      · have := hr1 p hp
        rw [if_neg hout] at this
        rw [this]
        exact hrest p hp hout)

open Kopis.CrtScheme.NttAlg in
/-- `split_and_transform` at `q₂`, with the reduction. -/
theorem split_and_transform_q2 (elem : Array U16 256#usize) (out : Array I16 512#usize)
    (base : Usize) (hbase : 8 * base.val + 256 ≤ 512)
    (g : ℕ → ℤ) (hg : ∀ c < 256, (elem.val[c]!).bv.toInt = g c) :
    backend.neon.ntt.split_and_transform true true elem out base
      ⦃ (r : Array I16 512#usize) => HalfOK 10753 5376 zeta2 g base out r ⦄ :=
  split_and_transform_walk true elem out base hbase g 10753 12482 5376 backend.crt.Q2
    backend.crt.Q2_BARRETT_M hg
    (by simp only [backend.crt.q, if_true]) (by rw [q2_val]; norm_num)
    (by simp only [backend.crt.barrett_m, if_true]) q2_m_val
    (by norm_num) (by norm_num) (by decide) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) _ (fun bb hb hrest hv => by
      apply WP.spec_mono (ntt_block_State_q2 bb base _
        (show 8 * base.val + 256 ≤ (512#usize : Usize).val from hbase)
        (fun p hp hin => hb p hp hin) hv)
      rintro r ⟨hr1, hr2, hr3⟩
      refine ⟨fun p hp hin => ?_, fun p hp hout => ?_, hr2, hr3⟩
      · have := hr1 p hp
        rwa [if_pos hin] at this
      · have := hr1 p hp
        rw [if_neg hout] at this
        rw [this]
        exact hrest p hp hout)

/-! ## …and what `from_ring_elem` establishes

`NttOK` is the NEON twin of AVX2's: both blocks bounded, and both leaf states reached.
`from_ring_elem` is now two `split_and_transform` calls into the same buffer — the first at
vector 0, the second at vector `VECS` — so the only bookkeeping is that the second leaves the
first's half alone. -/

open Kopis.CrtScheme.NttAlg in
/-- What one `from_ring_elem` call establishes about its output. -/
def NttOK (g : ℕ → ℤ) (ne : Array I16 512#usize) : Prop :=
  (∀ c < 256, |(ne.val[c]!).val| ≤ 3840) ∧
  (∀ c < 256, |(ne.val[256 + c]!).val| ≤ 5376) ∧
  State zeta1 256 1 1 (fun c => ((g c : ℤ) : ZMod 7681))
    (fun c => (((ne.val[c]!).val : ℤ) : ZMod 7681)) ∧
  State zeta2 256 1 1 (fun c => ((g c : ℤ) : ZMod 10753))
    (fun c => (((ne.val[256 + c]!).val : ℤ) : ZMod 10753))

open Kopis.CrtScheme.NttAlg in
/-- The two halves, assembled.  Shared by the reducing and the non-reducing entry point: they
differ only in which `split_and_transform` established each half. -/
theorem NttOK_of_halves (g : ℕ → ℤ) (out b1 r : Array I16 512#usize)
    (h1 : HalfOK 7681 3840 zeta1 g 0#usize out b1)
    (h2 : HalfOK 10753 5376 zeta2 g 32#usize b1 r) :
    NttOK g r := by
  obtain ⟨hb1b, -, hb1v, hb1s⟩ := h1
  obtain ⟨hrb, hrr, hrv, hrs⟩ := h2
  have he1 : ∀ c < 256, (r.val[c]!).val = (b1.val[c]!).val := fun c hc =>
    hrr c (by omega) (by unfold fromVec; scalar_tac)
  refine ⟨fun c hc => by rw [he1 c hc]; exact hb1b c (by omega) (by unfold fromVec; scalar_tac),
    fun c hc => hrb (256 + c) (by omega) (by unfold fromVec; scalar_tac), ?_, ?_⟩
  · intro n hn r' hr'
    show (((r.val[n * 1 + r']!).val : ℤ) : ZMod 7681) = _
    rw [he1 (n * 1 + r') (by omega)]
    have := hb1v (n * 1 + r') (by omega)
    unfold posZ at this
    rw [show (8 : ℕ) * (0#usize : Usize).val + (n * 1 + r') = n * 1 + r' from by scalar_tac]
      at this
    rw [this]
    exact hb1s n hn r' hr'
  · intro n hn r' hr'
    show (((r.val[256 + (n * 1 + r')]!).val : ℤ) : ZMod 10753) = _
    have := hrv (n * 1 + r') (by omega)
    unfold posZ at this
    rw [show (8 : ℕ) * (32#usize : Usize).val + (n * 1 + r') = 256 + (n * 1 + r')
      from by scalar_tac] at this
    rw [this]
    exact hrs n hn r' hr'

open Kopis.CrtScheme.NttAlg in
theorem from_ring_elem_NttOK (elem : Array U16 256#usize) (g : ℕ → ℤ)
    (hg : ∀ c < 256, (elem.val[c]!).bv.toInt = g c) :
    backend.neon.ntt.from_ring_elem true elem
      ⦃ (r : Array I16 512#usize) => NttOK g r ⦄ := by
  unfold backend.neon.ntt.from_ring_elem
  have hvecs : backend.neon.ntt.VECS = ok 32#usize := by
    simp only [backend.neon.ntt.VECS, consts.RING_DEG]; rfl
  apply WP.spec_bind (split_and_transform_q1 elem _ 0#usize (by scalar_tac) g hg)
  intro b1 hb1
  rw [hvecs, bind_tc_ok]
  apply WP.spec_mono (split_and_transform_q2 elem b1 32#usize (by scalar_tac) g hg)
  intro r hr
  exact NttOK_of_halves g _ b1 r hb1 hr

/-! ## `from_secret`: the same, without the reduction

`from_secret` skips the Barrett pass, so the coefficients have to be centred already — which they
are, being CBD samples stored as wrapping `u16`.  That is the one hypothesis these carry. -/

theorem split_and_transform_nored_walk (SECOND : Bool) (elem : Array U16 256#usize)
    (out : Array I16 512#usize) (base : Usize) (hbase : 8 * base.val + 256 ≤ 512)
    (g : ℕ → ℤ) (q : ℕ) (A0 : ℤ) (qc mc : I16)
    (hg : ∀ c < 256, (elem.val[c]!).bv.toInt = g c) (hgb : ∀ c < 256, |g c| ≤ A0)
    (hqc : backend.crt.q SECOND = ok qc) (hmc : backend.crt.barrett_m SECOND = ok mc)
    (P : Array I16 512#usize → Prop)
    (hnext : ∀ (bb : Array I16 512#usize),
      (∀ p < 512, fromVec base.val 0 p → |(bb.val[p]!).val| ≤ A0) →
      (∀ p < 512, ¬ fromVec base.val 0 p → (bb.val[p]!).val = (out.val[p]!).val) →
      (∀ c < 256, posZ q bb (8 * base.val + c) = ((g c : ℤ) : ZMod q)) →
      backend.neon.ntt.ntt_block SECOND bb base ⦃ (r : Array I16 512#usize) => P r ⦄) :
    backend.neon.ntt.split_and_transform SECOND false elem out base
      ⦃ (r : Array I16 512#usize) => P r ⦄ := by
  unfold backend.neon.ntt.split_and_transform
  rw [hqc, bind_tc_ok]
  obtain ⟨qv, hqv, hqvl⟩ := dup_n_s16_spec qc
  rw [hqv, bind_tc_ok, hmc, bind_tc_ok]
  obtain ⟨bm, hbm, hbml⟩ := dup_n_s16_spec mc
  rw [hbm, bind_tc_ok]
  have hsh : backend.crt.BARRETT_SH - (1#i32 : Std.I32) = ok (10#i32 : Std.I32) := by
    simp only [backend.crt.BARRETT_SH]
    rfl
  rw [hsh, bind_tc_ok, round_const, bind_tc_ok]
  obtain ⟨rnd, hrnd, hrndl⟩ := dup_n_s16_spec 1024#i16
  rw [hrnd, bind_tc_ok]
  have hvecs : backend.neon.ntt.VECS = ok 32#usize := by
    simp only [backend.neon.ntt.VECS, consts.RING_DEG]; rfl
  rw [hvecs, bind_tc_ok]
  apply WP.spec_bind (split_and_transform_loop_nored ⟨0#usize, 32#usize⟩ elem out base hbase
    qv bm rnd g hg rfl)
  intro b1 hb1
  have hval : ∀ c < 256, (b1.val[8 * base.val + c]!).val = g c := by
    intro c hc
    have h := hb1 (8 * base.val + c) (by scalar_tac)
    rw [if_pos (by unfold fromVec; scalar_tac),
      show 8 * base.val + c - 8 * base.val = c from by omega] at h
    exact h
  refine hnext b1 (fun p hp hin => ?_) (fun p hp hout => ?_) (fun c hc => ?_)
  · have h := hb1 p hp
    rw [if_pos (by unfold fromVec at hin ⊢; scalar_tac)] at h
    rw [h]
    have := hgb (p - 8 * base.val) (by unfold fromVec at hin; omega)
    exact this
  · have h := hb1 p hp
    rw [if_neg (by unfold fromVec at hout ⊢; scalar_tac)] at h
    exact h
  · unfold posZ
    rw [hval c hc]

open Kopis.CrtScheme.NttAlg in
/-- `split_and_transform` at `q₁`, without the reduction. -/
theorem split_and_transform_nored_q1 (elem : Array U16 256#usize) (out : Array I16 512#usize)
    (base : Usize) (hbase : 8 * base.val + 256 ≤ 512) (g : ℕ → ℤ)
    (hg : ∀ c < 256, (elem.val[c]!).bv.toInt = g c) (hgb : ∀ c < 256, |g c| ≤ 3840) :
    backend.neon.ntt.split_and_transform false false elem out base
      ⦃ (r : Array I16 512#usize) => HalfOK 7681 3840 zeta1 g base out r ⦄ :=
  split_and_transform_nored_walk false elem out base hbase g 7681 3840 backend.crt.Q1
    backend.crt.Q1_BARRETT_M hg hgb
    (by simp only [backend.crt.q, Bool.false_eq_true, if_false])
    (by simp only [backend.crt.barrett_m, Bool.false_eq_true, if_false]) _
    (fun bb hb hrest hv => by
      apply WP.spec_mono (ntt_block_State_q1 bb base _
        (show 8 * base.val + 256 ≤ (512#usize : Usize).val from hbase)
        (fun p hp hin => hb p hp hin) hv)
      rintro r ⟨hr1, hr2, hr3⟩
      refine ⟨fun p hp hin => ?_, fun p hp hout => ?_, hr2, hr3⟩
      · have := hr1 p hp
        rwa [if_pos hin] at this
      · have := hr1 p hp
        rw [if_neg hout] at this
        rw [this]
        exact hrest p hp hout)

open Kopis.CrtScheme.NttAlg in
/-- `split_and_transform` at `q₂`, without the reduction. -/
theorem split_and_transform_nored_q2 (elem : Array U16 256#usize) (out : Array I16 512#usize)
    (base : Usize) (hbase : 8 * base.val + 256 ≤ 512) (g : ℕ → ℤ)
    (hg : ∀ c < 256, (elem.val[c]!).bv.toInt = g c) (hgb : ∀ c < 256, |g c| ≤ 5376) :
    backend.neon.ntt.split_and_transform true false elem out base
      ⦃ (r : Array I16 512#usize) => HalfOK 10753 5376 zeta2 g base out r ⦄ :=
  split_and_transform_nored_walk true elem out base hbase g 10753 5376 backend.crt.Q2
    backend.crt.Q2_BARRETT_M hg hgb
    (by simp only [backend.crt.q, if_true])
    (by simp only [backend.crt.barrett_m, if_true]) _
    (fun bb hb hrest hv => by
      apply WP.spec_mono (ntt_block_State_q2 bb base _
        (show 8 * base.val + 256 ≤ (512#usize : Usize).val from hbase)
        (fun p hp hin => hb p hp hin) hv)
      rintro r ⟨hr1, hr2, hr3⟩
      refine ⟨fun p hp hin => ?_, fun p hp hout => ?_, hr2, hr3⟩
      · have := hr1 p hp
        rwa [if_pos hin] at this
      · have := hr1 p hp
        rw [if_neg hout] at this
        rw [this]
        exact hrest p hp hout)

open Kopis.CrtScheme.NttAlg in
theorem from_ring_elem_NttOK_nored (elem : Array U16 256#usize) (g : ℕ → ℤ)
    (hg : ∀ c < 256, (elem.val[c]!).bv.toInt = g c) (hgb : ∀ c < 256, |g c| ≤ 3840) :
    backend.neon.ntt.from_ring_elem false elem
      ⦃ (r : Array I16 512#usize) => NttOK g r ⦄ := by
  unfold backend.neon.ntt.from_ring_elem
  have hvecs : backend.neon.ntt.VECS = ok 32#usize := by
    simp only [backend.neon.ntt.VECS, consts.RING_DEG]; rfl
  apply WP.spec_bind (split_and_transform_nored_q1 elem _ 0#usize (by scalar_tac) g hg hgb)
  intro b1 hb1
  rw [hvecs, bind_tc_ok]
  apply WP.spec_mono (split_and_transform_nored_q2 elem b1 32#usize (by scalar_tac) g hg
    (fun c hc => le_trans (hgb c hc) (by norm_num)))
  intro r hr
  exact NttOK_of_halves g _ b1 r hb1 hr

/-! ## Two of the eight dispatch points -/

theorem from_uniform_NttOK (elem : Array U16 256#usize) (g : ℕ → ℤ)
    (hg : ∀ c < 256, (elem.val[c]!).bv.toInt = g c) :
    backend.neon.ntt.from_uniform elem ⦃ (r : Array I16 512#usize) => NttOK g r ⦄ :=
  from_ring_elem_NttOK elem g hg

theorem from_secret_NttOK (elem : Array U16 256#usize) (g : ℕ → ℤ)
    (hg : ∀ c < 256, (elem.val[c]!).bv.toInt = g c) (hgb : ∀ c < 256, |g c| ≤ 3840) :
    backend.neon.ntt.from_secret elem ⦃ (r : Array I16 512#usize) => NttOK g r ⦄ :=
  from_ring_elem_NttOK_nored elem g hg hgb

/-! ## The pointwise multiply-accumulate

Two blocks of thirty-two vectors.  `smull`/`smull2` widen the eight `i16` products into two
vectors of four `i32`, and the accumulator's index arithmetic lines up exactly: output slot
`256·block + 8·i + j` takes `lhs` and `rhs` at the same position, whichever half of the pair `j`
falls in. -/

theorem toInt32_bounds (x : BitVec 32) : -2147483648 ≤ x.toInt ∧ x.toInt < 2147483648 := by
  have h1 := BitVec.le_toInt x
  have h2 := BitVec.toInt_lt (x := x)
  norm_num at h1 h2
  omega

private theorem bmod32_eq_self (x : ℤ) (h1 : -2147483648 ≤ x) (h2 : x < 2147483648) :
    x.bmod (2 ^ 32) = x := by
  unfold Int.bmod
  norm_num
  omega

/-- `add.4s` lane `i`, wrapping. -/
theorem add32_lane_toInt (a b c : Vec128) (hc : bits c = Model.add32 (bits a) (bits b)) :
    ∀ i < 4, (lane32 c i).toInt = ((lane32 a i).toInt + (lane32 b i).toInt).bmod (2 ^ 32) := by
  intro i hi
  have hl : lane32 c i = lane32 a i + lane32 b i := by
    show laneOf 32 (bits c) i = _
    rw [hc]
    simp only [Model.add32]
    exact laneOf_ofLanes32 _ hi
  rw [hl, BitVec.toInt_add]

/-- `smull.4s` lane `i`: the exact product of two `i16`s. -/
theorem smull_low_lane_toInt (a b c : Vec128) (hc : bits c = Model.smullLowS16 (bits a) (bits b)) :
    ∀ i < 4, (lane32 c i).toInt = (lane16 a i).toInt * (lane16 b i).toInt := by
  intro i hi
  have hl : lane32 c i = (lane16 a i).signExtend 32 * (lane16 b i).signExtend 32 := by
    show laneOf 32 (bits c) i = _
    rw [hc]
    simp only [Model.smullLowS16]
    exact laneOf_ofLanes32 _ hi
  have ha := toInt_bounds (lane16 a i)
  have hb := toInt_bounds (lane16 b i)
  rw [hl, BitVec.toInt_mul, BitVec.toInt_signExtend, BitVec.toInt_signExtend,
    show (2 : ℕ) ^ min 32 16 = 2 ^ 16 from by norm_num,
    bmod16_eq_self (z := (lane16 a i).toInt) (by omega) (by omega),
    bmod16_eq_self (z := (lane16 b i).toInt) (by omega) (by omega)]
  exact bmod32_eq_self _ (by nlinarith) (by nlinarith)

/-- `smull2.4s` lane `i`. -/
theorem smull_high_lane_toInt (a b c : Vec128)
    (hc : bits c = Model.smullHighS16 (bits a) (bits b)) :
    ∀ i < 4, (lane32 c i).toInt = (lane16 a (4 + i)).toInt * (lane16 b (4 + i)).toInt := by
  intro i hi
  have hl : lane32 c i = (lane16 a (4 + i)).signExtend 32 * (lane16 b (4 + i)).signExtend 32 := by
    show laneOf 32 (bits c) i = _
    rw [hc]
    simp only [Model.smullHighS16]
    exact laneOf_ofLanes32 _ hi
  have ha := toInt_bounds (lane16 a (4 + i))
  have hb := toInt_bounds (lane16 b (4 + i))
  rw [hl, BitVec.toInt_mul, BitVec.toInt_signExtend, BitVec.toInt_signExtend,
    show (2 : ℕ) ^ min 32 16 = 2 ^ 16 from by norm_num,
    bmod16_eq_self (z := (lane16 a (4 + i)).toInt) (by omega) (by omega),
    bmod16_eq_self (z := (lane16 b (4 + i)).toInt) (by omega) (by omega)]
  exact bmod32_eq_self _ (by nlinarith) (by nlinarith)

theorem pointwise_inner_walk (iv : Usize) (iter : core.ops.range.Range Usize)
    (acc : Array I32 512#usize) (lhs rhs : Array I16 512#usize) (block : Usize) (B : ℤ)
    (hiv : iv.val = 32) (hblock : block.val < 2) (hend : iter.«end».val = 32)
    (hB : ∀ t < 512, 256 * block.val + 8 * iter.start.val ≤ t → t < 256 * block.val + 256 →
      |(acc.val[t]!).val + (lhs.val[t]!).val * (rhs.val[t]!).val| ≤ B)
    (hBlt : B < 2147483648) :
    backend.neon.ntt.pointwise_mul_acc_loop0_loop0 iv iter acc lhs rhs block
      ⦃ (r : Array I32 512#usize) => ∀ t < 512,
          if 256 * block.val + 8 * iter.start.val ≤ t ∧ t < 256 * block.val + 256 then
            (r.val[t]!).val = (acc.val[t]!).val + (lhs.val[t]!).val * (rhs.val[t]!).val
          else (r.val[t]!).val = (acc.val[t]!).val ⦄ := by
  unfold backend.neon.ntt.pointwise_mul_acc_loop0_loop0
  by_cases hlt : iter.start.val < iter.«end».val
  · let* ⟨ o, iter1, ho, hstart', hend' ⟩ ← core.iter.range.IteratorRange.next_Usize_some_spec
    rw [ho]
    simp only
    have hi32 : iter.start.val < 32 := by omega
    let* ⟨ i2, hi2 ⟩ ← Std.Usize.mul_spec (x := iv) (y := block) (by scalar_tac)
    let* ⟨ i3, hi3 ⟩ ← Std.Usize.add_spec (x := i2) (y := iter.start) (by scalar_tac)
    have hi3v : i3.val = 32 * block.val + iter.start.val := by scalar_tac
    obtain ⟨l, hl, hll⟩ := load_i16_spec lhs i3 (by scalar_tac)
    rw [hl, bind_tc_ok]
    let* ⟨ i4, hi4 ⟩ ← Std.Usize.mul_spec (x := iv) (y := block) (by scalar_tac)
    let* ⟨ i5, hi5 ⟩ ← Std.Usize.add_spec (x := i4) (y := iter.start) (by scalar_tac)
    have hi5v : i5.val = 32 * block.val + iter.start.val := by scalar_tac
    obtain ⟨rr, hr, hrl⟩ := load_i16_spec rhs i5 (by scalar_tac)
    rw [hr, bind_tc_ok]
    obtain ⟨fst, hfst, hfstb⟩ := smull_low_s16_model l rr
    rw [hfst, bind_tc_ok]
    obtain ⟨snd, hsnd, hsndb⟩ := smull_high_s16_model l rr
    rw [hsnd, bind_tc_ok]
    let* ⟨ i6, hi6 ⟩ ← Std.Usize.mul_spec (x := 2#usize) (y := iv) (by scalar_tac)
    let* ⟨ i7, hi7 ⟩ ← Std.Usize.mul_spec (x := i6) (y := block) (by scalar_tac)
    let* ⟨ i8, hi8 ⟩ ← Std.Usize.mul_spec (x := 2#usize) (y := iter.start) (by scalar_tac)
    let* ⟨ a0, ha0 ⟩ ← Std.Usize.add_spec (x := i7) (y := i8) (by scalar_tac)
    have ha0v : a0.val = 64 * block.val + 2 * iter.start.val := by scalar_tac
    let* ⟨ a1, ha1 ⟩ ← Std.Usize.add_spec (x := a0) (y := 1#usize) (by scalar_tac)
    have ha1v : a1.val = a0.val + 1 := by scalar_tac
    obtain ⟨v, hv, hvl⟩ := load_i32_spec acc a0 (by scalar_tac)
    rw [hv, bind_tc_ok]
    obtain ⟨v1, hv1, hv1b⟩ := add_32_model v fst
    rw [hv1, bind_tc_ok]
    obtain ⟨acc1, hacc1, hacc1v⟩ := store_i32_spec acc a0 v1 (by scalar_tac)
    rw [hacc1, bind_tc_ok]
    obtain ⟨v2, hv2, hv2l⟩ := load_i32_spec acc1 a1 (by scalar_tac)
    rw [hv2, bind_tc_ok]
    obtain ⟨v3, hv3, hv3b⟩ := add_32_model v2 snd
    rw [hv3, bind_tc_ok]
    obtain ⟨acc2, hacc2, hacc2v⟩ := store_i32_spec acc1 a1 v3 (by scalar_tac)
    rw [hacc2, bind_tc_ok]
    -- what `acc2` is, slot by slot
    have hpos : ∀ k < 8, 4 * a0.val + k = 256 * block.val + 8 * iter.start.val + k := by
      intro k hk; omega
    have hacc2all : ∀ t < 512, (acc2.val[t]!).val =
        if 256 * block.val + 8 * iter.start.val ≤ t
            ∧ t < 256 * block.val + 8 * iter.start.val + 8 then
          (acc.val[t]!).val + (lhs.val[t]!).val * (rhs.val[t]!).val
        else (acc.val[t]!).val := by
      intro t ht
      by_cases hin : 256 * block.val + 8 * iter.start.val ≤ t
          ∧ t < 256 * block.val + 8 * iter.start.val + 8
      · have hbnd : |(acc.val[t]!).val + (lhs.val[t]!).val * (rhs.val[t]!).val| ≤ B :=
          hB t ht hin.1 (by omega)
        rw [abs_le] at hbnd
        have hbnd2 : -B ≤ (acc.val[t]!).bv.toInt
              + (lhs.val[t]!).bv.toInt * (rhs.val[t]!).bv.toInt ∧
            (acc.val[t]!).bv.toInt + (lhs.val[t]!).bv.toInt * (rhs.val[t]!).bv.toInt ≤ B := hbnd
        rw [if_pos hin]
        by_cases hlo : t < 4 * a0.val + 4
        · -- the low half: `smull` and the first accumulate
          have hk : t - 4 * a0.val < 4 := by omega
          rw [show (acc2.val[t]!).val = (acc2.val[t]!).bv.toInt from rfl,
            hacc2v t (by scalar_tac), if_neg (by omega),
            hacc1v t (by scalar_tac), if_pos (by omega)]
          rw [show ((lane32 v1 (t - 4 * a0.val)) : BitVec 32).toInt
              = ((lane32 v (t - 4 * a0.val)).toInt
                  + (lane32 fst (t - 4 * a0.val)).toInt).bmod (2 ^ 32) from
            add32_lane_toInt v fst v1 hv1b _ hk,
            hvl (t - 4 * a0.val) hk,
            smull_low_lane_toInt l rr fst hfstb (t - 4 * a0.val) hk,
            hll (t - 4 * a0.val) (by omega), hrl (t - 4 * a0.val) (by omega),
            show 4 * a0.val + (t - 4 * a0.val) = t from by omega,
            show 8 * i3.val + (t - 4 * a0.val) = t from by omega,
            show 8 * i5.val + (t - 4 * a0.val) = t from by omega]
          exact bmod32_eq_self _ (by omega) (by omega)
        · -- the high half
          have hk : t - 4 * a1.val < 4 := by omega
          rw [show (acc2.val[t]!).val = (acc2.val[t]!).bv.toInt from rfl,
            hacc2v t (by scalar_tac), if_pos (by omega)]
          rw [show ((lane32 v3 (t - 4 * a1.val)) : BitVec 32).toInt
              = ((lane32 v2 (t - 4 * a1.val)).toInt
                  + (lane32 snd (t - 4 * a1.val)).toInt).bmod (2 ^ 32) from
            add32_lane_toInt v2 snd v3 hv3b _ hk,
            hv2l (t - 4 * a1.val) hk,
            smull_high_lane_toInt l rr snd hsndb (t - 4 * a1.val) hk]
          rw [show (acc1.val[4 * a1.val + (t - 4 * a1.val)]!).bv
              = (acc1.val[t]!).bv from by rw [show 4 * a1.val + (t - 4 * a1.val) = t from by omega],
            hacc1v t (by scalar_tac), if_neg (by omega),
            hll (4 + (t - 4 * a1.val)) (by omega), hrl (4 + (t - 4 * a1.val)) (by omega),
            show 8 * i3.val + (4 + (t - 4 * a1.val)) = t from by omega,
            show 8 * i5.val + (4 + (t - 4 * a1.val)) = t from by omega]
          exact bmod32_eq_self _ (by omega) (by omega)
      · rw [if_neg hin,
          show (acc2.val[t]!).val = (acc2.val[t]!).bv.toInt from rfl,
          hacc2v t (by scalar_tac), if_neg (by omega),
          hacc1v t (by scalar_tac), if_neg (by omega)]
        rfl
    apply WP.spec_mono (pointwise_inner_walk iv iter1 acc2 lhs rhs block B hiv hblock
      (by rw [hend']; exact hend)
      (by
        intro t ht h1 h2
        rw [hacc2all t ht, if_neg (by omega)]
        exact hB t ht (by omega) h2)
      hBlt)
    intro r hr t ht
    have hrt := hr t ht
    have hat := hacc2all t ht
    by_cases hin : 256 * block.val + 8 * iter.start.val ≤ t ∧ t < 256 * block.val + 256
    · rw [if_pos hin]
      by_cases hin1 : 256 * block.val + 8 * iter1.start.val ≤ t ∧ t < 256 * block.val + 256
      · rw [if_pos hin1] at hrt
        rw [hrt, hat, if_neg (by omega)]
      · rw [if_neg hin1] at hrt
        rw [hrt, hat, if_pos (by omega)]
    · rw [if_neg hin]
      rw [if_neg (by omega)] at hrt
      rw [hrt, hat, if_neg (by omega)]
  · let* ⟨ o, iter1, hnone, _ ⟩ ← core.iter.range.IteratorRange.next_Usize_none_spec
    rw [hnone]
    refine (WP.spec_ok _).mpr (fun t ht => ?_)
    rw [if_neg (by scalar_tac)]
termination_by 32 - iter.start.val
decreasing_by scalar_decr_tac

theorem pointwise_outer_walk (iter : core.ops.range.Range Usize) (acc : Array I32 512#usize)
    (lhs rhs : Array I16 512#usize) (B : ℤ) (hend : iter.«end».val = 2)
    (hB : ∀ t < 512, 256 * iter.start.val ≤ t →
      |(acc.val[t]!).val + (lhs.val[t]!).val * (rhs.val[t]!).val| ≤ B)
    (hBlt : B < 2147483648) :
    backend.neon.ntt.pointwise_mul_acc_loop0 iter acc lhs rhs
      ⦃ (r : Array I32 512#usize) => ∀ t < 512,
          if 256 * iter.start.val ≤ t then
            (r.val[t]!).val = (acc.val[t]!).val + (lhs.val[t]!).val * (rhs.val[t]!).val
          else (r.val[t]!).val = (acc.val[t]!).val ⦄ := by
  unfold backend.neon.ntt.pointwise_mul_acc_loop0
  by_cases hlt : iter.start.val < iter.«end».val
  · let* ⟨ o, iter1, ho, hstart', hend' ⟩ ← core.iter.range.IteratorRange.next_Usize_some_spec
    rw [ho]
    simp only
    have hb2 : iter.start.val < 2 := by omega
    have hvecs : backend.neon.ntt.VECS = ok 32#usize := by
      simp only [backend.neon.ntt.VECS, consts.RING_DEG]; rfl
    rw [hvecs, bind_tc_ok]
    apply WP.spec_bind (pointwise_inner_walk 32#usize ⟨0#usize, 32#usize⟩ acc lhs rhs iter.start
      B rfl hb2 rfl
      (by
        intro t ht h1 h2
        exact hB t ht (by scalar_tac))
      hBlt)
    intro acc1 hacc1
    have hacc1' : ∀ t < 512, (acc1.val[t]!).val =
        if 256 * iter.start.val ≤ t ∧ t < 256 * iter.start.val + 256 then
          (acc.val[t]!).val + (lhs.val[t]!).val * (rhs.val[t]!).val
        else (acc.val[t]!).val := by
      intro t ht
      have h := hacc1 t ht
      by_cases hin : 256 * iter.start.val ≤ t ∧ t < 256 * iter.start.val + 256
      · rw [if_pos (by scalar_tac)] at h
        rw [h, if_pos hin]
      · rw [if_neg (by scalar_tac)] at h
        rw [h, if_neg hin]
    apply WP.spec_mono (pointwise_outer_walk iter1 acc1 lhs rhs B (by rw [hend']; exact hend)
      (by
        intro t ht hge
        rw [hacc1' t ht, if_neg (by omega)]
        exact hB t ht (by omega))
      hBlt)
    intro r hr t ht
    have hrt := hr t ht
    by_cases hge : 256 * iter.start.val ≤ t
    · rw [if_pos hge]
      by_cases hge1 : 256 * iter1.start.val ≤ t
      · rw [if_pos hge1] at hrt
        rw [hrt, hacc1' t ht, if_neg (by omega)]
      · rw [if_neg hge1] at hrt
        rw [hrt, hacc1' t ht, if_pos (by omega)]
    · rw [if_neg hge]
      rw [if_neg (by omega)] at hrt
      rw [hrt, hacc1' t ht, if_neg (by omega)]
  · let* ⟨ o, iter1, hnone, _ ⟩ ← core.iter.range.IteratorRange.next_Usize_none_spec
    rw [hnone]
    refine (WP.spec_ok _).mpr (fun t ht => ?_)
    rw [if_neg (by scalar_tac)]
termination_by 2 - iter.start.val
decreasing_by scalar_decr_tac

/-- **The pointwise multiply-accumulate, as integers.**  Slot by slot, and exactly — the
accumulator never wraps under the bound the caller supplies. -/
theorem pointwise_acc_int (acc : Array I32 512#usize) (lhs rhs : Array I16 512#usize) (B : ℤ)
    (hB : ∀ t < 512, |(acc.val[t]!).val + (lhs.val[t]!).val * (rhs.val[t]!).val| ≤ B)
    (hBlt : B < 2147483648) :
    backend.neon.ntt.pointwise_mul_acc acc lhs rhs
      ⦃ (r : Array I32 512#usize) => ∀ t < 512,
          (r.val[t]!).val = (acc.val[t]!).val + (lhs.val[t]!).val * (rhs.val[t]!).val ⦄ := by
  unfold backend.neon.ntt.pointwise_mul_acc
  apply WP.spec_mono (pointwise_outer_walk ⟨0#usize, 2#usize⟩ acc lhs rhs B rfl
    (fun t ht _ => hB t ht) hBlt)
  intro r hr t ht
  have h := hr t ht
  rwa [if_pos (by scalar_tac)] at h

theorem setWidth16_toNat_eq (x : BitVec 32) :
    (((BitVec.setWidth 16 x).toNat : ℤ)) = x.toInt % 2 ^ 16 := by
  have h := x.isLt
  rw [BitVec.toNat_setWidth, BitVec.toInt_eq_toNat_bmod]
  push_cast
  simp only [Int.bmod]
  norm_num
  split <;> omega

/-! ## The CRT combine's lane algebra

Garner, one lane at a time.  Both residues arrive *centred*; the combine first lifts each into
`[0, q)` with a conditional add — `x + ((x >>ₛ 15) & q)`, which is `q` exactly when `x` is
negative — then forms `t = (a₂ − a₁)·q₁⁻¹ mod q₂`, lifts that too, and widens
`a₁ + t·q₁` into 32 bits.  A conditional subtract of `CRT_Q` centres the result. -/

theorem sshr15_bits (x : BitVec 16) :
    x.sshiftRight 15 = if x.msb then BitVec.allOnes 16 else 0#16 := by bv_decide

theorem msb_iff_neg (x : BitVec 16) : x.msb = true ↔ x.toInt < 0 := by
  rw [BitVec.toInt_eq_msb_cond]
  have h := x.isLt
  split <;> simp_all

/-- **The conditional add.**  `x + ((x >>ₛ 15) & q)` lands in `[0, q)` when `|x| < q`. -/
theorem cond_add_lane (x m c a q : Vec128) (Q : ℤ)
    (hm : bits m = Model.sshrNS16 15 (bits x))
    (hc : bits c = Model.andV (bits m) (bits q))
    (ha : bits a = Model.add16 (bits x) (bits c))
    (hq : ∀ i < 8, (lane16 q i).toInt = Q) (hQpos : 0 < Q) (hQlt : Q ≤ 2 ^ 14)
    (hx : ∀ i < 8, |(lane16 x i).toInt| ≤ Q) :
    ∀ i < 8, (lane16 a i).toInt
        = (lane16 x i).toInt + (if (lane16 x i).toInt < 0 then Q else 0) := by
  intro i hi
  have hml : lane16 m i = (lane16 x i).sshiftRight 15 := by
    show laneOf 16 (bits m) i = _
    rw [hm]
    simp only [Model.sshrNS16]
    exact laneOf_ofLanes16 _ hi
  have hcl : lane16 c i = lane16 m i &&& lane16 q i := by
    show laneOf 16 (bits c) i = _
    rw [hc]
    simp only [Model.andV]
    exact laneOf_and 16 _ _ i
  have hcv : (lane16 c i).toInt = if (lane16 x i).toInt < 0 then Q else 0 := by
    rw [hcl, hml, sshr15_bits]
    by_cases hmsb : (lane16 x i).msb
    · rw [if_pos hmsb, if_pos ((msb_iff_neg _).mp hmsb), BitVec.allOnes_and]
      exact hq i hi
    · rw [if_neg hmsb, if_neg (by simpa [msb_iff_neg] using hmsb), BitVec.zero_and]
      rfl
  have hxb := abs_le.mp (hx i hi)
  rw [add_lane_toInt x c a ha i hi, hcv]
  refine bmod16_eq_self ?_ ?_ <;> (split <;> omega)

/-- `sxtl.4s` lane `i`: exact sign extension of the low four `i16`s. -/
theorem sxtl_low_lane_toInt (a c : Vec128) (hc : bits c = Model.sxtlLowS16 (bits a)) :
    ∀ i < 4, (lane32 c i).toInt = (lane16 a i).toInt := by
  intro i hi
  have hl : lane32 c i = (lane16 a i).signExtend 32 := by
    show laneOf 32 (bits c) i = _
    rw [hc]
    simp only [Model.sxtlLowS16]
    exact laneOf_ofLanes32 _ hi
  have ha := toInt_bounds (lane16 a i)
  rw [hl, BitVec.toInt_signExtend, show (2 : ℕ) ^ min 32 16 = 2 ^ 16 from by norm_num,
    bmod16_eq_self (z := (lane16 a i).toInt) (by omega) (by omega)]

/-- `sxtl2.4s` lane `i`. -/
theorem sxtl_high_lane_toInt (a c : Vec128) (hc : bits c = Model.sxtlHighS16 (bits a)) :
    ∀ i < 4, (lane32 c i).toInt = (lane16 a (4 + i)).toInt := by
  intro i hi
  have hl : lane32 c i = (lane16 a (4 + i)).signExtend 32 := by
    show laneOf 32 (bits c) i = _
    rw [hc]
    simp only [Model.sxtlHighS16]
    exact laneOf_ofLanes32 _ hi
  have ha := toInt_bounds (lane16 a (4 + i))
  rw [hl, BitVec.toInt_signExtend, show (2 : ℕ) ^ min 32 16 = 2 ^ 16 from by norm_num,
    bmod16_eq_self (z := (lane16 a (4 + i)).toInt) (by omega) (by omega)]

private theorem bmod_congr {x y : ℤ} {n : ℕ} (h : x % (n : ℤ) = y % (n : ℤ)) : x.bmod n = y.bmod n := by
  simp only [Int.bmod, h]

private theorem bmod_emod' (y : ℤ) (n : ℕ) : (y.bmod n) % (n : ℤ) = y % (n : ℤ) := by
  simp only [Int.bmod]
  split
  · exact Int.emod_emod_of_dvd _ dvd_rfl
  · rw [Int.sub_emod_right, Int.emod_emod_of_dvd _ dvd_rfl]

private theorem bmod_add_bmod (a b : ℤ) (n : ℕ) : (a + b.bmod n).bmod n = (a + b).bmod n :=
  bmod_congr (by rw [Int.add_emod, bmod_emod' b n, ← Int.add_emod])

/-- `mla.4s` lane `i`, wrapping: the *first* operand is the accumulator. -/
theorem mla32_lane_toInt (a b c d : Vec128) (hd : bits d = Model.mla32 (bits a) (bits b) (bits c)) :
    ∀ i < 4, (lane32 d i).toInt
      = ((lane32 a i).toInt + (lane32 b i).toInt * (lane32 c i).toInt).bmod (2 ^ 32) := by
  intro i hi
  have hl : lane32 d i = lane32 a i + lane32 b i * lane32 c i := by
    show laneOf 32 (bits d) i = _
    rw [hd]
    simp only [Model.mla32]
    exact laneOf_ofLanes32 _ hi
  rw [hl, BitVec.toInt_add, BitVec.toInt_mul, bmod_add_bmod]

/-- `sub.4s` lane `i`, wrapping. -/
theorem sub32_lane_toInt (a b c : Vec128) (hc : bits c = Model.sub32 (bits a) (bits b)) :
    ∀ i < 4, (lane32 c i).toInt = ((lane32 a i).toInt - (lane32 b i).toInt).bmod (2 ^ 32) := by
  intro i hi
  have hl : lane32 c i = lane32 a i - lane32 b i := by
    show laneOf 32 (bits c) i = _
    rw [hc]
    simp only [Model.sub32]
    exact laneOf_ofLanes32 _ hi
  rw [hl, BitVec.toInt_sub]

/-- **The conditional subtract.**  `x − (CRT_Q & (x >ₛ CRT_Q_HALF))` centres a Garner value:
`CRT_Q` comes off exactly when `x` is above the half-way point. -/
theorem crt_sub_lane (x over v x1 cq ch : Vec128) (CQ CH : ℤ)
    (hover : bits over = Model.cmgtS32 (bits x) (bits ch))
    (hv : bits v = Model.andV (bits cq) (bits over))
    (hx1 : bits x1 = Model.sub32 (bits x) (bits v))
    (hcq : ∀ i < 4, (lane32 cq i).toInt = CQ) (hch : ∀ i < 4, (lane32 ch i).toInt = CH)
    (hCQ0 : 0 ≤ CQ) (hCQlt : CQ < 1073741824)
    (hx : ∀ i < 4, 0 ≤ (lane32 x i).toInt ∧ (lane32 x i).toInt < CQ) :
    ∀ i < 4, (lane32 x1 i).toInt
      = (lane32 x i).toInt - (if CH < (lane32 x i).toInt then CQ else 0) := by
  intro i hi
  have hoverl : lane32 over i =
      if BitVec.slt (lane32 ch i) (lane32 x i) then BitVec.allOnes 32 else 0#32 := by
    show laneOf 32 (bits over) i = _
    rw [hover]
    simp only [Model.cmgtS32]
    exact laneOf_ofLanes32 _ hi
  have hvl : lane32 v i = lane32 cq i &&& lane32 over i := by
    show laneOf 32 (bits v) i = _
    rw [hv]
    simp only [Model.andV]
    exact laneOf_and 32 _ _ i
  have hslt : BitVec.slt (lane32 ch i) (lane32 x i) = decide (CH < (lane32 x i).toInt) := by
    rw [BitVec.slt_eq_decide, hch i hi]
  have hvv : (lane32 v i).toInt = if CH < (lane32 x i).toInt then CQ else 0 := by
    rw [hvl, hoverl, hslt]
    by_cases hlt : CH < (lane32 x i).toInt
    · rw [decide_eq_true hlt, if_pos rfl, if_pos hlt, BitVec.and_allOnes]
      exact hcq i hi
    · rw [decide_eq_false hlt, if_neg (by simp), if_neg hlt, BitVec.and_zero]
      rfl
  have hxb := hx i hi
  rw [sub32_lane_toInt x v x1 hx1 i hi, hvv]
  refine bmod32_eq_self _ ?_ ?_ <;> (split <;> omega)

/-! ## The conditional subtract, over the two wide halves

The same `IterMut` framing as the NTT's re-centring passes, over a two-element slice this time,
and with a 32-bit lane conclusion. -/

theorem crt_sub_iter (iter : core.slice.iter.IterMut Vec128)
    (back : core.slice.iter.IterMut Vec128 → core.slice.iter.IterMut Vec128)
    (cq ch : Vec128) (CQ CH : ℤ) (val0 : ℕ → ℕ → ℤ)
    (hcq : ∀ i < 4, (lane32 cq i).toInt = CQ) (hch : ∀ i < 4, (lane32 ch i).toInt = CH)
    (hCQ0 : 0 ≤ CQ) (hCQlt : CQ < 1073741824)
    (hval0b : ∀ j < 2, ∀ m < 4, 0 ≤ val0 j m ∧ val0 j m < CQ)
    (h_len : iter.slice.val.length = 2) (h_iter_i : iter.i ≤ 2)
    (hval0 : ∀ (j : ℕ) (hj : j < iter.slice.val.length), ∀ m < 4,
      (lane32 (sAt iter.slice j hj) m).toInt = val0 j m)
    (hback_len : ∀ (im : core.slice.iter.IterMut Vec128),
      im.slice.val.length = 2 → (back im).slice.val.length = 2)
    (hback_writes : ∀ (im : core.slice.iter.IterMut Vec128)
      (_him : im.slice.val.length = 2) (j : ℕ) (_hj : j < iter.i)
      (hb : j < (back im).slice.val.length) (m : ℕ) (_hm : m < 4),
        (lane32 (sAt (back im).slice j hb) m).toInt
          = val0 j m - (if CH < val0 j m then CQ else 0))
    (hback_rest : ∀ (im : core.slice.iter.IterMut Vec128)
      (_him : im.slice.val.length = 2) (j : ℕ) (_hge : iter.i ≤ j)
      (hb : j < (back im).slice.val.length) (hb' : j < im.slice.val.length),
        sAt (back im).slice j hb = sAt im.slice j hb') :
    backend.neon.ntt.reduce_invntt_loop0_loop0 iter back cq ch
      ⦃ (r : core.slice.iter.IterMut Vec128 ×
             (core.slice.iter.IterMut Vec128 → core.slice.iter.IterMut Vec128)) =>
          r.1.slice.val.length = 2 ∧
          ∀ (im : core.slice.iter.IterMut Vec128), im.slice.val.length = 2 →
            (r.2 im).slice.val.length = 2 ∧
            ∀ (j : ℕ) (hj : j < (r.2 im).slice.val.length) (m : ℕ), m < 4 →
              (lane32 (sAt (r.2 im).slice j hj) m).toInt
                = val0 j m - (if CH < val0 j m then CQ else 0) ⦄ := by
  unfold backend.neon.ntt.reduce_invntt_loop0_loop0
  by_cases hlt : iter.i < iter.slice.len
  · let* ⟨ o, iter1, next_back, h_all ⟩ ← CbdGeneric.iter_mut_next_spec
    obtain ⟨ho, hit2_slice, hit2_i, hnb_none, hnb_some⟩ := h_all
    rw [ho]
    simp only []
    have hii : iter.i < 2 := by
      have h := hlt
      rw [← h_len]
      simpa [Slice.len, Slice.length] using h
    have hivl : iter.i < iter.slice.val.length := by omega
    obtain ⟨over0, hover0, hover0b⟩ := cmgt_s32_model (sAt iter.slice iter.i hivl) ch
    apply WP.spec_bind (show cmgt_s32 (sAt iter.slice iter.i hivl) ch
        ⦃ (o' : Vec128) =>
            bits o' = Model.cmgtS32 (bits (sAt iter.slice iter.i hivl)) (bits ch) ⦄
      from by rw [hover0]; exact (WP.spec_ok _).mpr hover0b)
    intro over hoverb
    obtain ⟨v0, hv0, hv0b⟩ := and_model cq over
    apply WP.spec_bind (show backend.neon.intrinsics.and cq over
        ⦃ (v' : Vec128) => bits v' = Model.andV (bits cq) (bits over) ⦄
      from by rw [hv0]; exact (WP.spec_ok _).mpr hv0b)
    intro v hvb
    obtain ⟨x10, hx10, hx10b⟩ := sub_32_model (sAt iter.slice iter.i hivl) v
    apply WP.spec_bind (show sub_32 (sAt iter.slice iter.i hivl) v
        ⦃ (x' : Vec128) => bits x' = Model.sub32 (bits (sAt iter.slice iter.i hivl)) (bits v) ⦄
      from by rw [hx10]; exact (WP.spec_ok _).mpr hx10b)
    intro x1 hx1b
    have hslot : ∀ m < 4, (lane32 x1 m).toInt
        = val0 iter.i m - (if CH < val0 iter.i m then CQ else 0) := by
      intro m hm
      have h := crt_sub_lane (sAt iter.slice iter.i hivl) over v x1 cq ch CQ CH hoverb hvb hx1b
        hcq hch hCQ0 hCQlt (fun k hk => by rw [hval0 iter.i hivl k hk]; exact hval0b iter.i (by omega) k hk)
        m hm
      rw [h, hval0 iter.i hivl m hm]
    have hnbs : ∀ im : core.slice.iter.IterMut Vec128,
        (next_back im (some x1)).slice = im.slice.setAtNat iter.i x1 := by
      intro im
      rw [hnb_some im x1]
    have hlen' : ∀ (im : core.slice.iter.IterMut Vec128), im.slice.val.length = 2 →
        (next_back im (some x1)).slice.val.length = 2 := by
      intro im him
      rw [hnbs im]
      simpa [Slice.setAtNat] using him
    apply WP.spec_mono (crt_sub_iter iter1 (fun im => back (next_back im (some x1))) cq ch CQ CH
      val0 hcq hch hCQ0 hCQlt hval0b (by rw [hit2_slice]; exact h_len) (by omega)
      (by
        intro j hj m hm
        simp only [hit2_slice] at hj ⊢
        exact hval0 j hj m hm)
      (fun im him => hback_len _ (hlen' im him))
      (by
        intro im him j hj hb m hm
        by_cases hje : j = iter.i
        · have hbm : j < (next_back im (some x1)).slice.val.length := by
            rw [hlen' im him]; omega
          rw [hback_rest (next_back im (some x1)) (hlen' im him) j (by omega) hb hbm]
          have hset : ∀ (h1 : j < (im.slice.setAtNat iter.i x1).val.length),
              sAt (next_back im (some x1)).slice j hbm
                = sAt (im.slice.setAtNat iter.i x1) j h1 := by
            intro h1
            simp only [hnbs im]
          rw [hset (by rw [← hnbs im]; exact hbm),
            sAt_setAtNat im.slice iter.i x1 j _ (by omega), if_pos hje, hje]
          exact hslot m hm
        · exact hback_writes (next_back im (some x1)) (hlen' im him) j (by omega) hb m hm)
      (by
        intro im him j hge hb hb'
        have hbm : j < (next_back im (some x1)).slice.val.length := by
          rw [hlen' im him]; omega
        rw [hback_rest (next_back im (some x1)) (hlen' im him) j (by omega) hb hbm]
        have hset : ∀ (h1 : j < (im.slice.setAtNat iter.i x1).val.length),
            sAt (next_back im (some x1)).slice j hbm
              = sAt (im.slice.setAtNat iter.i x1) j h1 := by
          intro h1
          simp only [hnbs im]
        rw [hset (by rw [← hnbs im]; exact hbm),
          sAt_setAtNat im.slice iter.i x1 j _ hb', if_neg (by omega)]))
    rintro ⟨r1, r2⟩ hr
    exact hr
  · let* ⟨ o, iter1, next_back, h_all ⟩ ← CbdGeneric.iter_mut_next_spec_none
    obtain ⟨ho, hit_eq, hnb⟩ := h_all
    rw [ho]
    have hi2 : iter.i = 2 := by
      have hnot : ¬ (iter.i < 2) := by
        have h := hlt
        rw [← h_len]
        simpa [Slice.len, Slice.length] using h
      omega
    refine (WP.spec_ok _).mpr ⟨by rw [hit_eq]; exact h_len, fun im him => ?_⟩
    simp only [hnb]
    exact ⟨hback_len im him, fun j hj m hm =>
      hback_writes im him j (by rw [hback_len im him] at hj; omega) hj m hm⟩

/-! ## `reduce_invntt`'s loop

One vector per iteration: canonicalise both residues, solve Garner's congruence with a Montgomery
multiply by `CRT_Q1_INV_MONT`, canonicalise that too, widen `a₁ + t·q₁` into two 32-bit halves,
centre them, and narrow back to `u16`.  `Kopis/Crt/Scheme.lean`'s `garner_value` and `garner_mult`
carry the arithmetic; everything here is the lane bookkeeping. -/

open Kopis.CrtScheme in
theorem reduce_invntt_loop_walk (iter : core.ops.range.Range Usize)
    (v1 v2 : Array I16 256#usize) (q1v q2v qim qimq q1w crtq crtqh : Vec128)
    (out : Array U16 256#usize) (X : ℕ → ℤ)
    (hq1 : ∀ j < 8, (lane16 q1v j).toInt = 7681)
    (hq2 : ∀ j < 8, (lane16 q2v j).toInt = 10753)
    (hqim : ∀ j < 8, (lane16 qim j).toInt = 3563)
    (hqimq : ∀ j < 8, (2 ^ 16 : ℤ) ∣ ((lane16 qimq j).toInt * 10753 - (lane16 qim j).toInt))
    (hq1w : ∀ j < 4, (lane32 q1w j).toInt = 7681)
    (hcq : ∀ j < 4, (lane32 crtq j).toInt = 82593793)
    (hcqh : ∀ j < 4, (lane32 crtqh j).toInt = 41296896)
    (hr1b : ∀ c < 256, |(v1.val[c]!).val| < 7681)
    (hr2b : ∀ c < 256, |(v2.val[c]!).val| < 10753)
    (hX1 : ∀ c < 256, (X c) ≡ (v1.val[c]!).val [ZMOD 7681])
    (hX2 : ∀ c < 256, (X c) ≡ (v2.val[c]!).val [ZMOD 10753])
    (hXb : ∀ c < 256, 2 * |X c| < 82593793)
    (hend : iter.«end».val = 32)
    (hpre : ∀ c < 256, c < 8 * iter.start.val → ((out.val[c]!).val : ℤ) = X c % 2 ^ 16) :
    backend.neon.ntt.reduce_invntt_loop0 iter v1 v2 q1v q2v qim qimq q1w crtq crtqh out
      ⦃ (r : Array U16 256#usize) => ∀ c < 256, ((r.val[c]!).val : ℤ) = X c % 2 ^ 16 ⦄ := by
  unfold backend.neon.ntt.reduce_invntt_loop0
  by_cases hlt : iter.start.val < iter.«end».val
  · let* ⟨ o, iter1, ho, hstart', hend' ⟩ ← core.iter.range.IteratorRange.next_Usize_some_spec
    rw [ho]
    simp only
    have hi32 : iter.start.val < 32 := by omega
    obtain ⟨r1, hr1, hr1v⟩ := load_i16_val v1 iter.start (by omega)
    rw [hr1, bind_tc_ok]
    obtain ⟨r2, hr2, hr2v⟩ := load_i16_val v2 iter.start (by omega)
    rw [hr2, bind_tc_ok]
    have hr1bnd : ∀ k < 8, |(lane16 r1 k).toInt| < 7681 := by
      intro k hk; rw [hr1v k hk]; exact hr1b _ (by omega)
    have hr2bnd : ∀ k < 8, |(lane16 r2 k).toInt| < 10753 := by
      intro k hk; rw [hr2v k hk]; exact hr2b _ (by omega)
    -- canonicalise the first residue
    obtain ⟨m1, hm1, hm1b⟩ := sshr_n_s16_model 15#i32 r1 (by decide) (by decide)
    rw [hm1, bind_tc_ok]
    obtain ⟨n1, hn1, hn1b⟩ := and_model m1 q1v
    rw [hn1, bind_tc_ok]
    obtain ⟨a1, ha1, ha1b⟩ := add_16_model r1 n1
    rw [ha1, bind_tc_ok]
    have himm : (15#i32 : Std.I32).val.toNat = 15 := by scalar_tac
    have ha1v : ∀ k < 8, (lane16 a1 k).toInt
        = (lane16 r1 k).toInt + (if (lane16 r1 k).toInt < 0 then 7681 else 0) :=
      cond_add_lane r1 m1 n1 a1 q1v 7681 (by rw [hm1b, himm]) hn1b ha1b hq1 (by norm_num)
        (by norm_num) (fun k hk => le_of_lt (hr1bnd k hk))
    -- and the second
    obtain ⟨m2, hm2, hm2b⟩ := sshr_n_s16_model 15#i32 r2 (by decide) (by decide)
    rw [hm2, bind_tc_ok]
    obtain ⟨n2, hn2, hn2b⟩ := and_model m2 q2v
    rw [hn2, bind_tc_ok]
    obtain ⟨a2, ha2, ha2b⟩ := add_16_model r2 n2
    rw [ha2, bind_tc_ok]
    have ha2v : ∀ k < 8, (lane16 a2 k).toInt
        = (lane16 r2 k).toInt + (if (lane16 r2 k).toInt < 0 then 10753 else 0) :=
      cond_add_lane r2 m2 n2 a2 q2v 10753 (by rw [hm2b, himm]) hn2b ha2b hq2 (by norm_num)
        (by norm_num) (fun k hk => le_of_lt (hr2bnd k hk))
    -- the difference, then Garner's `t`
    obtain ⟨d, hd, hdb⟩ := sub_16_model a2 a1
    rw [hd, bind_tc_ok]
    have ha1r : ∀ k < 8, 0 ≤ (lane16 a1 k).toInt ∧ (lane16 a1 k).toInt < 7681 := by
      intro k hk
      have h := abs_lt.mp (hr1bnd k hk)
      rw [ha1v k hk]
      split <;> omega
    have ha2r : ∀ k < 8, 0 ≤ (lane16 a2 k).toInt ∧ (lane16 a2 k).toInt < 10753 := by
      intro k hk
      have h := abs_lt.mp (hr2bnd k hk)
      rw [ha2v k hk]
      split <;> omega
    have hdv : ∀ k < 8, (lane16 d k).toInt = (lane16 a2 k).toInt - (lane16 a1 k).toInt := by
      intro k hk
      have h1 := ha1r k hk
      have h2 := ha2r k hk
      rw [sub_lane_toInt a2 a1 d hdb k hk]
      exact bmod16_eq_self (by omega) (by omega)
    apply WP.spec_bind (mont_mul_lane_spec d qim qimq q2v 10753 hq2 (by norm_num) (by norm_num)
      (fun k hk => by rw [hqim k hk]; norm_num) hqimq
      (fun k hk => by
        have h1 := ha1r k hk
        have h2 := ha2r k hk
        rw [hdv k hk, hqim k hk, abs_mul, abs_of_nonneg (by norm_num : (0:ℤ) ≤ 3563)]
        have : |(lane16 a2 k).toInt - (lane16 a1 k).toInt| ≤ 18434 := by
          rw [abs_le]; omega
        nlinarith))
    intro t ht
    -- canonicalise `t`
    obtain ⟨m3, hm3, hm3b⟩ := sshr_n_s16_model 15#i32 t (by decide) (by decide)
    rw [hm3, bind_tc_ok]
    obtain ⟨n3, hn3, hn3b⟩ := and_model m3 q2v
    rw [hn3, bind_tc_ok]
    obtain ⟨t1, ht1, ht1b⟩ := add_16_model t n3
    rw [ht1, bind_tc_ok]
    have ht1v : ∀ k < 8, (lane16 t1 k).toInt
        = (lane16 t k).toInt + (if (lane16 t k).toInt < 0 then 10753 else 0) :=
      cond_add_lane t m3 n3 t1 q2v 10753 (by rw [hm3b, himm]) hn3b ht1b hq2 (by norm_num)
        (by norm_num) (fun k hk => by have := ht k hk; rw [abs_le]; omega)
    have ht1r : ∀ k < 8, 0 ≤ (lane16 t1 k).toInt ∧ (lane16 t1 k).toInt < 10753 := by
      intro k hk
      have h := ht k hk
      rw [ht1v k hk]
      split <;> omega
    -- the Garner value each lane should carry
    have hgar : ∀ k < 8, (if 41296896 < (lane16 a1 k).toInt + 7681 * (lane16 t1 k).toInt then
          (lane16 a1 k).toInt + 7681 * (lane16 t1 k).toInt - 82593793
        else (lane16 a1 k).toInt + 7681 * (lane16 t1 k).toInt) = X (8 * iter.start.val + k) := by
      intro k hk
      have hc : 8 * iter.start.val + k < 256 := by omega
      have hmm : (10753 : ℤ) ∣ ((lane16 t1 k).toInt * 2 ^ 16
          - ((lane16 a2 k).toInt - (lane16 a1 k).toInt) * 3563) := by
        obtain ⟨e, he⟩ := (ht k hk).1
        rw [hqim k hk, hdv k hk] at he
        rw [ht1v k hk]
        by_cases hneg : (lane16 t k).toInt < 0
        · exact ⟨e + 2 ^ 16, by rw [if_pos hneg]; linarith [he]⟩
        · exact ⟨e, by rw [if_neg hneg]; linarith [he]⟩
      refine garner_value (x := X (8 * iter.start.val + k))
        (r1 := (lane16 r1 k).toInt) (r2 := (lane16 r2 k).toInt)
        (a1 := (lane16 a1 k).toInt) (a2 := (lane16 a2 k).toInt)
        (t := (lane16 t1 k).toInt)
        (by simp only [Kopis.CrtScheme.q1]; rw [hr1v k hk]; exact hX1 _ hc)
        (by simp only [Kopis.CrtScheme.q2]; rw [hr2v k hk]; exact hX2 _ hc)
        (by simp only [Kopis.CrtScheme.q1]; rw [ha1v k hk]
            split <;> (unfold Int.ModEq; omega))
        (by simp only [Kopis.CrtScheme.q1]; exact ha1r k hk)
        (by simp only [Kopis.CrtScheme.q2]; rw [ha2v k hk]
            split <;> (unfold Int.ModEq; omega))
        (by simp only [Kopis.CrtScheme.q2]; exact ha2r k hk)
        (by simp only [Kopis.CrtScheme.q1, Kopis.CrtScheme.q2]; exact garner_mult hmm)
        (by simp only [Kopis.CrtScheme.q2]; exact ht1r k hk) (hXb _ hc)
    -- widen into two 32-bit halves and form `a₁ + t₁·q₁`
    obtain ⟨w9, hw9, hw9b⟩ := sxtl_low_s16_model a1
    rw [hw9, bind_tc_ok]
    obtain ⟨w10, hw10, hw10b⟩ := sxtl_low_s16_model t1
    rw [hw10, bind_tc_ok]
    obtain ⟨w11, hw11, hw11b⟩ := mla_32_model w9 w10 q1w
    rw [hw11, bind_tc_ok]
    obtain ⟨w12, hw12, hw12b⟩ := sxtl_high_s16_model a1
    rw [hw12, bind_tc_ok]
    obtain ⟨w13, hw13, hw13b⟩ := sxtl_high_s16_model t1
    rw [hw13, bind_tc_ok]
    obtain ⟨w14, hw14, hw14b⟩ := mla_32_model w12 w13 q1w
    rw [hw14, bind_tc_ok]
    set W : ℕ → ℕ → ℤ := fun j m =>
      (lane16 a1 (4 * j + m)).toInt + 7681 * (lane16 t1 (4 * j + m)).toInt with hW
    have hWr : ∀ j < 2, ∀ m < 4, 0 ≤ W j m ∧ W j m < 82593793 := by
      intro j hj m hm
      have h1 := ha1r (4 * j + m) (by omega)
      have h2 := ht1r (4 * j + m) (by omega)
      rw [hW]
      constructor <;> nlinarith
    have hw11v : ∀ m < 4, (lane32 w11 m).toInt = W 0 m := by
      intro m hm
      have h1 := ha1r m (by omega)
      have h2 := ht1r m (by omega)
      rw [mla32_lane_toInt w9 w10 q1w w11 hw11b m hm, sxtl_low_lane_toInt a1 w9 hw9b m hm,
        sxtl_low_lane_toInt t1 w10 hw10b m hm, hq1w m hm, hW]
      have he : (lane16 a1 m).toInt + (lane16 t1 m).toInt * 7681
          = (lane16 a1 (4 * 0 + m)).toInt + 7681 * (lane16 t1 (4 * 0 + m)).toInt := by
        simp only [Nat.mul_zero, Nat.zero_add]; ring
      rw [he]
      have := hWr 0 (by omega) m hm
      rw [hW] at this
      exact bmod32_eq_self _ (by omega) (by omega)
    have hw14v : ∀ m < 4, (lane32 w14 m).toInt = W 1 m := by
      intro m hm
      have h1 := ha1r (4 + m) (by omega)
      have h2 := ht1r (4 + m) (by omega)
      rw [mla32_lane_toInt w12 w13 q1w w14 hw14b m hm, sxtl_high_lane_toInt a1 w12 hw12b m hm,
        sxtl_high_lane_toInt t1 w13 hw13b m hm, hq1w m hm, hW]
      have he : (lane16 a1 (4 + m)).toInt + (lane16 t1 (4 + m)).toInt * 7681
          = (lane16 a1 (4 * 1 + m)).toInt + 7681 * (lane16 t1 (4 * 1 + m)).toInt := by
        simp only [Nat.mul_one]; ring
      rw [he]
      have := hWr 1 (by omega) m hm
      rw [hW] at this
      exact bmod32_eq_self _ (by omega) (by omega)
    -- the slice round trip and the conditional subtract
    let* ⟨ sl, to_back, hs_val, hto_back ⟩ ← Array.to_slice_mut_spec
    let* ⟨ iter2, imb, hi2_slice, hi2_zero, hi2_back ⟩ ← iter_mut_spec
    have hs_len : sl.val.length = 2 := by rw [hs_val]; rfl
    have hi2_len : iter2.slice.val.length = 2 := by rw [hi2_slice]; exact hs_len
    have hi2Z : ∀ (j : ℕ) (hj : j < iter2.slice.val.length), ∀ m < 4,
        (lane32 (sAt iter2.slice j hj) m).toInt = W j m := by
      intro j hj m hm
      have hj2 : j < 2 := by omega
      have heq : sAt iter2.slice j hj = if j = 0 then w11 else w14 := by
        unfold sAt
        have : iter2.slice.val = [w11, w14] := by rw [hi2_slice, hs_val]; rfl
        rcases (show j = 0 ∨ j = 1 from by omega) with rfl | rfl
        · rw [if_pos rfl]; exact List.getElem_of_eq this _
        · rw [if_neg (by omega)]; exact List.getElem_of_eq this _
      rw [heq]
      rcases (show j = 0 ∨ j = 1 from by omega) with rfl | rfl
      · rw [if_pos rfl]; exact hw11v m hm
      · rw [if_neg (by omega)]; exact hw14v m hm
    apply WP.spec_bind (crt_sub_iter iter2 (fun im1 => im1) crtq crtqh 82593793 41296896 W
      hcq hcqh (by norm_num) (by norm_num) hWr hi2_len (by rw [hi2_zero]; omega) hi2Z
      (fun im him => him)
      (fun im him j hj hbnd m hm => absurd hj (by rw [hi2_zero]; omega))
      (fun im him j _ hbnd hbnd' => rfl))
    rintro ⟨im, bk⟩ ⟨him_len, hbk⟩
    obtain ⟨hbk_len, hbkv⟩ := hbk im him_len
    show (do let v15 ← (to_back (imb (bk im))).index_usize 0#usize
             let v16 ← (to_back (imb (bk im))).index_usize 1#usize
             let v17 ← xtn_pair_32 v15 v16
             let out1 ← store_u16 out iter.start v17
             backend.neon.ntt.reduce_invntt_loop0 iter1 v1 v2 q1v q2v qim qimq q1w crtq crtqh
               out1)
        ⦃ (r : Array U16 256#usize) => ∀ c < 256, ((r.val[c]!).val : ℤ) = X c % 2 ^ 16 ⦄
    set wide := to_back (imb (bk im)) with hwide
    have hwide_val : wide.val = (bk im).slice.val := by
      rw [hwide, hi2_back, hto_back]
      exact Std.Array.from_slice_val _ _ (by rw [hbk_len]; simp)
    have hwl : wide.val.length = 2 := by rw [hwide_val]; exact hbk_len
    obtain ⟨v15, hv15, hv15v⟩ := WP.spec_imp_exists
      (Array.index_usize_spec wide 0#usize (by simp [Array.length]))
    rw [hv15, bind_tc_ok]
    obtain ⟨v16, hv16, hv16v⟩ := WP.spec_imp_exists
      (Array.index_usize_spec wide 1#usize (by simp [Array.length]))
    rw [hv16, bind_tc_ok]
    have hlane : ∀ j < 2, ∀ m < 4,
        (lane32 (if j = 0 then v15 else v16) m).toInt
          = W j m - (if 41296896 < W j m then 82593793 else 0) := by
      intro j hj m hm
      have hjb : j < (bk im).slice.val.length := by rw [hbk_len]; omega
      have heq : (if j = 0 then v15 else v16) = sAt (bk im).slice j hjb := by
        unfold sAt
        rcases (show j = 0 ∨ j = 1 from by omega) with rfl | rfl
        · rw [if_pos rfl, hv15v]
          exact List.getElem_of_eq hwide_val _
        · rw [if_neg (by omega), hv16v]
          exact List.getElem_of_eq hwide_val _
      rw [heq]
      exact hbkv j hjb m hm
    obtain ⟨v17, hv17, hv17b⟩ := xtn_pair_32_model v15 v16
    rw [hv17, bind_tc_ok]
    obtain ⟨out1, hout1, hout1v⟩ := store_u16_spec out iter.start v17 (by scalar_tac)
    rw [hout1, bind_tc_ok]
    -- what one iteration writes
    have hwrite : ∀ k < 8, ((out1.val[8 * iter.start.val + k]!).val : ℤ)
        = X (8 * iter.start.val + k) % 2 ^ 16 := by
      intro k hk
      have hb : (out1.val[8 * iter.start.val + k]!).bv = lane16 v17 k := by
        rw [hout1v _ (by scalar_tac), if_pos (by omega),
          show 8 * iter.start.val + k - 8 * iter.start.val = k from by omega]
      rw [show ((out1.val[8 * iter.start.val + k]!).val : ℤ)
          = (((out1.val[8 * iter.start.val + k]!).bv.toNat : ℕ) : ℤ) from rfl, hb,
        xtn_pair_lane v15 v16 v17 hv17b k hk]
      by_cases h4 : k < 4
      · rw [if_pos h4, setWidth16_toNat_eq]
        have h := hlane 0 (by omega) k h4
        rw [if_pos rfl] at h
        rw [h, ← hgar k hk, hW]
        simp only [Nat.mul_zero, Nat.zero_add]
        split <;> simp
      · rw [if_neg h4, setWidth16_toNat_eq]
        have h := hlane 1 (by omega) (k - 4) (by omega)
        rw [if_neg (by omega)] at h
        rw [h, ← hgar k hk, hW]
        simp only [Nat.mul_one]
        rw [show 4 + (k - 4) = k from by omega]
        split <;> simp
    exact reduce_invntt_loop_walk iter1 v1 v2 q1v q2v qim qimq q1w crtq crtqh out1 X
      hq1 hq2 hqim hqimq hq1w hcq hcqh hr1b hr2b hX1 hX2 hXb (by rw [hend']; exact hend)
      (by
        intro c hc hlow
        by_cases hold : c < 8 * iter.start.val
        · rw [show ((out1.val[c]!).val : ℤ) = (((out1.val[c]!).bv.toNat : ℕ) : ℤ) from rfl,
            hout1v c (by scalar_tac), if_neg (by omega)]
          exact hpre c hc hold
        · have hk : c - 8 * iter.start.val < 8 := by omega
          have := hwrite (c - 8 * iter.start.val) hk
          rwa [show 8 * iter.start.val + (c - 8 * iter.start.val) = c from by omega] at this)
  · let* ⟨ o, iter1, hnone, _ ⟩ ← core.iter.range.IteratorRange.next_Usize_none_spec
    rw [hnone]
    refine (WP.spec_ok _).mpr (fun c hc => ?_)
    exact hpre c hc (by scalar_tac)
termination_by 32 - iter.start.val
decreasing_by scalar_decr_tac

/-! ## `reduce_invntt`

Two `reduce_block` calls, the eight broadcast constants, and the Garner loop. -/

unseal backend.crt.CRT_Q backend.crt.CRT_Q_HALF backend.crt.CRT_Q1_INV_MONT
  backend.crt.Q1 backend.crt.Q2 backend.crt.Q2_INV in
theorem crt_consts :
    backend.crt.CRT_Q.val = 82593793 ∧ backend.crt.CRT_Q_HALF.val = 41296896 ∧
    backend.crt.CRT_Q1_INV_MONT.val = 3563 ∧
    (2 ^ 16 : ℤ) ∣ (backend.crt.Q2_INV.val * 10753 - 1) := by
  refine ⟨by decide, by decide, by decide, by decide⟩

unseal backend.crt.Q1 in
theorem q1_cast_val : (IScalar.cast .I32 backend.crt.Q1).val = 7681 := by decide

private theorem usize_two_mul_32 : (2#usize : Usize) * 32#usize = ok 64#usize := by
  obtain ⟨v, hv, hvv⟩ := WP.spec_imp_exists
    (Std.Usize.mul_spec (x := 2#usize) (y := 32#usize) (by scalar_tac))
  rw [hv]
  congr 1
  exact UScalar.eq_of_val_eq (by scalar_tac)

open Kopis.CrtScheme in
theorem reduce_invntt_walk (acc : Array I32 512#usize) (X : ℕ → ℤ)
    (hXb : ∀ c < 256, 2 * |X c| < 82593793)
    (hacc1 : ∀ t < 256, |(acc.val[4 * (0#usize : Usize).val + t]!).val| ≤ 58982400)
    (hacc2 : ∀ t < 256, |(acc.val[4 * (64#usize : Usize).val + t]!).val| ≤ 115605504)
    (a01 : ℕ → ZMod 7681)
    (ha01 : ∀ c < 256, a01 c
      = (900 : ZMod 7681) * accZ32 7681 acc (4 * (0#usize : Usize).val + c))
    (a02 : ℕ → ZMod 10753)
    (ha02 : ∀ c < 256, a02 c
      = (1764 : ZMod 10753) * accZ32 10753 acc (4 * (64#usize : Usize).val + c))
    (hres1 : ∀ c < 256, ((X c : ℤ) : ZMod 7681)
      = (((backend.crt.INVNTT_SCALE_1.val : ℤ) : ZMod 7681) * (900 : ZMod 7681))
          * invAllRaw 7681 zeta1 a01 c)
    (hres2 : ∀ c < 256, ((X c : ℤ) : ZMod 10753)
      = (((backend.crt.INVNTT_SCALE_2.val : ℤ) : ZMod 10753) * (1764 : ZMod 10753))
          * invAllRaw 10753 zeta2 a02 c) :
    backend.neon.ntt.reduce_invntt acc
      ⦃ (r : Array U16 256#usize) => ∀ c < 256, ((r.val[c]!).val : ℤ) = X c % 2 ^ 16 ⦄ := by
  obtain ⟨hcqv, hcqhv, hqimv, hq2inv⟩ := crt_consts
  unfold backend.neon.ntt.reduce_invntt
  apply WP.spec_bind (reduce_block_val_q1 acc 0#usize _ a01 (by scalar_tac) hacc1 ha01)
  rintro v11 ⟨hb1, hv1⟩
  have hvecs : backend.neon.ntt.VECS = ok 32#usize := by
    simp only [backend.neon.ntt.VECS, consts.RING_DEG]; rfl
  rw [hvecs, bind_tc_ok,
    usize_two_mul_32, bind_tc_ok]
  apply WP.spec_bind (reduce_block_val_q2 acc 64#usize _ a02 (by scalar_tac) hacc2 ha02)
  rintro v21 ⟨hb2, hv2⟩
  obtain ⟨q1v, hq1v, hq1vl⟩ := dup_n_s16_spec backend.crt.Q1
  rw [hq1v, bind_tc_ok]
  obtain ⟨q2v, hq2v, hq2vl⟩ := dup_n_s16_spec backend.crt.Q2
  rw [hq2v, bind_tc_ok]
  obtain ⟨qim, hqimE, hqiml⟩ := dup_n_s16_spec backend.crt.CRT_Q1_INV_MONT
  rw [hqimE, bind_tc_ok]
  simp only [lift, bind_tc_ok]
  obtain ⟨qimq, hqimqE, hqimql⟩ := dup_n_s16_spec
    (core.num.I16.wrapping_mul backend.crt.CRT_Q1_INV_MONT backend.crt.Q2_INV)
  rw [hqimqE, bind_tc_ok]
  obtain ⟨q1w, hq1wE, hq1wl⟩ := dup_n_s32_spec (IScalar.cast .I32 backend.crt.Q1)
  rw [hq1wE, bind_tc_ok]
  obtain ⟨crtq, hcrtqE, hcrtql⟩ := dup_n_s32_spec backend.crt.CRT_Q
  rw [hcrtqE, bind_tc_ok]
  obtain ⟨crtqh, hcrtqhE, hcrtqhl⟩ := dup_n_s32_spec backend.crt.CRT_Q_HALF
  rw [hcrtqhE, bind_tc_ok]
  apply reduce_invntt_loop_walk ⟨0#usize, 32#usize⟩ v11 v21 q1v q2v qim qimq q1w crtq crtqh
    _ X
    (fun j hj => by rw [hq1vl j hj]; exact q1_val)
    (fun j hj => by rw [hq2vl j hj]; exact q2_val)
    (fun j hj => by rw [hqiml j hj]; exact hqimv)
    (fun j hj => by
      rw [hqiml j hj, hqimql j hj]
      have h1 : ((core.num.I16.wrapping_mul backend.crt.CRT_Q1_INV_MONT
          backend.crt.Q2_INV).bv).toInt
          = tblZq backend.crt.CRT_Q1_INV_MONT.val backend.crt.Q2_INV.val := by
        show ((backend.crt.CRT_Q1_INV_MONT.bv * backend.crt.Q2_INV.bv : BitVec 16)).toInt = _
        rw [BitVec.toInt_mul]
        rfl
      rw [h1]
      exact tblZq_mont _ _ _ hq2inv)
    (fun j hj => by rw [hq1wl j hj]; exact q1_cast_val)
    (fun j hj => by rw [hcrtql j hj]; exact hcqv)
    (fun j hj => by rw [hcrtqhl j hj]; exact hcqhv)
    (fun c hc => by have h := abs_le.mp (hb1 c hc); rw [abs_lt]; omega)
    (fun c hc => by have h := abs_le.mp (hb2 c hc); rw [abs_lt]; omega)
    (fun c hc => (ZMod.intCast_eq_intCast_iff _ _ _).mp
      (by rw [hres1 c hc, ← hv1 c hc]; rfl))
    (fun c hc => (ZMod.intCast_eq_intCast_iff _ _ _).mp
      (by rw [hres2 c hc, ← hv2 c hc]; rfl))
    hXb rfl
    (by intro c hc hlow; exact absurd hlow (by scalar_tac))

/-! ## The accumulator is a leaf state

The last structural step before the entry point: `N` pointwise products, summed by the accumulate
loop, and scaled by `R⁻¹` because the reduction that follows divides by the Montgomery radix.
That is exactly the `State` hypothesis `reduce_invntt_walk` asks for. -/

open Kopis.CrtScheme.NttAlg Kopis.CrtScheme.LevelFn in
theorem acc_State_q1 (N : ℕ) (acc : Array I32 512#usize) (nu nv : ℕ → Array I16 512#usize)
    (Fu Fv : ℕ → ℕ → ZMod 7681)
    (hu : ∀ jj < N, State zeta1 256 1 1 (Fu jj)
      (fun c => ((((nu jj).val[c]!).val : ℤ) : ZMod 7681)))
    (hv : ∀ jj < N, State zeta1 256 1 1 (Fv jj)
      (fun c => ((((nv jj).val[c]!).val : ℤ) : ZMod 7681)))
    (hacc : ∀ t < 512, (acc.val[t]!).val
      = ∑ jj ∈ Finset.range N, ((nu jj).val[t]!).val * ((nv jj).val[t]!).val) :
    State zeta1 256 1 (900 : ZMod 7681)
      (fun n => ∑ jj ∈ Finset.range N, nconv (Fu jj) (Fv jj) n)
      (fun cc => accZ32 7681 acc (0 + cc) * (900 : ZMod 7681)) := by
  have hprod : ∀ jj < N, State zeta1 256 1 1 (nconv (Fu jj) (Fv jj))
      (fun c => ((((nu jj).val[c]!).val : ℤ) : ZMod 7681)
        * ((((nv jj).val[c]!).val : ℤ) : ZMod 7681)) :=
    fun jj hjj => State_leaf_mul_q1 (hu jj hjj) (hv jj hjj)
  have hsum := Kopis.CrtScheme.LevelFn.State_sum hprod
  have hsc := Kopis.CrtScheme.LevelFn.State_scale (k := (900 : ZMod 7681)) hsum
  rw [mul_one] at hsc
  intro n hn r hr
  have hx := hsc n hn r hr
  show accZ32 7681 acc (0 + (n * 1 + r)) * 900 = _
  rw [show accZ32 7681 acc (0 + (n * 1 + r)) * (900 : ZMod 7681)
      = 900 * ∑ jj ∈ Finset.range N, ((((nu jj).val[n * 1 + r]!).val : ℤ) : ZMod 7681)
          * ((((nv jj).val[n * 1 + r]!).val : ℤ) : ZMod 7681) from by
    rw [accZ32, show 0 + (n * 1 + r) = n * 1 + r from by omega, hacc _ (by omega),
      Int.cast_sum, Finset.sum_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun jj _ => by push_cast; ring]
  exact hx

open Kopis.CrtScheme.NttAlg Kopis.CrtScheme.LevelFn in
theorem acc_State_q2 (N : ℕ) (acc : Array I32 512#usize) (nu nv : ℕ → Array I16 512#usize)
    (Fu Fv : ℕ → ℕ → ZMod 10753)
    (hu : ∀ jj < N, State zeta2 256 1 1 (Fu jj)
      (fun c => ((((nu jj).val[256 + c]!).val : ℤ) : ZMod 10753)))
    (hv : ∀ jj < N, State zeta2 256 1 1 (Fv jj)
      (fun c => ((((nv jj).val[256 + c]!).val : ℤ) : ZMod 10753)))
    (hacc : ∀ t < 512, (acc.val[t]!).val
      = ∑ jj ∈ Finset.range N, ((nu jj).val[t]!).val * ((nv jj).val[t]!).val) :
    State zeta2 256 1 (1764 : ZMod 10753)
      (fun n => ∑ jj ∈ Finset.range N, nconv (Fu jj) (Fv jj) n)
      (fun cc => accZ32 10753 acc (256 + cc) * (1764 : ZMod 10753)) := by
  have hprod : ∀ jj < N, State zeta2 256 1 1 (nconv (Fu jj) (Fv jj))
      (fun c => ((((nu jj).val[256 + c]!).val : ℤ) : ZMod 10753)
        * ((((nv jj).val[256 + c]!).val : ℤ) : ZMod 10753)) :=
    fun jj hjj => State_leaf_mul_q2 (hu jj hjj) (hv jj hjj)
  have hsum := Kopis.CrtScheme.LevelFn.State_sum hprod
  have hsc := Kopis.CrtScheme.LevelFn.State_scale (k := (1764 : ZMod 10753)) hsum
  rw [mul_one] at hsc
  intro n hn r hr
  have hx := hsc n hn r hr
  show accZ32 10753 acc (256 + (n * 1 + r)) * 1764 = _
  rw [show accZ32 10753 acc (256 + (n * 1 + r)) * (1764 : ZMod 10753)
      = 1764 * ∑ jj ∈ Finset.range N,
          ((((nu jj).val[256 + (n * 1 + r)]!).val : ℤ) : ZMod 10753)
          * ((((nv jj).val[256 + (n * 1 + r)]!).val : ℤ) : ZMod 10753) from by
    rw [accZ32, hacc _ (by omega), Int.cast_sum, Finset.sum_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun jj _ => by push_cast; ring]
  exact hx

/-! ## The three Montgomery constants cancel

`invntt_block` carries `256·σ = R` out and the reduction's `R⁻¹` undoes it. -/

unseal backend.crt.INVNTT_SCALE_1 in
theorem cancel_q1 :
    (((backend.crt.INVNTT_SCALE_1.val : ℤ) : ZMod 7681) * (900 : ZMod 7681))
      * (2 ^ 8 * (900 : ZMod 7681)) = 1 := by decide

unseal backend.crt.INVNTT_SCALE_2 in
theorem cancel_q2 :
    (((backend.crt.INVNTT_SCALE_2.val : ℤ) : ZMod 10753) * (1764 : ZMod 10753))
      * (2 ^ 8 * (1764 : ZMod 10753)) = 1 := by decide

/-! ## The NEON NTT entry point

What the whole chain delivers: `N` pointwise products, accumulated, inverse-transformed and
CRT-combined, are the coefficients of the sum of negacyclic convolutions — as wrapping `u16`. -/

open Kopis.CrtScheme.NttAlg Kopis.CrtScheme.LevelFn in
theorem ntt_entry_neon (N : ℕ) (hN : N ≤ 4)
    (acc : Array I32 512#usize) (nu nv : ℕ → Array I16 512#usize) (gu gv : ℕ → ℕ → ℤ)
    (hnu : ∀ jj < N, NttOK (gu jj) (nu jj)) (hnv : ∀ jj < N, NttOK (gv jj) (nv jj))
    (hacc : ∀ t < 512, (acc.val[t]!).val
      = ∑ jj ∈ Finset.range N, ((nu jj).val[t]!).val * ((nv jj).val[t]!).val)
    (X : ℕ → ℤ) (hXb : ∀ c < 256, 2 * |X c| < 82593793)
    (hX1 : ∀ c < 256, ((X c : ℤ) : ZMod 7681)
      = ∑ jj ∈ Finset.range N, nconv (fun n => ((gu jj n : ℤ) : ZMod 7681))
          (fun n => ((gv jj n : ℤ) : ZMod 7681)) c)
    (hX2 : ∀ c < 256, ((X c : ℤ) : ZMod 10753)
      = ∑ jj ∈ Finset.range N, nconv (fun n => ((gu jj n : ℤ) : ZMod 10753))
          (fun n => ((gv jj n : ℤ) : ZMod 10753)) c) :
    backend.neon.ntt.reduce_invntt acc
      ⦃ (r : Array U16 256#usize) => ∀ c < 256, ((r.val[c]!).val : ℤ) = X c % 2 ^ 16 ⦄ := by
  have hNz : ((N : ℤ)) ≤ 4 := by exact_mod_cast hN
  have hbnd : ∀ (B : ℤ) (t : ℕ), t < 512 → (0 ≤ B) →
      (∀ jj < N, |((nu jj).val[t]!).val| ≤ B) →
      (∀ jj < N, |((nv jj).val[t]!).val| ≤ B) →
      |(acc.val[t]!).val| ≤ (N : ℤ) * (B * B) := by
    intro B t ht hB0 hu hv
    rw [hacc t ht]
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    have hstep : (∑ jj ∈ Finset.range N, |((nu jj).val[t]!).val * ((nv jj).val[t]!).val|)
        ≤ ∑ _jj ∈ Finset.range N, B * B := by
      refine Finset.sum_le_sum fun jj hjj => ?_
      rw [abs_mul]
      exact mul_le_mul (hu jj (Finset.mem_range.mp hjj)) (hv jj (Finset.mem_range.mp hjj))
        (abs_nonneg _) hB0
    refine le_trans hstep ?_
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hacc1 : ∀ t < 256, |(acc.val[4 * (0#usize : Usize).val + t]!).val| ≤ 58982400 := by
    intro t ht
    rw [show 4 * (0#usize : Usize).val + t = t from by scalar_tac]
    refine le_trans (hbnd 3840 t (by omega) (by norm_num)
      (fun jj hjj => (hnu jj hjj).1 t ht) (fun jj hjj => (hnv jj hjj).1 t ht)) ?_
    nlinarith
  have hacc2 : ∀ t < 256, |(acc.val[4 * (64#usize : Usize).val + t]!).val| ≤ 115605504 := by
    intro t ht
    rw [show 4 * (64#usize : Usize).val + t = 256 + t from by scalar_tac]
    refine le_trans (hbnd 5376 (256 + t) (by omega) (by norm_num)
      (fun jj hjj => (hnu jj hjj).2.1 t ht) (fun jj hjj => (hnv jj hjj).2.1 t ht)) ?_
    nlinarith
  -- the two leaf states the accumulator carries
  have hs1 := acc_State_q1 N acc nu nv _ _ (fun jj hjj => (hnu jj hjj).2.2.1)
    (fun jj hjj => (hnv jj hjj).2.2.1) hacc
  have hs2 := acc_State_q2 N acc nu nv _ _ (fun jj hjj => (hnu jj hjj).2.2.2)
    (fun jj hjj => (hnv jj hjj).2.2.2) hacc
  have hr1 := State_root (invAll_State zeta1 zeta1_sq zeta1_pair hs1)
  have hr2 := State_root (invAll_State zeta2 zeta2_sq zeta2_pair hs2)
  refine reduce_invntt_walk acc X hXb hacc1 hacc2
    (fun cc => accZ32 7681 acc (0 + cc) * (900 : ZMod 7681))
    (fun c hc => by rw [show 4 * (0#usize : Usize).val + c = 0 + c from by scalar_tac]; ring)
    (fun cc => accZ32 10753 acc (256 + cc) * (1764 : ZMod 10753))
    (fun c hc => by rw [show 4 * (64#usize : Usize).val + c = 256 + c from by scalar_tac]; ring)
    (fun c hc => ?_) (fun c hc => ?_)
  · rw [hX1 c hc, hr1 c hc, ← mul_assoc, cancel_q1, one_mul]
  · rw [hX2 c hc, hr2 c hc, ← mul_assoc, cancel_q2, one_mul]

/-! ## Two utilities the twin stack wants -/

/-- The `i32` view of a zero-filled accumulator. -/
theorem acc_zero (t : ℕ) (ht : t < 512) :
    (((Array.repeat 512#usize (0#i32)).val[t]!).val : ℤ) = 0 := by
  rw [Array.repeat_val, getElem!_pos _ t
      (by rw [List.length_replicate]; show t < 512; omega),
    List.getElem_replicate]
  rfl

/-- Both halves of an `NttOK` block are inside `5376`, which is the common operand bound the
accumulate loop wants. -/
theorem NttOK_lane_bound {g : ℕ → ℤ} {ne : Array I16 512#usize} (h : NttOK g ne)
    (t : ℕ) (ht : t < 512) : |(ne.val[t]!).val| ≤ 5376 := by
  obtain ⟨h1, h2, _, _⟩ := h
  by_cases hlow : t < 256
  · exact le_trans (h1 t hlow) (by norm_num)
  · have := h2 (t - 256) (by omega)
    rwa [show 256 + (t - 256) = t from by omega] at this

open Kopis.CrtScheme.NttAlg in
/-- **The `reduce_invntt_to_ring_elem` dispatch.**  `available` is `ok true`, so there is no
portable branch to discharge, and `ntt_entry_neon` is the whole of it.  Stated in the shape the
generated twin's `NttBridge` wants: a residue mod `2¹⁶` rather than an equation. -/
theorem reduce_invntt_to_ring_elem_neon (N : ℕ) (hN : N ≤ 4)
    (acc : Array I32 512#usize) (nu nv : ℕ → Array I16 512#usize) (gu gv : ℕ → ℕ → ℤ)
    (hnu : ∀ jj < N, NttOK (gu jj) (nu jj)) (hnv : ∀ jj < N, NttOK (gv jj) (nv jj))
    (hacc : ∀ t < 512, (acc.val[t]!).val
      = ∑ jj ∈ Finset.range N, ((nu jj).val[t]!).val * ((nv jj).val[t]!).val)
    (H : ℕ → ℤ) (hHb : ∀ n < 256, 2 * |H n| < 82593793)
    (hH1 : ∀ c < 256, ((H c : ℤ) : ZMod 7681)
      = ∑ jj ∈ Finset.range N, nconv (fun n => ((gu jj n : ℤ) : ZMod 7681))
          (fun n => ((gv jj n : ℤ) : ZMod 7681)) c)
    (hH2 : ∀ c < 256, ((H c : ℤ) : ZMod 10753)
      = ∑ jj ∈ Finset.range N, nconv (fun n => ((gu jj n : ℤ) : ZMod 10753))
          (fun n => ((gv jj n : ℤ) : ZMod 10753)) c) :
    arithmetic.ntt.reduce_invntt_to_ring_elem acc
      ⦃ (r : arithmetic.ring_arith.RingElem) =>
          ∀ n, n < 256 → ((r.val[n]!).val : ℤ) % 65536 = H n % 65536 ⦄ := by
  unfold arithmetic.ntt.reduce_invntt_to_ring_elem
  rw [show backend.neon.cpu.available = ok true from rfl, bind_tc_ok, if_pos rfl]
  apply WP.spec_bind (ntt_entry_neon N hN acc nu nv gu gv hnu hnv hacc H hHb hH1 hH2)
  intro r hr
  simp only [WP.spec_ok]
  intro n hn
  rw [hr n hn, Int.emod_emod_of_dvd _ (by norm_num)]

/-- **The `NttElem::from_uniform` dispatch**, on top of `from_uniform_NttOK`. -/
theorem elem_from_uniform_NttOK (elem : arithmetic.ring_arith.RingElem) (g : ℕ → ℤ)
    (hg : ∀ c < 256, (elem.val[c]!).bv.toInt = g c) :
    arithmetic.ntt.NttElem.from_uniform elem
      ⦃ (r : arithmetic.ntt.NttElem) => NttOK g r ⦄ := by
  unfold arithmetic.ntt.NttElem.from_uniform
  rw [show backend.neon.cpu.available = ok true from rfl, bind_tc_ok, if_pos rfl]
  apply WP.spec_bind (from_uniform_NttOK elem g hg)
  intro r hr
  simp only [WP.spec_ok]
  exact hr

/-- **The `NttElem::from_secret` dispatch.**  The two per-prime bounds the twin has are stronger
than the single `|g| ≤ 3840` the NEON sampler needs. -/
theorem elem_from_secret_NttOK (elem : arithmetic.ring_arith.RingElem) (g : ℕ → ℤ)
    (hg : ∀ c < 256, (elem.val[c]!).bv.toInt = g c)
    (hs1 : ∀ c < 256, 2 * |g c| < 7681) (_hs2 : ∀ c < 256, 2 * |g c| < 10753) :
    arithmetic.ntt.NttElem.from_secret elem
      ⦃ (r : arithmetic.ntt.NttElem) => NttOK g r ⦄ := by
  unfold arithmetic.ntt.NttElem.from_secret
  rw [show backend.neon.cpu.available = ok true from rfl, bind_tc_ok, if_pos rfl]
  apply WP.spec_bind
    (from_secret_NttOK elem g hg (fun c hc => by have := hs1 c hc; omega))
  intro r hr
  simp only [WP.spec_ok]
  exact hr

end Kopis.Neon
