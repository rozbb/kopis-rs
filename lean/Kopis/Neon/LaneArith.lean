/-
  # Kopis/Neon/LaneArith.lean — the NEON lanes as signed integers, and `mont_mul`.

  Everything proved about the vector backend so far is *bit*-level: the deserializer and the
  sampler move bits around, so `BitVec` and `streamNat` are the right vocabulary and no
  arithmetic bridge is needed.  The NTT is different — `mont_mul` and `barrett` are congruences
  and magnitude bounds over ℤ, exactly like the serial `mont_reduce_spec` and
  `barrett_reduce_spec` — so its lanes have to be readable as signed integers.

  ## What is new here, and it has no AVX2 counterpart

  AArch64 has no plain 16-bit high multiply.  `Kopis/Avx2/LaneArith.lean` can read `vpmulhw` as
  `⌊a·b / 2¹⁶⌋` and be done; here the nearest instruction is `sqdmulh`, which returns the
  *doubled* high half with signed saturation, and the backend's Montgomery multiply is

      mont_mul a z zq q  =  shsub(sqdmulh(a, z), sqdmulh(t, q))     where  t = a·zq

  — two doubled high halves subtracted and halved *once*, rather than each shifted down
  separately.  `NEON_VERIFICATION_PLAN.md` §F1 calls the argument for that the first genuinely
  new piece of mathematics in the plan, and `mont_mul_lane` below is it.

  The argument, which is the comment on the Rust wrapper made precise.  Write `A = a·ψ` and
  `T = t·q`.  Because `zq ≡ ψ·q⁻¹ (mod 2¹⁶)`, the two agree mod `2¹⁶`: `A = 2¹⁶p + r` and
  `T = 2¹⁶k + r` with the *same* `r`.  Then

      ⌊2A/2¹⁶⌋ = 2p + ⌊2r/2¹⁶⌋   and   ⌊2T/2¹⁶⌋ = 2k + ⌊2r/2¹⁶⌋

  with the *same* carry bit `⌊2r/2¹⁶⌋ ∈ {0,1}`, because it depends only on `r`.  So the
  difference is `2(p − k)` exactly, the halving recovers `p − k`, and

      mont_mul · 2¹⁶  =  a·ψ − t·q

  with no error term at all — which is the form the NTT wants, since `t·q ≡ 0 (mod q)` gives the
  congruence and `|t| ≤ 2¹⁵` gives the bound.

  ## Saturation

  `sqdmulh` saturates only when both operands are `−2¹⁵`, and the lemmas below carry that as an
  explicit hypothesis on the *second* operand (the ψ, the modulus, or the Barrett multiplier),
  never on the first (the data).  No constant in `src/backend/crt.rs` is `−2¹⁵`, so every call
  site discharges it by evaluation — but it is a hypothesis, not an assumption.
-/
import Kopis.Neon.Model

open Aeneas Aeneas.Std Result
open RustKopisNeon

namespace Kopis.Neon

open RustKopisNeon.backend.neon.intrinsics

set_option maxHeartbeats 1000000

/-! ## Reading a 16-bit lane as an integer -/

/-- A 16-bit lane's signed range. -/
theorem toInt_bounds (x : BitVec 16) : -32768 ≤ x.toInt ∧ x.toInt < 32768 := by
  have h1 := BitVec.le_toInt x
  have h2 := BitVec.toInt_lt (x := x)
  norm_num at h1 h2
  omega

/-- `BitVec.ofInt` is exact on the signed 16-bit range. -/
theorem toInt_ofInt16 (v : ℤ) (h1 : -32768 ≤ v) (h2 : v ≤ 32767) :
    (BitVec.ofInt 16 v).toInt = v := by
  rw [BitVec.toInt_ofInt]
  unfold Int.bmod
  norm_num
  split <;> omega

/-- Signed saturation is the identity on the range it saturates *to*. -/
theorem toInt_satS16 (v : ℤ) (h1 : -32768 ≤ v) (h2 : v ≤ 32767) : (satS16 v).toInt = v := by
  unfold satS16
  rw [if_neg (by omega), if_neg (by omega)]
  exact toInt_ofInt16 v h1 h2

/-- A floor shift by a non-negative divisor is Euclidean division, which is the form `omega`
reasons about. -/
theorem fdiv_eq_ediv_pos (a : ℤ) {b : ℤ} (hb : 0 ≤ b) : a.fdiv b = a / b :=
  Int.fdiv_eq_ediv_of_nonneg a hb

/-! ## The instructions, lane by lane, over ℤ

Each is the corresponding `Model` equation read through `BitVec.toInt`. -/

/-- `add.8h` lane `i`, wrapping. -/
theorem add_lane_toInt (a b c : Vec128) (hc : bits c = Model.add16 (bits a) (bits b)) :
    ∀ i < 8, (lane16 c i).toInt = ((lane16 a i).toInt + (lane16 b i).toInt).bmod (2 ^ 16) := by
  intro i hi
  have hl : lane16 c i = lane16 a i + lane16 b i := by
    show laneOf 16 (bits c) i = _
    rw [hc]
    simp only [Model.add16]
    exact laneOf_ofLanes16 _ hi
  rw [hl, BitVec.toInt_add]

/-- `sub.8h` lane `i`, wrapping. -/
theorem sub_lane_toInt (a b c : Vec128) (hc : bits c = Model.sub16 (bits a) (bits b)) :
    ∀ i < 8, (lane16 c i).toInt = ((lane16 a i).toInt - (lane16 b i).toInt).bmod (2 ^ 16) := by
  intro i hi
  have hl : lane16 c i = lane16 a i - lane16 b i := by
    show laneOf 16 (bits c) i = _
    rw [hc]
    simp only [Model.sub16]
    exact laneOf_ofLanes16 _ hi
  rw [hl, BitVec.toInt_sub]

/-- `mul.8h` lane `i`: the product truncated to 16 bits. -/
theorem mul_lane_toInt (a b c : Vec128) (hc : bits c = Model.mul16 (bits a) (bits b)) :
    ∀ i < 8, (lane16 c i).toInt = ((lane16 a i).toInt * (lane16 b i).toInt).bmod (2 ^ 16) := by
  intro i hi
  have hl : lane16 c i = lane16 a i * lane16 b i := by
    show laneOf 16 (bits c) i = _
    rw [hc]
    simp only [Model.mul16]
    exact laneOf_ofLanes16 _ hi
  rw [hl, BitVec.toInt_mul]

/-- `sshr.8h #k` lane `i`: an arithmetic shift is a floor division. -/
theorem sshr_lane_toInt (k : ℕ) (a c : Vec128) (hc : bits c = Model.sshrNS16 k (bits a)) :
    ∀ i < 8, (lane16 c i).toInt = (lane16 a i).toInt >>> k := by
  intro i hi
  have hl : lane16 c i = (lane16 a i).sshiftRight k := by
    show laneOf 16 (bits c) i = _
    rw [hc]
    simp only [Model.sshrNS16]
    exact laneOf_ofLanes16 _ hi
  rw [hl, BitVec.toInt_sshiftRight]

/-- `shsub.8h` lane `i` is *exactly* `⌊(a − b)/2⌋`: the subtraction happens at 17 bits and the
halving brings it back inside 16, so there is no wrapping to account for. -/
theorem shsub_lane_toInt (a b c : Vec128) (hc : bits c = Model.shsubS16 (bits a) (bits b)) :
    ∀ i < 8, (lane16 c i).toInt = ((lane16 a i).toInt - (lane16 b i).toInt) / 2 := by
  intro i hi
  obtain ⟨ha1, ha2⟩ := toInt_bounds (lane16 a i)
  obtain ⟨hb1, hb2⟩ := toInt_bounds (lane16 b i)
  have hl : lane16 c i
      = BitVec.ofInt 16 (Int.fdiv ((lane16 a i).toInt - (lane16 b i).toInt) 2) := by
    show laneOf 16 (bits c) i = _
    rw [hc]
    simp only [Model.shsubS16]
    exact laneOf_ofLanes16 _ hi
  rw [hl, fdiv_eq_ediv_pos _ (by norm_num)]
  exact toInt_ofInt16 _ (by omega) (by omega)

/-- `sqdmulh.8h` lane `i` is `⌊2·a·b / 2¹⁶⌋`, with the saturation ruled out by `b ≠ −2¹⁵`. -/
theorem sqdmulh_lane_toInt (a b c : Vec128) (hc : bits c = Model.sqdmulhS16 (bits a) (bits b))
    (i : ℕ) (hi : i < 8) (hb : -32767 ≤ (lane16 b i).toInt) :
    (lane16 c i).toInt = 2 * ((lane16 a i).toInt * (lane16 b i).toInt) / 65536 := by
  obtain ⟨ha1, ha2⟩ := toInt_bounds (lane16 a i)
  obtain ⟨hb1, hb2⟩ := toInt_bounds (lane16 b i)
  have hl : lane16 c i
      = satS16 (Int.fdiv (2 * (lane16 a i).toInt * (lane16 b i).toInt) 65536) := by
    show laneOf 16 (bits c) i = _
    rw [hc]
    simp only [Model.sqdmulhS16]
    exact laneOf_ofLanes16 _ hi
  -- the product never reaches 2³¹, so the shift lands strictly inside a 16-bit lane
  have hP1 : -2147418112 ≤ 2 * ((lane16 a i).toInt * (lane16 b i).toInt) := by nlinarith
  have hP2 : 2 * ((lane16 a i).toInt * (lane16 b i).toInt) ≤ 2147418112 := by nlinarith
  rw [hl, fdiv_eq_ediv_pos _ (by norm_num),
    show (2 : ℤ) * (lane16 a i).toInt * (lane16 b i).toInt
      = 2 * ((lane16 a i).toInt * (lane16 b i).toInt) from by ring]
  exact toInt_satS16 _ (by omega) (by omega)

/-! ## `mulhi`

`mulhi a b = sshr #1 (sqdmulh a b)`: undo `sqdmulh`'s doubling and the plain high half is left.
Not used by `mont_mul`, which fuses the two shifts, but `barrett` needs it on its own. -/

/-- Shifting the doubled high half down by one gives the high half. -/
theorem halve_double_high (P : ℤ) : (2 * P / 65536) / 2 = P / 65536 := by omega

open RustKopisNeon.backend.neon.intrinsics in
/-- `mulhi` lane `i` is `⌊aᵢ·bᵢ / 2¹⁶⌋`. -/
theorem mulhi_lane_toInt (a b s c : Vec128)
    (hs : bits s = Model.sqdmulhS16 (bits a) (bits b))
    (hc : bits c = Model.sshrNS16 1 (bits s))
    (i : ℕ) (hi : i < 8) (hb : -32767 ≤ (lane16 b i).toInt) :
    (lane16 c i).toInt = (lane16 a i).toInt * (lane16 b i).toInt / 65536 := by
  rw [sshr_lane_toInt 1 s c hc i hi, sqdmulh_lane_toInt a b s hs i hi hb,
    Int.shiftRight_eq_div_pow]
  simpa using halve_double_high ((lane16 a i).toInt * (lane16 b i).toInt)

/-! ## `mont_mul`

The theorem the plan calls new.  Stated multiplied out — `c · 2¹⁶ = a·ψ − t·q` — so that the NTT
gets both facts it needs without a division in sight: the congruence mod `q` because `t·q` is a
multiple of `q`, and the magnitude bound because `|t| ≤ 2¹⁵`. -/

/-- The carry-cancellation identity, as pure integer arithmetic.  `A` and `T` agreeing mod `2¹⁶`
is what makes the two `sqdmulh` results carry the *same* bit, so subtracting them doubled and
halving once is exact. -/
theorem mont_carry_cancel (A T c : ℤ) (hAT : A % 65536 = T % 65536)
    (hc : c = (2 * A / 65536 - 2 * T / 65536) / 2) :
    c * 65536 = A - T := by omega

/-- `Int.bmod` does not change a residue. -/
theorem bmod_emod (x : ℤ) : (x.bmod (2 ^ 16)) % 65536 = x % 65536 := by
  unfold Int.bmod
  norm_num
  split <;> omega

open RustKopisNeon.backend.neon.intrinsics in
/-- **`mont_mul` is exact.**  With `t = a·zq` truncated to 16 bits and `zq·q ≡ z (mod 2¹⁶)`, the
`shsub` of the two `sqdmulh` results satisfies

    result · 2¹⁶ = a·z − t·q

with no error term.  The two saturation side conditions are on the *constants* — a ψ and the
modulus — and no constant in the crate is `−2¹⁵`. -/
theorem mont_mul_lane (a z zq q t s1 s2 c : Vec128)
    (ht : bits t = Model.mul16 (bits a) (bits zq))
    (hs1 : bits s1 = Model.sqdmulhS16 (bits a) (bits z))
    (hs2 : bits s2 = Model.sqdmulhS16 (bits t) (bits q))
    (hc : bits c = Model.shsubS16 (bits s1) (bits s2))
    (i : ℕ) (hi : i < 8)
    (hz : -32767 ≤ (lane16 z i).toInt)
    (hq : -32767 ≤ (lane16 q i).toInt)
    (hzq : (lane16 zq i).toInt * (lane16 q i).toInt % 65536 = (lane16 z i).toInt % 65536) :
    (lane16 c i).toInt * 65536
      = (lane16 a i).toInt * (lane16 z i).toInt - (lane16 t i).toInt * (lane16 q i).toInt := by
  -- `t` is `a·zq` mod `2¹⁶`, so `t·q` and `a·z` are congruent mod `2¹⁶`
  have htv : (lane16 t i).toInt
      = ((lane16 a i).toInt * (lane16 zq i).toInt).bmod (2 ^ 16) := mul_lane_toInt a zq t ht i hi
  have hAT : (lane16 a i).toInt * (lane16 z i).toInt % 65536
      = (lane16 t i).toInt * (lane16 q i).toInt % 65536 := by
    conv_rhs => rw [htv, Int.mul_emod, bmod_emod, ← Int.mul_emod, Int.mul_assoc, Int.mul_emod,
      hzq, ← Int.mul_emod]
  -- each `sqdmulh` is the doubled high half
  have h1 := sqdmulh_lane_toInt a z s1 hs1 i hi hz
  have h2 := sqdmulh_lane_toInt t q s2 hs2 i hi hq
  -- and the halving subtraction cancels the shared carry
  have h3 := shsub_lane_toInt s1 s2 c hc i hi
  rw [h1, h2] at h3
  exact mont_carry_cancel _ _ _ hAT h3

end Kopis.Neon
