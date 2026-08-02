/-
  # Kopis/Avx2/LaneArith.lean — the AVX2 lanes as signed integers.

  Everything proved about the vector backend so far is *bit*-level: the deserializer and the
  sampler move bits around, so `BitVec` and `streamNat` are the right vocabulary and no
  arithmetic bridge is needed.  The NTT is different — `mont_mul` and `barrett` are congruences
  and magnitude bounds over ℤ, exactly like the serial `mont_reduce_spec` and
  `barrett_reduce_spec` — so its lanes have to be readable as signed integers.

  Lean supplies most of that (`BitVec.toInt_add`, `toInt_sub`, `toInt_mul`, `toInt_sshiftRight`),
  all in the `Int.bmod` form the serial proofs already use.  The piece that is missing, and the
  reason this file exists, is `vpmulhw`: the *high* half of a signed 16×16 product.
  `toInt_extractLsb'_high` says that half, read as a signed 16-bit number, is exactly
  `⌊a·b / 2¹⁶⌋` — which is what makes Montgomery reduction work, and the one step where a
  sign-extension error would be invisible at the bit level.

  With these, a `mont_mul` or `barrett` lane spec is ordinary integer arithmetic in the same
  shape as `Kopis/Properties/NttReduce*.lean`.  See the Phase F notes in
  `AVX2_VERIFICATION_PLAN.md`.
-/
import Kopis.Avx2.Model

open Aeneas Aeneas.Std Result
open RustKopisAvx2

namespace Kopis.Avx2

open RustKopisAvx2.backend.avx2.intrinsics

set_option maxHeartbeats 1000000

/-! ## The high half of a signed product

`vpmulhw` sign-extends its 16-bit operands to 32 bits, multiplies, and keeps bits 16..31.  Read
as a signed 16-bit number that is the floor of the true quotient — including for negative
products, which is the case worth checking, and the one an unsigned model would get wrong. -/

/-- The top half of a 32-bit word, read as a signed 16-bit number, is the arithmetic shift of
the whole word. -/
theorem toInt_extractLsb'_high (P : BitVec 32) :
    (BitVec.extractLsb' 16 16 P).toInt = P.toInt >>> (16 : ℕ) := by
  have h32 : P.toNat < 2 ^ 32 := P.isLt
  rw [BitVec.toInt_extractLsb', BitVec.toInt_eq_toNat_bmod, Int.shiftRight_eq_div_pow,
    Nat.shiftRight_eq_div_pow]
  simp only [Int.bmod]
  norm_num
  split <;> split <;> omega

/-- A 16-bit lane's signed range. -/
theorem toInt_bounds (x : BitVec 16) : -32768 ≤ x.toInt ∧ x.toInt < 32768 := by
  have h1 := BitVec.le_toInt x
  have h2 := BitVec.toInt_lt (x := x)
  norm_num at h1 h2
  omega

/-- `bmod` by `2³²` is the identity on the signed 32-bit range. -/
private theorem bmod32_eq_self {z : ℤ} (h1 : -(2 ^ 31 : ℤ) ≤ z) (h2 : z < 2 ^ 31) :
    z.bmod (2 ^ 32) = z := by
  unfold Int.bmod
  norm_num
  split <;> omega

/-- A signed 16×16 product does not overflow 32 bits, so the sign-extended product is the
integer product. -/
theorem toInt_signExtend_mul (x y : BitVec 16) :
    ((x.signExtend 32) * (y.signExtend 32)).toInt = x.toInt * y.toInt := by
  obtain ⟨hx1, hx2⟩ := toInt_bounds x
  obtain ⟨hy1, hy2⟩ := toInt_bounds y
  have hb1 : -(2 ^ 31 : ℤ) ≤ x.toInt * y.toInt := by nlinarith
  have hb2 : x.toInt * y.toInt < 2 ^ 31 := by nlinarith
  rw [BitVec.toInt_mul, BitVec.toInt_signExtend_of_le (by omega),
    BitVec.toInt_signExtend_of_le (by omega)]
  exact bmod32_eq_self hb1 hb2

/-! ## The lane specs, over ℤ

Each is the corresponding `Model` equation read through `BitVec.toInt`.  `mulhi` is the one with
content; the rest are Lean's own lemmas, restated on lanes so the NTT proofs can use them
uniformly. -/

/-- `vpmulhw` lane `i` is `⌊aᵢ·bᵢ / 2¹⁶⌋`. -/
theorem mulhi_lane_toInt (a b c : Vec256) (hc : bits c = Model.mulhiEpi16 (bits a) (bits b)) :
    ∀ i < 16, (lane16 c i).toInt = ((lane16 a i).toInt * (lane16 b i).toInt) >>> (16 : ℕ) := by
  intro i hi
  have hl : lane16 c i =
      BitVec.extractLsb' 16 16 ((lane16 a i).signExtend 32 * (lane16 b i).signExtend 32) := by
    show laneOf 16 (bits c) i = _
    rw [hc]
    simp only [Model.mulhiEpi16]
    exact laneOf_ofLanes16 _ hi
  rw [hl, toInt_extractLsb'_high, toInt_signExtend_mul]

/-- `vpmullw` lane `i` is the product truncated to 16 bits. -/
theorem mullo_lane_toInt (a b c : Vec256) (hc : bits c = Model.mulloEpi16 (bits a) (bits b)) :
    ∀ i < 16, (lane16 c i).toInt = ((lane16 a i).toInt * (lane16 b i).toInt).bmod (2 ^ 16) := by
  intro i hi
  have hl : lane16 c i = lane16 a i * lane16 b i := by
    show laneOf 16 (bits c) i = _
    rw [hc]
    simp only [Model.mulloEpi16]
    exact laneOf_ofLanes16 _ hi
  rw [hl, BitVec.toInt_mul]

/-- `vpaddw` lane `i`, wrapping. -/
theorem add_lane_toInt (a b c : Vec256) (hc : bits c = Model.addEpi16 (bits a) (bits b)) :
    ∀ i < 16, (lane16 c i).toInt = ((lane16 a i).toInt + (lane16 b i).toInt).bmod (2 ^ 16) := by
  intro i hi
  have hl : lane16 c i = lane16 a i + lane16 b i := by
    show laneOf 16 (bits c) i = _
    rw [hc]
    simp only [Model.addEpi16]
    exact laneOf_ofLanes16 _ hi
  rw [hl, BitVec.toInt_add]

/-- `vpsubw` lane `i`, wrapping. -/
theorem sub_lane_toInt (a b c : Vec256) (hc : bits c = Model.subEpi16 (bits a) (bits b)) :
    ∀ i < 16, (lane16 c i).toInt = ((lane16 a i).toInt - (lane16 b i).toInt).bmod (2 ^ 16) := by
  intro i hi
  have hl : lane16 c i = lane16 a i - lane16 b i := by
    show laneOf 16 (bits c) i = _
    rw [hc]
    simp only [Model.subEpi16]
    exact laneOf_ofLanes16 _ hi
  rw [hl, BitVec.toInt_sub]

/-- `vpsraw` lane `i`: an arithmetic shift is a floor division. -/
theorem srai_lane_toInt (k : ℕ) (a c : Vec256) (hc : bits c = Model.sraiEpi16 k (bits a)) :
    ∀ i < 16, (lane16 c i).toInt = (lane16 a i).toInt >>> k := by
  intro i hi
  have hl : lane16 c i = (lane16 a i).sshiftRight k := by
    show laneOf 16 (bits c) i = _
    rw [hc]
    simp only [Model.sraiEpi16]
    exact laneOf_ofLanes16 _ hi
  rw [hl, BitVec.toInt_sshiftRight]

end Kopis.Avx2
