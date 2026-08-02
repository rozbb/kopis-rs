/-
  # Kopis/Avx2/Cbd.lean — the AVX2 centred-binomial sampler.

  `src/backend/avx2/sample.rs` is short because it reuses the deserializer: it pulls the `MU`-bit
  field for each coefficient out with `ser::deserialize` — which Phase C characterises exactly —
  and then does two small population counts per 16-bit lane.

  So the whole content here is the popcount.  `popcount_small` looks the low nibble up in a
  `vpshufb` table and adds bit 4, which is valid precisely because every value it sees is below
  32; that bound comes from `MU/2 ≤ 5`, not from an assumption.  The result is

      out[k] = cbdX buf (MU/2) (MU·k) − cbdX buf (MU/2) (MU·k + MU/2)   (wrapping, u16)

  and `cbdX` is the same definition the portable sampler is proved against.
-/
import Kopis.Avx2.Ser

open Aeneas Aeneas.Std Result
open RustKopisAvx2

namespace Kopis.Avx2

open Kopis.Properties (streamNat streamByte streamBit streamNat_lt cbdX cbdX_le cbdX_eq_bitSum
  testBit_streamNat)

set_option maxHeartbeats 1000000
set_option maxRecDepth 4000

/-! ## The nibble table -/

/-- Popcount of a nibble, as the sum of its four bits. -/
def nibblePop (v : ℕ) : ℕ := ∑ j ∈ Finset.range 4, ((v % 16).testBit j).toNat

/-- The table the backend ships is the nibble popcount, in both 128-bit halves. -/
theorem nibble_table (k : ℕ) (hk : k < 32) :
    ((backend.avx2.sample.NIBBLE_POPCOUNT.val[k]!) : U8).val = nibblePop k := by
  simp only [backend.avx2.sample.NIBBLE_POPCOUNT, nibblePop]
  rcases show k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 ∨ k = 8 ∨ k = 9 ∨
      k = 10 ∨ k = 11 ∨ k = 12 ∨ k = 13 ∨ k = 14 ∨ k = 15 ∨ k = 16 ∨ k = 17 ∨ k = 18 ∨ k = 19 ∨
      k = 20 ∨ k = 21 ∨ k = 22 ∨ k = 23 ∨ k = 24 ∨ k = 25 ∨ k = 26 ∨ k = 27 ∨ k = 28 ∨ k = 29 ∨
      k = 30 ∨ k = 31 from by omega with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl <;>
    decide

/-- Nibble popcount plus bit 4 is the popcount of the whole five-bit value — the identity
`popcount_small` is built on. -/
theorem pop_split (v : ℕ) :
    nibblePop v + (v >>> 4) % 2 = ∑ i ∈ Finset.range 5, (v.testBit i).toNat := by
  rw [Finset.sum_range_succ]
  congr 1
  · refine Finset.sum_congr rfl fun j hj => ?_
    rw [show (16:ℕ) = 2 ^ 4 from rfl, Nat.testBit_mod_two_pow]
    simp [Finset.mem_range.mp hj]
  · rw [Nat.testBit_eq_decide_div_mod_eq, Nat.shiftRight_eq_div_pow]
    rcases Nat.mod_two_eq_zero_or_one (v / 2 ^ 4) with h | h <;>
      simp only [show (2:ℕ) ^ 4 = 16 from rfl] at h <;> simp [h]

/-! ## `popcount_small`

One `vpshufb` covers the low nibble; the high byte of each 16-bit lane is zero, so its lookup
yields `nibblePop 0 = 0` and does not disturb the 16-bit sum.  Bit 4 contributes itself.  Valid
exactly while every lane is below 32. -/

open RustKopisAvx2.backend.avx2.intrinsics in
theorem popcount_small_spec (v lut : Vec256)
    (hlut : ∀ i < 32, (lane8 lut i).toNat = nibblePop i)
    (hv : ∀ m < 16, (lane16 v m).toNat < 32) :
    backend.avx2.sample.popcount_small v lut
      ⦃ (c : Vec256) => ∀ m < 16,
          (lane16 c m).toNat
            = ∑ i ∈ Finset.range 5, ((lane16 v m).toNat.testBit i).toNat ⦄ := by
  unfold backend.avx2.sample.popcount_small
  obtain ⟨v1, hv1, hv1l⟩ := set1_epi16_spec 15#i16
  rw [hv1, bind_tc_ok]
  obtain ⟨v2, hv2, hv2b⟩ := and_si256_model v v1
  rw [hv2, bind_tc_ok]
  obtain ⟨low, hlow, hlowb⟩ := shuffle_epi8_model lut v2
  rw [hlow, bind_tc_ok]
  obtain ⟨v3, hv3, hv3b⟩ := srli_epi16_model 4#i32 v (by decide)
  rw [hv3, bind_tc_ok]
  obtain ⟨v4, hv4, hv4l⟩ := set1_epi16_spec 1#i16
  rw [hv4, bind_tc_ok]
  obtain ⟨bit4, hbit4, hbit4b⟩ := and_si256_model v3 v4
  rw [hbit4, bind_tc_ok]
  obtain ⟨c, hc, hcb⟩ := add_epi16_model low bit4
  rw [hc]
  simp only [WP.spec_ok]
  intro m hm
  have hp8 : (2:ℕ) ^ 8 = 256 := by norm_num
  have hp16 : (2:ℕ) ^ 16 = 65536 := by norm_num
  -- the masked value: each lane's low nibble
  have hnib : ∀ m' < 16, (lane16 v2 m').toNat = (lane16 v m').toNat % 16 := by
    intro m' hm'
    have hl : lane16 v2 m' = lane16 v m' &&& lane16 v1 m' := by
      show laneOf 16 (bits v2) m' = _
      rw [hv2b]
      simp only [Model.andSi256]
      exact laneOf_and 16 (bits v) (bits v1) m'
    rw [hl, hv1l m' hm', BitVec.toNat_and,
      show ((15#i16 : I16).bv).toNat = 2 ^ 4 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  -- its two bytes: the nibble, and zero
  have hlo8 : ∀ m' < 16, (lane8 v2 (2 * m')).toNat = (lane16 v m').toNat % 16 := by
    intro m' hm'
    have hsm : (lane16 v2 m').toNat < 256 := by have := hnib m' hm'; omega
    show (laneOf 8 (bits v2) (2 * m')).toNat = _
    rw [laneOf_laneOf 8 2 (bits v2) (2 * m') (by omega),
      show 2 * m' / 2 = m' from by omega, show 2 * m' % 2 = 0 from by omega]
    show ((laneOf 8 (lane16 v2 m') 0)).toNat = _
    rw [toNat_laneOf]
    simp only [Nat.mul_zero, Nat.shiftRight_zero]
    rw [Nat.mod_eq_of_lt (by omega), hnib m' hm']
  have hhi8 : ∀ m' < 16, (lane8 v2 (2 * m' + 1)).toNat = 0 := by
    intro m' hm'
    have hsm : (lane16 v2 m').toNat < 256 := by have := hnib m' hm'; omega
    show (laneOf 8 (bits v2) (2 * m' + 1)).toNat = _
    rw [laneOf_laneOf 8 2 (bits v2) (2 * m' + 1) (by omega),
      show (2 * m' + 1) / 2 = m' from by omega, show (2 * m' + 1) % 2 = 1 from by omega]
    show ((laneOf 8 (lane16 v2 m') 1)).toNat = _
    rw [toNat_laneOf, Nat.mul_one, Nat.shiftRight_eq_div_pow,
      Nat.div_eq_of_lt (by omega)]
    simp
  -- the table lookups
  have hshufb : ∀ i < 32, (lane8 low i).toNat = nibblePop (lane8 v2 i).toNat := by
    intro i hi
    have hhalf : i / 2 < 16 := by omega
    have hsmall : (lane8 v2 i).toNat < 16 := by
      by_cases hpar : i % 2 = 0
      · rw [show i = 2 * (i / 2) from by omega, hlo8 _ hhalf]
        omega
      · rw [show i = 2 * (i / 2) + 1 from by omega, hhi8 _ hhalf]
        omega
    have hbit7 : (lane8 v2 i).getLsbD 7 = false := by
      show (lane8 v2 i).toNat.testBit 7 = false
      exact Nat.testBit_lt_two_pow (by omega)
    have hand : ((lane8 v2 i) &&& 0x0F#8).toNat = (lane8 v2 i).toNat := by
      rw [BitVec.toNat_and, show ((0x0F#8 : BitVec 8)).toNat = 2 ^ 4 - 1 from rfl,
        Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt (by omega)]
    have hl : lane8 low i = lane8 lut (16 * (i / 16) + (lane8 v2 i).toNat) := by
      show laneOf 8 (bits low) i = _
      rw [hlowb]
      simp only [Model.shuffleEpi8]
      rw [laneOf_ofLanes8 _ hi, if_neg (by simpa using hbit7), hand]
    rw [hl, hlut _ (by omega)]
    unfold nibblePop
    rw [show (16 * (i / 16) + (lane8 v2 i).toNat) % 16 = (lane8 v2 i).toNat % 16 from by omega]
  -- the low half of the result is the nibble popcount, the high half zero
  have hlowlane : (lane16 low m).toNat = nibblePop ((lane16 v m).toNat) := by
    have hb : lane16 low m = lane8 low (2 * m + 1) ++ lane8 low (2 * m) := lane16_eq_bytes _ m
    have hz : (lane8 low (2 * m + 1)).toNat = 0 := by
      rw [hshufb _ (by omega), hhi8 m hm]
      simp [nibblePop]
    have hzz : lane8 low (2 * m + 1) = 0#8 := by
      apply BitVec.eq_of_toNat_eq; simpa using hz
    rw [hb, hzz, BitVec.toNat_append]
    simp only [BitVec.toNat_ofNat, Nat.zero_mod, Nat.zero_shiftLeft, Nat.zero_or]
    rw [hshufb _ (by omega), hlo8 m hm]
    unfold nibblePop
    rw [Nat.mod_mod_of_dvd _ (dvd_refl 16)]
  -- bit 4
  have hbit4lane : (lane16 bit4 m).toNat = ((lane16 v m).toNat >>> 4) % 2 := by
    have hl : lane16 bit4 m = lane16 v3 m &&& lane16 v4 m := by
      show laneOf 16 (bits bit4) m = _
      rw [hbit4b]
      simp only [Model.andSi256]
      exact laneOf_and 16 (bits v3) (bits v4) m
    have hv3l : lane16 v3 m = lane16 v m >>> 4 := by
      show laneOf 16 (bits v3) m = _
      rw [hv3b]
      simp only [Model.srliEpi16]
      rw [laneOf_ofLanes16 _ hm]
      rfl
    rw [hl, hv3l, hv4l m hm, BitVec.toNat_and,
      show ((1#i16 : I16).bv).toNat = 2 ^ 1 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod,
      BitVec.toNat_ushiftRight]
  -- and their sum does not wrap
  have hsum : lane16 c m = lane16 low m + lane16 bit4 m := by
    show laneOf 16 (bits c) m = _
    rw [hcb]
    simp only [Model.addEpi16]
    exact laneOf_ofLanes16 _ hm
  have hbnd : (lane16 low m).toNat + (lane16 bit4 m).toNat < 2 ^ 16 := by
    have h1 : nibblePop ((lane16 v m).toNat) ≤ 4 := by
      unfold nibblePop
      calc ∑ j ∈ Finset.range 4, (((lane16 v m).toNat % 16).testBit j).toNat
          ≤ ∑ _j ∈ Finset.range 4, 1 := Finset.sum_le_sum fun j _ => by
              cases (((lane16 v m).toNat % 16).testBit j) <;> simp
        _ = 4 := by simp
    rw [hlowlane, hbit4lane]
    omega
  rw [hsum, BitVec.toNat_add, Nat.mod_eq_of_lt hbnd, hlowlane, hbit4lane, pop_split]

/-! ## The dynamic shift

`vpsrlw` takes its count from a register rather than an immediate, which is how the backend
avoids monomorphising over `MU/2`. -/

open RustKopisAvx2.backend.avx2.intrinsics in
theorem shift_right_dynamic_spec (v : Vec256) (count : Usize) (hc : count.val ≤ 8) :
    backend.avx2.sample.shift_right_dynamic v count
      ⦃ (c : Vec256) => ∀ m < 16, lane16 c m = lane16 v m >>> count.val ⦄ := by
  unfold backend.avx2.sample.shift_right_dynamic
  let* ⟨ ic, hic ⟩ ← UScalar.hcast_inBounds_spec .I32 count (by scalar_tac)
  obtain ⟨w, hw, hwb⟩ := cvtsi32_si128_model ic
  rw [hw, bind_tc_ok]
  obtain ⟨c, hc', hcl⟩ := srl_epi16_spec v w
  rw [hc']
  simp only [WP.spec_ok]
  intro m hm
  rw [hcl m hm]
  congr 1
  -- the count is the low 64 bits of the half-register, i.e. the `usize` itself
  rw [hwb]
  simp only [Model.cvtsi32Si128, toNat_laneOf, Nat.mul_zero, Nat.shiftRight_zero,
    BitVec.toNat_setWidth]
  have hbv : (ic.bv).toNat = count.val := i32_bv_toNat hic
  rw [hbv, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]

/-! ## The loop

Each iteration turns sixteen `MU`-bit fields into sixteen coefficients: mask off the low half,
shift down and mask off the high half, popcount both, subtract. -/

open RustKopisAvx2.backend.avx2.intrinsics in
theorem cbd_loop_spec (buf : Slice U8) (mu half : ℕ) (hmu : mu = 2 * half) (hhalf : 1 ≤ half)
    (hhalf5 : half ≤ 5) (halfU : Usize) (hhalfU : halfU.val = half)
    (fields : Array U16 256#usize)
    (hfields : ∀ j < 256, (fields.val[j]!).val = streamNat buf (mu * j) mu)
    (lut half_mask : Vec256)
    (hlut : ∀ i < 32, (lane8 lut i).toNat = nibblePop i)
    (hmask : ∀ m < 16, (lane16 half_mask m).toNat = 2 ^ half - 1)
    (iter : core.ops.range.Range Usize) (hend : iter.«end».val = 16)
    (out : arithmetic.ring_arith.RingElem) :
    backend.avx2.sample.cbd_loop halfU iter fields lut half_mask out
      ⦃ (r : arithmetic.ring_arith.RingElem) => ∀ j < 256,
          (r.val[j]!).val =
            if j < 16 * iter.start.val then (out.val[j]!).val
            else Kopis.Properties.cbdU16 buf half (mu * j) ⦄ := by
  unfold backend.avx2.sample.cbd_loop
  by_cases hlt : iter.start.val < iter.«end».val
  · let* ⟨ o, iter1, ho, hstart', hend' ⟩ ← core.iter.range.IteratorRange.next_Usize_some_spec
    rw [ho]
    simp only
    have hi16 : iter.start.val < 16 := by omega
    -- the sixteen fields of this block
    obtain ⟨field, hfield, hfieldl⟩ := load_u16_spec fields iter.start (by scalar_tac)
    rw [hfield, bind_tc_ok]
    have hfv : ∀ k < 16, (lane16 field k).toNat
        = streamNat buf (mu * (16 * iter.start.val + k)) mu := by
      intro k hk
      rw [hfieldl k hk]
      exact hfields _ (by omega)
    -- the low half
    obtain ⟨low, hlow, hlowb⟩ := and_si256_model field half_mask
    rw [hlow, bind_tc_ok]
    have hlowv : ∀ k < 16, (lane16 low k).toNat
        = streamNat buf (mu * (16 * iter.start.val + k)) half := by
      intro k hk
      have hl : lane16 low k = lane16 field k &&& lane16 half_mask k := by
        show laneOf 16 (bits low) k = _
        rw [hlowb]
        simp only [Model.andSi256]
        exact laneOf_and 16 (bits field) (bits half_mask) k
      rw [hl, toNat_and_mask _ _ half (hmask k hk), hfv k hk,
        Kopis.Properties.streamNat_mod _ _ _ _ (by omega)]
    -- the high half
    apply WP.spec_bind (shift_right_dynamic_spec field halfU (by omega))
    intro sh hshl
    obtain ⟨high, hhigh, hhighb⟩ := and_si256_model sh half_mask
    rw [hhigh, bind_tc_ok]
    have hhighv : ∀ k < 16, (lane16 high k).toNat
        = streamNat buf (mu * (16 * iter.start.val + k) + half) half := by
      intro k hk
      have hl : lane16 high k = lane16 sh k &&& lane16 half_mask k := by
        show laneOf 16 (bits high) k = _
        rw [hhighb]
        simp only [Model.andSi256]
        exact laneOf_and 16 (bits sh) (bits half_mask) k
      rw [hl, toNat_and_mask _ _ half (hmask k hk), hshl k hk, BitVec.toNat_ushiftRight,
        hfv k hk, hhalfU, Kopis.Properties.streamNat_shiftRight _ _ _ _ (by omega),
        Kopis.Properties.streamNat_mod _ _ _ _ (by omega)]
    -- both halves are below 32, so the nibble popcount is valid
    have hbound : ∀ (x : Vec256), (∀ k < 16, ∃ p, (lane16 x k).toNat = streamNat buf p half) →
        ∀ k < 16, (lane16 x k).toNat < 32 := by
      intro x hx k hk
      obtain ⟨p, hp⟩ := hx k hk
      rw [hp]
      exact lt_of_lt_of_le (Kopis.Properties.streamNat_lt _ _ _)
        (by calc (2:ℕ) ^ half ≤ 2 ^ 5 := Nat.pow_le_pow_right (by norm_num) hhalf5
              _ = 32 := by norm_num)
    apply WP.spec_bind (popcount_small_spec low lut hlut
      (hbound low (fun k hk => ⟨_, hlowv k hk⟩)))
    intro pl hpl
    apply WP.spec_bind (popcount_small_spec high lut hlut
      (hbound high (fun k hk => ⟨_, hhighv k hk⟩)))
    intro ph hph
    -- the difference, wrapping
    obtain ⟨coeff, hcoeff, hcoeffb⟩ := sub_epi16_model pl ph
    rw [hcoeff, bind_tc_ok]
    have hcv : ∀ k < 16, (lane16 coeff k).toNat
        = Kopis.Properties.cbdU16 buf half (mu * (16 * iter.start.val + k)) := by
      intro k hk
      have hl : lane16 coeff k = lane16 pl k - lane16 ph k := by
        show laneOf 16 (bits coeff) k = _
        rw [hcoeffb]
        simp only [Model.subEpi16]
        exact laneOf_ofLanes16 _ hk
      rw [hl, BitVec.toNat_sub, hpl k hk, hph k hk, hlowv k hk, hhighv k hk,
        Kopis.Properties.cbdX_eq_bitSum_of_le buf half _ 5 hhalf5,
        Kopis.Properties.cbdX_eq_bitSum_of_le buf half _ 5 hhalf5]
      unfold Kopis.Properties.cbdU16
      have h1 := Kopis.Properties.cbdX_le buf half (mu * (16 * iter.start.val + k))
      have h2 := Kopis.Properties.cbdX_le buf half (mu * (16 * iter.start.val + k) + half)
      have h3 : (2:ℕ) ^ 16 = 65536 := by norm_num
      congr 1
      omega
    -- store, then recurse
    obtain ⟨out1, hout1, hout1v⟩ := store_u16_spec out iter.start coeff (by scalar_tac)
    rw [hout1, bind_tc_ok]
    apply WP.spec_mono (cbd_loop_spec buf mu half hmu hhalf hhalf5 halfU hhalfU fields hfields
      lut half_mask hlut hmask iter1 (by rw [hend']; exact hend) out1)
    intro r hr j hj
    rw [hr j hj]
    by_cases hlow' : j < 16 * iter1.start.val
    · rw [if_pos hlow']
      have hbv : (out1.val[j]!).val = ((out1.val[j]!).bv).toNat := rfl
      rw [hbv, hout1v j hj]
      by_cases hin : 16 * iter.start.val ≤ j ∧ j < 16 * iter.start.val + 16
      · rw [if_pos hin, if_neg (by omega)]
        have hk : j - 16 * iter.start.val < 16 := by omega
        show (lane16 coeff (j - 16 * iter.start.val)).toNat = _
        rw [hcv _ hk]
        congr 2
        omega
      · rw [if_neg hin, if_pos (by omega)]
        rfl
    · rw [if_neg hlow', if_neg (by omega)]
  · let* ⟨ o, iter1, hnone, _ ⟩ ← core.iter.range.IteratorRange.next_Usize_none_spec
    rw [hnone]
    refine (WP.spec_ok _).mpr (fun j hj => ?_)
    rw [if_pos (by omega)]
termination_by iter.«end».val - iter.start.val
decreasing_by scalar_decr_tac

/-! ## The whole sampler

The constants — the nibble table, and the `(1 << MU/2) - 1` half-mask — then the loop.  The
fields come from `ser::deserialize`, so Phase C supplies them. -/

open RustKopisAvx2.backend.avx2.intrinsics in
/-- **The AVX2 sampler computes the centred binomial difference.**  Coefficient `k` is the
popcount of the low `MU/2` bits of its field minus that of the high `MU/2`, as a wrapping
`u16` — exactly what `sample::cbd` documents. -/
theorem cbd_streamNat (buf : Slice U8) (mu half : ℕ) (hmu : mu = 2 * half) (hhalf : 1 ≤ half)
    (hhalf5 : half ≤ 5) (hlen : buf.length = 32 * mu) (MU : Usize) (hMU : MU.val = mu) :
    backend.avx2.sample.cbd MU buf
      ⦃ (r : arithmetic.ring_arith.RingElem) => ∀ j < 256,
          (r.val[j]!).val = Kopis.Properties.cbdU16 buf half (mu * j) ⦄ := by
  have hmu13 : mu ≤ 13 := by omega
  unfold backend.avx2.sample.cbd
  -- the fields: Phase C
  apply WP.spec_bind (deserialize_streamNat buf mu (by omega) hmu13 hlen MU hMU)
  intro fields hfields
  -- the nibble lookup table
  apply WP.spec_bind (WP.exists_imp_spec
    (load_u8_spec backend.avx2.sample.NIBBLE_POPCOUNT 0#usize (by scalar_tac)))
  intro lut hlutl
  have hlutv : ∀ i < 32, (lane8 lut i).toNat = nibblePop i := by
    intro i hi
    rw [hlutl i hi]
    show ((backend.avx2.sample.NIBBLE_POPCOUNT.val[32 * (0#usize).val + i]!) : U8).val = _
    rw [show 32 * (0#usize).val + i = i from by scalar_tac]
    exact nibble_table i hi
  -- half = MU / 2
  let* ⟨ halfU, hhalfU ⟩ ← Std.Usize.div_spec
  have hhalfUv : halfU.val = half := by rw [hhalfU, hMU]; omega
  -- the half-mask `(1 << half) - 1`
  have h2h : 2 ^ half ≤ 32 := by
    calc (2:ℕ) ^ half ≤ 2 ^ 5 := Nat.pow_le_pow_right (by norm_num) hhalf5
      _ = 32 := by norm_num
  have hsz : Std.U16.size = 65536 := by simp [Std.U16.size, Std.U16.numBits]
  let* ⟨ i1, hi1, hi1bv ⟩ ← Std.U16.ShiftLeft_spec
  have hi1v : i1.val = 2 ^ half := by
    rw [hi1, hhalfUv, Nat.shiftLeft_eq, one_mul, hsz, Nat.mod_eq_of_lt (by omega)]
  let* ⟨ i2, hi2 ⟩ ← Std.U16.sub_spec (show (1#u16).val ≤ i1.val by
    rw [hi1v]; exact Nat.one_le_two_pow)
  have hi2v : i2.val = 2 ^ half - 1 := by rw [hi2, hi1v]
  have hi16max : IScalar.max IScalarTy.I16 = 32767 := by
    simp [IScalarTy.numBits, Std.I16.max_eq]
  let* ⟨ i3, hi3 ⟩ ← UScalar.hcast_inBounds_spec .I16 i2 (by rw [hi2v, hi16max]; omega)
  obtain ⟨half_mask, hhm, hhml⟩ := set1_epi16_spec i3
  rw [hhm, bind_tc_ok]
  have hmaskv : ∀ m < 16, (lane16 half_mask m).toNat = 2 ^ half - 1 := by
    intro m hm
    rw [hhml m hm]
    refine iscalar_bv_toNat ?_
    rw [hi3, hi2v]
  -- the zero output, and the trip count
  obtain ⟨out, hout⟩ : ∃ o, arithmetic.ring_arith.RingElem.Insts.CoreDefaultDefault.default
      = ok o := ⟨Array.repeat 256#usize 0#u16, rfl⟩
  rw [hout, bind_tc_ok]
  have hrd : (consts.RING_DEG : Usize) / 16#usize = ok 16#usize := by
    simp only [consts.RING_DEG]; rfl
  rw [hrd, bind_tc_ok]
  -- and the loop
  apply WP.spec_mono (cbd_loop_spec buf mu half hmu hhalf hhalf5 halfU hhalfUv fields hfields
    lut half_mask hlutv hmaskv ⟨0#usize, 16#usize⟩ rfl out)
  intro r hr j hj
  rw [hr j hj, if_neg (by simp)]

end Kopis.Avx2
