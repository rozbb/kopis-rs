/-
  # Kopis/Neon/NttGrowth.lean — how big a lane gets (plan phase F3).

  `src/backend/neon/ntt.rs` re-centres after forward levels 3 and 6 plus a final pass — runs of
  3, 3 and 2 Cooley-Tukey levels — and says so:

  > which the crude 0.75q-per-level budget in `crate::backend::crt` covers … Note this forward
  > schedule does *not* match AVX2's, which re-centers after levels 3 and 7 and rests on a
  > sharper, table-dependent bound — growth bounds do not transfer between the two backends.

  `NEON_VERIFICATION_PLAN.md` §2(c) says the same thing from the other side: this is *easier* to
  mechanize than AVX2's phase F3, and `Kopis/Avx2/NttGrowth.lean` does not port.  It does not
  port because AVX2's four-level run needs the growth of a level to be shown proportional to the
  bound already reached — the levels compound, and four flat `+0.75q` steps would overflow.  A
  three-level run does not need that: three flat steps from `q/2` reach `2.75q`, inside the
  `3.05q` an `i16` lane holds for `q₂ = 10753`, with room to spare.

  So this file states the growth of one butterfly, once, in the *compounding* form the sharp
  Montgomery bound gives — `2¹⁶·|t| ≤ B·Zb + 2¹⁵·q` — and leaves the arithmetic of instantiating
  it to the caller.  That form is strictly stronger than the crude budget and costs nothing extra
  to state, so the file does not commit to which of the two the schedule is checked against; §F3
  of the plan says the crude one suffices here, and the numbers above are why.

  What is here: the two bound predicates, the load/store bridge between a block and its vectors,
  the Montgomery and butterfly bounds, and `barrett_block`, which is what re-centres a whole
  block to `|r| < q/2` between runs.
-/
import Kopis.Neon.NttReduce

open Aeneas Aeneas.Std Result
open RustKopisNeon
open RustKopisNeon.backend.neon.intrinsics

namespace Kopis.Neon

set_option maxHeartbeats 1000000

/-! ## Bounds on vectors and on a block -/

/-- Every 16-bit lane of `v` has magnitude at most `B`. -/
def VecBnd (v : Vec128) (B : ℤ) : Prop := ∀ i < 8, |(lane16 v i).toInt| ≤ B

/-- Every `i16` of the block has magnitude at most `B`. -/
def BlockBnd (b : Array I16 256#usize) (B : ℤ) : Prop := ∀ j < 256, |(b.val[j]!).val| ≤ B

theorem VecBnd.mono {v : Vec128} {B B' : ℤ} (h : VecBnd v B) (hle : B ≤ B') : VecBnd v B' :=
  fun i hi => le_trans (h i hi) hle

theorem BlockBnd.mono {b : Array I16 256#usize} {B B' : ℤ} (h : BlockBnd b B) (hle : B ≤ B') :
    BlockBnd b B' := fun j hj => le_trans (h j hj) hle

/-! ## A block and its thirty-two vectors

`load_i16 b i` reads `b[8i .. 8i+8]` and `store_i16 b i v` writes it back; everything below moves
between the two views through these. -/

/-- A load reads eight consecutive `i16` of the block. -/
theorem load_i16_val (b : Array I16 256#usize) (i : Usize) (hi : i.val < 32) :
    ∃ c, load_i16 b i = ok c ∧ ∀ k < 8, (lane16 c k).toInt = (b.val[8 * i.val + k]!).val := by
  obtain ⟨c, hc, h⟩ := load_i16_spec b i (by scalar_tac)
  exact ⟨c, hc, fun k hk => by rw [h k hk]; rfl⟩

/-- A store replaces eight consecutive `i16` and leaves the rest alone. -/
theorem store_i16_val (b : Array I16 256#usize) (i : Usize) (v : Vec128) (hi : i.val < 32) :
    ∃ b', store_i16 b i v = ok b' ∧ ∀ j < 256,
      (b'.val[j]!).val =
        if 8 * i.val ≤ j ∧ j < 8 * i.val + 8 then (lane16 v (j - 8 * i.val)).toInt
        else (b.val[j]!).val := by
  obtain ⟨b', hb', h⟩ := store_i16_spec b i v (by scalar_tac)
  refine ⟨b', hb', fun j hj => ?_⟩
  have hj' := h j (by scalar_tac)
  show ((b'.val[j]!) : I16).bv.toInt = _
  rw [hj']
  split <;> rfl

/-! ## The Montgomery multiply, as a bound

`mont_mul_lane_spec`'s sharp conjunct, packaged so a butterfly can consume it: if every input
lane is at most `B` and every twiddle at most `Zb`, the product is at most `Bt` for any `Bt` with
`2¹⁶·Bt ≥ B·Zb + 2¹⁵·q`.  Note what the bound is proportional to — `B`, not a constant — which is
the whole reason a four-level run is possible on AVX2 and why three is comfortable here. -/

theorem mont_mul_bnd (a z zq qv : Vec128) (Q Zb B Bt : ℤ)
    (hQ : ∀ i < 8, (lane16 qv i).toInt = Q) (hQpos : 0 < Q) (hQlt : Q ≤ 2 ^ 14)
    (hz : ∀ i < 8, |(lane16 z i).toInt| ≤ Zb) (hZb : Zb ≤ 2 ^ 14)
    (hzq : ∀ i < 8, (2 ^ 16 : ℤ) ∣ ((lane16 zq i).toInt * Q - (lane16 z i).toInt))
    (hA : VecBnd a B) (hB0 : 0 ≤ B) (hBZ : B * Zb < 2 ^ 15 * Q)
    (hBt : B * Zb + 2 ^ 15 * Q ≤ 2 ^ 16 * Bt) :
    backend.neon.ntt.mont_mul a z zq qv
      ⦃ (c : Vec128) => VecBnd c Bt ∧ ∀ i < 8,
          Q ∣ ((lane16 c i).toInt * 2 ^ 16 - (lane16 a i).toInt * (lane16 z i).toInt) ⦄ := by
  have hZb0 : ∀ i < 8, 0 ≤ |(lane16 z i).toInt| := fun i _ => abs_nonneg _
  have hprod : ∀ i < 8, |(lane16 a i).toInt * (lane16 z i).toInt| < 2 ^ 15 * Q := by
    intro i hi
    rw [abs_mul]
    have h1 := hA i hi
    have h2 := hz i hi
    nlinarith [abs_nonneg (lane16 a i).toInt, abs_nonneg (lane16 z i).toInt]
  apply WP.spec_mono (mont_mul_lane_spec a z zq qv Q hQ hQpos (by omega)
    (fun i hi => by have := hz i hi; have := abs_le.mp this; omega) hzq hprod)
  intro c hc
  refine ⟨fun i hi => ?_, fun i hi => (hc i hi).1⟩
  obtain ⟨-, -, -, hsharp⟩ := hc i hi
  have h1 := hA i hi
  have h2 := hz i hi
  have hmul : |(lane16 a i).toInt| * |(lane16 z i).toInt| ≤ B * Zb := by
    nlinarith [abs_nonneg (lane16 a i).toInt, abs_nonneg (lane16 z i).toInt]
  nlinarith [abs_nonneg (lane16 c i).toInt]

/-! ## The two butterflies, as bounds

A Cooley-Tukey level adds the Montgomery product to a bound already reached; a Gentleman-Sande
level doubles first and multiplies after.  Both need the sums to stay inside an `i16`, which is
the `hfit` hypothesis and the thing the reduction schedule exists to maintain. -/

theorem ct_butterfly_bnd (lo hi z zq qv : Vec128) (Q Zb B Bt : ℤ)
    (hQ : ∀ i < 8, (lane16 qv i).toInt = Q) (hQpos : 0 < Q) (hQlt : Q ≤ 2 ^ 14)
    (hz : ∀ i < 8, |(lane16 z i).toInt| ≤ Zb) (hZb : Zb ≤ 2 ^ 14)
    (hzq : ∀ i < 8, (2 ^ 16 : ℤ) ∣ ((lane16 zq i).toInt * Q - (lane16 z i).toInt))
    (hlo : VecBnd lo B) (hhi : VecBnd hi B) (hB0 : 0 ≤ B)
    (hBZ : B * Zb < 2 ^ 15 * Q) (hBt : B * Zb + 2 ^ 15 * Q ≤ 2 ^ 16 * Bt) (_hBt0 : 0 ≤ Bt)
    (hfit : B + Bt ≤ 32767) :
    backend.neon.ntt.ct_butterfly lo hi z zq qv
      ⦃ (r : Vec128 × Vec128) => VecBnd r.1 (B + Bt) ∧ VecBnd r.2 (B + Bt) ⦄ := by
  unfold backend.neon.ntt.ct_butterfly
  apply WP.spec_bind (mont_mul_bnd hi z zq qv Q Zb B Bt hQ hQpos hQlt hz hZb hzq hhi hB0 hBZ hBt)
  rintro t ⟨htb, -⟩
  obtain ⟨hi1, hhi1, hhi1b⟩ := sub_16_model lo t
  rw [hhi1, bind_tc_ok]
  obtain ⟨lo1, hlo1, hlo1b⟩ := add_16_model lo t
  rw [hlo1, bind_tc_ok]
  refine (WP.spec_ok _).mpr ⟨?_, ?_⟩
  · intro i hi'
    have hl := hlo i hi'
    have ht := htb i hi'
    have hv := add_lane_toInt lo t lo1 hlo1b i hi'
    rw [hv, bmod16_eq_self (by rw [abs_le] at hl ht; omega) (by rw [abs_le] at hl ht; omega)]
    rw [abs_le] at hl ht ⊢
    omega
  · intro i hi'
    have hl := hlo i hi'
    have ht := htb i hi'
    have hv := sub_lane_toInt lo t hi1 hhi1b i hi'
    rw [hv, bmod16_eq_self (by rw [abs_le] at hl ht; omega) (by rw [abs_le] at hl ht; omega)]
    rw [abs_le] at hl ht ⊢
    omega

theorem gs_butterfly_bnd (lo hi z zq qv : Vec128) (Q Zb B Bt : ℤ)
    (hQ : ∀ i < 8, (lane16 qv i).toInt = Q) (hQpos : 0 < Q) (hQlt : Q ≤ 2 ^ 14)
    (hz : ∀ i < 8, |(lane16 z i).toInt| ≤ Zb) (hZb : Zb ≤ 2 ^ 14)
    (hzq : ∀ i < 8, (2 ^ 16 : ℤ) ∣ ((lane16 zq i).toInt * Q - (lane16 z i).toInt))
    (hlo : VecBnd lo B) (hhi : VecBnd hi B) (hB0 : 0 ≤ B)
    (hBZ : 2 * B * Zb < 2 ^ 15 * Q) (hBt : 2 * B * Zb + 2 ^ 15 * Q ≤ 2 ^ 16 * Bt)
    (hfit : 2 * B ≤ 32767) :
    backend.neon.ntt.gs_butterfly lo hi z zq qv
      ⦃ (r : Vec128 × Vec128) => VecBnd r.1 (2 * B) ∧ VecBnd r.2 Bt ⦄ := by
  unfold backend.neon.ntt.gs_butterfly
  obtain ⟨diff, hdiff, hdiffb⟩ := sub_16_model lo hi
  rw [hdiff, bind_tc_ok]
  obtain ⟨lo1, hlo1, hlo1b⟩ := add_16_model lo hi
  rw [hlo1, bind_tc_ok]
  have hdb : VecBnd diff (2 * B) := by
    intro i hi'
    have hl := hlo i hi'
    have hh := hhi i hi'
    have hv := sub_lane_toInt lo hi diff hdiffb i hi'
    rw [hv, bmod16_eq_self (by rw [abs_le] at hl hh; omega) (by rw [abs_le] at hl hh; omega)]
    rw [abs_le] at hl hh ⊢
    omega
  have hlb : VecBnd lo1 (2 * B) := by
    intro i hi'
    have hl := hlo i hi'
    have hh := hhi i hi'
    have hv := add_lane_toInt lo hi lo1 hlo1b i hi'
    rw [hv, bmod16_eq_self (by rw [abs_le] at hl hh; omega) (by rw [abs_le] at hl hh; omega)]
    rw [abs_le] at hl hh ⊢
    omega
  apply WP.spec_bind (mont_mul_bnd diff z zq qv Q Zb (2 * B) Bt hQ hQpos hQlt hz hZb hzq hdb
    (by omega) hBZ hBt)
  rintro t ⟨htb, -⟩
  exact (WP.spec_ok _).mpr ⟨hlb, htb⟩

/-! ## `barrett_block`

The pass that re-centres a whole block between runs of levels.  After it, every `i16` of the
block is congruent to what it was mod `q` and strictly inside `±q/2` — which is the state the
next run of Cooley-Tukey levels starts from, and hence the `B = (q−1)/2` the schedule is checked
against. -/

theorem barrett_block_loop_spec (b : Array I16 256#usize) (m round qv : Vec128) (Q M : ℤ)
    (hQ : ∀ i < 8, (lane16 qv i).toInt = Q) (hM : ∀ i < 8, (lane16 m i).toInt = M)
    (hRnd : ∀ i < 8, (lane16 round i).toInt = 2 ^ 10)
    (hQpos : 0 < Q) (hQlt : Q < 2 ^ 14) (hQodd : ¬ (2 ∣ Q))
    (hMpos : 0 < M) (hMlt : M < 2 ^ 15) (hD : |2 ^ 27 - Q * M| ≤ 2047)
    (iter : core.ops.range.Range Usize) (hend : iter.«end».val = 32) :
    backend.neon.ntt.barrett_block_loop iter b m round qv
      ⦃ (r : Array I16 256#usize) => ∀ j < 256,
          if j < 8 * iter.start.val then (r.val[j]!).val = (b.val[j]!).val
          else Q ∣ ((r.val[j]!).val - (b.val[j]!).val) ∧ 2 * |(r.val[j]!).val| < Q ⦄ := by
  unfold backend.neon.ntt.barrett_block_loop
  by_cases hlt : iter.start.val < iter.«end».val
  · let* ⟨ o, iter1, ho, hstart', hend' ⟩ ← core.iter.range.IteratorRange.next_Usize_some_spec
    rw [ho]
    simp only
    have hi32 : iter.start.val < 32 := by omega
    obtain ⟨vec, hvec, hvecl⟩ := load_i16_val b iter.start hi32
    rw [hvec, bind_tc_ok]
    apply WP.spec_bind (barrett_lane_spec vec m round qv Q M hQ hM hRnd hQpos hQlt hQodd hMpos
      hMlt hD)
    intro red hred
    obtain ⟨b1, hb1, hb1v⟩ := store_i16_val b iter.start red hi32
    rw [hb1, bind_tc_ok]
    apply WP.spec_mono (barrett_block_loop_spec b1 m round qv Q M hQ hM hRnd hQpos hQlt hQodd
      hMpos hMlt hD iter1 (by rw [hend']; exact hend))
    intro r hr j hj
    have hrj := hr j hj
    by_cases hg : j < 8 * iter.start.val
    · rw [if_pos hg]
      rw [if_pos (by omega)] at hrj
      rw [hrj, hb1v j hj, if_neg (by omega)]
    · rw [if_neg hg]
      by_cases hin : j < 8 * iter1.start.val
      · rw [if_pos hin] at hrj
        rw [hrj, hb1v j hj, if_pos (by omega)]
        have hk : j - 8 * iter.start.val < 8 := by omega
        obtain ⟨hdvd, hbnd⟩ := hred (j - 8 * iter.start.val) hk
        rw [hvecl _ hk, show 8 * iter.start.val + (j - 8 * iter.start.val) = j from by omega]
          at hdvd
        exact ⟨hdvd, hbnd⟩
      · rw [if_neg hin] at hrj
        rw [hb1v j hj, if_neg (by omega)] at hrj
        exact hrj
  · let* ⟨ o, iter1, hnone, _ ⟩ ← core.iter.range.IteratorRange.next_Usize_none_spec
    rw [hnone]
    refine (WP.spec_ok _).mpr (fun j hj => ?_)
    rw [if_pos (by omega)]
termination_by iter.«end».val - iter.start.val
decreasing_by scalar_decr_tac

/-- **`barrett_block` re-centres a block.**  Every coefficient keeps its residue mod `q` and ends
strictly inside `±q/2`. -/
theorem barrett_block_spec (b : Array I16 256#usize) (m round qv : Vec128) (Q M : ℤ)
    (hQ : ∀ i < 8, (lane16 qv i).toInt = Q) (hM : ∀ i < 8, (lane16 m i).toInt = M)
    (hRnd : ∀ i < 8, (lane16 round i).toInt = 2 ^ 10)
    (hQpos : 0 < Q) (hQlt : Q < 2 ^ 14) (hQodd : ¬ (2 ∣ Q))
    (hMpos : 0 < M) (hMlt : M < 2 ^ 15) (hD : |2 ^ 27 - Q * M| ≤ 2047) :
    backend.neon.ntt.barrett_block b m round qv
      ⦃ (r : Array I16 256#usize) => BlockBnd r ((Q - 1) / 2) ∧ ∀ j < 256,
          Q ∣ ((r.val[j]!).val - (b.val[j]!).val) ⦄ := by
  unfold backend.neon.ntt.barrett_block
  have hvecs : backend.neon.ntt.VECS = ok 32#usize := by
    simp only [backend.neon.ntt.VECS, consts.RING_DEG]; rfl
  rw [hvecs, bind_tc_ok]
  apply WP.spec_mono (barrett_block_loop_spec b m round qv Q M hQ hM hRnd hQpos hQlt hQodd hMpos
    hMlt hD ⟨0#usize, 32#usize⟩ rfl)
  intro r hr
  constructor
  · intro j hj
    have := hr j hj
    rw [if_neg (by simp)] at this
    obtain ⟨-, hb⟩ := this
    omega
  · intro j hj
    have := hr j hj
    rw [if_neg (by simp)] at this
    exact this.1

end Kopis.Neon
