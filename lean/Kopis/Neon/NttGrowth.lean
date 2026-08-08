/-
  # Kopis/Neon/NttGrowth.lean — how big a lane gets (plan phase F3).

  `src/backend/neon/ntt.rs` re-centres the forward transform after levels 3 and 7 — two runs of
  four Cooley-Tukey levels — and the inverse after levels 2, 4 and 6.  Both reductions of the
  forward transform now happen to a group that is already in registers, so there is no
  whole-block pass left to state.

  A four-level run does *not* fit the crude 0.75q-per-level budget in `crate::backend::crt`, and
  that is the point of stating the growth of a butterfly in the *compounding* form the sharp
  Montgomery bound gives — `2¹⁶·|t| ≤ B·Zb + 2¹⁵·q`.  A level maps `|a|` to
  `|a|·(1 + q/2^17) + q/2` rather than to `|a| + 0.75q`, so from a centered start four levels
  reach 2.95q of the 3.05q an `i16` lane holds for `q₂ = 10753`.  `Kopis/Avx2/NttGrowth.lean`
  still does not port — AVX2's bound is table-dependent where this one is not — but the *shape*
  of the argument is now the same on both backends, and for the same reason.

  This file states that growth once and leaves the arithmetic of instantiating it to the caller.

  What is here: the bound predicates, the load/store bridge between a block and its vectors, and
  the Montgomery and butterfly bounds.  The re-centring pass itself is a loop over the eight
  vectors of a group, and lives with the group loop in `Kopis/Neon/NttBarrettIter.lean`.
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

/-- Every `i16` of the 256-coefficient residue block that starts at vector `base` of `b` has
magnitude at most `B`.

The forward transform runs in place inside a larger buffer — `split_and_transform` hands
`ntt_block` the whole `[i16; 512]` and the vector index its prime's half starts at — so its
statements are about a window, not about a whole array.  `BlockBnd` is the `base = 0`,
`N = 256` case and is what the inverse transform, which still owns a block outright, uses. -/
def BlockBndAt {N : Usize} (b : Array I16 N) (base : ℕ) (B : ℤ) : Prop :=
  ∀ j < 256, |(b.val[8 * base + j]!).val| ≤ B

theorem VecBnd.mono {v : Vec128} {B B' : ℤ} (h : VecBnd v B) (hle : B ≤ B') : VecBnd v B' :=
  fun i hi => le_trans (h i hi) hle

theorem BlockBnd.mono {b : Array I16 256#usize} {B B' : ℤ} (h : BlockBnd b B) (hle : B ≤ B') :
    BlockBnd b B' := fun j hj => le_trans (h j hj) hle

theorem BlockBndAt.mono {N : Usize} {b : Array I16 N} {base : ℕ} {B B' : ℤ}
    (h : BlockBndAt b base B) (hle : B ≤ B') : BlockBndAt b base B' :=
  fun j hj => le_trans (h j hj) hle

/-! ## A block and its thirty-two vectors

`load_i16 b i` reads `b[8i .. 8i+8]` and `store_i16 b i v` writes it back; everything below moves
between the two views through these.  Both are stated for an arbitrary array length, because the
forward transform's window sits inside a longer buffer; `load_i16_val` / `store_i16_val` are the
whole-block instances the inverse transform uses. -/

/-- A load reads eight consecutive `i16` of the array. -/
theorem load_i16_gen {N : Usize} (b : Array I16 N) (i : Usize) (hi : 8 * i.val + 8 ≤ N.val) :
    ∃ c, load_i16 b i = ok c ∧ ∀ k < 8, (lane16 c k).toInt = (b.val[8 * i.val + k]!).val := by
  obtain ⟨c, hc, h⟩ := load_i16_spec b i (by omega)
  exact ⟨c, hc, fun k hk => by rw [h k hk]; rfl⟩

/-- A store replaces eight consecutive `i16` and leaves the rest of the array alone. -/
theorem store_i16_gen {N : Usize} (b : Array I16 N) (i : Usize) (v : Vec128)
    (hi : 8 * i.val + 8 ≤ N.val) :
    ∃ b', store_i16 b i v = ok b' ∧ ∀ j < N.val,
      (b'.val[j]!).val =
        if 8 * i.val ≤ j ∧ j < 8 * i.val + 8 then (lane16 v (j - 8 * i.val)).toInt
        else (b.val[j]!).val := by
  obtain ⟨b', hb', h⟩ := store_i16_spec b i v (by omega)
  refine ⟨b', hb', fun j hj => ?_⟩
  have hj' := h j hj
  show ((b'.val[j]!) : I16).bv.toInt = _
  rw [hj']
  split <;> rfl

/-- A load reads eight consecutive `i16` of the block. -/
theorem load_i16_val (b : Array I16 256#usize) (i : Usize) (hi : i.val < 32) :
    ∃ c, load_i16 b i = ok c ∧ ∀ k < 8, (lane16 c k).toInt = (b.val[8 * i.val + k]!).val :=
  load_i16_gen b i (by scalar_tac)

/-- A store replaces eight consecutive `i16` and leaves the rest alone. -/
theorem store_i16_val (b : Array I16 256#usize) (i : Usize) (v : Vec128) (hi : i.val < 32) :
    ∃ b', store_i16 b i v = ok b' ∧ ∀ j < 256,
      (b'.val[j]!).val =
        if 8 * i.val ≤ j ∧ j < 8 * i.val + 8 then (lane16 v (j - 8 * i.val)).toInt
        else (b.val[j]!).val := by
  obtain ⟨b', hb', h⟩ := store_i16_gen b i v (by scalar_tac)
  exact ⟨b', hb', fun j hj => h j (by scalar_tac)⟩

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

end Kopis.Neon
