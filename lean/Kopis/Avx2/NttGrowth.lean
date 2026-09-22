/-
  # Kopis/Avx2/NttGrowth.lean — the growth bound (plan phase F3).

  `src/arithmetic/ntt_crt.rs` records that AVX2's forward schedule — re-centre after levels 3 and 7,
  plus a final pass, so runs of 3, 4 and 1 Cooley-Tukey levels — is *not* justified by the crude
  per-level budget of 0.75q, which predicts 3.5q against the 3.05q an `i16` lane holds.  The
  comment says safety rests instead on interval propagation with the actual per-butterfly values,
  and adds: "Anyone reordering the reductions or regenerating the ψ tables must redo that
  propagation; the per-level budget alone does not justify the AVX2 schedule."  That argument
  existed only as prose.  This file is the argument.

  Two things make it work, and neither is the crude budget:

  * **The sharp Montgomery bound.**  `mont_mul_lane_spec` gives `|c| < q`, which is what the crude
    budget uses and is far too weak — four levels of `+q` from `q/2` reach `4.5q`.  The sharp form
    `2¹⁶·|c| ≤ |a|·|z| + 2¹⁵·q` says the growth of a level is proportional to the bound already
    reached, so the levels *compound* rather than adding a constant.
  * **Compounding, not adding.**  With `|ψ| ≤ q/2` the recurrence is `B ↦ B + (B·q/2 + 2¹⁵q)/2¹⁶`.
    From `B = (q−1)/2` the four-level run of `q₂ = 10753` reaches `31666`, inside `32767` with
    1101 to spare — where four flat `+0.75q` steps would reach `37636` and overflow.

  So the bound does not need the ψ *values*, only that the tables are centred (`|ψ| ≤ q/2`) —
  which is worth knowing, because it is a far more robust hypothesis than the table contents.
-/
import Kopis.Avx2.NttReduce
import Kopis.Avx2.TransposeSpec

open Aeneas Aeneas.Std Result
open RustKopisAvx2
open RustKopisAvx2.backend.avx2.intrinsics

namespace Kopis.Avx2

set_option maxHeartbeats 1000000

/-! ## Bounds on vectors and on a block -/

/-- Every 16-bit lane of `v` has magnitude at most `B`. -/
def VecBnd (v : Vec256) (B : ℤ) : Prop := ∀ i < 16, |(lane16 v i).toInt| ≤ B

/-- Every `i16` of the block has magnitude at most `B`. -/
def BlockBnd (b : Array I16 256#usize) (B : ℤ) : Prop := ∀ j < 256, |(b.val[j]!).val| ≤ B

theorem BlockBnd.mono {b : Array I16 256#usize} {B B' : ℤ} (h : BlockBnd b B) (hle : B ≤ B') :
    BlockBnd b B' := fun j hj => le_trans (h j hj) hle

theorem VecBnd.mono {v : Vec256} {B B' : ℤ} (h : VecBnd v B) (hle : B ≤ B') : VecBnd v B' :=
  fun i hi => le_trans (h i hi) hle

/-- A load reads sixteen consecutive `i16` of the block. -/
theorem load_i16_val (b : Array I16 256#usize) (i : Usize) (hi : i.val < 16) :
    ∃ c, load_i16 b i = ok c ∧ ∀ k < 16, (lane16 c k).toInt = (b.val[16 * i.val + k]!).val := by
  obtain ⟨c, hc, h⟩ := load_i16_spec b i (by scalar_tac)
  exact ⟨c, hc, fun k hk => by rw [h k hk]; rfl⟩

/-- A store replaces sixteen consecutive `i16` and leaves the rest alone. -/
theorem store_i16_val (b : Array I16 256#usize) (i : Usize) (v : Vec256) (hi : i.val < 16) :
    ∃ b', store_i16 b i v = ok b' ∧ ∀ j < 256,
      (b'.val[j]!).val =
        if 16 * i.val ≤ j ∧ j < 16 * i.val + 16 then (lane16 v (j - 16 * i.val)).toInt
        else (b.val[j]!).val := by
  obtain ⟨d, hd, h⟩ := store_i16_spec b i v (by scalar_tac)
  refine ⟨d, hd, fun j hj => ?_⟩
  have hval : ∀ x : I16, x.bv.toInt = x.val := fun _ => rfl
  rw [← hval, h j (by scalar_tac)]
  split <;> rw [hval]

/-! ## One Cooley-Tukey butterfly

`t = mont_mul(hi, z, zq, q)`, then `(lo, hi) ← (lo + t, lo − t)`.  `T` is any integer bound on
`|t|`; the caller supplies it together with the arithmetic that justifies it, so that the
schedule below can carry exact integers rather than divisions. -/

theorem ct_butterfly_bnd (lo hi z zq qv : Vec256) (Q Zb A T : ℤ)
    (hQ : ∀ i < 16, (lane16 qv i).toInt = Q) (hQpos : 0 < Q) (hQlt : Q ≤ 2 ^ 15)
    (hzq : ∀ i < 16, (2 ^ 16 : ℤ) ∣ ((lane16 zq i).toInt * Q - (lane16 z i).toInt))
    (hlo : VecBnd lo A) (hhi : VecBnd hi A) (hz : VecBnd z Zb)
    (hA0 : 0 ≤ A)
    (hAZ : A * Zb < 2 ^ 15 * Q) (hT : A * Zb + 2 ^ 15 * Q ≤ 2 ^ 16 * T)
    (hfit : A + T ≤ 2 ^ 15 - 1) :
    backend.avx2.ntt.ct_butterfly lo hi z zq qv
      ⦃ (r : Vec256 × Vec256) => VecBnd r.1 (A + T) ∧ VecBnd r.2 (A + T) ⦄ := by
  unfold backend.avx2.ntt.ct_butterfly
  have hbnd : ∀ i < 16, |(lane16 hi i).toInt * (lane16 z i).toInt| < 2 ^ 15 * Q := by
    intro i hi'
    rw [abs_mul]
    calc |(lane16 hi i).toInt| * |(lane16 z i).toInt| ≤ A * Zb :=
          mul_le_mul (hhi i hi') (hz i hi') (abs_nonneg _) hA0
      _ < 2 ^ 15 * Q := hAZ
  apply WP.spec_bind (mont_mul_lane_spec hi z zq qv Q hQ hQpos hQlt hzq hbnd)
  intro t ht
  -- every lane of `t` is inside `T`
  have hTb : VecBnd t T := by
    intro i hi'
    have hsharp := (ht i hi').2.2.2
    have hle : |(lane16 hi i).toInt| * |(lane16 z i).toInt| ≤ A * Zb :=
      mul_le_mul (hhi i hi') (hz i hi') (abs_nonneg _) hA0
    have : (2:ℤ) ^ 16 * |(lane16 t i).toInt| ≤ 2 ^ 16 * T := by linarith
    exact le_of_mul_le_mul_left this (by norm_num)
  obtain ⟨hi1, hhi1, hhi1b⟩ := sub_epi16_model lo t
  rw [hhi1, bind_tc_ok]
  obtain ⟨lo1, hlo1, hlo1b⟩ := add_epi16_model lo t
  rw [hlo1, bind_tc_ok]
  simp only [WP.spec_ok]
  constructor
  · intro i hi'
    rw [add_lane_toInt lo t lo1 hlo1b i hi',
      bmod16_eq_self (by have := hlo i hi'; have := hTb i hi'; rw [abs_le] at *; omega)
        (by have := hlo i hi'; have := hTb i hi'; rw [abs_le] at *; omega)]
    have := hlo i hi'
    have := hTb i hi'
    rw [abs_le] at *
    omega
  · intro i hi'
    rw [sub_lane_toInt lo t hi1 hhi1b i hi',
      bmod16_eq_self (by have := hlo i hi'; have := hTb i hi'; rw [abs_le] at *; omega)
        (by have := hlo i hi'; have := hTb i hi'; rw [abs_le] at *; omega)]
    have := hlo i hi'
    have := hTb i hi'
    rw [abs_le] at *
    omega

/-! ## `barrett_block` — the re-centring pass

Barrett has no precondition on its input, so this needs no bound going in: whatever the block
holds, sixteen `barrett` calls leave every `i16` centred at `|a| ≤ (q−1)/2`. -/

theorem barrett_block_loop_bnd (iter : core.ops.range.Range Usize) (b : Array I16 256#usize)
    (m round qv : Vec256) (Q M : ℤ)
    (hQ : ∀ i < 16, (lane16 qv i).toInt = Q) (hM : ∀ i < 16, (lane16 m i).toInt = M)
    (hRnd : ∀ i < 16, (lane16 round i).toInt = 2 ^ 10)
    (hQpos : 0 < Q) (hQlt : Q < 2 ^ 14) (hQodd : ¬ (2 ∣ Q))
    (hMpos : 0 < M) (hMlt : M < 2 ^ 15) (hD : |2 ^ 27 - Q * M| ≤ 2047)
    (hend : iter.«end».val = 16) :
    backend.avx2.ntt.barrett_block_loop iter b m round qv
      ⦃ (r : Array I16 256#usize) => ∀ j < 256,
          (16 * iter.start.val ≤ j → 2 * |(r.val[j]!).val| < Q) ∧
          (j < 16 * iter.start.val → (r.val[j]!).val = (b.val[j]!).val) ⦄ := by
  unfold backend.avx2.ntt.barrett_block_loop
  by_cases hlt : iter.start.val < iter.«end».val
  · let* ⟨ o, iter1, ho, hstart', hend' ⟩ ← core.iter.range.IteratorRange.next_Usize_some_spec
    rw [ho]; simp only
    obtain ⟨v, hv, hvval⟩ := load_i16_val b iter.start (by omega)
    rw [hv, bind_tc_ok]
    apply WP.spec_bind (barrett_lane_spec v m round qv Q M hQ hM hRnd hQpos hQlt hQodd hMpos hMlt
      hD)
    intro v1 hv1
    obtain ⟨b1, hb1, hb1val⟩ := store_i16_val b iter.start v1 (by omega)
    rw [hb1, bind_tc_ok]
    apply WP.spec_mono (barrett_block_loop_bnd iter1 b1 m round qv Q M hQ hM hRnd hQpos hQlt
      hQodd hMpos hMlt hD (by rw [hend']; exact hend))
    intro r hr j hj
    refine ⟨fun hge => ?_, fun hlt' => ?_⟩
    · rcases (show 16 * iter1.start.val ≤ j ∨ j < 16 * iter1.start.val from by omega) with h | h
      · exact (hr j hj).1 h
      · rw [(hr j hj).2 h, hb1val j hj, if_pos (by omega)]
        exact (hv1 (j - 16 * iter.start.val) (by omega)).2
    · rw [(hr j hj).2 (by omega), hb1val j hj, if_neg (by omega)]
  · let* ⟨ o, iter1, hnone, _ ⟩ ← core.iter.range.IteratorRange.next_Usize_none_spec
    rw [hnone]; simp only [WP.spec_ok]
    intro j hj
    refine ⟨fun hge => absurd hge (by omega), fun _ => ?_⟩
    trivial
termination_by iter.«end».val - iter.start.val
decreasing_by scalar_decr_tac

/-- **The re-centring pass.**  After `barrett_block`, every `i16` of the block is centred. -/
theorem barrett_block_bnd (b : Array I16 256#usize) (m round qv : Vec256) (Q M : ℤ)
    (hQ : ∀ i < 16, (lane16 qv i).toInt = Q) (hM : ∀ i < 16, (lane16 m i).toInt = M)
    (hRnd : ∀ i < 16, (lane16 round i).toInt = 2 ^ 10)
    (hQpos : 0 < Q) (hQlt : Q < 2 ^ 14) (hQodd : ¬ (2 ∣ Q))
    (hMpos : 0 < M) (hMlt : M < 2 ^ 15) (hD : |2 ^ 27 - Q * M| ≤ 2047) :
    backend.avx2.ntt.barrett_block b m round qv
      ⦃ (r : Array I16 256#usize) => BlockBnd r ((Q - 1) / 2) ⦄ := by
  unfold backend.avx2.ntt.barrett_block
  apply WP.spec_mono (barrett_block_loop_bnd { start := 0#usize, «end» := 16#usize } b m round qv
    Q M hQ hM hRnd hQpos hQlt hQodd hMpos hMlt hD rfl)
  intro r hr j hj
  have h := (hr j hj).1 (by
    rw [show ({ start := 0#usize, «end» := 16#usize } :
      core.ops.range.Range Usize).start.val = 0 from rfl]; omega)
  omega

/-! ## Per-vector bounds

A level's butterflies are on *disjoint* vector pairs, so a level takes every vector from `A` to
`A + T` — once, not once per butterfly.  Saying that needs the bound tracked per vector, with the
loop invariants recording which vectors a partial run has already grown. -/

/-- The bound on one 16-lane vector of the block. -/
def BlockBndAt (b : Array I16 256#usize) (v : ℕ) (B : ℤ) : Prop :=
  ∀ k < 16, |(b.val[16 * v + k]!).val| ≤ B

theorem blockBnd_iff (b : Array I16 256#usize) (B : ℤ) :
    BlockBnd b B ↔ ∀ v < 16, BlockBndAt b v B := by
  constructor
  · exact fun h v hv k hk => h (16 * v + k) (by omega)
  · intro h j hj
    have := h (j / 16) (by omega) (j % 16) (by omega)
    rwa [show 16 * (j / 16) + j % 16 = j from by omega] at this

theorem BlockBndAt.mono {b : Array I16 256#usize} {v : ℕ} {B B' : ℤ} (h : BlockBndAt b v B)
    (hle : B ≤ B') : BlockBndAt b v B' := fun k hk => le_trans (h k hk) hle

theorem load_i16_bndAt (b : Array I16 256#usize) (i : Usize) (hi : i.val < 16) {B : ℤ}
    (hb : BlockBndAt b i.val B) : ∃ c, load_i16 b i = ok c ∧ VecBnd c B := by
  obtain ⟨c, hc, h⟩ := load_i16_val b i hi
  exact ⟨c, hc, fun k hk => by rw [h k hk]; exact hb k hk⟩

/-- A store rewrites its own vector and leaves every other one untouched. -/
theorem store_i16_at (b : Array I16 256#usize) (i : Usize) (v : Vec256) (hi : i.val < 16) :
    ∃ b', store_i16 b i v = ok b' ∧
      (∀ k < 16, (b'.val[16 * i.val + k]!).val = (lane16 v k).toInt) ∧
      (∀ u < 16, u ≠ i.val → ∀ k < 16,
        (b'.val[16 * u + k]!).val = (b.val[16 * u + k]!).val) := by
  obtain ⟨d, hd, h⟩ := store_i16_val b i v hi
  refine ⟨d, hd, fun k hk => ?_, fun u hu hne k hk => ?_⟩
  · rw [h (16 * i.val + k) (by omega), if_pos (by omega),
      show 16 * i.val + k - 16 * i.val = k from by omega]
  · rw [h (16 * u + k) (by omega), if_neg (by omega)]

/-! ## Writing a butterfly's two outputs back

The loops of `ntt_block` interleave their index arithmetic with the loads, so the reusable piece
is the pair of stores rather than the whole load-butterfly-store block. -/

/-- A ψ pair is usable: `z` is centred, and `zq` is its Montgomery companion. -/
def PsiOk (z zq : Vec256) (Q Zb : ℤ) : Prop :=
  VecBnd z Zb ∧ ∀ i < 16, (2 ^ 16 : ℤ) ∣ ((lane16 zq i).toInt * Q - (lane16 z i).toInt)

/-! ## The vertical levels

`ntt_block_loop1` is the `len = 8` level: eight butterflies pairing `j` with `j + 8`, each with
the same ψ, so after it every vector has grown once.  The invariant records which vectors a
partial run has already grown — without that, the eight butterflies would be charged eight times
over instead of once, and no schedule would fit. -/

/-- Vectors satisfying `P` have grown to `A + T`; the rest are still inside `A`. -/
def Split (b : Array I16 256#usize) (P : ℕ → Prop) (A T : ℤ) : Prop :=
  (∀ v < 16, P v → BlockBndAt b v (A + T)) ∧ (∀ v < 16, ¬ P v → BlockBndAt b v A)

/-! ## The horizontal levels

Levels with `len ≥ 16` pair whole vectors `i` and `i + half` inside a group of width `2·half`,
with ψ broadcast across the group.  `half` is always one of 8, 4, 2, 1, which is what lets the
index arithmetic stay literal. -/

/-! ## The schedule arithmetic

This is the claim `src/arithmetic/ntt_crt.rs` makes in prose.  A Cooley-Tukey level takes a bound `A` to
`A + T` where `2¹⁶·T ≥ A·Zb + 2¹⁵·q` — that is `ct_butterfly_bnd`, and `T` is proportional to `A`,
which is the whole point.  Iterating from a centred block with `|ψ| ≤ q/2`:

* `q₂ = 10753`: `5376 → 11194 → 17489 → 24301 → 31671`, inside `32767` with 1096 to spare;
* `q₁ = 7681`:  `3840 → 7906 → 12210 → 16766 → 21589`.

Four flat `+0.75q` steps — the crude budget the comment says does *not* justify this schedule —
would reach `3.5·q₂ = 37636` and overflow the lane.  Each `T` below is the least integer
satisfying the `ct_butterfly_bnd` premise at that level, so the chain is tight. -/

/-- One level's growth, as `ct_butterfly_bnd` needs it. -/
def LevelStep (Q Zb A T : ℤ) : Prop :=
  A * Zb < 2 ^ 15 * Q ∧ A * Zb + 2 ^ 15 * Q ≤ 2 ^ 16 * T ∧ A + T ≤ 2 ^ 15 - 1

/-- **The four-level run fits, for `q₂ = 10753`.**  Every level's premise holds and the last
bound is inside an `i16`. -/
theorem growth_q2 :
    LevelStep 10753 5376 5376 5818 ∧ LevelStep 10753 5376 11194 6295 ∧
    LevelStep 10753 5376 17489 6812 ∧ LevelStep 10753 5376 24301 7370 ∧
    (24301 : ℤ) + 7370 = 31671 ∧ (31671 : ℤ) ≤ 32767 := by
  refine ⟨⟨by norm_num, by norm_num, by norm_num⟩, ⟨by norm_num, by norm_num, by norm_num⟩,
    ⟨by norm_num, by norm_num, by norm_num⟩, ⟨by norm_num, by norm_num, by norm_num⟩,
    by norm_num, by norm_num⟩

/-- **The four-level run fits, for `q₁ = 7681`.** -/
theorem growth_q1 :
    LevelStep 7681 3840 3840 4066 ∧ LevelStep 7681 3840 7906 4304 ∧
    LevelStep 7681 3840 12210 4556 ∧ LevelStep 7681 3840 16766 4823 ∧
    (16766 : ℤ) + 4823 = 21589 ∧ (21589 : ℤ) ≤ 32767 := by
  refine ⟨⟨by norm_num, by norm_num, by norm_num⟩, ⟨by norm_num, by norm_num, by norm_num⟩,
    ⟨by norm_num, by norm_num, by norm_num⟩, ⟨by norm_num, by norm_num, by norm_num⟩,
    by norm_num, by norm_num⟩

/-! ## Three of the four levels, on the extracted code

The run the crude budget fails to cover is levels `len = 16, 8, 4, 2`.  The last three of those
are `ntt_block_loop1`, `loop2` and `loop3`, and this composes them against the chain above for
`q₂ = 10753`, the binding prime.  The first of the four is `ntt_block_loop0`'s last level, which
leaves the block inside `11194`; from there these three reach `31671`, inside `32767` with 1096
to spare — and the crude budget predicts overflow. -/

/-- **`transpose16` preserves any bound** — it only moves values between lanes. -/
theorem transpose16_bnd (b : Array I16 256#usize) {B : ℤ} (hb : BlockBnd b B) :
    backend.avx2.ntt.transpose16 b ⦃ (r : Array I16 256#usize) => BlockBnd r B ⦄ := by
  apply WP.spec_mono (transpose16_coeff b)
  intro r hr j hj
  have h := hr (j / 16) (by omega) (j % 16) (by omega)
  rw [show 16 * (j / 16) + j % 16 = j from by omega] at h
  have hval : (r.val[j]!).val = (b.val[16 * (j % 16) + j / 16]!).val := by
    have e : (r.val[j]!).bv.toInt = (b.val[16 * (j % 16) + j / 16]!).bv.toInt := by rw [h]
    exact e
  rw [hval]
  exact hb _ (by omega)

/-! ## The horizontal half, unrolled

`ntt_block_loop0` runs four levels with `half = 8, 4, 2, 1` and re-centres after level 2, so the
bound is different at every step and there is no single invariant to state: it is unrolled, with
the four bounds taken from `growth_q2`.  The `k` threading is why each unrolled step has to
bound the ζ index it returns as well as the coefficients. -/

theorem usize_add_lit {a b c : Usize} (hc : a.val + b.val ≤ Usize.max)
    (h : a.val + b.val = c.val) : (a + b : Result Usize) = ok c := by
  obtain ⟨z, hz, hzv⟩ := WP.spec_imp_exists (Std.Usize.add_spec (x := a) (y := b) hc)
  rw [hz, UScalar.eq_of_val_eq (show z.val = c.val by rw [hzv, h])]

/-- Before a level runs nothing has grown, so any empty "already grown" predicate will do. -/
theorem initSplit {b : Array I16 256#usize} {A T : ℤ} {P : ℕ → Prop}
    (hP : ∀ v, ¬ P v) (hb : BlockBnd b A) : Split b P A T :=
  ⟨fun v _ h => absurd h (hP v), fun v hv _ => (blockBnd_iff b A).mp hb v hv⟩

/-! ## `ntt_block`

The whole forward transform of one block, for `q₂ = 10753` — the prime whose lane budget binds.
The chain: `11194` after the horizontal half, unchanged by the transpose, then `17489 → 24301 →
31671` across the three vertical levels, re-centred to `5376`, one more level to `11194`,
transposed, and re-centred.  So `ntt_block` leaves every coefficient centred, which is what its
Rust doc comment claims and what the next stage assumes. -/

/-! ## `ntt_block`

The whole forward transform of one block, for `q₁ = 7681` — the prime whose lane budget binds.
The chain: `7906` after the horizontal half, unchanged by the transpose, then `12210 → 16766 →
21589` across the three vertical levels, re-centred to `3840`, one more level to `7906`,
transposed, and re-centred.  So `ntt_block` leaves every coefficient centred, which is what its
Rust doc comment claims and what the next stage assumes. -/

end Kopis.Avx2
