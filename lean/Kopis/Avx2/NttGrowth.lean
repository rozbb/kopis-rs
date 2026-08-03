/-
  # Kopis/Avx2/NttGrowth.lean — the growth bound (plan phase F3).

  `src/backend/crt.rs` records that AVX2's forward schedule — re-centre after levels 3 and 7,
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

/-- Loading a vector out of a bounded block gives a bounded vector. -/
theorem load_i16_bnd (b : Array I16 256#usize) (i : Usize) (hi : i.val < 16) {B : ℤ}
    (hb : BlockBnd b B) : ∃ c, load_i16 b i = ok c ∧ VecBnd c B := by
  obtain ⟨c, hc, h⟩ := load_i16_val b i hi
  exact ⟨c, hc, fun k hk => by rw [h k hk]; exact hb (16 * i.val + k) (by omega)⟩

/-- Storing a bounded vector into a bounded block keeps the block bounded. -/
theorem store_i16_bnd (b : Array I16 256#usize) (i : Usize) (v : Vec256) (hi : i.val < 16)
    {B : ℤ} (hb : BlockBnd b B) (hv : VecBnd v B) :
    ∃ b', store_i16 b i v = ok b' ∧ BlockBnd b' B := by
  obtain ⟨d, hd, h⟩ := store_i16_val b i v hi
  refine ⟨d, hd, fun j hj => ?_⟩
  rw [h j hj]
  split
  · exact hv (j - 16 * i.val) (by omega)
  · exact hb j hj

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

theorem store_pair_bnd (b : Array I16 256#usize) (u1 u2 : Usize) (lo1 hi1 : Vec256) (B : ℤ)
    (hu1 : u1.val < 16) (hu2 : u2.val < 16) (hne : u1.val ≠ u2.val)
    (hlo : VecBnd lo1 B) (hhi : VecBnd hi1 B) :
    (do let b1 ← store_i16 b u1 lo1
        store_i16 b1 u2 hi1)
      ⦃ (r : Array I16 256#usize) =>
          BlockBndAt r u1.val B ∧ BlockBndAt r u2.val B ∧
          ∀ u < 16, u ≠ u1.val → u ≠ u2.val → ∀ k < 16,
            (r.val[16 * u + k]!).val = (b.val[16 * u + k]!).val ⦄ := by
  obtain ⟨b1, hb1, hb1at, hb1oth⟩ := store_i16_at b u1 lo1 hu1
  rw [hb1, bind_tc_ok]
  obtain ⟨b2, hb2, hb2at, hb2oth⟩ := store_i16_at b1 u2 hi1 hu2
  rw [hb2]
  simp only [WP.spec_ok]
  refine ⟨fun k hk => ?_, fun k hk => ?_, fun u hu hnu1 hnu2 k hk => ?_⟩
  · rw [hb2oth u1.val hu1 hne k hk, hb1at k hk]
    exact hlo k hk
  · rw [hb2at k hk]
    exact hhi k hk
  · rw [hb2oth u hu hnu2 k hk, hb1oth u hu hnu1 k hk]

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

theorem ntt_block_loop1_bnd (SECOND : Bool) (iter : core.ops.range.Range Usize)
    (b : Array I16 256#usize) (qv : Vec256) (Q Zb A T : ℤ)
    (hQ : ∀ i < 16, (lane16 qv i).toInt = Q) (hQpos : 0 < Q) (hQlt : Q ≤ 2 ^ 15)
    (hA0 : 0 ≤ A) (hT0 : 0 ≤ T)
    (hAZ : A * Zb < 2 ^ 15 * Q) (hT : A * Zb + 2 ^ 15 * Q ≤ 2 ^ 16 * T)
    (hfit : A + T ≤ 2 ^ 15 - 1)
    (htbl : ∃ z zq,
      (if SECOND then (do let t ← backend.avx2.ntt.FWD8_Q2; backend.avx2.ntt.ld_tbl t 0#usize)
       else (do let t ← backend.avx2.ntt.FWD8_Q1; backend.avx2.ntt.ld_tbl t 0#usize))
        = ok (z, zq) ∧ PsiOk z zq Q Zb)
    (hend : iter.«end».val = 8)
    (hsplit : Split b (fun v => v < iter.start.val ∨ (8 ≤ v ∧ v < 8 + iter.start.val)) A T) :
    backend.avx2.ntt.ntt_block_loop1 SECOND iter b qv
      ⦃ (r : Array I16 256#usize) => BlockBnd r (A + T) ⦄ := by
  unfold backend.avx2.ntt.ntt_block_loop1
  obtain ⟨z, zq, htz, hzb, hzqm⟩ := htbl
  by_cases hlt : iter.start.val < iter.«end».val
  · let* ⟨ o, iter1, ho, hstart', hend' ⟩ ← core.iter.range.IteratorRange.next_Usize_some_spec
    rw [ho]; simp only
    rw [htz, bind_tc_ok]
    -- `show` performs the iota reduction of the pattern-matching `let` that `simp` leaves alone
    show (do let lo ← load_i16 b iter.start
             let i ← iter.start + 8#usize
             let hi ← load_i16 b i
             let (lo1, hi1) ← backend.avx2.ntt.ct_butterfly lo hi z zq qv
             let b1 ← store_i16 b iter.start lo1
             let b2 ← store_i16 b1 i hi1
             backend.avx2.ntt.ntt_block_loop1 SECOND iter1 b2 qv)
        ⦃ (r : Array I16 256#usize) => BlockBnd r (A + T) ⦄
    obtain ⟨hgrown, hplain⟩ := hsplit
    obtain ⟨lo, hlo, hlob⟩ := load_i16_bndAt b iter.start (by omega)
      (hplain iter.start.val (by omega) (by omega))
    rw [hlo, bind_tc_ok]
    step*
    obtain ⟨hi, hhi, hhib⟩ := load_i16_bndAt b i (by omega)
      (hplain i.val (by omega) (by omega))
    rw [hhi, bind_tc_ok]
    apply WP.spec_bind (ct_butterfly_bnd lo hi z zq qv Q Zb A T hQ hQpos hQlt hzqm hlob hhib hzb
      hA0 hAZ hT hfit)
    intro r hr
    obtain ⟨lo1, hi1'⟩ := r
    obtain ⟨hr1, hr2⟩ := hr
    simp only at hr1 hr2
    show (do let b1 ← store_i16 b iter.start lo1
             let b2 ← store_i16 b1 i hi1'
             backend.avx2.ntt.ntt_block_loop1 SECOND iter1 b2 qv)
        ⦃ (r : Array I16 256#usize) => BlockBnd r (A + T) ⦄
    rw [← bind_assoc]
    apply WP.spec_bind (store_pair_bnd b iter.start i lo1 hi1' (A + T) (by omega) (by omega)
      (by omega) hr1 hr2)
    intro b2 hb2
    obtain ⟨hb2a, hb2b, hb2o⟩ := hb2
    apply ntt_block_loop1_bnd SECOND iter1 b2 qv Q Zb A T hQ hQpos hQlt hA0 hT0 hAZ hT hfit
      ⟨z, zq, htz, hzb, hzqm⟩ (by rw [hend']; exact hend)
    constructor
    · intro v hv hP
      rcases (show v = iter.start.val ∨ v = i.val ∨ (v ≠ iter.start.val ∧ v ≠ i.val)
        from by omega) with rfl | rfl | ⟨h1, h2⟩
      · exact hb2a
      · exact hb2b
      · intro k hk
        rw [hb2o v hv h1 h2 k hk]
        exact hgrown v hv (by omega) k hk
    · intro v hv hP
      intro k hk
      rw [hb2o v hv (by omega) (by omega) k hk]
      exact hplain v hv (by omega) k hk
  · let* ⟨ o, iter1, hnone, _ ⟩ ← core.iter.range.IteratorRange.next_Usize_none_spec
    rw [hnone]; simp only [WP.spec_ok]
    rw [blockBnd_iff]
    intro v hv
    exact hsplit.1 v hv (by omega)
termination_by iter.«end».val - iter.start.val
decreasing_by scalar_decr_tac

/-- The `len = 1` level: eight butterflies pairing `2h` with `2h + 1`, ψ from group `h`. -/
theorem ntt_block_loop4_bnd (SECOND : Bool) (iter : core.ops.range.Range Usize)
    (b : Array I16 256#usize) (qv : Vec256) (Q Zb A T : ℤ)
    (hQ : ∀ i < 16, (lane16 qv i).toInt = Q) (hQpos : 0 < Q) (hQlt : Q ≤ 2 ^ 15)
    (hA0 : 0 ≤ A) (hAZ : A * Zb < 2 ^ 15 * Q) (hT : A * Zb + 2 ^ 15 * Q ≤ 2 ^ 16 * T)
    (hfit : A + T ≤ 2 ^ 15 - 1)
    (htbl : ∀ h : Usize, h.val < 8 → ∃ z zq,
      (if SECOND then (do let t ← backend.avx2.ntt.FWD1_Q2; backend.avx2.ntt.ld_tbl t h)
       else (do let t ← backend.avx2.ntt.FWD1_Q1; backend.avx2.ntt.ld_tbl t h))
        = ok (z, zq) ∧ PsiOk z zq Q Zb)
    (hend : iter.«end».val = 8)
    (hsplit : Split b (fun v => v < 2 * iter.start.val) A T) :
    backend.avx2.ntt.ntt_block_loop4 SECOND iter b qv
      ⦃ (r : Array I16 256#usize) => BlockBnd r (A + T) ⦄ := by
  unfold backend.avx2.ntt.ntt_block_loop4
  by_cases hlt : iter.start.val < iter.«end».val
  · let* ⟨ o, iter1, ho, hstart', hend' ⟩ ← core.iter.range.IteratorRange.next_Usize_some_spec
    rw [ho]; simp only
    obtain ⟨z, zq, htz, hzb, hzqm⟩ := htbl iter.start (by omega)
    rw [htz, bind_tc_ok]
    show (do let i ← 2#usize * iter.start
             let lo ← load_i16 b i
             let i1 ← i + 1#usize
             let hi ← load_i16 b i1
             let (lo1, hi1) ← backend.avx2.ntt.ct_butterfly lo hi z zq qv
             let b1 ← store_i16 b i lo1
             let i2 ← i + 1#usize
             let b2 ← store_i16 b1 i2 hi1
             backend.avx2.ntt.ntt_block_loop4 SECOND iter1 b2 qv)
        ⦃ (r : Array I16 256#usize) => BlockBnd r (A + T) ⦄
    obtain ⟨hgrown, hplain⟩ := hsplit
    step*
    obtain ⟨lo, hlo, hlob⟩ := load_i16_bndAt b i (by omega) (hplain i.val (by omega) (by omega))
    rw [hlo, bind_tc_ok]
    step*
    obtain ⟨hi, hhi, hhib⟩ := load_i16_bndAt b i1 (by omega) (hplain i1.val (by omega) (by omega))
    rw [hhi, bind_tc_ok]
    apply WP.spec_bind (ct_butterfly_bnd lo hi z zq qv Q Zb A T hQ hQpos hQlt hzqm hlob hhib hzb
      hA0 hAZ hT hfit)
    intro r hr
    obtain ⟨lo1, hi1'⟩ := r
    obtain ⟨hr1, hr2⟩ := hr
    simp only at hr1 hr2
    show (do let b1 ← store_i16 b i lo1
             let i2 ← i + 1#usize
             let b2 ← store_i16 b1 i2 hi1'
             backend.avx2.ntt.ntt_block_loop4 SECOND iter1 b2 qv)
        ⦃ (r : Array I16 256#usize) => BlockBnd r (A + T) ⦄
    obtain ⟨b1, hb1, hb1at, hb1oth⟩ := store_i16_at b i lo1 (by omega)
    rw [hb1, bind_tc_ok]
    step*
    obtain ⟨b2, hb2, hb2at, hb2oth⟩ := store_i16_at b1 i2 hi1' (by omega)
    rw [hb2, bind_tc_ok]
    apply ntt_block_loop4_bnd SECOND iter1 b2 qv Q Zb A T hQ hQpos hQlt hA0 hAZ hT hfit htbl
      (by rw [hend']; exact hend)
    constructor
    · intro v hv hP
      rcases (show v = i.val ∨ v = i2.val ∨ (v ≠ i.val ∧ v ≠ i2.val) from by omega)
        with rfl | rfl | ⟨h1, h2⟩
      · intro k hk
        rw [hb2oth i.val (by omega) (by omega) k hk, hb1at k hk]
        exact hr1 k hk
      · intro k hk
        rw [hb2at k hk]
        exact hr2 k hk
      · intro k hk
        rw [hb2oth v hv h2 k hk, hb1oth v hv h1 k hk]
        exact hgrown v hv (by omega) k hk
    · intro v hv hP k hk
      rw [hb2oth v hv (by omega) k hk, hb1oth v hv (by omega) k hk]
      exact hplain v hv (by omega) k hk
  · let* ⟨ o, iter1, hnone, _ ⟩ ← core.iter.range.IteratorRange.next_Usize_none_spec
    rw [hnone]; simp only [WP.spec_ok]
    rw [blockBnd_iff]
    intro v hv
    exact hsplit.1 v hv (by omega)
termination_by iter.«end».val - iter.start.val
decreasing_by scalar_decr_tac

/-- The `len = 4` level, one group: `4` butterflies pairing `8h + j` with `8h + j + 4`.
Groups `0 … h` are done, so the "already grown" set is exactly `v < 8h`. -/
theorem ntt_block_loop2_loop0_bnd (SECOND : Bool) (iter : core.ops.range.Range Usize)
    (b : Array I16 256#usize) (qv : Vec256) (h : Usize) (Q Zb A T : ℤ)
    (hQ : ∀ i < 16, (lane16 qv i).toInt = Q) (hQpos : 0 < Q) (hQlt : Q ≤ 2 ^ 15)
    (hA0 : 0 ≤ A) (hAZ : A * Zb < 2 ^ 15 * Q) (hT : A * Zb + 2 ^ 15 * Q ≤ 2 ^ 16 * T)
    (hfit : A + T ≤ 2 ^ 15 - 1)
    (hh : h.val < 2)
    (htbl : ∃ z zq,
      (if SECOND then (do let t ← backend.avx2.ntt.FWD4_Q2; backend.avx2.ntt.ld_tbl t h)
       else (do let t ← backend.avx2.ntt.FWD4_Q1; backend.avx2.ntt.ld_tbl t h))
        = ok (z, zq) ∧ PsiOk z zq Q Zb)
    (hend : iter.«end».val = 4) (hstartle : iter.start.val ≤ 4)
    (hsplit : Split b (fun v => v < 8 * h.val
        ∨ (8 * h.val ≤ v ∧ v < 8 * h.val + iter.start.val)
        ∨ (8 * h.val + 4 ≤ v ∧ v < 8 * h.val + 4 + iter.start.val)) A T) :
    backend.avx2.ntt.ntt_block_loop2_loop0 SECOND iter b qv h
      ⦃ (r : Array I16 256#usize) => Split r (fun v => v < 8 * h.val + 8) A T ⦄ := by
  unfold backend.avx2.ntt.ntt_block_loop2_loop0
  obtain ⟨z, zq, htz, hzb, hzqm⟩ := htbl
  by_cases hlt : iter.start.val < iter.«end».val
  · let* ⟨ o, iter1, ho, hstart', hend' ⟩ ← core.iter.range.IteratorRange.next_Usize_some_spec
    rw [ho]; simp only
    rw [htz, bind_tc_ok]
    show (do let i ← 8#usize * h
             let i1 ← i + iter.start
             let lo ← load_i16 b i1
             let i2 ← i + iter.start
             let i3 ← i2 + 4#usize
             let hi ← load_i16 b i3
             let (lo1, hi1) ← backend.avx2.ntt.ct_butterfly lo hi z zq qv
             let i4 ← i + iter.start
             let b1 ← store_i16 b i4 lo1
             let i5 ← i + iter.start
             let i6 ← i5 + 4#usize
             let b2 ← store_i16 b1 i6 hi1
             backend.avx2.ntt.ntt_block_loop2_loop0 SECOND iter1 b2 qv h)
        ⦃ (r : Array I16 256#usize) => Split r (fun v => v < 8 * h.val + 8) A T ⦄
    obtain ⟨hgrown, hplain⟩ := hsplit
    step*
    obtain ⟨lo, hlo, hlob⟩ := load_i16_bndAt b i1 (by omega)
      (hplain i1.val (by omega) (by omega))
    rw [hlo, bind_tc_ok]
    step*
    obtain ⟨hi, hhi, hhib⟩ := load_i16_bndAt b i3 (by omega)
      (hplain i3.val (by omega) (by omega))
    rw [hhi, bind_tc_ok]
    apply WP.spec_bind (ct_butterfly_bnd lo hi z zq qv Q Zb A T hQ hQpos hQlt hzqm hlob hhib hzb
      hA0 hAZ hT hfit)
    intro r hr
    obtain ⟨lo1, hi1'⟩ := r
    obtain ⟨hr1, hr2⟩ := hr
    simp only at hr1 hr2
    show (do let i4 ← i + iter.start
             let b1 ← store_i16 b i4 lo1
             let i5 ← i + iter.start
             let i6 ← i5 + 4#usize
             let b2 ← store_i16 b1 i6 hi1'
             backend.avx2.ntt.ntt_block_loop2_loop0 SECOND iter1 b2 qv h)
        ⦃ (r : Array I16 256#usize) => Split r (fun v => v < 8 * h.val + 8) A T ⦄
    step*
    obtain ⟨b1, hb1, hb1at, hb1oth⟩ := store_i16_at b i4 lo1 (by omega)
    rw [hb1, bind_tc_ok]
    step*
    obtain ⟨b2, hb2, hb2at, hb2oth⟩ := store_i16_at b1 i6 hi1' (by omega)
    rw [hb2, bind_tc_ok]
    apply ntt_block_loop2_loop0_bnd SECOND iter1 b2 qv h Q Zb A T hQ hQpos hQlt hA0 hAZ hT
      hfit hh ⟨z, zq, htz, hzb, hzqm⟩ (by rw [hend']; exact hend) (by omega)
    constructor
    · intro v hv hP
      rcases (show v = i4.val ∨ v = i6.val ∨ (v ≠ i4.val ∧ v ≠ i6.val) from by omega)
        with rfl | rfl | ⟨hne1, hne2⟩
      · intro k hk
        rw [hb2oth i4.val (by omega) (by omega) k hk, hb1at k hk]
        exact hr1 k hk
      · intro k hk
        rw [hb2at k hk]
        exact hr2 k hk
      · intro k hk
        rw [hb2oth v hv hne2 k hk, hb1oth v hv hne1 k hk]
        exact hgrown v hv (by omega) k hk
    · intro v hv hP k hk
      rw [hb2oth v hv (by omega) k hk, hb1oth v hv (by omega) k hk]
      exact hplain v hv (by omega) k hk
  · let* ⟨ o, iter1, hnone, _ ⟩ ← core.iter.range.IteratorRange.next_Usize_none_spec
    rw [hnone]; simp only [WP.spec_ok]
    obtain ⟨hgrown, hplain⟩ := hsplit
    refine ⟨fun v hv hP => hgrown v hv ?_, fun v hv hP => hplain v hv ?_⟩
    · have hP' : v < 8 * h.val + 8 := hP
      show v < 8 * h.val ∨ (8 * h.val ≤ v ∧ v < 8 * h.val + iter.start.val)
        ∨ (8 * h.val + 4 ≤ v ∧ v < 8 * h.val + 4 + iter.start.val)
      omega
    · have hP' : ¬ (v < 8 * h.val + 8) := hP
      show ¬ (v < 8 * h.val ∨ (8 * h.val ≤ v ∧ v < 8 * h.val + iter.start.val)
        ∨ (8 * h.val + 4 ≤ v ∧ v < 8 * h.val + 4 + iter.start.val))
      omega
termination_by iter.«end».val - iter.start.val
decreasing_by scalar_decr_tac

/-- The `len = 2` level, one group: `2` butterflies pairing `4h + j` with `4h + j + 2`.
Groups `0 … h` are done, so the "already grown" set is exactly `v < 4h`. -/
theorem ntt_block_loop3_loop0_bnd (SECOND : Bool) (iter : core.ops.range.Range Usize)
    (b : Array I16 256#usize) (qv : Vec256) (h : Usize) (Q Zb A T : ℤ)
    (hQ : ∀ i < 16, (lane16 qv i).toInt = Q) (hQpos : 0 < Q) (hQlt : Q ≤ 2 ^ 15)
    (hA0 : 0 ≤ A) (hAZ : A * Zb < 2 ^ 15 * Q) (hT : A * Zb + 2 ^ 15 * Q ≤ 2 ^ 16 * T)
    (hfit : A + T ≤ 2 ^ 15 - 1)
    (hh : h.val < 4)
    (htbl : ∃ z zq,
      (if SECOND then (do let t ← backend.avx2.ntt.FWD2_Q2; backend.avx2.ntt.ld_tbl t h)
       else (do let t ← backend.avx2.ntt.FWD2_Q1; backend.avx2.ntt.ld_tbl t h))
        = ok (z, zq) ∧ PsiOk z zq Q Zb)
    (hend : iter.«end».val = 2) (hstartle : iter.start.val ≤ 2)
    (hsplit : Split b (fun v => v < 4 * h.val
        ∨ (4 * h.val ≤ v ∧ v < 4 * h.val + iter.start.val)
        ∨ (4 * h.val + 2 ≤ v ∧ v < 4 * h.val + 2 + iter.start.val)) A T) :
    backend.avx2.ntt.ntt_block_loop3_loop0 SECOND iter b qv h
      ⦃ (r : Array I16 256#usize) => Split r (fun v => v < 4 * h.val + 4) A T ⦄ := by
  unfold backend.avx2.ntt.ntt_block_loop3_loop0
  obtain ⟨z, zq, htz, hzb, hzqm⟩ := htbl
  by_cases hlt : iter.start.val < iter.«end».val
  · let* ⟨ o, iter1, ho, hstart', hend' ⟩ ← core.iter.range.IteratorRange.next_Usize_some_spec
    rw [ho]; simp only
    rw [htz, bind_tc_ok]
    show (do let i ← 4#usize * h
             let i1 ← i + iter.start
             let lo ← load_i16 b i1
             let i2 ← i + iter.start
             let i3 ← i2 + 2#usize
             let hi ← load_i16 b i3
             let (lo1, hi1) ← backend.avx2.ntt.ct_butterfly lo hi z zq qv
             let i4 ← i + iter.start
             let b1 ← store_i16 b i4 lo1
             let i5 ← i + iter.start
             let i6 ← i5 + 2#usize
             let b2 ← store_i16 b1 i6 hi1
             backend.avx2.ntt.ntt_block_loop3_loop0 SECOND iter1 b2 qv h)
        ⦃ (r : Array I16 256#usize) => Split r (fun v => v < 4 * h.val + 4) A T ⦄
    obtain ⟨hgrown, hplain⟩ := hsplit
    step*
    obtain ⟨lo, hlo, hlob⟩ := load_i16_bndAt b i1 (by omega)
      (hplain i1.val (by omega) (by omega))
    rw [hlo, bind_tc_ok]
    step*
    obtain ⟨hi, hhi, hhib⟩ := load_i16_bndAt b i3 (by omega)
      (hplain i3.val (by omega) (by omega))
    rw [hhi, bind_tc_ok]
    apply WP.spec_bind (ct_butterfly_bnd lo hi z zq qv Q Zb A T hQ hQpos hQlt hzqm hlob hhib hzb
      hA0 hAZ hT hfit)
    intro r hr
    obtain ⟨lo1, hi1'⟩ := r
    obtain ⟨hr1, hr2⟩ := hr
    simp only at hr1 hr2
    show (do let i4 ← i + iter.start
             let b1 ← store_i16 b i4 lo1
             let i5 ← i + iter.start
             let i6 ← i5 + 2#usize
             let b2 ← store_i16 b1 i6 hi1'
             backend.avx2.ntt.ntt_block_loop3_loop0 SECOND iter1 b2 qv h)
        ⦃ (r : Array I16 256#usize) => Split r (fun v => v < 4 * h.val + 4) A T ⦄
    step*
    obtain ⟨b1, hb1, hb1at, hb1oth⟩ := store_i16_at b i4 lo1 (by omega)
    rw [hb1, bind_tc_ok]
    step*
    obtain ⟨b2, hb2, hb2at, hb2oth⟩ := store_i16_at b1 i6 hi1' (by omega)
    rw [hb2, bind_tc_ok]
    apply ntt_block_loop3_loop0_bnd SECOND iter1 b2 qv h Q Zb A T hQ hQpos hQlt hA0 hAZ hT
      hfit hh ⟨z, zq, htz, hzb, hzqm⟩ (by rw [hend']; exact hend) (by omega)
    constructor
    · intro v hv hP
      rcases (show v = i4.val ∨ v = i6.val ∨ (v ≠ i4.val ∧ v ≠ i6.val) from by omega)
        with rfl | rfl | ⟨hne1, hne2⟩
      · intro k hk
        rw [hb2oth i4.val (by omega) (by omega) k hk, hb1at k hk]
        exact hr1 k hk
      · intro k hk
        rw [hb2at k hk]
        exact hr2 k hk
      · intro k hk
        rw [hb2oth v hv hne2 k hk, hb1oth v hv hne1 k hk]
        exact hgrown v hv (by omega) k hk
    · intro v hv hP k hk
      rw [hb2oth v hv (by omega) k hk, hb1oth v hv (by omega) k hk]
      exact hplain v hv (by omega) k hk
  · let* ⟨ o, iter1, hnone, _ ⟩ ← core.iter.range.IteratorRange.next_Usize_none_spec
    rw [hnone]; simp only [WP.spec_ok]
    obtain ⟨hgrown, hplain⟩ := hsplit
    refine ⟨fun v hv hP => hgrown v hv ?_, fun v hv hP => hplain v hv ?_⟩
    · have hP' : v < 4 * h.val + 4 := hP
      show v < 4 * h.val ∨ (4 * h.val ≤ v ∧ v < 4 * h.val + iter.start.val)
        ∨ (4 * h.val + 2 ≤ v ∧ v < 4 * h.val + 2 + iter.start.val)
      omega
    · have hP' : ¬ (v < 4 * h.val + 4) := hP
      show ¬ (v < 4 * h.val ∨ (4 * h.val ≤ v ∧ v < 4 * h.val + iter.start.val)
        ∨ (4 * h.val + 2 ≤ v ∧ v < 4 * h.val + 2 + iter.start.val))
      omega
termination_by iter.«end».val - iter.start.val
decreasing_by scalar_decr_tac

/-- The `len = 4` level: 2 groups of 4 butterflies. -/
theorem ntt_block_loop2_bnd (SECOND : Bool) (iter : core.ops.range.Range Usize)
    (b : Array I16 256#usize) (qv : Vec256) (Q Zb A T : ℤ)
    (hQ : ∀ i < 16, (lane16 qv i).toInt = Q) (hQpos : 0 < Q) (hQlt : Q ≤ 2 ^ 15)
    (hA0 : 0 ≤ A) (hAZ : A * Zb < 2 ^ 15 * Q) (hT : A * Zb + 2 ^ 15 * Q ≤ 2 ^ 16 * T)
    (hfit : A + T ≤ 2 ^ 15 - 1)
    (htbl : ∀ h : Usize, h.val < 2 → ∃ z zq,
      (if SECOND then (do let t ← backend.avx2.ntt.FWD4_Q2;
                          backend.avx2.ntt.ld_tbl t h)
       else (do let t ← backend.avx2.ntt.FWD4_Q1;
                backend.avx2.ntt.ld_tbl t h))
        = ok (z, zq) ∧ PsiOk z zq Q Zb)
    (hend : iter.«end».val = 2) (hstartle : iter.start.val ≤ 2)
    (hsplit : Split b (fun v => v < 8 * iter.start.val) A T) :
    backend.avx2.ntt.ntt_block_loop2 SECOND iter b qv
      ⦃ (r : Array I16 256#usize) => BlockBnd r (A + T) ⦄ := by
  unfold backend.avx2.ntt.ntt_block_loop2
  by_cases hlt : iter.start.val < iter.«end».val
  · let* ⟨ o, iter1, ho, hstart', hend' ⟩ ← core.iter.range.IteratorRange.next_Usize_some_spec
    rw [ho]; simp only
    apply WP.spec_bind (ntt_block_loop2_loop0_bnd SECOND
      { start := 0#usize, «end» := 4#usize } b qv iter.start Q Zb A T hQ hQpos hQlt hA0 hAZ hT
      hfit (by omega) (htbl iter.start (by omega)) rfl (by decide) ?_)
    · intro b1 hb1
      apply ntt_block_loop2_bnd SECOND iter1 b1 qv Q Zb A T hQ hQpos hQlt hA0 hAZ hT hfit htbl
        (by rw [hend']; exact hend) (by omega)
      obtain ⟨hg, hp⟩ := hb1
      refine ⟨fun v hv hP => hg v hv ?_, fun v hv hP => hp v hv ?_⟩
      · have hP' : v < 8 * iter1.start.val := hP
        show v < 8 * iter.start.val + 8
        omega
      · have hP' : ¬ (v < 8 * iter1.start.val) := hP
        show ¬ (v < 8 * iter.start.val + 8)
        omega
    · obtain ⟨hg, hp⟩ := hsplit
      refine ⟨fun v hv hP => hg v hv ?_, fun v hv hP => hp v hv ?_⟩
      · have hP' : v < 8 * iter.start.val
            ∨ (8 * iter.start.val ≤ v ∧ v < 8 * iter.start.val + 0)
            ∨ (8 * iter.start.val + 4 ≤ v ∧ v < 8 * iter.start.val + 4 + 0) := hP
        show v < 8 * iter.start.val
        omega
      · have hP' : ¬ (v < 8 * iter.start.val
            ∨ (8 * iter.start.val ≤ v ∧ v < 8 * iter.start.val + 0)
            ∨ (8 * iter.start.val + 4 ≤ v ∧ v < 8 * iter.start.val + 4 + 0)) := hP
        show ¬ (v < 8 * iter.start.val)
        omega
  · let* ⟨ o, iter1, hnone, _ ⟩ ← core.iter.range.IteratorRange.next_Usize_none_spec
    rw [hnone]; simp only [WP.spec_ok]
    rw [blockBnd_iff]
    intro v hv
    refine hsplit.1 v hv ?_
    show v < 8 * iter.start.val
    omega
termination_by iter.«end».val - iter.start.val
decreasing_by scalar_decr_tac

/-- The `len = 2` level: 4 groups of 2 butterflies. -/
theorem ntt_block_loop3_bnd (SECOND : Bool) (iter : core.ops.range.Range Usize)
    (b : Array I16 256#usize) (qv : Vec256) (Q Zb A T : ℤ)
    (hQ : ∀ i < 16, (lane16 qv i).toInt = Q) (hQpos : 0 < Q) (hQlt : Q ≤ 2 ^ 15)
    (hA0 : 0 ≤ A) (hAZ : A * Zb < 2 ^ 15 * Q) (hT : A * Zb + 2 ^ 15 * Q ≤ 2 ^ 16 * T)
    (hfit : A + T ≤ 2 ^ 15 - 1)
    (htbl : ∀ h : Usize, h.val < 4 → ∃ z zq,
      (if SECOND then (do let t ← backend.avx2.ntt.FWD2_Q2;
                          backend.avx2.ntt.ld_tbl t h)
       else (do let t ← backend.avx2.ntt.FWD2_Q1;
                backend.avx2.ntt.ld_tbl t h))
        = ok (z, zq) ∧ PsiOk z zq Q Zb)
    (hend : iter.«end».val = 4) (hstartle : iter.start.val ≤ 4)
    (hsplit : Split b (fun v => v < 4 * iter.start.val) A T) :
    backend.avx2.ntt.ntt_block_loop3 SECOND iter b qv
      ⦃ (r : Array I16 256#usize) => BlockBnd r (A + T) ⦄ := by
  unfold backend.avx2.ntt.ntt_block_loop3
  by_cases hlt : iter.start.val < iter.«end».val
  · let* ⟨ o, iter1, ho, hstart', hend' ⟩ ← core.iter.range.IteratorRange.next_Usize_some_spec
    rw [ho]; simp only
    apply WP.spec_bind (ntt_block_loop3_loop0_bnd SECOND
      { start := 0#usize, «end» := 2#usize } b qv iter.start Q Zb A T hQ hQpos hQlt hA0 hAZ hT
      hfit (by omega) (htbl iter.start (by omega)) rfl (by decide) ?_)
    · intro b1 hb1
      apply ntt_block_loop3_bnd SECOND iter1 b1 qv Q Zb A T hQ hQpos hQlt hA0 hAZ hT hfit htbl
        (by rw [hend']; exact hend) (by omega)
      obtain ⟨hg, hp⟩ := hb1
      refine ⟨fun v hv hP => hg v hv ?_, fun v hv hP => hp v hv ?_⟩
      · have hP' : v < 4 * iter1.start.val := hP
        show v < 4 * iter.start.val + 4
        omega
      · have hP' : ¬ (v < 4 * iter1.start.val) := hP
        show ¬ (v < 4 * iter.start.val + 4)
        omega
    · obtain ⟨hg, hp⟩ := hsplit
      refine ⟨fun v hv hP => hg v hv ?_, fun v hv hP => hp v hv ?_⟩
      · have hP' : v < 4 * iter.start.val
            ∨ (4 * iter.start.val ≤ v ∧ v < 4 * iter.start.val + 0)
            ∨ (4 * iter.start.val + 2 ≤ v ∧ v < 4 * iter.start.val + 2 + 0) := hP
        show v < 4 * iter.start.val
        omega
      · have hP' : ¬ (v < 4 * iter.start.val
            ∨ (4 * iter.start.val ≤ v ∧ v < 4 * iter.start.val + 0)
            ∨ (4 * iter.start.val + 2 ≤ v ∧ v < 4 * iter.start.val + 2 + 0)) := hP
        show ¬ (v < 4 * iter.start.val)
        omega
  · let* ⟨ o, iter1, hnone, _ ⟩ ← core.iter.range.IteratorRange.next_Usize_none_spec
    rw [hnone]; simp only [WP.spec_ok]
    rw [blockBnd_iff]
    intro v hv
    refine hsplit.1 v hv ?_
    show v < 4 * iter.start.val
    omega
termination_by iter.«end».val - iter.start.val
decreasing_by scalar_decr_tac

/-! ## The horizontal levels

Levels with `len ≥ 16` pair whole vectors `i` and `i + half` inside a group of width `2·half`,
with ψ broadcast across the group.  `half` is always one of 8, 4, 2, 1, which is what lets the
index arithmetic stay literal. -/

theorem ntt_block_loop0_loop0_loop0_bnd (b : Array I16 256#usize) (qv : Vec256)
    (half start i : Usize) (z zq : Vec256) (Q Zb A T : ℤ)
    (hQ : ∀ j < 16, (lane16 qv j).toInt = Q) (hQpos : 0 < Q) (hQlt : Q ≤ 2 ^ 15)
    (hA0 : 0 ≤ A) (hAZ : A * Zb < 2 ^ 15 * Q) (hT : A * Zb + 2 ^ 15 * Q ≤ 2 ^ 16 * T)
    (hfit : A + T ≤ 2 ^ 15 - 1) (hpsi : PsiOk z zq Q Zb)
    (hhalf : half.val = 8 ∨ half.val = 4 ∨ half.val = 2 ∨ half.val = 1)
    (hgrp : start.val + 2 * half.val ≤ 16)
    (hi : start.val ≤ i.val ∧ i.val ≤ start.val + half.val)
    (hsplit : Split b (fun v => v < start.val
        ∨ (start.val ≤ v ∧ v < i.val)
        ∨ (start.val + half.val ≤ v ∧ v < i.val + half.val)) A T) :
    backend.avx2.ntt.ntt_block_loop0_loop0_loop0 b qv half start z zq i
      ⦃ (r : Array I16 256#usize) =>
          Split r (fun v => v < start.val + 2 * half.val) A T ⦄ := by
  unfold backend.avx2.ntt.ntt_block_loop0_loop0_loop0
  have hzb := hpsi.1
  have hzqm := hpsi.2
  obtain ⟨hgrown, hplain⟩ := hsplit
  by_cases hlt : i.val < start.val + half.val
  · step*
    obtain ⟨lo, hlo, hlob⟩ := load_i16_bndAt b i (by omega) (hplain i.val (by omega) (by omega))
    rw [hlo, bind_tc_ok]
    step*
    obtain ⟨hiv, hhiv, hhivb⟩ := load_i16_bndAt b i2 (by omega)
      (hplain i2.val (by omega) (by omega))
    rw [hhiv, bind_tc_ok]
    apply WP.spec_bind (ct_butterfly_bnd lo hiv z zq qv Q Zb A T hQ hQpos hQlt hzqm hlob hhivb
      hzb hA0 hAZ hT hfit)
    intro r hr
    obtain ⟨lo1, hi1'⟩ := r
    obtain ⟨hr1, hr2⟩ := hr
    simp only at hr1 hr2
    show (do let b1 ← store_i16 b i lo1
             let b2 ← store_i16 b1 i2 hi1'
             let i3 ← i + 1#usize
             backend.avx2.ntt.ntt_block_loop0_loop0_loop0 b2 qv half start z zq i3)
        ⦃ (r : Array I16 256#usize) =>
            Split r (fun v => v < start.val + 2 * half.val) A T ⦄
    obtain ⟨b1, hb1, hb1at, hb1oth⟩ := store_i16_at b i lo1 (by omega)
    rw [hb1, bind_tc_ok]
    obtain ⟨b2, hb2, hb2at, hb2oth⟩ := store_i16_at b1 i2 hi1' (by omega)
    rw [hb2, bind_tc_ok]
    step*
    constructor
    · intro v hv hP
      have hP' : v < start.val ∨ (start.val ≤ v ∧ v < i3.val)
          ∨ (start.val + half.val ≤ v ∧ v < i3.val + half.val) := hP
      rcases (show v = i.val ∨ v = i2.val ∨ (v ≠ i.val ∧ v ≠ i2.val) from by omega)
        with rfl | rfl | ⟨hne1, hne2⟩
      · intro k hk
        rw [hb2oth i.val (by omega) (by omega) k hk, hb1at k hk]
        exact hr1 k hk
      · intro k hk
        rw [hb2at k hk]
        exact hr2 k hk
      · intro k hk
        rw [hb2oth v hv hne2 k hk, hb1oth v hv hne1 k hk]
        exact hgrown v hv (by omega) k hk
    · intro v hv hP k hk
      have hP' : ¬ (v < start.val ∨ (start.val ≤ v ∧ v < i3.val)
          ∨ (start.val + half.val ≤ v ∧ v < i3.val + half.val)) := hP
      rw [hb2oth v hv (by omega) k hk, hb1oth v hv (by omega) k hk]
      exact hplain v hv (by omega) k hk
  · step*
    rw [if_neg (by scalar_tac)]
    simp only [WP.spec_ok]
    refine ⟨fun v hv hP => hgrown v hv ?_, fun v hv hP => hplain v hv ?_⟩
    · have hP' : v < start.val + 2 * half.val := hP
      show v < start.val ∨ (start.val ≤ v ∧ v < i.val)
        ∨ (start.val + half.val ≤ v ∧ v < i.val + half.val)
      omega
    · have hP' : ¬ (v < start.val + 2 * half.val) := hP
      show ¬ (v < start.val ∨ (start.val ≤ v ∧ v < i.val)
        ∨ (start.val + half.val ≤ v ∧ v < i.val + half.val))
      omega
termination_by start.val + half.val - i.val
decreasing_by scalar_decr_tac

/-! ## The schedule arithmetic

This is the claim `src/backend/crt.rs` makes in prose.  A Cooley-Tukey level takes a bound `A` to
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

/-- **The crude per-level budget really does fail.**  Four flat `+0.75·q₂` steps from `q₂/2`
overflow an `i16` lane — so the schedule is *not* justified by it, exactly as `crt.rs` says. -/
theorem crude_budget_overflows :
    (5376 : ℤ) + 4 * (3 * 10753 / 4) > 32767 := by norm_num

/-! ## Three of the four levels, on the extracted code

The run the crude budget fails to cover is levels `len = 16, 8, 4, 2`.  The last three of those
are `ntt_block_loop1`, `loop2` and `loop3`, and this composes them against the chain above for
`q₂ = 10753`, the binding prime.  The first of the four is `ntt_block_loop0`'s last level, which
leaves the block inside `11194`; from there these three reach `31671`, inside `32767` with 1096
to spare — and the crude budget predicts overflow. -/

theorem vertical_levels_bnd_q2 (SECOND : Bool) (b : Array I16 256#usize) (qv : Vec256)
    (hQ : ∀ i < 16, (lane16 qv i).toInt = 10753)
    (htbl8 : ∃ z zq,
      (if SECOND then (do let t ← backend.avx2.ntt.FWD8_Q2; backend.avx2.ntt.ld_tbl t 0#usize)
       else (do let t ← backend.avx2.ntt.FWD8_Q1; backend.avx2.ntt.ld_tbl t 0#usize))
        = ok (z, zq) ∧ PsiOk z zq 10753 5376)
    (htbl4 : ∀ h : Usize, h.val < 2 → ∃ z zq,
      (if SECOND then (do let t ← backend.avx2.ntt.FWD4_Q2; backend.avx2.ntt.ld_tbl t h)
       else (do let t ← backend.avx2.ntt.FWD4_Q1; backend.avx2.ntt.ld_tbl t h))
        = ok (z, zq) ∧ PsiOk z zq 10753 5376)
    (htbl2 : ∀ h : Usize, h.val < 4 → ∃ z zq,
      (if SECOND then (do let t ← backend.avx2.ntt.FWD2_Q2; backend.avx2.ntt.ld_tbl t h)
       else (do let t ← backend.avx2.ntt.FWD2_Q1; backend.avx2.ntt.ld_tbl t h))
        = ok (z, zq) ∧ PsiOk z zq 10753 5376)
    (hb : BlockBnd b 11194) :
    (do let b3 ← backend.avx2.ntt.ntt_block_loop1 SECOND
          { start := 0#usize, «end» := 8#usize } b qv
        let b4 ← backend.avx2.ntt.ntt_block_loop2 SECOND
          { start := 0#usize, «end» := 2#usize } b3 qv
        backend.avx2.ntt.ntt_block_loop3 SECOND
          { start := 0#usize, «end» := 4#usize } b4 qv)
      ⦃ (r : Array I16 256#usize) => BlockBnd r 31671 ⦄ := by
  obtain ⟨-, s2, s3, s4, -, -⟩ := growth_q2
  apply WP.spec_bind (ntt_block_loop1_bnd SECOND { start := 0#usize, «end» := 8#usize } b qv
    10753 5376 11194 6295 hQ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    s2.1 s2.2.1 s2.2.2 htbl8 rfl
    ⟨fun v hv hP => absurd hP (by simp), fun v hv hP => (blockBnd_iff b 11194).mp hb v hv⟩)
  intro b3 hb3
  apply WP.spec_bind (ntt_block_loop2_bnd SECOND { start := 0#usize, «end» := 2#usize } b3 qv
    10753 5376 17489 6812 hQ (by norm_num) (by norm_num) (by norm_num)
    s3.1 s3.2.1 s3.2.2 htbl4 rfl (by decide)
    ⟨fun v hv hP => absurd hP (by simp), fun v hv hP =>
      ((blockBnd_iff b3 17489).mp hb3) v hv⟩)
  intro b4 hb4
  apply WP.spec_mono (ntt_block_loop3_bnd SECOND { start := 0#usize, «end» := 4#usize } b4 qv
    10753 5376 24301 7370 hQ (by norm_num) (by norm_num) (by norm_num)
    s4.1 s4.2.1 s4.2.2 htbl2 rfl (by decide)
    ⟨fun v hv hP => absurd hP (by simp), fun v hv hP =>
      ((blockBnd_iff b4 24301).mp hb4) v hv⟩)
  intro r hr
  exact hr.mono (by norm_num)

/-- One horizontal level: the groups of width `2·half`, each with its own broadcast ψ.

`step*` closes the recursive call with this theorem's own induction hypothesis, so the goal it
leaves is the invariant itself — an explicit `apply` here is wrong. -/
theorem ntt_block_loop0_loop0_bnd (SECOND : Bool) (b : Array I16 256#usize) (qv : Vec256)
    (k half start : Usize) (Q Zb A T : ℤ)
    (hQ : ∀ j < 16, (lane16 qv j).toInt = Q) (hQpos : 0 < Q) (hQlt : Q ≤ 2 ^ 15)
    (hA0 : 0 ≤ A) (hAZ : A * Zb < 2 ^ 15 * Q) (hT : A * Zb + 2 ^ 15 * Q ≤ 2 ^ 16 * T)
    (hfit : A + T ≤ 2 ^ 15 - 1)
    (hzeta : ∀ kk : Usize, kk.val < 256 → ∃ zi zqi : I16,
      backend.crt.zeta SECOND kk = ok zi ∧ backend.crt.zeta_q SECOND kk = ok zqi ∧
      |zi.val| ≤ Zb ∧ (2 ^ 16 : ℤ) ∣ (zqi.val * Q - zi.val))
    (hhalf : half.val = 8 ∨ half.val = 4 ∨ half.val = 2 ∨ half.val = 1)
    (hdvd : (2 * half.val) ∣ start.val) (hstart : start.val ≤ 16)
    (hk : k.val + (16 - start.val) ≤ 255)
    (hsplit : Split b (fun v => v < start.val) A T) :
    backend.avx2.ntt.ntt_block_loop0_loop0 SECOND b qv k half start
      ⦃ (r : (Array I16 256#usize) × Usize) =>
          BlockBnd r.1 (A + T) ∧ r.2.val ≤ k.val + (16 - start.val) ⦄ := by
  unfold backend.avx2.ntt.ntt_block_loop0_loop0
  by_cases hlt : start.val < 16
  · rw [if_pos (by scalar_tac)]
    step*
    obtain ⟨zi, zqi, hzi, hzqi, hzib, hzqid⟩ := hzeta k1 (by omega)
    rw [hzi, bind_tc_ok]
    obtain ⟨z, hz, hzl⟩ := set1_epi16_spec zi
    rw [hz, bind_tc_ok, hzqi, bind_tc_ok]
    obtain ⟨zq, hzq, hzql⟩ := set1_epi16_spec zqi
    rw [hzq, bind_tc_ok]
    have hpsi : PsiOk z zq Q Zb := by
      constructor
      · intro j hj
        rw [show (lane16 z j).toInt = zi.val from by rw [hzl j hj]; rfl]
        exact hzib
      · intro j hj
        rw [show (lane16 zq j).toInt = zqi.val from by rw [hzql j hj]; rfl,
          show (lane16 z j).toInt = zi.val from by rw [hzl j hj]; rfl]
        exact hzqid
    apply WP.spec_bind (ntt_block_loop0_loop0_loop0_bnd b qv half start start z zq Q Zb A T
      hQ hQpos hQlt hA0 hAZ hT hfit hpsi hhalf
      (by rcases hhalf with h | h | h | h <;> rw [h] at hdvd <;> omega)
      ⟨le_refl _, by omega⟩ ?_)
    · intro b1 hb1
      step*
      · rcases hhalf with h | h | h | h <;> scalar_tac
      · step*
        · rcases hhalf with h | h | h | h <;> scalar_tac
        all_goals first
          | (rcases hhalf with h | h | h | h <;> rw [h] at hdvd ⊢ <;> omega)
          | (rcases hhalf with h | h | h | h <;> rw [h] at hdvd <;> omega)
          | (rcases hhalf with h | h | h | h <;> omega)
          | (obtain ⟨hg, hp⟩ := hb1
             refine ⟨fun v hv hP => hg v hv ?_, fun v hv hP => hp v hv ?_⟩ <;>
               (try simp only at hP ⊢) <;>
               (rcases hhalf with h | h | h | h <;> rw [h] at hdvd <;> omega))
          | (exact ⟨r_post1, by rcases hhalf with h | h | h | h <;> omega⟩)
    · obtain ⟨hg, hp⟩ := hsplit
      refine ⟨fun v hv hP => hg v hv ?_, fun v hv hP => hp v hv ?_⟩
      · have hP' : v < start.val ∨ (start.val ≤ v ∧ v < start.val)
            ∨ (start.val + half.val ≤ v ∧ v < start.val + half.val) := hP
        show v < start.val
        omega
      · have hP' : ¬ (v < start.val ∨ (start.val ≤ v ∧ v < start.val)
            ∨ (start.val + half.val ≤ v ∧ v < start.val + half.val)) := hP
        show ¬ (v < start.val)
        omega
  · rw [if_neg (by scalar_tac)]
    simp only [WP.spec_ok]
    refine ⟨?_, by omega⟩
    rw [blockBnd_iff]
    intro v hv
    refine hsplit.1 v hv ?_
    show v < start.val
    omega
termination_by 16 - start.val
decreasing_by scalar_decr_tac

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
the four bounds taken from `growth_q2`.  The `k` threading is why
`ntt_block_loop0_loop0_bnd` also bounds the ζ index it returns. -/

private theorem usize_add_lit {a b c : Usize} (hc : a.val + b.val ≤ Usize.max)
    (h : a.val + b.val = c.val) : (a + b : Result Usize) = ok c := by
  obtain ⟨z, hz, hzv⟩ := WP.spec_imp_exists (Std.Usize.add_spec (x := a) (y := b) hc)
  rw [hz, UScalar.eq_of_val_eq (show z.val = c.val by rw [hzv, h])]

/-- Before a level runs nothing has grown, so any empty "already grown" predicate will do. -/
private theorem initSplit {b : Array I16 256#usize} {A T : ℤ} {P : ℕ → Prop}
    (hP : ∀ v, ¬ P v) (hb : BlockBnd b A) : Split b P A T :=
  ⟨fun v _ h => absurd h (hP v), fun v hv _ => (blockBnd_iff b A).mp hb v hv⟩

theorem ntt_block_loop0_bnd_q2 (SECOND : Bool) (b : Array I16 256#usize) (qv bm round : Vec256)
    (hQ : ∀ j < 16, (lane16 qv j).toInt = 10753)
    (hM : ∀ j < 16, (lane16 bm j).toInt = 12482)
    (hRnd : ∀ j < 16, (lane16 round j).toInt = 2 ^ 10)
    (hzeta : ∀ kk : Usize, kk.val < 256 → ∃ zi zqi : I16,
      backend.crt.zeta SECOND kk = ok zi ∧ backend.crt.zeta_q SECOND kk = ok zqi ∧
      |zi.val| ≤ 5376 ∧ (2 ^ 16 : ℤ) ∣ (zqi.val * 10753 - zi.val))
    (hb : BlockBnd b 5376) :
    backend.avx2.ntt.ntt_block_loop0 SECOND b qv bm round 0#usize 8#usize 0#usize
      ⦃ (r : Array I16 256#usize) => BlockBnd r 11194 ⦄ := by
  obtain ⟨s1, s2, s3, s4, -, -⟩ := growth_q2
  -- level 0, `half = 8`
  unfold backend.avx2.ntt.ntt_block_loop0
  rw [if_pos (by scalar_tac)]
  apply WP.spec_bind (ntt_block_loop0_loop0_bnd SECOND b qv 0#usize 8#usize 0#usize
    10753 5376 5376 5818 hQ (by norm_num) (by norm_num) (by norm_num) s1.1 s1.2.1 s1.2.2
    hzeta (by norm_num) (by norm_num) (by norm_num) (by norm_num) (initSplit (by simp) hb))
  rintro ⟨b1, k1⟩ ⟨hb1, hk1⟩
  simp only at hb1 hk1
  show (do let b2 ← (if (0#usize) = 2#usize then backend.avx2.ntt.barrett_block b1 bm round qv
             else ok b1)
           let half1 ← 8#usize / 2#usize
           let level1 ← 0#usize + 1#usize
           backend.avx2.ntt.ntt_block_loop0 SECOND b2 qv bm round k1 half1 level1)
      ⦃ (r : Array I16 256#usize) => BlockBnd r 11194 ⦄
  rw [if_neg (by decide), bind_tc_ok,
    show (8#usize / 2#usize : Result Usize) = ok 4#usize from rfl, bind_tc_ok,
    show (0#usize + 1#usize : Result Usize) = ok 1#usize from
      usize_add_lit (by scalar_tac) (by rfl), bind_tc_ok]
  -- level 1, `half = 4`
  unfold backend.avx2.ntt.ntt_block_loop0
  rw [if_pos (by scalar_tac)]
  apply WP.spec_bind (ntt_block_loop0_loop0_bnd SECOND b1 qv k1 4#usize 0#usize
    10753 5376 11194 6295 hQ (by norm_num) (by norm_num) (by norm_num) s2.1 s2.2.1 s2.2.2
    hzeta (by norm_num) (by norm_num) (by norm_num) (by scalar_tac) (initSplit (by simp) hb1))
  rintro ⟨b2, k2⟩ ⟨hb2, hk2⟩
  simp only at hb2 hk2
  show (do let b3 ← (if (1#usize) = 2#usize then backend.avx2.ntt.barrett_block b2 bm round qv
             else ok b2)
           let half1 ← 4#usize / 2#usize
           let level1 ← 1#usize + 1#usize
           backend.avx2.ntt.ntt_block_loop0 SECOND b3 qv bm round k2 half1 level1)
      ⦃ (r : Array I16 256#usize) => BlockBnd r 11194 ⦄
  rw [if_neg (by decide), bind_tc_ok,
    show (4#usize / 2#usize : Result Usize) = ok 2#usize from rfl, bind_tc_ok,
    show (1#usize + 1#usize : Result Usize) = ok 2#usize from
      usize_add_lit (by scalar_tac) (by rfl), bind_tc_ok]
  -- level 2, `half = 2`, then the re-centring pass
  unfold backend.avx2.ntt.ntt_block_loop0
  rw [if_pos (by scalar_tac)]
  apply WP.spec_bind (ntt_block_loop0_loop0_bnd SECOND b2 qv k2 2#usize 0#usize
    10753 5376 17489 6812 hQ (by norm_num) (by norm_num) (by norm_num) s3.1 s3.2.1 s3.2.2
    hzeta (by norm_num) (by norm_num) (by norm_num) (by scalar_tac) (initSplit (by simp) hb2))
  rintro ⟨b3, k3⟩ ⟨hb3, hk3⟩
  simp only at hb3 hk3
  show (do let b4 ← (if (2#usize) = 2#usize then backend.avx2.ntt.barrett_block b3 bm round qv
             else ok b3)
           let half1 ← 2#usize / 2#usize
           let level1 ← 2#usize + 1#usize
           backend.avx2.ntt.ntt_block_loop0 SECOND b4 qv bm round k3 half1 level1)
      ⦃ (r : Array I16 256#usize) => BlockBnd r 11194 ⦄
  rw [if_pos rfl]
  apply WP.spec_bind (barrett_block_bnd b3 bm round qv 10753 12482 hQ hM hRnd
    (by norm_num) (by norm_num) (by decide) (by norm_num) (by norm_num) (by norm_num))
  intro b4 hb4
  rw [show (2#usize / 2#usize : Result Usize) = ok 1#usize from rfl, bind_tc_ok,
    show (2#usize + 1#usize : Result Usize) = ok 3#usize from
      usize_add_lit (by scalar_tac) (by rfl), bind_tc_ok]
  -- level 3, `half = 1`, from a centred block again
  unfold backend.avx2.ntt.ntt_block_loop0
  rw [if_pos (by scalar_tac)]
  apply WP.spec_bind (ntt_block_loop0_loop0_bnd SECOND b4 qv k3 1#usize 0#usize
    10753 5376 5376 5818 hQ (by norm_num) (by norm_num) (by norm_num) s1.1 s1.2.1 s1.2.2
    hzeta (by norm_num) (by norm_num) (by norm_num) (by scalar_tac)
    (initSplit (by simp) (hb4.mono (by norm_num))))
  rintro ⟨b5, k5⟩ ⟨hb5, hk5⟩
  simp only at hb5 hk5
  show (do let b6 ← (if (3#usize) = 2#usize then backend.avx2.ntt.barrett_block b5 bm round qv
             else ok b5)
           let half1 ← 1#usize / 2#usize
           let level1 ← 3#usize + 1#usize
           backend.avx2.ntt.ntt_block_loop0 SECOND b6 qv bm round k5 half1 level1)
      ⦃ (r : Array I16 256#usize) => BlockBnd r 11194 ⦄
  rw [if_neg (by decide), bind_tc_ok,
    show (1#usize / 2#usize : Result Usize) = ok 0#usize from rfl, bind_tc_ok,
    show (3#usize + 1#usize : Result Usize) = ok 4#usize from
      usize_add_lit (by scalar_tac) (by rfl), bind_tc_ok]
  -- `half = 0`: the loop is done
  unfold backend.avx2.ntt.ntt_block_loop0
  rw [if_neg (by scalar_tac)]
  simp only [WP.spec_ok]
  exact hb5

/-! ## `ntt_block`

The whole forward transform of one block, for `q₂ = 10753` — the prime whose lane budget binds.
The chain: `11194` after the horizontal half, unchanged by the transpose, then `17489 → 24301 →
31671` across the three vertical levels, re-centred to `5376`, one more level to `11194`,
transposed, and re-centred.  So `ntt_block` leaves every coefficient centred, which is what its
Rust doc comment claims and what the next stage assumes. -/

theorem ntt_block_bnd_q2 (b : Array I16 256#usize)
    (hzeta : ∀ kk : Usize, kk.val < 256 → ∃ zi zqi : I16,
      backend.crt.zeta true kk = ok zi ∧ backend.crt.zeta_q true kk = ok zqi ∧
      |zi.val| ≤ 5376 ∧ (2 ^ 16 : ℤ) ∣ (zqi.val * 10753 - zi.val))
    (htbl8 : ∃ z zq,
      (do let t ← backend.avx2.ntt.FWD8_Q2; backend.avx2.ntt.ld_tbl t 0#usize) = ok (z, zq) ∧
        PsiOk z zq 10753 5376)
    (htbl4 : ∀ h : Usize, h.val < 2 → ∃ z zq,
      (do let t ← backend.avx2.ntt.FWD4_Q2; backend.avx2.ntt.ld_tbl t h) = ok (z, zq) ∧
        PsiOk z zq 10753 5376)
    (htbl2 : ∀ h : Usize, h.val < 4 → ∃ z zq,
      (do let t ← backend.avx2.ntt.FWD2_Q2; backend.avx2.ntt.ld_tbl t h) = ok (z, zq) ∧
        PsiOk z zq 10753 5376)
    (htbl1 : ∀ h : Usize, h.val < 8 → ∃ z zq,
      (do let t ← backend.avx2.ntt.FWD1_Q2; backend.avx2.ntt.ld_tbl t h) = ok (z, zq) ∧
        PsiOk z zq 10753 5376)
    (hb : BlockBnd b 5376) :
    backend.avx2.ntt.ntt_block true b
      ⦃ (r : Array I16 256#usize) => BlockBnd r 5376 ⦄ := by
  obtain ⟨s1, s2, s3, s4, -, -⟩ := growth_q2
  unfold backend.avx2.ntt.ntt_block backend.crt.q backend.crt.barrett_m
  simp only [if_true, bind_tc_ok]
  obtain ⟨qv, hqv, hqvl⟩ := set1_epi16_spec backend.crt.Q2
  rw [hqv, bind_tc_ok]
  obtain ⟨bm, hbm, hbml⟩ := set1_epi16_spec backend.crt.Q2_BARRETT_M
  rw [hbm, bind_tc_ok]
  have hSH : (backend.crt.BARRETT_SH : I32).val = 11 := by
    simp only [backend.crt.BARRETT_SH]; rfl
  step*
  have hi2e : i2 = 10#i32 := IScalar.eq_of_val_eq (by rw [i2_post, hSH]; rfl)
  rw [hi2e, show (1#i16 <<< (10#i32) : Result I16) = ok 1024#i16 from rfl, bind_tc_ok]
  obtain ⟨rnd, hrnd, hrndl⟩ := set1_epi16_spec 1024#i16
  rw [hrnd, bind_tc_ok]
  -- the three broadcast constants, as lane facts
  have hQ : ∀ j < 16, (lane16 qv j).toInt = 10753 := fun j hj => by rw [hqvl j hj]; simp only [backend.crt.Q2]; decide
  have hM : ∀ j < 16, (lane16 bm j).toInt = 12482 := fun j hj => by rw [hbml j hj]; simp only [backend.crt.Q2_BARRETT_M]; decide
  have hRnd : ∀ j < 16, (lane16 rnd j).toInt = 2 ^ 10 := fun j hj => by
    rw [hrndl j hj]; decide
  -- the horizontal half, then the transpose
  apply WP.spec_bind (ntt_block_loop0_bnd_q2 true b qv bm rnd hQ hM hRnd hzeta hb)
  intro b1 hb1
  apply WP.spec_bind (transpose16_bnd b1 hb1)
  intro b2 hb2
  -- three vertical levels
  apply WP.spec_bind (ntt_block_loop1_bnd true { start := 0#usize, «end» := 8#usize } b2 qv
    10753 5376 11194 6295 hQ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    s2.1 s2.2.1 s2.2.2 htbl8 rfl (initSplit (by simp) hb2))
  intro b3 hb3
  apply WP.spec_bind (ntt_block_loop2_bnd true { start := 0#usize, «end» := 2#usize } b3 qv
    10753 5376 17489 6812 hQ (by norm_num) (by norm_num) (by norm_num)
    s3.1 s3.2.1 s3.2.2 htbl4 rfl (by decide) (initSplit (by simp) hb3))
  intro b4 hb4
  apply WP.spec_bind (ntt_block_loop3_bnd true { start := 0#usize, «end» := 4#usize } b4 qv
    10753 5376 24301 7370 hQ (by norm_num) (by norm_num) (by norm_num)
    s4.1 s4.2.1 s4.2.2 htbl2 rfl (by decide) (initSplit (by simp) hb4))
  intro b5 hb5
  -- re-centre, the last level, transpose, re-centre
  apply WP.spec_bind (barrett_block_bnd b5 bm rnd qv 10753 12482 hQ hM hRnd
    (by norm_num) (by norm_num) (by decide) (by norm_num) (by norm_num) (by norm_num))
  intro b6 hb6
  apply WP.spec_bind (ntt_block_loop4_bnd true { start := 0#usize, «end» := 8#usize } b6 qv
    10753 5376 5376 5818 hQ (by norm_num) (by norm_num) (by norm_num)
    s1.1 s1.2.1 s1.2.2 htbl1 rfl (initSplit (by simp) (hb6.mono (by norm_num))))
  intro b7 hb7
  apply WP.spec_bind (transpose16_bnd b7 hb7)
  intro b8 hb8
  apply WP.spec_mono (barrett_block_bnd b8 bm rnd qv 10753 12482 hQ hM hRnd
    (by norm_num) (by norm_num) (by decide) (by norm_num) (by norm_num) (by norm_num))
  intro r hr
  exact hr.mono (by norm_num)

theorem ntt_block_loop0_bnd_q1 (SECOND : Bool) (b : Array I16 256#usize) (qv bm round : Vec256)
    (hQ : ∀ j < 16, (lane16 qv j).toInt = 7681)
    (hM : ∀ j < 16, (lane16 bm j).toInt = 17474)
    (hRnd : ∀ j < 16, (lane16 round j).toInt = 2 ^ 10)
    (hzeta : ∀ kk : Usize, kk.val < 256 → ∃ zi zqi : I16,
      backend.crt.zeta SECOND kk = ok zi ∧ backend.crt.zeta_q SECOND kk = ok zqi ∧
      |zi.val| ≤ 3840 ∧ (2 ^ 16 : ℤ) ∣ (zqi.val * 7681 - zi.val))
    (hb : BlockBnd b 3840) :
    backend.avx2.ntt.ntt_block_loop0 SECOND b qv bm round 0#usize 8#usize 0#usize
      ⦃ (r : Array I16 256#usize) => BlockBnd r 7906 ⦄ := by
  obtain ⟨s1, s2, s3, s4, -, -⟩ := growth_q1
  -- level 0, `half = 8`
  unfold backend.avx2.ntt.ntt_block_loop0
  rw [if_pos (by scalar_tac)]
  apply WP.spec_bind (ntt_block_loop0_loop0_bnd SECOND b qv 0#usize 8#usize 0#usize
    7681 3840 3840 4066 hQ (by norm_num) (by norm_num) (by norm_num) s1.1 s1.2.1 s1.2.2
    hzeta (by norm_num) (by norm_num) (by norm_num) (by norm_num) (initSplit (by simp) hb))
  rintro ⟨b1, k1⟩ ⟨hb1, hk1⟩
  simp only at hb1 hk1
  show (do let b2 ← (if (0#usize) = 2#usize then backend.avx2.ntt.barrett_block b1 bm round qv
             else ok b1)
           let half1 ← 8#usize / 2#usize
           let level1 ← 0#usize + 1#usize
           backend.avx2.ntt.ntt_block_loop0 SECOND b2 qv bm round k1 half1 level1)
      ⦃ (r : Array I16 256#usize) => BlockBnd r 7906 ⦄
  rw [if_neg (by decide), bind_tc_ok,
    show (8#usize / 2#usize : Result Usize) = ok 4#usize from rfl, bind_tc_ok,
    show (0#usize + 1#usize : Result Usize) = ok 1#usize from
      usize_add_lit (by scalar_tac) (by rfl), bind_tc_ok]
  -- level 1, `half = 4`
  unfold backend.avx2.ntt.ntt_block_loop0
  rw [if_pos (by scalar_tac)]
  apply WP.spec_bind (ntt_block_loop0_loop0_bnd SECOND b1 qv k1 4#usize 0#usize
    7681 3840 7906 4304 hQ (by norm_num) (by norm_num) (by norm_num) s2.1 s2.2.1 s2.2.2
    hzeta (by norm_num) (by norm_num) (by norm_num) (by scalar_tac) (initSplit (by simp) hb1))
  rintro ⟨b2, k2⟩ ⟨hb2, hk2⟩
  simp only at hb2 hk2
  show (do let b3 ← (if (1#usize) = 2#usize then backend.avx2.ntt.barrett_block b2 bm round qv
             else ok b2)
           let half1 ← 4#usize / 2#usize
           let level1 ← 1#usize + 1#usize
           backend.avx2.ntt.ntt_block_loop0 SECOND b3 qv bm round k2 half1 level1)
      ⦃ (r : Array I16 256#usize) => BlockBnd r 7906 ⦄
  rw [if_neg (by decide), bind_tc_ok,
    show (4#usize / 2#usize : Result Usize) = ok 2#usize from rfl, bind_tc_ok,
    show (1#usize + 1#usize : Result Usize) = ok 2#usize from
      usize_add_lit (by scalar_tac) (by rfl), bind_tc_ok]
  -- level 2, `half = 2`, then the re-centring pass
  unfold backend.avx2.ntt.ntt_block_loop0
  rw [if_pos (by scalar_tac)]
  apply WP.spec_bind (ntt_block_loop0_loop0_bnd SECOND b2 qv k2 2#usize 0#usize
    7681 3840 12210 4556 hQ (by norm_num) (by norm_num) (by norm_num) s3.1 s3.2.1 s3.2.2
    hzeta (by norm_num) (by norm_num) (by norm_num) (by scalar_tac) (initSplit (by simp) hb2))
  rintro ⟨b3, k3⟩ ⟨hb3, hk3⟩
  simp only at hb3 hk3
  show (do let b4 ← (if (2#usize) = 2#usize then backend.avx2.ntt.barrett_block b3 bm round qv
             else ok b3)
           let half1 ← 2#usize / 2#usize
           let level1 ← 2#usize + 1#usize
           backend.avx2.ntt.ntt_block_loop0 SECOND b4 qv bm round k3 half1 level1)
      ⦃ (r : Array I16 256#usize) => BlockBnd r 7906 ⦄
  rw [if_pos rfl]
  apply WP.spec_bind (barrett_block_bnd b3 bm round qv 7681 17474 hQ hM hRnd
    (by norm_num) (by norm_num) (by decide) (by norm_num) (by norm_num) (by norm_num))
  intro b4 hb4
  rw [show (2#usize / 2#usize : Result Usize) = ok 1#usize from rfl, bind_tc_ok,
    show (2#usize + 1#usize : Result Usize) = ok 3#usize from
      usize_add_lit (by scalar_tac) (by rfl), bind_tc_ok]
  -- level 3, `half = 1`, from a centred block again
  unfold backend.avx2.ntt.ntt_block_loop0
  rw [if_pos (by scalar_tac)]
  apply WP.spec_bind (ntt_block_loop0_loop0_bnd SECOND b4 qv k3 1#usize 0#usize
    7681 3840 3840 4066 hQ (by norm_num) (by norm_num) (by norm_num) s1.1 s1.2.1 s1.2.2
    hzeta (by norm_num) (by norm_num) (by norm_num) (by scalar_tac)
    (initSplit (by simp) (hb4.mono (by norm_num))))
  rintro ⟨b5, k5⟩ ⟨hb5, hk5⟩
  simp only at hb5 hk5
  show (do let b6 ← (if (3#usize) = 2#usize then backend.avx2.ntt.barrett_block b5 bm round qv
             else ok b5)
           let half1 ← 1#usize / 2#usize
           let level1 ← 3#usize + 1#usize
           backend.avx2.ntt.ntt_block_loop0 SECOND b6 qv bm round k5 half1 level1)
      ⦃ (r : Array I16 256#usize) => BlockBnd r 7906 ⦄
  rw [if_neg (by decide), bind_tc_ok,
    show (1#usize / 2#usize : Result Usize) = ok 0#usize from rfl, bind_tc_ok,
    show (3#usize + 1#usize : Result Usize) = ok 4#usize from
      usize_add_lit (by scalar_tac) (by rfl), bind_tc_ok]
  -- `half = 0`: the loop is done
  unfold backend.avx2.ntt.ntt_block_loop0
  rw [if_neg (by scalar_tac)]
  simp only [WP.spec_ok]
  exact hb5

/-! ## `ntt_block`

The whole forward transform of one block, for `q₁ = 7681` — the prime whose lane budget binds.
The chain: `7906` after the horizontal half, unchanged by the transpose, then `12210 → 16766 →
21589` across the three vertical levels, re-centred to `3840`, one more level to `7906`,
transposed, and re-centred.  So `ntt_block` leaves every coefficient centred, which is what its
Rust doc comment claims and what the next stage assumes. -/

theorem ntt_block_bnd_q1 (b : Array I16 256#usize)
    (hzeta : ∀ kk : Usize, kk.val < 256 → ∃ zi zqi : I16,
      backend.crt.zeta false kk = ok zi ∧ backend.crt.zeta_q false kk = ok zqi ∧
      |zi.val| ≤ 3840 ∧ (2 ^ 16 : ℤ) ∣ (zqi.val * 7681 - zi.val))
    (htbl8 : ∃ z zq,
      (do let t ← backend.avx2.ntt.FWD8_Q1; backend.avx2.ntt.ld_tbl t 0#usize) = ok (z, zq) ∧
        PsiOk z zq 7681 3840)
    (htbl4 : ∀ h : Usize, h.val < 2 → ∃ z zq,
      (do let t ← backend.avx2.ntt.FWD4_Q1; backend.avx2.ntt.ld_tbl t h) = ok (z, zq) ∧
        PsiOk z zq 7681 3840)
    (htbl2 : ∀ h : Usize, h.val < 4 → ∃ z zq,
      (do let t ← backend.avx2.ntt.FWD2_Q1; backend.avx2.ntt.ld_tbl t h) = ok (z, zq) ∧
        PsiOk z zq 7681 3840)
    (htbl1 : ∀ h : Usize, h.val < 8 → ∃ z zq,
      (do let t ← backend.avx2.ntt.FWD1_Q1; backend.avx2.ntt.ld_tbl t h) = ok (z, zq) ∧
        PsiOk z zq 7681 3840)
    (hb : BlockBnd b 3840) :
    backend.avx2.ntt.ntt_block false b
      ⦃ (r : Array I16 256#usize) => BlockBnd r 3840 ⦄ := by
  obtain ⟨s1, s2, s3, s4, -, -⟩ := growth_q1
  unfold backend.avx2.ntt.ntt_block backend.crt.q backend.crt.barrett_m
  simp only [Bool.false_eq_true, reduceIte, bind_tc_ok]
  obtain ⟨qv, hqv, hqvl⟩ := set1_epi16_spec backend.crt.Q1
  rw [hqv, bind_tc_ok]
  obtain ⟨bm, hbm, hbml⟩ := set1_epi16_spec backend.crt.Q1_BARRETT_M
  rw [hbm, bind_tc_ok]
  have hSH : (backend.crt.BARRETT_SH : I32).val = 11 := by
    simp only [backend.crt.BARRETT_SH]; rfl
  step*
  have hi2e : i2 = 10#i32 := IScalar.eq_of_val_eq (by rw [i2_post, hSH]; rfl)
  rw [hi2e, show (1#i16 <<< (10#i32) : Result I16) = ok 1024#i16 from rfl, bind_tc_ok]
  obtain ⟨rnd, hrnd, hrndl⟩ := set1_epi16_spec 1024#i16
  rw [hrnd, bind_tc_ok]
  -- the three broadcast constants, as lane facts
  have hQ : ∀ j < 16, (lane16 qv j).toInt = 7681 := fun j hj => by rw [hqvl j hj]; simp only [backend.crt.Q1]; decide
  have hM : ∀ j < 16, (lane16 bm j).toInt = 17474 := fun j hj => by rw [hbml j hj]; simp only [backend.crt.Q1_BARRETT_M]; decide
  have hRnd : ∀ j < 16, (lane16 rnd j).toInt = 2 ^ 10 := fun j hj => by
    rw [hrndl j hj]; decide
  -- the horizontal half, then the transpose
  apply WP.spec_bind (ntt_block_loop0_bnd_q1 false b qv bm rnd hQ hM hRnd hzeta hb)
  intro b1 hb1
  apply WP.spec_bind (transpose16_bnd b1 hb1)
  intro b2 hb2
  -- three vertical levels
  apply WP.spec_bind (ntt_block_loop1_bnd false { start := 0#usize, «end» := 8#usize } b2 qv
    7681 3840 7906 4304 hQ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    s2.1 s2.2.1 s2.2.2 htbl8 rfl (initSplit (by simp) hb2))
  intro b3 hb3
  apply WP.spec_bind (ntt_block_loop2_bnd false { start := 0#usize, «end» := 2#usize } b3 qv
    7681 3840 12210 4556 hQ (by norm_num) (by norm_num) (by norm_num)
    s3.1 s3.2.1 s3.2.2 htbl4 rfl (by decide) (initSplit (by simp) hb3))
  intro b4 hb4
  apply WP.spec_bind (ntt_block_loop3_bnd false { start := 0#usize, «end» := 4#usize } b4 qv
    7681 3840 16766 4823 hQ (by norm_num) (by norm_num) (by norm_num)
    s4.1 s4.2.1 s4.2.2 htbl2 rfl (by decide) (initSplit (by simp) hb4))
  intro b5 hb5
  -- re-centre, the last level, transpose, re-centre
  apply WP.spec_bind (barrett_block_bnd b5 bm rnd qv 7681 17474 hQ hM hRnd
    (by norm_num) (by norm_num) (by decide) (by norm_num) (by norm_num) (by norm_num))
  intro b6 hb6
  apply WP.spec_bind (ntt_block_loop4_bnd false { start := 0#usize, «end» := 8#usize } b6 qv
    7681 3840 3840 4066 hQ (by norm_num) (by norm_num) (by norm_num)
    s1.1 s1.2.1 s1.2.2 htbl1 rfl (initSplit (by simp) (hb6.mono (by norm_num))))
  intro b7 hb7
  apply WP.spec_bind (transpose16_bnd b7 hb7)
  intro b8 hb8
  apply WP.spec_mono (barrett_block_bnd b8 bm rnd qv 7681 17474 hQ hM hRnd
    (by norm_num) (by norm_num) (by decide) (by norm_num) (by norm_num) (by norm_num))
  intro r hr
  exact hr.mono (by norm_num)

end Kopis.Avx2