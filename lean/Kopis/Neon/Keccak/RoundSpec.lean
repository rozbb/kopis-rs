/-
  # Kopis/Neon/Keccak/RoundSpec.lean — `keccak::round` is one Keccak-p round.

  The theorem the rest of the NEON Keccak proof rests on.  `Kopis/Neon/Keccak/State.lean` gives
  the dictionary between the 25 registers and two `Words`; this file walks the 65 intrinsic
  operations and lands on `RndW`.
-/
import Kopis.Neon.Keccak.State
import Kopis.Keccak.Const
import Mathlib.Tactic.IntervalCases

open Aeneas Aeneas.Std Result
open RustKopisNeon
open RustKopisNeon.backend.neon.intrinsics
open Kopis.Bits

namespace Kopis.Neon.Keccak

open Kopis.Keccak
open Spec.SHA3

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

/-! ## The round constant

`round_const` reads `RC[24 − ROUNDS + round] = RC[12 + round]`, so the Rust's `round` is the
spec's `iᵣ` shifted by twelve — Keccak-p[1600, 12] is the *last* twelve rounds of Keccak-f. -/

unseal backend.neon.keccak.RC in
/-- The NEON extraction's `RC` table agrees with the transcription in `Kopis/Keccak/Const.lean`. -/
theorem neon_RC_eq (r : ℕ) (hr : r < 12) :
    (backend.neon.keccak.RC.val[12 + r]!).bv = rustRC[r]'(by omega) := by
  interval_cases r <;> decide +kernel +revert

unseal backend.neon.keccak.ROUNDS in
theorem round_const_spec (r : Std.Usize) (hr : r.val < 12) :
    backend.neon.keccak.round_const r
      ⦃ (v : Vec128) => ∀ l < 2, lane64 v l = rcWord (12 + r.val) ⦄ := by
  unfold backend.neon.keccak.round_const
  rw [show massert (r < backend.neon.keccak.ROUNDS) = ok () from by
      simp only [massert, show backend.neon.keccak.ROUNDS = 12#usize from by decide,
        if_pos (show r < 12#usize by scalar_tac)], bind_tc_ok,
    show backend.neon.keccak.ROUNDS = 12#usize from by decide]
  let* ⟨ i, hi ⟩ ← Std.Usize.sub_spec (x := 24#usize) (y := 12#usize) (by scalar_tac)
  let* ⟨ i1, hi1 ⟩ ← Std.Usize.add_spec (x := i) (y := r) (by scalar_tac)
  have hi1v : i1.val = 12 + r.val := by scalar_tac
  obtain ⟨w, hw, hwv⟩ := WP.spec_imp_exists
    (Array.index_usize_spec backend.neon.keccak.RC i1 (by simp [Array.length]; omega))
  rw [hw, bind_tc_ok]
  obtain ⟨v, hv, hvl⟩ := dup_n_u64_spec w
  rw [hv]
  refine (WP.spec_ok _).mpr (fun l hl => ?_)
  have hidx : w = backend.neon.keccak.RC.val[12 + r.val]! := by
    rw [hwv, ← getElem!_pos backend.neon.keccak.RC.val i1.val
      (by have := backend.neon.keccak.RC.property; scalar_tac), hi1v]
  rw [hvl l hl, hidx, neon_RC_eq r.val hr, rcWord_eq_rustRC r.val hr]

/-! ## The round — scaffolding notes

`round_spec` itself is not here yet.  What *is* established, and was checked against the
extraction, is how to walk it:

    unfold backend.neon.keccak.round
    repeat (first
      | (apply WP.spec_bind (xar_step _ _ _ (by decide) (by decide)); intro _ _)
      | (apply WP.spec_bind (eor_step _ _); intro _ _)
      | step)

Plain `step*` stops at the first `xar`: `xar_step` carries two side hypotheses (`0 ≤ IMM.val`,
`IMM.val ≤ 63`) that aeneas's `step` will not discharge, and `@[step]` alone does not help.  They
cannot be dropped — `xar_spec` is an axiom that says nothing outside that range, so there is no
hypothesis-free variant to state.  Supplying them explicitly with `(by decide)` inside a `repeat`
alternative walks all 25 `xar`s; the `IMM` is fixed by unification with the goal, so one
alternative covers every rotation amount.

After the walk the goal is a single `WP.spec_ok` over the 26 `Array.update`s, with every register
named and its lane equation in context.  From there: collapse the updates with
`simp +decide only [getElem!_list_set, …]` (`+decide`, not plain `simp only` — the side condition
is a bound on the *write* index, which plain `simp only` cannot discharge, so the lemma silently
never fires), then close each of the 25 per-lane goals with `parity_of`, `dTerm_of`, `tVal_of`,
`chiRow_of` from `State.lean`, ending at `RndW_fused`.  Fold the register side *into* the spec's
vocabulary, never the other way round. -/

set_option maxRecDepth 1000000 in
theorem round_spec (src dst : Std.Array Vec128 25#usize) (rc : Vec128) (iᵣ : ℕ)
    (l : ℕ) (hl : l < 2) (hrc : lane64 rc l = rcWord iᵣ) :
    backend.neon.keccak.round src dst rc
      ⦃ (r : Std.Array Vec128 25#usize) => ∀ x y : Fin 5,
          stateWords r l x y = RndW (stateWords src l) iᵣ x y ⦄ := by
  unfold backend.neon.keccak.round
  step*
  all_goals try scalar_tac
  rename_i x y
  -- θ: the five column parities
  have hc0 : ∀ i, lane64 c0 i = parity (stateWords src i) 0 :=
    parity_of src 0 v v1 v2 v4 v5 v3 c0
      (lane_read src 0 0 v v_post) (lane_read src 0 1 v1 v1_post) (lane_read src 0 2 v2 v2_post)
      (lane_read src 0 3 v4 v4_post) (lane_read src 0 4 v5 v5_post) v3_post c0_post
  have hc1 : ∀ i, lane64 c1 i = parity (stateWords src i) 1 :=
    parity_of src 1 v6 v7 v8 v10 v11 v9 c1
      (lane_read src 1 0 v6 v6_post) (lane_read src 1 1 v7 v7_post) (lane_read src 1 2 v8 v8_post)
      (lane_read src 1 3 v10 v10_post) (lane_read src 1 4 v11 v11_post) v9_post c1_post
  have hc2 : ∀ i, lane64 c2 i = parity (stateWords src i) 2 :=
    parity_of src 2 v12 v13 v14 v16 v17 v15 c2
      (lane_read src 2 0 v12 v12_post) (lane_read src 2 1 v13 v13_post) (lane_read src 2 2 v14 v14_post)
      (lane_read src 2 3 v16 v16_post) (lane_read src 2 4 v17 v17_post) v15_post c2_post
  have hc3 : ∀ i, lane64 c3 i = parity (stateWords src i) 3 :=
    parity_of src 3 v18 v19 v20 v22 v23 v21 c3
      (lane_read src 3 0 v18 v18_post) (lane_read src 3 1 v19 v19_post) (lane_read src 3 2 v20 v20_post)
      (lane_read src 3 3 v22 v22_post) (lane_read src 3 4 v23 v23_post) v21_post c3_post
  have hc4 : ∀ i, lane64 c4 i = parity (stateWords src i) 4 :=
    parity_of src 4 v24 v25 v26 v28 v29 v27 c4
      (lane_read src 4 0 v24 v24_post) (lane_read src 4 1 v25 v25_post) (lane_read src 4 2 v26 v26_post)
      (lane_read src 4 3 v28 v28_post) (lane_read src 4 4 v29 v29_post) v27_post c4_post
  -- θ: the five mixing terms
  have hd0 : ∀ i < 2, lane64 v30 i = dTerm (stateWords src i) 0 :=
    dTerm_of src 0 c4 c1 v30 hc4 hc1 v30_post
  have hd1 : ∀ i < 2, lane64 v31 i = dTerm (stateWords src i) 1 :=
    dTerm_of src 1 c0 c2 v31 hc0 hc2 v31_post
  have hd2 : ∀ i < 2, lane64 v32 i = dTerm (stateWords src i) 2 :=
    dTerm_of src 2 c1 c3 v32 hc1 hc3 v32_post
  have hd3 : ∀ i < 2, lane64 v33 i = dTerm (stateWords src i) 3 :=
    dTerm_of src 3 c2 c4 v33 hc2 hc4 v33_post
  have hd4 : ∀ i < 2, lane64 v34 i = dTerm (stateWords src i) 4 :=
    dTerm_of src 4 c3 c0 v34 hc3 hc0 v34_post
  -- the D-vector lookups are the registers `rax1` produced
  have hk00 : i = 0#usize :=
    UScalar.eq_of_val_eq (by rw [i_post]; decide)
  subst hk00
  have hlk00 : v35 = v30 := by rw [v35_post]; rfl
  have hk01 : i1 = 1#usize :=
    UScalar.eq_of_val_eq (by rw [i1_post]; decide)
  subst hk01
  have hlk01 : v36 = v31 := by rw [v36_post]; rfl
  have hk02 : i2 = 2#usize :=
    UScalar.eq_of_val_eq (by rw [i2_post]; decide)
  subst hk02
  have hlk02 : v37 = v32 := by rw [v37_post]; rfl
  have hk03 : i3 = 3#usize :=
    UScalar.eq_of_val_eq (by rw [i3_post]; decide)
  subst hk03
  have hlk03 : v38 = v33 := by rw [v38_post]; rfl
  have hk04 : i4 = 4#usize :=
    UScalar.eq_of_val_eq (by rw [i4_post]; decide)
  subst hk04
  have hlk04 : v39 = v34 := by rw [v39_post]; rfl
  have hk10 : i10 = 3#usize :=
    UScalar.eq_of_val_eq (by rw [i10_post]; decide)
  subst hk10
  have hlk10 : v45 = v33 := by rw [v45_post]; rfl
  have hk11 : i11 = 4#usize :=
    UScalar.eq_of_val_eq (by rw [i11_post]; decide)
  subst hk11
  have hlk11 : v46 = v34 := by rw [v46_post]; rfl
  have hk12 : i12 = 0#usize :=
    UScalar.eq_of_val_eq (by rw [i12_post]; decide)
  subst hk12
  have hlk12 : v47 = v30 := by rw [v47_post]; rfl
  have hk13 : i13 = 1#usize :=
    UScalar.eq_of_val_eq (by rw [i13_post]; decide)
  subst hk13
  have hlk13 : v48 = v31 := by rw [v48_post]; rfl
  have hk14 : i14 = 2#usize :=
    UScalar.eq_of_val_eq (by rw [i14_post]; decide)
  subst hk14
  have hlk14 : v49 = v32 := by rw [v49_post]; rfl
  have hk20 : i20 = 1#usize :=
    UScalar.eq_of_val_eq (by rw [i20_post]; decide)
  subst hk20
  have hlk20 : v55 = v31 := by rw [v55_post]; rfl
  have hk21 : i21 = 2#usize :=
    UScalar.eq_of_val_eq (by rw [i21_post]; decide)
  subst hk21
  have hlk21 : v56 = v32 := by rw [v56_post]; rfl
  have hk22 : i22 = 3#usize :=
    UScalar.eq_of_val_eq (by rw [i22_post]; decide)
  subst hk22
  have hlk22 : v57 = v33 := by rw [v57_post]; rfl
  have hk23 : i23 = 4#usize :=
    UScalar.eq_of_val_eq (by rw [i23_post]; decide)
  subst hk23
  have hlk23 : v58 = v34 := by rw [v58_post]; rfl
  have hk24 : i24 = 0#usize :=
    UScalar.eq_of_val_eq (by rw [i24_post]; decide)
  subst hk24
  have hlk24 : v59 = v30 := by rw [v59_post]; rfl
  have hk30 : i30 = 4#usize :=
    UScalar.eq_of_val_eq (by rw [i30_post]; decide)
  subst hk30
  have hlk30 : v65 = v34 := by rw [v65_post]; rfl
  have hk31 : i31 = 0#usize :=
    UScalar.eq_of_val_eq (by rw [i31_post]; decide)
  subst hk31
  have hlk31 : v66 = v30 := by rw [v66_post]; rfl
  have hk32 : i32 = 1#usize :=
    UScalar.eq_of_val_eq (by rw [i32_post]; decide)
  subst hk32
  have hlk32 : v67 = v31 := by rw [v67_post]; rfl
  have hk33 : i33 = 2#usize :=
    UScalar.eq_of_val_eq (by rw [i33_post]; decide)
  subst hk33
  have hlk33 : v68 = v32 := by rw [v68_post]; rfl
  have hk34 : i34 = 3#usize :=
    UScalar.eq_of_val_eq (by rw [i34_post]; decide)
  subst hk34
  have hlk34 : v69 = v33 := by rw [v69_post]; rfl
  have hk40 : i40 = 2#usize :=
    UScalar.eq_of_val_eq (by rw [i40_post]; decide)
  subst hk40
  have hlk40 : v75 = v32 := by rw [v75_post]; rfl
  have hk41 : i41 = 3#usize :=
    UScalar.eq_of_val_eq (by rw [i41_post]; decide)
  subst hk41
  have hlk41 : v76 = v33 := by rw [v76_post]; rfl
  have hk42 : i42 = 4#usize :=
    UScalar.eq_of_val_eq (by rw [i42_post]; decide)
  subst hk42
  have hlk42 : v77 = v34 := by rw [v77_post]; rfl
  have hk43 : i43 = 0#usize :=
    UScalar.eq_of_val_eq (by rw [i43_post]; decide)
  subst hk43
  have hlk43 : v78 = v30 := by rw [v78_post]; rfl
  have hk44 : i44 = 1#usize :=
    UScalar.eq_of_val_eq (by rw [i44_post]; decide)
  subst hk44
  have hlk44 : v79 = v31 := by rw [v79_post]; rfl
  -- ρπ: the twenty-five fused temporaries
  have ht00 : ∀ i < 2, lane64 t0 i = tVal (stateWords src i) 0 0 :=
    tVal_of src 0 0 v v30 t0
      (lane_read src 0 0 v v_post) hd0
      (by intro i hi; rw [t0_post i hi, hlk00]; congr 1) (by decide)
  have ht01 : ∀ i < 2, lane64 t1 i = tVal (stateWords src i) 0 1 :=
    tVal_of src 0 1 v7 v31 t1
      (lane_read src 1 1 v7 v7_post) hd1
      (by intro i hi; rw [t1_post i hi, hlk01]; congr 1) (by decide)
  have ht02 : ∀ i < 2, lane64 t2 i = tVal (stateWords src i) 0 2 :=
    tVal_of src 0 2 v14 v32 t2
      (lane_read src 2 2 v14 v14_post) hd2
      (by intro i hi; rw [t2_post i hi, hlk02]; congr 1) (by decide)
  have ht03 : ∀ i < 2, lane64 t3 i = tVal (stateWords src i) 0 3 :=
    tVal_of src 0 3 v22 v33 t3
      (lane_read src 3 3 v22 v22_post) hd3
      (by intro i hi; rw [t3_post i hi, hlk03]; congr 1) (by decide)
  have ht04 : ∀ i < 2, lane64 t4 i = tVal (stateWords src i) 0 4 :=
    tVal_of src 0 4 v29 v34 t4
      (lane_read src 4 4 v29 v29_post) hd4
      (by intro i hi; rw [t4_post i hi, hlk04]; congr 1) (by decide)
  have ht10 : ∀ i < 2, lane64 t01 i = tVal (stateWords src i) 1 0 :=
    tVal_of src 1 0 v18 v33 t01
      (lane_read src 3 0 v18 v18_post) hd3
      (by intro i hi; rw [t01_post i hi, hlk10]; congr 1) (by decide)
  have ht11 : ∀ i < 2, lane64 t11 i = tVal (stateWords src i) 1 1 :=
    tVal_of src 1 1 v25 v34 t11
      (lane_read src 4 1 v25 v25_post) hd4
      (by intro i hi; rw [t11_post i hi, hlk11]; congr 1) (by decide)
  have ht12 : ∀ i < 2, lane64 t21 i = tVal (stateWords src i) 1 2 :=
    tVal_of src 1 2 v2 v30 t21
      (lane_read src 0 2 v2 v2_post) hd0
      (by intro i hi; rw [t21_post i hi, hlk12]; congr 1) (by decide)
  have ht13 : ∀ i < 2, lane64 t31 i = tVal (stateWords src i) 1 3 :=
    tVal_of src 1 3 v10 v31 t31
      (lane_read src 1 3 v10 v10_post) hd1
      (by intro i hi; rw [t31_post i hi, hlk13]; congr 1) (by decide)
  have ht14 : ∀ i < 2, lane64 t41 i = tVal (stateWords src i) 1 4 :=
    tVal_of src 1 4 v17 v32 t41
      (lane_read src 2 4 v17 v17_post) hd2
      (by intro i hi; rw [t41_post i hi, hlk14]; congr 1) (by decide)
  have ht20 : ∀ i < 2, lane64 t02 i = tVal (stateWords src i) 2 0 :=
    tVal_of src 2 0 v6 v31 t02
      (lane_read src 1 0 v6 v6_post) hd1
      (by intro i hi; rw [t02_post i hi, hlk20]; congr 1) (by decide)
  have ht21 : ∀ i < 2, lane64 t12 i = tVal (stateWords src i) 2 1 :=
    tVal_of src 2 1 v13 v32 t12
      (lane_read src 2 1 v13 v13_post) hd2
      (by intro i hi; rw [t12_post i hi, hlk21]; congr 1) (by decide)
  have ht22 : ∀ i < 2, lane64 t22 i = tVal (stateWords src i) 2 2 :=
    tVal_of src 2 2 v20 v33 t22
      (lane_read src 3 2 v20 v20_post) hd3
      (by intro i hi; rw [t22_post i hi, hlk22]; congr 1) (by decide)
  have ht23 : ∀ i < 2, lane64 t32 i = tVal (stateWords src i) 2 3 :=
    tVal_of src 2 3 v28 v34 t32
      (lane_read src 4 3 v28 v28_post) hd4
      (by intro i hi; rw [t32_post i hi, hlk23]; congr 1) (by decide)
  have ht24 : ∀ i < 2, lane64 t42 i = tVal (stateWords src i) 2 4 :=
    tVal_of src 2 4 v5 v30 t42
      (lane_read src 0 4 v5 v5_post) hd0
      (by intro i hi; rw [t42_post i hi, hlk24]; congr 1) (by decide)
  have ht30 : ∀ i < 2, lane64 t03 i = tVal (stateWords src i) 3 0 :=
    tVal_of src 3 0 v24 v34 t03
      (lane_read src 4 0 v24 v24_post) hd4
      (by intro i hi; rw [t03_post i hi, hlk30]; congr 1) (by decide)
  have ht31 : ∀ i < 2, lane64 t13 i = tVal (stateWords src i) 3 1 :=
    tVal_of src 3 1 v1 v30 t13
      (lane_read src 0 1 v1 v1_post) hd0
      (by intro i hi; rw [t13_post i hi, hlk31]; congr 1) (by decide)
  have ht32 : ∀ i < 2, lane64 t23 i = tVal (stateWords src i) 3 2 :=
    tVal_of src 3 2 v8 v31 t23
      (lane_read src 1 2 v8 v8_post) hd1
      (by intro i hi; rw [t23_post i hi, hlk32]; congr 1) (by decide)
  have ht33 : ∀ i < 2, lane64 t33 i = tVal (stateWords src i) 3 3 :=
    tVal_of src 3 3 v16 v32 t33
      (lane_read src 2 3 v16 v16_post) hd2
      (by intro i hi; rw [t33_post i hi, hlk33]; congr 1) (by decide)
  have ht34 : ∀ i < 2, lane64 t43 i = tVal (stateWords src i) 3 4 :=
    tVal_of src 3 4 v23 v33 t43
      (lane_read src 3 4 v23 v23_post) hd3
      (by intro i hi; rw [t43_post i hi, hlk34]; congr 1) (by decide)
  have ht40 : ∀ i < 2, lane64 t04 i = tVal (stateWords src i) 4 0 :=
    tVal_of src 4 0 v12 v32 t04
      (lane_read src 2 0 v12 v12_post) hd2
      (by intro i hi; rw [t04_post i hi, hlk40]; congr 1) (by decide)
  have ht41 : ∀ i < 2, lane64 t14 i = tVal (stateWords src i) 4 1 :=
    tVal_of src 4 1 v19 v33 t14
      (lane_read src 3 1 v19 v19_post) hd3
      (by intro i hi; rw [t14_post i hi, hlk41]; congr 1) (by decide)
  have ht42 : ∀ i < 2, lane64 t24 i = tVal (stateWords src i) 4 2 :=
    tVal_of src 4 2 v26 v34 t24
      (lane_read src 4 2 v26 v26_post) hd4
      (by intro i hi; rw [t24_post i hi, hlk42]; congr 1) (by decide)
  have ht43 : ∀ i < 2, lane64 t34 i = tVal (stateWords src i) 4 3 :=
    tVal_of src 4 3 v4 v30 t34
      (lane_read src 0 3 v4 v4_post) hd0
      (by intro i hi; rw [t34_post i hi, hlk43]; congr 1) (by decide)
  have ht44 : ∀ i < 2, lane64 t44 i = tVal (stateWords src i) 4 4 :=
    tVal_of src 4 4 v11 v31 t44
      (lane_read src 1 4 v11 v11_post) hd1
      (by intro i hi; rw [t44_post i hi, hlk44]; congr 1) (by decide)
  -- χ: the twenty-five outputs
  have ho00 : ∀ i < 2, lane64 v40 i = chiRow (stateWords src i) 0 0 :=
    chiRow_of src 0 0 t0 t1 t2 v40
      ht00 ht01 ht02 v40_post
  have ho01 : ∀ i < 2, lane64 v41 i = chiRow (stateWords src i) 0 1 :=
    chiRow_of src 0 1 t1 t2 t3 v41
      ht01 ht02 ht03 v41_post
  have ho02 : ∀ i < 2, lane64 v42 i = chiRow (stateWords src i) 0 2 :=
    chiRow_of src 0 2 t2 t3 t4 v42
      ht02 ht03 ht04 v42_post
  have ho03 : ∀ i < 2, lane64 v43 i = chiRow (stateWords src i) 0 3 :=
    chiRow_of src 0 3 t3 t4 t0 v43
      ht03 ht04 ht00 v43_post
  have ho04 : ∀ i < 2, lane64 v44 i = chiRow (stateWords src i) 0 4 :=
    chiRow_of src 0 4 t4 t0 t1 v44
      ht04 ht00 ht01 v44_post
  have ho10 : ∀ i < 2, lane64 v50 i = chiRow (stateWords src i) 1 0 :=
    chiRow_of src 1 0 t01 t11 t21 v50
      ht10 ht11 ht12 v50_post
  have ho11 : ∀ i < 2, lane64 v51 i = chiRow (stateWords src i) 1 1 :=
    chiRow_of src 1 1 t11 t21 t31 v51
      ht11 ht12 ht13 v51_post
  have ho12 : ∀ i < 2, lane64 v52 i = chiRow (stateWords src i) 1 2 :=
    chiRow_of src 1 2 t21 t31 t41 v52
      ht12 ht13 ht14 v52_post
  have ho13 : ∀ i < 2, lane64 v53 i = chiRow (stateWords src i) 1 3 :=
    chiRow_of src 1 3 t31 t41 t01 v53
      ht13 ht14 ht10 v53_post
  have ho14 : ∀ i < 2, lane64 v54 i = chiRow (stateWords src i) 1 4 :=
    chiRow_of src 1 4 t41 t01 t11 v54
      ht14 ht10 ht11 v54_post
  have ho20 : ∀ i < 2, lane64 v60 i = chiRow (stateWords src i) 2 0 :=
    chiRow_of src 2 0 t02 t12 t22 v60
      ht20 ht21 ht22 v60_post
  have ho21 : ∀ i < 2, lane64 v61 i = chiRow (stateWords src i) 2 1 :=
    chiRow_of src 2 1 t12 t22 t32 v61
      ht21 ht22 ht23 v61_post
  have ho22 : ∀ i < 2, lane64 v62 i = chiRow (stateWords src i) 2 2 :=
    chiRow_of src 2 2 t22 t32 t42 v62
      ht22 ht23 ht24 v62_post
  have ho23 : ∀ i < 2, lane64 v63 i = chiRow (stateWords src i) 2 3 :=
    chiRow_of src 2 3 t32 t42 t02 v63
      ht23 ht24 ht20 v63_post
  have ho24 : ∀ i < 2, lane64 v64 i = chiRow (stateWords src i) 2 4 :=
    chiRow_of src 2 4 t42 t02 t12 v64
      ht24 ht20 ht21 v64_post
  have ho30 : ∀ i < 2, lane64 v70 i = chiRow (stateWords src i) 3 0 :=
    chiRow_of src 3 0 t03 t13 t23 v70
      ht30 ht31 ht32 v70_post
  have ho31 : ∀ i < 2, lane64 v71 i = chiRow (stateWords src i) 3 1 :=
    chiRow_of src 3 1 t13 t23 t33 v71
      ht31 ht32 ht33 v71_post
  have ho32 : ∀ i < 2, lane64 v72 i = chiRow (stateWords src i) 3 2 :=
    chiRow_of src 3 2 t23 t33 t43 v72
      ht32 ht33 ht34 v72_post
  have ho33 : ∀ i < 2, lane64 v73 i = chiRow (stateWords src i) 3 3 :=
    chiRow_of src 3 3 t33 t43 t03 v73
      ht33 ht34 ht30 v73_post
  have ho34 : ∀ i < 2, lane64 v74 i = chiRow (stateWords src i) 3 4 :=
    chiRow_of src 3 4 t43 t03 t13 v74
      ht34 ht30 ht31 v74_post
  have ho40 : ∀ i < 2, lane64 v80 i = chiRow (stateWords src i) 4 0 :=
    chiRow_of src 4 0 t04 t14 t24 v80
      ht40 ht41 ht42 v80_post
  have ho41 : ∀ i < 2, lane64 v81 i = chiRow (stateWords src i) 4 1 :=
    chiRow_of src 4 1 t14 t24 t34 v81
      ht41 ht42 ht43 v81_post
  have ho42 : ∀ i < 2, lane64 v82 i = chiRow (stateWords src i) 4 2 :=
    chiRow_of src 4 2 t24 t34 t44 v82
      ht42 ht43 ht44 v82_post
  have ho43 : ∀ i < 2, lane64 v83 i = chiRow (stateWords src i) 4 3 :=
    chiRow_of src 4 3 t34 t44 t04 v83
      ht43 ht44 ht40 v83_post
  have ho44 : ∀ i < 2, lane64 v84 i = chiRow (stateWords src i) 4 4 :=
    chiRow_of src 4 4 t44 t04 t14 v84
      ht44 ht40 ht41 v84_post
  simp only [stateWords_apply, r_post, dst25_post, dst24_post, dst23_post, dst22_post, dst21_post, dst20_post, dst19_post, dst18_post, dst17_post, dst16_post, dst15_post, dst14_post, dst13_post, dst12_post, dst11_post, dst10_post, dst9_post, dst8_post, dst7_post, dst6_post, dst5_post, dst4_post, dst3_post, dst2_post, dst1_post,
    Std.Array.set_val_eq, i5_post, i6_post, i7_post, i8_post, i9_post, i15_post, i16_post, i17_post, i18_post, i19_post, i25_post, i26_post, i27_post, i28_post, i29_post, i35_post, i36_post, i37_post, i38_post, i39_post, i45_post, i46_post, i47_post, i48_post, i49_post]
  have hdl : dst.val.length = 25 := dst.property
  fin_cases x <;> fin_cases y <;>
    simp +decide only [idx, getElem!_list_set, List.length_set, hdl]
  · rw [RndW_fused]
    norm_num
    have hv85 : v85 = v40 := by
      rw [v85_post, ← getElem!_pos (dst25.val) 0 (by have := dst25.property; scalar_tac)]
      simp +decide only [dst25_post, dst24_post, dst23_post, dst22_post, dst21_post, dst20_post, dst19_post, dst18_post, dst17_post, dst16_post, dst15_post, dst14_post, dst13_post, dst12_post, dst11_post, dst10_post, dst9_post, dst8_post, dst7_post, dst6_post, dst5_post, dst4_post, dst3_post, dst2_post, dst1_post, Std.Array.set_val_eq, i5_post, i6_post, i7_post, i8_post, i9_post, i15_post, i16_post, i17_post, i18_post, i19_post, i25_post, i26_post, i27_post, i28_post, i29_post, i35_post, i36_post, i37_post, i38_post, i39_post, i45_post, i46_post, i47_post, i48_post, i49_post,
        getElem!_list_set, List.length_set, hdl, reduceIte]
    rw [v86_post l, hv85, ho00 l hl, hrc]
  · rw [RndW_fused]
    norm_num
    exact ho10 l hl
  · rw [RndW_fused]
    norm_num
    exact ho20 l hl
  · rw [RndW_fused]
    norm_num
    exact ho30 l hl
  · rw [RndW_fused]
    norm_num
    exact ho40 l hl
  · rw [RndW_fused]
    norm_num
    exact ho01 l hl
  · rw [RndW_fused]
    norm_num
    exact ho11 l hl
  · rw [RndW_fused]
    norm_num
    exact ho21 l hl
  · rw [RndW_fused]
    norm_num
    exact ho31 l hl
  · rw [RndW_fused]
    norm_num
    exact ho41 l hl
  · rw [RndW_fused]
    norm_num
    exact ho02 l hl
  · rw [RndW_fused]
    norm_num
    exact ho12 l hl
  · rw [RndW_fused]
    norm_num
    exact ho22 l hl
  · rw [RndW_fused]
    norm_num
    exact ho32 l hl
  · rw [RndW_fused]
    norm_num
    exact ho42 l hl
  · rw [RndW_fused]
    norm_num
    exact ho03 l hl
  · rw [RndW_fused]
    norm_num
    exact ho13 l hl
  · rw [RndW_fused]
    norm_num
    exact ho23 l hl
  · rw [RndW_fused]
    norm_num
    exact ho33 l hl
  · rw [RndW_fused]
    norm_num
    exact ho43 l hl
  · rw [RndW_fused]
    norm_num
    exact ho04 l hl
  · rw [RndW_fused]
    norm_num
    exact ho14 l hl
  · rw [RndW_fused]
    norm_num
    exact ho24 l hl
  · rw [RndW_fused]
    norm_num
    exact ho34 l hl
  · rw [RndW_fused]
    norm_num
    exact ho44 l hl

end Kopis.Neon.Keccak
