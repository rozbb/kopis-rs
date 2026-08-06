/-
  # Kopis/Avx2/Keccak/RoundSpec.lean — `keccak::round` is one Keccak-p round.

  This is the theorem the rest of the AVX2 Keccak proof rests on: the 208 intrinsic operations
  `src/backend/avx2/keccak.rs::round` performs compute, in each of the four 64-bit lanes
  independently, exactly `Rnd` of FIPS 202 §3.3 — read through `Round.lean`'s word form `RndW`
  and `Fused.lean`'s account of how the Rust fuses ρ, π and θ into `chi_row!`.

  `dst` does not appear in the postcondition: every one of its 25 registers is overwritten, which
  is what `State.lean`'s `idx_surjective` certifies.  `l` and `hl : l < 4` are parameters rather
  than `∀ l < 4` inside the postcondition, because `step*` introduces four binders either way and
  with the `∀` inside, `rename_i` binds the proof where the index is meant.

  The shape of the proof is worth stating, since it is entirely mechanical and was generated from
  the extracted body:

  * `step*` walks all 208 operations, given the three `@[step]` wrappers in `Ops.lean`.  It needs
    `maxRecDepth 1000000`; the default 512 is nowhere near enough.
  * The 60 `have`s fold registers *into* the spec's vocabulary with `State.lean`'s `lane_read`,
    `parity_of`, `dTerm_of`, `tVal_of` and `chiRow_of` — five column parities, five θ mixing
    terms, 25 `chi_row!` temporaries, 25 outputs.
  * `fin_cases x <;> fin_cases y` then splits into the 25 lanes, and one `simp +decide` collapses
    the 26 `Array.update`s to the register written at that index.  `+decide` rather than plain
    `simp only` matters: `getElem!_list_set`'s side condition is a bound on the *write* index,
    which `simp only` cannot discharge, so the lemma would silently never fire.
  * Each lane then closes against `RndW_fused`, with `h00` carrying ι's round constant on the
    one lane that gets it.

  Nothing here does AC normalisation, and that is deliberate — see the note in `State.lean`.
-/
import Kopis.Avx2.Keccak.State

open Aeneas Aeneas.Std Result
open RustKopisAvx2
open RustKopisAvx2.backend.avx2.intrinsics
open Kopis.Avx2
open Spec.SHA3

namespace Kopis.Avx2.Keccak

set_option maxHeartbeats 4000000
set_option maxRecDepth 1000000

noncomputable section

/-- **`keccak::round` is one round of Keccak-p[1600, 12] in each of the four lanes.**  `rc` must
carry the round constant of spec round `iᵣ` in every lane, which is what `round_const_spec`
provides. -/
theorem round_spec (src dst : Std.Array Vec256 25#usize) (rc : Vec256) (iᵣ l : ℕ)
    (hl : l < 4) (hrc : ∀ i < 4, lane64 rc i = rcWord iᵣ) :
    backend.avx2.keccak.round src dst rc
      ⦃ (r : Std.Array Vec256 25#usize) => ∀ x y : Fin 5,
          stateWords r l x y = RndW (stateWords src l) iᵣ x y ⦄ := by
  unfold backend.avx2.keccak.round
  step*
  rename_i x y
  have hc0 : ∀ i, lane64 c0 i = parity (stateWords src i) 0 :=
    parity_of src 0 c0 v v1 v3 v4 v7
      (lane_read src 0 0 v v_post) (lane_read src 0 1 v1 v1_post) (lane_read src 0 2 v3 v3_post) (lane_read src 0 3 v4 v4_post) (lane_read src 0 4 v7 v7_post)
      (by rw [c0_post, v6_post, v2_post, v5_post])
  have hc1 : ∀ i, lane64 c1 i = parity (stateWords src i) 1 :=
    parity_of src 1 c1 v8 v9 v11 v12 v15
      (lane_read src 1 0 v8 v8_post) (lane_read src 1 1 v9 v9_post) (lane_read src 1 2 v11 v11_post) (lane_read src 1 3 v12 v12_post) (lane_read src 1 4 v15 v15_post)
      (by rw [c1_post, v14_post, v10_post, v13_post])
  have hc2 : ∀ i, lane64 c2 i = parity (stateWords src i) 2 :=
    parity_of src 2 c2 v16 v17 v19 v20 v23
      (lane_read src 2 0 v16 v16_post) (lane_read src 2 1 v17 v17_post) (lane_read src 2 2 v19 v19_post) (lane_read src 2 3 v20 v20_post) (lane_read src 2 4 v23 v23_post)
      (by rw [c2_post, v22_post, v18_post, v21_post])
  have hc3 : ∀ i, lane64 c3 i = parity (stateWords src i) 3 :=
    parity_of src 3 c3 v24 v25 v27 v28 v31
      (lane_read src 3 0 v24 v24_post) (lane_read src 3 1 v25 v25_post) (lane_read src 3 2 v27 v27_post) (lane_read src 3 3 v28 v28_post) (lane_read src 3 4 v31 v31_post)
      (by rw [c3_post, v30_post, v26_post, v29_post])
  have hc4 : ∀ i, lane64 c4 i = parity (stateWords src i) 4 :=
    parity_of src 4 c4 v32 v33 v35 v36 v39
      (lane_read src 4 0 v32 v32_post) (lane_read src 4 1 v33 v33_post) (lane_read src 4 2 v35 v35_post) (lane_read src 4 3 v36 v36_post) (lane_read src 4 4 v39 v39_post)
      (by rw [c4_post, v38_post, v34_post, v37_post])
  have hd0 : ∀ i < 4, lane64 v41 i = dTerm (stateWords src i) 0 :=
    dTerm_of src 0 c4 c1 v40 v41 hc4 hc1 v40_post v41_post
  have hd1 : ∀ i < 4, lane64 v43 i = dTerm (stateWords src i) 1 :=
    dTerm_of src 1 c0 c2 v42 v43 hc0 hc2 v42_post v43_post
  have hd2 : ∀ i < 4, lane64 v45 i = dTerm (stateWords src i) 2 :=
    dTerm_of src 2 c1 c3 v44 v45 hc1 hc3 v44_post v45_post
  have hd3 : ∀ i < 4, lane64 v47 i = dTerm (stateWords src i) 3 :=
    dTerm_of src 3 c2 c4 v46 v47 hc2 hc4 v46_post v47_post
  have hd4 : ∀ i < 4, lane64 v49 i = dTerm (stateWords src i) 4 :=
    dTerm_of src 4 c3 c0 v48 v49 hc3 hc0 v48_post v49_post
  have hmt0 : v50 = v41 := by simp only [v50_post, i_post]; rfl
  have htt0 : ∀ i < 4, lane64 t0 i = tVal (stateWords src i) 0 0 :=
    tVal_of src 0 0 v v41 v51 t0
      (lane_read src 0 0 v v_post)
      hd0 (by rw [v51_post, hmt0])
      (by exact t0_post)   -- rustTable[0][0].2 reduces to 0
  have hmt1 : v52 = v43 := by simp only [v52_post, i1_post]; rfl
  have htt1 : ∀ i < 4, lane64 t1 i = tVal (stateWords src i) 0 1 :=
    tVal_of src 0 1 v9 v43 v53 t1
      (lane_read src 1 1 v9 v9_post)
      hd1 (by rw [v53_post, hmt1])
      (by exact t1_post)   -- rustTable[0][1].2 reduces to 44
  have hmt2 : v54 = v45 := by simp only [v54_post, i2_post]; rfl
  have htt2 : ∀ i < 4, lane64 t2 i = tVal (stateWords src i) 0 2 :=
    tVal_of src 0 2 v19 v45 v55 t2
      (lane_read src 2 2 v19 v19_post)
      hd2 (by rw [v55_post, hmt2])
      (by exact t2_post)   -- rustTable[0][2].2 reduces to 43
  have hmt3 : v56 = v47 := by simp only [v56_post, i3_post]; rfl
  have htt3 : ∀ i < 4, lane64 t3 i = tVal (stateWords src i) 0 3 :=
    tVal_of src 0 3 v28 v47 v57 t3
      (lane_read src 3 3 v28 v28_post)
      hd3 (by rw [v57_post, hmt3])
      (by exact t3_post)   -- rustTable[0][3].2 reduces to 21
  have hmt4 : v58 = v49 := by simp only [v58_post, i4_post]; rfl
  have htt4 : ∀ i < 4, lane64 t4 i = tVal (stateWords src i) 0 4 :=
    tVal_of src 0 4 v39 v49 v59 t4
      (lane_read src 4 4 v39 v39_post)
      hd4 (by rw [v59_post, hmt4])
      (by exact t4_post)   -- rustTable[0][4].2 reduces to 14
  have hmt01 : v70 = v47 := by simp only [v70_post, i10_post]; rfl
  have htt01 : ∀ i < 4, lane64 t01 i = tVal (stateWords src i) 1 0 :=
    tVal_of src 1 0 v24 v47 v71 t01
      (lane_read src 3 0 v24 v24_post)
      hd3 (by rw [v71_post, hmt01])
      (by exact t01_post)   -- rustTable[1][0].2 reduces to 28
  have hmt11 : v72 = v49 := by simp only [v72_post, i11_post]; rfl
  have htt11 : ∀ i < 4, lane64 t11 i = tVal (stateWords src i) 1 1 :=
    tVal_of src 1 1 v33 v49 v73 t11
      (lane_read src 4 1 v33 v33_post)
      hd4 (by rw [v73_post, hmt11])
      (by exact t11_post)   -- rustTable[1][1].2 reduces to 20
  have hmt21 : v74 = v41 := by simp only [v74_post, i12_post]; rfl
  have htt21 : ∀ i < 4, lane64 t21 i = tVal (stateWords src i) 1 2 :=
    tVal_of src 1 2 v3 v41 v75 t21
      (lane_read src 0 2 v3 v3_post)
      hd0 (by rw [v75_post, hmt21])
      (by exact t21_post)   -- rustTable[1][2].2 reduces to 3
  have hmt31 : v76 = v43 := by simp only [v76_post, i13_post]; rfl
  have htt31 : ∀ i < 4, lane64 t31 i = tVal (stateWords src i) 1 3 :=
    tVal_of src 1 3 v12 v43 v77 t31
      (lane_read src 1 3 v12 v12_post)
      hd1 (by rw [v77_post, hmt31])
      (by exact t31_post)   -- rustTable[1][3].2 reduces to 45
  have hmt41 : v78 = v45 := by simp only [v78_post, i14_post]; rfl
  have htt41 : ∀ i < 4, lane64 t41 i = tVal (stateWords src i) 1 4 :=
    tVal_of src 1 4 v23 v45 v79 t41
      (lane_read src 2 4 v23 v23_post)
      hd2 (by rw [v79_post, hmt41])
      (by exact t41_post)   -- rustTable[1][4].2 reduces to 61
  have hmt02 : v90 = v43 := by simp only [v90_post, i20_post]; rfl
  have htt02 : ∀ i < 4, lane64 t02 i = tVal (stateWords src i) 2 0 :=
    tVal_of src 2 0 v8 v43 v91 t02
      (lane_read src 1 0 v8 v8_post)
      hd1 (by rw [v91_post, hmt02])
      (by exact t02_post)   -- rustTable[2][0].2 reduces to 1
  have hmt12 : v92 = v45 := by simp only [v92_post, i21_post]; rfl
  have htt12 : ∀ i < 4, lane64 t12 i = tVal (stateWords src i) 2 1 :=
    tVal_of src 2 1 v17 v45 v93 t12
      (lane_read src 2 1 v17 v17_post)
      hd2 (by rw [v93_post, hmt12])
      (by exact t12_post)   -- rustTable[2][1].2 reduces to 6
  have hmt22 : v94 = v47 := by simp only [v94_post, i22_post]; rfl
  have htt22 : ∀ i < 4, lane64 t22 i = tVal (stateWords src i) 2 2 :=
    tVal_of src 2 2 v27 v47 v95 t22
      (lane_read src 3 2 v27 v27_post)
      hd3 (by rw [v95_post, hmt22])
      (by exact t22_post)   -- rustTable[2][2].2 reduces to 25
  have hmt32 : v96 = v49 := by simp only [v96_post, i23_post]; rfl
  have htt32 : ∀ i < 4, lane64 t32 i = tVal (stateWords src i) 2 3 :=
    tVal_of src 2 3 v36 v49 v97 t32
      (lane_read src 4 3 v36 v36_post)
      hd4 (by rw [v97_post, hmt32])
      (by exact t32_post)   -- rustTable[2][3].2 reduces to 8
  have hmt42 : v98 = v41 := by simp only [v98_post, i24_post]; rfl
  have htt42 : ∀ i < 4, lane64 t42 i = tVal (stateWords src i) 2 4 :=
    tVal_of src 2 4 v7 v41 v99 t42
      (lane_read src 0 4 v7 v7_post)
      hd0 (by rw [v99_post, hmt42])
      (by exact t42_post)   -- rustTable[2][4].2 reduces to 18
  have hmt03 : v110 = v49 := by simp only [v110_post, i30_post]; rfl
  have htt03 : ∀ i < 4, lane64 t03 i = tVal (stateWords src i) 3 0 :=
    tVal_of src 3 0 v32 v49 v111 t03
      (lane_read src 4 0 v32 v32_post)
      hd4 (by rw [v111_post, hmt03])
      (by exact t03_post)   -- rustTable[3][0].2 reduces to 27
  have hmt13 : v112 = v41 := by simp only [v112_post, i31_post]; rfl
  have htt13 : ∀ i < 4, lane64 t13 i = tVal (stateWords src i) 3 1 :=
    tVal_of src 3 1 v1 v41 v113 t13
      (lane_read src 0 1 v1 v1_post)
      hd0 (by rw [v113_post, hmt13])
      (by exact t13_post)   -- rustTable[3][1].2 reduces to 36
  have hmt23 : v114 = v43 := by simp only [v114_post, i32_post]; rfl
  have htt23 : ∀ i < 4, lane64 t23 i = tVal (stateWords src i) 3 2 :=
    tVal_of src 3 2 v11 v43 v115 t23
      (lane_read src 1 2 v11 v11_post)
      hd1 (by rw [v115_post, hmt23])
      (by exact t23_post)   -- rustTable[3][2].2 reduces to 10
  have hmt33 : v116 = v45 := by simp only [v116_post, i33_post]; rfl
  have htt33 : ∀ i < 4, lane64 t33 i = tVal (stateWords src i) 3 3 :=
    tVal_of src 3 3 v20 v45 v117 t33
      (lane_read src 2 3 v20 v20_post)
      hd2 (by rw [v117_post, hmt33])
      (by exact t33_post)   -- rustTable[3][3].2 reduces to 15
  have hmt43 : v118 = v47 := by simp only [v118_post, i34_post]; rfl
  have htt43 : ∀ i < 4, lane64 t43 i = tVal (stateWords src i) 3 4 :=
    tVal_of src 3 4 v31 v47 v119 t43
      (lane_read src 3 4 v31 v31_post)
      hd3 (by rw [v119_post, hmt43])
      (by exact t43_post)   -- rustTable[3][4].2 reduces to 56
  have hmt04 : v130 = v45 := by simp only [v130_post, i40_post]; rfl
  have htt04 : ∀ i < 4, lane64 t04 i = tVal (stateWords src i) 4 0 :=
    tVal_of src 4 0 v16 v45 v131 t04
      (lane_read src 2 0 v16 v16_post)
      hd2 (by rw [v131_post, hmt04])
      (by exact t04_post)   -- rustTable[4][0].2 reduces to 62
  have hmt14 : v132 = v47 := by simp only [v132_post, i41_post]; rfl
  have htt14 : ∀ i < 4, lane64 t14 i = tVal (stateWords src i) 4 1 :=
    tVal_of src 4 1 v25 v47 v133 t14
      (lane_read src 3 1 v25 v25_post)
      hd3 (by rw [v133_post, hmt14])
      (by exact t14_post)   -- rustTable[4][1].2 reduces to 55
  have hmt24 : v134 = v49 := by simp only [v134_post, i42_post]; rfl
  have htt24 : ∀ i < 4, lane64 t24 i = tVal (stateWords src i) 4 2 :=
    tVal_of src 4 2 v35 v49 v135 t24
      (lane_read src 4 2 v35 v35_post)
      hd4 (by rw [v135_post, hmt24])
      (by exact t24_post)   -- rustTable[4][2].2 reduces to 39
  have hmt34 : v136 = v41 := by simp only [v136_post, i43_post]; rfl
  have htt34 : ∀ i < 4, lane64 t34 i = tVal (stateWords src i) 4 3 :=
    tVal_of src 4 3 v4 v41 v137 t34
      (lane_read src 0 3 v4 v4_post)
      hd0 (by rw [v137_post, hmt34])
      (by exact t34_post)   -- rustTable[4][3].2 reduces to 41
  have hmt44 : v138 = v43 := by simp only [v138_post, i44_post]; rfl
  have htt44 : ∀ i < 4, lane64 t44 i = tVal (stateWords src i) 4 4 :=
    tVal_of src 4 4 v15 v43 v139 t44
      (lane_read src 1 4 v15 v15_post)
      hd1 (by rw [v139_post, hmt44])
      (by exact t44_post)   -- rustTable[4][4].2 reduces to 2
  have hvv61 : ∀ i < 4, lane64 v61 i = chiRow (stateWords src i) 0 0 :=
    chiRow_of src 0 0 t0 t1 t2 v60 v61
      htt0 htt1 htt2 v60_post v61_post
  have hvv63 : ∀ i < 4, lane64 v63 i = chiRow (stateWords src i) 0 1 :=
    chiRow_of src 0 1 t1 t2 t3 v62 v63
      htt1 htt2 htt3 v62_post v63_post
  have hvv65 : ∀ i < 4, lane64 v65 i = chiRow (stateWords src i) 0 2 :=
    chiRow_of src 0 2 t2 t3 t4 v64 v65
      htt2 htt3 htt4 v64_post v65_post
  have hvv67 : ∀ i < 4, lane64 v67 i = chiRow (stateWords src i) 0 3 :=
    chiRow_of src 0 3 t3 t4 t0 v66 v67
      htt3 htt4 htt0 v66_post v67_post
  have hvv69 : ∀ i < 4, lane64 v69 i = chiRow (stateWords src i) 0 4 :=
    chiRow_of src 0 4 t4 t0 t1 v68 v69
      htt4 htt0 htt1 v68_post v69_post
  have hvv81 : ∀ i < 4, lane64 v81 i = chiRow (stateWords src i) 1 0 :=
    chiRow_of src 1 0 t01 t11 t21 v80 v81
      htt01 htt11 htt21 v80_post v81_post
  have hvv83 : ∀ i < 4, lane64 v83 i = chiRow (stateWords src i) 1 1 :=
    chiRow_of src 1 1 t11 t21 t31 v82 v83
      htt11 htt21 htt31 v82_post v83_post
  have hvv85 : ∀ i < 4, lane64 v85 i = chiRow (stateWords src i) 1 2 :=
    chiRow_of src 1 2 t21 t31 t41 v84 v85
      htt21 htt31 htt41 v84_post v85_post
  have hvv87 : ∀ i < 4, lane64 v87 i = chiRow (stateWords src i) 1 3 :=
    chiRow_of src 1 3 t31 t41 t01 v86 v87
      htt31 htt41 htt01 v86_post v87_post
  have hvv89 : ∀ i < 4, lane64 v89 i = chiRow (stateWords src i) 1 4 :=
    chiRow_of src 1 4 t41 t01 t11 v88 v89
      htt41 htt01 htt11 v88_post v89_post
  have hvv101 : ∀ i < 4, lane64 v101 i = chiRow (stateWords src i) 2 0 :=
    chiRow_of src 2 0 t02 t12 t22 v100 v101
      htt02 htt12 htt22 v100_post v101_post
  have hvv103 : ∀ i < 4, lane64 v103 i = chiRow (stateWords src i) 2 1 :=
    chiRow_of src 2 1 t12 t22 t32 v102 v103
      htt12 htt22 htt32 v102_post v103_post
  have hvv105 : ∀ i < 4, lane64 v105 i = chiRow (stateWords src i) 2 2 :=
    chiRow_of src 2 2 t22 t32 t42 v104 v105
      htt22 htt32 htt42 v104_post v105_post
  have hvv107 : ∀ i < 4, lane64 v107 i = chiRow (stateWords src i) 2 3 :=
    chiRow_of src 2 3 t32 t42 t02 v106 v107
      htt32 htt42 htt02 v106_post v107_post
  have hvv109 : ∀ i < 4, lane64 v109 i = chiRow (stateWords src i) 2 4 :=
    chiRow_of src 2 4 t42 t02 t12 v108 v109
      htt42 htt02 htt12 v108_post v109_post
  have hvv121 : ∀ i < 4, lane64 v121 i = chiRow (stateWords src i) 3 0 :=
    chiRow_of src 3 0 t03 t13 t23 v120 v121
      htt03 htt13 htt23 v120_post v121_post
  have hvv123 : ∀ i < 4, lane64 v123 i = chiRow (stateWords src i) 3 1 :=
    chiRow_of src 3 1 t13 t23 t33 v122 v123
      htt13 htt23 htt33 v122_post v123_post
  have hvv125 : ∀ i < 4, lane64 v125 i = chiRow (stateWords src i) 3 2 :=
    chiRow_of src 3 2 t23 t33 t43 v124 v125
      htt23 htt33 htt43 v124_post v125_post
  have hvv127 : ∀ i < 4, lane64 v127 i = chiRow (stateWords src i) 3 3 :=
    chiRow_of src 3 3 t33 t43 t03 v126 v127
      htt33 htt43 htt03 v126_post v127_post
  have hvv129 : ∀ i < 4, lane64 v129 i = chiRow (stateWords src i) 3 4 :=
    chiRow_of src 3 4 t43 t03 t13 v128 v129
      htt43 htt03 htt13 v128_post v129_post
  have hvv141 : ∀ i < 4, lane64 v141 i = chiRow (stateWords src i) 4 0 :=
    chiRow_of src 4 0 t04 t14 t24 v140 v141
      htt04 htt14 htt24 v140_post v141_post
  have hvv143 : ∀ i < 4, lane64 v143 i = chiRow (stateWords src i) 4 1 :=
    chiRow_of src 4 1 t14 t24 t34 v142 v143
      htt14 htt24 htt34 v142_post v143_post
  have hvv145 : ∀ i < 4, lane64 v145 i = chiRow (stateWords src i) 4 2 :=
    chiRow_of src 4 2 t24 t34 t44 v144 v145
      htt24 htt34 htt44 v144_post v145_post
  have hvv147 : ∀ i < 4, lane64 v147 i = chiRow (stateWords src i) 4 3 :=
    chiRow_of src 4 3 t34 t44 t04 v146 v147
      htt34 htt44 htt04 v146_post v147_post
  have hvv149 : ∀ i < 4, lane64 v149 i = chiRow (stateWords src i) 4 4 :=
    chiRow_of src 4 4 t44 t04 t14 v148 v149
      htt44 htt04 htt14 v148_post v149_post

  have hd25len : (dst25.val : List Vec256).length = 25 := dst25.property
  have hdlen : (dst.val : List Vec256).length = 25 := dst.property
  have hz : ((0#usize : Std.Usize) : ℕ) = 0 := rfl
  have h150 : v150 = (dst25.val)[0]! :=
    v150_post.trans (getElem!_pos _ 0 (by rw [hd25len]; decide)).symm
  have h00 : lane64 v151 l = chiRow (stateWords src l) 0 0 ^^^ rcWord iᵣ := by
    have hv150 : lane64 v150 l = lane64 v61 l := by
      rw [h150]
      simp +decide only [dst25_post, dst24_post, dst23_post, dst22_post, dst21_post, dst20_post, dst19_post, dst18_post, dst17_post, dst16_post, dst15_post, dst14_post, dst13_post, dst12_post, dst11_post, dst10_post, dst9_post, dst8_post, dst7_post, dst6_post, dst5_post, dst4_post, dst3_post, dst2_post, dst1_post,
        Std.Array.set_val_eq, i5_post, i6_post, i7_post, i8_post, i9_post, i15_post, i16_post, i17_post, i18_post, i19_post, i25_post, i26_post, i27_post, i28_post, i29_post, i35_post, i36_post, i37_post, i38_post, i39_post, i45_post, i46_post, i47_post, i48_post, i49_post,
        getElem!_list_set, List.length_set, hdlen,
        Nat.reduceMul, Nat.reduceAdd, if_true, if_false]
    have hx : lane64 v151 l = lane64 v150 l ^^^ lane64 rc l := by
      simp only [lane64, v151_post, lane64_xor_bits]
    rw [hx, hv150, hvv61 l hl, hrc l hl]
  fin_cases x <;> fin_cases y <;>
    simp +decide only [stateWords_apply, idx, r_post, dst25_post, dst24_post, dst23_post, dst22_post, dst21_post, dst20_post, dst19_post, dst18_post, dst17_post, dst16_post, dst15_post, dst14_post, dst13_post, dst12_post, dst11_post, dst10_post, dst9_post, dst8_post, dst7_post, dst6_post, dst5_post, dst4_post, dst3_post, dst2_post, dst1_post,
      Std.Array.set_val_eq, i5_post, i6_post, i7_post, i8_post, i9_post, i15_post, i16_post, i17_post, i18_post, i19_post, i25_post, i26_post, i27_post, i28_post, i29_post, i35_post, i36_post, i37_post, i38_post, i39_post, i45_post, i46_post, i47_post, i48_post, i49_post, getElem!_list_set, List.length_set, hdlen, hz,
      Nat.reduceMul, Nat.reduceAdd, if_true, if_false]
  · rw [h00, RndW_fused]; simp +decide
  · simp +decide [RndW_fused, hvv81 l hl]
  · simp +decide [RndW_fused, hvv101 l hl]
  · simp +decide [RndW_fused, hvv121 l hl]
  · simp +decide [RndW_fused, hvv141 l hl]
  · simp +decide [RndW_fused, hvv63 l hl]
  · simp +decide [RndW_fused, hvv83 l hl]
  · simp +decide [RndW_fused, hvv103 l hl]
  · simp +decide [RndW_fused, hvv123 l hl]
  · simp +decide [RndW_fused, hvv143 l hl]
  · simp +decide [RndW_fused, hvv65 l hl]
  · simp +decide [RndW_fused, hvv85 l hl]
  · simp +decide [RndW_fused, hvv105 l hl]
  · simp +decide [RndW_fused, hvv125 l hl]
  · simp +decide [RndW_fused, hvv145 l hl]
  · simp +decide [RndW_fused, hvv67 l hl]
  · simp +decide [RndW_fused, hvv87 l hl]
  · simp +decide [RndW_fused, hvv107 l hl]
  · simp +decide [RndW_fused, hvv127 l hl]
  · simp +decide [RndW_fused, hvv147 l hl]
  · simp +decide [RndW_fused, hvv69 l hl]
  · simp +decide [RndW_fused, hvv89 l hl]
  · simp +decide [RndW_fused, hvv109 l hl]
  · simp +decide [RndW_fused, hvv129 l hl]
  · simp +decide [RndW_fused, hvv149 l hl]

end

end Kopis.Avx2.Keccak
