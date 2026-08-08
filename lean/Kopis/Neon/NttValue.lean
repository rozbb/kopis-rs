/-
  # Kopis/Neon/NttValue.lean — what one NEON butterfly does to the residues (plan phase F4).

  `Kopis/Neon/Butterfly.lean` already states both butterflies *exactly*, over ℤ: the Cooley-Tukey
  pair is `(lo + t, lo − t)` with `t` the Montgomery product, named existentially and pinned down
  by `q ∣ t·2¹⁶ − hi·z`; the Gentleman-Sande pair is `(lo + hi, ·)` with the second slot pinned
  down the same way.  This file casts those identities into `ZMod q`, where the `2⁻¹⁶` becomes a
  factor `Rinv` and the statements take the shape `Kopis/Crt/NttAlgebra.lean`'s `State_ct` and
  `State_gs` ask of a layer.

  That is the only content here.  The bound hypotheses are inherited unchanged from
  `Butterfly.lean` — they are what makes the wrapping `vaddq_s16` / `vsubq_s16` exact, so that
  the integer identity survives the cast — and `mont_resZ` is the one new lemma: the Montgomery
  divisibility, read in `ZMod q`.
-/
import Kopis.Neon.NttZeta
import Kopis.Neon.Butterfly

open Aeneas Aeneas.Std Result
open RustKopisNeon
open RustKopisNeon.backend.neon.intrinsics

namespace Kopis.Neon

set_option maxHeartbeats 1000000

/-- Lane `i` of a vector, as a residue. -/
noncomputable def laneZ (q : ℕ) (v : Vec128) (i : ℕ) : ZMod q := (((lane16 v i).toInt : ℤ) : ZMod q)

/-- Array position `p` of a block, as a residue.  Stated for an arbitrary array length, because
the forward transform's block is a window inside a longer buffer. -/
noncomputable def posZ (q : ℕ) {N : Usize} (b : Array I16 N) (p : ℕ) : ZMod q :=
  (((b.val[p]!).val : ℤ) : ZMod q)

/-- **The Montgomery divisibility, read in `ZMod q`.**  `t·2¹⁶ ≡ x·z` becomes `t = z·R⁻¹·x`. -/
theorem mont_resZ (q : ℕ) (Rinv : ZMod q) (hR : ((2 ^ 16 : ℤ) : ZMod q) * Rinv = 1)
    (t x z : ℤ) (h : (q : ℤ) ∣ (t * 2 ^ 16 - x * z)) :
    ((t : ℤ) : ZMod q) = ((z : ℤ) : ZMod q) * Rinv * ((x : ℤ) : ZMod q) := by
  have hcast : ((t * 2 ^ 16 - x * z : ℤ) : ZMod q) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ q).mpr h
  push_cast at hcast
  calc ((t : ℤ) : ZMod q) = ((t : ℤ) : ZMod q) * (((2 ^ 16 : ℤ) : ZMod q) * Rinv) := by
        rw [hR]; ring
    _ = ((z : ℤ) : ZMod q) * Rinv * ((x : ℤ) : ZMod q) := by
        push_cast
        linear_combination Rinv * hcast

/-! ## The two butterflies, as residues -/

/-- **One Cooley-Tukey butterfly, as residues.**  `mont_mul` contributes the `2⁻¹⁶`, which is why
the twiddle that appears is `z · R⁻¹` and not `z`. -/
theorem ct_butterfly_val (lo hi z zq qv : Vec128) (q : ℕ) (Zb B Bt : ℤ) (Rinv : ZMod q)
    (hR : ((2 ^ 16 : ℤ) : ZMod q) * Rinv = 1)
    (hQ : ∀ i < 8, (lane16 qv i).toInt = (q : ℤ)) (hQpos : 0 < (q : ℤ)) (hQlt : (q : ℤ) ≤ 2 ^ 14)
    (hz : ∀ i < 8, |(lane16 z i).toInt| ≤ Zb) (hZb : Zb ≤ 2 ^ 14)
    (hzq : ∀ i < 8, (2 ^ 16 : ℤ) ∣ ((lane16 zq i).toInt * (q : ℤ) - (lane16 z i).toInt))
    (hlo : VecBnd lo B) (hhi : VecBnd hi B) (hB0 : 0 ≤ B)
    (hBZ : B * Zb < 2 ^ 15 * (q : ℤ)) (hBt : B * Zb + 2 ^ 15 * (q : ℤ) ≤ 2 ^ 16 * Bt)
    (hfit : B + Bt ≤ 32767) :
    backend.neon.ntt.ct_butterfly lo hi z zq qv
      ⦃ (r : Vec128 × Vec128) => ∀ i < 8,
          laneZ q r.1 i = laneZ q lo i + (laneZ q z i * Rinv) * laneZ q hi i ∧
          laneZ q r.2 i = laneZ q lo i - (laneZ q z i * Rinv) * laneZ q hi i ⦄ := by
  apply WP.spec_mono (ct_butterfly_spec lo hi z zq qv (q : ℤ) Zb B Bt hQ hQpos hQlt hz hZb hzq
    hlo hhi hB0 hBZ hBt hfit)
  rintro r ⟨-, -, hval⟩ i hi'
  obtain ⟨t, hdvd, -, h1, h2⟩ := hval i hi'
  have ht : ((t : ℤ) : ZMod q) = laneZ q z i * Rinv * laneZ q hi i :=
    mont_resZ q Rinv hR t _ _ hdvd
  constructor
  · show laneZ q r.1 i = _
    unfold laneZ
    rw [h1]
    push_cast
    rw [show (((t : ℤ)) : ZMod q) = laneZ q z i * Rinv * laneZ q hi i from ht]
    unfold laneZ
    ring
  · show laneZ q r.2 i = _
    unfold laneZ
    rw [h2]
    push_cast
    rw [show (((t : ℤ)) : ZMod q) = laneZ q z i * Rinv * laneZ q hi i from ht]
    unfold laneZ
    ring

/-- **One Gentleman-Sande butterfly, as residues.**  The tables feeding `z` on the inverse side
already carry the negation `State_gs` expects, so no sign has to be inserted by hand. -/
theorem gs_butterfly_val (lo hi z zq qv : Vec128) (q : ℕ) (Zb B Bt : ℤ) (Rinv : ZMod q)
    (hR : ((2 ^ 16 : ℤ) : ZMod q) * Rinv = 1)
    (hQ : ∀ i < 8, (lane16 qv i).toInt = (q : ℤ)) (hQpos : 0 < (q : ℤ)) (hQlt : (q : ℤ) ≤ 2 ^ 14)
    (hz : ∀ i < 8, |(lane16 z i).toInt| ≤ Zb) (hZb : Zb ≤ 2 ^ 14)
    (hzq : ∀ i < 8, (2 ^ 16 : ℤ) ∣ ((lane16 zq i).toInt * (q : ℤ) - (lane16 z i).toInt))
    (hlo : VecBnd lo B) (hhi : VecBnd hi B) (hB0 : 0 ≤ B)
    (hBZ : 2 * B * Zb < 2 ^ 15 * (q : ℤ)) (hBt : 2 * B * Zb + 2 ^ 15 * (q : ℤ) ≤ 2 ^ 16 * Bt)
    (hfit : 2 * B ≤ 32767) :
    backend.neon.ntt.gs_butterfly lo hi z zq qv
      ⦃ (r : Vec128 × Vec128) => ∀ i < 8,
          laneZ q r.1 i = laneZ q lo i + laneZ q hi i ∧
          laneZ q r.2 i = (laneZ q z i * Rinv) * (laneZ q lo i - laneZ q hi i) ⦄ := by
  apply WP.spec_mono (gs_butterfly_spec lo hi z zq qv (q : ℤ) Zb B Bt hQ hQpos hQlt hz hZb hzq
    hlo hhi hB0 hBZ hBt hfit)
  rintro r ⟨-, -, hval⟩ i hi'
  obtain ⟨h1, hdvd⟩ := hval i hi'
  refine ⟨?_, ?_⟩
  · show laneZ q r.1 i = _
    unfold laneZ
    rw [h1]
    push_cast
    rfl
  · have ht := mont_resZ q Rinv hR _ _ _ hdvd
    show laneZ q r.2 i = _
    unfold laneZ
    rw [ht]
    push_cast
    ring

/-! ## Loads and stores, as residues -/

theorem load_posZ (q : ℕ) {N : Usize} (b : Array I16 N) (i : Usize)
    (hi : 8 * i.val + 8 ≤ N.val) :
    ∃ c, load_i16 b i = ok c ∧ ∀ m < 8, laneZ q c m = posZ q b (8 * i.val + m) := by
  obtain ⟨c, hc, h⟩ := load_i16_gen b i hi
  exact ⟨c, hc, fun m hm => by unfold laneZ posZ; rw [h m hm]⟩

theorem store_posZ (q : ℕ) {N : Usize} (b : Array I16 N) (i : Usize) (v : Vec128)
    (hi : 8 * i.val + 8 ≤ N.val) :
    ∃ b', store_i16 b i v = ok b' ∧ ∀ p < N.val,
      posZ q b' p =
        if 8 * i.val ≤ p ∧ p < 8 * i.val + 8 then laneZ q v (p - 8 * i.val)
        else posZ q b p := by
  obtain ⟨b', hb', h⟩ := store_i16_gen b i v hi
  refine ⟨b', hb', fun p hp => ?_⟩
  unfold posZ laneZ
  rw [h p hp]
  split <;> rfl

end Kopis.Neon
