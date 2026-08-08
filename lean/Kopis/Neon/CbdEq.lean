/-
  # Kopis/Neon/CbdEq.lean — Phase D's target.

  The NEON centred-binomial sampler and the portable one produce the same ring element:

      backend::neon::sample::cbd MU buf  =  sample::cbd MU buf out

  for `MU ∈ {6, 8, 10}` and every correctly-sized input.

  The two sides are characterised differently, which is the only subtlety.  `cbd_streamNat`
  gives the NEON coefficient as a *raw* `u16` (`cbdU16`), while the portable chain gives its
  value in `ZMod (2¹³)` (`cbd_spec`) together with a magnitude bound (`cbd_bd`).  A `u16` that
  is small-signed with bound `b` is determined by its residue mod `2¹³` as soon as `2b < 2¹³`,
  and here `b = MU/2 ≤ 5`, so the two characterisations pin down the same word.
-/
import Kopis.Neon.Cbd
import Kopis.Neon.CbdGeneric

open Aeneas Aeneas.Std Result
open RustKopisNeon

namespace Kopis.Neon

open Kopis.Properties (cbdX cbdX_le cbdU16)
open arithmetic.ring_arith (RingElem)

set_option maxHeartbeats 1000000
set_option maxRecDepth 8000

/-! ## A small-signed `u16` is determined by its residue mod `2¹³` -/

/-- The centred representative of a small-signed `u16`. -/
private def centred (v : U16) : ℤ := if v.val ≤ 32768 then (v.val : ℤ) else (v.val : ℤ) - 2 ^ 16

private theorem centred_bound {v : U16} {b : ℕ} (hb : b ≤ 8)
    (h : CbdGeneric.smallSignedU16 v b) : -(b : ℤ) ≤ centred v ∧ centred v ≤ (b : ℤ) := by
  unfold CbdGeneric.smallSignedU16 at h
  unfold centred
  have hlt : v.val < 2 ^ 16 := by have := v.hBounds; simp at this ⊢; omega
  rcases h with h | h
  · rw [if_pos (by omega)]; omega
  · rw [if_neg (by omega)]
    have : (2:ℕ) ^ 16 = 65536 := by norm_num
    omega

private theorem centred_cast (v : U16) :
    ((centred v : ℤ) : ZMod (2 ^ 13)) = ((v.val : ℕ) : ZMod (2 ^ 13)) := by
  unfold centred
  have h216 : ((2 ^ 16 : ℤ) : ZMod (2 ^ 13)) = 0 := by
    have hn : ((2 ^ 16 : ℕ) : ZMod (2 ^ 13)) = 0 := by
      rw [show (2 : ℕ) ^ 16 = 2 ^ 13 * 8 from by norm_num, Nat.cast_mul, ZMod.natCast_self,
        zero_mul]
    exact_mod_cast hn
  split
  · push_cast; ring
  · push_cast [h216]; ring

/-- Two small-signed `u16`s that agree mod `2¹³` are equal, provided the bound leaves room. -/
private theorem u16_eq_of_smallSigned {x y : U16} {b : ℕ} (hb : b ≤ 8)
    (hx : CbdGeneric.smallSignedU16 x b) (hy : CbdGeneric.smallSignedU16 y b)
    (h : ((x.val : ℕ) : ZMod (2 ^ 13)) = ((y.val : ℕ) : ZMod (2 ^ 13))) : x = y := by
  obtain ⟨hxl, hxu⟩ := centred_bound hb hx
  obtain ⟨hyl, hyu⟩ := centred_bound hb hy
  -- the two centred representatives agree mod `2¹³` and are both small, hence equal
  have hz : ((centred x : ℤ) : ZMod (2 ^ 13)) = ((centred y : ℤ) : ZMod (2 ^ 13)) := by
    rw [centred_cast, centred_cast]; exact h
  have hdvd : ((2:ℤ) ^ 13) ∣ (centred x - centred y) := by
    have := (ZMod.intCast_eq_intCast_iff' (centred x) (centred y) (2 ^ 13)).mp hz
    have hmod : (centred x) % ((2:ℤ) ^ 13) = (centred y) % ((2:ℤ) ^ 13) := by
      exact_mod_cast this
    omega
  have hcen : centred x = centred y := by
    rcases hdvd with ⟨c, hc⟩
    have hb8 : (b : ℤ) ≤ 8 := by exact_mod_cast hb
    have : c = 0 := by nlinarith [hc, hxl, hxu, hyl, hyu]
    omega
  -- and equal centred representatives means equal words
  have hxlt : x.val < 2 ^ 16 := by have := x.hBounds; simp at this ⊢; omega
  have hylt : y.val < 2 ^ 16 := by have := y.hBounds; simp at this ⊢; omega
  apply UScalar.eq_of_val_eq
  unfold centred at hcen
  have h216 : (2:ℤ) ^ 16 = 65536 := by norm_num
  split at hcen <;> split at hcen <;> omega

/-! ## The NEON coefficient is small-signed, and has the right residue -/

private theorem cbdU16_lt (buf : Slice U8) (half p : ℕ) (_hhalf : half ≤ 5) :
    cbdU16 buf half p < 2 ^ 16 := by
  unfold cbdU16
  exact Nat.mod_lt _ (by positivity)

private theorem cbdU16_smallSigned (buf : Slice U8) (half p : ℕ) (hhalf : half ≤ 5)
    (v : U16) (hv : v.val = cbdU16 buf half p) :
    CbdGeneric.smallSignedU16 v half := by
  have hx := cbdX_le buf half p
  have hy := cbdX_le buf half (p + half)
  have h216 : (2:ℕ) ^ 16 = 65536 := by norm_num
  unfold CbdGeneric.smallSignedU16
  rw [hv]
  unfold cbdU16
  rcases Nat.lt_or_ge (cbdX buf half p) (cbdX buf half (p + half)) with hlt | hge
  · right
    rw [Nat.mod_eq_of_lt (by omega)]
    omega
  · left
    rw [show cbdX buf half p + 2 ^ 16 - cbdX buf half (p + half)
        = 2 ^ 16 + (cbdX buf half p - cbdX buf half (p + half)) from by omega,
      Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
    omega

private theorem cbdU16_cast (buf : Slice U8) (mu half k : ℕ) (hhalf : half ≤ 5) (v : U16)
    (hv : v.val = cbdU16 buf half (mu * k)) :
    ((v.val : ℕ) : ZMod (2 ^ 13)) = CbdGeneric.cbdVal buf mu half k := by
  have hx := cbdX_le buf half (mu * k)
  have hy := cbdX_le buf half (mu * k + half)
  have h216 : (2:ℕ) ^ 16 = 65536 := by norm_num
  have hz : ((2 ^ 16 : ℕ) : ZMod (2 ^ 13)) = 0 := by
    rw [show (2 : ℕ) ^ 16 = 2 ^ 13 * 8 from by norm_num, Nat.cast_mul, ZMod.natCast_self, zero_mul]
  have hmod : ∀ x : ℕ, ((x % 2 ^ 16 : ℕ) : ZMod (2 ^ 13)) = (x : ZMod (2 ^ 13)) := fun x => by
    conv_rhs => rw [← Nat.mod_add_div x (2 ^ 16)]
    push_cast [hz]
    ring
  rw [hv]
  unfold cbdU16 CbdGeneric.cbdVal
  rw [hmod, Nat.cast_sub (by omega), Nat.cast_add, hz]
  ring

/-! ## Phase D -/

/-- **Phase D.**  The vector sampler is bit-identical to the portable one, for every `MU` the
crate instantiates. -/
theorem neon_cbd_eq (buf : Slice U8) (MU : Usize) (out : RingElem)
    (hMU : MU.val = 6 ∨ MU.val = 8 ∨ MU.val = 10)
    (hlen : buf.val.length = 32 * MU.val) :
    backend.neon.sample.cbd_lanes MU buf = sample.cbd MU buf out := by
  have hhalf : MU.val / 2 ≤ 5 := by omega
  have hhalf1 : 1 ≤ MU.val / 2 := by omega
  have hmu : MU.val = 2 * (MU.val / 2) := by omega
  have hlen' : buf.length = 32 * MU.val := by simpa [Slice.length] using hlen
  obtain ⟨r1, hr1, hp1⟩ := WP.spec_imp_exists
    (cbd_streamNat buf MU.val (MU.val / 2) hmu hhalf1 hhalf hlen' MU rfl)
  obtain ⟨r2, hr2, hp2⟩ := WP.spec_imp_exists (CbdGeneric.cbd_spec MU buf out hMU hlen)
  obtain ⟨r2', hr2', hbd⟩ := WP.spec_imp_exists (CbdGeneric.cbd_bd MU buf out hMU hlen)
  have hr2eq : r2 = r2' := by
    have := hr2.symm.trans hr2'
    exact Result.ok.inj this
  subst hr2eq
  rw [hr1, hr2]
  congr 1
  apply Subtype.ext
  apply List.ext_getElem
  · have h1 := r1.property
    have h2 := r2.property
    scalar_tac
  · intro k hk1 hk2
    have hlen1 : r1.val.length = 256 := r1.property
    have hk : k < 256 := by omega
    rw [← getElem!_pos r1.val k hk1, ← getElem!_pos r2.val k hk2]
    have hv1 : (r1.val[k]!).val = cbdU16 buf (MU.val / 2) (MU.val * k) := hp1 k hk
    refine u16_eq_of_smallSigned (b := MU.val / 2) (by omega)
      (cbdU16_smallSigned buf _ _ hhalf _ hv1) (hbd k hk) ?_
    rw [cbdU16_cast buf MU.val (MU.val / 2) k hhalf _ hv1]
    exact (hp2 k hk).symm

end Kopis.Neon
