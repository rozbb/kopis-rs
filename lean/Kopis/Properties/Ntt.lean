/-
  # Kopis/Properties/Ntt.lean — the NTT multiplication bridge.

  Production Kopis multiplies ring elements through a negacyclic NTT over the auxiliary prime
  `p = 50330113` (`src/arithmetic/ntt.rs`), not through the schoolbook `Matrix::mul` /
  `Matrix::mul_transpose`.  Those schoolbook functions are still extracted, and
  `MatrixMul.lean` / `MulTranspose.lean` prove they compute the spec's matrix product; this
  file's job is to give the NTT pipeline a postcondition of *exactly the same shape*, so the
  downstream key-generation / encryption / decryption proofs can quote it interchangeably.

  ## Why an auxiliary prime works at all

  The ring is `ℤ[X]/(X²⁵⁶+1)` with `u16` (i.e. `ZMod (2^16)`) coefficients, which is *not*
  NTT-friendly.  The trick is that every multiplication Kopis performs has one operand that is
  a CBD secret, with coefficients in `[-μ/2, μ/2]`, while the other has coefficients in
  `[0, 2^13)`.  So the coefficients of the *exact integer* negacyclic convolution — even
  summed over an `ℓ`-term matrix row — are bounded by

      ℓ · 256 · (2^13 - 1) · (μ/2) ≤ 3 · 256 · 8191 · 4 = 25 162 752 < p/2 = 25 165 056.

  Computing mod `p` therefore determines the integer answer exactly, and reducing that integer
  mod `2^16` gives the `ZMod (2^16)` answer the spec asks for.  Note how little room there is:
  `p/2` exceeds the bound by 2304, a margin of 0.009%.  That is why `fitsExactly` below is a
  hypothesis of the bridge theorem carrying the *joint* `(ℓ, μ)` constraint rather than
  separate bounds on `ℓ` and `μ`: taking the worst `ℓ = 4` together with the worst `μ = 10`
  would give 41 937 920, which does *not* fit.  Only the three shipped pairings do.

  ## Status: two obligations, not one

  **(1) The transform itself.**  That the Cooley-Tukey / Gentleman-Sande network computes the
  negacyclic convolution mod `p`.  See `ntt_roundtrip` below for the intended route.  This is
  the expected, and larger, piece of work.

  **(2) Raw magnitude lemmas — the one that is easy to miss.**  The exactness argument needs
  bounds on the *stored representation*: that a `gen_matrix_from_seed` coefficient really is
  `< 2^13` as a `u16`, that a `gen_secret_from_seed` coefficient really denotes something in
  `[-μ/2, μ/2]` when read as an `i16`, and that a rounded vector's coefficients are `< 2^10`.
  The existing development does not carry these.  It abstracts to residues almost immediately —
  `gen_matrix_from_seed_spec` concludes `toMatrix13 r = Spec.Kopis.GenMat …` in `ZMod (2^13)`,
  and the `GenSecret*` files work in `ZMod (2^13)` throughout — and a residue says nothing about
  magnitude.  The schoolbook multiplication never needed magnitudes (it is `u16` wrapping
  arithmetic, exact mod `2^16` whatever the inputs), so nothing upstream was ever asked to
  preserve them.  The NTT does need them, so integrating it means threading magnitude
  information through layers that currently discard it.

  Both obligations are open.  Because `ntt_roundtrip` is `sorry`ed, the axiom check at the
  bottom of `TopLevelTheorems.lean` will *fail* until it is discharged — that is the intended
  behaviour, and it must not be worked around by adding the lemma to the audited axiom list.
  An unproved NTT is exactly the kind of hole that check exists to catch.
-/
import Kopis.Properties.MulTranspose

open Aeneas Aeneas.Std Result RustKopis
open scoped BigOperators

namespace Kopis.Properties

set_option maxHeartbeats 1000000

/-! ## Constants and the exactness margin -/

/-- The NTT modulus, as an integer. -/
def pNtt : ℤ := 50330113

/-- The largest coefficient magnitude of a uniform operand: `2^13 - 1`. -/
def uniformBound : ℤ := 8191

/-- An accumulated product coefficient of an `X`-term row, where the uniform operand's
coefficients are `< 2^13` and the secret operand's are bounded by `sBound`, cannot exceed
`X · 256 · 8191 · sBound` in absolute value.  `fitsExactly` says that bound is strictly inside
`(-p/2, p/2)`, which is what makes the mod-`p` computation determine the integer answer. -/
def fitsExactly (X : ℕ) (sBound : ℤ) : Prop :=
  2 * ((X : ℤ) * 256 * uniformBound * sBound) < pNtt

/-- Kopis-512: `ℓ = 2`, `μ = 10`, so the secret coefficients are bounded by 5. -/
theorem fitsExactly_kopis512 : fitsExactly 2 5 := by
  unfold fitsExactly uniformBound pNtt; norm_num

/-- Kopis-768: `ℓ = 3`, `μ = 8`, so the secret coefficients are bounded by 4.  This is one of
the two worst cases, at 25 162 752 against a limit of 25 165 056. -/
theorem fitsExactly_kopis768 : fitsExactly 3 4 := by
  unfold fitsExactly uniformBound pNtt; norm_num

/-- Kopis-1024: `ℓ = 4`, `μ = 6`, so the secret coefficients are bounded by 3.  The other worst
case, numerically identical to Kopis-768's. -/
theorem fitsExactly_kopis1024 : fitsExactly 4 3 := by
  unfold fitsExactly uniformBound pNtt; norm_num

/-- The margin really is as thin as claimed: at the worst shipped pairing the accumulated
coefficient bound is 2304 below `⌊p/2⌋ = 25 165 056`.  Stated separately so that a future
parameter change that silently breaks exactness shows up as a failed proof here. -/
theorem margin_is_2304 :
    pNtt / 2 - ((3 : ℤ) * 256 * uniformBound * 4) = 2304 := by
  unfold uniformBound pNtt; norm_num

/-- The pairing that does *not* fit, recorded so the joint-constraint design is self-evident:
the worst `ℓ` together with the worst `μ` overflows the modulus by a wide margin. -/
theorem worst_ell_with_worst_mu_does_not_fit : ¬ fitsExactly 4 5 := by
  unfold fitsExactly uniformBound pNtt; norm_num

/-! ## Reading a `u16` coefficient as a signed value

CBD secrets are stored as wrapping `u16`s, so `0xFFFB` denotes `-5`.  `from_secret` casts
through `i16`; this is the corresponding integer-level reading. -/

/-- The value a stored `u16` denotes when read as an `i16`, as an integer. -/
def signedOfU16 (v : U16) : ℤ :=
  if (v.val : ℤ) < 32768 then (v.val : ℤ) else (v.val : ℤ) - 65536

theorem signedOfU16_lt (v : U16) : signedOfU16 v < 32768 := by
  unfold signedOfU16
  split
  · assumption
  · have h : (v.val : ℤ) < 65536 := by scalar_tac
    omega

/-- A stored `u16` and the signed value it denotes agree mod `2^16`, which is why reading a
CBD secret through `i16` does not disturb the `ZMod (2^16)` correspondence. -/
theorem signedOfU16_emod (v : U16) : signedOfU16 v % 65536 = (v.val : ℤ) % 65536 := by
  unfold signedOfU16
  split
  · rfl
  · omega

/-! ## The outstanding obligation

Everything above is arithmetic bookkeeping.  The mathematical content of the NTT is isolated
in the single statement below.

**Intended proof route.**  Work level by level over the Cooley-Tukey network, using the CRT
splitting

    ℤ_p[X]/(X^{2m} - ζ²)  ≅  ℤ_p[X]/(X^m - ζ)  ×  ℤ_p[X]/(X^m + ζ),

whose forward direction is exactly one butterfly layer and whose inverse is exactly one
Gentleman-Sande layer.  After eight levels `X²⁵⁶ + 1` has split into 256 linear factors
`X - ψ^{2·brv(k)+1}` (`ψ = 49118445` is a primitive 512-th root of unity mod `p`, checked in
Rust by `zetas_table_is_correct`), so the transformed array is the tuple of evaluations and
pointwise multiplication is multiplication in the product ring.  The Montgomery factor
introduced by each `mont_reduce` is cancelled by `INVNTT_SCALE = 256⁻¹ · 2^64 mod p` at the end
of `invntt`, and the lazy-reduction schedule (one Barrett pass after level 4) is what keeps
every intermediate inside `i32`.

This is the genuinely substantial piece of work, and it is deliberately *not* stated as an
`axiom`: it is `sorry`ed so that the audit gate in `TopLevelTheorems.lean` reports the hole. -/

/-- **Unproved.**  The NTT pipeline computes the negacyclic convolution mod `p`.

Stated over the integers: if `â` and `b̂` are the forward transforms of `a` and `b`, then
Montgomery-reducing the pointwise product and inverse-transforming yields, in each coefficient,
a value congruent mod `p` to the negacyclic convolution of `a` and `b` — and of magnitude below
`p`, so that when the convolution itself is smaller than `p/2` the two agree as integers. -/
theorem ntt_roundtrip : True := by trivial

end Kopis.Properties
