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
import Kopis.Properties.GenMatrix

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

/-- Every shipped parameter set satisfies the joint exactness constraint with `sBound = μ/2`.
This is what lets the downstream key-generation / encryption / decryption proofs discharge the
`fitsExactly` precondition of the NTT multiplication bridge from the parameter set alone. -/
theorem fitsExactly_paramSet (p : Spec.Kopis.ParameterSet) :
    fitsExactly (Spec.Kopis.ℓ p) ((Spec.Kopis.μ p / 2 : ℕ) : ℤ) := by
  cases p
  · exact fitsExactly_kopis512
  · exact fitsExactly_kopis768
  · exact fitsExactly_kopis1024

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

/-! ## Wrapping arithmetic is exact in range

`src/arithmetic/ntt.rs` writes every value-domain operation as an explicit `wrapping_*` so that
aeneas extracts total functions instead of `Result`-monadic ones with a panic-freedom side
condition each (see the comment above `mont_reduce` there).  The price is that correctness must
now say "the wrapping never actually wrapped", and these are the lemmas that discharge it.

Aeneas gives signed wrapping operations the value semantics `Int.bmod _ (2^numBits)`, so the
whole question reduces to: `Int.bmod` is the identity on its own balanced range. -/

/-- `Int.bmod` is the identity on `[-2^31, 2^31)` — the `i32` case. -/
theorem bmod_i32_exact {z : ℤ} (hlo : -2147483648 ≤ z) (hhi : z < 2147483648) :
    Int.bmod z (2 ^ 32) = z := by
  rw [Int.bmod_def]
  norm_num
  omega

/-- `Int.bmod` is the identity on `[-2^63, 2^63)` — the `i64` case. -/
theorem bmod_i64_exact {z : ℤ} (hlo : -9223372036854775808 ≤ z) (hhi : z < 9223372036854775808) :
    Int.bmod z (2 ^ 64) = z := by
  rw [Int.bmod_def]
  norm_num
  omega

/-- A wrapping `i32` multiplication is exact when the true product is in range. -/
theorem I32_wrapping_mul_exact (x y : I32)
    (hlo : -2147483648 ≤ x.val * y.val) (hhi : x.val * y.val < 2147483648) :
    (core.num.I32.wrapping_mul x y).val = x.val * y.val := by
  rw [core.num.I32.wrapping_mul, IScalar.wrapping_mul_val_eq]
  exact bmod_i32_exact hlo hhi

/-- A wrapping `i32` subtraction is exact when the true difference is in range. -/
theorem I32_wrapping_sub_exact (x y : I32)
    (hlo : -2147483648 ≤ x.val - y.val) (hhi : x.val - y.val < 2147483648) :
    (core.num.I32.wrapping_sub x y).val = x.val - y.val := by
  rw [core.num.I32.wrapping_sub, IScalar.wrapping_sub_val_eq]
  exact bmod_i32_exact hlo hhi

/-- A wrapping `i32` addition is exact when the true sum is in range.  This is the one the
butterfly loops need: the forward transform's `a[j] + t` and the inverse transform's un-reduced
sum path both rely on the magnitude analysis keeping them inside `i32`. -/
theorem I32_wrapping_add_exact (x y : I32)
    (hlo : -2147483648 ≤ x.val + y.val) (hhi : x.val + y.val < 2147483648) :
    (core.num.I32.wrapping_add x y).val = x.val + y.val := by
  rw [core.num.I32.wrapping_add, IScalar.wrapping_add_val_eq]
  exact bmod_i32_exact hlo hhi

/-- A wrapping `i64` multiplication is exact when the true product is in range.  Used for
`zeta * a[j+len]` in the butterflies and for the pointwise products, both of which are bounded
by `p²` and so are nowhere near `2^63`. -/
theorem I64_wrapping_mul_exact (x y : I64)
    (hlo : -9223372036854775808 ≤ x.val * y.val)
    (hhi : x.val * y.val < 9223372036854775808) :
    (core.num.I64.wrapping_mul x y).val = x.val * y.val := by
  rw [core.num.I64.wrapping_mul, IScalar.wrapping_mul_val_eq]
  exact bmod_i64_exact hlo hhi

/-- A wrapping `i64` subtraction is exact when the true difference is in range.  This is the
one `mont_reduce` needs for `a - t·p`: with `|a| < 2^31·p` and `|t| ≤ 2^31`, the difference is
below `2^32·p ≈ 2^57.6`, comfortably inside `i64`. -/
theorem I64_wrapping_sub_exact (x y : I64)
    (hlo : -9223372036854775808 ≤ x.val - y.val)
    (hhi : x.val - y.val < 9223372036854775808) :
    (core.num.I64.wrapping_sub x y).val = x.val - y.val := by
  rw [core.num.I64.wrapping_sub, IScalar.wrapping_sub_val_eq]
  exact bmod_i64_exact hlo hhi

/-- A wrapping `i64` addition is exact when the true sum is in range (the Barrett rounding
addend `+2^47`). -/
theorem I64_wrapping_add_exact (x y : I64)
    (hlo : -9223372036854775808 ≤ x.val + y.val)
    (hhi : x.val + y.val < 9223372036854775808) :
    (core.num.I64.wrapping_add x y).val = x.val + y.val := by
  rw [core.num.I64.wrapping_add, IScalar.wrapping_add_val_eq]
  exact bmod_i64_exact hlo hhi

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

/-! ### `mont_reduce`: the next reduction spec to prove

The natural use of the `*_exact` lemmas above.

`mont_reduce a` computes `t := (a mod 2^32) · p⁻¹`, reinterpreted as an `i32`, and returns
`(a - t·p) >> 32`.  The argument has four steps:

1. `p · P_INV ≡ 1 (mod 2^32)` (checked in Rust by `literal_constants_are_correct`), so
   `t·p ≡ a (mod 2^32)` and hence `2^32 ∣ a - t·p`.
2. Therefore the arithmetic shift by 32 is exact division, and `result · 2^32 = a - t·p`.
3. `t·p ≡ 0 (mod p)`, so `result · 2^32 ≡ a (mod p)` — the Montgomery property.
4. `|a| < 2^31·p` and `|t| ≤ 2^31` give `|a - t·p| < 2^32·p`, hence `|result| < p`; this also
   keeps the `i64` operations in range for `I64_wrapping_sub_exact` / `I64_wrapping_mul_exact`,
   and makes the final `i64 → i32` truncation exact.

Step 1 is the only fiddly part: it has to be done through the `u32`/`i32` casts, where the
value semantics are `Int.bmod`/`Int.emod` rather than plain arithmetic. -/

/-! ### The bridge interface

The transform-level correctness, stated as a **drop-in for `matrix_mul_transpose_spec`**: the
Rust path `from_uniform A → from_secret s → mul_transpose` produces exactly the schoolbook
product that `matrix_mul_transpose_spec` proves `Matrix.mul_transpose A s` produces. Downstream
proofs (`ExpandDecap`, `PkeEncryptTop`, `PkeDecryptTop`) can then replace the schoolbook step
with this one, discharging the magnitude preconditions from the `gen_matrix` / `gen_secret`
magnitude lemmas (still to be proved — see `NTT_REFACTOR_STATUS.md`).

Preconditions are the exactness hypotheses from the top of this file: the uniform operand's
coefficients are `< 2^13`, the secret operand's signed coefficients are bounded by `sBound`,
and `(X, sBound)` satisfies `fitsExactly` (so the integer product lands in `(-p/2, p/2)` and the
mod-`p` computation is exact). `signedOfU16` reads a wrapping-`u16` coefficient as its signed
value, matching `from_secret`'s `as i16 as i32`.

This is the single mathematical hole. It is `sorry`ed, not `axiom`ed, so the `TopLevelTheorems`
audit gate reports it. Its eventual proof is the reduction specs + the CRT butterfly argument
described above. NOTE: the escaping NTT-domain values (`mat_a_ntt` into the public key,
`vec_s_ntt` into the secret key) additionally need `from_uniform_matrix` / `from_secret_matrix`
specs relating them to a mathematical forward NTT; those are part of discharging this hole and
are not yet stated here. -/

/-- Every coefficient of every entry of a uniform matrix operand is `< 2^13`. -/
def UniformBounded {X Y : Usize} (A : Mat X Y) : Prop :=
  ∀ i j c, i < X.val → j < Y.val → c < 256 → (((A.val[i]!).val[j]!).val[c]!).val < 2 ^ 13

/-- Every coefficient of every entry of a secret matrix operand, read as a signed `i16`, has
absolute value `≤ sBound`. -/
def SecretBounded {X Z : Usize} (s : Mat X Z) (sBound : ℤ) : Prop :=
  ∀ i k c, i < X.val → k < Z.val → c < 256 →
    |signedOfU16 (((s.val[i]!).val[k]!).val[c]!)| ≤ sBound

/-- Two Hoare triples on the same computation combine into one with a conjoined postcondition. -/
theorem spec_and {α} {m : Result α} {P Q : α → Prop}
    (hP : m ⦃ r => P r ⦄) (hQ : m ⦃ r => Q r ⦄) : m ⦃ r => P r ∧ Q r ⦄ := by
  unfold WP.spec WP.theta WP.wp_return at *
  cases m <;> simp_all

/-! ### The NTT representation functions and the decomposed bridge

`from_uniform_matrix` / `from_secret_matrix` map a coefficient matrix into the NTT domain;
`mul` / `mul_transpose` multiply pointwise there.  Because the escaping NTT matrices
(`mat_a_ntt` into the public key, `vec_s_ntt`/`sprime_ntt` into the secret material) are
consumed at a *different* program point than where they are built, the bridge is stated as
four decomposed specs — two constructors and two multipliers — rather than as one bundled
triple.

The coefficient matrix an NTT matrix denotes is recovered by the opaque inverses `nttInvU` /
`nttInvS` (a *function*, so the witness is determined by the stored NTT matrix and needs no
existential when consumed downstream).  Pinning these to the concrete inverse NTT and
discharging the four specs (plus the raw-magnitude lemmas below) is the single mathematical
hole `ntt_spec`; each obligation is `sorry`ed, never `axiom`ed, so the `TopLevelTheorems`
audit gate reports every one of them. -/

/-- The uniform coefficient matrix an NTT matrix denotes (opaque inverse NTT). -/
opaque nttInvU {X Y : Usize} (n : arithmetic.ntt.NttMatrix X Y) : Mat X Y

/-- The secret coefficient matrix an NTT matrix denotes (opaque inverse NTT). -/
opaque nttInvS {X Y : Usize} (n : arithmetic.ntt.NttMatrix X Y) : Mat X Y

/-- **Part of the NTT hole.** `from_uniform_matrix A` denotes `A`. -/
theorem from_uniform_matrix_spec {X Y : Usize} (A : Mat X Y) :
    arithmetic.ntt.NttMatrix.from_uniform_matrix A
      ⦃ (r : arithmetic.ntt.NttMatrix X Y) => nttInvU r = A ⦄ := by
  sorry

/-- **Part of the NTT hole.** `from_secret_matrix s` denotes `s`. -/
theorem from_secret_matrix_spec {X Y : Usize} (s : Mat X Y) :
    arithmetic.ntt.NttMatrix.from_secret_matrix s
      ⦃ (r : arithmetic.ntt.NttMatrix X Y) => nttInvS r = s ⦄ := by
  sorry

/-- **Part of the NTT hole (`ntt_spec`).** Pointwise product of NTT matrices computes the
schoolbook product of the coefficient matrices they denote, in `ℤ[X]/(X²⁵⁶+1)` with `u16`
coefficients — the same postcondition as `matrix_mul_spec` — given the joint magnitude
constraint `fitsExactly`. -/
theorem ntt_mul_spec {X Y Z : Usize}
    (nttA : arithmetic.ntt.NttMatrix X Y) (nttS : arithmetic.ntt.NttMatrix Y Z) (sBound : ℤ)
    (_hfit : fitsExactly Y.val sBound)
    (_hA : UniformBounded (nttInvU nttA)) (_hs : SecretBounded (nttInvS nttS) sBound) :
    arithmetic.ntt.NttMatrix.mul nttA nttS
      ⦃ (r : Mat X Z) =>
          ∀ (i : Nat) (_hi : i < X.val) (k : Nat) (_hk : k < Z.val),
            toRingElem ((r.val[i]!).val[k]!)
              = ∑ jj ∈ Finset.range Y.val,
                  toRingElem (((nttInvU nttA).val[i]!).val[jj]!)
                    * toRingElem (((nttInvS nttS).val[jj]!).val[k]!) ⦄ := by
  sorry

/-- **Part of the NTT hole (`ntt_spec`).** `mul_transpose` of NTT matrices computes the
schoolbook product `Aᵀ·s` of the coefficient matrices they denote, matching
`matrix_mul_transpose_spec`. -/
theorem ntt_mul_transpose_spec {X Y Z : Usize}
    (nttA : arithmetic.ntt.NttMatrix X Y) (nttS : arithmetic.ntt.NttMatrix X Z) (sBound : ℤ)
    (_hfit : fitsExactly X.val sBound)
    (_hA : UniformBounded (nttInvU nttA)) (_hs : SecretBounded (nttInvS nttS) sBound) :
    arithmetic.ntt.NttMatrix.mul_transpose nttA nttS
      ⦃ (r : Mat Y Z) =>
          ∀ (j : Nat) (_hj : j < Y.val) (k : Nat) (_hk : k < Z.val),
            toRingElem ((r.val[j]!).val[k]!)
              = ∑ ii ∈ Finset.range X.val,
                  toRingElem (((nttInvU nttA).val[ii]!).val[j]!)
                    * toRingElem (((nttInvS nttS).val[ii]!).val[k]!) ⦄ := by
  sorry

/-! ### Raw-magnitude lemmas (part of the NTT hole)

The exactness argument for `ntt_mul(_transpose)` needs bounds on the *stored representation*
that the residue-level specs (`gen_matrix_from_seed_spec`, `gen_secret_from_seed_spec`,
`Matrix.deserialize_10`, the rounding of a product to `R10`) discard.  These are stated here as
`sorry`ed Hoare triples so the whole NTT hole is enumerable in one file. -/

/-- `getElem!` after a `List.set` at an in-bounds index (local copy; the file-scoped
copies elsewhere are `private`). -/
private theorem ntt_getElem!_list_set {α : Type _} [Inhabited α] (l : List α) (j : ℕ)
    (v : α) (k : ℕ) (hj : j < l.length) :
    (l.set j v)[k]! = if k = j then v else l[k]! := by
  by_cases h : k = j
  · subst h
    rw [getElem!_pos _ k (by rw [List.length_set]; exact hj), List.getElem_set_self, if_pos rfl]
  · by_cases hk : k < l.length
    · rw [getElem!_pos _ k (by rw [List.length_set]; exact hk),
        List.getElem_set_of_ne (Ne.symm h), ← getElem!_pos _ k hk, if_neg h]
    · rw [getElem!_neg _ k (by rw [List.length_set]; exact hk), getElem!_neg _ k hk, if_neg h]

/-- A 13-bit `from_bytes` deserialization has every `u16` coefficient `< 2^13`. -/
private theorem ntt_from_bytes_raw (bytes : Slice U8) (hlen : bytes.length = 32 * 13) :
    arithmetic.ring_arith.RingElem.deserialize bytes 13#usize
      ⦃ (r : arithmetic.ring_arith.RingElem) =>
          ∀ c (_hc : c < 256), (r.val[c]!).val < 2 ^ 13 ⦄ := by
  unfold arithmetic.ring_arith.RingElem.deserialize
  simp only [consts.RING_DEG, consts.MODULUS_Q_BITS]
  have hlen416 : bytes.length = 416 := by omega
  step*
  have hb : bytes.len = 416#usize := by scalar_tac
  simp only [core.array.TryFromSharedArraySlice.try_from, dif_pos hb, bind_tc_ok,
    core.result.Result.unwrap]
  apply WP.spec_bind (deserialize_13_spec bytes ⟨bytes.val, by scalar_tac⟩ rfl hlen416)
  intro r hr
  simp only [WP.spec_ok]
  intro c hc
  have hb2 : c < r.val.length := by have := r.property; grind
  have heq : (r.val[c]!).val = streamNat bytes (13 * c) 13 := by
    rw [getElem!_pos r.val c hb2]; exact hr c hc
  rw [heq]; exact streamNat_lt _ _ _

/-- **Inner loop, magnitude version.**  If every coefficient of `mat` is `< 2^13`, then so is
every coefficient of the matrix produced after filling row `i`'s remaining columns from the
13-bit `from_bytes` reads (each of which is `< 2^13`). -/
private theorem ntt_gen_matrix_loop0_loop0_bd {L : Usize} (iter : core.ops.range.Range Usize)
    (seed : Array U8 32#usize) (mat : arithmetic.matrix_arith.Matrix L L)
    (buf : Array U8 416#usize) (i : Usize)
    (hi : i.val < L.val) (hend : iter.«end».val = L.val)
    (hmat : ∀ (a b c : ℕ), a < L.val → b < L.val → c < 256 →
        (((mat.val[a]!).val[b]!).val[c]!).val < 2 ^ 13) :
    sample.gen_matrix_from_seed_loop0_loop0 iter seed mat buf i
      ⦃ (result : arithmetic.matrix_arith.Matrix L L × Array U8 416#usize) =>
          ∀ (a b c : ℕ), a < L.val → b < L.val → c < 256 →
            (((result.1.val[a]!).val[b]!).val[c]!).val < 2 ^ 13 ⦄ := by
  unfold sample.gen_matrix_from_seed_loop0_loop0
  by_cases hlt : iter.start.val < iter.«end».val
  · let* ⟨ o, iter1, ho, hstart', hend' ⟩ ← core.iter.range.IteratorRange.next_Usize_some_spec
    rw [ho]; simp only
    have hj_lt : iter.start.val < L.val := by rw [← hend]; exact hlt
    simp only [consts.MODULUS_Q_BITS]
    step*
    have hs3 : s3.length = 416 := by rw [Slice.length, s3_post1]; exact buf.property
    have hs4 : s4.val.length = 416 := by rw [← Slice.length, __post1, hs3]
    have hs5len : ((buf.from_slice s4).to_slice).length = 32 * 13 := by
      simp only [Slice.length, Array.to_slice, Array.from_slice_val buf s4 hs4]; omega
    simp only [s5_post, s3_post2]
    let* ⟨ re, hre ⟩ ← ntt_from_bytes_raw _ hs5len
    let* ⟨ row, index_mut_back, hrow, hback ⟩ ← Array.index_mut_usize_spec
    let* ⟨ a1, ha1 ⟩ ← Array.update_spec
    have h_end_new : iter1.«end».val = L.val := by rw [hend']; exact hend
    apply WP.spec_mono
      (ntt_gen_matrix_loop0_loop0_bd iter1 seed (index_mut_back a1) (buf.from_slice s4) i hi
        h_end_new ?_)
    · rintro r hr a b c ha hb hc; exact hr a b c ha hb hc
    · intro a b c ha hb hc
      have hml : i.val < mat.val.length := by have := mat.property; grind
      rw [hback, Std.Array.set_val_eq]
      by_cases hai : a = i.val
      · subst hai
        rw [ntt_getElem!_list_set mat.val i.val a1 i.val hml, if_pos rfl, ha1,
          Std.Array.set_val_eq]
        have hrl : iter.start.val < row.val.length := by have := row.property; omega
        by_cases hbj : b = iter.start.val
        · subst hbj
          rw [ntt_getElem!_list_set row.val iter.start.val re iter.start.val hrl, if_pos rfl]
          exact hre c hc
        · rw [ntt_getElem!_list_set row.val iter.start.val re b hrl, if_neg hbj]
          have hbe : row.val[b]! = (mat.val[i.val]!).val[b]! := by
            rw [hrow, getElem!_pos mat.val i.val hml]
          rw [hbe]; exact hmat i.val b c hi hb hc
      · rw [ntt_getElem!_list_set mat.val i.val a1 a hml, if_neg hai]
        exact hmat a b c ha hb hc
  · let* ⟨ o, iter1, hnone, _ ⟩ ← core.iter.range.IteratorRange.next_Usize_none_spec
    rw [hnone]; simp only [WP.spec_ok]
    exact hmat

/-- **Outer loop, magnitude version.**  Preserves the `< 2^13` bound on every coefficient. -/
private theorem ntt_gen_matrix_loop0_bd {L : Usize} (iter : core.ops.range.Range Usize)
    (seed : Array U8 32#usize) (mat : arithmetic.matrix_arith.Matrix L L)
    (buf : Array U8 416#usize) (hend : iter.«end».val = L.val)
    (hmat : ∀ (a b c : ℕ), a < L.val → b < L.val → c < 256 →
        (((mat.val[a]!).val[b]!).val[c]!).val < 2 ^ 13) :
    sample.gen_matrix_from_seed_loop0 iter seed mat buf
      ⦃ (result : arithmetic.matrix_arith.Matrix L L) =>
          ∀ (a b c : ℕ), a < L.val → b < L.val → c < 256 →
            (((result.val[a]!).val[b]!).val[c]!).val < 2 ^ 13 ⦄ := by
  unfold sample.gen_matrix_from_seed_loop0
  by_cases hlt : iter.start.val < iter.«end».val
  · let* ⟨ o, iter1, ho, hstart', hend' ⟩ ← core.iter.range.IteratorRange.next_Usize_some_spec
    rw [ho]; simp only
    have hj_lt : iter.start.val < L.val := by rw [← hend]; exact hlt
    let* ⟨ mat1, buf1, hpr ⟩ ←
      ntt_gen_matrix_loop0_loop0_bd { start := 0#usize, «end» := L } seed mat buf iter.start hj_lt
        rfl hmat
    have h_end_new : iter1.«end».val = L.val := by rw [hend']; exact hend
    apply WP.spec_mono (ntt_gen_matrix_loop0_bd iter1 seed mat1 buf1 h_end_new hpr)
    rintro r hr a b c ha hb hc; exact hr a b c ha hb hc
  · let* ⟨ o, iter1, hnone, _ ⟩ ← core.iter.range.IteratorRange.next_Usize_none_spec
    rw [hnone]; simp only [WP.spec_ok]
    exact hmat

/-- **Part of the NTT hole.** A matrix sampled from a seed has every `u16` coefficient `< 2^13`
(the 13-bit `from_bytes` read keeps them in `[0, 2^13)`). -/
theorem gen_matrix_uniformBounded {L : Usize} (seed : Array U8 32#usize) :
    sample.gen_matrix_from_seed L seed
      ⦃ (r : arithmetic.matrix_arith.Matrix L L) => UniformBounded r ⦄ := by
  unfold sample.gen_matrix_from_seed
  simp only [arithmetic.matrix_arith.Matrix.Insts.CoreDefaultDefault.default,
    arithmetic.ring_arith.RingElem.Insts.CoreDefaultDefault.default, bind_tc_ok]
  apply WP.spec_mono (ntt_gen_matrix_loop0_bd { start := 0#usize, «end» := L } seed _ _ rfl ?_)
  · intro r hr i j c hi hj hc; exact hr i j c hi hj hc
  · intro a b c ha hb hc
    rw [Array.repeat_val, getElem!_pos _ a (by rw [List.length_replicate]; exact ha),
      List.getElem_replicate, Array.repeat_val,
      getElem!_pos _ b (by rw [List.length_replicate]; exact hb), List.getElem_replicate,
      Array.repeat_val, getElem!_pos _ c (by rw [List.length_replicate]; exact hc),
      List.getElem_replicate]
    decide

/-- **Part of the NTT hole.** A CBD secret sampled from a seed has every coefficient, read as a
signed `i16`, bounded in absolute value by `μ/2`. -/
theorem gen_secret_secretBounded {L MU : Usize} (seed : Array U8 32#usize) :
    sample.gen_secret_from_seed L MU seed
      ⦃ (r : arithmetic.matrix_arith.Matrix L 1#usize) =>
          SecretBounded r ((MU.val / 2 : ℕ) : ℤ) ⦄ := by
  sorry

/-- **Part of the NTT hole.** Deserializing 10-bit-packed bytes yields coefficients `< 2^10`,
hence `< 2^13`. -/
theorem deserialize_10_uniformBounded {L : Usize} (bytes : Slice U8) :
    arithmetic.matrix_arith.Matrix.deserialize_10 L 1#usize bytes
      ⦃ (r : arithmetic.matrix_arith.Matrix L 1#usize) => UniformBounded r ⦄ := by
  sorry

/-- `toRingElem`'s coefficient value is the physical `u16` value (local copy of the
`RoundTop` helper, which this file does not import). -/
private theorem ntt_toRingElem_coeff_val (re : arithmetic.ring_arith.RingElem)
    (k : ℕ) (hk : k < 256) :
    ((toRingElem re)[k]!).val = (re.val[k]!).val := by
  have hb : k < re.val.length := by have := re.property; grind
  have hlt : (re.val[k]'hb).val < 2 ^ 16 := by
    have h := (re.val[k]'hb).hBounds; simpa only [UScalarTy.numBits] using h
  rw [getElem!_pos (toRingElem re) k hk, getElem!_pos re.val k hb]
  simp only [toRingElem, Vector.getElem_ofFn]
  rw [ZMod.val_natCast, Nat.mod_eq_of_lt hlt]

/-- **Part of the NTT hole.** A right shift by `Q_BITS - P_BITS = 3` produces `u16`
coefficients `< 2^13` (a 16-bit value shifted right by 3 is `< 2^13`). -/
theorem shift_right_uniformBounded {L : Usize}
    (self : arithmetic.matrix_arith.Matrix L 1#usize) (sh : Usize) (h : sh.val = 3) :
    arithmetic.matrix_arith.Matrix.shift_right self sh
      ⦃ (r : arithmetic.matrix_arith.Matrix L 1#usize) => UniformBounded r ⦄ := by
  have hsh : sh.val < 16 := by omega
  apply WP.spec_mono (matrix_shift_right_spec self sh hsh)
  intro r hr i j c hi hj hc
  have he := hr i hi j hj
  have hb16 : (((self.val[i]!).val[j]!).val[c]!).val < 2 ^ 16 := by
    have hh := (((self.val[i]!).val[j]!).val[c]!).hBounds
    simpa only [UScalarTy.numBits] using hh
  have hrv : (((r.val[i]!).val[j]!).val[c]!).val
      = (((self.val[i]!).val[j]!).val[c]!).val >>> sh.val := by
    rw [← ntt_toRingElem_coeff_val ((r.val[i]!).val[j]!) c hc,
      getElem!_pos (toRingElem ((r.val[i]!).val[j]!)) c hc, he]
    simp only [Spec.Kopis.Polynomial.shiftRight, Vector.getElem_map, ZMod.val_natCast]
    rw [← getElem!_pos (toRingElem ((self.val[i]!).val[j]!)) c hc,
      ntt_toRingElem_coeff_val ((self.val[i]!).val[j]!) c hc]
    have : (((self.val[i]!).val[j]!).val[c]!).val >>> sh.val < 2 ^ 16 := by
      have := Nat.shiftRight_le (((self.val[i]!).val[j]!).val[c]!).val sh.val
      omega
    rw [Nat.mod_eq_of_lt this]
  rw [hrv, h]
  -- `x >>> 3 = x / 8 < 2^16 / 8 = 2^13` since `x < 2^16`
  rw [Nat.shiftRight_eq_div_pow]
  omega

end Kopis.Properties
