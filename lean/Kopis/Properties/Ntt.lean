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

  ## What lives where — the NTT proof is complete

  There is no hole left.  The two obligations this file once carried are both discharged:

  **(1) The transform itself** — that the Cooley-Tukey / Gentleman-Sande networks compute the
  negacyclic convolution mod `p` — lives in `NttMath` (the CRT/convolution mathematics),
  `NttForward` / `NttInverse` (the extracted butterfly networks), `NttMul` (the pointwise
  product and the `mont_reduce → invntt → to_wrapping_u16` pipeline) and `NttBridge`
  (`ntt_mul_spec` / `ntt_mul_transpose_spec`, the matrix-level statements).

  **(2) Raw magnitude lemmas — the ones that were easy to miss.**  The exactness argument needs
  bounds on the *stored representation*: that a `gen_matrix_from_seed` coefficient really is
  `< 2^13` as a `u16`, that a `gen_secret_from_seed` coefficient really denotes something in
  `[-μ/2, μ/2]` when read as an `i16`, and that a rounded vector's coefficients are `< 2^10`.
  The rest of the development abstracts to residues almost immediately —
  `gen_matrix_from_seed_spec` concludes `toMatrix13 r = Spec.Kopis.GenMat …` in `ZMod (2^13)`,
  and the `GenSecret*` files work in `ZMod (2^13)` throughout — and a residue says nothing about
  magnitude.  The schoolbook multiplication never needed magnitudes (it is `u16` wrapping
  arithmetic, exact mod `2^16` whatever the inputs), so nothing upstream was ever asked to
  preserve them.  They are proved here (`gen_matrix_uniformBounded`, `gen_secret_secretBounded`,
  `deserialize_10_uniformBounded`, `shift_right_uniformBounded`) and threaded to the call sites.

  Note there is no *roundtrip* obligation anywhere.  The bridge denotes coefficient matrices in
  the forward direction (`nttFwdU`/`nttFwdS`, in `NttBridge`), so `invNTT ∘ NTT = id` and NTT
  injectivity are never needed; the convolution theorem is the whole of the mathematics.
-/
import Kopis.Properties.MulTranspose
import Kopis.Properties.GenMatrix
import Kopis.Properties.DeserializeVec
import Kopis.Properties.GenSecretTop

open Aeneas Aeneas.Std Result RustKopisSerial
open scoped BigOperators

namespace Kopis.Properties

set_option maxHeartbeats 1000000

/-! ## Constants and the exactness margin -/

/-- The CRT modulus the transform's exactness rests on: `q₁·q₂` with `q₁ = 7681`, `q₂ = 10753`
(`CRT_Q` in `src/backend/crt.rs`).  Until 2026-08-04 this was the single 26-bit prime
`p = 50330113`; the portable transform moved to the two-prime scheme the vector backends already
used, and the exactness margin moved with it — the new modulus is 1.64× larger, so every
parameter set that fitted still fits, with more room. -/
def crtQ : ℤ := 82593793

/-- The largest coefficient magnitude of a uniform operand: `2^13 - 1`. -/
def uniformBound : ℤ := 8191

/-- An accumulated product coefficient of an `X`-term row, where the uniform operand's
coefficients are `< 2^13` and the secret operand's are bounded by `sBound`, cannot exceed
`X · 256 · 8191 · sBound` in absolute value.  `fitsExactly` says that bound is strictly inside
`(-q₁q₂/2, q₁q₂/2)`, which is what makes the two-residue computation determine the integer
answer. -/
def fitsExactly (X : ℕ) (sBound : ℤ) : Prop :=
  2 * ((X : ℤ) * 256 * uniformBound * sBound) < crtQ

/-- Kopis-512: `ℓ = 2`, `μ = 10`, so the secret coefficients are bounded by 5. -/
theorem fitsExactly_kopis512 : fitsExactly 2 5 := by
  unfold fitsExactly uniformBound crtQ; norm_num

/-- Kopis-768: `ℓ = 3`, `μ = 8`, so the secret coefficients are bounded by 4.  This is one of
the two worst cases, at 25 162 752 against a limit of 41 296 896. -/
theorem fitsExactly_kopis768 : fitsExactly 3 4 := by
  unfold fitsExactly uniformBound crtQ; norm_num

/-- Kopis-1024: `ℓ = 4`, `μ = 6`, so the secret coefficients are bounded by 3.  The other worst
case, numerically identical to Kopis-768's. -/
theorem fitsExactly_kopis1024 : fitsExactly 4 3 := by
  unfold fitsExactly uniformBound crtQ; norm_num

/-- Every shipped parameter set satisfies the joint exactness constraint with `sBound = μ/2`.
This is what lets the downstream key-generation / encryption / decryption proofs discharge the
`fitsExactly` precondition of the NTT multiplication bridge from the parameter set alone. -/
theorem fitsExactly_paramSet (p : Spec.Kopis.ParameterSet) :
    fitsExactly (Spec.Kopis.ℓ p) ((Spec.Kopis.μ p / 2 : ℕ) : ℤ) := by
  cases p
  · exact fitsExactly_kopis512
  · exact fitsExactly_kopis768
  · exact fitsExactly_kopis1024

/-- How much margin there actually is: at the worst shipped pairing the accumulated coefficient
bound is 16 134 144 below `⌊q₁q₂/2⌋ = 41 296 896`.  Stated separately so that a future parameter
change that silently breaks exactness shows up as a failed proof here.  Under the old single
prime this margin was 2304 — the two-prime modulus is what turned it from thin into ample. -/
theorem margin_is_16134144 :
    crtQ / 2 - ((3 : ℤ) * 256 * uniformBound * 4) = 16134144 := by
  unfold uniformBound crtQ; norm_num

/-- The pairing that does *not* fit, recorded so the joint-constraint design is self-evident:
the worst `ℓ` together with the worst `μ` overflows the modulus by a wide margin. -/
theorem worst_ell_with_worst_mu_does_not_fit : ¬ fitsExactly 4 5 := by
  unfold fitsExactly uniformBound crtQ; norm_num


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
/-! ## The shape of the transform proof

Everything above is arithmetic bookkeeping.  The mathematical content of the NTT is developed in
`NttCrtZeta` / `NttCrtLane` / `NttCrtLevel` / `NttCrtBlock` / `NttCrtElem` / `NttBridge`; the
route it takes is the one sketched here.

**The proof route.**  Work level by level over the Cooley-Tukey network, using the CRT splitting

    ℤ_q[X]/(X^{2m} - ζ²)  ≅  ℤ_q[X]/(X^m - ζ)  ×  ℤ_q[X]/(X^m + ζ),

whose forward direction is exactly one butterfly layer and whose inverse is exactly one
Gentleman-Sande layer.  After eight levels `X²⁵⁶ + 1` has split into 256 linear factors, so the
transformed array is the tuple of evaluations and pointwise multiplication is multiplication in
the product ring.  All of that happens *twice*, over `q₁ = 7681` and `q₂ = 10753`; the pair of
residues determines the coefficient because the accumulated product is inside `±q₁q₂/2`, which is
what `fitsExactly` above says.  The Montgomery factor each `mont_mul` introduces is cancelled by
`INVNTT_SCALE` at the end of `invntt_block`, and the lazy-reduction schedule (Barrett after levels
3 and 6 forward, after every second level inverse) is what keeps every intermediate inside an
`i16`.

Nothing here is assumed: the audit gate in `TopLevelTheoremsSerial.lean` throws on `sorryAx`, so a
regression that reopened any of it would fail the build. -/

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

The bridge itself is in `NttBridge.lean`: `nttFwdU`/`nttFwdS` denote the escaping NTT-domain
values (`mat_a_ntt` into the public key, `vec_s_ntt` into the secret key) as the forward images
of named coefficient matrices, and `ntt_mul_spec` / `ntt_mul_transpose_spec` are the multiplier
statements.  The magnitude lemmas below are what discharge their preconditions at the call
sites. -/

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

/-! ### Raw-magnitude lemmas

The exactness argument for `ntt_mul(_transpose)` needs bounds on the *stored representation*
that the residue-level specs (`gen_matrix_from_seed_spec`, `gen_secret_from_seed_spec`,
`Matrix.deserialize_10`, the rounding of a product to `R10`) discard.  All four are proved
here, in one file, so the exactness preconditions are enumerable in one place. -/

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

/-- **Exactness precondition.** A matrix sampled from a seed has every `u16` coefficient `< 2^13`
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

/-- A small-signed `u16` (magnitude `≤ h ≤ 2¹⁵−1`) reads through `signedOfU16` as an integer of
absolute value `≤ h`. -/
theorem signedOfU16_le_of_smallSigned {v : U16} {h : ℕ}
    (hs : smallSignedU16 v h) (hh : h ≤ 32767) : |signedOfU16 v| ≤ (h : ℤ) := by
  have hn16 : v.val < 65536 := by scalar_tac
  have h216 : (2 : ℕ) ^ 16 = 65536 := by norm_num
  unfold smallSignedU16 at hs
  rw [h216] at hs
  unfold signedOfU16
  rcases hs with hlow | hhigh <;> split_ifs with hcond <;> rw [abs_le] <;> constructor <;> omega

/-- **Exactness precondition.** A CBD secret sampled from a seed has every
coefficient, read as a signed `i16`, bounded in absolute value by `μ/2`.  The `μ ∈ {6, 8, 10}`
hypothesis matches `gen_secret_from_seed_spec` (already in scope at every call site) and is
needed because the extracted sampler only succeeds for those shipped parameter widths (for
larger `μ` the fixed 320-byte CBD buffer slice is out of range and the computation fails). -/
theorem gen_secret_secretBounded {L MU : Usize} (seed : Array U8 32#usize)
    (hMU : MU.val = 6 ∨ MU.val = 8 ∨ MU.val = 10) :
    sample.gen_secret_from_seed L MU seed
      ⦃ (r : arithmetic.matrix_arith.Matrix L 1#usize) =>
          SecretBounded r ((MU.val / 2 : ℕ) : ℤ) ⦄ := by
  apply WP.spec_mono (gen_secret_from_seed_bd L MU seed hMU)
  intro r hr i k c hi hk hc
  have hk0 : k = 0 := by have : (1#usize).val = 1 := rfl; omega
  subst hk0
  exact signedOfU16_le_of_smallSigned (hr i hi c hc) (by omega)

set_option maxRecDepth 20000

/-- A 10-bit `RingElem.deserialize` has every `u16` coefficient `< 2^10`. -/
private theorem ntt_ringElem_deser10_raw (bytes : Slice U8) (hlen : bytes.length = 32 * 10) :
    arithmetic.ring_arith.RingElem.deserialize bytes 10#usize
      ⦃ (r : arithmetic.ring_arith.RingElem) =>
          ∀ c (_hc : c < 256), (r.val[c]!).val < 2 ^ 10 ⦄ := by
  unfold arithmetic.ring_arith.RingElem.deserialize
  simp only [consts.RING_DEG, consts.MODULUS_Q_BITS, consts.10]
  have hlen320 : bytes.length = 320 := by omega
  step*
  have hb : bytes.len = 320#usize := by scalar_tac
  simp only [core.array.TryFromSharedArraySlice.try_from, dif_pos hb, bind_tc_ok,
    core.result.Result.unwrap]
  apply WP.spec_bind (deserialize_10_spec bytes ⟨bytes.val, by scalar_tac⟩ rfl hlen320)
  intro r hr
  simp only [WP.spec_ok]
  intro c hc
  have hb2 : c < r.val.length := by have := r.property; grind
  have heq : (r.val[c]!).val = streamNat bytes (10 * c) 10 := by
    rw [getElem!_pos r.val c hb2]; exact hr c hc
  rw [heq]; exact streamNat_lt _ _ _

/-- **Inner loop, magnitude version** of `Matrix.deserialize_10` (`Y = 1`).  Writing row `i`'s
single column with a 10-bit `RingElem.deserialize` (coefficients `< 2^10 < 2^13`) preserves the
`< 2^13` bound. -/
private theorem ntt_matrix_deser10_inner_bd {L : Usize}
    (iter : core.ops.range.Range Usize)
    (bytes : Slice U8) (result : arithmetic.matrix_arith.Matrix L 1#usize)
    (chunk_len : Usize) (i : Usize)
    (hchunk : chunk_len.val = 32 * 10)
    (hi : i.val < L.val) (hlen : bytes.length = L.val * (32 * 10))
    (hs0 : iter.start.val = 0) (hend : iter.«end».val = 1)
    (hres : ∀ a (_ha : a < L.val) c (_hc : c < 256),
        (((result.val[a]!).val[0]!).val[c]!).val < 2 ^ 13) :
    arithmetic.matrix_arith.Matrix.deserialize_10_loop0_loop0 (X := L) (Y := 1#usize)
        iter bytes result chunk_len i
      ⦃ (r : arithmetic.matrix_arith.Matrix L 1#usize) =>
          ∀ a (_ha : a < L.val) c (_hc : c < 256),
            (((r.val[a]!).val[0]!).val[c]!).val < 2 ^ 13 ⦄ := by
  unfold arithmetic.matrix_arith.Matrix.deserialize_10_loop0_loop0
  have hm : 0 < 32 * 10 := by norm_num
  have hbufmax : L.val * (32 * 10) ≤ Usize.max := hlen ▸ bytes.property
  have hlt : iter.start.val < iter.«end».val := by omega
  let* ⟨ o, iter1, ho, hstart', hend' ⟩ ← core.iter.range.IteratorRange.next_Usize_some_spec
  rw [ho]; simp only
  let* ⟨ i1, hi1 ⟩ ← Std.Usize.mul_spec (show i.val * (1#usize).val ≤ Usize.max from by
    simpa using le_trans (le_of_lt hi) (le_trans (Nat.le_mul_of_pos_right _ hm) hbufmax))
  have hi1v : i1.val = i.val := by rw [hi1]; simp
  let* ⟨ idx, hidx ⟩ ← Std.Usize.add_spec (show i1.val + iter.start.val ≤ Usize.max from by
    rw [hi1v, hs0]
    simpa using le_trans (le_of_lt hi) (le_trans (Nat.le_mul_of_pos_right _ hm) hbufmax))
  have hidxv : idx.val = i.val := by rw [hidx, hi1v, hs0]; omega
  let* ⟨ i2, hi2 ⟩ ← Std.Usize.mul_spec (show idx.val * chunk_len.val ≤ Usize.max from by
    rw [hidxv, hchunk]; exact le_trans (Nat.mul_le_mul_right (32 * 10) (le_of_lt hi)) hbufmax)
  have hi2v : i2.val = i.val * (32 * 10) := by rw [hi2, hidxv, hchunk]
  let* ⟨ i3, hi3 ⟩ ← Std.Usize.add_spec (show idx.val + (1#usize).val ≤ Usize.max from by
    rw [hidxv]
    simpa using le_trans (le_trans (show i.val + 1 ≤ L.val by omega) (Nat.le_mul_of_pos_right _ hm)) hbufmax)
  have hi3v : i3.val = i.val + 1 := by rw [hi3, hidxv]
  let* ⟨ i4, hi4 ⟩ ← Std.Usize.mul_spec (show i3.val * chunk_len.val ≤ Usize.max from by
    rw [hi3v, hchunk]; exact le_trans (Nat.mul_le_mul_right (32 * 10) (by omega)) hbufmax)
  have hi4v : i4.val = (i.val + 1) * (32 * 10) := by rw [hi4, hi3v, hchunk]
  have hle : i2.val ≤ i4.val := by rw [hi2v, hi4v]; exact Nat.mul_le_mul_right _ (by omega)
  have hbnd : i4.val ≤ bytes.length := by rw [hi4v, hlen]; exact Nat.mul_le_mul_right _ (by omega)
  have hbndl : i4.val ≤ bytes.val.length := by have := hbnd; simp only [Slice.length] at this; exact this
  have hchunk_spec : core.slice.index.SliceIndexRangeUsizeSlice.index
        ({ start := i2, «end» := i4 } : core.ops.range.Range Usize) bytes
      ⦃ (s : Slice U8) => s.val = bytes.val.slice i2.val i4.val ∧ s.length = 32 * 10 ⦄ := by
    simp only [core.slice.index.SliceIndexRangeUsizeSlice.index, UScalar.le_equiv]
    rw [if_pos ⟨hle, hbnd⟩]
    simp only [WP.spec_ok]
    refine ⟨trivial, ?_⟩
    show (bytes.val.slice i2.val i4.val).length = 32 * 10
    rw [List.slice_length, hi2v, hi4v]
    have h1 : (i.val + 1) * (32 * 10) ≤ bytes.val.length := hi4v ▸ hbndl
    omega
  let* ⟨ chunk, hchunk_val, hchunk_len ⟩ ← hchunk_spec
  let* ⟨ re, hre ⟩ ← ntt_ringElem_deser10_raw chunk hchunk_len
  have hib : i.val < result.val.length := by have := result.property; omega
  let* ⟨ row, index_mut_back, hrow, hback ⟩ ← Array.index_mut_usize_spec result i hib
  have hrowlen : row.val.length = 1 := by have := row.property; scalar_tac
  let* ⟨ a1, ha1 ⟩ ← Array.update_spec
  unfold arithmetic.matrix_arith.Matrix.deserialize_10_loop0_loop0
  let* ⟨ o2, iter2, hnone2, _ ⟩ ← core.iter.range.IteratorRange.next_Usize_none_spec iter1
    (show iter1.start.val ≥ iter1.«end».val by rw [hstart', hend']; omega)
  rw [hnone2]; simp only [WP.spec_ok]
  intro a _ha c hc
  rw [hback]
  simp only [Array.set_val_eq]
  by_cases hai : a = i.val
  · subst hai
    rw [ntt_getElem!_list_set result.val i.val a1 i.val hib, if_pos rfl, ha1]
    simp only [Array.set_val_eq]
    rw [hs0, ntt_getElem!_list_set row.val 0 re 0 (by rw [hrowlen]; omega), if_pos rfl]
    have := hre c hc; omega
  · rw [ntt_getElem!_list_set result.val i.val a1 a hib, if_neg hai]
    exact hres a _ha c hc

/-- **Outer loop, magnitude version** of `Matrix.deserialize_10` (`Y = 1`). -/
private theorem ntt_matrix_deser10_outer_bd {L : Usize}
    (iter : core.ops.range.Range Usize)
    (bytes : Slice U8) (result : arithmetic.matrix_arith.Matrix L 1#usize)
    (chunk_len : Usize)
    (hchunk : chunk_len.val = 32 * 10)
    (hlen : bytes.length = L.val * (32 * 10))
    (hstart : iter.start.val ≤ L.val) (hend : iter.«end».val = L.val)
    (hres : ∀ a (_ha : a < L.val) c (_hc : c < 256),
        (((result.val[a]!).val[0]!).val[c]!).val < 2 ^ 13) :
    arithmetic.matrix_arith.Matrix.deserialize_10_loop0 (X := L) (Y := 1#usize)
        iter bytes result chunk_len
      ⦃ (r : arithmetic.matrix_arith.Matrix L 1#usize) =>
          ∀ a (_ha : a < L.val) c (_hc : c < 256),
            (((r.val[a]!).val[0]!).val[c]!).val < 2 ^ 13 ⦄ := by
  unfold arithmetic.matrix_arith.Matrix.deserialize_10_loop0
  by_cases hlt : iter.start.val < iter.«end».val
  · let* ⟨ o, iter1, ho, hstart', hend' ⟩ ← core.iter.range.IteratorRange.next_Usize_some_spec
    rw [ho]; simp only
    have hi_lt : iter.start.val < L.val := by scalar_tac
    let* ⟨ result1, hres1 ⟩ ←
      ntt_matrix_deser10_inner_bd { start := 0#usize, «end» := 1#usize } bytes result
        chunk_len iter.start hchunk hi_lt hlen (by simp) (by simp) hres
    apply WP.spec_mono
      (ntt_matrix_deser10_outer_bd iter1 bytes result1 chunk_len hchunk hlen
        (by rw [hstart']; scalar_tac) (by rw [hend']; exact hend) hres1)
    intro r hr a ha c hc; exact hr a ha c hc
  · let* ⟨ o, iter1, hnone, _ ⟩ ← core.iter.range.IteratorRange.next_Usize_none_spec
    rw [hnone]; simp only [WP.spec_ok]
    exact hres
  termination_by iter.«end».val - iter.start.val
  decreasing_by scalar_decr_tac

/-- **Exactness precondition.** Deserializing an `L × 1` matrix of 10-bit-packed
coefficients from an `L·320`-byte buffer yields every `u16` coefficient `< 2^10 < 2^13`.  The
length and no-overflow hypotheses match `matrix_deserialize_10_spec` (both are already in scope
at every call site) and are needed because the extracted code `massert`s the buffer length and
performs checked size multiplications. -/
theorem deserialize_10_uniformBounded {L : Usize} (bytes : Slice U8)
    (hlen : bytes.length = L.val * (32 * 10)) (hfit : L.val * 10 * 256 ≤ Usize.max) :
    arithmetic.matrix_arith.Matrix.deserialize_10 L 1#usize bytes
      ⦃ (r : arithmetic.matrix_arith.Matrix L 1#usize) => UniformBounded r ⦄ := by
  unfold arithmetic.matrix_arith.Matrix.deserialize_10
  simp only [consts.RING_DEG]
  have hm : 0 < 32 * 10 := by norm_num
  have hbufmax : L.val * (32 * 10) ≤ Usize.max := hlen ▸ bytes.property
  have hLmax : L.val ≤ Usize.max := le_trans (Nat.le_mul_of_pos_right _ hm) hbufmax
  have hb1 : L.val * 10 ≤ Usize.max := by have := hfit; omega
  have hsz : ∀ x : ℕ, x ≤ Usize.max → x < UScalar.size .Usize := by
    intro x hx
    have h1 : UScalar.size .Usize = 2 ^ System.Platform.numBits := by
      simp only [UScalar.size, UScalarTy.Usize_numBits_eq]
    have h2 : (Usize.max : ℕ) = 2 ^ System.Platform.numBits - 1 := by
      simp only [Usize.max, Usize.numBits, UScalarTy.Usize_numBits_eq]
    have h3 : 0 < 2 ^ System.Platform.numBits := by positivity
    omega
  let* ⟨ i, hi ⟩ ← Std.Usize.mul_spec (show L.val * (1#usize).val ≤ Usize.max from by
    simp only [show (1#usize).val = 1 from rfl, Nat.mul_one]; exact hLmax)
  have hiv : i.val = L.val := by rw [hi]; simp
  let* ⟨ i1, hi1 ⟩ ← Std.Usize.mul_spec (show i.val * (10#usize).val ≤ Usize.max from by
    rw [hiv]; simp only [show (10#usize).val = 10 from rfl]; omega)
  have hi1v : i1.val = L.val * 10 := by rw [hi1, hiv]
  let* ⟨ iu, hiu ⟩ ← Std.Usize.mul_spec (show i1.val * (256#usize).val ≤ Usize.max from by
    rw [hi1v]; simp only [show (256#usize).val = 256 from rfl]; omega)
  simp only [lift, bind_tc_ok]
  let* ⟨ right_val, hrv ⟩ ← Std.Usize.div_spec
  have hrvv : right_val.val = L.val * (32 * 10) := by
    rw [hrv]
    simp only [Std.Usize.wrapping_mul_val_eq, show (1#usize).val = 1 from rfl,
      show (10#usize).val = 10 from rfl, show (256#usize).val = 256 from rfl, Nat.mul_one]
    rw [Nat.mod_eq_of_lt (hsz _ hLmax), Nat.mod_eq_of_lt (hsz _ hb1),
      Nat.mod_eq_of_lt (hsz _ hfit),
      show L.val * 10 * 256 = L.val * (32 * 10) * 8 from by ring,
      Nat.mul_div_cancel _ (by norm_num)]
  have hmeq : Slice.len bytes = right_val :=
    UScalar.eq_of_val_eq (by rw [Slice.len_val, hrvv]; exact hlen)
  rw [show massert (Slice.len bytes = right_val) = ok () from by
    simp only [massert, if_pos hmeq], bind_tc_ok]
  have hdef : arithmetic.matrix_arith.Matrix.Insts.CoreDefaultDefault.default L 1#usize
      = ok (Array.repeat L (Array.repeat 1#usize (Array.repeat 256#usize 0#u16))) := by
    simp only [arithmetic.matrix_arith.Matrix.Insts.CoreDefaultDefault.default,
      arithmetic.ring_arith.RingElem.Insts.CoreDefaultDefault.default, bind_tc_ok]
  rw [hdef, bind_tc_ok]
  let* ⟨ i5, hi5 ⟩ ← Std.Usize.mul_spec (show (10#usize).val * (256#usize).val ≤ Usize.max from by
    have h2560 : (10#usize).val * (256#usize).val = 2560 := rfl
    rw [h2560]
    rcases Usize.bounds_eq with h | h <;> rw [h] <;> simp only [U32.max_eq, U64.max_eq] <;> omega)
  let* ⟨ chunk_len, hcl ⟩ ← Std.Usize.div_spec
  have hcv : chunk_len.val = 32 * 10 := by rw [hcl, hi5]
  apply WP.spec_mono
    (ntt_matrix_deser10_outer_bd { start := 0#usize, «end» := L } bytes _ chunk_len
      hcv hlen (by simp) rfl ?_)
  · intro r hr i j c hi hj hc
    have hj0 : j = 0 := by have : (1#usize).val = 1 := rfl; omega
    subst hj0
    exact hr i hi c hc
  · intro a _ha c hc
    rw [Array.repeat_val, getElem!_pos _ a (by rw [List.length_replicate]; exact _ha),
      List.getElem_replicate, Array.repeat_val,
      getElem!_pos _ 0 (by rw [List.length_replicate]; norm_num), List.getElem_replicate,
      Array.repeat_val, getElem!_pos _ c (by rw [List.length_replicate]; exact hc),
      List.getElem_replicate]
    decide

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

/-- **Exactness precondition.** A right shift by `Q_BITS - P_BITS = 3` produces `u16`
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
