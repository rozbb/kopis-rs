#!/usr/bin/env python3
"""The `NttBridge` twin's patch, applied by `scripts/gen_avx2_twins.py`.

`Kopis/Properties/NttBridge.lean` is the one module of the serial stack whose proof cannot be
transferred by renaming: it names the *contents of an `NttElem`*, and the two backends store
different things there — one residue mod `p = 50330113` against two 16-bit residues, mod
`q1 = 7681` and `q2 = 10753`, packed into one `i32`.  The edits below bridge that, and they are
large enough to deserve their own file.

The fix, in four moves:

  1. The two element constructors and the two accumulate loops *are* dispatch points, so their
     serial statements hold only on the portable branch: they take `cpu.available = ok false`.
  2. `ElemOK` is replaced, at the matrix-loop level, by `UOK` / `SOK`, which carry one reading
     per outcome of the probe.  `available_ok` fixes one boolean for every call site, so exactly
     one conjunct is ever used, and the loops go on treating the predicate opaquely.
  3. `ntt_mul_inner_spec` + `ntt_entry_spec` are bundled into `ntt_inner_entry_spec` (and its
     `mul_transpose` twin), whose statement mentions only ring elements.  That is the single
     place the representation difference lives; the three nested loops above it are unchanged.
  4. The vector `from_secret` transforms without a leading Barrett reduction, so it needs its
     input already centred.  `SecretSmall` threads that one condition through the secret matrix
     loops, and `secretSmall_of_bounded` / `secretSmall_of_fit` discharge it from the magnitude
     hypotheses every call site already carries.

Every edit is anchored on exact serial text and asserted to apply exactly `n` times, so a change
to the serial proof fails the generator loudly rather than silently producing a stale twin.
"""

_EDITS: list = []


def rep(old: str, new: str, cnt: int = 1) -> None:
    _EDITS.append((old, new, cnt))


# ---------------------------------------------------------------------------
# the branch-dependent element predicates
# ---------------------------------------------------------------------------
# --- extra import ---------------------------------------------------------
rep("import Kopis.Bits.Stream\n", "import Kopis.Bits.Stream\nimport Kopis.Avx2.MulT\n")

# --- 1. the two element constructors, on the portable branch --------------
rep("theorem from_uniform_elem_spec (elem : arithmetic.ring_arith.RingElem) :",
    "theorem from_uniform_elem_spec (hb : backend.avx2.cpu.available = ok false)\n"
    "    (elem : arithmetic.ring_arith.RingElem) :")
rep("""  unfold arithmetic.ntt.NttElem.from_uniform
  have hRD :""",
    """  unfold arithmetic.ntt.NttElem.from_uniform
  rw [hb, bind_tc_ok]
  simp only [Bool.false_eq_true, if_false, bind_tc_ok]
  have hRD :""")
rep("theorem from_secret_elem_spec (elem : arithmetic.ring_arith.RingElem) :",
    "theorem from_secret_elem_spec (hb : backend.avx2.cpu.available = ok false)\n"
    "    (elem : arithmetic.ring_arith.RingElem) :")
rep("""  unfold arithmetic.ntt.NttElem.from_secret
  have hRD :""",
    """  unfold arithmetic.ntt.NttElem.from_secret
  rw [hb, bind_tc_ok]
  simp only [Bool.false_eq_true, if_false, bind_tc_ok]
  have hRD :""")

# --- 2. the denotations are noncomputable here (the intrinsics are axioms) -
rep("def nttFwdU {X Y : Usize} (A : Mat X Y) : arithmetic.ntt.NttMatrix X Y :=",
    "noncomputable def nttFwdU {X Y : Usize} (A : Mat X Y) : arithmetic.ntt.NttMatrix X Y :=")
rep("def nttFwdS {X Y : Usize} (s : Mat X Y) : arithmetic.ntt.NttMatrix X Y :=",
    "noncomputable def nttFwdS {X Y : Usize} (s : Mat X Y) : arithmetic.ntt.NttMatrix X Y :=")

# --- 3. UOK / SOK -----------------------------------------------------------
rep("""theorem from_uniform_elemOK (elem : arithmetic.ring_arith.RingElem) :
    arithmetic.ntt.NttElem.from_uniform elem
      ⦃ (r : arithmetic.ntt.NttElem) => ElemOK (uP elem) r ⦄ :=
  from_uniform_elem_spec elem

theorem from_secret_elemOK (elem : arithmetic.ring_arith.RingElem) :
    arithmetic.ntt.NttElem.from_secret elem
      ⦃ (r : arithmetic.ntt.NttElem) => ElemOK (sP elem) r ⦄ :=
  from_secret_elem_spec elem
""",
r"""/-! ### AVX2 only: the branch-dependent element predicates

The two backends do not build the same array.  The portable `from_uniform` widens each `u16` into
one residue mod `p = 50330113`; the vector one packs two 16-bit residues, mod `q₁ = 7681` and
`q₂ = 10753`, into each `i32`.  `ElemOK` names the mod-`p` reading, so it is *false* on the vector
branch, not merely unproved, and no single predicate serves both.

`UOK` / `SOK` carry one reading per outcome of `cpu::available`.  `available_ok` fixes one boolean
for every call site, so exactly one conjunct is ever used and the other is discharged vacuously.
Everything between the constructors and `ntt_inner_entry_spec` treats them opaquely, which is why
the matrix bookkeeping still transfers verbatim.

The AVX2 conjuncts carry a hypothesis about the *input* that the portable ones do not need: the
vector path reads the stored `u16`s as `i16`s, so for a uniform operand the two readings agree
only below `2¹⁵` (`UniformBounded` gives `2¹³`).  Attaching it to the predicate rather than to the
matrix loops keeps those loops free of magnitude hypotheses.  `from_secret` is different — it runs
without the Barrett reduction, so its input has to be small for the vector routine's *bound* proof
to run at all, and that one condition (`SecretSmall`) does have to be threaded. -/

/-- A stored `u16` read as an `i16` is exactly its `BitVec` signed reading, which is the form the
AVX2 lane lemmas use. -/
theorem signedOfU16_toInt (v : U16) : (v.bv).toInt = signedOfU16 v := by
  have hn : v.bv.toNat = v.val := rfl
  have hlt : v.val < 65536 := by have := v.hBounds; scalar_tac
  simp only [BitVec.toInt, signedOfU16, hn]
  norm_num
  split <;> split <;> omega

/-- AVX2 only: the input condition the vector `from_secret` needs.  It transforms without a
leading Barrett reduction, so every coefficient must already be centred inside both primes. -/
def SecretSmall {X Y : Usize} (s : Mat X Y) : Prop :=
  ∀ a b c, a < X.val → b < Y.val → c < 256 →
    2 * |signedOfU16 (((s.val[a]!).val[b]!).val[c]!)| < 7681

theorem secretSmall_of_bounded {X Y : Usize} {s : Mat X Y} {b : ℤ}
    (hs : SecretBounded s b) (hb : b ≤ 3840) : SecretSmall s := fun a bb c ha hbb hc => by
  have := hs a bb c ha hbb hc; omega

/-- The magnitude constraint already carried by every multiplier call site implies it: with at
least one inner term, `fitsExactly` forces `sBound ≤ 11`. -/
theorem secretSmall_of_fit {X Y : Usize} {s : Mat X Y} {sBound : ℤ}
    (hfit : fitsExactly X.val sBound) (hs : SecretBounded s sBound) : SecretSmall s := by
  intro a b c ha hb hc
  have h1 := hs a b c ha hb hc
  have h0 : (0:ℤ) ≤ sBound := le_trans (abs_nonneg _) h1
  have hX1 : (1:ℤ) ≤ (X.val : ℤ) := by exact_mod_cast (by omega : 1 ≤ X.val)
  unfold fitsExactly uniformBound pNtt at hfit
  nlinarith [hfit, hX1, h0, h1]

/-- What one call of `from_uniform` establishes, on whichever branch runs. -/
def UOK (elem : arithmetic.ring_arith.RingElem) (ne : arithmetic.ntt.NttElem) : Prop :=
  (backend.avx2.cpu.available = ok false → ElemOK (uP elem) ne)
  ∧ (backend.avx2.cpu.available = ok true →
      (∀ c, c < 256 → (elem.val[c]!).val < 2 ^ 13) → Kopis.Avx2.NttOK (uZ elem) ne)

/-- What one call of `from_secret` establishes, on whichever branch runs. -/
def SOK (elem : arithmetic.ring_arith.RingElem) (ne : arithmetic.ntt.NttElem) : Prop :=
  (backend.avx2.cpu.available = ok false → ElemOK (sP elem) ne)
  ∧ (backend.avx2.cpu.available = ok true →
      (∀ c, c < 256 → 2 * |sZ elem c| < 7681) → Kopis.Avx2.NttOK (sZ elem) ne)

theorem from_uniform_elemOK (elem : arithmetic.ring_arith.RingElem) :
    arithmetic.ntt.NttElem.from_uniform elem
      ⦃ (r : arithmetic.ntt.NttElem) => UOK elem r ⦄ := by
  obtain ⟨b, hb⟩ := Kopis.Avx2.available_ok
  cases b with
  | false =>
    refine WP.spec_mono (from_uniform_elem_spec hb elem) (fun r hr => ⟨fun _ => hr, ?_⟩)
    intro h; rw [hb] at h; exact absurd h (by simp)
  | true =>
    by_cases hub : ∀ c, c < 256 → (elem.val[c]!).val < 2 ^ 13
    · refine WP.spec_mono (Kopis.Avx2.from_uniform_NttOK hb elem (uZ elem) (fun c hc => ?_))
        (fun r hr => ⟨fun h => absurd (hb ▸ h) (by simp), fun _ _ => hr⟩)
      rw [signedOfU16_toInt, signedOfU16, if_pos (by have := hub c hc; omega)]
      rfl
    · refine WP.spec_mono (Kopis.Avx2.from_uniform_NttOK hb elem
        (fun c => (elem.val[c]!).bv.toInt) (fun c hc => rfl))
        (fun r hr => ⟨fun h => absurd (hb ▸ h) (by simp), fun _ h => absurd h hub⟩)

theorem from_secret_elemOK (elem : arithmetic.ring_arith.RingElem)
    (hsm : ∀ c, c < 256 → 2 * |sZ elem c| < 7681) :
    arithmetic.ntt.NttElem.from_secret elem
      ⦃ (r : arithmetic.ntt.NttElem) => SOK elem r ⦄ := by
  obtain ⟨b, hb⟩ := Kopis.Avx2.available_ok
  cases b with
  | false =>
    refine WP.spec_mono (from_secret_elem_spec hb elem) (fun r hr => ⟨fun _ => hr, ?_⟩)
    intro h; rw [hb] at h; exact absurd h (by simp)
  | true =>
    refine WP.spec_mono (Kopis.Avx2.from_secret_NttOK hb elem (sZ elem)
      (fun c hc => signedOfU16_toInt _)
      (fun c hc => hsm c hc)
      (fun c hc => by have := hsm c hc; omega))
      (fun r hr => ⟨fun h => absurd (hb ▸ h) (by simp), fun _ _ => hr⟩)
""")

# --- 4. the matrix loops carry UOK / SOK ----------------------------------
rep("ElemOK (uP ((mat.val[i.val]!).val[b]!))", "UOK ((mat.val[i.val]!).val[b]!)", 1)
rep("ElemOK (uP ((mat.val[a]!).val[b]!))", "UOK ((mat.val[a]!).val[b]!)", 1)
rep("ElemOK (uP ((A.val[a]!).val[b]!))", "UOK ((A.val[a]!).val[b]!)", 2)
rep("ElemOK (sP ((mat.val[i.val]!).val[b]!))", "SOK ((mat.val[i.val]!).val[b]!)", 1)
rep("ElemOK (sP ((mat.val[a]!).val[b]!))", "SOK ((mat.val[a]!).val[b]!)", 1)
rep("ElemOK (sP ((s.val[a]!).val[b]!))", "SOK ((s.val[a]!).val[b]!)", 2)

# ---------------------------------------------------------------------------
# SecretSmall, the entry theorem's tail, and the two inner loops
# ---------------------------------------------------------------------------
# --- (a) secretSmall_of_fit's arithmetic ----------------------------------
rep("""  unfold fitsExactly uniformBound pNtt at hfit
  nlinarith [hfit, hX1, h0, h1]""",
    """  unfold fitsExactly uniformBound pNtt at hfit
  have hstep : (4193792 : ℤ) * sBound ≤ 2 * ((X.val : ℤ) * 256 * 8191 * sBound) := by nlinarith
  omega""")

# --- (b) the secret matrix loops thread `SecretSmall` ----------------------
rep("""theorem from_secret_matrix_inner_spec {X Y : Usize}
    (iter : core.ops.range.Range Usize) (mat : Mat X Y)
    (ret : arithmetic.ntt.NttMatrix X Y) (i : Usize) (hi : i.val < X.val)
    (hend : iter.«end».val = Y.val) :""",
    """theorem from_secret_matrix_inner_spec {X Y : Usize}
    (iter : core.ops.range.Range Usize) (mat : Mat X Y)
    (ret : arithmetic.ntt.NttMatrix X Y) (i : Usize) (hi : i.val < X.val)
    (hend : iter.«end».val = Y.val) (hsm : SecretSmall mat) :""")
rep("""    let* ⟨ne, hne⟩ ← from_secret_elemOK re""",
    """    let* ⟨ne, hne⟩ ← from_secret_elemOK re
      (fun c hc => by unfold sZ; rw [hre']; exact hsm i.val iter.start.val c hi hj_lt hc)""")
rep("""    apply WP.spec_mono (from_secret_matrix_inner_spec iter1 mat (index_mut_back a2) i hi
      (by rw [hend']; exact hend))""",
    """    apply WP.spec_mono (from_secret_matrix_inner_spec iter1 mat (index_mut_back a2) i hi
      (by rw [hend']; exact hend) hsm)""")
rep("""theorem from_secret_matrix_outer_spec {X Y : Usize}
    (iter : core.ops.range.Range Usize) (mat : Mat X Y)
    (ret : arithmetic.ntt.NttMatrix X Y) (hend : iter.«end».val = X.val) :""",
    """theorem from_secret_matrix_outer_spec {X Y : Usize}
    (iter : core.ops.range.Range Usize) (mat : Mat X Y)
    (ret : arithmetic.ntt.NttMatrix X Y) (hend : iter.«end».val = X.val)
    (hsm : SecretSmall mat) :""")
rep("""      from_secret_matrix_inner_spec { start := 0#usize, «end» := Y } mat ret iter.start hi_lt rfl
    subst hm1
    apply WP.spec_mono (from_secret_matrix_outer_spec iter1 mat1 ret1
      (by rw [hend']; exact hend))""",
    """      from_secret_matrix_inner_spec { start := 0#usize, «end» := Y } mat ret iter.start hi_lt rfl
        hsm
    subst hm1
    apply WP.spec_mono (from_secret_matrix_outer_spec iter1 mat1 ret1
      (by rw [hend']; exact hend) hsm)""")
rep("""theorem from_secret_matrix_full {X Y : Usize} (s : Mat X Y) :""",
    """theorem from_secret_matrix_full {X Y : Usize} (s : Mat X Y) (hsm : SecretSmall s) :""")
rep("""  apply WP.spec_mono (from_secret_matrix_outer_spec { start := 0#usize, «end» := X } s _ rfl)""",
    """  apply WP.spec_mono (from_secret_matrix_outer_spec { start := 0#usize, «end» := X } s _ rfl hsm)""")
rep("""theorem from_secret_matrix_ok {X Y : Usize} (s : Mat X Y) :
    arithmetic.ntt.NttMatrix.from_secret_matrix s ⦃ fun _ => True ⦄ :=
  WP.spec_mono (from_secret_matrix_full s) (fun _ _ => trivial)""",
    """theorem from_secret_matrix_ok {X Y : Usize} (s : Mat X Y) (hsm : SecretSmall s) :
    arithmetic.ntt.NttMatrix.from_secret_matrix s ⦃ fun _ => True ⦄ :=
  WP.spec_mono (from_secret_matrix_full s hsm) (fun _ _ => trivial)""")
rep("""theorem from_secret_matrix_spec {X Y : Usize} (s : Mat X Y) :
    arithmetic.ntt.NttMatrix.from_secret_matrix s
      ⦃ (r : arithmetic.ntt.NttMatrix X Y) => r = nttFwdS s ⦄ :=
  spec_eq_getD (from_secret_matrix_ok s)""",
    """theorem from_secret_matrix_spec {X Y : Usize} (s : Mat X Y) (hsm : SecretSmall s) :
    arithmetic.ntt.NttMatrix.from_secret_matrix s
      ⦃ (r : arithmetic.ntt.NttMatrix X Y) => r = nttFwdS s ⦄ :=
  spec_eq_getD (from_secret_matrix_ok s hsm)""")
rep("""theorem nttFwdS_entry {X Y : Usize} (s : Mat X Y) (a b : ℕ) (ha : a < X.val) (hb : b < Y.val) :
    SOK ((s.val[a]!).val[b]!) (((nttFwdS s).val[a]!).val[b]!) :=
  getD_of_spec (from_secret_matrix_full s) a b ha hb""",
    """theorem nttFwdS_entry {X Y : Usize} (s : Mat X Y) (hsm : SecretSmall s)
    (a b : ℕ) (ha : a < X.val) (hb : b < Y.val) :
    SOK ((s.val[a]!).val[b]!) (((nttFwdS s).val[a]!).val[b]!) :=
  getD_of_spec (from_secret_matrix_full s hsm) a b ha hb""")

# --- (c) ntt_entry_spec on the portable branch, with its tail factored out --
rep("""set_option maxRecDepth 8000 in
/-- **The convolution theorem, for one entry.**""",
    r"""/-- AVX2 only: `NttAlg.nconv` and `nconvR` agree below 256 over any commutative ring.  The
serial file proves this only for `Zp`; the AVX2 endpoint theorem needs it at `ZMod q₁` and
`ZMod q₂`. -/
theorem nconvAlg_eq_nconvR {R : Type*} [CommRing R] (f g : ℕ → R) (n : ℕ) (hn : n < 256) :
    Kopis.Avx2.NttAlg.nconv f g n = nconvR f g n := by
  unfold Kopis.Avx2.NttAlg.nconv nconvR
  refine Finset.sum_congr rfl (fun i hi => ?_)
  have hi' : i < 256 := Finset.mem_range.mp hi
  by_cases hle : i ≤ n
  · rw [if_pos hle, Finset.sum_eq_single (n - i)]
    · rw [if_pos (by omega)]
    · intro j hj hne
      have hj' : j < 256 := Finset.mem_range.mp hj
      rw [if_neg (by omega), if_neg (by omega)]
    · intro h; exact absurd (Finset.mem_range.mpr (by omega : n - i < 256)) h
  · rw [if_neg hle, Finset.sum_eq_single (n + 256 - i)]
    · rw [if_neg (by omega), if_pos (by omega)]; ring
    · intro j hj hne
      have hj' : j < 256 := Finset.mem_range.mp hj
      rw [if_neg (by omega), if_neg (by omega)]
    · intro h; exact absurd (Finset.mem_range.mpr (by omega : n + 256 - i < 256)) h

/-- The exactness bound on the integer answer, from the two operand bounds and `fitsExactly`.
Lifted out of `ntt_entry_spec` because the AVX2 branch needs it too. -/
theorem convZ_bound (N : ℕ) (sBound : ℤ) (u v : ℕ → arithmetic.ring_arith.RingElem)
    (hfit : fitsExactly N sBound)
    (hub : ∀ jj c, jj < N → c < 256 → ((u jj).val[c]!).val < 2 ^ 13)
    (hvb : ∀ jj c, jj < N → c < 256 → |signedOfU16 ((v jj).val[c]!)| ≤ sBound) :
    ∀ n, n < 256 → |convZ u v N n| ≤ 25165056 := by
  intro n hn
  unfold convZ
  have hterm : ∀ jj ∈ Finset.range N,
      |NttMath.nconvR (uZ (u jj)) (sZ (v jj)) n| ≤ 256 * 8191 * sBound := by
    intro jj hjj
    have hjj' : jj < N := Finset.mem_range.mp hjj
    refine NttMath.abs_nconvR_le hn (fun c hc => ?_) (fun c hc => hvb jj c hjj' hc)
    have h13 : (2:ℕ) ^ 13 = 8192 := by norm_num
    have hb := hub jj c hjj' hc
    unfold uZ
    rw [abs_of_nonneg (Int.natCast_nonneg _)]
    omega
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  unfold fitsExactly uniformBound pNtt at hfit
  have h1 : 2 * ((N : ℤ) * 256 * 8191 * sBound) + 1 ≤ 50330113 := by omega
  linarith

set_option maxRecDepth 8000 in
/-- The last step of the entry theorem: the returned `u16`s agree with the integer convolution
mod `2¹⁶`, hence the ring elements agree.  AVX2 only: lifted out of `ntt_entry_spec` because the
two branches reconverge exactly here — the postcondition is about the coefficients of the answer,
not about how the accumulator stored them. -/
theorem entry_tail (N : ℕ) (u v : ℕ → arithmetic.ring_arith.RingElem)
    (r : arithmetic.ring_arith.RingElem)
    (hr : ∀ n, n < 256 → ((r.val[n]!).val : ℤ) % 65536 = convZ u v N n % 65536) :
    toRingElem r = ∑ jj ∈ Finset.range N, toRingElem (u jj) * toRingElem (v jj) := by
  apply Vector.ext
  intro n hn
  have h216 : ((2 ^ 16 : ℕ) : ℤ) = 65536 := by norm_num
  have hleft : (toRingElem r)[n]'hn = ((convZ u v N n : ℤ) : ZMod (2 ^ 16)) := by
    rw [toRingElem_get r n hn]
    have hcast := (ZMod.intCast_eq_intCast_iff' (((r.val[n]!).val : ℕ) : ℤ)
      (convZ u v N n) (2 ^ 16)).mpr (by rw [h216]; exact hr n hn)
    rw [← hcast]
    simp
  rw [hleft, poly_sum_get _ _ n hn]
  unfold convZ
  rw [Int.cast_sum]
  refine Finset.sum_congr rfl (fun jj hjj => ?_)
  rw [NttMath.nconvR_intCast,
    show ((toRingElem (u jj)) * (toRingElem (v jj)))[n]'hn
        = convCoeff (toRingElem (u jj)) (toRingElem (v jj)) n from mul_get _ _ n hn,
    convCoeff_eq_nconvR _ _ n hn]
  exact NttMath.nconvR_congr hn (fun c hc => by rw [uZ_cast, toRingElem_get! _ c hc])
    (fun c hc => by rw [sZ_cast, toRingElem_get! _ c hc])

set_option maxRecDepth 8000 in
/-- **The convolution theorem, for one entry.**""")
rep("""theorem ntt_entry_spec (N : ℕ) (sBound : ℤ)""",
    """theorem ntt_entry_spec (hb : backend.avx2.cpu.available = ok false) (N : ℕ) (sBound : ℤ)""")
# the exactness-bound block inside ntt_entry_spec now delegates to convZ_bound
rep("""  have hHb : ∀ n, n < 256 → |convZ u v N n| ≤ 25165056 := by
    intro n hn
    unfold convZ
    have hterm : ∀ jj ∈ Finset.range N,
        |NttMath.nconvR (uZ (u jj)) (sZ (v jj)) n| ≤ 256 * 8191 * sBound := by
      intro jj hjj
      have hjj' : jj < N := Finset.mem_range.mp hjj
      refine NttMath.abs_nconvR_le hn (fun c hc => ?_) (fun c hc => hvb jj c hjj' hc)
      have h13 : (2:ℕ) ^ 13 = 8192 := by norm_num
      have hb := hub jj c hjj' hc
      unfold uZ
      rw [abs_of_nonneg (Int.natCast_nonneg _)]
      omega
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    refine le_trans (Finset.sum_le_sum hterm) ?_
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    unfold fitsExactly uniformBound pNtt at hfit
    have h1 : 2 * ((N : ℤ) * 256 * 8191 * sBound) + 1 ≤ 50330113 := hfit
    linarith""",
    """  have hHb : ∀ n, n < 256 → |convZ u v N n| ≤ 25165056 :=
    convZ_bound N sBound u v hfit hub hvb""")
# and its tail is now `entry_tail`
rep("""  apply WP.spec_mono (reduce_invntt_to_ring_elem_spec acc (convP u v N) (convZ u v N)
    haccb hst hHz hHb)
  intro r hr
  apply Vector.ext
  intro n hn
  have h216 : ((2 ^ 16 : ℕ) : ℤ) = 65536 := by norm_num
  have hleft : (toRingElem r)[n]'hn = ((convZ u v N n : ℤ) : ZMod (2 ^ 16)) := by
    rw [toRingElem_get r n hn]
    have hcast := (ZMod.intCast_eq_intCast_iff' (((r.val[n]!).val : ℕ) : ℤ)
      (convZ u v N n) (2 ^ 16)).mpr (by rw [h216]; exact hr n hn)
    rw [← hcast]
    simp
  rw [hleft, poly_sum_get _ _ n hn]
  unfold convZ
  rw [Int.cast_sum]
  refine Finset.sum_congr rfl (fun jj hjj => ?_)
  rw [NttMath.nconvR_intCast,
    show ((toRingElem (u jj)) * (toRingElem (v jj)))[n]'hn
        = convCoeff (toRingElem (u jj)) (toRingElem (v jj)) n from mul_get _ _ n hn,
    convCoeff_eq_nconvR _ _ n hn]
  exact NttMath.nconvR_congr hn (fun c hc => by rw [uZ_cast, toRingElem_get! _ c hc])
    (fun c hc => by rw [sZ_cast, toRingElem_get! _ c hc])""",
    """  exact WP.spec_mono (reduce_invntt_to_ring_elem_spec hb acc (convP u v N) (convZ u v N)
    haccb hst hHz hHb) (fun r hr => entry_tail N u v r hr)""")

# --- (e) the two inner accumulate loops are portable-branch only ------------
rep("""theorem ntt_mul_inner_spec {X Y Z : Usize}
    (iter : core.ops.range.Range Usize)""",
    """theorem ntt_mul_inner_spec {X Y Z : Usize} (hb : backend.avx2.cpu.available = ok false)
    (iter : core.ops.range.Range Usize)""")
rep("""    let* ⟨acc1, hacc1v, hacc1b⟩ ← pointwise_mul_acc_spec acc ne ne1
      ((iter.start.val : ℤ) * (pNtt * pNtt))
      (by rw [hne']; exact fun c hc => hself iter.start.val c hj_lt hc)""",
    """    let* ⟨acc1, hacc1v, hacc1b⟩ ← pointwise_mul_acc_spec hb acc ne ne1
      ((iter.start.val : ℤ) * (pNtt * pNtt))
      (by rw [hne']; exact fun c hc => hself iter.start.val c hj_lt hc)""")
rep("""    apply WP.spec_mono (ntt_mul_inner_spec iter1 self other i k acc1 hi hk""",
    """    apply WP.spec_mono (ntt_mul_inner_spec hb iter1 self other i k acc1 hi hk""")
rep("""theorem ntt_mulT_inner_spec {X Y Z : Usize}
    (iter : core.ops.range.Range Usize)""",
    """theorem ntt_mulT_inner_spec {X Y Z : Usize} (hb : backend.avx2.cpu.available = ok false)
    (iter : core.ops.range.Range Usize)""")
rep("""    let* ⟨acc1, hacc1v, hacc1b⟩ ← pointwise_mul_acc_spec acc ne ne1
      ((iter.start.val : ℤ) * (pNtt * pNtt))
      (by rw [hne']; exact fun c hc => hself iter.start.val c hi_lt hc)""",
    """    let* ⟨acc1, hacc1v, hacc1b⟩ ← pointwise_mul_acc_spec hb acc ne ne1
      ((iter.start.val : ℤ) * (pNtt * pNtt))
      (by rw [hne']; exact fun c hc => hself iter.start.val c hi_lt hc)""")
rep("""    apply WP.spec_mono (ntt_mulT_inner_spec iter1 self other j k acc1 hj hk""",
    """    apply WP.spec_mono (ntt_mulT_inner_spec hb iter1 self other j k acc1 hj hk""")

# ---------------------------------------------------------------------------
# accumulate and reduce, bundled
# ---------------------------------------------------------------------------
COMBINED_PRE = r'''
/-! ### AVX2 only: accumulate and reduce, together

The two backends' accumulators hold different things — one `i64` per coefficient against 512
`i32` lanes carrying two 16-bit residues — so no statement *about the accumulator* can be shared,
and `ntt_mul_inner_spec` cannot be transferred.  Bundling the inner loop with the reduction that
consumes it confines the difference to a single lemma: the conclusion below names only ring
elements, so the three nested loops above it are untouched.  The postcondition carries the
reduction's triple as a continuation, which is what lets `mul_loop0_loop0` bind the two in
sequence without ever naming the accumulator's contents.

`available_ok` fixes one boolean for every dispatch, so both branches are proved: the portable one
by `ntt_mul_inner_spec` + `ntt_entry_spec`, the vector one by `Kopis.Avx2.mul_inner_avx` +
`reduce_invntt_to_ring_elem_avx`, which end at the same postcondition (`entry_tail`). -/

/-- The `ℤ/q` reading of the integer convolution, in the shape the AVX2 endpoint theorem asks
for. -/
private theorem convZ_mod (q : ℕ) [NeZero q] (N : ℕ)
    (u v : ℕ → arithmetic.ring_arith.RingElem) (c : ℕ) (hc : c < 256) :
    ((convZ u v N c : ℤ) : ZMod q)
      = ∑ jj ∈ Finset.range N, Kopis.Avx2.NttAlg.nconv
          (fun n => ((uZ (u jj) n : ℤ) : ZMod q)) (fun n => ((sZ (v jj) n : ℤ) : ZMod q)) c := by
  unfold convZ
  rw [Int.cast_sum]
  exact Finset.sum_congr rfl fun jj _ => by
    rw [NttMath.nconvR_intCast, nconvAlg_eq_nconvR _ _ c hc]

'''

COMBINED_MUL = r'''/-- **One entry of the product: the accumulate loop, and the reduction that consumes it.** -/
theorem ntt_inner_entry_spec {X Y Z : Usize} (sBound : ℤ)
    (self : arithmetic.ntt.NttMatrix X Y) (other : arithmetic.ntt.NttMatrix Y Z)
    (u v : ℕ → arithmetic.ring_arith.RingElem) (i k : Usize)
    (hi : i.val < X.val) (hk : k.val < Z.val) (hY : Y.val ≤ 4)
    (hu : ∀ jj, jj < Y.val → UOK (u jj) ((self.val[i.val]!).val[jj]!))
    (hv : ∀ jj, jj < Y.val → SOK (v jj) ((other.val[jj]!).val[k.val]!))
    (hfit : fitsExactly Y.val sBound)
    (hub : ∀ jj c, jj < Y.val → c < 256 → ((u jj).val[c]!).val < 2 ^ 13)
    (hvb : ∀ jj c, jj < Y.val → c < 256 → |signedOfU16 ((v jj).val[c]!)| ≤ sBound) :
    arithmetic.ntt.NttMatrix.mul_loop0_loop0_loop0
        { start := 0#usize, «end» := Y } self other i k (Array.repeat 256#usize (0#i64))
      ⦃ (p : (arithmetic.ntt.NttMatrix X Y) × (arithmetic.ntt.NttMatrix Y Z) ×
             (Array I64 256#usize)) =>
          p.1 = self ∧ p.2.1 = other ∧
          arithmetic.ntt.reduce_invntt_to_ring_elem p.2.2
            ⦃ (r : arithmetic.ring_arith.RingElem) =>
                toRingElem r = ∑ jj ∈ Finset.range Y.val,
                  toRingElem (u jj) * toRingElem (v jj) ⦄ ⦄ := by
  have hHb := convZ_bound Y.val sBound u v hfit hub hvb
  obtain ⟨b, hb⟩ := Kopis.Avx2.available_ok
  cases b with
  | false =>
    have hzero : ∀ c, c < 256 → accZ (Array.repeat 256#usize (0#i64)) c = 0 := by
      intro c hc
      unfold accZ
      rw [Array.repeat_val, getElem!_pos _ c (by rw [List.length_replicate]; exact hc),
        List.getElem_replicate]
      rfl
    apply WP.spec_mono (ntt_mul_inner_spec hb { start := 0#usize, «end» := Y } self other i k
      (Array.repeat 256#usize (0#i64)) hi hk (by simp) rfl hY
      (fun j c hj hc => ElemOK_bound ((hu j hj).1 hb) c hc)
      (fun j c hj hc => ElemOK_bound ((hv j hj).1 hb) c hc)
      (fun c hc => by rw [hzero c hc]; simp))
    rintro ⟨p1, p2, p3⟩ ⟨hp1, hp2, hp3⟩
    simp only at hp1 hp2 hp3
    refine ⟨hp1, hp2, ?_⟩
    exact ntt_entry_spec hb Y.val sBound u v _ _ (fun jj hjj => (hu jj hjj).1 hb)
      (fun jj hjj => (hv jj hjj).1 hb) hfit hub hvb hY p3
      (fun c hc => by
        rw [hp3 c hc, hzero c hc, zero_add]
        simp only [show ((0#usize : Usize).val) = 0 from rfl, ← Finset.range_eq_Ico])
  | true =>
    have hsmall : ∀ jj, jj < Y.val → ∀ c, c < 256 → 2 * |sZ (v jj) c| < 7681 := by
      intro jj hjj c hc
      have h1 := hvb jj c hjj hc
      have h0 : (0:ℤ) ≤ sBound := le_trans (abs_nonneg _) h1
      have hY1 : (1:ℤ) ≤ (Y.val : ℤ) := by exact_mod_cast (by omega : 1 ≤ Y.val)
      have hf := hfit
      unfold fitsExactly uniformBound pNtt at hf
      have hstep : (4193792 : ℤ) * sBound ≤ 2 * ((Y.val : ℤ) * 256 * 8191 * sBound) := by
        nlinarith
      unfold sZ
      omega
    have hnu : ∀ jj, jj < Y.val →
        Kopis.Avx2.NttOK (uZ (u jj)) ((self.val[i.val]!).val[jj]!) :=
      fun jj hjj => (hu jj hjj).2 hb (fun c hc => hub jj c hjj hc)
    have hnv : ∀ jj, jj < Y.val →
        Kopis.Avx2.NttOK (sZ (v jj)) ((other.val[jj]!).val[k.val]!) :=
      fun jj hjj => (hv jj hjj).2 hb (fun c hc => hsmall jj hjj c hc)
    apply WP.spec_mono (Kopis.Avx2.mul_inner_avx hb { start := 0#usize, «end» := Y } self other
      i k (Array.repeat 256#usize (0#i64)) 5376 (by norm_num) (by norm_num) hi hk (by simp) rfl hY
      (fun j t hj ht => Kopis.Avx2.NttOK_lane_bound (hnu j hj) t ht)
      (fun j t hj ht => Kopis.Avx2.NttOK_lane_bound (hnv j hj) t ht)
      (fun t ht => by rw [Kopis.Avx2.i32View_zero t ht]; simp))
    rintro ⟨p1, p2, p3⟩ ⟨hp1, hp2, hp3, hp4⟩
    simp only at hp1 hp2 hp3 hp4
    refine ⟨hp1, hp2, ?_⟩
    refine WP.spec_mono (Kopis.Avx2.reduce_invntt_to_ring_elem_avx hb Y.val hY p3
      (fun jj => (self.val[i.val]!).val[jj]!) (fun jj => (other.val[jj]!).val[k.val]!)
      (fun jj => uZ (u jj)) (fun jj => sZ (v jj)) hnu hnv
      (fun t ht => by
        rw [hp3 t ht, Kopis.Avx2.i32View_zero t ht, zero_add]
        simp only [show ((0#usize : Usize).val) = 0 from rfl, ← Finset.range_eq_Ico])
      (convZ u v Y.val) hHb (fun c hc => convZ_mod 7681 Y.val u v c hc)
      (fun c hc => convZ_mod 10753 Y.val u v c hc))
      (fun r hr => entry_tail Y.val u v r hr)

'''

COMBINED_MULT = r'''/-- **One entry of `mul_transpose`'s product**, the same statement with the outer index of `self`
playing the role of the inner one. -/
theorem ntt_mulT_inner_entry_spec {X Y Z : Usize} (sBound : ℤ)
    (self : arithmetic.ntt.NttMatrix X Y) (other : arithmetic.ntt.NttMatrix X Z)
    (u v : ℕ → arithmetic.ring_arith.RingElem) (j k : Usize)
    (hj : j.val < Y.val) (hk : k.val < Z.val) (hX : X.val ≤ 4)
    (hu : ∀ ii, ii < X.val → UOK (u ii) ((self.val[ii]!).val[j.val]!))
    (hv : ∀ ii, ii < X.val → SOK (v ii) ((other.val[ii]!).val[k.val]!))
    (hfit : fitsExactly X.val sBound)
    (hub : ∀ ii c, ii < X.val → c < 256 → ((u ii).val[c]!).val < 2 ^ 13)
    (hvb : ∀ ii c, ii < X.val → c < 256 → |signedOfU16 ((v ii).val[c]!)| ≤ sBound) :
    arithmetic.ntt.NttMatrix.mul_transpose_loop0_loop0_loop0
        { start := 0#usize, «end» := X } self other j k (Array.repeat 256#usize (0#i64))
      ⦃ (p : (arithmetic.ntt.NttMatrix X Y) × (arithmetic.ntt.NttMatrix X Z) ×
             (Array I64 256#usize)) =>
          p.1 = self ∧ p.2.1 = other ∧
          arithmetic.ntt.reduce_invntt_to_ring_elem p.2.2
            ⦃ (r : arithmetic.ring_arith.RingElem) =>
                toRingElem r = ∑ ii ∈ Finset.range X.val,
                  toRingElem (u ii) * toRingElem (v ii) ⦄ ⦄ := by
  have hHb := convZ_bound X.val sBound u v hfit hub hvb
  obtain ⟨b, hb⟩ := Kopis.Avx2.available_ok
  cases b with
  | false =>
    have hzero : ∀ c, c < 256 → accZ (Array.repeat 256#usize (0#i64)) c = 0 := by
      intro c hc
      unfold accZ
      rw [Array.repeat_val, getElem!_pos _ c (by rw [List.length_replicate]; exact hc),
        List.getElem_replicate]
      rfl
    apply WP.spec_mono (ntt_mulT_inner_spec hb { start := 0#usize, «end» := X } self other j k
      (Array.repeat 256#usize (0#i64)) hj hk (by simp) rfl hX
      (fun ii c hii hc => ElemOK_bound ((hu ii hii).1 hb) c hc)
      (fun ii c hii hc => ElemOK_bound ((hv ii hii).1 hb) c hc)
      (fun c hc => by rw [hzero c hc]; simp))
    rintro ⟨p1, p2, p3⟩ ⟨hp1, hp2, hp3⟩
    simp only at hp1 hp2 hp3
    refine ⟨hp1, hp2, ?_⟩
    exact ntt_entry_spec hb X.val sBound u v _ _ (fun ii hii => (hu ii hii).1 hb)
      (fun ii hii => (hv ii hii).1 hb) hfit hub hvb hX p3
      (fun c hc => by
        rw [hp3 c hc, hzero c hc, zero_add]
        simp only [show ((0#usize : Usize).val) = 0 from rfl, ← Finset.range_eq_Ico])
  | true =>
    have hsmall : ∀ ii, ii < X.val → ∀ c, c < 256 → 2 * |sZ (v ii) c| < 7681 := by
      intro ii hii c hc
      have h1 := hvb ii c hii hc
      have h0 : (0:ℤ) ≤ sBound := le_trans (abs_nonneg _) h1
      have hX1 : (1:ℤ) ≤ (X.val : ℤ) := by exact_mod_cast (by omega : 1 ≤ X.val)
      have hf := hfit
      unfold fitsExactly uniformBound pNtt at hf
      have hstep : (4193792 : ℤ) * sBound ≤ 2 * ((X.val : ℤ) * 256 * 8191 * sBound) := by
        nlinarith
      unfold sZ
      omega
    have hnu : ∀ ii, ii < X.val →
        Kopis.Avx2.NttOK (uZ (u ii)) ((self.val[ii]!).val[j.val]!) :=
      fun ii hii => (hu ii hii).2 hb (fun c hc => hub ii c hii hc)
    have hnv : ∀ ii, ii < X.val →
        Kopis.Avx2.NttOK (sZ (v ii)) ((other.val[ii]!).val[k.val]!) :=
      fun ii hii => (hv ii hii).2 hb (fun c hc => hsmall ii hii c hc)
    apply WP.spec_mono (Kopis.Avx2.mulT_inner_avx hb { start := 0#usize, «end» := X } self other
      j k (Array.repeat 256#usize (0#i64)) 5376 (by norm_num) (by norm_num) hj hk (by simp) rfl hX
      (fun ii t hii ht => Kopis.Avx2.NttOK_lane_bound (hnu ii hii) t ht)
      (fun ii t hii ht => Kopis.Avx2.NttOK_lane_bound (hnv ii hii) t ht)
      (fun t ht => by rw [Kopis.Avx2.i32View_zero t ht]; simp))
    rintro ⟨p1, p2, p3⟩ ⟨hp1, hp2, hp3, hp4⟩
    simp only at hp1 hp2 hp3 hp4
    refine ⟨hp1, hp2, ?_⟩
    refine WP.spec_mono (Kopis.Avx2.reduce_invntt_to_ring_elem_avx hb X.val hX p3
      (fun ii => (self.val[ii]!).val[j.val]!) (fun ii => (other.val[ii]!).val[k.val]!)
      (fun ii => uZ (u ii)) (fun ii => sZ (v ii)) hnu hnv
      (fun t ht => by
        rw [hp3 t ht, Kopis.Avx2.i32View_zero t ht, zero_add]
        simp only [show ((0#usize : Usize).val) = 0 from rfl, ← Finset.range_eq_Ico])
      (convZ u v X.val) hHb (fun c hc => convZ_mod 7681 X.val u v c hc)
      (fun c hc => convZ_mod 10753 X.val u v c hc))
      (fun r hr => entry_tail X.val u v r hr)

'''

# the shared preamble goes before the three nested loops of `mul`; each combined lemma goes
# immediately after the inner loop it replaces
rep("""/-! ### The three nested loops of `mul` -/""",
    COMBINED_PRE + """/-! ### The three nested loops of `mul` -/""")
rep("""/-- The middle loop of `mul`: one output ring element per column `k`. -/""",
    COMBINED_MUL + """/-- The middle loop of `mul`: one output ring element per column `k`. -/""")
rep("""/-- The middle loop of `mul_transpose`. -/""",
    COMBINED_MULT + """/-- The middle loop of `mul_transpose`. -/""")

# --- rewire `mul`'s middle loop -------------------------------------------
rep("""    have hk_lt : iter.start.val < Z.val := by omega
    have hzero : ∀ c, c < 256 → accZ (Array.repeat 256#usize (0#i64)) c = 0 := by
      intro c hc
      unfold accZ
      rw [Array.repeat_val, getElem!_pos _ c (by rw [List.length_replicate]; exact hc),
        List.getElem_replicate]
      rfl
    have hselfb : ∀ j c, j < Y.val → c < 256 →
        |aZ (((nttFwdU A).val[i.val]!).val[j]!) c| ≤ pNtt :=
      fun j c hj hc => ElemOK_bound (nttFwdU_entry A i.val j hi hj) c hc
    have hotherb : ∀ j c, j < Y.val → c < 256 →
        |aZ (((nttFwdS s).val[j]!).val[iter.start.val]!) c| ≤ pNtt :=
      fun j c hj hc => ElemOK_bound (nttFwdS_entry s j iter.start.val hj hk_lt) c hc
    let* ⟨self1, other1, acc1, hs1, ho1, hacc1⟩ ←
      ntt_mul_inner_spec { start := 0#usize, «end» := Y } (nttFwdU A) (nttFwdS s) i iter.start
        (Array.repeat 256#usize (0#i64)) hi hk_lt (by simp) rfl hY hselfb hotherb
        (fun c hc => by rw [hzero c hc]; simp)
    subst hs1; subst ho1
    have hacc1' : ∀ c, c < 256 → accZ acc1 c
        = ∑ jj ∈ Finset.range Y.val,
            aZ (((nttFwdU A).val[i.val]!).val[jj]!) c
              * aZ (((nttFwdS s).val[jj]!).val[iter.start.val]!) c := by
      intro c hc
      rw [hacc1 c hc, hzero c hc, zero_add, ← Finset.range_eq_Ico]
    let* ⟨re, hre⟩ ← ntt_entry_spec Y.val sBound
      (fun jj => (A.val[i.val]!).val[jj]!) (fun jj => (s.val[jj]!).val[iter.start.val]!)
      (fun jj => ((nttFwdU A).val[i.val]!).val[jj]!)
      (fun jj => ((nttFwdS s).val[jj]!).val[iter.start.val]!)
      (fun jj hjj => nttFwdU_entry A i.val jj hi hjj)
      (fun jj hjj => nttFwdS_entry s jj iter.start.val hjj hk_lt)
      hfit (fun jj c hjj hc => hA i.val jj c hi hjj hc)
      (fun jj c hjj hc => hs jj iter.start.val c hjj hk_lt hc) hY acc1 hacc1'""",
    """    have hk_lt : iter.start.val < Z.val := by omega
    let* ⟨self1, other1, acc1, hs1, ho1, hred⟩ ←
      ntt_inner_entry_spec sBound (nttFwdU A) (nttFwdS s)
        (fun jj => (A.val[i.val]!).val[jj]!) (fun jj => (s.val[jj]!).val[iter.start.val]!)
        i iter.start hi hk_lt hY
        (fun jj hjj => nttFwdU_entry A i.val jj hi hjj)
        (fun jj hjj => nttFwdS_entry s (secretSmall_of_fit hfit hs) jj iter.start.val hjj hk_lt)
        hfit (fun jj c hjj hc => hA i.val jj c hi hjj hc)
        (fun jj c hjj hc => hs jj iter.start.val c hjj hk_lt hc)
    subst hs1; subst ho1
    let* ⟨re, hre⟩ ← hred""")

# --- rewire `mul_transpose`'s middle loop ---------------------------------
rep("""    have hk_lt : iter.start.val < Z.val := by omega
    have hzero : ∀ c, c < 256 → accZ (Array.repeat 256#usize (0#i64)) c = 0 := by
      intro c hc
      unfold accZ
      rw [Array.repeat_val, getElem!_pos _ c (by rw [List.length_replicate]; exact hc),
        List.getElem_replicate]
      rfl
    have hselfb : ∀ ii c, ii < X.val → c < 256 →
        |aZ (((nttFwdU A).val[ii]!).val[j.val]!) c| ≤ pNtt :=
      fun ii c hii hc => ElemOK_bound (nttFwdU_entry A ii j.val hii hj) c hc
    have hotherb : ∀ ii c, ii < X.val → c < 256 →
        |aZ (((nttFwdS s).val[ii]!).val[iter.start.val]!) c| ≤ pNtt :=
      fun ii c hii hc => ElemOK_bound (nttFwdS_entry s ii iter.start.val hii hk_lt) c hc
    let* ⟨self1, other1, acc1, hs1, ho1, hacc1⟩ ←
      ntt_mulT_inner_spec { start := 0#usize, «end» := X } (nttFwdU A) (nttFwdS s) j iter.start
        (Array.repeat 256#usize (0#i64)) hj hk_lt (by simp) rfl hX hselfb hotherb
        (fun c hc => by rw [hzero c hc]; simp)
    subst hs1; subst ho1
    have hacc1' : ∀ c, c < 256 → accZ acc1 c
        = ∑ ii ∈ Finset.range X.val,
            aZ (((nttFwdU A).val[ii]!).val[j.val]!) c
              * aZ (((nttFwdS s).val[ii]!).val[iter.start.val]!) c := by
      intro c hc
      rw [hacc1 c hc, hzero c hc, zero_add, ← Finset.range_eq_Ico]
    let* ⟨re, hre⟩ ← ntt_entry_spec X.val sBound
      (fun ii => (A.val[ii]!).val[j.val]!) (fun ii => (s.val[ii]!).val[iter.start.val]!)
      (fun ii => ((nttFwdU A).val[ii]!).val[j.val]!)
      (fun ii => ((nttFwdS s).val[ii]!).val[iter.start.val]!)
      (fun ii hii => nttFwdU_entry A ii j.val hii hj)
      (fun ii hii => nttFwdS_entry s ii iter.start.val hii hk_lt)
      hfit (fun ii c hii hc => hA ii j.val c hii hj hc)
      (fun ii c hii hc => hs ii iter.start.val c hii hk_lt hc) hX acc1 hacc1'""",
    """    have hk_lt : iter.start.val < Z.val := by omega
    let* ⟨self1, other1, acc1, hs1, ho1, hred⟩ ←
      ntt_mulT_inner_entry_spec sBound (nttFwdU A) (nttFwdS s)
        (fun ii => (A.val[ii]!).val[j.val]!) (fun ii => (s.val[ii]!).val[iter.start.val]!)
        j iter.start hj hk_lt hX
        (fun ii hii => nttFwdU_entry A ii j.val hii hj)
        (fun ii hii => nttFwdS_entry s (secretSmall_of_fit hfit hs) ii iter.start.val hii hk_lt)
        hfit (fun ii c hii hc => hA ii j.val c hii hj hc)
        (fun ii c hii hc => hs ii iter.start.val c hii hk_lt hc)
    subst hs1; subst ho1
    let* ⟨re, hre⟩ ← hred""")

def patch(t: str) -> str:
    for old, new, cnt in _EDITS:
        got = t.count(old)
        if got != cnt:
            raise SystemExit(
                f"gen_avx2_twins: NttBridge patch anchor matched {got} times (want {cnt}); "
                f"the serial proof changed.  Anchor starts: {old[:90]!r}")
        t = t.replace(old, new)
    return t
