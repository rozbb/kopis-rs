/-
  # Kopis/Properties/NttBridge.lean — the forward NTT denotation and the multiplication bridge.

  This is the module that connects the *extracted transform network* (`NttForward` /
  `NttInverse`, which prove what `ntt` and `invntt` compute) to the *matrix-level* interface the
  key-generation, encryption and decryption proofs consume.

  It sits above `NttForward` because it needs `ntt_full_spec`, and `NttForward` in turn needs the
  reduction value specs in `Ntt.lean` — so the bridge cannot live in `Ntt.lean` itself.
  `Ntt.lean` keeps the scalar groundwork (`fitsExactly`, `signedOfU16`, the reduction specs and
  the raw-magnitude lemmas); this file keeps everything that mentions the transform.
-/
import Kopis.Properties.Ntt
import Kopis.Properties.NttForward

open Aeneas Aeneas.Std Result RustKopis
open scoped BigOperators

namespace Kopis.Properties

open NttMath

set_option maxHeartbeats 1000000

/-! ### The coefficient-widening loops

`NttElem::from_uniform` and `from_secret` each widen a `RingElem`'s 256 `u16` coefficients into
an `[i32; 256]` and then run the forward transform.  They differ only in the widening: uniform
zero-extends (`u16 → i32`), secret reinterprets the bits as signed first (`u16 → i16 → i32`).
Both widenings land far inside `i32`, so `ntt_full_spec` applies with `B = 65536`. -/

/-- `Int.bmod _ 2^16` on a `u16`-ranged integer is exactly the signed reading — this is why the
`u16 → i16` reinterpretation and `signedOfU16` agree. -/
theorem bmod_pow16_eq_signed {z : ℤ} (h0 : 0 ≤ z) (h1 : z < 65536) :
    Int.bmod z (2 ^ 16) = if z < 32768 then z else z - 65536 := by
  rw [Int.bmod_def]
  norm_num
  split <;> omega

/-- `Int.bmod` is the identity on `[-2^15, 2^15)` — the `i16` case. -/
theorem bmod_i16_exact {z : ℤ} (hlo : -32768 ≤ z) (hhi : z < 32768) :
    Int.bmod z (2 ^ 16) = z := by
  rw [Int.bmod_def]
  norm_num
  omega

/-- Loop invariant of the uniform widening loop: indices at or past `iter.start` have been
overwritten with the zero-extended `u16` coefficient; earlier ones are untouched. -/
theorem from_uniform_loop_spec (iter : core.ops.range.Range Usize)
    (elem : arithmetic.ring_arith.RingElem) (a : Array I32 256#usize)
    (hend : iter.«end».val = 256) :
    arithmetic.ntt.NttElem.from_uniform_loop iter elem a
      ⦃ (r : Array I32 256#usize) =>
          ∀ c, c < 256 →
            aZ r c = if iter.start.val ≤ c then ((elem.val[c]!).val : ℤ) else aZ a c ⦄ := by
  unfold arithmetic.ntt.NttElem.from_uniform_loop
  by_cases hlt : iter.start.val < iter.«end».val
  · let* ⟨o, iter1, ho, hstart', hend'⟩ ← core.iter.range.IteratorRange.next_Usize_some_spec
    rw [ho]; simp only
    have hi_lt : iter.start.val < 256 := by omega
    have hei : iter.start.val < elem.val.length := by have := elem.property; scalar_tac
    have hal : iter.start.val < a.length := by have := a.property; scalar_tac
    have hend1 : iter1.«end».val = 256 := by rw [hend']; exact hend
    step*
    rename_i c
    have hc : c < 256 := by assumption
    have hi2v : (i2.val : ℤ) = ((i1.val : ℕ) : ℤ) := by
      rw [i2_post, UScalar.hcast_val_eq, show IScalarTy.I32.numBits = 32 from rfl]
      exact bmod_i32_exact (by have := i1.hBounds; scalar_tac)
        (by have := i1.hBounds; scalar_tac)
    rw [r_post1 c hc, hstart', a1_post, aZ_set a iter.start i2 hi_lt c, hi2v, i1_post]
    by_cases hcase : iter.start.val + 1 ≤ c
    · rw [if_pos hcase, if_pos (by omega : iter.start.val ≤ c)]
    · rw [if_neg hcase]
      by_cases hci : c = iter.start.val
      · rw [if_pos hci, if_pos (by omega : iter.start.val ≤ c), hci,
          ← getElem!_pos _ iter.start.val hei]
      · rw [if_neg hci, if_neg (by omega : ¬ iter.start.val ≤ c)]
  · let* ⟨o, iter1, hnone, _⟩ ← core.iter.range.IteratorRange.next_Usize_none_spec
    rw [hnone]; simp only [WP.spec_ok]
    intro c hc
    rw [if_neg (by omega : ¬ iter.start.val ≤ c)]
  termination_by iter.«end».val - iter.start.val
  decreasing_by scalar_decr_tac

/-- Loop invariant of the secret widening loop: same, but the `u16` is reinterpreted as signed
(`u16 → i16`, a pure bit reinterpretation) before the exact `i16 → i32` widening. -/
theorem from_secret_loop_spec (iter : core.ops.range.Range Usize)
    (elem : arithmetic.ring_arith.RingElem) (a : Array I32 256#usize)
    (hend : iter.«end».val = 256) :
    arithmetic.ntt.NttElem.from_secret_loop iter elem a
      ⦃ (r : Array I32 256#usize) =>
          ∀ c, c < 256 →
            aZ r c = if iter.start.val ≤ c then signedOfU16 (elem.val[c]!) else aZ a c ⦄ := by
  unfold arithmetic.ntt.NttElem.from_secret_loop
  by_cases hlt : iter.start.val < iter.«end».val
  · let* ⟨o, iter1, ho, hstart', hend'⟩ ← core.iter.range.IteratorRange.next_Usize_some_spec
    rw [ho]; simp only
    have hi_lt : iter.start.val < 256 := by omega
    have hei : iter.start.val < elem.val.length := by have := elem.property; scalar_tac
    have hal : iter.start.val < a.length := by have := a.property; scalar_tac
    have hend1 : iter1.«end».val = 256 := by rw [hend']; exact hend
    step*
    rename_i c
    have hc : c < 256 := by assumption
    have hb0 : (0:ℤ) ≤ ((i1.val : ℕ) : ℤ) := by positivity
    have hb1 : ((i1.val : ℕ) : ℤ) < 65536 := by have := i1.hBounds; scalar_tac
    -- `u16 → i16` is `Int.bmod _ 2^16`, i.e. exactly `signedOfU16`; the `i16 → i32` widening
    -- that follows is exact because the value already fits in 16 bits.
    have hi2v : (i2.val : ℤ) = signedOfU16 i1 := by
      rw [i2_post, UScalar.hcast_val_eq, show IScalarTy.I16.numBits = 16 from rfl,
        bmod_pow16_eq_signed hb0 hb1]
      rfl
    have hi3v : (i3.val : ℤ) = signedOfU16 i1 := by
      rw [i3_post, IScalar.cast_val_eq,
        show Min.min IScalarTy.I32.numBits IScalarTy.I16.numBits = 16 from rfl, hi2v]
      refine bmod_i16_exact ?_ ?_ <;>
        · unfold signedOfU16; split <;> omega
    rw [r_post1 c hc, hstart', a1_post, aZ_set a iter.start i3 hi_lt c, hi3v, i1_post]
    by_cases hcase : iter.start.val + 1 ≤ c
    · rw [if_pos hcase, if_pos (by omega : iter.start.val ≤ c)]
    · rw [if_neg hcase]
      by_cases hci : c = iter.start.val
      · rw [if_pos hci, if_pos (by omega : iter.start.val ≤ c), hci,
          ← getElem!_pos _ iter.start.val hei]
      · rw [if_neg hci, if_neg (by omega : ¬ iter.start.val ≤ c)]
  · let* ⟨o, iter1, hnone, _⟩ ← core.iter.range.IteratorRange.next_Usize_none_spec
    rw [hnone]; simp only [WP.spec_ok]
    intro c hc
    rw [if_neg (by omega : ¬ iter.start.val ≤ c)]
  termination_by iter.«end».val - iter.start.val
  decreasing_by scalar_decr_tac

/-! ### The element-level forward transform

`NttElem::from_uniform` / `from_secret` = widen, then run `ntt`.  `ntt_full_spec` needs only a
coefficient bound `B ≤ 65536`, which both widenings satisfy comfortably (a zero-extended `u16` is
`< 65536`; a `signedOfU16` reading is `≤ 32768` in absolute value), so each composes directly. -/

/-- **`NttElem::from_uniform` computes the CRT transform of the unsigned coefficients.** -/
theorem from_uniform_elem_spec (elem : arithmetic.ring_arith.RingElem) :
    arithmetic.ntt.NttElem.from_uniform elem
      ⦃ (r : Array I32 256#usize) =>
          State 256 1 1 (fun c => ((((elem.val[c]!).val : ℕ) : ℤ) : Zp)) (aP r)
          ∧ (∀ c, c < 256 → -pNtt < aZ r c ∧ aZ r c < pNtt) ⦄ := by
  unfold arithmetic.ntt.NttElem.from_uniform
  have hRD : (consts.RING_DEG : Usize).val = 256 := by simp only [consts.RING_DEG]; rfl
  let* ⟨a1, ha1⟩ ← from_uniform_loop_spec { start := 0#usize, «end» := consts.RING_DEG } elem
    (Array.repeat 256#usize 0#i32) hRD
  have hz : ∀ c, c < 256 → aZ a1 c = (((elem.val[c]!).val : ℕ) : ℤ) := by
    intro c hc
    rw [ha1 c hc, if_pos (Nat.zero_le c)]
  let* ⟨a2, hst, hbd⟩ ← ntt_full_spec a1 _ 65536
    (fun c hc => by unfold aP; rw [hz c hc])
    (by norm_num) (by norm_num)
    (fun c hc => by
      rw [hz c hc, abs_of_nonneg (by positivity)]
      have := (elem.val[c]!).hBounds; scalar_tac)
  exact ⟨hst, hbd⟩

/-- **`NttElem::from_secret` computes the CRT transform of the signed coefficients.** -/
theorem from_secret_elem_spec (elem : arithmetic.ring_arith.RingElem) :
    arithmetic.ntt.NttElem.from_secret elem
      ⦃ (r : Array I32 256#usize) =>
          State 256 1 1 (fun c => ((signedOfU16 (elem.val[c]!) : ℤ) : Zp)) (aP r)
          ∧ (∀ c, c < 256 → -pNtt < aZ r c ∧ aZ r c < pNtt) ⦄ := by
  unfold arithmetic.ntt.NttElem.from_secret
  have hRD : (consts.RING_DEG : Usize).val = 256 := by simp only [consts.RING_DEG]; rfl
  let* ⟨a1, ha1⟩ ← from_secret_loop_spec { start := 0#usize, «end» := consts.RING_DEG } elem
    (Array.repeat 256#usize 0#i32) hRD
  have hz : ∀ c, c < 256 → aZ a1 c = signedOfU16 (elem.val[c]!) := by
    intro c hc
    rw [ha1 c hc, if_pos (Nat.zero_le c)]
  let* ⟨a2, hst, hbd⟩ ← ntt_full_spec a1 _ 65536
    (fun c hc => by unfold aP; rw [hz c hc])
    (by norm_num) (by norm_num)
    (fun c hc => by
      rw [hz c hc, abs_le]
      have hb := (elem.val[c]!).hBounds
      unfold signedOfU16
      constructor <;> split <;> scalar_tac)
  exact ⟨hst, hbd⟩

/-! ### The NTT representation functions and the decomposed bridge

`from_uniform_matrix` / `from_secret_matrix` map a coefficient matrix into the NTT domain;
`mul` / `mul_transpose` multiply pointwise there.  Because the escaping NTT matrices
(`mat_a_ntt` into the public key, `vec_s_ntt`/`sprime_ntt` into the secret material) are
consumed at a *different* program point than where they are built, the bridge is stated as
four decomposed specs — two constructors and two multipliers — rather than as one bundled
triple.

The denotation runs **forward**: `nttFwdU A` / `nttFwdS s` are the NTT-domain matrices that
`from_uniform_matrix` / `from_secret_matrix` produce from a coefficient matrix.  They are
ordinary `def`s, not `opaque` constants, so the specs below have definitional content to work
with.

The earlier design pointed the bridge the other way, with *opaque* inverses `nttInvU`/`nttInvS`
mapping stored NTT data back to coefficients.  That direction cannot work: an `opaque` constant
supports only reflexivity and congruence, so `nttInvU (from_uniform_matrix A) = A` is not merely
unproven but underivable — there are models in which `nttInvU` is constant.  Going forward also
avoids needing the NTT **roundtrip** theorem (`invNTT ∘ NTT = id`) and NTT injectivity at all:
the only mathematics left is the convolution theorem, which is what `ntt_mul_spec` states.

No existential is needed downstream either.  A consumer that holds a stored NTT matrix names its
coefficient matrix explicitly and carries an equation `stored = nttFwdU A`; every call site
already knows that `A` (it comes from the spec side), so the witness is supplied rather than
quantified over. -/

/-- Total value extractor for a `Result`: the `ok` value, or `default` on failure/divergence.
Used only to give the forward NTT denotations below a total definition; every use is paired
with a success proof, so the `default` branch is never the value being reasoned about. -/
def Result.getD {α : Type} [Inhabited α] (r : Result α) : α :=
  match r with
  | .ok v => v
  | _ => default

@[simp] theorem Result.getD_ok {α : Type} [Inhabited α] (v : α) :
    Result.getD (.ok v) = v := rfl

/-- The NTT-domain matrix denoting the uniform coefficient matrix `A` — i.e. what
`from_uniform_matrix` computes from it. -/
def nttFwdU {X Y : Usize} (A : Mat X Y) : arithmetic.ntt.NttMatrix X Y :=
  Result.getD (arithmetic.ntt.NttMatrix.from_uniform_matrix A)

/-- The NTT-domain matrix denoting the secret coefficient matrix `s` — i.e. what
`from_secret_matrix` computes from it. -/
def nttFwdS {X Y : Usize} (s : Mat X Y) : arithmetic.ntt.NttMatrix X Y :=
  Result.getD (arithmetic.ntt.NttMatrix.from_secret_matrix s)

/-! ### The matrix loops

`from_uniform_matrix` / `from_secret_matrix` are entrywise maps of the element transform over an
`X × Y` matrix.  In forward form the two `from_*_matrix` specs assert exactly that the
computation *succeeds* (their value is `nttFwdU`/`nttFwdS` by definition), so success is all the
loops have to give — and it follows from the element specs above, which are total. -/

/-- The inner matrix loop succeeds: every entry's element transform does. -/
theorem from_uniform_matrix_inner_ok {X Y : Usize}
    (iter : core.ops.range.Range Usize) (mat : Mat X Y)
    (ret : arithmetic.ntt.NttMatrix X Y) (i : Usize) (hi : i.val < X.val)
    (hend : iter.«end».val = Y.val) :
    arithmetic.ntt.NttMatrix.from_uniform_matrix_loop0_loop0 iter mat ret i
      ⦃ fun _ => True ⦄ := by
  unfold arithmetic.ntt.NttMatrix.from_uniform_matrix_loop0_loop0
  by_cases hlt : iter.start.val < iter.«end».val
  · let* ⟨o, iter1, ho, hstart', hend'⟩ ← core.iter.range.IteratorRange.next_Usize_some_spec
    rw [ho]; simp only
    have hmi : i.val < mat.val.length := by have := mat.property; scalar_tac
    let* ⟨a, ha⟩ ← Array.index_usize_spec mat i hmi
    have haj : iter.start.val < a.val.length := by
      have := a.property; scalar_tac
    let* ⟨re, hre⟩ ← Array.index_usize_spec a iter.start haj
    let* ⟨ne, hne1, hne2⟩ ← from_uniform_elem_spec re
    have hri : i.val < ret.length := by have := ret.property; scalar_tac
    let* ⟨a1, index_mut_back, ha1, hback⟩ ← Array.index_mut_usize_spec ret i hri
    have ha1j : iter.start.val < a1.length := by
      have := a1.property; scalar_tac
    let* ⟨a2, ha2⟩ ← Array.update_spec a1 iter.start ne ha1j
    exact from_uniform_matrix_inner_ok iter1 mat (index_mut_back a2) i hi
      (by rw [hend']; exact hend)
  · let* ⟨o, iter1, hnone, _⟩ ← core.iter.range.IteratorRange.next_Usize_none_spec
    rw [hnone]; simp only [WP.spec_ok]
  termination_by iter.«end».val - iter.start.val
  decreasing_by scalar_decr_tac

/-- The outer matrix loop succeeds. -/
theorem from_uniform_matrix_outer_ok {X Y : Usize}
    (iter : core.ops.range.Range Usize) (mat : Mat X Y)
    (ret : arithmetic.ntt.NttMatrix X Y) (hend : iter.«end».val = X.val) :
    arithmetic.ntt.NttMatrix.from_uniform_matrix_loop0 iter mat ret ⦃ fun _ => True ⦄ := by
  unfold arithmetic.ntt.NttMatrix.from_uniform_matrix_loop0
  by_cases hlt : iter.start.val < iter.«end».val
  · let* ⟨o, iter1, ho, hstart', hend'⟩ ← core.iter.range.IteratorRange.next_Usize_some_spec
    rw [ho]; simp only
    let* ⟨mat1, ret1⟩ ← from_uniform_matrix_inner_ok { start := 0#usize, «end» := Y } mat ret
      iter.start (by omega) rfl
    exact from_uniform_matrix_outer_ok iter1 mat1 ret1 (by rw [hend']; exact hend)
  · let* ⟨o, iter1, hnone, _⟩ ← core.iter.range.IteratorRange.next_Usize_none_spec
    rw [hnone]; simp only [WP.spec_ok]
  termination_by iter.«end».val - iter.start.val
  decreasing_by scalar_decr_tac

/-- `from_uniform_matrix` succeeds on every input. -/
theorem from_uniform_matrix_ok {X Y : Usize} (A : Mat X Y) :
    arithmetic.ntt.NttMatrix.from_uniform_matrix A ⦃ fun _ => True ⦄ := by
  unfold arithmetic.ntt.NttMatrix.from_uniform_matrix
    arithmetic.ntt.NttMatrix.Insts.CoreDefaultDefault.default
    arithmetic.ntt.NttElem.Insts.CoreDefaultDefault.default
  simp only [bind_tc_ok]
  exact from_uniform_matrix_outer_ok { start := 0#usize, «end» := X } A _ rfl

/-- The inner matrix loop succeeds, secret variant. -/
theorem from_secret_matrix_inner_ok {X Y : Usize}
    (iter : core.ops.range.Range Usize) (mat : Mat X Y)
    (ret : arithmetic.ntt.NttMatrix X Y) (i : Usize) (hi : i.val < X.val)
    (hend : iter.«end».val = Y.val) :
    arithmetic.ntt.NttMatrix.from_secret_matrix_loop0_loop0 iter mat ret i
      ⦃ fun _ => True ⦄ := by
  unfold arithmetic.ntt.NttMatrix.from_secret_matrix_loop0_loop0
  by_cases hlt : iter.start.val < iter.«end».val
  · let* ⟨o, iter1, ho, hstart', hend'⟩ ← core.iter.range.IteratorRange.next_Usize_some_spec
    rw [ho]; simp only
    have hmi : i.val < mat.val.length := by have := mat.property; scalar_tac
    let* ⟨a, ha⟩ ← Array.index_usize_spec mat i hmi
    have haj : iter.start.val < a.val.length := by
      have := a.property; scalar_tac
    let* ⟨re, hre⟩ ← Array.index_usize_spec a iter.start haj
    let* ⟨ne, hne1, hne2⟩ ← from_secret_elem_spec re
    have hri : i.val < ret.length := by have := ret.property; scalar_tac
    let* ⟨a1, index_mut_back, ha1, hback⟩ ← Array.index_mut_usize_spec ret i hri
    have ha1j : iter.start.val < a1.length := by
      have := a1.property; scalar_tac
    let* ⟨a2, ha2⟩ ← Array.update_spec a1 iter.start ne ha1j
    exact from_secret_matrix_inner_ok iter1 mat (index_mut_back a2) i hi
      (by rw [hend']; exact hend)
  · let* ⟨o, iter1, hnone, _⟩ ← core.iter.range.IteratorRange.next_Usize_none_spec
    rw [hnone]; simp only [WP.spec_ok]
  termination_by iter.«end».val - iter.start.val
  decreasing_by scalar_decr_tac

/-- The outer matrix loop succeeds, secret variant. -/
theorem from_secret_matrix_outer_ok {X Y : Usize}
    (iter : core.ops.range.Range Usize) (mat : Mat X Y)
    (ret : arithmetic.ntt.NttMatrix X Y) (hend : iter.«end».val = X.val) :
    arithmetic.ntt.NttMatrix.from_secret_matrix_loop0 iter mat ret ⦃ fun _ => True ⦄ := by
  unfold arithmetic.ntt.NttMatrix.from_secret_matrix_loop0
  by_cases hlt : iter.start.val < iter.«end».val
  · let* ⟨o, iter1, ho, hstart', hend'⟩ ← core.iter.range.IteratorRange.next_Usize_some_spec
    rw [ho]; simp only
    let* ⟨mat1, ret1⟩ ← from_secret_matrix_inner_ok { start := 0#usize, «end» := Y } mat ret
      iter.start (by omega) rfl
    exact from_secret_matrix_outer_ok iter1 mat1 ret1 (by rw [hend']; exact hend)
  · let* ⟨o, iter1, hnone, _⟩ ← core.iter.range.IteratorRange.next_Usize_none_spec
    rw [hnone]; simp only [WP.spec_ok]
  termination_by iter.«end».val - iter.start.val
  decreasing_by scalar_decr_tac

/-- `from_secret_matrix` succeeds on every input. -/
theorem from_secret_matrix_ok {X Y : Usize} (A : Mat X Y) :
    arithmetic.ntt.NttMatrix.from_secret_matrix A ⦃ fun _ => True ⦄ := by
  unfold arithmetic.ntt.NttMatrix.from_secret_matrix
    arithmetic.ntt.NttMatrix.Insts.CoreDefaultDefault.default
    arithmetic.ntt.NttElem.Insts.CoreDefaultDefault.default
  simp only [bind_tc_ok]
  exact from_secret_matrix_outer_ok { start := 0#usize, «end» := X } A _ rfl

/-- A `⦃ fun _ => True ⦄` triple is exactly success, so the `Result.getD` value is the result. -/
theorem spec_eq_getD {α : Type} [Inhabited α] {m : Result α} (h : m ⦃ fun _ => True ⦄) :
    m ⦃ (r : α) => r = Result.getD m ⦄ := by
  cases hm : m with
  | ok v => simp only [Result.getD, WP.spec_ok]
  | fail e => rw [hm] at h; simp [WP.spec, WP.theta] at h
  | div => rw [hm] at h; simp [WP.spec, WP.theta] at h

/-- **Part of the NTT hole.** `from_uniform_matrix A` succeeds, with value `nttFwdU A`.
Given the definition of `nttFwdU`, the content here is exactly that the computation does not
fail or diverge; the *transform* content lives in `ntt_mul_spec` below, which is where it is
actually consumed. -/
theorem from_uniform_matrix_spec {X Y : Usize} (A : Mat X Y) :
    arithmetic.ntt.NttMatrix.from_uniform_matrix A
      ⦃ (r : arithmetic.ntt.NttMatrix X Y) => r = nttFwdU A ⦄ :=
  spec_eq_getD (from_uniform_matrix_ok A)

/-- **Part of the NTT hole.** `from_secret_matrix s` succeeds, with value `nttFwdS s`. -/
theorem from_secret_matrix_spec {X Y : Usize} (s : Mat X Y) :
    arithmetic.ntt.NttMatrix.from_secret_matrix s
      ⦃ (r : arithmetic.ntt.NttMatrix X Y) => r = nttFwdS s ⦄ :=
  spec_eq_getD (from_secret_matrix_ok s)

/-- **Part of the NTT hole (`ntt_spec`) — the convolution theorem.** Pointwise product in the
NTT domain computes the schoolbook product of the underlying coefficient matrices, in
`ℤ[X]/(X²⁵⁶+1)` with `u16` coefficients — the same postcondition as `matrix_mul_spec` — given
the joint magnitude constraint `fitsExactly`. -/
theorem ntt_mul_spec {X Y Z : Usize}
    (A : Mat X Y) (s : Mat Y Z) (sBound : ℤ)
    (_hfit : fitsExactly Y.val sBound)
    (_hA : UniformBounded A) (_hs : SecretBounded s sBound) :
    arithmetic.ntt.NttMatrix.mul (nttFwdU A) (nttFwdS s)
      ⦃ (r : Mat X Z) =>
          ∀ (i : Nat) (_hi : i < X.val) (k : Nat) (_hk : k < Z.val),
            toRingElem ((r.val[i]!).val[k]!)
              = ∑ jj ∈ Finset.range Y.val,
                  toRingElem ((A.val[i]!).val[jj]!)
                    * toRingElem ((s.val[jj]!).val[k]!) ⦄ := by
  sorry

/-- **Part of the NTT hole (`ntt_spec`).** `mul_transpose` in the NTT domain computes the
schoolbook product `Aᵀ·s` of the underlying coefficient matrices, matching
`matrix_mul_transpose_spec`. -/
theorem ntt_mul_transpose_spec {X Y Z : Usize}
    (A : Mat X Y) (s : Mat X Z) (sBound : ℤ)
    (_hfit : fitsExactly X.val sBound)
    (_hA : UniformBounded A) (_hs : SecretBounded s sBound) :
    arithmetic.ntt.NttMatrix.mul_transpose (nttFwdU A) (nttFwdS s)
      ⦃ (r : Mat Y Z) =>
          ∀ (j : Nat) (_hj : j < Y.val) (k : Nat) (_hk : k < Z.val),
            toRingElem ((r.val[j]!).val[k]!)
              = ∑ ii ∈ Finset.range X.val,
                  toRingElem ((A.val[ii]!).val[j]!)
                    * toRingElem ((s.val[ii]!).val[k]!) ⦄ := by
  sorry

end Kopis.Properties
