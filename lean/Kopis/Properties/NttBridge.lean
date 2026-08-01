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
import Kopis.Properties.NttMul

open Aeneas Aeneas.Std Result RustKopis
open scoped BigOperators

namespace Kopis.Properties

open NttMath

set_option maxHeartbeats 1000000
set_option maxRecDepth 8000

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


/-! ### One transformed element

`ElemOK f ne` bundles what `NttElem::from_uniform` / `from_secret` establish about a single
transformed entry: `ne` holds the evaluations of the coefficient function `f` at the 256 leaf
constants, each centred in `(-p, p)`.  Bundling keeps the matrix loop invariants readable, and
`uP`/`sP` name the two coefficient functions (unsigned resp. signed reading of the stored
`u16`s) that the two constructors transform. -/

/-- The integer coefficient function of a *uniform* ring element: its stored `u16`s. -/
def uZ (re : arithmetic.ring_arith.RingElem) (c : ℕ) : ℤ := ((re.val[c]!).val : ℕ)

/-- The integer coefficient function of a *secret* ring element: its stored `u16`s read as
`i16`s, which is what `from_secret`'s `as i16 as i32` computes. -/
def sZ (re : arithmetic.ring_arith.RingElem) (c : ℕ) : ℤ := signedOfU16 (re.val[c]!)

/-- The `ℤ/p` coefficient function of a uniform ring element. -/
def uP (re : arithmetic.ring_arith.RingElem) (c : ℕ) : Zp := ((((re.val[c]!).val : ℕ) : ℤ) : Zp)

/-- The `ℤ/p` coefficient function of a secret ring element. -/
def sP (re : arithmetic.ring_arith.RingElem) (c : ℕ) : Zp :=
  ((signedOfU16 (re.val[c]!) : ℤ) : Zp)

theorem uP_eq (re : arithmetic.ring_arith.RingElem) (c : ℕ) : uP re c = ((uZ re c : ℤ) : Zp) := rfl

theorem sP_eq (re : arithmetic.ring_arith.RingElem) (c : ℕ) : sP re c = ((sZ re c : ℤ) : Zp) := rfl

/-- What one call of `from_uniform` / `from_secret` establishes about its output. -/
def ElemOK (f : ℕ → Zp) (ne : arithmetic.ntt.NttElem) : Prop :=
  State 256 1 1 f (aP ne) ∧ ∀ c, c < 256 → -pNtt < aZ ne c ∧ aZ ne c < pNtt

theorem from_uniform_elemOK (elem : arithmetic.ring_arith.RingElem) :
    arithmetic.ntt.NttElem.from_uniform elem
      ⦃ (r : arithmetic.ntt.NttElem) => ElemOK (uP elem) r ⦄ :=
  from_uniform_elem_spec elem

theorem from_secret_elemOK (elem : arithmetic.ring_arith.RingElem) :
    arithmetic.ntt.NttElem.from_secret elem
      ⦃ (r : arithmetic.ntt.NttElem) => ElemOK (sP elem) r ⦄ :=
  from_secret_elem_spec elem

/-- The leaf reading of `ElemOK`: entry `c` is the evaluation of `f` at the `c`-th leaf. -/
theorem ElemOK_leaf {f : ℕ → Zp} {ne : arithmetic.ntt.NttElem} (h : ElemOK f ne)
    (c : ℕ) (hc : c < 256) :
    aP ne c = ∑ i ∈ Finset.range 256, f i * cst (256 + c) ^ i := by
  have := State_leaf h.1 c hc
  rw [this, one_mul]

theorem ElemOK_bound {f : ℕ → Zp} {ne : arithmetic.ntt.NttElem} (h : ElemOK f ne)
    (c : ℕ) (hc : c < 256) : |aZ ne c| ≤ pNtt := by
  obtain ⟨hlo, hhi⟩ := h.2 c hc
  rw [abs_le]; omega

/-! ### The matrix loops

`from_uniform_matrix` / `from_secret_matrix` are entrywise maps of the element transform over an
`X × Y` matrix.  The invariants say: entries at or past the cursor have been filled with the
element transform of the corresponding coefficient entry; every other entry is untouched. -/

/-- `getElem!` after a `List.set` at an in-bounds index (local copy). -/
private theorem br_getElem!_list_set {α : Type _} [Inhabited α] (l : List α) (j : ℕ) (v : α)
    (k : ℕ) (hj : j < l.length) : (l.set j v)[k]! = if k = j then v else l[k]! := by
  by_cases h : k = j
  · subst h
    rw [getElem!_pos _ k (by rw [List.length_set]; exact hj), List.getElem_set_self, if_pos rfl]
  · by_cases hk : k < l.length
    · rw [getElem!_pos _ k (by rw [List.length_set]; exact hk),
        List.getElem_set_of_ne (Ne.symm h), ← getElem!_pos _ k hk, if_neg h]
    · rw [getElem!_neg _ k (by rw [List.length_set]; exact hk), getElem!_neg _ k hk, if_neg h]

/-- Reading back a single-entry update of a matrix of arrays. -/
private theorem arr2_writeback {α : Type} [Inhabited α] {X Y : Usize}
    (ret : Std.Array (Std.Array α Y) X) (i j : Usize) (row : Std.Array α Y) (ne : α)
    (hi : i.val < X.val) (hj : j.val < Y.val) (hrow : row = ret.val[i.val]!) (a b : ℕ) :
    (((ret.set i (row.set j ne)).val[a]!).val[b]!)
      = if a = i.val ∧ b = j.val then ne else (ret.val[a]!).val[b]! := by
  have hml : i.val < ret.val.length := by have := ret.property; scalar_tac
  have hrl : j.val < row.val.length := by have := row.property; scalar_tac
  rw [Std.Array.set_val_eq, br_getElem!_list_set ret.val i.val _ a hml]
  by_cases hai : a = i.val
  · rw [if_pos hai, Std.Array.set_val_eq, br_getElem!_list_set row.val j.val ne b hrl]
    by_cases hbj : b = j.val
    · rw [if_pos hbj, if_pos (⟨hai, hbj⟩ : a = i.val ∧ b = j.val)]
    · rw [if_neg hbj, if_neg (fun h : a = i.val ∧ b = j.val => hbj h.2), hai, hrow]
  · rw [if_neg hai, if_neg (fun h : a = i.val ∧ b = j.val => hai h.1)]

/-- The inner matrix loop, uniform variant: it fills row `i`'s columns from `iter.start` on. -/
theorem from_uniform_matrix_inner_spec {X Y : Usize}
    (iter : core.ops.range.Range Usize) (mat : Mat X Y)
    (ret : arithmetic.ntt.NttMatrix X Y) (i : Usize) (hi : i.val < X.val)
    (hend : iter.«end».val = Y.val) :
    arithmetic.ntt.NttMatrix.from_uniform_matrix_loop0_loop0 iter mat ret i
      ⦃ (p : (Mat X Y) × (arithmetic.ntt.NttMatrix X Y)) =>
          p.1 = mat
          ∧ (∀ b, iter.start.val ≤ b → b < Y.val →
              ElemOK (uP ((mat.val[i.val]!).val[b]!)) ((p.2.val[i.val]!).val[b]!))
          ∧ (∀ a b, (a ≠ i.val ∨ b < iter.start.val) →
              (p.2.val[a]!).val[b]! = (ret.val[a]!).val[b]!) ⦄ := by
  unfold arithmetic.ntt.NttMatrix.from_uniform_matrix_loop0_loop0
  by_cases hlt : iter.start.val < iter.«end».val
  · let* ⟨o, iter1, ho, hstart', hend'⟩ ← core.iter.range.IteratorRange.next_Usize_some_spec
    rw [ho]; simp only
    have hj_lt : iter.start.val < Y.val := by omega
    have hmi : i.val < mat.val.length := by have := mat.property; scalar_tac
    let* ⟨a, ha⟩ ← Array.index_usize_spec mat i hmi
    have ha' : a = mat.val[i.val]! := by rw [ha, getElem!_pos mat.val i.val hmi]
    have haj : iter.start.val < a.val.length := by have := a.property; scalar_tac
    let* ⟨re, hre⟩ ← Array.index_usize_spec a iter.start haj
    have hre' : re = (mat.val[i.val]!).val[iter.start.val]! := by
      rw [hre, ha', getElem!_pos (mat.val[i.val]!).val iter.start.val (by rw [← ha']; exact haj)]
    let* ⟨ne, hne⟩ ← from_uniform_elemOK re
    have hri : i.val < ret.length := by have := ret.property; scalar_tac
    let* ⟨a1, index_mut_back, ha1, hback⟩ ← Array.index_mut_usize_spec ret i hri
    have ha1' : a1 = ret.val[i.val]! := by
      rw [ha1, getElem!_pos ret.val i.val (by have := ret.property; scalar_tac)]
    have ha1j : iter.start.val < a1.length := by have := a1.property; scalar_tac
    let* ⟨a2, ha2⟩ ← Array.update_spec a1 iter.start ne ha1j
    have hnew : ∀ x y, ((index_mut_back a2).val[x]!).val[y]!
        = if x = i.val ∧ y = iter.start.val then ne else (ret.val[x]!).val[y]! := by
      intro x y
      rw [hback, ha2]
      exact arr2_writeback ret i iter.start a1 ne hi hj_lt ha1' x y
    apply WP.spec_mono (from_uniform_matrix_inner_spec iter1 mat (index_mut_back a2) i hi
      (by rw [hend']; exact hend))
    rintro ⟨p1, p2⟩ ⟨hp1, hp2, hp3⟩
    simp only at hp1 hp2 hp3
    rw [hstart'] at hp2 hp3
    refine ⟨hp1, ?_, ?_⟩
    · intro b hb1 hb2
      rcases Nat.eq_or_lt_of_le hb1 with hbe | hbgt
      · rw [hp3 i.val b (Or.inr (by omega)), hnew i.val b, if_pos ⟨rfl, hbe.symm⟩, ← hbe, ← hre']
        exact hne
      · exact hp2 b (by omega) hb2
    · intro x y hxy
      have hxy' : x ≠ i.val ∨ y < iter.start.val + 1 := by
        rcases hxy with h | h
        · exact Or.inl h
        · exact Or.inr (by omega)
      have hne2 : ¬ (x = i.val ∧ y = iter.start.val) := by
        rcases hxy with h | h
        · exact fun hc => h hc.1
        · exact fun hc => absurd hc.2 (by omega)
      rw [hp3 x y hxy', hnew x y, if_neg hne2]
  · let* ⟨o, iter1, hnone, _⟩ ← core.iter.range.IteratorRange.next_Usize_none_spec
    rw [hnone]; simp only [WP.spec_ok]
    exact ⟨trivial, fun b hb1 hb2 => absurd hb2 (by omega), fun _ _ _ => trivial⟩
  termination_by iter.«end».val - iter.start.val
  decreasing_by scalar_decr_tac

/-- The outer matrix loop, uniform variant. -/
theorem from_uniform_matrix_outer_spec {X Y : Usize}
    (iter : core.ops.range.Range Usize) (mat : Mat X Y)
    (ret : arithmetic.ntt.NttMatrix X Y) (hend : iter.«end».val = X.val) :
    arithmetic.ntt.NttMatrix.from_uniform_matrix_loop0 iter mat ret
      ⦃ (r : arithmetic.ntt.NttMatrix X Y) =>
          (∀ a b, iter.start.val ≤ a → a < X.val → b < Y.val →
              ElemOK (uP ((mat.val[a]!).val[b]!)) ((r.val[a]!).val[b]!))
          ∧ (∀ (a b : ℕ), a < iter.start.val →
              (r.val[a]!).val[b]! = (ret.val[a]!).val[b]!) ⦄ := by
  unfold arithmetic.ntt.NttMatrix.from_uniform_matrix_loop0
  by_cases hlt : iter.start.val < iter.«end».val
  · let* ⟨o, iter1, ho, hstart', hend'⟩ ← core.iter.range.IteratorRange.next_Usize_some_spec
    rw [ho]; simp only
    have hi_lt : iter.start.val < X.val := by omega
    let* ⟨mat1, ret1, hm1, hf1, hu1⟩ ←
      from_uniform_matrix_inner_spec { start := 0#usize, «end» := Y } mat ret iter.start hi_lt rfl
    subst hm1
    apply WP.spec_mono (from_uniform_matrix_outer_spec iter1 mat1 ret1
      (by rw [hend']; exact hend))
    rintro r ⟨hr1, hr2⟩
    rw [hstart'] at hr1 hr2
    refine ⟨?_, ?_⟩
    · intro a b ha1 ha2 hb
      rcases Nat.eq_or_lt_of_le ha1 with hae | hagt
      · rw [hr2 a b (by omega), ← hae]
        exact hf1 b (Nat.zero_le b) hb
      · exact hr1 a b (by omega) ha2 hb
    · intro a b ha
      rw [hr2 a b (by omega), hu1 a b (Or.inl (by omega))]
  · let* ⟨o, iter1, hnone, _⟩ ← core.iter.range.IteratorRange.next_Usize_none_spec
    rw [hnone]; simp only [WP.spec_ok]
    exact ⟨fun a b ha1 ha2 hb => absurd ha2 (by omega), by simp⟩
  termination_by iter.«end».val - iter.start.val
  decreasing_by scalar_decr_tac

/-- **`from_uniform_matrix` transforms every entry.** -/
theorem from_uniform_matrix_full {X Y : Usize} (A : Mat X Y) :
    arithmetic.ntt.NttMatrix.from_uniform_matrix A
      ⦃ (r : arithmetic.ntt.NttMatrix X Y) =>
          ∀ a b, a < X.val → b < Y.val →
            ElemOK (uP ((A.val[a]!).val[b]!)) ((r.val[a]!).val[b]!) ⦄ := by
  unfold arithmetic.ntt.NttMatrix.from_uniform_matrix
    arithmetic.ntt.NttMatrix.Insts.CoreDefaultDefault.default
    arithmetic.ntt.NttElem.Insts.CoreDefaultDefault.default
  simp only [bind_tc_ok]
  apply WP.spec_mono (from_uniform_matrix_outer_spec { start := 0#usize, «end» := X } A _ rfl)
  rintro r ⟨hr1, _⟩
  exact fun a b ha hb => hr1 a b (Nat.zero_le a) ha hb

/-- The inner matrix loop, secret variant. -/
theorem from_secret_matrix_inner_spec {X Y : Usize}
    (iter : core.ops.range.Range Usize) (mat : Mat X Y)
    (ret : arithmetic.ntt.NttMatrix X Y) (i : Usize) (hi : i.val < X.val)
    (hend : iter.«end».val = Y.val) :
    arithmetic.ntt.NttMatrix.from_secret_matrix_loop0_loop0 iter mat ret i
      ⦃ (p : (Mat X Y) × (arithmetic.ntt.NttMatrix X Y)) =>
          p.1 = mat
          ∧ (∀ b, iter.start.val ≤ b → b < Y.val →
              ElemOK (sP ((mat.val[i.val]!).val[b]!)) ((p.2.val[i.val]!).val[b]!))
          ∧ (∀ a b, (a ≠ i.val ∨ b < iter.start.val) →
              (p.2.val[a]!).val[b]! = (ret.val[a]!).val[b]!) ⦄ := by
  unfold arithmetic.ntt.NttMatrix.from_secret_matrix_loop0_loop0
  by_cases hlt : iter.start.val < iter.«end».val
  · let* ⟨o, iter1, ho, hstart', hend'⟩ ← core.iter.range.IteratorRange.next_Usize_some_spec
    rw [ho]; simp only
    have hj_lt : iter.start.val < Y.val := by omega
    have hmi : i.val < mat.val.length := by have := mat.property; scalar_tac
    let* ⟨a, ha⟩ ← Array.index_usize_spec mat i hmi
    have ha' : a = mat.val[i.val]! := by rw [ha, getElem!_pos mat.val i.val hmi]
    have haj : iter.start.val < a.val.length := by have := a.property; scalar_tac
    let* ⟨re, hre⟩ ← Array.index_usize_spec a iter.start haj
    have hre' : re = (mat.val[i.val]!).val[iter.start.val]! := by
      rw [hre, ha', getElem!_pos (mat.val[i.val]!).val iter.start.val (by rw [← ha']; exact haj)]
    let* ⟨ne, hne⟩ ← from_secret_elemOK re
    have hri : i.val < ret.length := by have := ret.property; scalar_tac
    let* ⟨a1, index_mut_back, ha1, hback⟩ ← Array.index_mut_usize_spec ret i hri
    have ha1' : a1 = ret.val[i.val]! := by
      rw [ha1, getElem!_pos ret.val i.val (by have := ret.property; scalar_tac)]
    have ha1j : iter.start.val < a1.length := by have := a1.property; scalar_tac
    let* ⟨a2, ha2⟩ ← Array.update_spec a1 iter.start ne ha1j
    have hnew : ∀ x y, ((index_mut_back a2).val[x]!).val[y]!
        = if x = i.val ∧ y = iter.start.val then ne else (ret.val[x]!).val[y]! := by
      intro x y
      rw [hback, ha2]
      exact arr2_writeback ret i iter.start a1 ne hi hj_lt ha1' x y
    apply WP.spec_mono (from_secret_matrix_inner_spec iter1 mat (index_mut_back a2) i hi
      (by rw [hend']; exact hend))
    rintro ⟨p1, p2⟩ ⟨hp1, hp2, hp3⟩
    simp only at hp1 hp2 hp3
    rw [hstart'] at hp2 hp3
    refine ⟨hp1, ?_, ?_⟩
    · intro b hb1 hb2
      rcases Nat.eq_or_lt_of_le hb1 with hbe | hbgt
      · rw [hp3 i.val b (Or.inr (by omega)), hnew i.val b, if_pos ⟨rfl, hbe.symm⟩, ← hbe, ← hre']
        exact hne
      · exact hp2 b (by omega) hb2
    · intro x y hxy
      have hxy' : x ≠ i.val ∨ y < iter.start.val + 1 := by
        rcases hxy with h | h
        · exact Or.inl h
        · exact Or.inr (by omega)
      have hne2 : ¬ (x = i.val ∧ y = iter.start.val) := by
        rcases hxy with h | h
        · exact fun hc => h hc.1
        · exact fun hc => absurd hc.2 (by omega)
      rw [hp3 x y hxy', hnew x y, if_neg hne2]
  · let* ⟨o, iter1, hnone, _⟩ ← core.iter.range.IteratorRange.next_Usize_none_spec
    rw [hnone]; simp only [WP.spec_ok]
    exact ⟨trivial, fun b hb1 hb2 => absurd hb2 (by omega), fun _ _ _ => trivial⟩
  termination_by iter.«end».val - iter.start.val
  decreasing_by scalar_decr_tac

/-- The outer matrix loop, secret variant. -/
theorem from_secret_matrix_outer_spec {X Y : Usize}
    (iter : core.ops.range.Range Usize) (mat : Mat X Y)
    (ret : arithmetic.ntt.NttMatrix X Y) (hend : iter.«end».val = X.val) :
    arithmetic.ntt.NttMatrix.from_secret_matrix_loop0 iter mat ret
      ⦃ (r : arithmetic.ntt.NttMatrix X Y) =>
          (∀ a b, iter.start.val ≤ a → a < X.val → b < Y.val →
              ElemOK (sP ((mat.val[a]!).val[b]!)) ((r.val[a]!).val[b]!))
          ∧ (∀ (a b : ℕ), a < iter.start.val →
              (r.val[a]!).val[b]! = (ret.val[a]!).val[b]!) ⦄ := by
  unfold arithmetic.ntt.NttMatrix.from_secret_matrix_loop0
  by_cases hlt : iter.start.val < iter.«end».val
  · let* ⟨o, iter1, ho, hstart', hend'⟩ ← core.iter.range.IteratorRange.next_Usize_some_spec
    rw [ho]; simp only
    have hi_lt : iter.start.val < X.val := by omega
    let* ⟨mat1, ret1, hm1, hf1, hu1⟩ ←
      from_secret_matrix_inner_spec { start := 0#usize, «end» := Y } mat ret iter.start hi_lt rfl
    subst hm1
    apply WP.spec_mono (from_secret_matrix_outer_spec iter1 mat1 ret1
      (by rw [hend']; exact hend))
    rintro r ⟨hr1, hr2⟩
    rw [hstart'] at hr1 hr2
    refine ⟨?_, ?_⟩
    · intro a b ha1 ha2 hb
      rcases Nat.eq_or_lt_of_le ha1 with hae | hagt
      · rw [hr2 a b (by omega), ← hae]
        exact hf1 b (Nat.zero_le b) hb
      · exact hr1 a b (by omega) ha2 hb
    · intro a b ha
      rw [hr2 a b (by omega), hu1 a b (Or.inl (by omega))]
  · let* ⟨o, iter1, hnone, _⟩ ← core.iter.range.IteratorRange.next_Usize_none_spec
    rw [hnone]; simp only [WP.spec_ok]
    exact ⟨fun a b ha1 ha2 hb => absurd ha2 (by omega), by simp⟩
  termination_by iter.«end».val - iter.start.val
  decreasing_by scalar_decr_tac

/-- **`from_secret_matrix` transforms every entry.** -/
theorem from_secret_matrix_full {X Y : Usize} (s : Mat X Y) :
    arithmetic.ntt.NttMatrix.from_secret_matrix s
      ⦃ (r : arithmetic.ntt.NttMatrix X Y) =>
          ∀ a b, a < X.val → b < Y.val →
            ElemOK (sP ((s.val[a]!).val[b]!)) ((r.val[a]!).val[b]!) ⦄ := by
  unfold arithmetic.ntt.NttMatrix.from_secret_matrix
    arithmetic.ntt.NttMatrix.Insts.CoreDefaultDefault.default
    arithmetic.ntt.NttElem.Insts.CoreDefaultDefault.default
  simp only [bind_tc_ok]
  apply WP.spec_mono (from_secret_matrix_outer_spec { start := 0#usize, «end» := X } s _ rfl)
  rintro r ⟨hr1, _⟩
  exact fun a b ha hb => hr1 a b (Nat.zero_le a) ha hb

/-! ### From the triples to the denotations

A triple with *any* postcondition already forces success, so it transfers verbatim to the total
`Result.getD` value — which is how `nttFwdU`/`nttFwdS` are defined.  This is the payoff of
pointing the bridge forward: the two `from_*_matrix` specs and the entrywise characterisations of
`nttFwdU`/`nttFwdS` are all one-line consequences of the loop proofs. -/

/-- Any postcondition of a triple holds of the extracted `Result.getD` value. -/
theorem getD_of_spec {α : Type} [Inhabited α] {m : Result α} {P : α → Prop} (h : m ⦃ P ⦄) :
    P (Result.getD m) := by
  cases hm : m with
  | ok v => rw [hm] at h; simpa only [Result.getD, WP.spec_ok] using h
  | fail e => rw [hm] at h; simp [WP.spec, WP.theta] at h
  | div => rw [hm] at h; simp [WP.spec, WP.theta] at h

/-- Weakening to the pure success claim, which `spec_eq_getD` turns into the value. -/
theorem from_uniform_matrix_ok {X Y : Usize} (A : Mat X Y) :
    arithmetic.ntt.NttMatrix.from_uniform_matrix A ⦃ fun _ => True ⦄ :=
  WP.spec_mono (from_uniform_matrix_full A) (fun _ _ => trivial)

theorem from_secret_matrix_ok {X Y : Usize} (s : Mat X Y) :
    arithmetic.ntt.NttMatrix.from_secret_matrix s ⦃ fun _ => True ⦄ :=
  WP.spec_mono (from_secret_matrix_full s) (fun _ _ => trivial)

/-- A `⦃ fun _ => True ⦄` triple is exactly success, so the `Result.getD` value is the result. -/
theorem spec_eq_getD {α : Type} [Inhabited α] {m : Result α} (h : m ⦃ fun _ => True ⦄) :
    m ⦃ (r : α) => r = Result.getD m ⦄ := by
  cases hm : m with
  | ok v => simp only [Result.getD, WP.spec_ok]
  | fail e => rw [hm] at h; simp [WP.spec, WP.theta] at h
  | div => rw [hm] at h; simp [WP.spec, WP.theta] at h

/-- **`from_uniform_matrix A` succeeds, with value `nttFwdU A`.** -/
theorem from_uniform_matrix_spec {X Y : Usize} (A : Mat X Y) :
    arithmetic.ntt.NttMatrix.from_uniform_matrix A
      ⦃ (r : arithmetic.ntt.NttMatrix X Y) => r = nttFwdU A ⦄ :=
  spec_eq_getD (from_uniform_matrix_ok A)

/-- **`from_secret_matrix s` succeeds, with value `nttFwdS s`.** -/
theorem from_secret_matrix_spec {X Y : Usize} (s : Mat X Y) :
    arithmetic.ntt.NttMatrix.from_secret_matrix s
      ⦃ (r : arithmetic.ntt.NttMatrix X Y) => r = nttFwdS s ⦄ :=
  spec_eq_getD (from_secret_matrix_ok s)

/-- **Every entry of `nttFwdU A` is the forward transform of the matching coefficient entry.** -/
theorem nttFwdU_entry {X Y : Usize} (A : Mat X Y) (a b : ℕ) (ha : a < X.val) (hb : b < Y.val) :
    ElemOK (uP ((A.val[a]!).val[b]!)) (((nttFwdU A).val[a]!).val[b]!) :=
  getD_of_spec (from_uniform_matrix_full A) a b ha hb

/-- **Every entry of `nttFwdS s` is the forward transform of the matching coefficient entry.** -/
theorem nttFwdS_entry {X Y : Usize} (s : Mat X Y) (a b : ℕ) (ha : a < X.val) (hb : b < Y.val) :
    ElemOK (sP ((s.val[a]!).val[b]!)) (((nttFwdS s).val[a]!).val[b]!) :=
  getD_of_spec (from_secret_matrix_full s) a b ha hb

/-! ## The convolution theorem

`NttMatrix::mul` computes entry `(i,k)` as `reduce_invntt_to_ring_elem (Σ_j lhs_j ∘ rhs_j)`.
`ntt_entry_spec` below is the whole of the mathematics: pointwise multiplication in the NTT
domain, undone by the inverse transform, is the negacyclic convolution of the coefficient
matrices — accumulated over the inner index — and the exactness bound makes the mod-`p`
computation determine the integer answer, hence the `ℤ/2¹⁶` one the specification asks for.

The three nested loops on top of it are ordinary bookkeeping. -/

/-! ### Coefficientwise reading of the spec's polynomials -/

private theorem poly_add_get {m : ℕ} (f g : Spec.Kopis.Polynomial m) (n : ℕ) (hn : n < 256) :
    (f + g)[n]'hn = f[n]'hn + g[n]'hn := by
  show (Spec.Kopis.Polynomial.add f g)[n]'hn = _
  simp only [Spec.Kopis.Polynomial.add, Vector.getElem_zipWith]

private theorem poly_zero_get {m : ℕ} (n : ℕ) (hn : n < 256) :
    (0 : Spec.Kopis.Polynomial m)[n]'hn = 0 := by
  show (Spec.Kopis.Polynomial.zero m)[n]'hn = 0
  simp only [Spec.Kopis.Polynomial.zero, Vector.getElem_replicate]

/-- Coefficient `n` of a finite sum of ring elements is the sum of the coefficients. -/
theorem poly_sum_get {m : ℕ} (S : Finset ℕ) (F : ℕ → Spec.Kopis.Polynomial m)
    (n : ℕ) (hn : n < 256) : (∑ j ∈ S, F j)[n]'hn = ∑ j ∈ S, (F j)[n]'hn := by
  classical
  induction S using Finset.induction with
  | empty => simp only [Finset.sum_empty]; exact poly_zero_get n hn
  | insert a S ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    calc (F a + ∑ x ∈ S, F x)[n]'hn = (F a)[n]'hn + (∑ x ∈ S, F x)[n]'hn :=
          poly_add_get (F a) (∑ x ∈ S, F x) n hn
      _ = (F a)[n]'hn + ∑ x ∈ S, (F x)[n]'hn := by rw [ih]

/-- The abstraction `toRingElem` reads coefficient `n` as the stored `u16`. -/
theorem toRingElem_get (re : arithmetic.ring_arith.RingElem) (n : ℕ) (hn : n < 256) :
    (toRingElem re)[n]'hn = (((re.val[n]!).val : ℕ) : ZMod (2 ^ 16)) := by
  have hb : n < re.val.length := by have := re.property; grind
  simp only [toRingElem, Vector.getElem_ofFn]
  rw [getElem!_pos re.val n hb]

theorem toRingElem_get! (re : arithmetic.ring_arith.RingElem) (n : ℕ) (hn : n < 256) :
    (toRingElem re)[n]! = (((re.val[n]!).val : ℕ) : ZMod (2 ^ 16)) := by
  rw [getElem!_pos (toRingElem re) n hn]
  exact toRingElem_get re n hn

/-- The audited negacyclic product coefficient is the single-sum convolution. -/
theorem convCoeff_eq_nconvR {m : ℕ} (a b : Spec.Kopis.Polynomial m) (n : ℕ) (hn : n < 256) :
    convCoeff a b n = NttMath.nconvR (fun i => a[i]!) (fun j => b[j]!) n := by
  unfold convCoeff NttMath.nconvR
  refine Finset.sum_congr rfl (fun i hi => ?_)
  have hi' : i < 256 := Finset.mem_range.mp hi
  by_cases hle : i ≤ n
  · rw [if_pos hle, Finset.sum_eq_single (n - i)]
    · rw [convContrib, if_pos (by omega), if_pos (by omega)]
    · intro j hj hne
      have hj' : j < 256 := Finset.mem_range.mp hj
      rw [convContrib, if_neg (by omega)]
    · intro hm; exact absurd (Finset.mem_range.mpr (by omega : n - i < 256)) hm
  · rw [if_neg hle, Finset.sum_eq_single (n + 256 - i)]
    · rw [convContrib, if_pos (by omega), if_neg (by omega)]; ring
    · intro j hj hne
      have hj' : j < 256 := Finset.mem_range.mp hj
      rw [convContrib, if_neg (by omega)]
    · intro hm; exact absurd (Finset.mem_range.mpr (by omega : n + 256 - i < 256)) hm

/-- The signed reading of a stored `u16` agrees with it in `ℤ/2¹⁶`. -/
theorem sZ_cast (re : arithmetic.ring_arith.RingElem) (c : ℕ) :
    ((sZ re c : ℤ) : ZMod (2 ^ 16)) = (((re.val[c]!).val : ℕ) : ZMod (2 ^ 16)) := by
  have h := signedOfU16_emod (re.val[c]!)
  have hc : ((2 ^ 16 : ℕ) : ℤ) = 65536 := by norm_num
  have := (ZMod.intCast_eq_intCast_iff' (sZ re c) ((re.val[c]!).val : ℤ) (2 ^ 16)).mpr
    (by rw [hc]; exact h)
  rw [this]
  push_cast
  rfl

/-- The unsigned reading of a stored `u16` in `ℤ/2¹⁶`. -/
theorem uZ_cast (re : arithmetic.ring_arith.RingElem) (c : ℕ) :
    ((uZ re c : ℤ) : ZMod (2 ^ 16)) = (((re.val[c]!).val : ℕ) : ZMod (2 ^ 16)) := by
  unfold uZ; push_cast; rfl

/-! ### One entry of the product

Both `mul` and `mul_transpose` reduce to the same statement about a single output ring element:
an `i64` accumulator holding `Σ_j (forward transform of uⱼ) ∘ (forward transform of vⱼ)` is
turned by `reduce_invntt_to_ring_elem` into `Σ_j uⱼ · vⱼ` in `ℤ[X]/(X²⁵⁶+1)`.  Stating it over
two arbitrary families `u`, `v` — rather than over a row of `A` and a column of `s` — is what
lets one proof serve both multipliers. -/

/-- The `ℤ/p` coefficient function of the answer. -/
def convP (u v : ℕ → arithmetic.ring_arith.RingElem) (N n : ℕ) : Zp :=
  ∑ jj ∈ Finset.range N, NttMath.nconvR (uP (u jj)) (sP (v jj)) n

/-- Its integer lift — the *exact* answer, which `fitsExactly` keeps inside `(-p/2, p/2)`. -/
def convZ (u v : ℕ → arithmetic.ring_arith.RingElem) (N n : ℕ) : ℤ :=
  ∑ jj ∈ Finset.range N, NttMath.nconvR (uZ (u jj)) (sZ (v jj)) n

set_option maxRecDepth 8000 in
/-- **The convolution theorem, for one entry.**  If the `i64` accumulator holds the sum over `jj`
of the pointwise products of the transforms of `u jj` and `v jj`, then
`reduce_invntt_to_ring_elem` returns exactly `Σ_jj u jj · v jj` in `ℤ[X]/(X²⁵⁶+1)` with
`ZMod (2¹⁶)` coefficients — the schoolbook answer. -/
theorem ntt_entry_spec (N : ℕ) (sBound : ℤ)
    (u v : ℕ → arithmetic.ring_arith.RingElem)
    (nu nv : ℕ → arithmetic.ntt.NttElem)
    (hu : ∀ jj, jj < N → ElemOK (uP (u jj)) (nu jj))
    (hv : ∀ jj, jj < N → ElemOK (sP (v jj)) (nv jj))
    (hfit : fitsExactly N sBound)
    (hub : ∀ jj c, jj < N → c < 256 → ((u jj).val[c]!).val < 2 ^ 13)
    (hvb : ∀ jj c, jj < N → c < 256 → |signedOfU16 ((v jj).val[c]!)| ≤ sBound)
    (hN : N ≤ 4)
    (acc : Array I64 256#usize)
    (hacc : ∀ c, c < 256 → accZ acc c
        = ∑ jj ∈ Finset.range N, aZ (nu jj) c * aZ (nv jj) c) :
    arithmetic.ntt.reduce_invntt_to_ring_elem acc
      ⦃ (r : arithmetic.ring_arith.RingElem) =>
          toRingElem r = ∑ jj ∈ Finset.range N, toRingElem (u jj) * toRingElem (v jj) ⦄ := by
  have hp0 : (0:ℤ) < pNtt := by unfold pNtt; norm_num
  have hNz : ((N : ℤ)) ≤ 4 := by exact_mod_cast hN
  have hNn : (0:ℤ) ≤ (N : ℤ) := Int.natCast_nonneg _
  -- ## the accumulator is inside `mont_reduce`'s input range
  have haccb : ∀ c, c < 256 → |accZ acc c| ≤ 2 ^ 31 * pNtt - 1 := by
    intro c hc
    rw [hacc c hc]
    have hterm : ∀ jj ∈ Finset.range N, |aZ (nu jj) c * aZ (nv jj) c| ≤ pNtt * pNtt := by
      intro jj hjj
      have hjj' : jj < N := Finset.mem_range.mp hjj
      rw [abs_mul]
      exact mul_le_mul (ElemOK_bound (hu jj hjj') c hc) (ElemOK_bound (hv jj hjj') c hc)
        (abs_nonneg _) (le_of_lt hp0)
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    refine le_trans (Finset.sum_le_sum hterm) ?_
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul,
      show pNtt * pNtt = 2533120274592769 from by unfold pNtt; norm_num,
      show (2:ℤ) ^ 31 * pNtt - 1 = 108083094669492223 from by unfold pNtt; norm_num]
    linarith
  -- ## the exactness bound: the integer answer is inside `(-p/2, p/2)`
  have hHb : ∀ n, n < 256 → |convZ u v N n| ≤ 25165056 := by
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
    linarith
  -- ## the integer answer reduces to the `ℤ/p` one
  have hHz : ∀ n, n < 256 → ((convZ u v N n : ℤ) : Zp) = convP u v N n := by
    intro n hn
    unfold convZ convP
    rw [Int.cast_sum]
    refine Finset.sum_congr rfl (fun jj _ => ?_)
    rw [NttMath.nconvR_intCast]
    rfl
  -- ## the accumulator evaluates the convolution at every leaf
  have hst : ∀ c, c < 256 → ((accZ acc c : ℤ) : Zp)
      = ∑ n ∈ Finset.range 256, convP u v N n * cst (256 + c) ^ n := by
    intro c hc
    have hleaf : ∀ jj, jj < N →
        ((aZ (nu jj) c : ℤ) : Zp) * ((aZ (nv jj) c : ℤ) : Zp)
          = ∑ n ∈ Finset.range 256,
              NttMath.nconvR (uP (u jj)) (sP (v jj)) n * cst (256 + c) ^ n := by
      intro jj hjj
      rw [← aP_def, ← aP_def, ElemOK_leaf (hu jj hjj) c hc, ElemOK_leaf (hv jj hjj) c hc,
        Ev_nconv _ _ (cst_leaf_pow c hc)]
      exact Finset.sum_congr rfl
        (fun n hn => by rw [nconv_eq_nconvR _ _ n (Finset.mem_range.mp hn)])
    calc ((accZ acc c : ℤ) : Zp)
        = ∑ jj ∈ Finset.range N, ((aZ (nu jj) c : ℤ) : Zp) * ((aZ (nv jj) c : ℤ) : Zp) := by
          rw [hacc c hc, Int.cast_sum]
          exact Finset.sum_congr rfl (fun jj _ => Int.cast_mul _ _)
      _ = ∑ jj ∈ Finset.range N, ∑ n ∈ Finset.range 256,
            NttMath.nconvR (uP (u jj)) (sP (v jj)) n * cst (256 + c) ^ n :=
          Finset.sum_congr rfl (fun jj hjj => hleaf jj (Finset.mem_range.mp hjj))
      _ = ∑ n ∈ Finset.range 256, ∑ jj ∈ Finset.range N,
            NttMath.nconvR (uP (u jj)) (sP (v jj)) n * cst (256 + c) ^ n := Finset.sum_comm
      _ = ∑ n ∈ Finset.range 256, convP u v N n * cst (256 + c) ^ n := by
          refine Finset.sum_congr rfl (fun n _ => ?_)
          unfold convP
          rw [Finset.sum_mul]
  -- ## run the pipeline and match the specification's coefficients
  apply WP.spec_mono (reduce_invntt_to_ring_elem_spec acc (convP u v N) (convZ u v N)
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
    (fun c hc => by rw [sZ_cast, toRingElem_get! _ c hc])

/-! ### The three nested loops of `mul` -/

private theorem br_sum_Ico_peel {M : Type*} [AddCommMonoid M] (f : ℕ → M) {a b : ℕ} (h : a < b) :
    ∑ j ∈ Finset.Ico a b, f j = f a + ∑ j ∈ Finset.Ico (a + 1) b, f j := by
  rw [show a + 1 = a.succ from rfl, Nat.Ico_succ_left_eq_erase_Ico,
    Finset.add_sum_erase _ f (Finset.mem_Ico.mpr ⟨le_refl a, h⟩)]

/-- The innermost loop of `mul`: accumulate the pointwise products over the inner index. -/
theorem ntt_mul_inner_spec {X Y Z : Usize}
    (iter : core.ops.range.Range Usize)
    (self : arithmetic.ntt.NttMatrix X Y) (other : arithmetic.ntt.NttMatrix Y Z)
    (i k : Usize) (acc : Array I64 256#usize)
    (hi : i.val < X.val) (hk : k.val < Z.val)
    (hstart : iter.start.val ≤ Y.val) (hend : iter.«end».val = Y.val) (hY : Y.val ≤ 4)
    (hself : ∀ j c, j < Y.val → c < 256 → |aZ ((self.val[i.val]!).val[j]!) c| ≤ pNtt)
    (hother : ∀ j c, j < Y.val → c < 256 → |aZ ((other.val[j]!).val[k.val]!) c| ≤ pNtt)
    (hacc : ∀ c, c < 256 → |accZ acc c| ≤ (iter.start.val : ℤ) * (pNtt * pNtt)) :
    arithmetic.ntt.NttMatrix.mul_loop0_loop0_loop0 iter self other i k acc
      ⦃ (p : (arithmetic.ntt.NttMatrix X Y) × (arithmetic.ntt.NttMatrix Y Z) ×
             (Array I64 256#usize)) =>
          p.1 = self ∧ p.2.1 = other ∧
          (∀ c, c < 256 → accZ p.2.2 c = accZ acc c
            + ∑ jj ∈ Finset.Ico iter.start.val Y.val,
                aZ ((self.val[i.val]!).val[jj]!) c * aZ ((other.val[jj]!).val[k.val]!) c) ⦄ := by
  have hpp : pNtt * pNtt = 2533120274592769 := by unfold pNtt; norm_num
  unfold arithmetic.ntt.NttMatrix.mul_loop0_loop0_loop0
  by_cases hlt : iter.start.val < iter.«end».val
  · let* ⟨o, iter1, ho, hstart', hend'⟩ ← core.iter.range.IteratorRange.next_Usize_some_spec
    rw [ho]; simp only
    have hj_lt : iter.start.val < Y.val := by omega
    have hsi : i.val < self.val.length := by have := self.property; scalar_tac
    let* ⟨a, ha⟩ ← Array.index_usize_spec self i hsi
    have ha' : a = self.val[i.val]! := by rw [ha, getElem!_pos self.val i.val hsi]
    have haj : iter.start.val < a.val.length := by have := a.property; scalar_tac
    let* ⟨ne, hne⟩ ← Array.index_usize_spec a iter.start haj
    have hne' : ne = (self.val[i.val]!).val[iter.start.val]! := by
      rw [hne, ha', getElem!_pos (self.val[i.val]!).val iter.start.val (by rw [← ha']; exact haj)]
    have hoj : iter.start.val < other.val.length := by have := other.property; scalar_tac
    let* ⟨a1, ha1⟩ ← Array.index_usize_spec other iter.start hoj
    have ha1' : a1 = other.val[iter.start.val]! := by
      rw [ha1, getElem!_pos other.val iter.start.val hoj]
    have ha1k : k.val < a1.val.length := by have := a1.property; scalar_tac
    let* ⟨ne1, hne1⟩ ← Array.index_usize_spec a1 k ha1k
    have hne1' : ne1 = (other.val[iter.start.val]!).val[k.val]! := by
      rw [hne1, ha1', getElem!_pos (other.val[iter.start.val]!).val k.val (by rw [← ha1']; exact ha1k)]
    -- the pointwise multiply-accumulate
    have hstz : (0:ℤ) ≤ (iter.start.val : ℤ) := Int.natCast_nonneg _
    have hstle : ((iter.start.val : ℤ)) ≤ 4 := by exact_mod_cast (by omega : iter.start.val ≤ 4)
    let* ⟨acc1, hacc1v, hacc1b⟩ ← pointwise_mul_acc_spec acc ne ne1
      ((iter.start.val : ℤ) * (pNtt * pNtt))
      (by rw [hne']; exact fun c hc => hself iter.start.val c hj_lt hc)
      (by rw [hne1']; exact fun c hc => hother iter.start.val c hj_lt hc)
      (mul_nonneg hstz (by unfold pNtt; norm_num))
      (by
        rw [hpp] at *
        linarith) hacc
    apply WP.spec_mono (ntt_mul_inner_spec iter1 self other i k acc1 hi hk
      (by omega) (by rw [hend']; exact hend) hY hself hother
      (fun c hc => by
        refine le_trans (hacc1b c hc) ?_
        rw [hstart']
        push_cast
        linarith))
    rintro ⟨p1, p2, p3⟩ ⟨hp1, hp2, hp3⟩
    simp only at hp1 hp2 hp3
    refine ⟨hp1, hp2, ?_⟩
    intro c hc
    rw [hp3 c hc, hacc1v c hc, hstart', hne', hne1',
      br_sum_Ico_peel _ hj_lt]
    ring
  · let* ⟨o, iter1, hnone, _⟩ ← core.iter.range.IteratorRange.next_Usize_none_spec
    rw [hnone]; simp only [WP.spec_ok]
    refine ⟨trivial, trivial, fun c hc => ?_⟩
    rw [Finset.Ico_eq_empty (by omega), Finset.sum_empty, add_zero]
  termination_by iter.«end».val - iter.start.val
  decreasing_by scalar_decr_tac

/-- The middle loop of `mul`: one output ring element per column `k`. -/
theorem ntt_mul_mid_spec {X Y Z : Usize} (A : Mat X Y) (s : Mat Y Z) (sBound : ℤ)
    (hfit : fitsExactly Y.val sBound) (hA : UniformBounded A) (hs : SecretBounded s sBound)
    (hY : Y.val ≤ 4)
    (iter : core.ops.range.Range Usize) (result : Mat X Z) (i : Usize) (hi : i.val < X.val)
    (hend : iter.«end».val = Z.val) :
    arithmetic.ntt.NttMatrix.mul_loop0_loop0 iter (nttFwdU A) (nttFwdS s) result i
      ⦃ (p : (arithmetic.ntt.NttMatrix X Y) × (arithmetic.ntt.NttMatrix Y Z) × (Mat X Z)) =>
          p.1 = nttFwdU A ∧ p.2.1 = nttFwdS s ∧
          (∀ ii kk, ii < X.val → kk < Z.val →
            toRingElem ((p.2.2.val[ii]!).val[kk]!)
              = if ii = i.val ∧ iter.start.val ≤ kk then
                  ∑ jj ∈ Finset.range Y.val,
                    toRingElem ((A.val[ii]!).val[jj]!) * toRingElem ((s.val[jj]!).val[kk]!)
                else toRingElem ((result.val[ii]!).val[kk]!)) ⦄ := by
  unfold arithmetic.ntt.NttMatrix.mul_loop0_loop0
  by_cases hlt : iter.start.val < iter.«end».val
  · let* ⟨o, iter1, ho, hstart', hend'⟩ ← core.iter.range.IteratorRange.next_Usize_some_spec
    rw [ho]; simp only
    have hk_lt : iter.start.val < Z.val := by omega
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
      (fun jj c hjj hc => hs jj iter.start.val c hjj hk_lt hc) hY acc1 hacc1'
    have hri : i.val < result.length := by have := result.property; scalar_tac
    let* ⟨a, index_mut_back, ha, hback⟩ ← Array.index_mut_usize_spec result i hri
    have ha' : a = result.val[i.val]! := by
      rw [ha, getElem!_pos result.val i.val (by have := result.property; scalar_tac)]
    have hak : iter.start.val < a.length := by have := a.property; scalar_tac
    let* ⟨a1, ha1⟩ ← Array.update_spec a iter.start re hak
    have hnew : ∀ x y, ((index_mut_back a1).val[x]!).val[y]!
        = if x = i.val ∧ y = iter.start.val then re else (result.val[x]!).val[y]! := by
      intro x y
      rw [hback, ha1]
      exact arr2_writeback result i iter.start a re hi hk_lt ha' x y
    apply WP.spec_mono (ntt_mul_mid_spec A s sBound hfit hA hs hY iter1 (index_mut_back a1) i hi
      (by rw [hend']; exact hend))
    rintro ⟨p1, p2, p3⟩ ⟨hp1, hp2, hp3⟩
    simp only at hp1 hp2 hp3
    refine ⟨hp1, hp2, ?_⟩
    intro ii kk hii hkk
    rw [hp3 ii kk hii hkk, hstart', hnew ii kk]
    by_cases hc1 : ii = i.val
    · by_cases hkke : kk = iter.start.val
      · rw [if_neg (show ¬ (ii = i.val ∧ iter.start.val + 1 ≤ kk) from by omega),
          if_pos (show ii = i.val ∧ kk = iter.start.val from ⟨hc1, hkke⟩),
          if_pos (show ii = i.val ∧ iter.start.val ≤ kk from ⟨hc1, by omega⟩)]
        subst hc1; subst hkke
        exact hre
      · by_cases hle : iter.start.val ≤ kk
        · rw [if_pos (show ii = i.val ∧ iter.start.val + 1 ≤ kk from ⟨hc1, by omega⟩),
            if_pos (show ii = i.val ∧ iter.start.val ≤ kk from ⟨hc1, hle⟩)]
        · rw [if_neg (show ¬ (ii = i.val ∧ iter.start.val + 1 ≤ kk) from by omega),
            if_neg (show ¬ (ii = i.val ∧ kk = iter.start.val) from by omega),
            if_neg (show ¬ (ii = i.val ∧ iter.start.val ≤ kk) from by omega)]
    · rw [if_neg (show ¬ (ii = i.val ∧ iter.start.val + 1 ≤ kk) from fun h => hc1 h.1),
        if_neg (show ¬ (ii = i.val ∧ kk = iter.start.val) from fun h => hc1 h.1),
        if_neg (show ¬ (ii = i.val ∧ iter.start.val ≤ kk) from fun h => hc1 h.1)]
  · let* ⟨o, iter1, hnone, _⟩ ← core.iter.range.IteratorRange.next_Usize_none_spec
    rw [hnone]; simp only [WP.spec_ok]
    refine ⟨trivial, trivial, fun ii kk hii hkk => ?_⟩
    rw [if_neg (by omega : ¬ (ii = i.val ∧ iter.start.val ≤ kk))]
  termination_by iter.«end».val - iter.start.val
  decreasing_by scalar_decr_tac

/-- The outer loop of `mul`: one row of the product per `i`. -/
theorem ntt_mul_outer_spec {X Y Z : Usize} (A : Mat X Y) (s : Mat Y Z) (sBound : ℤ)
    (hfit : fitsExactly Y.val sBound) (hA : UniformBounded A) (hs : SecretBounded s sBound)
    (hY : Y.val ≤ 4)
    (iter : core.ops.range.Range Usize) (result : Mat X Z) (hend : iter.«end».val = X.val) :
    arithmetic.ntt.NttMatrix.mul_loop0 iter (nttFwdU A) (nttFwdS s) result
      ⦃ (r : Mat X Z) =>
          ∀ ii kk, ii < X.val → kk < Z.val →
            toRingElem ((r.val[ii]!).val[kk]!)
              = if iter.start.val ≤ ii then
                  ∑ jj ∈ Finset.range Y.val,
                    toRingElem ((A.val[ii]!).val[jj]!) * toRingElem ((s.val[jj]!).val[kk]!)
                else toRingElem ((result.val[ii]!).val[kk]!) ⦄ := by
  unfold arithmetic.ntt.NttMatrix.mul_loop0
  by_cases hlt : iter.start.val < iter.«end».val
  · let* ⟨o, iter1, ho, hstart', hend'⟩ ← core.iter.range.IteratorRange.next_Usize_some_spec
    rw [ho]; simp only
    have hi_lt : iter.start.val < X.val := by omega
    let* ⟨self1, other1, ret1, hs1, ho1, hmid⟩ ←
      ntt_mul_mid_spec A s sBound hfit hA hs hY { start := 0#usize, «end» := Z } result
        iter.start hi_lt rfl
    subst hs1; subst ho1
    have hmid' : ∀ ii kk, ii < X.val → kk < Z.val →
        toRingElem ((ret1.val[ii]!).val[kk]!)
          = if ii = iter.start.val then
              ∑ jj ∈ Finset.range Y.val,
                toRingElem ((A.val[ii]!).val[jj]!) * toRingElem ((s.val[jj]!).val[kk]!)
            else toRingElem ((result.val[ii]!).val[kk]!) := by
      intro ii kk hii hkk
      rw [hmid ii kk hii hkk]
      by_cases h : ii = iter.start.val
      · rw [if_pos h, if_pos (show ii = iter.start.val ∧ _ ≤ kk from ⟨h, Nat.zero_le kk⟩)]
      · rw [if_neg h, if_neg (fun hc : ii = iter.start.val ∧ _ => h hc.1)]
    apply WP.spec_mono (ntt_mul_outer_spec A s sBound hfit hA hs hY iter1 ret1
      (by rw [hend']; exact hend))
    intro r hr ii kk hii hkk
    rw [hr ii kk hii hkk, hstart', hmid' ii kk hii hkk]
    by_cases hle : iter.start.val ≤ ii
    · rw [if_pos hle]
      by_cases he : ii = iter.start.val
      · rw [if_neg (by omega : ¬ iter.start.val + 1 ≤ ii), if_pos he]
      · rw [if_pos (by omega : iter.start.val + 1 ≤ ii)]
    · rw [if_neg hle, if_neg (by omega : ¬ iter.start.val + 1 ≤ ii),
        if_neg (by omega : ¬ ii = iter.start.val)]
  · let* ⟨o, iter1, hnone, _⟩ ← core.iter.range.IteratorRange.next_Usize_none_spec
    rw [hnone]; simp only [WP.spec_ok]
    intro ii kk hii hkk
    rw [if_neg (by omega : ¬ iter.start.val ≤ ii)]
  termination_by iter.«end».val - iter.start.val
  decreasing_by scalar_decr_tac

/-- **The convolution theorem.** Pointwise product in the NTT domain computes the schoolbook
product of the underlying coefficient matrices, in `ℤ[X]/(X²⁵⁶+1)` with `u16` coefficients — the
same postcondition as `matrix_mul_spec` — given the joint magnitude constraint `fitsExactly`.
`hY` discharges the `debug_assert!(Y <= MAX_L)` that bounds the `i64` accumulator. -/
theorem ntt_mul_spec {X Y Z : Usize}
    (A : Mat X Y) (s : Mat Y Z) (sBound : ℤ)
    (hfit : fitsExactly Y.val sBound)
    (hA : UniformBounded A) (hs : SecretBounded s sBound) (hY : Y.val ≤ 4) :
    arithmetic.ntt.NttMatrix.mul (nttFwdU A) (nttFwdS s)
      ⦃ (r : Mat X Z) =>
          ∀ (i : Nat) (_hi : i < X.val) (k : Nat) (_hk : k < Z.val),
            toRingElem ((r.val[i]!).val[k]!)
              = ∑ jj ∈ Finset.range Y.val,
                  toRingElem ((A.val[i]!).val[jj]!)
                    * toRingElem ((s.val[jj]!).val[k]!) ⦄ := by
  unfold arithmetic.ntt.NttMatrix.mul
  have hle : Y ≤ consts.MAX_L := by simp only [consts.MAX_L]; scalar_tac
  rw [show massert (Y ≤ consts.MAX_L) = ok () from by simp only [massert, if_pos hle], bind_tc_ok]
  have hdef : arithmetic.matrix_arith.Matrix.Insts.CoreDefaultDefault.default X Z
      = ok (Array.repeat X (Array.repeat Z (Array.repeat 256#usize 0#u16))) := by
    simp only [arithmetic.matrix_arith.Matrix.Insts.CoreDefaultDefault.default,
      arithmetic.ring_arith.RingElem.Insts.CoreDefaultDefault.default, bind_tc_ok]
  rw [hdef, bind_tc_ok]
  apply WP.spec_mono (ntt_mul_outer_spec A s sBound hfit hA hs hY
    { start := 0#usize, «end» := X } _ rfl)
  intro r hr i hi k hk
  rw [hr i k hi hk,
    if_pos (show ({ start := 0#usize, «end» := X } : core.ops.range.Range Usize).start.val ≤ i
      from Nat.zero_le i)]

/-! ### The three nested loops of `mul_transpose`

Structurally identical to `mul`'s, with the outer index of `self` playing the role of the inner
one: entry `(j,k)` of `Aᵀ·s` accumulates over `ii`, reading `A[ii][j]` against `s[ii][k]`. -/

/-- The innermost loop of `mul_transpose`. -/
theorem ntt_mulT_inner_spec {X Y Z : Usize}
    (iter : core.ops.range.Range Usize)
    (self : arithmetic.ntt.NttMatrix X Y) (other : arithmetic.ntt.NttMatrix X Z)
    (j k : Usize) (acc : Array I64 256#usize)
    (hj : j.val < Y.val) (hk : k.val < Z.val)
    (hstart : iter.start.val ≤ X.val) (hend : iter.«end».val = X.val) (hX : X.val ≤ 4)
    (hself : ∀ ii c, ii < X.val → c < 256 → |aZ ((self.val[ii]!).val[j.val]!) c| ≤ pNtt)
    (hother : ∀ ii c, ii < X.val → c < 256 → |aZ ((other.val[ii]!).val[k.val]!) c| ≤ pNtt)
    (hacc : ∀ c, c < 256 → |accZ acc c| ≤ (iter.start.val : ℤ) * (pNtt * pNtt)) :
    arithmetic.ntt.NttMatrix.mul_transpose_loop0_loop0_loop0 iter self other j k acc
      ⦃ (p : (arithmetic.ntt.NttMatrix X Y) × (arithmetic.ntt.NttMatrix X Z) ×
             (Array I64 256#usize)) =>
          p.1 = self ∧ p.2.1 = other ∧
          (∀ c, c < 256 → accZ p.2.2 c = accZ acc c
            + ∑ ii ∈ Finset.Ico iter.start.val X.val,
                aZ ((self.val[ii]!).val[j.val]!) c * aZ ((other.val[ii]!).val[k.val]!) c) ⦄ := by
  have hpp : pNtt * pNtt = 2533120274592769 := by unfold pNtt; norm_num
  unfold arithmetic.ntt.NttMatrix.mul_transpose_loop0_loop0_loop0
  by_cases hlt : iter.start.val < iter.«end».val
  · let* ⟨o, iter1, ho, hstart', hend'⟩ ← core.iter.range.IteratorRange.next_Usize_some_spec
    rw [ho]; simp only
    have hi_lt : iter.start.val < X.val := by omega
    have hsi : iter.start.val < self.val.length := by have := self.property; scalar_tac
    let* ⟨a, ha⟩ ← Array.index_usize_spec self iter.start hsi
    have ha' : a = self.val[iter.start.val]! := by
      rw [ha, getElem!_pos self.val iter.start.val hsi]
    have haj : j.val < a.val.length := by have := a.property; scalar_tac
    let* ⟨ne, hne⟩ ← Array.index_usize_spec a j haj
    have hne' : ne = (self.val[iter.start.val]!).val[j.val]! := by
      rw [hne, ha', getElem!_pos (self.val[iter.start.val]!).val j.val (by rw [← ha']; exact haj)]
    have hoi : iter.start.val < other.val.length := by have := other.property; scalar_tac
    let* ⟨a1, ha1⟩ ← Array.index_usize_spec other iter.start hoi
    have ha1' : a1 = other.val[iter.start.val]! := by
      rw [ha1, getElem!_pos other.val iter.start.val hoi]
    have ha1k : k.val < a1.val.length := by have := a1.property; scalar_tac
    let* ⟨ne1, hne1⟩ ← Array.index_usize_spec a1 k ha1k
    have hne1' : ne1 = (other.val[iter.start.val]!).val[k.val]! := by
      rw [hne1, ha1',
        getElem!_pos (other.val[iter.start.val]!).val k.val (by rw [← ha1']; exact ha1k)]
    have hstz : (0:ℤ) ≤ (iter.start.val : ℤ) := Int.natCast_nonneg _
    have hstle : ((iter.start.val : ℤ)) ≤ 4 := by exact_mod_cast (by omega : iter.start.val ≤ 4)
    let* ⟨acc1, hacc1v, hacc1b⟩ ← pointwise_mul_acc_spec acc ne ne1
      ((iter.start.val : ℤ) * (pNtt * pNtt))
      (by rw [hne']; exact fun c hc => hself iter.start.val c hi_lt hc)
      (by rw [hne1']; exact fun c hc => hother iter.start.val c hi_lt hc)
      (mul_nonneg hstz (by unfold pNtt; norm_num))
      (by
        rw [hpp] at *
        linarith) hacc
    apply WP.spec_mono (ntt_mulT_inner_spec iter1 self other j k acc1 hj hk
      (by omega) (by rw [hend']; exact hend) hX hself hother
      (fun c hc => by
        refine le_trans (hacc1b c hc) ?_
        rw [hstart']
        push_cast
        linarith))
    rintro ⟨p1, p2, p3⟩ ⟨hp1, hp2, hp3⟩
    simp only at hp1 hp2 hp3
    refine ⟨hp1, hp2, ?_⟩
    intro c hc
    rw [hp3 c hc, hacc1v c hc, hstart', hne', hne1', br_sum_Ico_peel _ hi_lt]
    ring
  · let* ⟨o, iter1, hnone, _⟩ ← core.iter.range.IteratorRange.next_Usize_none_spec
    rw [hnone]; simp only [WP.spec_ok]
    refine ⟨trivial, trivial, fun c hc => ?_⟩
    rw [Finset.Ico_eq_empty (by omega), Finset.sum_empty, add_zero]
  termination_by iter.«end».val - iter.start.val
  decreasing_by scalar_decr_tac

/-- The middle loop of `mul_transpose`. -/
theorem ntt_mulT_mid_spec {X Y Z : Usize} (A : Mat X Y) (s : Mat X Z) (sBound : ℤ)
    (hfit : fitsExactly X.val sBound) (hA : UniformBounded A) (hs : SecretBounded s sBound)
    (hX : X.val ≤ 4)
    (iter : core.ops.range.Range Usize) (result : Mat Y Z) (j : Usize) (hj : j.val < Y.val)
    (hend : iter.«end».val = Z.val) :
    arithmetic.ntt.NttMatrix.mul_transpose_loop0_loop0 iter (nttFwdU A) (nttFwdS s) result j
      ⦃ (p : (arithmetic.ntt.NttMatrix X Y) × (arithmetic.ntt.NttMatrix X Z) × (Mat Y Z)) =>
          p.1 = nttFwdU A ∧ p.2.1 = nttFwdS s ∧
          (∀ jj kk, jj < Y.val → kk < Z.val →
            toRingElem ((p.2.2.val[jj]!).val[kk]!)
              = if jj = j.val ∧ iter.start.val ≤ kk then
                  ∑ ii ∈ Finset.range X.val,
                    toRingElem ((A.val[ii]!).val[jj]!) * toRingElem ((s.val[ii]!).val[kk]!)
                else toRingElem ((result.val[jj]!).val[kk]!)) ⦄ := by
  unfold arithmetic.ntt.NttMatrix.mul_transpose_loop0_loop0
  by_cases hlt : iter.start.val < iter.«end».val
  · let* ⟨o, iter1, ho, hstart', hend'⟩ ← core.iter.range.IteratorRange.next_Usize_some_spec
    rw [ho]; simp only
    have hk_lt : iter.start.val < Z.val := by omega
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
      (fun ii c hii hc => hs ii iter.start.val c hii hk_lt hc) hX acc1 hacc1'
    have hrj : j.val < result.length := by have := result.property; scalar_tac
    let* ⟨a, index_mut_back, ha, hback⟩ ← Array.index_mut_usize_spec result j hrj
    have ha' : a = result.val[j.val]! := by
      rw [ha, getElem!_pos result.val j.val (by have := result.property; scalar_tac)]
    have hak : iter.start.val < a.length := by have := a.property; scalar_tac
    let* ⟨a1, ha1⟩ ← Array.update_spec a iter.start re hak
    have hnew : ∀ x y, ((index_mut_back a1).val[x]!).val[y]!
        = if x = j.val ∧ y = iter.start.val then re else (result.val[x]!).val[y]! := by
      intro x y
      rw [hback, ha1]
      exact arr2_writeback result j iter.start a re hj hk_lt ha' x y
    apply WP.spec_mono (ntt_mulT_mid_spec A s sBound hfit hA hs hX iter1 (index_mut_back a1) j hj
      (by rw [hend']; exact hend))
    rintro ⟨p1, p2, p3⟩ ⟨hp1, hp2, hp3⟩
    simp only at hp1 hp2 hp3
    refine ⟨hp1, hp2, ?_⟩
    intro jj kk hjj hkk
    rw [hp3 jj kk hjj hkk, hstart', hnew jj kk]
    by_cases hc1 : jj = j.val
    · by_cases hkke : kk = iter.start.val
      · rw [if_neg (show ¬ (jj = j.val ∧ iter.start.val + 1 ≤ kk) from by omega),
          if_pos (show jj = j.val ∧ kk = iter.start.val from ⟨hc1, hkke⟩),
          if_pos (show jj = j.val ∧ iter.start.val ≤ kk from ⟨hc1, by omega⟩)]
        subst hc1; subst hkke
        exact hre
      · by_cases hle : iter.start.val ≤ kk
        · rw [if_pos (show jj = j.val ∧ iter.start.val + 1 ≤ kk from ⟨hc1, by omega⟩),
            if_pos (show jj = j.val ∧ iter.start.val ≤ kk from ⟨hc1, hle⟩)]
        · rw [if_neg (show ¬ (jj = j.val ∧ iter.start.val + 1 ≤ kk) from by omega),
            if_neg (show ¬ (jj = j.val ∧ kk = iter.start.val) from by omega),
            if_neg (show ¬ (jj = j.val ∧ iter.start.val ≤ kk) from by omega)]
    · rw [if_neg (show ¬ (jj = j.val ∧ iter.start.val + 1 ≤ kk) from fun h => hc1 h.1),
        if_neg (show ¬ (jj = j.val ∧ kk = iter.start.val) from fun h => hc1 h.1),
        if_neg (show ¬ (jj = j.val ∧ iter.start.val ≤ kk) from fun h => hc1 h.1)]
  · let* ⟨o, iter1, hnone, _⟩ ← core.iter.range.IteratorRange.next_Usize_none_spec
    rw [hnone]; simp only [WP.spec_ok]
    refine ⟨trivial, trivial, fun jj kk hjj hkk => ?_⟩
    rw [if_neg (by omega : ¬ (jj = j.val ∧ iter.start.val ≤ kk))]
  termination_by iter.«end».val - iter.start.val
  decreasing_by scalar_decr_tac

/-- The outer loop of `mul_transpose`. -/
theorem ntt_mulT_outer_spec {X Y Z : Usize} (A : Mat X Y) (s : Mat X Z) (sBound : ℤ)
    (hfit : fitsExactly X.val sBound) (hA : UniformBounded A) (hs : SecretBounded s sBound)
    (hX : X.val ≤ 4)
    (iter : core.ops.range.Range Usize) (result : Mat Y Z) (hend : iter.«end».val = Y.val) :
    arithmetic.ntt.NttMatrix.mul_transpose_loop0 iter (nttFwdU A) (nttFwdS s) result
      ⦃ (r : Mat Y Z) =>
          ∀ jj kk, jj < Y.val → kk < Z.val →
            toRingElem ((r.val[jj]!).val[kk]!)
              = if iter.start.val ≤ jj then
                  ∑ ii ∈ Finset.range X.val,
                    toRingElem ((A.val[ii]!).val[jj]!) * toRingElem ((s.val[ii]!).val[kk]!)
                else toRingElem ((result.val[jj]!).val[kk]!) ⦄ := by
  unfold arithmetic.ntt.NttMatrix.mul_transpose_loop0
  by_cases hlt : iter.start.val < iter.«end».val
  · let* ⟨o, iter1, ho, hstart', hend'⟩ ← core.iter.range.IteratorRange.next_Usize_some_spec
    rw [ho]; simp only
    have hj_lt : iter.start.val < Y.val := by omega
    let* ⟨self1, other1, ret1, hs1, ho1, hmid⟩ ←
      ntt_mulT_mid_spec A s sBound hfit hA hs hX { start := 0#usize, «end» := Z } result
        iter.start hj_lt rfl
    subst hs1; subst ho1
    have hmid' : ∀ jj kk, jj < Y.val → kk < Z.val →
        toRingElem ((ret1.val[jj]!).val[kk]!)
          = if jj = iter.start.val then
              ∑ ii ∈ Finset.range X.val,
                toRingElem ((A.val[ii]!).val[jj]!) * toRingElem ((s.val[ii]!).val[kk]!)
            else toRingElem ((result.val[jj]!).val[kk]!) := by
      intro jj kk hjj hkk
      rw [hmid jj kk hjj hkk]
      by_cases h : jj = iter.start.val
      · rw [if_pos h, if_pos (show jj = iter.start.val ∧ _ ≤ kk from ⟨h, Nat.zero_le kk⟩)]
      · rw [if_neg h, if_neg (fun hc : jj = iter.start.val ∧ _ => h hc.1)]
    apply WP.spec_mono (ntt_mulT_outer_spec A s sBound hfit hA hs hX iter1 ret1
      (by rw [hend']; exact hend))
    intro r hr jj kk hjj hkk
    rw [hr jj kk hjj hkk, hstart', hmid' jj kk hjj hkk]
    by_cases hle : iter.start.val ≤ jj
    · rw [if_pos hle]
      by_cases he : jj = iter.start.val
      · rw [if_neg (by omega : ¬ iter.start.val + 1 ≤ jj), if_pos he]
      · rw [if_pos (by omega : iter.start.val + 1 ≤ jj)]
    · rw [if_neg hle, if_neg (by omega : ¬ iter.start.val + 1 ≤ jj),
        if_neg (by omega : ¬ jj = iter.start.val)]
  · let* ⟨o, iter1, hnone, _⟩ ← core.iter.range.IteratorRange.next_Usize_none_spec
    rw [hnone]; simp only [WP.spec_ok]
    intro jj kk hjj hkk
    rw [if_neg (by omega : ¬ iter.start.val ≤ jj)]
  termination_by iter.«end».val - iter.start.val
  decreasing_by scalar_decr_tac

/-- **The convolution theorem, transposed.** `mul_transpose` in the NTT domain computes the
schoolbook product `Aᵀ·s` of the underlying coefficient matrices, matching
`matrix_mul_transpose_spec`.  `hX` discharges the `debug_assert!(X <= MAX_L)`. -/
theorem ntt_mul_transpose_spec {X Y Z : Usize}
    (A : Mat X Y) (s : Mat X Z) (sBound : ℤ)
    (hfit : fitsExactly X.val sBound)
    (hA : UniformBounded A) (hs : SecretBounded s sBound) (hX : X.val ≤ 4) :
    arithmetic.ntt.NttMatrix.mul_transpose (nttFwdU A) (nttFwdS s)
      ⦃ (r : Mat Y Z) =>
          ∀ (j : Nat) (_hj : j < Y.val) (k : Nat) (_hk : k < Z.val),
            toRingElem ((r.val[j]!).val[k]!)
              = ∑ ii ∈ Finset.range X.val,
                  toRingElem ((A.val[ii]!).val[j]!)
                    * toRingElem ((s.val[ii]!).val[k]!) ⦄ := by
  unfold arithmetic.ntt.NttMatrix.mul_transpose
  have hle : X ≤ consts.MAX_L := by simp only [consts.MAX_L]; scalar_tac
  rw [show massert (X ≤ consts.MAX_L) = ok () from by simp only [massert, if_pos hle], bind_tc_ok]
  have hdef : arithmetic.matrix_arith.Matrix.Insts.CoreDefaultDefault.default Y Z
      = ok (Array.repeat Y (Array.repeat Z (Array.repeat 256#usize 0#u16))) := by
    simp only [arithmetic.matrix_arith.Matrix.Insts.CoreDefaultDefault.default,
      arithmetic.ring_arith.RingElem.Insts.CoreDefaultDefault.default, bind_tc_ok]
  rw [hdef, bind_tc_ok]
  apply WP.spec_mono (ntt_mulT_outer_spec A s sBound hfit hA hs hX
    { start := 0#usize, «end» := Y } _ rfl)
  intro r hr j hj k hk
  rw [hr j k hj hk,
    if_pos (show ({ start := 0#usize, «end» := Y } : core.ops.range.Range Usize).start.val ≤ j
      from Nat.zero_le j)]

end Kopis.Properties
