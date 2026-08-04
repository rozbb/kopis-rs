/-
  # Kopis/Properties/NttBridge.lean — the NTT multiplier, as a drop-in for the schoolbook one.

  `from_uniform_matrix` / `from_secret_matrix` map a coefficient matrix into the NTT domain and
  `mul` / `mul_transpose` multiply there; this file says the round trip computes the schoolbook
  product.  Everything about the *transform* is in `NttCrt{Zeta,Lane,Level,Block,Elem,Mul}.lean`;
  what is here is the matrix bookkeeping and the convolution theorem for one output entry.

  ## The two constructors are conditional, and not in the same way

  `from_uniform` reads each stored `u16` through an `i16`, so the signed and unsigned readings
  agree only below `2¹⁵`.  That condition is needed to *identify the coefficient function*, not to
  run the transform, so it sits in front of an implication inside the postcondition (`UOK`) and
  the matrix loops never see it.

  `from_secret` is different: it skips the leading Barrett pass, so its input must already be a
  centred residue for both primes — and without that there is no bound to hand `ntt_block`, so the
  walk does not run at all.  That one has to be threaded, and `SecretSmall` is what threads it.
  Every call site already carries `SecretBounded`, so `secretSmall_of_bounded` discharges it.
-/
import Kopis.Properties.Ntt
import Kopis.Properties.NttCrtMul
import Kopis.CrtConv
import Kopis.Bits.Stream

open Aeneas Aeneas.Std Result RustKopisSerial
open scoped BigOperators

namespace Kopis.Properties

open Kopis.Avx2.NttAlg Kopis.CrtConv

set_option maxHeartbeats 1000000
set_option maxRecDepth 200000

/-! ### One transformed element -/

/-- The integer coefficient function of a *uniform* ring element: its stored `u16`s. -/
def uZ (re : arithmetic.ring_arith.RingElem) (c : ℕ) : ℤ := ((re.val[c]!).val : ℕ)

/-- The integer coefficient function of a *secret* ring element: its stored `u16`s read as
`i16`s, which is what `from_secret` computes. -/
def sZ (re : arithmetic.ring_arith.RingElem) (c : ℕ) : ℤ := signedOfU16 (re.val[c]!)

/-- The coefficient function `from_uniform` transforms. -/
def uP (re : arithmetic.ring_arith.RingElem) (c : ℕ) : ℤ := uZ re c
/-- The coefficient function `from_secret` transforms. -/
def sP (re : arithmetic.ring_arith.RingElem) (c : ℕ) : ℤ := sZ re c

theorem uP_eq (re : arithmetic.ring_arith.RingElem) (c : ℕ) : uP re c = uZ re c := rfl
theorem sP_eq (re : arithmetic.ring_arith.RingElem) (c : ℕ) : sP re c = sZ re c := rfl

/-- What `from_uniform` establishes, once its input is known to be a uniform coefficient. -/
def UOK (f : ℕ → ℤ) (ne : arithmetic.ntt.NttElem) : Prop :=
  (∀ c, c < 256 → 0 ≤ f c ∧ f c < 8192) → NttOK f ne

/-- The input condition `from_secret` needs: already centred inside both primes. -/
def SecretSmall {X Y : Usize} (s : Mat X Y) : Prop :=
  ∀ a b c, a < X.val → b < Y.val → c < 256 →
    |signedOfU16 (((s.val[a]!).val[b]!).val[c]!)| ≤ 3840

theorem secretSmall_of_bounded {X Y : Usize} {s : Mat X Y} {b : ℤ}
    (hs : SecretBounded s b) (hb : b ≤ 3840) : SecretSmall s := fun a bb c ha hbb hc => by
  have := hs a bb c ha hbb hc; omega

/-- A uniform matrix entry satisfies `UOK`'s antecedent. -/
theorem uP_small {X Y : Usize} {A : Mat X Y} (hA : UniformBounded A) (a b : ℕ)
    (ha : a < X.val) (hb : b < Y.val) :
    ∀ c, c < 256 → 0 ≤ uP ((A.val[a]!).val[b]!) c ∧ uP ((A.val[a]!).val[b]!) c < 8192 := by
  intro c hc
  have := hA a b c ha hb hc
  unfold uP uZ
  exact ⟨Int.natCast_nonneg _, by omega⟩

theorem from_uniform_elemOK (elem : arithmetic.ring_arith.RingElem) :
    arithmetic.ntt.NttElem.from_uniform elem
      ⦃ (r : arithmetic.ntt.NttElem) => UOK (uP elem) r ⦄ := by
  apply WP.spec_mono (from_uniform_NttOK_signed elem)
  intro r hr hb
  refine NttOK_congr (fun c hc => ?_) hr
  have := hb c hc
  unfold uP uZ at this ⊢
  exact signedOfU16_of_small (by omega)

theorem from_secret_elemOK (elem : arithmetic.ring_arith.RingElem)
    (hs : ∀ c, c < 256 → |sP elem c| ≤ 3840) :
    arithmetic.ntt.NttElem.from_secret elem
      ⦃ (r : arithmetic.ntt.NttElem) => NttOK (sP elem) r ⦄ :=
  from_secret_NttOK elem hs

/-- Both halves of an `NttOK` element are inside 5376, which is the operand bound the accumulate
loop wants. -/
theorem NttOK_lane_bound {g : ℕ → ℤ} {ne : arithmetic.ntt.NttElem} (h : NttOK g ne)
    (t : ℕ) (ht : t < 512) : |eZ ne t| ≤ 5376 := by
  obtain ⟨h1, h2, _, _⟩ := h
  by_cases hlow : t < 256
  · exact le_trans (h1 t hlow) (by norm_num)
  · have := h2 (t - 256) (by omega)
    rwa [show 256 + (t - 256) = t from by omega] at this


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
              UOK (uP ((mat.val[i.val]!).val[b]!)) ((p.2.val[i.val]!).val[b]!))
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
              UOK (uP ((mat.val[a]!).val[b]!)) ((r.val[a]!).val[b]!))
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
            UOK (uP ((A.val[a]!).val[b]!)) ((r.val[a]!).val[b]!) ⦄ := by
  unfold arithmetic.ntt.NttMatrix.from_uniform_matrix
    arithmetic.ntt.NttMatrix.Insts.CoreDefaultDefault.default
    arithmetic.ntt.NttElem.Insts.CoreDefaultDefault.default
  simp only [bind_tc_ok]
  apply WP.spec_mono (from_uniform_matrix_outer_spec { start := 0#usize, «end» := X } A _ rfl)
  rintro r ⟨hr1, _⟩
  exact fun a b ha hb => hr1 a b (Nat.zero_le a) ha hb

/-- The inner matrix loop, secret variant. -/
theorem from_secret_matrix_inner_spec {X Y : Usize}
    (iter : core.ops.range.Range Usize) (mat : Mat X Y) (hsm : SecretSmall mat)
    (ret : arithmetic.ntt.NttMatrix X Y) (i : Usize) (hi : i.val < X.val)
    (hend : iter.«end».val = Y.val) :
    arithmetic.ntt.NttMatrix.from_secret_matrix_loop0_loop0 iter mat ret i
      ⦃ (p : (Mat X Y) × (arithmetic.ntt.NttMatrix X Y)) =>
          p.1 = mat
          ∧ (∀ b, iter.start.val ≤ b → b < Y.val →
              NttOK (sP ((mat.val[i.val]!).val[b]!)) ((p.2.val[i.val]!).val[b]!))
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
    have hsmall_re : ∀ c, c < 256 → |sP re c| ≤ 3840 := by
      intro c hc
      rw [hre']
      exact hsm i.val iter.start.val c hi hj_lt hc
    let* ⟨ne, hne⟩ ← from_secret_elemOK re hsmall_re
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
    apply WP.spec_mono (from_secret_matrix_inner_spec iter1 mat hsm (index_mut_back a2) i hi
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
    (iter : core.ops.range.Range Usize) (mat : Mat X Y) (hsm : SecretSmall mat)
    (ret : arithmetic.ntt.NttMatrix X Y) (hend : iter.«end».val = X.val) :
    arithmetic.ntt.NttMatrix.from_secret_matrix_loop0 iter mat ret
      ⦃ (r : arithmetic.ntt.NttMatrix X Y) =>
          (∀ a b, iter.start.val ≤ a → a < X.val → b < Y.val →
              NttOK (sP ((mat.val[a]!).val[b]!)) ((r.val[a]!).val[b]!))
          ∧ (∀ (a b : ℕ), a < iter.start.val →
              (r.val[a]!).val[b]! = (ret.val[a]!).val[b]!) ⦄ := by
  unfold arithmetic.ntt.NttMatrix.from_secret_matrix_loop0
  by_cases hlt : iter.start.val < iter.«end».val
  · let* ⟨o, iter1, ho, hstart', hend'⟩ ← core.iter.range.IteratorRange.next_Usize_some_spec
    rw [ho]; simp only
    have hi_lt : iter.start.val < X.val := by omega
    let* ⟨mat1, ret1, hm1, hf1, hu1⟩ ←
      from_secret_matrix_inner_spec { start := 0#usize, «end» := Y } mat hsm ret iter.start hi_lt rfl
    subst hm1
    apply WP.spec_mono (from_secret_matrix_outer_spec iter1 mat1 hsm ret1
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
theorem from_secret_matrix_full {X Y : Usize} (s : Mat X Y) (hsm : SecretSmall s) :
    arithmetic.ntt.NttMatrix.from_secret_matrix s
      ⦃ (r : arithmetic.ntt.NttMatrix X Y) =>
          ∀ a b, a < X.val → b < Y.val →
            NttOK (sP ((s.val[a]!).val[b]!)) ((r.val[a]!).val[b]!) ⦄ := by
  unfold arithmetic.ntt.NttMatrix.from_secret_matrix
    arithmetic.ntt.NttMatrix.Insts.CoreDefaultDefault.default
    arithmetic.ntt.NttElem.Insts.CoreDefaultDefault.default
  simp only [bind_tc_ok]
  apply WP.spec_mono (from_secret_matrix_outer_spec { start := 0#usize, «end» := X } s hsm _ rfl)
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

theorem from_secret_matrix_ok {X Y : Usize} (s : Mat X Y) (hsm : SecretSmall s) :
    arithmetic.ntt.NttMatrix.from_secret_matrix s ⦃ fun _ => True ⦄ :=
  WP.spec_mono (from_secret_matrix_full s hsm) (fun _ _ => trivial)

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
theorem from_secret_matrix_spec {X Y : Usize} (s : Mat X Y) (hsm : SecretSmall s) :
    arithmetic.ntt.NttMatrix.from_secret_matrix s
      ⦃ (r : arithmetic.ntt.NttMatrix X Y) => r = nttFwdS s ⦄ :=
  spec_eq_getD (from_secret_matrix_ok s hsm)

/-- **Every entry of `nttFwdU A` is the forward transform of the matching coefficient entry.** -/
theorem nttFwdU_entry {X Y : Usize} (A : Mat X Y) (a b : ℕ) (ha : a < X.val) (hb : b < Y.val) :
    UOK (uP ((A.val[a]!).val[b]!)) (((nttFwdU A).val[a]!).val[b]!) :=
  getD_of_spec (from_uniform_matrix_full A) a b ha hb

/-- **Every entry of `nttFwdS s` is the forward transform of the matching coefficient entry.** -/
theorem nttFwdS_entry {X Y : Usize} (s : Mat X Y) (hsm : SecretSmall s)
    (a b : ℕ) (ha : a < X.val) (hb : b < Y.val) :
    NttOK (sP ((s.val[a]!).val[b]!)) (((nttFwdS s).val[a]!).val[b]!) :=
  getD_of_spec (from_secret_matrix_full s hsm) a b ha hb

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
    convCoeff a b n = Kopis.CrtConv.nconvR (fun i => a[i]!) (fun j => b[j]!) n := by
  unfold convCoeff Kopis.CrtConv.nconvR
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
an `i32` accumulator holding `Σ_j (transform of uⱼ) ∘ (transform of vⱼ)` is turned by
`reduce_invntt_to_ring_elem` into `Σ_j uⱼ · vⱼ` in `ℤ[X]/(X²⁵⁶+1)`.  Stating it over two
arbitrary families is what lets one proof serve both multipliers. -/

/-- The exact integer answer, which `fitsExactly` keeps inside `(-q₁q₂/2, q₁q₂/2)`. -/
def convZ (u v : ℕ → arithmetic.ring_arith.RingElem) (N n : ℕ) : ℤ :=
  ∑ jj ∈ Finset.range N, nconvR (uZ (u jj)) (sZ (v jj)) n

/-- **The convolution theorem, for one entry.** -/
theorem ntt_entry_spec (N : ℕ) (sBound : ℤ)
    (u v : ℕ → arithmetic.ring_arith.RingElem)
    (nu nv : ℕ → arithmetic.ntt.NttElem)
    (hu : ∀ jj, jj < N → NttOK (uP (u jj)) (nu jj))
    (hv : ∀ jj, jj < N → NttOK (sP (v jj)) (nv jj))
    (hfit : fitsExactly N sBound)
    (hub : ∀ jj c, jj < N → c < 256 → ((u jj).val[c]!).val < 2 ^ 13)
    (hvb : ∀ jj c, jj < N → c < 256 → |signedOfU16 ((v jj).val[c]!)| ≤ sBound)
    (hN : N ≤ 4)
    (acc : Array I32 512#usize)
    (hacc : ∀ t, t < 512 → accZ acc t
        = ∑ jj ∈ Finset.range N, eZ (nu jj) t * eZ (nv jj) t) :
    arithmetic.ntt.reduce_invntt_to_ring_elem acc
      ⦃ (r : arithmetic.ring_arith.RingElem) =>
          toRingElem r = ∑ jj ∈ Finset.range N, toRingElem (u jj) * toRingElem (v jj) ⦄ := by
  -- the exactness bound
  have hHb : ∀ n, n < 256 → 2 * |convZ u v N n| < 82593793 := by
    intro n hn
    unfold convZ
    have hterm : ∀ jj ∈ Finset.range N,
        |nconvR (uZ (u jj)) (sZ (v jj)) n| ≤ 256 * 8191 * sBound := by
      intro jj hjj
      have hjj' : jj < N := Finset.mem_range.mp hjj
      refine abs_nconvR_le hn (fun c hc => ?_) (fun c hc => hvb jj c hjj' hc)
      have hb := hub jj c hjj' hc
      unfold uZ
      rw [abs_of_nonneg (Int.natCast_nonneg _)]
      have h13 : (2:ℕ) ^ 13 = 8192 := by norm_num
      omega
    have hsum : |∑ jj ∈ Finset.range N, nconvR (uZ (u jj)) (sZ (v jj)) n|
        ≤ (N : ℤ) * (256 * 8191 * sBound) := by
      refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
      refine le_trans (Finset.sum_le_sum hterm) ?_
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    unfold fitsExactly uniformBound crtQ at hfit
    have : 2 * ((N : ℤ) * 256 * 8191 * sBound) < 82593793 := hfit
    have h2 : 2 * |∑ jj ∈ Finset.range N, nconvR (uZ (u jj)) (sZ (v jj)) n|
        ≤ 2 * ((N : ℤ) * (256 * 8191 * sBound)) := by linarith
    nlinarith [h2]
  -- and the two residue readings
  unfold arithmetic.ntt.reduce_invntt_to_ring_elem
  refine WP.spec_bind (crt_entry_spec N hN acc nu nv (fun jj => uP (u jj)) (fun jj => sP (v jj))
    hu hv hacc (convZ u v N) hHb ?_ ?_) ?_
  · intro c hc
    unfold convZ
    rw [Int.cast_sum]
    refine Finset.sum_congr rfl (fun jj _ => ?_)
    rw [nconvR_intCast]
    rw [← nconv_eq_nconvR _ _ c hc]
    rfl
  · intro c hc
    unfold convZ
    rw [Int.cast_sum]
    refine Finset.sum_congr rfl (fun jj _ => ?_)
    rw [nconvR_intCast]
    rw [← nconv_eq_nconvR _ _ c hc]
    rfl
  · intro r hr
    simp only [WP.spec_ok]
    apply Vector.ext
    intro n hn
    have h216 : ((2 ^ 16 : ℕ) : ℤ) = 65536 := by norm_num
    have hleft : (toRingElem r)[n]'hn = ((convZ u v N n : ℤ) : ZMod (2 ^ 16)) := by
      rw [toRingElem_get r n hn]
      have hcast := (ZMod.intCast_eq_intCast_iff' (((r.val[n]!).val : ℕ) : ℤ)
        (convZ u v N n) (2 ^ 16)).mpr
        (by rw [h216, hr n hn]; exact Int.emod_emod_of_dvd _ (dvd_refl _))
      rw [← hcast]
      simp
    rw [hleft, poly_sum_get _ _ n hn]
    unfold convZ
    rw [Int.cast_sum]
    refine Finset.sum_congr rfl (fun jj hjj => ?_)
    rw [nconvR_intCast,
      show ((toRingElem (u jj)) * (toRingElem (v jj)))[n]'hn
          = convCoeff (toRingElem (u jj)) (toRingElem (v jj)) n from mul_get _ _ n hn,
      convCoeff_eq_nconvR _ _ n hn]
    exact nconvR_congr hn (fun c hc => by rw [uZ_cast, toRingElem_get! _ c hc])
      (fun c hc => by rw [sZ_cast, toRingElem_get! _ c hc])

/-! ### The three nested loops of `mul` -/

private theorem br_sum_Ico_peel {M : Type*} [AddCommMonoid M] (f : ℕ → M) {a b : ℕ} (h : a < b) :
    ∑ j ∈ Finset.Ico a b, f j = f a + ∑ j ∈ Finset.Ico (a + 1) b, f j := by
  rw [show a + 1 = a.succ from rfl, Nat.Ico_succ_left_eq_erase_Ico,
    Finset.add_sum_erase _ f (Finset.mem_Ico.mpr ⟨le_refl a, h⟩)]

/-- The innermost loop of `mul`: accumulate the pointwise products over the inner index. -/
theorem ntt_mul_inner_spec {X Y Z : Usize} (iter : core.ops.range.Range Usize)
    (self : arithmetic.ntt.NttMatrix X Y) (other : arithmetic.ntt.NttMatrix Y Z)
    (i k : Usize) (acc : Array I32 512#usize) (B : ℤ) (h0 : 0 ≤ B) (hB : 4 * (B * B) < 2 ^ 31)
    (hi : i.val < X.val) (hk : k.val < Z.val)
    (hstart : iter.start.val ≤ Y.val) (hend : iter.«end».val = Y.val) (hY : Y.val ≤ 4)
    (hself : ∀ j t, j < Y.val → t < 512 →
      |(eZ ((self.val[i.val]!).val[j]!) t)| ≤ B)
    (hother : ∀ j t, j < Y.val → t < 512 →
      |(eZ ((other.val[j]!).val[k.val]!) t)| ≤ B)
    (hacc : ∀ t < 512, |(accZ acc t)| ≤ (iter.start.val : ℤ) * (B * B)) :
    arithmetic.ntt.NttMatrix.mul_loop0_loop0_loop0 iter self other i k acc
      ⦃ (p : (arithmetic.ntt.NttMatrix X Y) × (arithmetic.ntt.NttMatrix Y Z) ×
             (Array I32 512#usize)) =>
          p.1 = self ∧ p.2.1 = other ∧
          (∀ t < 512, (accZ p.2.2 t) = (accZ acc t)
            + ∑ jj ∈ Finset.Ico iter.start.val Y.val,
                (eZ ((self.val[i.val]!).val[jj]!) t)
                  * (eZ ((other.val[jj]!).val[k.val]!) t)) ∧
          (∀ t < 512, |(accZ p.2.2 t)| ≤ (Y.val : ℤ) * (B * B)) ⦄ := by
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
      rw [hne1, ha1',
        getElem!_pos (other.val[iter.start.val]!).val k.val (by rw [← ha1']; exact ha1k)]
    have hstz : (0 : ℤ) ≤ (iter.start.val : ℤ) := Int.natCast_nonneg _
    have hstle : ((iter.start.val : ℤ)) ≤ 3 := by
      exact_mod_cast (by omega : iter.start.val ≤ 3)
    have hBB : (0 : ℤ) ≤ B * B := mul_nonneg h0 h0
    apply WP.spec_bind (pointwise_mul_acc_spec acc ne ne1 B B
      ((iter.start.val : ℤ) * (B * B)) h0 h0 (mul_nonneg hstz hBB)
      (by rw [hne']; exact fun t ht => hself iter.start.val t hj_lt ht)
      (by rw [hne1']; exact fun t ht => hother iter.start.val t hj_lt ht) hacc
      (by nlinarith))
    intro acc1 hacc1
    apply WP.spec_mono (ntt_mul_inner_spec iter1 self other i k acc1 B h0 hB hi hk
      (by omega) (by rw [hend']; exact hend) hY hself hother
      (fun t ht => by
        refine le_trans (hacc1.2 t ht) ?_
        rw [hstart']
        push_cast
        linarith))
    rintro ⟨p1, p2, p3⟩ ⟨hp1, hp2, hp3, hp4⟩
    simp only at hp1 hp2 hp3 hp4
    refine ⟨hp1, hp2, ?_, hp4⟩
    intro t ht
    rw [hp3 t ht, (hacc1.1 t ht), hstart', hne', hne1', br_sum_Ico_peel _ hj_lt]
    ring
  · let* ⟨o, iter1, hnone, _⟩ ← core.iter.range.IteratorRange.next_Usize_none_spec
    rw [hnone]; simp only [WP.spec_ok]
    refine ⟨trivial, trivial, fun t ht => ?_, fun t ht => ?_⟩
    · rw [Finset.Ico_eq_empty (by omega), Finset.sum_empty, add_zero]
    · refine le_trans (hacc t ht) ?_
      have : ((iter.start.val : ℤ)) ≤ (Y.val : ℤ) := by exact_mod_cast (by omega : iter.start.val ≤ Y.val)
      nlinarith [mul_nonneg h0 h0]
termination_by iter.«end».val - iter.start.val
decreasing_by scalar_decr_tac

/-- The middle loop of `mul`: one output ring element per column `k`. -/
theorem ntt_mul_mid_spec {X Y Z : Usize} (A : Mat X Y) (s : Mat Y Z) (sBound : ℤ)
    (hfit : fitsExactly Y.val sBound) (hA : UniformBounded A) (hs : SecretBounded s sBound)
    (hsb : sBound ≤ 3840)
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
    have hzero : ∀ t, t < 512 → accZ arithmetic.ntt.ACC_ZERO t = 0 := by
      intro t ht
      unfold accZ
      rw [show arithmetic.ntt.ACC_ZERO = Array.repeat 512#usize (0#i32) from by
          simp only [arithmetic.ntt.ACC_ZERO],
        Array.repeat_val, getElem!_pos _ t (by rw [List.length_replicate]; exact ht),
        List.getElem_replicate]
      rfl
    have hUe : ∀ j, j < Y.val → NttOK (uP (A.val[i.val]!).val[j]!) (((nttFwdU A).val[i.val]!).val[j]!) :=
      fun j hj => nttFwdU_entry A i.val j hi hj (uP_small hA i.val j hi hj)
    have hSe : ∀ j, j < Y.val → NttOK (sP (s.val[j]!).val[iter.start.val]!) (((nttFwdS s).val[j]!).val[iter.start.val]!) :=
      fun j hj => nttFwdS_entry s (secretSmall_of_bounded hs hsb) j iter.start.val hj hk_lt
    have hselfb : ∀ j t, j < Y.val → t < 512 → |eZ (((nttFwdU A).val[i.val]!).val[j]!) t| ≤ 5376 :=
      fun j t hj ht => NttOK_lane_bound (hUe j hj) t ht
    have hotherb : ∀ j t, j < Y.val → t < 512 → |eZ (((nttFwdS s).val[j]!).val[iter.start.val]!) t| ≤ 5376 :=
      fun j t hj ht => NttOK_lane_bound (hSe j hj) t ht
    let* ⟨self1, other1, acc1, hs1, ho1, hacc1, _⟩ ←
      ntt_mul_inner_spec { start := 0#usize, «end» := Y } (nttFwdU A) (nttFwdS s) i iter.start
        arithmetic.ntt.ACC_ZERO 5376 (by norm_num) (by norm_num) hi hk_lt (by simp) rfl hY
        hselfb hotherb (fun t ht => by rw [hzero t ht]; simp)
    subst hs1; subst ho1
    have hacc1' : ∀ t, t < 512 → accZ acc1 t
        = ∑ jj ∈ Finset.range Y.val,
            eZ (((nttFwdU A).val[i.val]!).val[jj]!) t
              * eZ (((nttFwdS s).val[jj]!).val[iter.start.val]!) t := by
      intro t ht
      rw [hacc1 t ht, hzero t ht, zero_add, ← Finset.range_eq_Ico]
    let* ⟨re, hre⟩ ← ntt_entry_spec Y.val sBound
      (fun jj => (A.val[i.val]!).val[jj]!) (fun jj => (s.val[jj]!).val[iter.start.val]!)
      (fun jj => ((nttFwdU A).val[i.val]!).val[jj]!)
      (fun jj => ((nttFwdS s).val[jj]!).val[iter.start.val]!)
      hUe hSe hfit (fun jj c hjj hc => hA i.val jj c hi hjj hc)
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
    apply WP.spec_mono (ntt_mul_mid_spec A s sBound hfit hA hs hsb hY iter1 (index_mut_back a1) i hi
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
    (hsb : sBound ≤ 3840)
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
      ntt_mul_mid_spec A s sBound hfit hA hs hsb hY { start := 0#usize, «end» := Z } result
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
    apply WP.spec_mono (ntt_mul_outer_spec A s sBound hfit hA hs hsb hY iter1 ret1
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
    (hA : UniformBounded A) (hs : SecretBounded s sBound) (hY : Y.val ≤ 4)
    (hsb : sBound ≤ 3840) :
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
  apply WP.spec_mono (ntt_mul_outer_spec A s sBound hfit hA hs hsb hY
    { start := 0#usize, «end» := X } _ rfl)
  intro r hr i hi k hk
  rw [hr i k hi hk,
    if_pos (show ({ start := 0#usize, «end» := X } : core.ops.range.Range Usize).start.val ≤ i
      from Nat.zero_le i)]

/-! ### The three nested loops of `mul_transpose`

Structurally identical to `mul`'s, with the outer index of `self` playing the role of the inner
one: entry `(j,k)` of `Aᵀ·s` accumulates over `ii`, reading `A[ii][j]` against `s[ii][k]`. -/

/-- The innermost loop of `mul_transpose`. -/
theorem ntt_mulT_inner_spec {X Y Z : Usize} (iter : core.ops.range.Range Usize)
    (self : arithmetic.ntt.NttMatrix X Y) (other : arithmetic.ntt.NttMatrix X Z)
    (j k : Usize) (acc : Array I32 512#usize) (B : ℤ) (h0 : 0 ≤ B) (hB : 4 * (B * B) < 2 ^ 31)
    (hj : j.val < Y.val) (hk : k.val < Z.val)
    (hstart : iter.start.val ≤ X.val) (hend : iter.«end».val = X.val) (hX : X.val ≤ 4)
    (hself : ∀ ii t, ii < X.val → t < 512 →
      |(eZ ((self.val[ii]!).val[j.val]!) t)| ≤ B)
    (hother : ∀ ii t, ii < X.val → t < 512 →
      |(eZ ((other.val[ii]!).val[k.val]!) t)| ≤ B)
    (hacc : ∀ t < 512, |(accZ acc t)| ≤ (iter.start.val : ℤ) * (B * B)) :
    arithmetic.ntt.NttMatrix.mul_transpose_loop0_loop0_loop0 iter self other j k acc
      ⦃ (p : (arithmetic.ntt.NttMatrix X Y) × (arithmetic.ntt.NttMatrix X Z) ×
             (Array I32 512#usize)) =>
          p.1 = self ∧ p.2.1 = other ∧
          (∀ t < 512, (accZ p.2.2 t) = (accZ acc t)
            + ∑ ii ∈ Finset.Ico iter.start.val X.val,
                (eZ ((self.val[ii]!).val[j.val]!) t)
                  * (eZ ((other.val[ii]!).val[k.val]!) t)) ∧
          (∀ t < 512, |(accZ p.2.2 t)| ≤ (X.val : ℤ) * (B * B)) ⦄ := by
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
    have hstz : (0 : ℤ) ≤ (iter.start.val : ℤ) := Int.natCast_nonneg _
    have hstle : ((iter.start.val : ℤ)) ≤ 3 := by
      exact_mod_cast (by omega : iter.start.val ≤ 3)
    have hBB : (0 : ℤ) ≤ B * B := mul_nonneg h0 h0
    apply WP.spec_bind (pointwise_mul_acc_spec acc ne ne1 B B
      ((iter.start.val : ℤ) * (B * B)) h0 h0 (mul_nonneg hstz hBB)
      (by rw [hne']; exact fun t ht => hself iter.start.val t hi_lt ht)
      (by rw [hne1']; exact fun t ht => hother iter.start.val t hi_lt ht) hacc
      (by nlinarith))
    intro acc1 hacc1
    apply WP.spec_mono (ntt_mulT_inner_spec iter1 self other j k acc1 B h0 hB hj hk
      (by omega) (by rw [hend']; exact hend) hX hself hother
      (fun t ht => by
        refine le_trans (hacc1.2 t ht) ?_
        rw [hstart']
        push_cast
        linarith))
    rintro ⟨p1, p2, p3⟩ ⟨hp1, hp2, hp3, hp4⟩
    simp only at hp1 hp2 hp3 hp4
    refine ⟨hp1, hp2, ?_, hp4⟩
    intro t ht
    rw [hp3 t ht, (hacc1.1 t ht), hstart', hne', hne1', br_sum_Ico_peel _ hi_lt]
    ring
  · let* ⟨o, iter1, hnone, _⟩ ← core.iter.range.IteratorRange.next_Usize_none_spec
    rw [hnone]; simp only [WP.spec_ok]
    refine ⟨trivial, trivial, fun t ht => ?_, fun t ht => ?_⟩
    · rw [Finset.Ico_eq_empty (by omega), Finset.sum_empty, add_zero]
    · refine le_trans (hacc t ht) ?_
      have : ((iter.start.val : ℤ)) ≤ (X.val : ℤ) := by
        exact_mod_cast (by omega : iter.start.val ≤ X.val)
      nlinarith [mul_nonneg h0 h0]
termination_by iter.«end».val - iter.start.val
decreasing_by scalar_decr_tac

/-- The middle loop of `mul_transpose`. -/
theorem ntt_mulT_mid_spec {X Y Z : Usize} (A : Mat X Y) (s : Mat X Z) (sBound : ℤ)
    (hfit : fitsExactly X.val sBound) (hA : UniformBounded A) (hs : SecretBounded s sBound)
    (hsb : sBound ≤ 3840)
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
    have hzero : ∀ t, t < 512 → accZ arithmetic.ntt.ACC_ZERO t = 0 := by
      intro t ht
      unfold accZ
      rw [show arithmetic.ntt.ACC_ZERO = Array.repeat 512#usize (0#i32) from by
          simp only [arithmetic.ntt.ACC_ZERO],
        Array.repeat_val, getElem!_pos _ t (by rw [List.length_replicate]; exact ht),
        List.getElem_replicate]
      rfl
    have hUe : ∀ ii, ii < X.val → NttOK (uP (A.val[ii]!).val[j.val]!) (((nttFwdU A).val[ii]!).val[j.val]!) :=
      fun ii hii => nttFwdU_entry A ii j.val hii hj (uP_small hA ii j.val hii hj)
    have hSe : ∀ ii, ii < X.val → NttOK (sP (s.val[ii]!).val[iter.start.val]!) (((nttFwdS s).val[ii]!).val[iter.start.val]!) :=
      fun ii hii => nttFwdS_entry s (secretSmall_of_bounded hs hsb) ii iter.start.val hii hk_lt
    have hselfb : ∀ ii t, ii < X.val → t < 512 → |eZ (((nttFwdU A).val[ii]!).val[j.val]!) t| ≤ 5376 :=
      fun ii t hii ht => NttOK_lane_bound (hUe ii hii) t ht
    have hotherb : ∀ ii t, ii < X.val → t < 512 → |eZ (((nttFwdS s).val[ii]!).val[iter.start.val]!) t| ≤ 5376 :=
      fun ii t hii ht => NttOK_lane_bound (hSe ii hii) t ht
    let* ⟨self1, other1, acc1, hs1, ho1, hacc1, _⟩ ←
      ntt_mulT_inner_spec { start := 0#usize, «end» := X } (nttFwdU A) (nttFwdS s) j iter.start
        arithmetic.ntt.ACC_ZERO 5376 (by norm_num) (by norm_num) hj hk_lt (by simp) rfl hX
        hselfb hotherb (fun t ht => by rw [hzero t ht]; simp)
    subst hs1; subst ho1
    have hacc1' : ∀ t, t < 512 → accZ acc1 t
        = ∑ ii ∈ Finset.range X.val,
            eZ (((nttFwdU A).val[ii]!).val[j.val]!) t
              * eZ (((nttFwdS s).val[ii]!).val[iter.start.val]!) t := by
      intro t ht
      rw [hacc1 t ht, hzero t ht, zero_add, ← Finset.range_eq_Ico]
    let* ⟨re, hre⟩ ← ntt_entry_spec X.val sBound
      (fun ii => (A.val[ii]!).val[j.val]!) (fun ii => (s.val[ii]!).val[iter.start.val]!)
      (fun ii => ((nttFwdU A).val[ii]!).val[j.val]!)
      (fun ii => ((nttFwdS s).val[ii]!).val[iter.start.val]!)
      hUe hSe hfit (fun ii c hii hc => hA ii j.val c hii hj hc)
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
    apply WP.spec_mono (ntt_mulT_mid_spec A s sBound hfit hA hs hsb hX iter1 (index_mut_back a1) j hj
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
    (hsb : sBound ≤ 3840)
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
      ntt_mulT_mid_spec A s sBound hfit hA hs hsb hX { start := 0#usize, «end» := Z } result
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
    apply WP.spec_mono (ntt_mulT_outer_spec A s sBound hfit hA hs hsb hX iter1 ret1
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
    (hA : UniformBounded A) (hs : SecretBounded s sBound) (hX : X.val ≤ 4)
    (hsb : sBound ≤ 3840) :
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
  apply WP.spec_mono (ntt_mulT_outer_spec A s sBound hfit hA hs hsb hX
    { start := 0#usize, «end» := Y } _ rfl)
  intro r hr j hj k hk
  rw [hr j k hj hk,
    if_pos (show ({ start := 0#usize, «end» := Y } : core.ops.range.Range Usize).start.val ≤ j
      from Nat.zero_le j)]

end Kopis.Properties
