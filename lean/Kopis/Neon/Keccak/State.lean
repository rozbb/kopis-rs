/-
  # Kopis/Neon/Keccak/State.lean — the 25-register state as two sponges.

  `keccak.rs` holds the two parallel sponges in `[Vec128; PLEN]`: register `5y + x` carries lane
  `A[x, y]` of both, one per 64-bit field.  `Kopis/Keccak/Round.lean` works with
  `Words = Fin 5 → Fin 5 → BitVec 64`, one per sponge.  This file is the dictionary between them.

  It exists because `keccak::round` reads and writes its 25 registers at *literal* indices —
  aeneas cannot execute an array access at a computed index, so the Rust is written out — and
  every one of those literals has to be turned back into an `(x, y)` coordinate before `RndW` can
  be applied.

  The four `*_of` lemmas differ from AVX2's, because the instructions do: `eor3` folds a column
  three at a time, `rax1` *is* θ's mixing term, `xar` *is* θ's per-lane xor composed with ρ's
  rotation, and `bcax` *is* χ.
-/
import Kopis.Neon.Keccak.Ops

open Aeneas Aeneas.Std Result
open RustKopisNeon
open RustKopisNeon.backend.neon.intrinsics
open Kopis.Bits

namespace Kopis.Neon.Keccak

open Kopis.Keccak
open Spec.SHA3

set_option maxHeartbeats 1000000

noncomputable section

/-- `Vec128` is inhabited — `dup_n_u64` returns one.  This is only so that `getElem!`, which
demands a default, can read the register array at an index whose bound is not in scope; nothing
below depends on *which* vector the default is, and every use is at an in-bounds index.

(An earlier note in the plan said `Vec128` could not be given an `Inhabited` instance.  That was
wrong: `dup_n_u64_spec` produces a witness from a scalar.  The `vAt` / `sAt` accessors elsewhere
in `Kopis/Neon/` predate this and are still fine; they simply are not the only option.) -/
noncomputable instance : Inhabited Vec128 := ⟨Classical.choose (dup_n_u64_spec 0#u64)⟩

/-- Sponge `l`'s state, read out of the 25 registers: `A[x, y]` is 64-bit lane `l` of register
`5y + x`. -/
def stateWords (st : Std.Array Vec128 25#usize) (l : ℕ) : Words :=
  fun x y => lane64 (st.val[idx x y]!) l

@[simp] theorem stateWords_apply (st : Std.Array Vec128 25#usize) (l : ℕ) (x y : Fin 5) :
    stateWords st l x y = lane64 (st.val[idx x y]!) l := rfl

/-! ## Flat index back to coordinates -/

theorem coordY_val (k : ℕ) (h : k < 25) : (coordY k).val = k / 5 := by
  simp only [coordY]; omega

/-- Every register index is a lane's — `idx` is a bijection `Fin 5 × Fin 5 ≃ Fin 25`.  This is
what makes "write all 25 registers" equal "write every lane". -/
theorem idx_surjective (k : ℕ) (h : k < 25) : ∃ x y : Fin 5, idx x y = k :=
  ⟨coordX k, coordY k, idx_coord k h⟩

/-! ## Reading a register the round has just written -/

theorem stateWords_update_ne (st : Std.Array Vec128 25#usize) (k : Std.Usize) (v : Vec128)
    (l : ℕ) (x y : Fin 5) (hne : idx x y ≠ k.val) (hk : k.val < 25) :
    stateWords (st.set k v) l x y = stateWords st l x y := by
  have hlen : st.val.length = 25 := st.property
  have hval : (st.set k v).val = st.val.set k.val v := by simp only [Std.Array.set_val_eq]
  simp only [stateWords_apply, hval,
    getElem!_list_set st.val k.val v (idx x y) (by rw [hlen]; exact hk), if_neg hne]

theorem stateWords_update_self (st : Std.Array Vec128 25#usize) (k : Std.Usize) (v : Vec128)
    (l : ℕ) (x y : Fin 5) (heq : idx x y = k.val) (hk : k.val < 25) :
    stateWords (st.set k v) l x y = lane64 v l := by
  have hlen : st.val.length = 25 := st.property
  have hval : (st.set k v).val = st.val.set k.val v := by simp only [Std.Array.set_val_eq]
  simp only [stateWords_apply, hval,
    getElem!_list_set st.val k.val v (idx x y) (by rw [hlen]; exact hk), if_pos heq]

/-! ## Folding the register computation into the spec's vocabulary

Each lemma takes the register-level equation `step*` leaves in context and returns the
*spec-side* name for that register, so the proof walks θ → ρπ → χ turning registers into
`parity`, `dTerm`, `tVal`, `chiRow` until the goal is literally `RndW_fused`.

The direction matters.  Expanding the spec side into raw xors instead leaves two large xor trees
differing only by associativity and commutativity, and closing *that* needs `simp` to
AC-normalise with the permutative `BitVec.xor_comm`, whose term ordering is superlinear in the
size of the atoms.  Folding the register side *into* the spec's vocabulary needs no AC reasoning
at all. -/

/-- A register `step*` produced from `Array.index_usize src k` is that lane of the state. -/
theorem lane_read (src : Std.Array Vec128 25#usize) (x y : Fin 5) (a : Vec128)
    (h : a = (src.val)[idx x y]'(by rw [src.property]; exact idx_lt x y)) :
    ∀ i, lane64 a i = stateWords src i x y := by
  intro i; rw [h, stateWords_apply, getElem!_pos]

/-- Two `eor3`s fold a column: `eor3(eor3(a₀,a₁,a₂), a₃, a₄)` is θ's `C(x)`. -/
theorem parity_of (src : Std.Array Vec128 25#usize) (x : Fin 5) (a0 a1 a2 a3 a4 t c : Vec128)
    (e0 : ∀ i, lane64 a0 i = stateWords src i x 0)
    (e1 : ∀ i, lane64 a1 i = stateWords src i x 1)
    (e2 : ∀ i, lane64 a2 i = stateWords src i x 2)
    (e3 : ∀ i, lane64 a3 i = stateWords src i x 3)
    (e4 : ∀ i, lane64 a4 i = stateWords src i x 4)
    (ht : ∀ i, lane64 t i = lane64 a0 i ^^^ lane64 a1 i ^^^ lane64 a2 i)
    (hc : ∀ i, lane64 c i = lane64 t i ^^^ lane64 a3 i ^^^ lane64 a4 i) :
    ∀ i, lane64 c i = parity (stateWords src i) x := by
  intro i
  rw [hc i, ht i, e0 i, e1 i, e2 i, e3 i, e4 i, parity]

/-- `rax1(cl, cr)` *is* θ's `D(x)`. -/
theorem dTerm_of (src : Std.Array Vec128 25#usize) (x : Fin 5) (cl cr d : Vec128)
    (hcl : ∀ i, lane64 cl i = parity (stateWords src i) (x - 1))
    (hcr : ∀ i, lane64 cr i = parity (stateWords src i) (x + 1))
    (hd : ∀ i < 2, lane64 d i = lane64 cl i ^^^ (lane64 cr i).rotateLeft 1) :
    ∀ i < 2, lane64 d i = dTerm (stateWords src i) x := by
  intro i hi
  rw [hd i hi, hcl i, hcr i, dTerm]

/-- `xar` with `IMM = (64 − r) % 64` *is* θ's per-lane xor composed with ρ's rotation, so one
instruction produces a `chi_row!` temporary — the fused `πW (ρW (θW W))` at that coordinate. -/
theorem tVal_of (src : Std.Array Vec128 25#usize) (y x : Fin 5) (a d t : Vec128)
    (ha : ∀ i, lane64 a i = stateWords src i (x + 3 * y) x)
    (hd : ∀ i < 2, lane64 d i = dTerm (stateWords src i) (x + 3 * y))
    (ht : ∀ i < 2, lane64 t i
      = (lane64 a i ^^^ lane64 d i).rotateRight ((64 - (rustTable[y][x]).2) % 64))
    (hr : (rustTable[y][x]).2 < 64) :
    ∀ i < 2, lane64 t i = tVal (stateWords src i) y x := by
  intro i hi
  rw [ht i hi, rotateRight_compl _ _ hr, ha i, hd i hi, tVal, rho_offset_eq, stateWords_apply]

/-- `bcax(t₀, t₂, t₁)` *is* χ.  Note the operand order: `bcax a b c = a ^ (b & ~c)`, and χ is
`B[x] ^ (~B[x+1] & B[x+2])`, so the complemented one is the *last* argument. -/
theorem chiRow_of (src : Std.Array Vec128 25#usize) (y x : Fin 5) (t0 t1 t2 v : Vec128)
    (h0 : ∀ i < 2, lane64 t0 i = tVal (stateWords src i) y x)
    (h1 : ∀ i < 2, lane64 t1 i = tVal (stateWords src i) y (x + 1))
    (h2 : ∀ i < 2, lane64 t2 i = tVal (stateWords src i) y (x + 2))
    (hv : ∀ i < 2, lane64 v i = lane64 t0 i ^^^ (lane64 t2 i &&& ~~~lane64 t1 i)) :
    ∀ i < 2, lane64 v i = chiRow (stateWords src i) y x := by
  intro i hi
  rw [hv i hi, h0 i hi, h1 i hi, h2 i hi, chiRow, BitVec.and_comm]

end

end Kopis.Neon.Keccak
