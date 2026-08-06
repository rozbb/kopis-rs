/-
  # Kopis/Avx2/Keccak/State.lean — the 25-register state as four sponges.

  `keccak.rs` holds the four parallel sponges in `[Vec256; PLEN]`: register `5y + x` carries lane
  `A[x, y]` of all four, one per 64-bit field.  `Round.lean` works with `Words = Fin 5 → Fin 5 →
  BitVec 64`, one per sponge.  This file is the dictionary between them.

  It exists because `keccak::round` reads and writes its 25 registers at *literal* indices
  (`src[0]`, `src[6]`, `dst[5 * y + 1]`, …) — aeneas cannot execute an array access at a computed
  index, so the Rust is written out — and every one of those literals has to be turned back into
  a `(x, y)` coordinate before `RndW` can be applied.  `coordX` / `coordY` / `idx_coord` are that
  turn, and they are `decide`able at each of the 25 literals.
-/
import Kopis.Avx2.Keccak.Fused
import Kopis.Avx2.Keccak.Ops

open Aeneas Aeneas.Std Result
open RustKopisAvx2
open RustKopisAvx2.backend.avx2.intrinsics

namespace Kopis.Avx2.Keccak

set_option maxHeartbeats 1000000

noncomputable section

/-- `Vec256` is inhabited — `setzero_si256` returns one.  This is only so that `getElem!`, which
demands a default, can read the register array at an index whose bound is not in scope; nothing
below depends on *which* vector the default is, and every use is at an in-bounds index. -/
noncomputable instance : Inhabited Vec256 := ⟨Classical.choose setzero_si256_spec⟩

/-- Sponge `l`'s state, read out of the 25 registers: `A[x, y]` is 64-bit lane `l` of register
`5y + x`. -/
def stateWords (st : Std.Array Vec256 25#usize) (l : ℕ) : Words :=
  fun x y => lane64 (st.val[idx x y]!) l

@[simp] theorem stateWords_apply (st : Std.Array Vec256 25#usize) (l : ℕ) (x y : Fin 5) :
    stateWords st l x y = lane64 (st.val[idx x y]!) l := rfl

/-! ## Flat index back to coordinates

`5y + x` with `x, y < 5`, so `x = k % 5` and `y = k / 5`. -/

def coordX (k : ℕ) : Fin 5 := ⟨k % 5, Nat.mod_lt _ (by norm_num)⟩

def coordY (k : ℕ) : Fin 5 := ⟨k / 5 % 5, Nat.mod_lt _ (by norm_num)⟩

/-- The coordinates of a flat register index, for the 25 that name a lane. -/
theorem idx_coord (k : ℕ) (h : k < 25) : idx (coordX k) (coordY k) = k := by
  simp only [idx, coordX, coordY]
  omega

/-- …and `y` really is `k / 5` there, without the wrap. -/
theorem coordY_val (k : ℕ) (h : k < 25) : (coordY k).val = k / 5 := by
  simp only [coordY]; omega

/-- Every register index is a lane's, and the map is injective — `idx` is a bijection
`Fin 5 × Fin 5 ≃ Fin 25`.  This is what makes "write all 25 registers" equal "write every lane". -/
theorem idx_surjective (k : ℕ) (h : k < 25) : ∃ x y : Fin 5, idx x y = k :=
  ⟨coordX k, coordY k, idx_coord k h⟩

/-! ## Reading a register the round has just written

`round` fills `dst` with 25 `Array.update`s at literal indices.  After the last of them the
value at `idx x y` is whatever was written there, which is the shape the postcondition wants. -/

/-- An `Array.update` at a *different* index leaves a register alone. -/
theorem stateWords_update_ne (st : Std.Array Vec256 25#usize) (k : Std.Usize) (v : Vec256)
    (l : ℕ) (x y : Fin 5) (hne : idx x y ≠ k.val) (hk : k.val < 25) :
    stateWords (st.set k v) l x y = stateWords st l x y := by
  have hlen : st.val.length = 25 := st.property
  have hval : (st.set k v).val = st.val.set k.val v := by simp only [Std.Array.set_val_eq]
  simp only [stateWords_apply, hval,
    getElem!_list_set st.val k.val v (idx x y) (by rw [hlen]; exact hk), if_neg hne]

/-- An `Array.update` at *this* index installs the new register. -/
theorem stateWords_update_self (st : Std.Array Vec256 25#usize) (k : Std.Usize) (v : Vec256)
    (l : ℕ) (x y : Fin 5) (heq : idx x y = k.val) (hk : k.val < 25) :
    stateWords (st.set k v) l x y = lane64 v l := by
  have hlen : st.val.length = 25 := st.property
  have hval : (st.set k v).val = st.val.set k.val v := by simp only [Std.Array.set_val_eq]
  simp only [stateWords_apply, hval,
    getElem!_list_set st.val k.val v (idx x y) (by rw [hlen]; exact hk), if_pos heq]

/-! ## Folding the register computation into the spec's vocabulary

The lemmas below are what `round_spec` is assembled from.  Each takes the register-level
equation `step*` leaves in context and returns the *spec-side* name for that register, so the
proof walks up θ → ρπ → χ turning registers into `parity`, `dTerm`, `tVal`, `chiRow` until the
goal is literally `RndW_fused`.  They are stated at *all* lanes rather than at a fixed one,
because `dTerm_of` needs its column parities at every lane, so the chain has to carry `∀ i`
throughout and only specialise at the end.

The direction matters, and getting it backwards is expensive.  Expanding the spec side into raw
xors instead leaves two enormous xor trees that differ only by associativity and commutativity,
and closing *that* needs `simp` to AC-normalise with the permutative `BitVec.xor_comm` — whose
term ordering (`Lean.Meta.acLt`) is superlinear in the size of the atoms being compared.  With
atoms of the form `laneOf 64 (bits (↑src)[k]!) l` a single lane goal exhausts 4M heartbeats after
a minute and a half.  Folding the register side *into* the spec's vocabulary, as here, makes both
sides structurally identical and needs no AC reasoning at all. -/

/-- A register `step*` produced from `Array.index_usize src k` is that lane of the state.  The
numeral `k` the extraction carries unifies with `idx x y` definitionally, so this applies at every
one of the 25 reads without any index arithmetic. -/
theorem lane_read (src : Std.Array Vec256 25#usize) (x y : Fin 5) (a : Vec256)
    (h : a = (src.val)[idx x y]'(by rw [src.property]; exact idx_lt x y)) :
    ∀ i, lane64 a i = stateWords src i x y := by
  intro i; rw [h, stateWords_apply, getElem!_pos]

/-- A register holding `keccak.rs`'s balanced column fold is θ's `C(x)`. -/
theorem parity_of (src : Std.Array Vec256 25#usize) (x : Fin 5) (c a0 a1 a2 a3 a4 : Vec256)
    (e0 : ∀ i, lane64 a0 i = stateWords src i x 0)
    (e1 : ∀ i, lane64 a1 i = stateWords src i x 1)
    (e2 : ∀ i, lane64 a2 i = stateWords src i x 2)
    (e3 : ∀ i, lane64 a3 i = stateWords src i x 3)
    (e4 : ∀ i, lane64 a4 i = stateWords src i x 4)
    (h : bits c = ((bits a0 ^^^ bits a1) ^^^ (bits a2 ^^^ bits a3)) ^^^ bits a4) :
    ∀ i, lane64 c i = parity (stateWords src i) x := by
  intro i
  rw [xor5_lane h i, e0 i, e1 i, e2 i, e3 i, e4 i, parity]

/-- A register holding `xor(c[x-1], rotl::<1,63>(c[x+1]))` is θ's `D(x)`. -/
theorem dTerm_of (src : Std.Array Vec256 25#usize) (x : Fin 5) (cl cr t d : Vec256)
    (hcl : ∀ i, lane64 cl i = parity (stateWords src i) (x - 1))
    (hcr : ∀ i, lane64 cr i = parity (stateWords src i) (x + 1))
    (ht : ∀ i < 4, lane64 t i = (lane64 cr i).rotateLeft 1)
    (hd : bits d = bits cl ^^^ bits t) :
    ∀ i < 4, lane64 d i = dTerm (stateWords src i) x := by
  intro i hi
  rw [dterm_lane i hi ht hd, hcl i, hcr i, dTerm]

/-- A register holding one `chi_row!` temporary is the fused `πW (ρW (θW W))` at that coordinate.
The rotation amount arrives as the transcribed `rustTable` entry, which is what `rotl_spec`
produces; `rho_offset_eq` is what makes that the spec's `ρ.Offsets[…] % 64`. -/
theorem tVal_of (src : Std.Array Vec256 25#usize) (y x : Fin 5) (a d w t : Vec256)
    (ha : ∀ i, lane64 a i = stateWords src i (x + 3 * y) x)
    (hd : ∀ i < 4, lane64 d i = dTerm (stateWords src i) (x + 3 * y))
    (hw : bits w = bits a ^^^ bits d)
    (ht : ∀ i < 4, lane64 t i = (lane64 w i).rotateLeft (rustTable[y][x]).2) :
    ∀ i < 4, lane64 t i = tVal (stateWords src i) y x := by
  intro i hi
  have hwi : lane64 w i = lane64 a i ^^^ lane64 d i := by
    simp only [lane64, hw, lane64_xor_bits]
  rw [ht i hi, hwi, ha i, hd i hi, tVal, rho_offset_eq, stateWords_apply]

/-- A register holding `chi_row!`'s output is `chiRow` — χ applied to the fused temporaries. -/
theorem chiRow_of (src : Std.Array Vec256 25#usize) (y x : Fin 5) (t0 t1 t2 w v : Vec256)
    (h0 : ∀ i < 4, lane64 t0 i = tVal (stateWords src i) y x)
    (h1 : ∀ i < 4, lane64 t1 i = tVal (stateWords src i) y (x + 1))
    (h2 : ∀ i < 4, lane64 t2 i = tVal (stateWords src i) y (x + 2))
    (hw : bits w = (~~~bits t1) &&& bits t2)
    (hv : bits v = bits t0 ^^^ bits w) :
    ∀ i < 4, lane64 v i = chiRow (stateWords src i) y x := by
  intro i hi
  have hwi : lane64 w i = (~~~lane64 t1 i) &&& lane64 t2 i := by
    simp only [lane64, hw, lane64_andnot_bits _ _ i hi]
  have hvi : lane64 v i = lane64 t0 i ^^^ lane64 w i := by
    simp only [lane64, hv, lane64_xor_bits]
  rw [hvi, hwi, h0 i hi, h1 i hi, h2 i hi, chiRow]

/-! ## What `round_spec` will say

With the above, the statement `keccak::round` has to be given is

    theorem round_spec (src dst : Std.Array Vec256 25#usize) (rc : Vec256) (iᵣ : ℕ)
        (hrc : ∀ l < 4, lane64 rc l = rcWord iᵣ) :
        backend.avx2.keccak.round src dst rc
          ⦃ (r : Std.Array Vec256 25#usize) => ∀ l < 4, ∀ x y : Fin 5,
              stateWords r l x y = RndW (stateWords src l) iᵣ x y ⦄

— `dst` does not appear in the postcondition because every one of its 25 registers is
overwritten, which is exactly what `idx_surjective` above certifies.  Take `l` and `hl : l < 4`
as *parameters* rather than writing `∀ l < 4` inside the postcondition: `step*` introduces four
binders either way, and with the `∀` inside, `rename_i` binds the proof where the index is meant.

The proof is 208 intrinsic steps (76 `xor_si256`, 30 `rotl`, 25 `andnot_si256`, 51 reads, 26
writes), and `step*` walks all of them automatically given the three `@[step]` wrappers in
`Ops.lean` — with `set_option maxRecDepth 1000000`, since the default 512 is nowhere near
enough.  That leaves 25 per-lane goals, one per register, after collapsing the 26 `Array.update`s
with `simp +decide only [getElem!_list_set, …]` (`+decide`, not plain `simp only`:
`getElem!_list_set`'s side condition is a bound on the *write* index and plain `simp only` cannot
discharge it, so the lemma silently never fires).

Each of those 25 then closes by folding registers into spec vocabulary with the four `*_of`
lemmas above — `parity_of` for the five column registers, `dTerm_of` for the five mixing terms,
`tVal_of` for the 25 `chi_row!` temporaries, `chiRow_of` for the outputs — ending at
`RndW_fused`, with `round_const_spec` supplying ι's constant on lane `(0,0)`.  No AC
normalisation is involved anywhere; see the note above for why that matters. -/

end

end Kopis.Avx2.Keccak
