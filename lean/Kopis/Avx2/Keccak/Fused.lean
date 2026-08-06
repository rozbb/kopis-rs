/-
  # Kopis/Avx2/Keccak/Fused.lean — the fused ρ-π-χ, and the tables `keccak.rs` hard-codes.

  `Round.lean` shows the FIPS round is `RndW = ιW ∘ χW ∘ πW ∘ ρW ∘ θW` on 64-bit words.
  `src/backend/avx2/keccak.rs` does not evaluate those five in sequence.  It computes θ's five
  `d` vectors up front, then for each output row runs `chi_row!`, which reads *by destination*:
  the five sources of one output row are a diagonal of the input, so the row needs the whole of
  `d` and nothing else, and θ's per-lane xor, ρ's rotation, π's permutation and χ all happen in
  registers with no `B` array written and read back.

  Two things have to be checked, and this file is both.

  * **The fusion is a rearrangement, not a different function.**  `tVal` is what `chi_row!`
    calls `t_k`, and `pi_rho_theta` says it is exactly `πW (ρW (θW W))` at that coordinate —
    which makes `RndW_fused` the round as the Rust computes it.
  * **The hard-coded tables are the right ones.**  Each `chi_row!` invocation carries five
    `(source index, rotation)` pairs as literals.  `rustTable` transcribes them and
    `rustTable_eq` proves they are `idx (x + 3y) x` and `ρ.Offsets[x + 3y][x] % 64`.  A typo in
    one of the 50 numbers is otherwise undetectable by reading.

  Note that `ρ.Offsets` holds the *unreduced* triangular numbers (…, 105, 210, 300, …); the
  reduction mod 64 is in `ρ` itself, and so is in `ρW` and in the table below.
-/
import Kopis.Avx2.Keccak.Round

namespace Kopis.Avx2.Keccak

open Spec.SHA3
open scoped Spec.Notations

set_option maxHeartbeats 1000000

/-! ## The fused value

For output row `y` and column `x`, `chi_row!` computes

    t_x = rotl::<r>(xor(src[f], d[f % 5]))

with `f` the source's flat index and `r` its ρ offset.  Since `f = 5x + (x + 3y) mod 5`, the
`f % 5` that selects the `d` entry is the source's own `x` coordinate — which is the column θ's
mixing term is indexed by, so the deferred θ xor lands on the right one. -/

/-- The value `chi_row!` binds to `t_x` when filling output row `y`. -/
def tVal (W : Words) (y x : Fin 5) : BitVec 64 :=
  (W (x + 3 * y) x ^^^ dTerm W (x + 3 * y)).rotateLeft (ρ.Offsets[x + 3 * y][x] % 64)

/-- **The fusion is exactly π ∘ ρ ∘ θ.**  Deferring θ's per-lane xor past ρ and π changes
nothing, because ρ and π act on whole lanes and θ's `d` depends only on the column. -/
theorem pi_rho_theta (W : Words) (x y : Fin 5) : πW (ρW (θW W)) x y = tVal W y x := rfl

/-- What `chi_row!` stores into `dst[5y + x]`, before ι. -/
def chiRow (W : Words) (y x : Fin 5) : BitVec 64 :=
  tVal W y x ^^^ ((~~~tVal W y (x + 1)) &&& tVal W y (x + 2))

/-- **The round as `keccak.rs` computes it.**  One `chi_row!` per output row, then ι on lane 0.
Nothing in the AVX2 code corresponds to `B` or to an intermediate state between ρ, π and χ. -/
theorem RndW_fused (W : Words) (iᵣ : Nat) (x y : Fin 5) :
    RndW W iᵣ x y = if x = 0 ∧ y = 0 then chiRow W y x ^^^ rcWord iᵣ else chiRow W y x := by
  simp only [RndW, ιW, χW, pi_rho_theta, chiRow]

/-! ## The hard-coded tables

The five `chi_row!` invocations in `keccak.rs::round`, transcribed verbatim:

    chi_row!(src, dst, d, 0, 0, 0, 6, 44, 12, 43, 18, 21, 24, 14);
    chi_row!(src, dst, d, 1, 3, 28, 9, 20, 10, 3, 16, 45, 22, 61);
    chi_row!(src, dst, d, 2, 1, 1, 7, 6, 13, 25, 19, 8, 20, 18);
    chi_row!(src, dst, d, 3, 4, 27, 5, 36, 11, 10, 17, 15, 23, 56);
    chi_row!(src, dst, d, 4, 2, 62, 8, 55, 14, 39, 15, 41, 21, 2);

read as `(f, r)` pairs, row `y`, column `x`. -/

def rustTable : Vector (Vector (Nat × Nat) 5) 5 :=
  #v[#v[(0, 0), (6, 44), (12, 43), (18, 21), (24, 14)],
     #v[(3, 28), (9, 20), (10, 3), (16, 45), (22, 61)],
     #v[(1, 1), (7, 6), (13, 25), (19, 8), (20, 18)],
     #v[(4, 27), (5, 36), (11, 10), (17, 15), (23, 56)],
     #v[(2, 62), (8, 55), (14, 39), (15, 41), (21, 2)]]

/-- **Every one of the 50 literals in `keccak.rs::round` is the right one.**  The source index
is the flat index of lane `(x + 3y, x)` and the rotation is that lane's ρ offset.

`decide +kernel` rather than `decide`: `ρ.Offsets` is built by a `for` loop inside `Id.run`,
which the ordinary whnf-based `Decidable` evaluator does not reduce.  Kernel reduction does, and
unlike `native_decide` it adds no axiom: this theorem's footprint is `propext`,
`Classical.choice`, `Quot.sound`, which is what `TrustBase.lean` expects. -/
theorem rustTable_eq (y x : Fin 5) :
    (rustTable[y][x]).1 = idx (x + 3 * y) x ∧
    (rustTable[y][x]).2 = ρ.Offsets[x + 3 * y][x] % 64 := by
  fin_cases y <;> fin_cases x <;> exact ⟨by decide +kernel, by decide +kernel⟩

/-- `tVal`'s rotation amount, rewritten to the transcribed table.  This is the direction proofs
want: `ρ.Offsets` is built by a `for` loop in `Id.run` and does not reduce, while `rustTable` is
a literal vector and computes, so rewriting *to* the table is what lets a rotation amount become
a numeral. -/
theorem rho_offset_eq (y x : Fin 5) :
    ρ.Offsets[x + 3 * y][x] % 64 = (rustTable[y][x]).2 := ((rustTable_eq y x).2).symm

/-- The table's rotations, restated as the thing `tVal` rotates by. -/
theorem tVal_rot (W : Words) (y x : Fin 5) :
    tVal W y x = (W (x + 3 * y) x ^^^ dTerm W (x + 3 * y)).rotateLeft (rustTable[y][x]).2 := by
  rw [tVal, (rustTable_eq y x).2]

/-- The table's source indices are a permutation of all 25 lanes: every input lane is read
exactly once per round, which is π being a bijection. -/
theorem rustTable_srcIdx_nodup :
    (List.finRange 5).flatMap (fun y => (List.finRange 5).map (fun x => (rustTable[y][x]).1))
      |>.Perm (List.range 25) := by
  decide +kernel

end Kopis.Avx2.Keccak
