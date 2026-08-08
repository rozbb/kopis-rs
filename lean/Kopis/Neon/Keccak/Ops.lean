/-
  # Kopis/Neon/Keccak/Ops.lean — the extracted keccak helpers, against the intrinsic axioms.

  `Kopis/Keccak/{Bits,Round,Fused}.lean` are pure spec: they say what the Keccak round *is* as an
  operation on 64-bit words.  This file says what the *instructions* do, per 64-bit lane, so the
  two can be joined.

  ## Why this is short

  AVX2 spends 449 lines here because it builds θ, ρ, π and χ out of `vpxor`, `vpandn` and a pair
  of shifts — 208 operations per round.  ARMv8.2's SHA-3 extension gives all four directly:

      eor3(a,b,c) = a ^ b ^ c                    θ's column fold, two at a time
      rax1(a,b)   = a ^ rotl(b, 1)               θ's mixing term
      xar(a,b,#n) = rotr(a ^ b, n)               θ's per-lane xor *and* ρ's rotation
      bcax(a,b,c) = a ^ (b & ~c)                 χ, in one instruction

  so one round is 65 instructions, not 208, and each maps onto a spec-level operation without an
  intermediate.  That is also why `build.rs` insists on `+sha3`: without it the extraction covers
  a different, larger backend.

  **`bcax`'s third operand is the complemented one.**  χ is `B[x] ^ (~B[x+1] & B[x+2])`, so the
  call is `bcax(B[x], B[x+2], B[x+1])` — the last two swapped relative to the formula's reading
  order.  `bcax_lane` below is stated so that getting this wrong cannot typecheck.
-/
import Kopis.Keccak.Fused
import Kopis.Neon.Intrinsics

open Aeneas Aeneas.Std Result
open RustKopisNeon
open RustKopisNeon.backend.neon.intrinsics
open Kopis.Bits

namespace Kopis.Neon.Keccak

set_option maxHeartbeats 1000000

/-! ## The four SHA-3 instructions, per 64-bit lane -/

theorem lane64_xor (x y : BitVec 128) (i : ℕ) :
    laneOf 64 (x ^^^ y) i = laneOf 64 x i ^^^ laneOf 64 y i :=
  laneOf_xor 64 x y i

theorem lane64_and (x y : BitVec 128) (i : ℕ) :
    laneOf 64 (x &&& y) i = laneOf 64 x i &&& laneOf 64 y i :=
  laneOf_and 64 x y i

theorem lane64_not (x : BitVec 128) (i : ℕ) (hi : i < 2) :
    laneOf 64 (~~~x) i = ~~~laneOf 64 x i := by
  ext j hj
  simp only [← BitVec.getLsbD_eq_getElem, BitVec.getLsbD_not, getLsbD_laneOf, hj, decide_true,
    Bool.true_and, BitVec.getLsbD_not]
  have hlt : 64 * i + j < 128 := by omega
  simp [hlt]

/-- `eor3` is the three-way xor, lane by lane. -/
theorem eor3_lane (a b c d : Vec128) (h : bits d = bits a ^^^ bits b ^^^ bits c) (i : ℕ) :
    lane64 d i = lane64 a i ^^^ lane64 b i ^^^ lane64 c i := by
  show laneOf 64 (bits d) i = _
  rw [h, lane64_xor, lane64_xor]

/-- `bcax a b c` is `a ^ (b & ~c)` — the **third** operand is the complemented one. -/
theorem bcax_lane (a b c d : Vec128) (h : bits d = bits a ^^^ (bits b &&& ~~~bits c))
    (i : ℕ) (hi : i < 2) :
    lane64 d i = lane64 a i ^^^ (lane64 b i &&& ~~~lane64 c i) := by
  show laneOf 64 (bits d) i = _
  rw [h, lane64_xor, lane64_and, lane64_not _ i hi]

/-! ## …as `⦃ ⦄` specs, so `step*` can walk a round -/

@[step] theorem eor3_step (a b c : Vec128) :
    eor3 a b c ⦃ (d : Vec128) => ∀ i, lane64 d i
      = lane64 a i ^^^ lane64 b i ^^^ lane64 c i ⦄ := by
  obtain ⟨d, hd, hb⟩ := eor3_spec a b c
  rw [hd]
  exact (WP.spec_ok _).mpr (fun i => eor3_lane a b c d hb i)

@[step] theorem bcax_step (a b c : Vec128) :
    bcax a b c ⦃ (d : Vec128) => ∀ i < 2, lane64 d i
      = lane64 a i ^^^ (lane64 b i &&& ~~~lane64 c i) ⦄ := by
  obtain ⟨d, hd, hb⟩ := bcax_spec a b c
  rw [hd]
  exact (WP.spec_ok _).mpr (fun i hi => bcax_lane a b c d hb i hi)

/-- ι's xor with the round constant is a plain `eor`. -/
@[step] theorem eor_step (a b : Vec128) :
    eor a b ⦃ (c : Vec128) => ∀ i, lane64 c i = lane64 a i ^^^ lane64 b i ⦄ := by
  obtain ⟨c, hc, hb⟩ := eor_spec a b
  rw [hc]
  refine (WP.spec_ok _).mpr (fun i => ?_)
  show laneOf 64 (bits c) i = _
  rw [hb, lane64_xor]

@[step] theorem rax1_step (a b : Vec128) :
    rax1 a b ⦃ (c : Vec128) => ∀ i < 2,
      lane64 c i = lane64 a i ^^^ (lane64 b i).rotateLeft 1 ⦄ := by
  obtain ⟨c, hc, hl⟩ := rax1_spec a b
  rw [hc]
  exact (WP.spec_ok _).mpr hl

@[step] theorem xar_step (IMM : Std.I32) (a b : Vec128) (h : 0 ≤ IMM.val) (h' : IMM.val ≤ 63) :
    xar IMM a b ⦃ (c : Vec128) => ∀ i < 2,
      lane64 c i = (lane64 a i ^^^ lane64 b i).rotateRight IMM.val.toNat ⦄ := by
  obtain ⟨c, hc, hl⟩ := xar_spec IMM a b h h'
  rw [hc]
  exact (WP.spec_ok _).mpr hl


/-! ## `xar` at each immediate the round uses

`step` cannot discharge `xar_step`'s two side conditions, so it never fires on the generic
lemma.  Every call site uses a literal, and there are twenty-five distinct ones, so the cheapest
fix is twenty-five hypothesis-free instances — after which `step*` walks a whole round. -/

@[step] theorem xar_step_0 (a b : Vec128) :
    xar 0#i32 a b ⦃ (c : Vec128) => ∀ i < 2,
      lane64 c i = (lane64 a i ^^^ lane64 b i).rotateRight 0 ⦄ :=
  xar_step 0#i32 a b (by decide) (by decide)

@[step] theorem xar_step_20 (a b : Vec128) :
    xar 20#i32 a b ⦃ (c : Vec128) => ∀ i < 2,
      lane64 c i = (lane64 a i ^^^ lane64 b i).rotateRight 20 ⦄ :=
  xar_step 20#i32 a b (by decide) (by decide)

@[step] theorem xar_step_21 (a b : Vec128) :
    xar 21#i32 a b ⦃ (c : Vec128) => ∀ i < 2,
      lane64 c i = (lane64 a i ^^^ lane64 b i).rotateRight 21 ⦄ :=
  xar_step 21#i32 a b (by decide) (by decide)

@[step] theorem xar_step_43 (a b : Vec128) :
    xar 43#i32 a b ⦃ (c : Vec128) => ∀ i < 2,
      lane64 c i = (lane64 a i ^^^ lane64 b i).rotateRight 43 ⦄ :=
  xar_step 43#i32 a b (by decide) (by decide)

@[step] theorem xar_step_50 (a b : Vec128) :
    xar 50#i32 a b ⦃ (c : Vec128) => ∀ i < 2,
      lane64 c i = (lane64 a i ^^^ lane64 b i).rotateRight 50 ⦄ :=
  xar_step 50#i32 a b (by decide) (by decide)

@[step] theorem xar_step_36 (a b : Vec128) :
    xar 36#i32 a b ⦃ (c : Vec128) => ∀ i < 2,
      lane64 c i = (lane64 a i ^^^ lane64 b i).rotateRight 36 ⦄ :=
  xar_step 36#i32 a b (by decide) (by decide)

@[step] theorem xar_step_44 (a b : Vec128) :
    xar 44#i32 a b ⦃ (c : Vec128) => ∀ i < 2,
      lane64 c i = (lane64 a i ^^^ lane64 b i).rotateRight 44 ⦄ :=
  xar_step 44#i32 a b (by decide) (by decide)

@[step] theorem xar_step_61 (a b : Vec128) :
    xar 61#i32 a b ⦃ (c : Vec128) => ∀ i < 2,
      lane64 c i = (lane64 a i ^^^ lane64 b i).rotateRight 61 ⦄ :=
  xar_step 61#i32 a b (by decide) (by decide)

@[step] theorem xar_step_19 (a b : Vec128) :
    xar 19#i32 a b ⦃ (c : Vec128) => ∀ i < 2,
      lane64 c i = (lane64 a i ^^^ lane64 b i).rotateRight 19 ⦄ :=
  xar_step 19#i32 a b (by decide) (by decide)

@[step] theorem xar_step_3 (a b : Vec128) :
    xar 3#i32 a b ⦃ (c : Vec128) => ∀ i < 2,
      lane64 c i = (lane64 a i ^^^ lane64 b i).rotateRight 3 ⦄ :=
  xar_step 3#i32 a b (by decide) (by decide)

@[step] theorem xar_step_63 (a b : Vec128) :
    xar 63#i32 a b ⦃ (c : Vec128) => ∀ i < 2,
      lane64 c i = (lane64 a i ^^^ lane64 b i).rotateRight 63 ⦄ :=
  xar_step 63#i32 a b (by decide) (by decide)

@[step] theorem xar_step_58 (a b : Vec128) :
    xar 58#i32 a b ⦃ (c : Vec128) => ∀ i < 2,
      lane64 c i = (lane64 a i ^^^ lane64 b i).rotateRight 58 ⦄ :=
  xar_step 58#i32 a b (by decide) (by decide)

@[step] theorem xar_step_39 (a b : Vec128) :
    xar 39#i32 a b ⦃ (c : Vec128) => ∀ i < 2,
      lane64 c i = (lane64 a i ^^^ lane64 b i).rotateRight 39 ⦄ :=
  xar_step 39#i32 a b (by decide) (by decide)

@[step] theorem xar_step_56 (a b : Vec128) :
    xar 56#i32 a b ⦃ (c : Vec128) => ∀ i < 2,
      lane64 c i = (lane64 a i ^^^ lane64 b i).rotateRight 56 ⦄ :=
  xar_step 56#i32 a b (by decide) (by decide)

@[step] theorem xar_step_46 (a b : Vec128) :
    xar 46#i32 a b ⦃ (c : Vec128) => ∀ i < 2,
      lane64 c i = (lane64 a i ^^^ lane64 b i).rotateRight 46 ⦄ :=
  xar_step 46#i32 a b (by decide) (by decide)

@[step] theorem xar_step_37 (a b : Vec128) :
    xar 37#i32 a b ⦃ (c : Vec128) => ∀ i < 2,
      lane64 c i = (lane64 a i ^^^ lane64 b i).rotateRight 37 ⦄ :=
  xar_step 37#i32 a b (by decide) (by decide)

@[step] theorem xar_step_28 (a b : Vec128) :
    xar 28#i32 a b ⦃ (c : Vec128) => ∀ i < 2,
      lane64 c i = (lane64 a i ^^^ lane64 b i).rotateRight 28 ⦄ :=
  xar_step 28#i32 a b (by decide) (by decide)

@[step] theorem xar_step_54 (a b : Vec128) :
    xar 54#i32 a b ⦃ (c : Vec128) => ∀ i < 2,
      lane64 c i = (lane64 a i ^^^ lane64 b i).rotateRight 54 ⦄ :=
  xar_step 54#i32 a b (by decide) (by decide)

@[step] theorem xar_step_49 (a b : Vec128) :
    xar 49#i32 a b ⦃ (c : Vec128) => ∀ i < 2,
      lane64 c i = (lane64 a i ^^^ lane64 b i).rotateRight 49 ⦄ :=
  xar_step 49#i32 a b (by decide) (by decide)

@[step] theorem xar_step_8 (a b : Vec128) :
    xar 8#i32 a b ⦃ (c : Vec128) => ∀ i < 2,
      lane64 c i = (lane64 a i ^^^ lane64 b i).rotateRight 8 ⦄ :=
  xar_step 8#i32 a b (by decide) (by decide)

@[step] theorem xar_step_2 (a b : Vec128) :
    xar 2#i32 a b ⦃ (c : Vec128) => ∀ i < 2,
      lane64 c i = (lane64 a i ^^^ lane64 b i).rotateRight 2 ⦄ :=
  xar_step 2#i32 a b (by decide) (by decide)

@[step] theorem xar_step_9 (a b : Vec128) :
    xar 9#i32 a b ⦃ (c : Vec128) => ∀ i < 2,
      lane64 c i = (lane64 a i ^^^ lane64 b i).rotateRight 9 ⦄ :=
  xar_step 9#i32 a b (by decide) (by decide)

@[step] theorem xar_step_25 (a b : Vec128) :
    xar 25#i32 a b ⦃ (c : Vec128) => ∀ i < 2,
      lane64 c i = (lane64 a i ^^^ lane64 b i).rotateRight 25 ⦄ :=
  xar_step 25#i32 a b (by decide) (by decide)

@[step] theorem xar_step_23 (a b : Vec128) :
    xar 23#i32 a b ⦃ (c : Vec128) => ∀ i < 2,
      lane64 c i = (lane64 a i ^^^ lane64 b i).rotateRight 23 ⦄ :=
  xar_step 23#i32 a b (by decide) (by decide)

@[step] theorem xar_step_62 (a b : Vec128) :
    xar 62#i32 a b ⦃ (c : Vec128) => ∀ i < 2,
      lane64 c i = (lane64 a i ^^^ lane64 b i).rotateRight 62 ⦄ :=
  xar_step 62#i32 a b (by decide) (by decide)

/-! ## A right rotation by `(64 − r) % 64` is a left rotation by `r`

`keccak.rs`'s `theta_rho!` computes ρ's offset as `(64 - r) % 64` and hands it to `xar`, which
rotates *right*.  The `% 64` is what keeps the one entry of ρ with `r = 0` from asking for 64. -/

theorem rotateRight_compl (w : BitVec 64) (r : ℕ) (hr : r < 64) :
    w.rotateRight ((64 - r) % 64) = w.rotateLeft r := by
  rcases Nat.eq_zero_or_pos r with rfl | hpos
  · ext j hj
    simp only [← BitVec.getLsbD_eq_getElem, BitVec.getLsbD_rotateRight,
      BitVec.getLsbD_rotateLeft]
    simp [hj]
  · ext j hj
    simp only [← BitVec.getLsbD_eq_getElem, BitVec.getLsbD_rotateRight,
      BitVec.getLsbD_rotateLeft, Nat.mod_eq_of_lt (show (64 - r) < 64 by omega),
      Nat.mod_eq_of_lt hr,
      show 64 - (64 - r) = r from by omega]

end Kopis.Neon.Keccak
