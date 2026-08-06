/-
  # Kopis/Avx2/Keccak/Ops.lean — the extracted keccak helpers, against the intrinsic axioms.

  `Bits.lean`, `Round.lean` and `Fused.lean` are pure spec: they say what the round *is* as an
  operation on 64-bit words.  This file is the first that mentions the extraction.  It gives
  each small `keccak.rs` helper its lane-level specification, discharged from
  `Kopis/Avx2/Intrinsics.lean`'s axioms.

  `rotl` is the interesting one.  It is `or(slli_epi64::<L>(v), srli_epi64::<R>(v))` with
  `L + R = 64` asserted, and it is a genuine rotation only because the shifts *saturate to zero*
  at counts of 64 rather than wrapping the count — which is what makes `L = 0` (hence `R = 64`)
  come out as the identity rather than as `v ||| v`.  That behaviour is part of
  `slli_epi64_spec` / `srli_epi64_spec`, is what `BitVec`'s `<<<` and `>>>` do, and is covered by
  the 0..=64 immediate range in `intrinsics_vectors.rs`.
-/
import Kopis.Avx2.Keccak.Fused
import Kopis.Avx2.Keccak.Const

open Aeneas Aeneas.Std Result
open RustKopisAvx2
open RustKopisAvx2.backend.avx2.intrinsics

namespace Kopis.Avx2.Keccak

set_option maxHeartbeats 1000000

noncomputable section

/-! ## A rotation is a shift pair -/

/-- On a 64-bit word, `rotateLeft r` is `(x <<< r) ||| (x >>> (64 - r))`.  At `r = 0` the right
shift is by 64, which `BitVec` (and `vpsrlq`) make zero, so the identity still holds. -/
theorem rotateLeft_eq_or (x : BitVec 64) (r : Nat) (h : r < 64) :
    x.rotateLeft r = (x <<< r) ||| (x >>> (64 - r)) := by
  have hr : r % 64 = r := Nat.mod_eq_of_lt h
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_rotateLeft, BitVec.getLsbD_or, BitVec.getLsbD_ushiftRight,
    BitVec.getLsbD_shiftLeft, hr]
  rcases Nat.lt_or_ge i r with hlt | hge
  · rw [Bool.cond_eq_ite, if_pos (by simpa using hlt)]
    simp only [hlt, decide_true, Bool.not_true, Bool.and_false, Bool.false_and, Bool.false_or]
  · rw [Bool.cond_eq_ite, if_neg (by simpa using hge),
      BitVec.getLsbD_of_ge x (64 - r + i) (by omega)]
    simp only [Bool.or_false, decide_eq_false (by omega : ¬ i < r), Bool.not_false,
      Bool.and_true]

/-! ## `rotl` -/

/-- **`keccak::rotl` rotates each of the four 64-bit lanes left by `L`.**

The `L + R = 64` the Rust `const`-asserts is a hypothesis here rather than something proved: it
is a compile-time assertion in Rust, and the extracted `massert` is discharged from it. -/
theorem rotl_spec (L R : Std.I32) (v : Vec256)
    (hL : 0 ≤ L.val) (hR : 0 ≤ R.val) (hsum : L.val + R.val = 64) (hLlt : L.val < 64) :
    ∃ c, backend.avx2.keccak.rotl L R v = ok c ∧
      ∀ i < 4, lane64 c i = (lane64 v i).rotateLeft L.val.toNat := by
  obtain ⟨s, hs, hsl⟩ := slli_epi64_spec L v hL
  obtain ⟨t, ht, htl⟩ := srli_epi64_spec R v hR
  obtain ⟨c, hc, hcb⟩ := or_si256_spec s t
  refine ⟨c, ?_, ?_⟩
  · -- the extracted body: `L + R`, the assertion, the two shifts, the or
    have hadd : (L + R : Result Std.I32) = ok (64#i32) := by
      have hspec := Std.I32.add_spec (x := L) (y := R) (by scalar_tac) (by scalar_tac)
      cases hcase : (L + R : Result Std.I32) with
      | ok z =>
          rw [hcase] at hspec
          simp only [WP.spec, WP.theta, WP.wp_return] at hspec
          exact congrArg ok (Std.IScalar.eq_of_val_eq (by rw [hspec, hsum]; rfl))
      | fail e => rw [hcase] at hspec; simp [WP.spec, WP.theta] at hspec
      | div => rw [hcase] at hspec; simp [WP.spec, WP.theta] at hspec
    simp only [backend.avx2.keccak.rotl, hadd, bind_tc_ok, massert, hs, ht, hc]
    simp
  · intro i hi
    have hlane : lane64 c i = lane64 s i ||| lane64 t i := by
      simp only [lane64, laneOf, hcb]
      rw [BitVec.extractLsb'_or]
    rw [hlane, hsl i hi, htl i hi,
      rotateLeft_eq_or (lane64 v i) L.val.toNat (by omega),
      show (64 - L.val.toNat) = R.val.toNat by omega]

/-! ## `transpose4x64`

Four registers each holding one word of all four sponges become four registers each holding four
consecutive words of one sponge — the whole of the conversion between the state's word-major
layout and each sponge's byte-major block, and its own inverse.

The instruction sequence is two `vpunpcklqdq`/`vpunpckhqdq` pairs, which transpose within each
128-bit half, then four `vperm2i128`, which move the halves across. -/

/-- A 64-bit lane is a lane of a 128-bit half: lane `l` is lane `l % 2` of half `l / 2`. -/
theorem lane64_split (v : Vec256) (l : ℕ) : lane64 v l = laneOf 64 (half v (l / 2)) (l % 2) :=
  laneOf_laneOf 64 2 (bits v) l (by norm_num)

/-- `vperm2i128`'s half `j`, once the immediate's zeroing bit is known clear and its selector
known.  Both are `decide`able at the two immediates `transpose4x64` uses. -/
private theorem half_perm {IMM : Std.I32} {a b r : Vec256} (j : ℕ) (hj : j < 2) (s : ℕ)
    (hz : ((IMM.bv >>> (4 * j)) &&& 8#32) = 0#32)
    (hs : ((IMM.bv >>> (4 * j)) &&& 3#32).toNat = s)
    (h : ∀ j < 2, half r j =
      if ((IMM.bv >>> (4 * j)) &&& 8#32) ≠ 0#32 then 0#128
      else selectHalf a b (((IMM.bv >>> (4 * j)) &&& 3#32).toNat)) :
    half r j = selectHalf a b s := by
  rw [h j hj, if_neg (by rw [hz]; simp), hs]

/-- The four input registers of a transpose, by lane index. -/
def inReg (a b c d : Vec256) : Nat → Vec256
  | 0 => a
  | 1 => b
  | 2 => c
  | _ => d

/-- **`keccak::transpose4x64` is the 4×4 transpose of 64-bit lanes.**  Output register `k`, lane
`l`, is input register `l`, lane `k`. -/
theorem transpose4x64_spec (a b c d : Vec256) :
    ∃ r0 r1 r2 r3, backend.avx2.keccak.transpose4x64 a b c d = ok (r0, r1, r2, r3) ∧
      ∀ l < 4, lane64 r0 l = lane64 (inReg a b c d l) 0 ∧
               lane64 r1 l = lane64 (inReg a b c d l) 1 ∧
               lane64 r2 l = lane64 (inReg a b c d l) 2 ∧
               lane64 r3 l = lane64 (inReg a b c d l) 3 := by
  obtain ⟨t0, ht0, ht0l⟩ := unpacklo_epi64_spec a b
  obtain ⟨t1, ht1, ht1l⟩ := unpackhi_epi64_spec a b
  obtain ⟨t2, ht2, ht2l⟩ := unpacklo_epi64_spec c d
  obtain ⟨t3, ht3, ht3l⟩ := unpackhi_epi64_spec c d
  obtain ⟨r0, hr0, hr0h⟩ := permute2x128_si256_spec 32#i32 t0 t2
  obtain ⟨r1, hr1, hr1h⟩ := permute2x128_si256_spec 32#i32 t1 t3
  obtain ⟨r2, hr2, hr2h⟩ := permute2x128_si256_spec 49#i32 t0 t2
  obtain ⟨r3, hr3, hr3h⟩ := permute2x128_si256_spec 49#i32 t1 t3
  refine ⟨r0, r1, r2, r3, ?_, ?_⟩
  · simp only [backend.avx2.keccak.transpose4x64, ht0, ht1, ht2, ht3, hr0, hr1, hr2, hr3,
      bind_tc_ok]
  · -- `0x20` takes the low half of each operand, `0x31` the high half.
    have e0 : half r0 0 = half t0 0 := half_perm 0 (by norm_num) 0 (by decide) (by decide) hr0h
    have e1 : half r0 1 = half t2 0 := half_perm 1 (by norm_num) 2 (by decide) (by decide) hr0h
    have f0 : half r1 0 = half t1 0 := half_perm 0 (by norm_num) 0 (by decide) (by decide) hr1h
    have f1 : half r1 1 = half t3 0 := half_perm 1 (by norm_num) 2 (by decide) (by decide) hr1h
    have g0 : half r2 0 = half t0 1 := half_perm 0 (by norm_num) 1 (by decide) (by decide) hr2h
    have g1 : half r2 1 = half t2 1 := half_perm 1 (by norm_num) 3 (by decide) (by decide) hr2h
    have k0 : half r3 0 = half t1 1 := half_perm 0 (by norm_num) 1 (by decide) (by decide) hr3h
    have k1 : half r3 1 = half t3 1 := half_perm 1 (by norm_num) 3 (by decide) (by decide) hr3h
    intro l hl
    have u0 : lane64 t0 0 = lane64 a 0 := by simpa using (ht0l 0 (by norm_num)).1
    have u1 : lane64 t0 1 = lane64 b 0 := by simpa using (ht0l 0 (by norm_num)).2
    have u2 : lane64 t0 2 = lane64 a 2 := by simpa using (ht0l 1 (by norm_num)).1
    have u3 : lane64 t0 3 = lane64 b 2 := by simpa using (ht0l 1 (by norm_num)).2
    have v0 : lane64 t1 0 = lane64 a 1 := by simpa using (ht1l 0 (by norm_num)).1
    have v1 : lane64 t1 1 = lane64 b 1 := by simpa using (ht1l 0 (by norm_num)).2
    have v2 : lane64 t1 2 = lane64 a 3 := by simpa using (ht1l 1 (by norm_num)).1
    have v3 : lane64 t1 3 = lane64 b 3 := by simpa using (ht1l 1 (by norm_num)).2
    have w0 : lane64 t2 0 = lane64 c 0 := by simpa using (ht2l 0 (by norm_num)).1
    have w1 : lane64 t2 1 = lane64 d 0 := by simpa using (ht2l 0 (by norm_num)).2
    have w2 : lane64 t2 2 = lane64 c 2 := by simpa using (ht2l 1 (by norm_num)).1
    have w3 : lane64 t2 3 = lane64 d 2 := by simpa using (ht2l 1 (by norm_num)).2
    have z0 : lane64 t3 0 = lane64 c 1 := by simpa using (ht3l 0 (by norm_num)).1
    have z1 : lane64 t3 1 = lane64 d 1 := by simpa using (ht3l 0 (by norm_num)).2
    have z2 : lane64 t3 2 = lane64 c 3 := by simpa using (ht3l 1 (by norm_num)).1
    have z3 : lane64 t3 3 = lane64 d 3 := by simpa using (ht3l 1 (by norm_num)).2
    -- each output lane, via its half, back to one input lane
    have step : ∀ (r s : Vec256) (jr js : ℕ), half r jr = half s js →
        ∀ m < 2, lane64 r (2 * jr + m) = lane64 s (2 * js + m) := by
      intro r s jr js hj m hm
      rw [lane64_split, lane64_split, show (2 * jr + m) / 2 = jr by omega,
        show (2 * jr + m) % 2 = m by omega, show (2 * js + m) / 2 = js by omega,
        show (2 * js + m) % 2 = m by omega, hj]
    rcases (show l = 0 ∨ l = 1 ∨ l = 2 ∨ l = 3 by omega) with rfl | rfl | rfl | rfl <;>
      refine ⟨?_, ?_, ?_, ?_⟩ <;>
      simp only [inReg,
        step r0 t0 0 0 e0 0 (by norm_num), step r0 t0 0 0 e0 1 (by norm_num),
        step r0 t2 1 0 e1 0 (by norm_num), step r0 t2 1 0 e1 1 (by norm_num),
        step r1 t1 0 0 f0 0 (by norm_num), step r1 t1 0 0 f0 1 (by norm_num),
        step r1 t3 1 0 f1 0 (by norm_num), step r1 t3 1 0 f1 1 (by norm_num),
        step r2 t0 0 1 g0 0 (by norm_num), step r2 t0 0 1 g0 1 (by norm_num),
        step r2 t2 1 1 g1 0 (by norm_num), step r2 t2 1 1 g1 1 (by norm_num),
        step r3 t1 0 1 k0 0 (by norm_num), step r3 t1 0 1 k0 1 (by norm_num),
        step r3 t3 1 1 k1 0 (by norm_num), step r3 t3 1 1 k1 1 (by norm_num),
        u0, u1, u2, u3, v0, v1, v2, v3, w0, w1, w2, w3, z0, z1, z2, z3]

/-! ## `round_const`

`Const.lean` has already checked the mathematically substantive half: the table entry
`keccak::round_const` reaches is FIPS 202's LFSR-derived `ι.RC (12 + round)`.  What is left is
the extracted plumbing — the `massert`, the index arithmetic, the array read, and the
`RC[..] as i64` cast, which is a reinterpretation and so leaves `.bv` alone.

Note that the arithmetic goes through `Std.Usize.sub_spec` / `add_spec` / `Array.index_usize_spec`
rather than by reduction: Aeneas's scalar operations are `if h : … then ok … else fail` whose
`Decidable` instances do not whnf-reduce, so even `24#usize - 12#usize = ok 12#usize` is *not*
provable by `rfl` or `decide`. -/

/-- The twelve `RC` entries the extraction actually reads, against the transcribed table. -/
theorem rc_entry (k : ℕ) (hk : k < 12) :
    ((backend.avx2.keccak.RC.val[12 + k]!).bv) = rustRC[k]'hk := by
  match k, hk with
  | 0, _ => decide +kernel +revert
  | 1, _ => decide +kernel +revert
  | 2, _ => decide +kernel +revert
  | 3, _ => decide +kernel +revert
  | 4, _ => decide +kernel +revert
  | 5, _ => decide +kernel +revert
  | 6, _ => decide +kernel +revert
  | 7, _ => decide +kernel +revert
  | 8, _ => decide +kernel +revert
  | 9, _ => decide +kernel +revert
  | 10, _ => decide +kernel +revert
  | 11, _ => decide +kernel +revert

/-- **`keccak::round_const round` broadcasts the constant of spec round `12 + round` to all four
64-bit lanes.**  The `12 +` is FIPS 202 §3.4: `KECCAK_p[1600, 12]` runs `iᵣ` over the *last*
twelve of Keccak-f's rounds, and `round_const` indexes `RC[24 - ROUNDS + round]` to match. -/
theorem round_const_spec (r : Std.Usize) (hr : r.val < 12) :
    backend.avx2.keccak.round_const r
      ⦃ (c : Vec256) => ∀ i < 4, lane64 c i = rcWord (12 + r.val) ⦄ := by
  unfold backend.avx2.keccak.round_const
  simp only [backend.avx2.keccak.ROUNDS]
  rw [show massert (r < 12#usize) = ok () from by
        simp only [massert, if_pos (show r < 12#usize by scalar_tac)], bind_tc_ok]
  let* ⟨ i, hi, _ ⟩ ← Std.Usize.sub_spec (x := 24#usize) (y := 12#usize) (by scalar_tac)
  have hiv : i.val = 12 := by rw [hi]
  let* ⟨ i1, hi1 ⟩ ← Std.Usize.add_spec (x := i) (y := r) (by rw [hiv]; scalar_tac)
  have hi1v : i1.val = 12 + r.val := by rw [hi1, hiv]
  have hbnd : i1.val < backend.avx2.keccak.RC.val.length := by
    have hlen : backend.avx2.keccak.RC.val.length = 24 := backend.avx2.keccak.RC.property
    rw [hi1v, hlen]; omega
  let* ⟨ i2, hi2 ⟩ ← Array.index_usize_spec backend.avx2.keccak.RC i1 hbnd
  rw [show (lift (UScalar.hcast IScalarTy.I64 i2) : Result Std.I64)
        = ok (UScalar.hcast IScalarTy.I64 i2) from rfl, bind_tc_ok]
  obtain ⟨c, hc, hcl⟩ := set1_epi64x_spec (UScalar.hcast IScalarTy.I64 i2)
  rw [hc]
  simp only [WP.spec_ok]
  intro k hk
  rw [hcl k hk]
  have hbv : Std.I64.bv (UScalar.hcast IScalarTy.I64 i2) = i2.bv :=
    Std.IScalar.bv_mk_apply (BitVec.zeroExtend Std.IScalarTy.I64.numBits i2.bv)
  have hentry : i2.bv = rustRC[r.val]'hr := by
    rw [hi2, ← getElem!_pos backend.avx2.keccak.RC.val i1.val hbnd, hi1v]
    exact rc_entry r.val hr
  rw [hbv, hentry, rcWord_eq_rustRC r.val hr]

/-! ## `load_words`

The one-liner: the four consecutive 64-bit words of a lane's block starting at `word` are the
32 bytes at byte offset `8 * word`. -/

/-- **`keccak::load_words block word` reads the 32 bytes at `8 * word`.** -/
theorem load_words_spec {RATE : Std.Usize} (block : Array Std.U8 RATE) (word : Std.Usize)
    (h : 8 * word.val + 32 ≤ RATE.val) :
    backend.avx2.keccak.load_words block word
      ⦃ (c : Vec256) => ∀ k < 32, lane8 c k = (block.val[8 * word.val + k]!).bv ⦄ := by
  have hmax : RATE.val ≤ Std.Usize.max := by
    have := block.property; scalar_tac
  unfold backend.avx2.keccak.load_words
  have h8 : (8#usize).val = 8 := rfl
  let* ⟨ i, hi ⟩ ← Std.Usize.mul_spec (x := 8#usize) (y := word) (by rw [h8]; omega)
  have hiv : i.val = 8 * word.val := hi
  obtain ⟨c, hc, hcl⟩ := load_u8x32_spec block i (by rw [hiv]; omega)
  rw [hc]
  simp only [WP.spec_ok]
  intro k hk
  rw [hcl k hk, hiv]

/-! ## The shapes `round`'s θ prologue is built from

`keccak::round` computes the five column parities as a balanced xor tree and the five mixing
terms as `xor(c[x-1], rotl::<1,63>(c[x+1]))`, both written out rather than looped (aeneas cannot
read an array at a computed index).  These two lemmas say those register-level shapes compute
`parity` and `dTerm` lane by lane, which is what turns the prologue into `θW`. -/

/-- `vpxor` acts lanewise, at 64 bits. -/
theorem lane64_xor_bits (x y : BitVec 256) (l : ℕ) :
    laneOf 64 (x ^^^ y) l = laneOf 64 x l ^^^ laneOf 64 y l := by
  simp only [laneOf]; rw [BitVec.extractLsb'_xor]

/-- The third AC lemma for `^^^`.  Lean core has `BitVec.xor_assoc` and `BitVec.xor_comm` but no
`xor_left_comm`, and without all three `simp` cannot AC-normalise an xor tree — which is exactly
what matching `round`'s two sides needs. -/
theorem xor_left_comm {w : ℕ} (a b c : BitVec w) : a ^^^ (b ^^^ c) = b ^^^ (a ^^^ c) := by
  rw [← BitVec.xor_assoc, ← BitVec.xor_assoc, BitVec.xor_comm a b]

/-- `vpandn` acts lanewise, at 64 bits — the companion to `lane64_xor_bits`, and what turns
`andnot_si256_step`'s whole-register equation into χ's per-lane one.

Unlike the xor version this needs `l < 4`: complement is the one bitwise operation that is *not*
lanewise for free, because `~~~` on the 256-bit word is zero outside the word while `~~~` on an
extracted lane is not.  Inside the register the two agree, which is all χ ever needs. -/
theorem lane64_andnot_bits (x y : BitVec 256) (l : ℕ) (hl : l < 4) :
    laneOf 64 ((~~~x) &&& y) l = (~~~laneOf 64 x l) &&& laneOf 64 y l := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  have hlt : 64 * l + j < 256 := by omega
  simp only [getLsbD_laneOf, BitVec.getLsbD_and, BitVec.getLsbD_not, hj, hlt, decide_true,
    Bool.true_and]

/-- **The column fold.**  `((a₀ ⊕ a₁) ⊕ (a₂ ⊕ a₃)) ⊕ a₄` — the bracketing `keccak.rs` uses, which
shortens the dependency chain — is the five-way xor of the lanes. -/
theorem xor5_lane {a0 a1 a2 a3 a4 c : Vec256}
    (h : bits c = ((bits a0 ^^^ bits a1) ^^^ (bits a2 ^^^ bits a3)) ^^^ bits a4) (l : ℕ) :
    lane64 c l = lane64 a0 l ^^^ lane64 a1 l ^^^ lane64 a2 l ^^^ lane64 a3 l ^^^ lane64 a4 l := by
  simp only [lane64, h, lane64_xor_bits, BitVec.xor_assoc]

/-- **The mixing term.**  `xor(cₗ, rotl::<1,63>(cᵣ))` is `dTerm`'s `C(x-1) ⊕ rotl 1 (C(x+1))`,
given that the `rotl` has already been discharged by `rotl_spec`. -/
theorem dterm_lane {cl cr t d : Vec256} (l : ℕ) (hl : l < 4)
    (ht : ∀ i < 4, lane64 t i = (lane64 cr i).rotateLeft 1)
    (hd : bits d = bits cl ^^^ bits t) :
    lane64 d l = lane64 cl l ^^^ (lane64 cr l).rotateLeft 1 := by
  simp only [lane64, hd, lane64_xor_bits]
  rw [show laneOf 64 (bits t) l = lane64 t l from rfl, ht l hl]

/-! ## `pad_block` -/

/-- **`keccak::pad_block` builds TurboSHAKE's one-block padded input.**  Bytes `0..32` are the
prefix, `32..32+S` the suffix, byte `32+S` is the domain separator, the last byte of the block is
`0x80`, and everything between is zero — RFC 9861's `pad10*1` when the whole message fits in one
block, which is what `32 + S < RATE` (a `const` assertion in the Rust) guarantees.

`hS` is one stronger than the Rust's assertion: it also separates the domain-separator byte from
the final `0x80` byte.  Kopis satisfies it with room to spare (`S` is 1 or 2, `RATE` is 136 or
168); without it the two writes would land on the same byte and it would hold `DS ||| 0x80`. -/
theorem pad_block_spec (RATE : Std.Usize) (DS : Std.U8) {S : Std.Usize}
    (prefix1 : Std.Array Std.U8 32#usize) (suffix : Std.Array Std.U8 S)
    (hS : 32 + S.val + 1 < RATE.val) :
    backend.avx2.keccak.pad_block RATE DS prefix1 suffix ⦃ (b : Std.Array Std.U8 RATE) => ∀ j < RATE.val,
          b.val[j]! =
            if j < 32 then prefix1.val[j]!
            else if j < 32 + S.val then suffix.val[j - 32]!
            else if j = 32 + S.val then DS
            else if j = RATE.val - 1 then 128#u8
            else 0#u8 ⦄ := by
  have hRmax : RATE.val ≤ Std.Usize.max := by scalar_tac
  have hplen : prefix1.val.length = 32 := prefix1.property
  have hsuflen : suffix.val.length = S.val := suffix.property
  unfold backend.avx2.keccak.pad_block
  have h32 : (32#usize : Std.Usize) ≤ RATE := by rw [Std.UScalar.le_equiv]; simp; omega
  step with Std.Array.index_mut_SliceIndexRangeToUsizeSlice as ⟨s, back, hsval, hslen, hsback⟩
  rw [show (lift (Std.Array.to_slice prefix1) : Result (Slice Std.U8))
        = ok (Std.Array.to_slice prefix1) from rfl, bind_tc_ok]
  have hcp1 : s.length = (Std.Array.to_slice prefix1).length := by
    rw [hslen]; simp only [Slice.length, Std.Array.val_to_slice, hplen]
  step with core.slice.Slice.copy_from_slice.step_spec as ⟨s2, hs2⟩
  let* ⟨ i, hi ⟩ ← Std.Usize.add_spec (x := 32#usize) (y := S) (by scalar_tac)
  have hiv : i.val = 32 + S.val := by rw [hi]
  have hb1len : (back s2).val.length = RATE.val := (back s2).property
  have hlo : (32#usize : Std.Usize) ≤ i := by rw [Std.UScalar.le_equiv, hiv]; simp
  have hhi : i ≤ RATE := by rw [Std.UScalar.le_equiv, hiv]; omega
  step with Std.Array.index_mut_SliceIndexRangeUsizeSlice.step as ⟨s3, imb1, hs3val, hs3len, hs3back⟩
  rw [show (lift (Std.Array.to_slice suffix) : Result (Slice Std.U8))
        = ok (Std.Array.to_slice suffix) from rfl, bind_tc_ok]
  have hcp2 : s3.length = (Std.Array.to_slice suffix).length := by
    rw [hs3len]; simp only [Slice.length, Std.Array.val_to_slice, hsuflen]; omega
  step with core.slice.Slice.copy_from_slice.step_spec as ⟨s5, hs5⟩
  have hb2len : (imb1 s5).val.length = RATE.val := (imb1 s5).property
  have hbnd2 : i.val < (imb1 s5).length := by
    show i.val < (imb1 s5).val.length
    rw [hb2len, hiv]; omega
  let* ⟨ b3, hb3 ⟩ ← Array.update_spec (imb1 s5) i DS hbnd2
  let* ⟨ i1, hi1, _ ⟩ ← Std.Usize.sub_spec (x := RATE) (y := 1#usize) (by scalar_tac)
  have hi1v : i1.val = RATE.val - 1 := by rw [hi1]
  have hb3len : b3.val.length = RATE.val := b3.property
  have hbnd3 : i1.val < b3.length := by
    show i1.val < b3.val.length
    rw [hb3len, hi1v]; omega
  let* ⟨ i2, hi2 ⟩ ← Array.index_usize_spec b3 i1 hbnd3
  -- the byte layout, built up one write at a time
  have hzero : ∀ j, j < RATE.val → (Std.Array.repeat RATE 0#u8).val[j]! = 0#u8 := by
    intro j hj
    rw [Std.Array.repeat_val, getElem!_pos _ j (by rw [List.length_replicate]; exact hj)]
    simp
  have hb1 : (back s2).val = (Std.Array.repeat RATE 0#u8).val.setSlice! 0 prefix1.val := by
    rw [hsback s2, hs2, Std.Array.val_to_slice]
  have hb2 : (imb1 s5).val = (back s2).val.setSlice! 32 suffix.val := by
    rw [hs3back s5, hs5, Std.Array.val_to_slice]
  have hb3v : b3.val = ((imb1 s5).val).set i.val DS := by rw [hb3]; simp only [Std.Array.set_val_eq]
  rw [show (lift (i2 ||| 128#u8) : Result Std.U8) = ok (i2 ||| 128#u8) from rfl, bind_tc_ok]
  have hlenb2 : (imb1 s5).val.length = RATE.val := hb2len
  have hi2zero : i2 = 0#u8 := by
    rw [hi2, ← getElem!_pos b3.val i1.val (by rw [hb3len, hi1v]; omega), hb3v,
      getElem!_list_set (imb1 s5).val i.val DS i1.val (by rw [hlenb2, hiv]; omega),
      if_neg (by rw [hi1v, hiv]; omega), hb2,
      List.getElem!_setSlice!_suffix _ _ _ _ (by rw [hsuflen, hi1v]; omega), hb1,
      List.getElem!_setSlice!_suffix _ _ _ _ (by rw [hplen, hi1v]; omega)]
    exact hzero _ (by rw [hi1v]; omega)
  have hbnd4 : i1.val < b3.length := hbnd3
  let* ⟨ b4, hb4 ⟩ ← Array.update_spec b3 i1 (i2 ||| 128#u8) hbnd4
  rename_i j hj
  have hb4v' : b4.val = b3.val.set i1.val (i2 ||| 128#u8) := by
    rw [hb4]; simp only [Std.Array.set_val_eq]
  rw [hb4v', getElem!_list_set b3.val i1.val (i2 ||| 128#u8) j (by rw [hb3len, hi1v]; omega)]
  by_cases hlast : j = i1.val
  · rw [if_pos hlast, hi2zero, hlast, hi1v, if_neg (by omega), if_neg (by omega),
      if_neg (by omega), if_pos rfl]
    decide
  · rw [if_neg hlast, hb3v,
      getElem!_list_set (imb1 s5).val i.val DS j (by rw [hlenb2, hiv]; omega)]
    by_cases hds : j = i.val
    · rw [if_pos hds, hds, hiv, if_neg (by omega), if_neg (by omega), if_pos rfl]
    · rw [if_neg hds, hb2]
      have hlen1 : (back s2).val.length = RATE.val := hb1len
      have hlenrep : (Std.Array.repeat RATE 0#u8).val.length = RATE.val := by
        rw [Std.Array.repeat_val, List.length_replicate]
      by_cases hpre : j < 32
      · rw [List.getElem!_setSlice!_prefix _ _ _ _ hpre, hb1,
          List.getElem!_setSlice!_middle _ _ _ _
            ⟨(by omega), (by rw [hplen]; omega), (by rw [hlenrep]; omega)⟩,
          if_pos hpre, Nat.sub_zero]
      · by_cases hsuf : j < 32 + S.val
        · rw [List.getElem!_setSlice!_middle _ _ _ _
            ⟨(by omega), (by rw [hsuflen]; omega), (by rw [hlen1]; omega)⟩,
            if_neg hpre, if_pos hsuf]
        · rw [List.getElem!_setSlice!_suffix _ _ _ _ (by rw [hsuflen]; omega), hb1,
            List.getElem!_setSlice!_suffix _ _ _ _ (by rw [hplen]; omega), hzero j hj,
            if_neg hpre, if_neg hsuf, if_neg (by rw [hiv] at hds; omega),
            if_neg (by rw [hi1v] at hlast; omega)]

/-! ## `@[step]` forms, so `step*` can walk `round`

`keccak::round` is 208 intrinsic operations (76 `xor_si256`, 30 `rotl`, 25 `andnot_si256`, 51
reads, 26 writes) written out in a single `do` block, because aeneas cannot execute an array
access at a computed index.  Stepping that by hand would be some 400 lines of `obtain`/`rw`.

It does not have to be: Aeneas's `step*` walks the whole body automatically once each operation
has a `⦃ ⦄`-shaped `@[step]` lemma — the array reads and writes already do, and these three
supply the rest.  `step*` then leaves exactly the algebraic goal, with every intermediate
register in context.  (It needs `set_option maxRecDepth 1000000`; the default 512 is nowhere
near enough for a body this long.)

`rotl_step`'s side conditions are `autoParam`s: every call site in `round` passes literal
rotation halves, so `decide` discharges them without the caller saying anything. -/

@[step] theorem xor_si256_step (a b : Vec256) :
    xor_si256 a b ⦃ (c : Vec256) => bits c = bits a ^^^ bits b ⦄ := by
  obtain ⟨c, hc, hb⟩ := xor_si256_spec a b
  rw [hc]; simp only [WP.spec_ok]; exact hb

@[step] theorem andnot_si256_step (a b : Vec256) :
    andnot_si256 a b ⦃ (c : Vec256) => bits c = (~~~bits a) &&& bits b ⦄ := by
  obtain ⟨c, hc, hb⟩ := andnot_si256_spec a b
  rw [hc]; simp only [WP.spec_ok]; exact hb

@[step] theorem rotl_step (L R : Std.I32) (v : Vec256)
    (hL : 0 ≤ L.val := by decide) (hR : 0 ≤ R.val := by decide)
    (hsum : L.val + R.val = 64 := by decide) (hLlt : L.val < 64 := by decide) :
    backend.avx2.keccak.rotl L R v
      ⦃ (c : Vec256) => ∀ i < 4, lane64 c i = (lane64 v i).rotateLeft L.val.toNat ⦄ := by
  obtain ⟨c, hc, hl⟩ := rotl_spec L R v hL hR hsum hLlt
  rw [hc]; simp only [WP.spec_ok]; exact hl

end

end Kopis.Avx2.Keccak
