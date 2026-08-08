import ExtractedRustNeon
import Kopis.Bits.Lanes
/-!
# NEON intrinsics: the assumed semantics

This file is the **entire trusted base** the NEON backend adds to the Kopis proofs. Everything
in `src/backend/neon/` other than `intrinsics.rs` is extracted to Lean by
`../extract_rust_to_lean.sh` and proved; that one module is extracted *opaquely*, which aeneas
emits as the uninterpreted constants

    axiom RustKopisNeon.backend.neon.intrinsics.Vec128 : Type
    axiom RustKopisNeon.backend.neon.intrinsics.add_16 : Vec128 → Vec128 → Result Vec128
    ...

and this file is what gives them meaning. Nothing below is *proved* — each axiom is a claim about
what an instruction does, to be read against the Arm Architecture Reference Manual (DDI 0487,
§C7.2: the `ADD`/`SQDMULH`/`TBL`/`USHL`/… entries and their ASL pseudocode) and against the
one-line wrapper it corresponds to in `src/backend/neon/intrinsics.rs`. **This file is the review
surface.** An axiom that is wrong here makes every NEON theorem worthless, silently.

Each axiom below *is* tested against silicon, which is a weaker thing than a proof and a much
stronger thing than nothing. `Kopis/Neon/Model.lean` gives every operation a computable model and
proves the axiom pins its result down to exactly that model; `make test-neon-model` replays
50 176 input/output pairs recorded on a real core through those models. So an axiom that
misreads the manual — a rotation the wrong way, `bcax`'s complement on the wrong operand — is
caught. What that cannot catch is an axiom whose *statement* is too weak to be wrong: read the
side conditions, not just the equations.

The ground truth is bits: `bits : Vec128 → BitVec 128` is the 128-bit word a vector register
holds, and each axiom fixes the result's bits in terms of the arguments'. Lane views
(`lane16`, `lane32`, …) are *derived* — they are `BitVec.extractLsb'` on that word, not separate
assumptions — so an axiom stated on 16-bit lanes and one stated on 32-bit lanes are talking
about the same object, which is what the transpose and narrowing sequences need.

Each axiom is stated as `∃ c, f args = ok c ∧ P c`: the shape that says "this call succeeds, and
here is what it returns". For the memory accessors the equation is conditional on the bound the
Rust wrapper asserts; outside that bound the wrapper panics, and nothing is claimed.

## One vector type

`src/backend/neon/intrinsics.rs` wraps every AArch64 arrangement — `int16x8_t`, `uint32x4_t`,
`uint64x2_t`, … — in a single `Vec128`, because `vreinterpretq_*` is a no-op at the instruction
level. So there is one `bits` here rather than one per arrangement, and no axiom anywhere says
"the identity". The lane width an operation reads is in its name.

## What is *not* assumed here

* **The CPU probe.** Unlike the AVX2 backend, `backend::neon::cpu` is extracted normally:
  `available()` is `cfg!(target_arch = "aarch64")`, which is a compile-time `true` on the target
  this is extracted for, so it comes out as `def … : Result Bool := ok true` and needs no
  assumption. The dispatch points therefore reduce to their NEON branch rather than needing a
  proof on both, which is a real simplification over `TopLevelTheoremsAvx2`.
* **Any relation between this model and the portable code.** That is what the correspondence
  proofs are for.

## Where the numbers come from

Three conventions are worth stating once, because they are the ones easiest to get wrong and
they recur below.

* **`>>` in ASL is a floor shift**, not truncation toward zero, so `SQDMULH`'s and `SHSUB`'s
  results are written here with `Int.fdiv` rather than `/` — Lean's `Int` division rounds the
  other way for negatives, and every value these two see is signed.
* **`USHL`'s shift amount is the low *byte* of its count lane, read as a signed 8-bit number**
  (`SInt(Elem[operand2, e, esize]<7:0>)`), not the whole lane. A negative count shifts right.
  Counts at or beyond the lane width in either direction shift the lane out entirely, which is
  what `BitVec`'s `<<<` and `>>>` do.
* **`TBL` zeroes on any index ≥ 16**, not merely on a set high bit. This differs from x86's
  `vpshufb`, which masks the index to its own 128-bit half and keys the zeroing off bit 7 — the
  AVX2 sibling of this file states it that way, and the two must not be confused.

## Prior art

The AVX2 sibling (`Kopis/Avx2/Intrinsics.lean`) is the model for the architecture and for the
memory accessors' shape; its arithmetic specifications follow libcrux's
`crates/utils/intrinsics/src/avx2_extract.rs`. libcrux has no NEON-with-FEAT_SHA3 model and no
model of the `TRN`/`XTN`/`SHRN` family, so everything below is written fresh against the Arm ARM.
-/
namespace Kopis.Neon

open Aeneas Std Result

/- The extracted opaque constants. Every unqualified `Vec128`, `add_16`, `load_i16`, … below is
one of them — the aeneas output for `src/backend/neon/intrinsics.rs`, in namespace
`RustKopisNeon.backend.neon.intrinsics`. Nothing else is opened, so anything unqualified and
lower-case is an extracted intrinsic. -/
open RustKopisNeon.backend.neon.intrinsics

/- The bit view below is an axiom, hence noncomputable, and so is everything phrased through
   it. -/
noncomputable section

/-! ## The bit view

`Vec128` is a `#[repr(transparent)]` newtype over `uint8x16_t`, which is exactly a 128-bit word.
`bits` reads that word; injectivity says the word is *all* there is to a register, so two vectors
with the same bits are the same vector. -/

axiom bits : Vec128 → BitVec 128

axiom bits_inj {a b : Vec128} : bits a = bits b → a = b

/- Lane `i` of width `w`, counting from the least significant end — the lane numbering the Arm
manuals use, so `lane16 v 0` is `V.16B[1:0]`.  Defined in `Kopis/Bits/Lanes.lean`, which both
backends share; re-exported here so that this file reads as one self-contained model. -/
export Kopis.Bits (laneOf)

@[reducible] def lane8 (v : Vec128) (i : Nat) : BitVec 8 := laneOf 8 (bits v) i
@[reducible] def lane16 (v : Vec128) (i : Nat) : BitVec 16 := laneOf 16 (bits v) i
@[reducible] def lane32 (v : Vec128) (i : Nat) : BitVec 32 := laneOf 32 (bits v) i
@[reducible] def lane64 (v : Vec128) (i : Nat) : BitVec 64 := laneOf 64 (bits v) i

/-- The width guard `(1..=13).contains(&bits)` terminates and does not fail. `contains` is a
`core` comparison that charon does not lower, so aeneas emits it uninterpreted; this assumes only
that it *returns*, not what it returns — both outcomes are proved. It appears nowhere in the
serial extraction: the guard is part of the vector dispatch. -/
axiom rangeInclusive_contains_ok {Idx U : Type}
    (i1 : core.cmp.PartialOrd Idx Idx) (i2 : core.cmp.PartialOrd Idx U)
    (i3 : core.cmp.PartialOrd U Idx)
    (r : core.ops.range.RangeInclusive Idx) (x : U) :
    ∃ b, RustKopisNeon.core.ops.range.RangeInclusive.contains i1 i2 i3 r x = ok b

/-! ## Saturation and small helpers -/

/-- Signed saturation of an integer into a 16-bit lane, as ASL's `SignedSatQ(·, 16)`. Only
`SQDMULH` needs it, and only when both its operands are −2^15. -/
def satS16 (x : Int) : BitVec 16 :=
  if x < -32768 then 0x8000#16
  else if 32767 < x then 0x7FFF#16
  else BitVec.ofInt 16 x

/-- The population count of a byte. `CNT` is the only operation here that is not expressible with
`BitVec`'s own operators. -/
def popCount8 (x : BitVec 8) : BitVec 8 :=
  ((List.range 8).map (fun j => if x.getLsbD j then (1 : BitVec 8) else 0)).sum

/-- The shift amount `USHL` reads out of one lane of its second operand: the *low byte*, as a
signed 8-bit number. Not the whole lane — a 16-bit count of `0xFF00` is a shift of 0. -/
def shiftAmount {w : Nat} (count : BitVec w) : Int :=
  (BitVec.setWidth 8 count).toInt

/-- One lane of `USHL`: shift left by `s`, or right by `-s` when `s` is negative. `BitVec`'s
shifts give zero past the lane width, which is what the instruction does. -/
def ushlLane {w : Nat} (x : BitVec w) (s : Int) : BitVec w :=
  if 0 ≤ s then x <<< s.toNat else x >>> (-s).toNat

/-! ## Broadcasts and constants -/

/-- `dup.8h` — every 16-bit lane is `a`. -/
axiom dup_n_s16_spec (a : Std.I16) :
    ∃ c, dup_n_s16 a = ok c ∧ ∀ i < 8, lane16 c i = a.bv

/-- `dup.8h` — every 16-bit lane is `a`. Same instruction as `dup_n_s16`; the wrappers differ
only in the Rust type of the scalar. -/
axiom dup_n_u16_spec (a : Std.U16) :
    ∃ c, dup_n_u16 a = ok c ∧ ∀ i < 8, lane16 c i = a.bv

/-- `dup.4s` — every 32-bit lane is `a`. -/
axiom dup_n_s32_spec (a : Std.I32) :
    ∃ c, dup_n_s32 a = ok c ∧ ∀ i < 4, lane32 c i = a.bv

/-- `dup.4s` — every 32-bit lane is `a`. -/
axiom dup_n_u32_spec (a : Std.U32) :
    ∃ c, dup_n_u32 a = ok c ∧ ∀ i < 4, lane32 c i = a.bv

/-- `dup.2d` — both 64-bit lanes are `a`. `keccak::round_const` splats a round constant with it. -/
axiom dup_n_u64_spec (a : Std.U64) :
    ∃ c, dup_n_u64 a = ok c ∧ ∀ i < 2, lane64 c i = a.bv

/-- The vector whose low 64-bit lane is `lo` and whose high one is `hi`. Two `fmov`s and an
`ins`, not one instruction — the only wrapper here that is not, because there is no
single-instruction way to build a vector from two general registers. -/
axiom set_u64x2_spec (lo hi : Std.U64) :
    ∃ c, set_u64x2 lo hi = ok c ∧ lane64 c 0 = lo.bv ∧ lane64 c 1 = hi.bv

/-! ## Bitwise -/

/-- `and.16b` — bitwise, all 128 bits at once. -/
axiom and_spec (a b : Vec128) :
    ∃ c, and a b = ok c ∧ bits c = bits a &&& bits b

/-- `eor.16b` — bitwise, all 128 bits at once. Keccak's ι is this. -/
axiom eor_spec (a b : Vec128) :
    ∃ c, eor a b = ok c ∧ bits c = bits a ^^^ bits b

/-- `cnt.16b` — the population count of each *byte*, in place. Note the arrangement: it counts
per byte, not per 16-bit lane, which is exactly why `sample::popcount_small` is only valid when
each lane's high byte is zero. -/
axiom cnt_u8_spec (a : Vec128) :
    ∃ c, cnt_u8 a = ok c ∧ ∀ i < 16, lane8 c i = popCount8 (lane8 a i)

/-! ## 16-bit lane arithmetic

`add`, `sub` and `mul` wrap rather than saturate, which is what `BitVec`'s `+`, `-` and `*` do,
and which is why they carry no signedness in their names. -/

/-- `add.8h` — 8 independent wrapping 16-bit additions. -/
axiom add_16_spec (a b : Vec128) :
    ∃ c, add_16 a b = ok c ∧ ∀ i < 8, lane16 c i = lane16 a i + lane16 b i

/-- `sub.8h` — 8 independent wrapping 16-bit subtractions. -/
axiom sub_16_spec (a b : Vec128) :
    ∃ c, sub_16 a b = ok c ∧ ∀ i < 8, lane16 c i = lane16 a i - lane16 b i

/-- `mul.8h` — the *low* half of each 16×16 product. Signed and unsigned agree on the low half,
so no sign extension appears here. -/
axiom mul_16_spec (a b : Vec128) :
    ∃ c, mul_16 a b = ok c ∧ ∀ i < 8, lane16 c i = lane16 a i * lane16 b i

/-- `sqdmulh.8h` — the high 16 bits of the *doubled* signed product, with signed saturation.

This is AArch64's stand-in for a plain 16-bit high multiply, which the instruction set does not
have, so it is the one the whole NTT rests on and the one to read most carefully. The ASL is

    product = 2 * SInt(element1) * SInt(element2);
    (element3, sat) = SignedSatQ(product >> 16, 16);

with `>>` a *floor* shift, hence `Int.fdiv`. The saturation can only bite when both operands are
−2^15: then the product is 2^31 and the shift gives 2^15, one past the top of the lane. No ψ,
Barrett multiplier or modulus in this crate is ever −2^15, which is what `intrinsics.rs`'s
comment on the wrapper claims and what a proof using this axiom has to discharge. -/
axiom sqdmulh_s16_spec (a b : Vec128) :
    ∃ c, sqdmulh_s16 a b = ok c ∧ ∀ i < 8,
      lane16 c i =
        satS16 (Int.fdiv (2 * (lane16 a i).toInt * (lane16 b i).toInt) 65536)

/-- `shsub.8h` — halving signed subtraction, `(a − b) >> 1`.

The subtraction is done at 17 bits and the shift is arithmetic and floor, so there is neither
overflow nor saturation: the result is the exact `⌊(a − b)/2⌋`. `ntt::mont_mul` uses it to halve
two `sqdmulh` results in one step rather than shifting each down separately. -/
axiom shsub_s16_spec (a b : Vec128) :
    ∃ c, shsub_s16 a b = ok c ∧ ∀ i < 8,
      lane16 c i = BitVec.ofInt 16 (Int.fdiv ((lane16 a i).toInt - (lane16 b i).toInt) 2)

/-- `sshr.8h #IMM` — arithmetic right shift by an immediate, so lanes fill with their sign bit.

The immediate is an ordinary argument after extraction (aeneas turns the const generic into a
leading parameter), so this quantifies over it, with the `1 ≤ IMM ≤ 16` range the Rust
`static_assert_uimm_bits!` guarantees as a hypothesis. At `IMM = 16` every lane becomes its own
sign, which is both the instruction's behaviour and `BitVec.sshiftRight`'s. -/
axiom sshr_n_s16_spec (IMM : Std.I32) (a : Vec128) (h : 1 ≤ IMM.val) (h' : IMM.val ≤ 16) :
    ∃ c, sshr_n_s16 IMM a = ok c ∧ ∀ i < 8,
      lane16 c i = (lane16 a i).sshiftRight IMM.val.toNat

/-- `ushl.8h` — logical shift by a per-lane *signed* count. See `shiftAmount`: the count is the
low byte of the corresponding lane of `counts`, read as a signed 8-bit number, and a negative one
shifts right. This is how the crate spells a variable right shift, since there is no `ushr` by a
register. -/
axiom ushl_u16_spec (a counts : Vec128) :
    ∃ c, ushl_u16 a counts = ok c ∧ ∀ i < 8,
      lane16 c i = ushlLane (lane16 a i) (shiftAmount (lane16 counts i))

/-! ## 32-bit lane arithmetic -/

/-- `add.4s` — 4 independent wrapping 32-bit additions. -/
axiom add_32_spec (a b : Vec128) :
    ∃ c, add_32 a b = ok c ∧ ∀ i < 4, lane32 c i = lane32 a i + lane32 b i

/-- `sub.4s` — 4 independent wrapping 32-bit subtractions. -/
axiom sub_32_spec (a b : Vec128) :
    ∃ c, sub_32 a b = ok c ∧ ∀ i < 4, lane32 c i = lane32 a i - lane32 b i

/-- `mla.4s` — multiply-accumulate, `a + b·c` per 32-bit lane, wrapping throughout. Note the
operand order: the *first* argument is the accumulator. -/
axiom mla_32_spec (a b c : Vec128) :
    ∃ d, mla_32 a b c = ok d ∧ ∀ i < 4,
      lane32 d i = lane32 a i + lane32 b i * lane32 c i

/-- `cmgt.4s` — signed 32-bit `a > b`, as an all-ones / all-zeros mask per lane. -/
axiom cmgt_s32_spec (a b : Vec128) :
    ∃ c, cmgt_s32 a b = ok c ∧ ∀ i < 4,
      lane32 c i = if BitVec.slt (lane32 b i) (lane32 a i) then BitVec.allOnes 32 else 0#32

/-- `ushl.4s` — as `ushl_u16`, at 32-bit lanes. The count is still the low *byte* of its lane. -/
axiom ushl_u32_spec (a counts : Vec128) :
    ∃ c, ushl_u32 a counts = ok c ∧ ∀ i < 4,
      lane32 c i = ushlLane (lane32 a i) (shiftAmount (lane32 counts i))

/-! ## Widening and narrowing

Each of these pairs an `.4s` form with its `2` variant so that one wrapper covers a whole 128-bit
result; the `low` / `high` in the names is which half of the 16-bit lanes it reads or writes.
Splitting them would need a 64-bit vector type, which exists only between the two halves. -/

/-- `smull.4s` — the signed 16×16→32 products of the *low* four lanes. -/
axiom smull_low_s16_spec (a b : Vec128) :
    ∃ c, smull_low_s16 a b = ok c ∧ ∀ i < 4,
      lane32 c i = (lane16 a i).signExtend 32 * (lane16 b i).signExtend 32

/-- `smull2.4s` — the signed 16×16→32 products of the *high* four lanes. -/
axiom smull_high_s16_spec (a b : Vec128) :
    ∃ c, smull_high_s16 a b = ok c ∧ ∀ i < 4,
      lane32 c i = (lane16 a (4 + i)).signExtend 32 * (lane16 b (4 + i)).signExtend 32

/-- `sxtl.4s` — the *low* four 16-bit lanes, sign-extended to 32 bits. -/
axiom sxtl_low_s16_spec (a : Vec128) :
    ∃ c, sxtl_low_s16 a = ok c ∧ ∀ i < 4, lane32 c i = (lane16 a i).signExtend 32

/-- `sxtl2.4s` — the *high* four 16-bit lanes, sign-extended to 32 bits. -/
axiom sxtl_high_s16_spec (a : Vec128) :
    ∃ c, sxtl_high_s16 a = ok c ∧ ∀ i < 4, lane32 c i = (lane16 a (4 + i)).signExtend 32

/-- `xtn.4h` + `xtn2.8h` — the low 16 bits of each 32-bit lane of `a` then of `b`, in order.

Truncating, not saturating, so no signedness arises. Unlike x86's `vpackusdw` this leaves the
lanes in order, which is why the NEON code has no permute to undo afterwards where the AVX2 code
has a `vpermq`. -/
axiom xtn_pair_32_spec (a b : Vec128) :
    ∃ c, xtn_pair_32 a b = ok c ∧ ∀ i < 4,
      lane16 c i = BitVec.setWidth 16 (lane32 a i) ∧
      lane16 c (4 + i) = BitVec.setWidth 16 (lane32 b i)

/-- `shrn.4h #16` + `shrn2.8h #16` — the *high* 16 bits of each 32-bit lane of `a` then of `b`.

The narrowing discards exactly the bits the shift brought in, so arithmetic and logical shifts
agree here and the result is bits 16..32 of the source lane outright. The count is fixed at 16
because that is the only one the backend uses: a Montgomery reduction with R = 2^16. -/
axiom shrn16_pair_s32_spec (a b : Vec128) :
    ∃ c, shrn16_pair_s32 a b = ok c ∧ ∀ i < 4,
      lane16 c i = BitVec.extractLsb' 16 16 (lane32 a i) ∧
      lane16 c (4 + i) = BitVec.extractLsb' 16 16 (lane32 b i)

/-! ## Permutes

`TRN1` and `TRN2` take the even and odd lanes respectively of both sources and interleave them;
`ntt::transpose8` is three `TRN` stages at widths 16, 32 and 64. There is no 128-bit-half
subtlety here — AArch64 vectors are 128 bits and these act across the whole register, which is
the single biggest difference from the AVX2 model's `unpack` family. -/

/-- `trn1.8h` — the even-indexed 16-bit lanes of `a` and `b`, interleaved. -/
axiom trn1_16_spec (a b : Vec128) :
    ∃ c, trn1_16 a b = ok c ∧ ∀ k < 4,
      lane16 c (2 * k) = lane16 a (2 * k) ∧
      lane16 c (2 * k + 1) = lane16 b (2 * k)

/-- `trn2.8h` — the odd-indexed 16-bit lanes of `a` and `b`, interleaved. -/
axiom trn2_16_spec (a b : Vec128) :
    ∃ c, trn2_16 a b = ok c ∧ ∀ k < 4,
      lane16 c (2 * k) = lane16 a (2 * k + 1) ∧
      lane16 c (2 * k + 1) = lane16 b (2 * k + 1)

/-- `trn1.4s` — the even-indexed 32-bit lanes of `a` and `b`, interleaved. -/
axiom trn1_32_spec (a b : Vec128) :
    ∃ c, trn1_32 a b = ok c ∧ ∀ k < 2,
      lane32 c (2 * k) = lane32 a (2 * k) ∧
      lane32 c (2 * k + 1) = lane32 b (2 * k)

/-- `trn2.4s` — the odd-indexed 32-bit lanes of `a` and `b`, interleaved. -/
axiom trn2_32_spec (a b : Vec128) :
    ∃ c, trn2_32 a b = ok c ∧ ∀ k < 2,
      lane32 c (2 * k) = lane32 a (2 * k + 1) ∧
      lane32 c (2 * k + 1) = lane32 b (2 * k + 1)

/-- `trn1.2d` — the low 64-bit lane of `a`, then that of `b`. -/
axiom trn1_64_spec (a b : Vec128) :
    ∃ c, trn1_64 a b = ok c ∧ lane64 c 0 = lane64 a 0 ∧ lane64 c 1 = lane64 b 0

/-- `trn2.2d` — the high 64-bit lane of `a`, then that of `b`. -/
axiom trn2_64_spec (a b : Vec128) :
    ∃ c, trn2_64 a b = ok c ∧ lane64 c 0 = lane64 a 1 ∧ lane64 c 1 = lane64 b 1

/-- `tbl.16b` — byte `i` of the result is byte `idx[i]` of `table`, or zero when `idx[i] ≥ 16`.

The zeroing condition is the whole index being out of range, **not** a set high bit, and the
table is the whole 128-bit register rather than a half. Both differ from x86's `vpshufb`; see
the note in this file's header. -/
axiom tbl1_u8_spec (table idx : Vec128) :
    ∃ c, tbl1_u8 table idx = ok c ∧ ∀ i < 16,
      lane8 c i =
        if (lane8 idx i).toNat < 16 then lane8 table (lane8 idx i).toNat else 0#8

/-! ## FEAT_SHA3

Four instructions, each of which is a Keccak step rather than a general bit trick. They exist in
the extraction only because `../extract_rust_to_lean.sh` extracts this backend with
`-C target-feature=+sha3`; see the note there about what that does and does not cover. -/

/-- `eor3.16b` — bitwise exclusive or of all three arguments, over all 128 bits. -/
axiom eor3_spec (a b c : Vec128) :
    ∃ d, eor3 a b c = ok d ∧ bits d = bits a ^^^ bits b ^^^ bits c

/-- `bcax.16b` — `a ^ (b & ~c)`, over all 128 bits.

Note which operand is complemented: the *third*. Keccak's χ is `B[x] ^ (~B[x+1] & B[x+2])`, so
it is `bcax(B[x], B[x+2], B[x+1])` — the last two arguments swapped relative to the reading order
of the formula, which is the error this axiom exists to make impossible to hide. -/
axiom bcax_spec (a b c : Vec128) :
    ∃ d, bcax a b c = ok d ∧ bits d = bits a ^^^ (bits b &&& ~~~bits c)

/-- `rax1.2d` — `a ^ rotl(b, 1)` per 64-bit lane, which is exactly θ's mixing of a column with
its neighbour. -/
axiom rax1_spec (a b : Vec128) :
    ∃ c, rax1 a b = ok c ∧ ∀ i < 2,
      lane64 c i = lane64 a i ^^^ (lane64 b i).rotateLeft 1

/-- `xar.2d #IMM` — `rotr(a ^ b, IMM)` per 64-bit lane: θ's per-lane xor and ρ's rotation in one.

A *right* rotation, so ρ's left rotation by `r` is this with `IMM = (64 − r) % 64` — which is
what the `theta_rho!` macro in `keccak.rs` computes, and the `% 64` there is what keeps the one
entry of ρ with `r = 0` from asking for an out-of-range 64. -/
axiom xar_spec (IMM : Std.I32) (a b : Vec128) (h : 0 ≤ IMM.val) (h' : IMM.val ≤ 63) :
    ∃ c, xar IMM a b = ok c ∧ ∀ i < 2,
      lane64 c i = (lane64 a i ^^^ lane64 b i).rotateRight IMM.val.toNat

/-! ## Memory

These are not instructions but the wrappers in `intrinsics.rs`, and their axioms carry the same
bound the wrapper asserts. The 16- and 32-bit ones are indexed in whole vectors — `load_i16 a i`
reads `a[8i .. 8i+8]` — and the byte ones in bytes, because `keccak` reads the sponge a 64-bit
word at a time and `ser` reads groups at multiples of the coefficient width.

`NttElem` and the pointwise accumulator are `[i16; 512]` and `[i32; 512]` outright — the two
residue blocks are the two halves — so these are plain typed accessors with no reinterpretation
to state. -/

/-- Loads the 8 `i16` at `src[8i ..]`. -/
axiom load_i16_spec {N : Std.Usize} (src : Array Std.I16 N) (i : Std.Usize)
    (h : 8 * (i.val + 1) ≤ N.val) :
    ∃ c, load_i16 src i = ok c ∧ ∀ k < 8, lane16 c k = (src.val[8 * i.val + k]!).bv

/-- Stores 8 `i16` at `dst[8i ..]`, leaving everything else alone. -/
axiom store_i16_spec {N : Std.Usize} (dst : Array Std.I16 N) (i : Std.Usize) (v : Vec128)
    (h : 8 * (i.val + 1) ≤ N.val) :
    ∃ dst', store_i16 dst i v = ok dst' ∧ ∀ j < N.val,
      (dst'.val[j]!).bv =
        if 8 * i.val ≤ j ∧ j < 8 * i.val + 8 then lane16 v (j - 8 * i.val)
        else (dst.val[j]!).bv

/-- Loads the 8 `u16` at `src[8i ..]`. Same bits as `load_i16`; the element type differs only in
how the rest of the crate reads them. -/
axiom load_u16_spec {N : Std.Usize} (src : Array Std.U16 N) (i : Std.Usize)
    (h : 8 * (i.val + 1) ≤ N.val) :
    ∃ c, load_u16 src i = ok c ∧ ∀ k < 8, lane16 c k = (src.val[8 * i.val + k]!).bv

/-- Stores 8 `u16` at `dst[8i ..]`. -/
axiom store_u16_spec {N : Std.Usize} (dst : Array Std.U16 N) (i : Std.Usize) (v : Vec128)
    (h : 8 * (i.val + 1) ≤ N.val) :
    ∃ dst', store_u16 dst i v = ok dst' ∧ ∀ j < N.val,
      (dst'.val[j]!).bv =
        if 8 * i.val ≤ j ∧ j < 8 * i.val + 8 then lane16 v (j - 8 * i.val)
        else (dst.val[j]!).bv

/-- Loads the 4 `i32` at `src[4i ..]`. -/
axiom load_i32_spec {N : Std.Usize} (src : Array Std.I32 N) (i : Std.Usize)
    (h : 4 * (i.val + 1) ≤ N.val) :
    ∃ c, load_i32 src i = ok c ∧ ∀ k < 4, lane32 c k = (src.val[4 * i.val + k]!).bv

/-- Stores 4 `i32` at `dst[4i ..]`, leaving everything else alone. -/
axiom store_i32_spec {N : Std.Usize} (dst : Array Std.I32 N) (i : Std.Usize) (v : Vec128)
    (h : 4 * (i.val + 1) ≤ N.val) :
    ∃ dst', store_i32 dst i v = ok dst' ∧ ∀ j < N.val,
      (dst'.val[j]!).bv =
        if 4 * i.val ≤ j ∧ j < 4 * i.val + 4 then lane32 v (j - 4 * i.val)
        else (dst.val[j]!).bv

/-- Loads the 16 bytes at `src[offset ..]` — byte-indexed, and slice-typed because the
deserializer's input has a length that depends on the coefficient width. -/
axiom load_u8x16_spec (src : Aeneas.Std.Slice Std.U8) (offset : Std.Usize)
    (h : offset.val + 16 ≤ src.val.length) :
    ∃ c, load_u8x16 src offset = ok c ∧
      ∀ k < 16, lane8 c k = (src.val[offset.val + k]!).bv

/-- Stores 16 bytes at `dst[offset ..]`, leaving everything else alone and the length unchanged.
`keccak`'s squeeze is the only caller. -/
axiom store_u8x16_spec (dst : Aeneas.Std.Slice Std.U8) (offset : Std.Usize) (v : Vec128)
    (h : offset.val + 16 ≤ dst.val.length) :
    ∃ dst', store_u8x16 dst offset v = ok dst' ∧
      dst'.val.length = dst.val.length ∧
      ∀ j < dst.val.length,
        (dst'.val[j]!).bv =
          if offset.val ≤ j ∧ j < offset.val + 16 then lane8 v (j - offset.val)
          else (dst.val[j]!).bv

end

end Kopis.Neon
