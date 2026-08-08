/-
  # Kopis/Neon/Model.lean — a computable model of every intrinsic, and its equivalence with the
  # assumed semantics.

  `Kopis/Neon/Intrinsics.lean` states what each SIMD wrapper does as an axiom of the shape
  `∃ c, f args = ok c ∧ <every lane of c is …>`.  Those axioms are the NEON trust base, they are
  written by reading the Arm ARM, and nothing checks them.  This file is the first half of
  checking them.

  For each operation it gives a **computable** function on `BitVec` — `Model.add16`,
  `Model.tbl1U8`, … — and then proves

      ∃ c, f a b = ok c ∧ bits c = Model.f (bits a) (bits b)

  from the axiom.  Two things follow.  First, each axiom pins its result down completely: it
  determines *the* 128-bit word, not merely a family of lane constraints, which is what lets the
  correspondence proofs rewrite with it.  Second — and this is the point — the model is now
  interchangeable with the axiom, and unlike the axiom it runs.

  ## The other half of the check

  This file makes the NEON axioms *testable*; it does not by itself test them.  The other half is
  `SpecTests/Neon/Run.lean` (`make test-neon-model`), which replays
  `../tests/neon_intrinsics_vectors.jsonl` — 50 176 input/output pairs recorded by executing the
  real instructions on a real core (`src/backend/neon/intrinsics_vectors.rs`) — through the models
  below.  Both halves have now run, on an Apple M1: all 46 wrappers agree on every vector.  See
  `NEON_VERIFICATION_PLAN.md` phase A2.

  The equivalence theorems are what make that a test of the *axioms* rather than of some
  unrelated function: a model that drifted from its axiom would fail to compile here, so the only
  way the runner can pass is if the axioms themselves describe the silicon.  Corrupting a model
  alone is caught by `lake build`; corrupting an axiom and its model together is caught by the
  runner.

  ## Reading it

  Each model is deliberately written in the shape of the corresponding axiom — lane `i` of the
  result is such-and-such a function of the arguments' lanes — so that the equivalence proofs are
  one `simp` each and a reviewer can read model and axiom side by side.

  The `TRN` models are the one place where the model's flat lane index and the axiom's `k` have
  to be reconciled: the axiom fixes lanes `2k` and `2k+1` together, the model computes lane `i`,
  and the two meet at `k = i / 2` with the parity of `i` selecting which half of the axiom to
  use.  That is the same reconciliation the AVX2 `unpack` proofs do, and the only one here —
  every other NEON operation is stated lane-for-lane, because `TRN1`/`TRN2` act across the whole
  register and there is no 128-bit-half boundary to work around.
-/
import Kopis.Neon.Lanes

namespace Kopis.Neon

open Aeneas Std Result
open RustKopisNeon.backend.neon.intrinsics

/-! ## The models

Every definition here is a total, computable function on `BitVec`. -/

namespace Model

/-! ### Broadcasts and constants -/

/-- `dup.8h`, from a signed scalar. -/
def dupNS16 (a : BitVec 16) : BitVec 128 := ofLanes16 fun _ => a

/-- `dup.8h`, from an unsigned scalar.  Same instruction as `dupNS16`. -/
def dupNU16 (a : BitVec 16) : BitVec 128 := ofLanes16 fun _ => a

/-- `dup.4s`, from a signed scalar. -/
def dupNS32 (a : BitVec 32) : BitVec 128 := ofLanes32 fun _ => a

/-- `dup.4s`, from an unsigned scalar. -/
def dupNU32 (a : BitVec 32) : BitVec 128 := ofLanes32 fun _ => a

/-- `dup.2d`. -/
def dupNU64 (a : BitVec 64) : BitVec 128 := ofLanes64 fun _ => a

/-- The vector with `lo` in the low 64-bit lane and `hi` in the high one. -/
def setU64x2 (lo hi : BitVec 64) : BitVec 128 := ofLanes64 fun i => if i = 0 then lo else hi

/-! ### Bitwise -/

/-- `and.16b`. -/
def andV (a b : BitVec 128) : BitVec 128 := a &&& b

/-- `eor.16b`. -/
def eorV (a b : BitVec 128) : BitVec 128 := a ^^^ b

/-- `cnt.16b` — population count per *byte*. -/
def cntU8 (a : BitVec 128) : BitVec 128 := ofLanes8 fun i => popCount8 (laneOf 8 a i)

/-! ### 16-bit lane arithmetic -/

/-- `add.8h`. -/
def add16 (a b : BitVec 128) : BitVec 128 :=
  ofLanes16 fun i => laneOf 16 a i + laneOf 16 b i

/-- `sub.8h`. -/
def sub16 (a b : BitVec 128) : BitVec 128 :=
  ofLanes16 fun i => laneOf 16 a i - laneOf 16 b i

/-- `mul.8h` — the low half of each 16×16 product. -/
def mul16 (a b : BitVec 128) : BitVec 128 :=
  ofLanes16 fun i => laneOf 16 a i * laneOf 16 b i

/-- `sqdmulh.8h` — the high half of the *doubled* signed product, saturating.  `Int.fdiv`, not
`/`: ASL's `>>` is a floor shift and every operand here is signed. -/
def sqdmulhS16 (a b : BitVec 128) : BitVec 128 :=
  ofLanes16 fun i => satS16 (Int.fdiv (2 * (laneOf 16 a i).toInt * (laneOf 16 b i).toInt) 65536)

/-- `shsub.8h` — `⌊(a − b)/2⌋`, exactly: the subtraction happens at 17 bits, so there is neither
overflow nor saturation. -/
def shsubS16 (a b : BitVec 128) : BitVec 128 :=
  ofLanes16 fun i => BitVec.ofInt 16 (Int.fdiv ((laneOf 16 a i).toInt - (laneOf 16 b i).toInt) 2)

/-- `sshr.8h #IMM` — arithmetic right shift by an immediate. -/
def sshrNS16 (imm : Nat) (a : BitVec 128) : BitVec 128 :=
  ofLanes16 fun i => (laneOf 16 a i).sshiftRight imm

/-- `ushl.8h` — logical shift by a per-lane signed count, read from the count lane's low byte. -/
def ushlU16 (a counts : BitVec 128) : BitVec 128 :=
  ofLanes16 fun i => ushlLane (laneOf 16 a i) (shiftAmount (laneOf 16 counts i))

/-! ### 32-bit lane arithmetic -/

/-- `add.4s`. -/
def add32 (a b : BitVec 128) : BitVec 128 :=
  ofLanes32 fun i => laneOf 32 a i + laneOf 32 b i

/-- `sub.4s`. -/
def sub32 (a b : BitVec 128) : BitVec 128 :=
  ofLanes32 fun i => laneOf 32 a i - laneOf 32 b i

/-- `mla.4s` — the *first* operand is the accumulator. -/
def mla32 (a b c : BitVec 128) : BitVec 128 :=
  ofLanes32 fun i => laneOf 32 a i + laneOf 32 b i * laneOf 32 c i

/-- `cmgt.4s` — signed 32-bit `a > b` as a lane mask. -/
def cmgtS32 (a b : BitVec 128) : BitVec 128 :=
  ofLanes32 fun i => if BitVec.slt (laneOf 32 b i) (laneOf 32 a i) then BitVec.allOnes 32 else 0#32

/-- `ushl.4s`. -/
def ushlU32 (a counts : BitVec 128) : BitVec 128 :=
  ofLanes32 fun i => ushlLane (laneOf 32 a i) (shiftAmount (laneOf 32 counts i))

/-! ### Widening and narrowing -/

/-- `smull.4s` — the low four lanes' signed 16×16→32 products. -/
def smullLowS16 (a b : BitVec 128) : BitVec 128 :=
  ofLanes32 fun i => (laneOf 16 a i).signExtend 32 * (laneOf 16 b i).signExtend 32

/-- `smull2.4s` — the high four lanes'. -/
def smullHighS16 (a b : BitVec 128) : BitVec 128 :=
  ofLanes32 fun i => (laneOf 16 a (4 + i)).signExtend 32 * (laneOf 16 b (4 + i)).signExtend 32

/-- `sxtl.4s`. -/
def sxtlLowS16 (a : BitVec 128) : BitVec 128 :=
  ofLanes32 fun i => (laneOf 16 a i).signExtend 32

/-- `sxtl2.4s`. -/
def sxtlHighS16 (a : BitVec 128) : BitVec 128 :=
  ofLanes32 fun i => (laneOf 16 a (4 + i)).signExtend 32

/-- `xtn.4h` + `xtn2.8h` — truncate `a`'s four 32-bit lanes into the low half, `b`'s into the
high half.  In order: unlike `vpackusdw` there is nothing to permute afterwards. -/
def xtnPair32 (a b : BitVec 128) : BitVec 128 :=
  ofLanes16 fun i =>
    if i < 4 then BitVec.setWidth 16 (laneOf 32 a i)
    else BitVec.setWidth 16 (laneOf 32 b (i - 4))

/-- `shrn.4h #16` + `shrn2.8h #16` — the high halves of the 32-bit lanes, same arrangement. -/
def shrn16PairS32 (a b : BitVec 128) : BitVec 128 :=
  ofLanes16 fun i =>
    if i < 4 then BitVec.extractLsb' 16 16 (laneOf 32 a i)
    else BitVec.extractLsb' 16 16 (laneOf 32 b (i - 4))

/-! ### Permutes

`TRN1` takes the even lanes of both sources, `TRN2` the odd ones; both interleave `a` into the
even result lanes and `b` into the odd ones. -/

/-- `trn1.8h`. -/
def trn1L16 (a b : BitVec 128) : BitVec 128 :=
  ofLanes16 fun i => if i % 2 = 0 then laneOf 16 a i else laneOf 16 b (i - 1)

/-- `trn2.8h`. -/
def trn2L16 (a b : BitVec 128) : BitVec 128 :=
  ofLanes16 fun i => if i % 2 = 0 then laneOf 16 a (i + 1) else laneOf 16 b i

/-- `trn1.4s`. -/
def trn1L32 (a b : BitVec 128) : BitVec 128 :=
  ofLanes32 fun i => if i % 2 = 0 then laneOf 32 a i else laneOf 32 b (i - 1)

/-- `trn2.4s`. -/
def trn2L32 (a b : BitVec 128) : BitVec 128 :=
  ofLanes32 fun i => if i % 2 = 0 then laneOf 32 a (i + 1) else laneOf 32 b i

/-- `trn1.2d`. -/
def trn1L64 (a b : BitVec 128) : BitVec 128 :=
  ofLanes64 fun i => if i % 2 = 0 then laneOf 64 a i else laneOf 64 b (i - 1)

/-- `trn2.2d`. -/
def trn2L64 (a b : BitVec 128) : BitVec 128 :=
  ofLanes64 fun i => if i % 2 = 0 then laneOf 64 a (i + 1) else laneOf 64 b i

/-- `tbl.16b` — whole-register byte permute, zeroing on any index ≥ 16.  Not `vpshufb`: the
table is all 16 bytes and the zeroing condition is the index's *value*, not its top bit. -/
def tbl1U8 (table idx : BitVec 128) : BitVec 128 :=
  ofLanes8 fun i =>
    if (laneOf 8 idx i).toNat < 16 then laneOf 8 table (laneOf 8 idx i).toNat else 0#8

/-! ### FEAT_SHA3 -/

/-- `eor3.16b`. -/
def eor3V (a b c : BitVec 128) : BitVec 128 := a ^^^ b ^^^ c

/-- `bcax.16b` — `a ^ (b & ~c)`; the *third* operand is the complemented one. -/
def bcaxV (a b c : BitVec 128) : BitVec 128 := a ^^^ (b &&& ~~~c)

/-- `rax1.2d` — `a ^ rotl(b, 1)` per 64-bit lane. -/
def rax1V (a b : BitVec 128) : BitVec 128 :=
  ofLanes64 fun i => laneOf 64 a i ^^^ (laneOf 64 b i).rotateLeft 1

/-- `xar.2d #IMM` — `rotr(a ^ b, IMM)` per 64-bit lane.  A *right* rotation. -/
def xarV (imm : Nat) (a b : BitVec 128) : BitVec 128 :=
  ofLanes64 fun i => (laneOf 64 a i ^^^ laneOf 64 b i).rotateRight imm

/-! ### Memory

The memory wrappers are not instructions; their axioms are about the crate's buffers, so there
is no `bits`-level equivalence theorem to state — the axiom's subject is an aeneas `Array` or
`Slice`, not a `BitVec`.  What is modelled here is the indexing claim itself, over a buffer as a
list of element words, which is the form the differential runner will evaluate.  The AVX2 file
stops in exactly the same place and for the same reason. -/

/-- `load_i16` / `load_u16`: the 8 elements at `src[8 i ..]`. -/
def loadW16 (src : List (BitVec 16)) (i : Nat) : BitVec 128 :=
  ofLanes16 fun k => src[8 * i + k]!

/-- `load_i32`: the 4 elements at `src[4 i ..]`. -/
def loadW32 (src : List (BitVec 32)) (i : Nat) : BitVec 128 :=
  ofLanes32 fun k => src[4 * i + k]!

/-- `load_u8x16`: the 16 bytes at `src[offset ..]`, byte-indexed. -/
def loadW8x16 (src : List (BitVec 8)) (offset : Nat) : BitVec 128 :=
  ofLanes8 fun k => src[offset + k]!

/-- `store_i16` / `store_u16`: `dst` with elements `8 i .. 8 i + 8` replaced. -/
def storeW16 (dst : List (BitVec 16)) (i : Nat) (v : BitVec 128) : List (BitVec 16) :=
  (List.range dst.length).map fun j =>
    if 8 * i ≤ j ∧ j < 8 * i + 8 then laneOf 16 v (j - 8 * i) else dst[j]!

/-- `store_i32`: `dst` with elements `4 i .. 4 i + 4` replaced. -/
def storeW32 (dst : List (BitVec 32)) (i : Nat) (v : BitVec 128) : List (BitVec 32) :=
  (List.range dst.length).map fun j =>
    if 4 * i ≤ j ∧ j < 4 * i + 4 then laneOf 32 v (j - 4 * i) else dst[j]!

/-- `store_u8x16`: `dst` with bytes `offset .. offset + 16` replaced. -/
def storeW8x16 (dst : List (BitVec 8)) (offset : Nat) (v : BitVec 128) : List (BitVec 8) :=
  (List.range dst.length).map fun j =>
    if offset ≤ j ∧ j < offset + 16 then laneOf 8 v (j - offset) else dst[j]!

end Model

/-! ## The models agree with the axioms

Each theorem below says the axiom determines the result's 128 bits exactly, and that they are
the model's.  These are the statements the correspondence proofs actually use — a whole-register
equation rewrites, a per-lane conjunction does not.

Every proof is the same three steps: take the axiom's witness, apply the lane-to-word bridge
from `Lanes.lean`, and evaluate the model's lane at the index. -/

noncomputable section

/-! ### Broadcasts and constants -/

theorem dup_n_s16_model (a : Std.I16) :
    ∃ c, dup_n_s16 a = ok c ∧ bits c = Model.dupNS16 a.bv := by
  obtain ⟨c, hc, h⟩ := dup_n_s16_spec a
  exact ⟨c, hc, eq_of_lane16_bv fun i hi => by
    simpa [Model.dupNS16, laneOf_ofLanes16 _ hi] using h i hi⟩

theorem dup_n_u16_model (a : Std.U16) :
    ∃ c, dup_n_u16 a = ok c ∧ bits c = Model.dupNU16 a.bv := by
  obtain ⟨c, hc, h⟩ := dup_n_u16_spec a
  exact ⟨c, hc, eq_of_lane16_bv fun i hi => by
    simpa [Model.dupNU16, laneOf_ofLanes16 _ hi] using h i hi⟩

theorem dup_n_s32_model (a : Std.I32) :
    ∃ c, dup_n_s32 a = ok c ∧ bits c = Model.dupNS32 a.bv := by
  obtain ⟨c, hc, h⟩ := dup_n_s32_spec a
  exact ⟨c, hc, eq_of_lane32_bv fun i hi => by
    simpa [Model.dupNS32, laneOf_ofLanes32 _ hi] using h i hi⟩

theorem dup_n_u32_model (a : Std.U32) :
    ∃ c, dup_n_u32 a = ok c ∧ bits c = Model.dupNU32 a.bv := by
  obtain ⟨c, hc, h⟩ := dup_n_u32_spec a
  exact ⟨c, hc, eq_of_lane32_bv fun i hi => by
    simpa [Model.dupNU32, laneOf_ofLanes32 _ hi] using h i hi⟩

theorem dup_n_u64_model (a : Std.U64) :
    ∃ c, dup_n_u64 a = ok c ∧ bits c = Model.dupNU64 a.bv := by
  obtain ⟨c, hc, h⟩ := dup_n_u64_spec a
  exact ⟨c, hc, eq_of_lane64_bv fun i hi => by
    simpa [Model.dupNU64, laneOf_ofLanes64 _ hi] using h i hi⟩

theorem set_u64x2_model (lo hi : Std.U64) :
    ∃ c, set_u64x2 lo hi = ok c ∧ bits c = Model.setU64x2 lo.bv hi.bv := by
  obtain ⟨c, hc, h0, h1⟩ := set_u64x2_spec lo hi
  refine ⟨c, hc, eq_of_lane64_bv fun i hi' => ?_⟩
  rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl
  · simpa [Model.setU64x2, laneOf_ofLanes64 _ hi'] using h0
  · simpa [Model.setU64x2, laneOf_ofLanes64 _ hi'] using h1

/-! ### Bitwise -/

theorem and_model (a b : Vec128) :
    ∃ c, and a b = ok c ∧ bits c = Model.andV (bits a) (bits b) := by
  obtain ⟨c, hc, h⟩ := and_spec a b
  exact ⟨c, hc, by simpa [Model.andV] using h⟩

theorem eor_model (a b : Vec128) :
    ∃ c, eor a b = ok c ∧ bits c = Model.eorV (bits a) (bits b) := by
  obtain ⟨c, hc, h⟩ := eor_spec a b
  exact ⟨c, hc, by simpa [Model.eorV] using h⟩

theorem cnt_u8_model (a : Vec128) :
    ∃ c, cnt_u8 a = ok c ∧ bits c = Model.cntU8 (bits a) := by
  obtain ⟨c, hc, h⟩ := cnt_u8_spec a
  exact ⟨c, hc, eq_of_lane8_bv fun i hi => by
    simpa [Model.cntU8, laneOf_ofLanes8 _ hi] using h i hi⟩

/-! ### 16-bit lane arithmetic -/

theorem add_16_model (a b : Vec128) :
    ∃ c, add_16 a b = ok c ∧ bits c = Model.add16 (bits a) (bits b) := by
  obtain ⟨c, hc, h⟩ := add_16_spec a b
  exact ⟨c, hc, eq_of_lane16_bv fun i hi => by
    simpa [Model.add16, laneOf_ofLanes16 _ hi] using h i hi⟩

theorem sub_16_model (a b : Vec128) :
    ∃ c, sub_16 a b = ok c ∧ bits c = Model.sub16 (bits a) (bits b) := by
  obtain ⟨c, hc, h⟩ := sub_16_spec a b
  exact ⟨c, hc, eq_of_lane16_bv fun i hi => by
    simpa [Model.sub16, laneOf_ofLanes16 _ hi] using h i hi⟩

theorem mul_16_model (a b : Vec128) :
    ∃ c, mul_16 a b = ok c ∧ bits c = Model.mul16 (bits a) (bits b) := by
  obtain ⟨c, hc, h⟩ := mul_16_spec a b
  exact ⟨c, hc, eq_of_lane16_bv fun i hi => by
    simpa [Model.mul16, laneOf_ofLanes16 _ hi] using h i hi⟩

theorem sqdmulh_s16_model (a b : Vec128) :
    ∃ c, sqdmulh_s16 a b = ok c ∧ bits c = Model.sqdmulhS16 (bits a) (bits b) := by
  obtain ⟨c, hc, h⟩ := sqdmulh_s16_spec a b
  exact ⟨c, hc, eq_of_lane16_bv fun i hi => by
    simpa [Model.sqdmulhS16, laneOf_ofLanes16 _ hi] using h i hi⟩

theorem shsub_s16_model (a b : Vec128) :
    ∃ c, shsub_s16 a b = ok c ∧ bits c = Model.shsubS16 (bits a) (bits b) := by
  obtain ⟨c, hc, h⟩ := shsub_s16_spec a b
  exact ⟨c, hc, eq_of_lane16_bv fun i hi => by
    simpa [Model.shsubS16, laneOf_ofLanes16 _ hi] using h i hi⟩

theorem sshr_n_s16_model (IMM : Std.I32) (a : Vec128) (h1 : 1 ≤ IMM.val) (h2 : IMM.val ≤ 16) :
    ∃ c, sshr_n_s16 IMM a = ok c ∧ bits c = Model.sshrNS16 IMM.val.toNat (bits a) := by
  obtain ⟨c, hc, h⟩ := sshr_n_s16_spec IMM a h1 h2
  exact ⟨c, hc, eq_of_lane16_bv fun i hi => by
    simpa [Model.sshrNS16, laneOf_ofLanes16 _ hi] using h i hi⟩

theorem ushl_u16_model (a counts : Vec128) :
    ∃ c, ushl_u16 a counts = ok c ∧ bits c = Model.ushlU16 (bits a) (bits counts) := by
  obtain ⟨c, hc, h⟩ := ushl_u16_spec a counts
  exact ⟨c, hc, eq_of_lane16_bv fun i hi => by
    simpa [Model.ushlU16, laneOf_ofLanes16 _ hi] using h i hi⟩

/-! ### 32-bit lane arithmetic -/

theorem add_32_model (a b : Vec128) :
    ∃ c, add_32 a b = ok c ∧ bits c = Model.add32 (bits a) (bits b) := by
  obtain ⟨c, hc, h⟩ := add_32_spec a b
  exact ⟨c, hc, eq_of_lane32_bv fun i hi => by
    simpa [Model.add32, laneOf_ofLanes32 _ hi] using h i hi⟩

theorem sub_32_model (a b : Vec128) :
    ∃ c, sub_32 a b = ok c ∧ bits c = Model.sub32 (bits a) (bits b) := by
  obtain ⟨c, hc, h⟩ := sub_32_spec a b
  exact ⟨c, hc, eq_of_lane32_bv fun i hi => by
    simpa [Model.sub32, laneOf_ofLanes32 _ hi] using h i hi⟩

theorem mla_32_model (a b c : Vec128) :
    ∃ d, mla_32 a b c = ok d ∧ bits d = Model.mla32 (bits a) (bits b) (bits c) := by
  obtain ⟨d, hd, h⟩ := mla_32_spec a b c
  exact ⟨d, hd, eq_of_lane32_bv fun i hi => by
    simpa [Model.mla32, laneOf_ofLanes32 _ hi] using h i hi⟩

theorem cmgt_s32_model (a b : Vec128) :
    ∃ c, cmgt_s32 a b = ok c ∧ bits c = Model.cmgtS32 (bits a) (bits b) := by
  obtain ⟨c, hc, h⟩ := cmgt_s32_spec a b
  exact ⟨c, hc, eq_of_lane32_bv fun i hi => by
    simpa [Model.cmgtS32, laneOf_ofLanes32 _ hi] using h i hi⟩

theorem ushl_u32_model (a counts : Vec128) :
    ∃ c, ushl_u32 a counts = ok c ∧ bits c = Model.ushlU32 (bits a) (bits counts) := by
  obtain ⟨c, hc, h⟩ := ushl_u32_spec a counts
  exact ⟨c, hc, eq_of_lane32_bv fun i hi => by
    simpa [Model.ushlU32, laneOf_ofLanes32 _ hi] using h i hi⟩

/-! ### Widening and narrowing -/

theorem smull_low_s16_model (a b : Vec128) :
    ∃ c, smull_low_s16 a b = ok c ∧ bits c = Model.smullLowS16 (bits a) (bits b) := by
  obtain ⟨c, hc, h⟩ := smull_low_s16_spec a b
  exact ⟨c, hc, eq_of_lane32_bv fun i hi => by
    simpa [Model.smullLowS16, laneOf_ofLanes32 _ hi] using h i hi⟩

theorem smull_high_s16_model (a b : Vec128) :
    ∃ c, smull_high_s16 a b = ok c ∧ bits c = Model.smullHighS16 (bits a) (bits b) := by
  obtain ⟨c, hc, h⟩ := smull_high_s16_spec a b
  exact ⟨c, hc, eq_of_lane32_bv fun i hi => by
    simpa [Model.smullHighS16, laneOf_ofLanes32 _ hi] using h i hi⟩

theorem sxtl_low_s16_model (a : Vec128) :
    ∃ c, sxtl_low_s16 a = ok c ∧ bits c = Model.sxtlLowS16 (bits a) := by
  obtain ⟨c, hc, h⟩ := sxtl_low_s16_spec a
  exact ⟨c, hc, eq_of_lane32_bv fun i hi => by
    simpa [Model.sxtlLowS16, laneOf_ofLanes32 _ hi] using h i hi⟩

theorem sxtl_high_s16_model (a : Vec128) :
    ∃ c, sxtl_high_s16 a = ok c ∧ bits c = Model.sxtlHighS16 (bits a) := by
  obtain ⟨c, hc, h⟩ := sxtl_high_s16_spec a
  exact ⟨c, hc, eq_of_lane32_bv fun i hi => by
    simpa [Model.sxtlHighS16, laneOf_ofLanes32 _ hi] using h i hi⟩

theorem xtn_pair_32_model (a b : Vec128) :
    ∃ c, xtn_pair_32 a b = ok c ∧ bits c = Model.xtnPair32 (bits a) (bits b) := by
  obtain ⟨c, hc, h⟩ := xtn_pair_32_spec a b
  refine ⟨c, hc, eq_of_lane16_bv fun i hi => ?_⟩
  rcases Nat.lt_or_ge i 4 with hlt | hge
  · obtain ⟨h₀, -⟩ := h i hlt
    simpa [Model.xtnPair32, laneOf_ofLanes16 _ hi, hlt] using h₀
  · obtain ⟨-, h₁⟩ := h (i - 4) (by omega)
    rw [show 4 + (i - 4) = i by omega] at h₁
    simpa [Model.xtnPair32, laneOf_ofLanes16 _ hi, Nat.not_lt.mpr hge] using h₁

theorem shrn16_pair_s32_model (a b : Vec128) :
    ∃ c, shrn16_pair_s32 a b = ok c ∧ bits c = Model.shrn16PairS32 (bits a) (bits b) := by
  obtain ⟨c, hc, h⟩ := shrn16_pair_s32_spec a b
  refine ⟨c, hc, eq_of_lane16_bv fun i hi => ?_⟩
  rcases Nat.lt_or_ge i 4 with hlt | hge
  · obtain ⟨h₀, -⟩ := h i hlt
    simpa [Model.shrn16PairS32, laneOf_ofLanes16 _ hi, hlt] using h₀
  · obtain ⟨-, h₁⟩ := h (i - 4) (by omega)
    rw [show 4 + (i - 4) = i by omega] at h₁
    simpa [Model.shrn16PairS32, laneOf_ofLanes16 _ hi, Nat.not_lt.mpr hge] using h₁

/-! ### Permutes

The axioms fix lanes `2k` and `2k+1` together; the model computes lane `i`.  They meet at
`k = i / 2`, with `i`'s parity choosing the conjunct. -/

theorem trn1_16_model (a b : Vec128) :
    ∃ c, trn1_16 a b = ok c ∧ bits c = Model.trn1L16 (bits a) (bits b) := by
  obtain ⟨c, hc, h⟩ := trn1_16_spec a b
  refine ⟨c, hc, eq_of_lane16_bv fun i hi => ?_⟩
  obtain ⟨h₀, h₁⟩ := h (i / 2) (by omega)
  by_cases he : i % 2 = 0
  · rw [show 2 * (i / 2) = i by omega] at h₀
    simpa [Model.trn1L16, laneOf_ofLanes16 _ hi, he] using h₀
  · rw [show 2 * (i / 2) + 1 = i by omega] at h₁
    simpa [Model.trn1L16, laneOf_ofLanes16 _ hi, he, show i - 1 = 2 * (i / 2) by omega] using h₁

theorem trn2_16_model (a b : Vec128) :
    ∃ c, trn2_16 a b = ok c ∧ bits c = Model.trn2L16 (bits a) (bits b) := by
  obtain ⟨c, hc, h⟩ := trn2_16_spec a b
  refine ⟨c, hc, eq_of_lane16_bv fun i hi => ?_⟩
  obtain ⟨h₀, h₁⟩ := h (i / 2) (by omega)
  by_cases he : i % 2 = 0
  · rw [show 2 * (i / 2) + 1 = i + 1 by omega, show 2 * (i / 2) = i by omega] at h₀
    simpa [Model.trn2L16, laneOf_ofLanes16 _ hi, he] using h₀
  · rw [show 2 * (i / 2) + 1 = i by omega] at h₁
    simpa [Model.trn2L16, laneOf_ofLanes16 _ hi, he] using h₁

theorem trn1_32_model (a b : Vec128) :
    ∃ c, trn1_32 a b = ok c ∧ bits c = Model.trn1L32 (bits a) (bits b) := by
  obtain ⟨c, hc, h⟩ := trn1_32_spec a b
  refine ⟨c, hc, eq_of_lane32_bv fun i hi => ?_⟩
  obtain ⟨h₀, h₁⟩ := h (i / 2) (by omega)
  by_cases he : i % 2 = 0
  · rw [show 2 * (i / 2) = i by omega] at h₀
    simpa [Model.trn1L32, laneOf_ofLanes32 _ hi, he] using h₀
  · rw [show 2 * (i / 2) + 1 = i by omega] at h₁
    simpa [Model.trn1L32, laneOf_ofLanes32 _ hi, he, show i - 1 = 2 * (i / 2) by omega] using h₁

theorem trn2_32_model (a b : Vec128) :
    ∃ c, trn2_32 a b = ok c ∧ bits c = Model.trn2L32 (bits a) (bits b) := by
  obtain ⟨c, hc, h⟩ := trn2_32_spec a b
  refine ⟨c, hc, eq_of_lane32_bv fun i hi => ?_⟩
  obtain ⟨h₀, h₁⟩ := h (i / 2) (by omega)
  by_cases he : i % 2 = 0
  · rw [show 2 * (i / 2) + 1 = i + 1 by omega, show 2 * (i / 2) = i by omega] at h₀
    simpa [Model.trn2L32, laneOf_ofLanes32 _ hi, he] using h₀
  · rw [show 2 * (i / 2) + 1 = i by omega] at h₁
    simpa [Model.trn2L32, laneOf_ofLanes32 _ hi, he] using h₁

theorem trn1_64_model (a b : Vec128) :
    ∃ c, trn1_64 a b = ok c ∧ bits c = Model.trn1L64 (bits a) (bits b) := by
  obtain ⟨c, hc, h0, h1⟩ := trn1_64_spec a b
  refine ⟨c, hc, eq_of_lane64_bv fun i hi => ?_⟩
  rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl
  · simpa [Model.trn1L64, laneOf_ofLanes64 _ hi] using h0
  · simpa [Model.trn1L64, laneOf_ofLanes64 _ hi] using h1

theorem trn2_64_model (a b : Vec128) :
    ∃ c, trn2_64 a b = ok c ∧ bits c = Model.trn2L64 (bits a) (bits b) := by
  obtain ⟨c, hc, h0, h1⟩ := trn2_64_spec a b
  refine ⟨c, hc, eq_of_lane64_bv fun i hi => ?_⟩
  rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl
  · simpa [Model.trn2L64, laneOf_ofLanes64 _ hi] using h0
  · simpa [Model.trn2L64, laneOf_ofLanes64 _ hi] using h1

theorem tbl1_u8_model (table idx : Vec128) :
    ∃ c, tbl1_u8 table idx = ok c ∧ bits c = Model.tbl1U8 (bits table) (bits idx) := by
  obtain ⟨c, hc, h⟩ := tbl1_u8_spec table idx
  exact ⟨c, hc, eq_of_lane8_bv fun i hi => by
    simpa [Model.tbl1U8, laneOf_ofLanes8 _ hi] using h i hi⟩

/-! ### FEAT_SHA3 -/

theorem eor3_model (a b c : Vec128) :
    ∃ d, eor3 a b c = ok d ∧ bits d = Model.eor3V (bits a) (bits b) (bits c) := by
  obtain ⟨d, hd, h⟩ := eor3_spec a b c
  exact ⟨d, hd, by simpa [Model.eor3V] using h⟩

theorem bcax_model (a b c : Vec128) :
    ∃ d, bcax a b c = ok d ∧ bits d = Model.bcaxV (bits a) (bits b) (bits c) := by
  obtain ⟨d, hd, h⟩ := bcax_spec a b c
  exact ⟨d, hd, by simpa [Model.bcaxV] using h⟩

theorem rax1_model (a b : Vec128) :
    ∃ c, rax1 a b = ok c ∧ bits c = Model.rax1V (bits a) (bits b) := by
  obtain ⟨c, hc, h⟩ := rax1_spec a b
  exact ⟨c, hc, eq_of_lane64_bv fun i hi => by
    simpa [Model.rax1V, laneOf_ofLanes64 _ hi] using h i hi⟩

theorem xar_model (IMM : Std.I32) (a b : Vec128) (h1 : 0 ≤ IMM.val) (h2 : IMM.val ≤ 63) :
    ∃ c, xar IMM a b = ok c ∧ bits c = Model.xarV IMM.val.toNat (bits a) (bits b) := by
  obtain ⟨c, hc, h⟩ := xar_spec IMM a b h1 h2
  exact ⟨c, hc, eq_of_lane64_bv fun i hi => by
    simpa [Model.xarV, laneOf_ofLanes64 _ hi] using h i hi⟩

end

end Kopis.Neon
