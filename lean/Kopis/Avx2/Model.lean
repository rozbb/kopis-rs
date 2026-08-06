/-
  # Kopis/Avx2/Model.lean — a computable model of every intrinsic, and its equivalence with the
  # assumed semantics.

  `Kopis/Avx2/Intrinsics.lean` states what each SIMD wrapper does as an axiom of the shape
  `∃ c, f args = ok c ∧ <every lane of c is …>`.  Those axioms are the AVX2 trust base, they are
  written by reading the Intel SDM, and nothing checks them.  This file is the first half of
  checking them.

  For each operation it gives a **computable** function on `BitVec` — `Model.addEpi16`,
  `Model.shuffleEpi8`, … — and then proves

      ∃ c, f a b = ok c ∧ bits c = Model.f (bits a) (bits b)

  from the axiom.  Two things follow.  First, each axiom pins its result down completely: it
  determines *the* 256-bit word, not merely a family of lane constraints, which is what lets the
  correspondence proofs rewrite with it.  Second — and this is the point — the model is now
  interchangeable with the axiom, and unlike the axiom it runs.  `SpecTests/Avx2/Run.lean`
  evaluates these definitions on vectors produced by the real instructions on real silicon
  (`src/backend/avx2/intrinsics_vectors.rs` writes `tests/intrinsics_vectors.jsonl`), so a wrong
  axiom shows up as a failing test rather than as a silently worthless proof.

  What the test can and cannot catch: it checks the model against hardware, and this file checks
  the model against the axiom, so a disagreement between axiom and hardware is caught *for the
  inputs tested*.  It is a differential test, not a proof — the assumption that remains is that
  agreement on ~1000 random inputs per operation implies agreement everywhere, which for
  straight-line SIMD arithmetic with no state is a good assumption and not a certainty.

  The lane-index arithmetic below (`i / 8`, `i % 8`, …) recovers the `(h, k)` decomposition the
  axioms quantify over from the flat lane index `ofLanes*` supplies; each proof discharges that
  by `omega` after `interval_cases` fixes the index.
-/
import Kopis.Avx2.Lanes

namespace Kopis.Avx2

open Aeneas Std Result
open RustKopisAvx2.backend.avx2.intrinsics

/-! ## The models

Every definition here is a total, computable function on `BitVec`.  They are deliberately
written in the shape of the corresponding axiom — lane `i` of the result is such-and-such a
function of the arguments' lanes — so that the equivalence proofs are one `simp` each and a
reviewer can read model and axiom side by side. -/

namespace Model

/-! ### Constants and bitwise -/

/-- `vpbroadcastw`. -/
def set1Epi16 (a : BitVec 16) : BitVec 256 := ofLanes16 fun _ => a

/-- `vpbroadcastd`. -/
def set1Epi32 (a : BitVec 32) : BitVec 256 := ofLanes32 fun _ => a

/-- `vpbroadcastq`. -/
def set1Epi64x (a : BitVec 64) : BitVec 256 := ofLanes64 fun _ => a

/-- `vpxor` against itself. -/
def setzeroSi256 : BitVec 256 := 0#256

/-- `vmovd`. -/
def cvtsi32Si128 (a : BitVec 32) : BitVec 128 := a.setWidth 128

/-- `vpand`. -/
def andSi256 (a b : BitVec 256) : BitVec 256 := a &&& b

/-- `vpxor`. -/
def xorSi256 (a b : BitVec 256) : BitVec 256 := a ^^^ b

/-- `vpor`. -/
def orSi256 (a b : BitVec 256) : BitVec 256 := a ||| b

/-- `vpandn` — the *first* operand is the complemented one. -/
def andnotSi256 (a b : BitVec 256) : BitVec 256 := (~~~a) &&& b

/-! ### Lane arithmetic -/

/-- `vpaddw`. -/
def addEpi16 (a b : BitVec 256) : BitVec 256 :=
  ofLanes16 fun i => laneOf 16 a i + laneOf 16 b i

/-- `vpsubw`. -/
def subEpi16 (a b : BitVec 256) : BitVec 256 :=
  ofLanes16 fun i => laneOf 16 a i - laneOf 16 b i

/-- `vpaddd`. -/
def addEpi32 (a b : BitVec 256) : BitVec 256 :=
  ofLanes32 fun i => laneOf 32 a i + laneOf 32 b i

/-- `vpsubd`. -/
def subEpi32 (a b : BitVec 256) : BitVec 256 :=
  ofLanes32 fun i => laneOf 32 a i - laneOf 32 b i

/-- `vpmullw` — the low half of each 16×16 product. -/
def mulloEpi16 (a b : BitVec 256) : BitVec 256 :=
  ofLanes16 fun i => laneOf 16 a i * laneOf 16 b i

/-- `vpmulhw` — the high half of each *signed* 16×16 product. -/
def mulhiEpi16 (a b : BitVec 256) : BitVec 256 :=
  ofLanes16 fun i =>
    BitVec.extractLsb' 16 16 ((laneOf 16 a i).signExtend 32 * (laneOf 16 b i).signExtend 32)

/-- `vpmulld` — the low half of each 32×32 product. -/
def mulloEpi32 (a b : BitVec 256) : BitVec 256 :=
  ofLanes32 fun i => laneOf 32 a i * laneOf 32 b i

/-- `vpcmpgtd` — signed 32-bit `a > b` as a lane mask. -/
def cmpgtEpi32 (a b : BitVec 256) : BitVec 256 :=
  ofLanes32 fun i =>
    if BitVec.slt (laneOf 32 b i) (laneOf 32 a i) then BitVec.allOnes 32 else 0#32

/-! ### Shifts

The immediate is a `Nat` here; the extracted code carries it as an `I32` whose non-negativity
the Rust `static_assert_uimm_bits!` guarantees, and the equivalence theorems below take
`IMM.val.toNat`. -/

/-- `vpsraw` by an immediate. -/
def sraiEpi16 (imm : Nat) (a : BitVec 256) : BitVec 256 :=
  ofLanes16 fun i => (laneOf 16 a i).sshiftRight imm

/-- `vpsrad` by an immediate. -/
def sraiEpi32 (imm : Nat) (a : BitVec 256) : BitVec 256 :=
  ofLanes32 fun i => (laneOf 32 a i).sshiftRight imm

/-- `vpsrlw` by an immediate. -/
def srliEpi16 (imm : Nat) (a : BitVec 256) : BitVec 256 :=
  ofLanes16 fun i => laneOf 16 a i >>> imm

/-- `vpslld` by an immediate. -/
def slliEpi32 (imm : Nat) (a : BitVec 256) : BitVec 256 :=
  ofLanes32 fun i => laneOf 32 a i <<< imm

/-- `vpsllq` by an immediate. -/
def slliEpi64 (imm : Nat) (a : BitVec 256) : BitVec 256 :=
  ofLanes64 fun i => laneOf 64 a i <<< imm

/-- `vpsrlq` by an immediate. -/
def srliEpi64 (imm : Nat) (a : BitVec 256) : BitVec 256 :=
  ofLanes64 fun i => laneOf 64 a i >>> imm

/-- `vpsrlw` by a register — the count is the whole low 64 bits of `count`. -/
def srlEpi16 (a : BitVec 256) (count : BitVec 128) : BitVec 256 :=
  ofLanes16 fun i => laneOf 16 a i >>> (laneOf 64 count 0).toNat

/-- `vpsrlvd` — per-lane variable logical shift. -/
def srlvEpi32 (a counts : BitVec 256) : BitVec 256 :=
  ofLanes32 fun i => laneOf 32 a i >>> (laneOf 32 counts i).toNat

/-! ### Shuffles, packs and lane surgery -/

/-- `vpshufb` — byte permute within each 128-bit half, high control bit zeroes. -/
def shuffleEpi8 (a b : BitVec 256) : BitVec 256 :=
  ofLanes8 fun i =>
    if (laneOf 8 b i).getLsbD 7 then 0#8
    else laneOf 8 a (16 * (i / 16) + (laneOf 8 b i &&& 0x0F#8).toNat)

/-- `vpunpcklwd`. -/
def unpackloEpi16 (a b : BitVec 256) : BitVec 256 :=
  ofLanes16 fun i =>
    if i % 2 = 0 then laneOf 16 a (8 * (i / 8) + i % 8 / 2)
    else laneOf 16 b (8 * (i / 8) + i % 8 / 2)

/-- `vpunpckhwd`. -/
def unpackhiEpi16 (a b : BitVec 256) : BitVec 256 :=
  ofLanes16 fun i =>
    if i % 2 = 0 then laneOf 16 a (8 * (i / 8) + 4 + i % 8 / 2)
    else laneOf 16 b (8 * (i / 8) + 4 + i % 8 / 2)

/-- `vpunpckldq`. -/
def unpackloEpi32 (a b : BitVec 256) : BitVec 256 :=
  ofLanes32 fun i =>
    if i % 2 = 0 then laneOf 32 a (4 * (i / 4) + i % 4 / 2)
    else laneOf 32 b (4 * (i / 4) + i % 4 / 2)

/-- `vpunpckhdq`. -/
def unpackhiEpi32 (a b : BitVec 256) : BitVec 256 :=
  ofLanes32 fun i =>
    if i % 2 = 0 then laneOf 32 a (4 * (i / 4) + 2 + i % 4 / 2)
    else laneOf 32 b (4 * (i / 4) + 2 + i % 4 / 2)

/-- `vpunpcklqdq`. -/
def unpackloEpi64 (a b : BitVec 256) : BitVec 256 :=
  ofLanes64 fun i =>
    if i % 2 = 0 then laneOf 64 a (2 * (i / 2)) else laneOf 64 b (2 * (i / 2))

/-- `vpunpckhqdq`. -/
def unpackhiEpi64 (a b : BitVec 256) : BitVec 256 :=
  ofLanes64 fun i =>
    if i % 2 = 0 then laneOf 64 a (2 * (i / 2) + 1) else laneOf 64 b (2 * (i / 2) + 1)

/-- The four 128-bit halves `vperm2i128` selects between, on bits rather than registers. -/
def selectHalfBV (a b : BitVec 256) : Nat → BitVec 128
  | 0 => laneOf 128 a 0
  | 1 => laneOf 128 a 1
  | 2 => laneOf 128 b 0
  | _ => laneOf 128 b 1

/-- `vperm2i128`. -/
def permute2x128Si256 (imm : BitVec 32) (a b : BitVec 256) : BitVec 256 :=
  ofLanes128 fun j =>
    if ((imm >>> (4 * j)) &&& 8#32) ≠ 0#32 then 0#128
    else selectHalfBV a b (((imm >>> (4 * j)) &&& 3#32).toNat)

/-- `vpermq`. -/
def permute4x64Epi64 (imm : BitVec 32) (a : BitVec 256) : BitVec 256 :=
  ofLanes64 fun i => laneOf 64 a (((imm >>> (2 * i)) &&& 3#32).toNat)

/-- `vpackssdw`. -/
def packsEpi32 (a b : BitVec 256) : BitVec 256 :=
  ofLanes16 fun i =>
    if i % 8 < 4 then satS (laneOf 32 a (4 * (i / 8) + i % 8))
    else satS (laneOf 32 b (4 * (i / 8) + (i % 8 - 4)))

/-- `vpackusdw`. -/
def packusEpi32 (a b : BitVec 256) : BitVec 256 :=
  ofLanes16 fun i =>
    if i % 8 < 4 then satU (laneOf 32 a (4 * (i / 8) + i % 8))
    else satU (laneOf 32 b (4 * (i / 8) + (i % 8 - 4)))

/-- `vpmovzxwd`. -/
def cvtepu16Epi32 (a : BitVec 128) : BitVec 256 :=
  ofLanes32 fun i => (laneOf 16 a i).setWidth 32

/-- The low half of a register. -/
def castsi256Si128 (a : BitVec 256) : BitVec 128 := BitVec.extractLsb' 0 128 a

/-- `vextracti128`. -/
def extracti128Si256 (imm : Nat) (a : BitVec 256) : BitVec 128 :=
  BitVec.extractLsb' (128 * (imm % 2)) 128 a

/-- `vbroadcasti128`. -/
def broadcastsi128Si256 (a : BitVec 128) : BitVec 256 := ofLanes128 fun _ => a

/-! ### Memory

The memory wrappers are not instructions; their axioms are about the crate's buffers.  The
models take the buffer as a list of element words and are what the differential test evaluates,
so the indexing claims of the loads and stores get checked rather than merely asserted. -/

/-- `load_i16` / `load_u16`: the 16 elements at `src[16 i ..]`. -/
def loadW16 (src : List (BitVec 16)) (i : Nat) : BitVec 256 :=
  ofLanes16 fun k => src[16 * i + k]!

/-- `load_i32`: the 8 elements at `src[8 i ..]`. -/
def loadW32 (src : List (BitVec 32)) (i : Nat) : BitVec 256 :=
  ofLanes32 fun k => src[8 * i + k]!

/-- `load_u8`: the 32 bytes at `src[32 i ..]`. -/
def loadW8 (src : List (BitVec 8)) (i : Nat) : BitVec 256 :=
  ofLanes8 fun k => src[32 * i + k]!

/-- `load_u8x16`: the 16 bytes at `src[offset ..]`, byte-indexed. -/
def loadW8x16 (src : List (BitVec 8)) (offset : Nat) : BitVec 128 :=
  ofLanes8' fun k => src[offset + k]!

/-- `load_u8x32`: the 32 bytes at `src[offset ..]`, byte-indexed. -/
def loadW8x32 (src : List (BitVec 8)) (offset : Nat) : BitVec 256 :=
  ofLanes8 fun k => src[offset + k]!

/-- `store_u8x32`: `dst` with bytes `offset .. offset + 32` replaced. -/
def storeW8x32 (dst : List (BitVec 8)) (offset : Nat) (v : BitVec 256) : List (BitVec 8) :=
  (List.range dst.length).map fun j =>
    if offset ≤ j ∧ j < offset + 32 then laneOf 8 v (j - offset) else dst[j]!

/-- `store_i16` / `store_u16`: `dst` with elements `16 i .. 16 i + 16` replaced. -/
def storeW16 (dst : List (BitVec 16)) (i : Nat) (v : BitVec 256) : List (BitVec 16) :=
  (List.range dst.length).map fun j =>
    if 16 * i ≤ j ∧ j < 16 * i + 16 then laneOf 16 v (j - 16 * i) else dst[j]!

/-- `store_i32`: `dst` with elements `8 i .. 8 i + 8` replaced. -/
def storeW32 (dst : List (BitVec 32)) (i : Nat) (v : BitVec 256) : List (BitVec 32) :=
  (List.range dst.length).map fun j =>
    if 8 * i ≤ j ∧ j < 8 * i + 8 then laneOf 32 v (j - 8 * i) else dst[j]!

end Model

/-! ## The models agree with the axioms

Each theorem below says the axiom determines the result's 256 bits exactly, and that they are
the model's.  These are the statements the correspondence proofs actually use — a whole-register
equation rewrites, a per-lane conjunction does not — and they are what makes the differential
test in `SpecTests/Avx2/` a test *of the axioms*.

Every proof is the same three steps: take the axiom's witness, apply the lane-to-word bridge
from `Lanes.lean`, and evaluate the model's lane at the index.  Where the axiom quantifies over
`(h, k)` and the model over a flat index, `omega` reconciles them. -/

noncomputable section

/-! ### Constants and bitwise -/

theorem set1_epi16_model (a : Std.I16) :
    ∃ c, set1_epi16 a = ok c ∧ bits c = Model.set1Epi16 a.bv := by
  obtain ⟨c, hc, h⟩ := set1_epi16_spec a
  exact ⟨c, hc, eq_of_lane16_bv fun i hi => by
    simpa [Model.set1Epi16, laneOf_ofLanes16 _ hi] using h i hi⟩

theorem set1_epi32_model (a : Std.I32) :
    ∃ c, set1_epi32 a = ok c ∧ bits c = Model.set1Epi32 a.bv := by
  obtain ⟨c, hc, h⟩ := set1_epi32_spec a
  exact ⟨c, hc, eq_of_lane32_bv fun i hi => by
    simpa [Model.set1Epi32, laneOf_ofLanes32 _ hi] using h i hi⟩

theorem set1_epi64x_model (a : Std.I64) :
    ∃ c, set1_epi64x a = ok c ∧ bits c = Model.set1Epi64x a.bv := by
  obtain ⟨c, hc, h⟩ := set1_epi64x_spec a
  exact ⟨c, hc, eq_of_lane64_bv fun i hi => by
    simpa [Model.set1Epi64x, laneOf_ofLanes64 _ hi] using h i hi⟩

theorem setzero_si256_model :
    ∃ c, setzero_si256 = ok c ∧ bits c = Model.setzeroSi256 := by
  obtain ⟨c, hc, h⟩ := setzero_si256_spec
  exact ⟨c, hc, by simpa [Model.setzeroSi256] using h⟩

theorem cvtsi32_si128_model (a : Std.I32) :
    ∃ c, cvtsi32_si128 a = ok c ∧ bits' c = Model.cvtsi32Si128 a.bv := by
  obtain ⟨c, hc, h⟩ := cvtsi32_si128_spec a
  exact ⟨c, hc, by simpa [Model.cvtsi32Si128] using h⟩

theorem and_si256_model (a b : Vec256) :
    ∃ c, and_si256 a b = ok c ∧ bits c = Model.andSi256 (bits a) (bits b) := by
  obtain ⟨c, hc, h⟩ := and_si256_spec a b
  exact ⟨c, hc, by simpa [Model.andSi256] using h⟩

theorem xor_si256_model (a b : Vec256) :
    ∃ c, xor_si256 a b = ok c ∧ bits c = Model.xorSi256 (bits a) (bits b) := by
  obtain ⟨c, hc, h⟩ := xor_si256_spec a b
  exact ⟨c, hc, by simpa [Model.xorSi256] using h⟩

theorem or_si256_model (a b : Vec256) :
    ∃ c, or_si256 a b = ok c ∧ bits c = Model.orSi256 (bits a) (bits b) := by
  obtain ⟨c, hc, h⟩ := or_si256_spec a b
  exact ⟨c, hc, by simpa [Model.orSi256] using h⟩

theorem andnot_si256_model (a b : Vec256) :
    ∃ c, andnot_si256 a b = ok c ∧ bits c = Model.andnotSi256 (bits a) (bits b) := by
  obtain ⟨c, hc, h⟩ := andnot_si256_spec a b
  exact ⟨c, hc, by simpa [Model.andnotSi256] using h⟩

/-! ### Lane arithmetic -/

theorem add_epi16_model (a b : Vec256) :
    ∃ c, add_epi16 a b = ok c ∧ bits c = Model.addEpi16 (bits a) (bits b) := by
  obtain ⟨c, hc, h⟩ := add_epi16_spec a b
  exact ⟨c, hc, eq_of_lane16_bv fun i hi => by
    simpa [Model.addEpi16, laneOf_ofLanes16 _ hi] using h i hi⟩

theorem sub_epi16_model (a b : Vec256) :
    ∃ c, sub_epi16 a b = ok c ∧ bits c = Model.subEpi16 (bits a) (bits b) := by
  obtain ⟨c, hc, h⟩ := sub_epi16_spec a b
  exact ⟨c, hc, eq_of_lane16_bv fun i hi => by
    simpa [Model.subEpi16, laneOf_ofLanes16 _ hi] using h i hi⟩

theorem add_epi32_model (a b : Vec256) :
    ∃ c, add_epi32 a b = ok c ∧ bits c = Model.addEpi32 (bits a) (bits b) := by
  obtain ⟨c, hc, h⟩ := add_epi32_spec a b
  exact ⟨c, hc, eq_of_lane32_bv fun i hi => by
    simpa [Model.addEpi32, laneOf_ofLanes32 _ hi] using h i hi⟩

theorem sub_epi32_model (a b : Vec256) :
    ∃ c, sub_epi32 a b = ok c ∧ bits c = Model.subEpi32 (bits a) (bits b) := by
  obtain ⟨c, hc, h⟩ := sub_epi32_spec a b
  exact ⟨c, hc, eq_of_lane32_bv fun i hi => by
    simpa [Model.subEpi32, laneOf_ofLanes32 _ hi] using h i hi⟩

theorem mullo_epi16_model (a b : Vec256) :
    ∃ c, mullo_epi16 a b = ok c ∧ bits c = Model.mulloEpi16 (bits a) (bits b) := by
  obtain ⟨c, hc, h⟩ := mullo_epi16_spec a b
  exact ⟨c, hc, eq_of_lane16_bv fun i hi => by
    simpa [Model.mulloEpi16, laneOf_ofLanes16 _ hi] using h i hi⟩

theorem mulhi_epi16_model (a b : Vec256) :
    ∃ c, mulhi_epi16 a b = ok c ∧ bits c = Model.mulhiEpi16 (bits a) (bits b) := by
  obtain ⟨c, hc, h⟩ := mulhi_epi16_spec a b
  exact ⟨c, hc, eq_of_lane16_bv fun i hi => by
    simpa [Model.mulhiEpi16, laneOf_ofLanes16 _ hi] using h i hi⟩

theorem mullo_epi32_model (a b : Vec256) :
    ∃ c, mullo_epi32 a b = ok c ∧ bits c = Model.mulloEpi32 (bits a) (bits b) := by
  obtain ⟨c, hc, h⟩ := mullo_epi32_spec a b
  exact ⟨c, hc, eq_of_lane32_bv fun i hi => by
    simpa [Model.mulloEpi32, laneOf_ofLanes32 _ hi] using h i hi⟩

theorem cmpgt_epi32_model (a b : Vec256) :
    ∃ c, cmpgt_epi32 a b = ok c ∧ bits c = Model.cmpgtEpi32 (bits a) (bits b) := by
  obtain ⟨c, hc, h⟩ := cmpgt_epi32_spec a b
  exact ⟨c, hc, eq_of_lane32_bv fun i hi => by
    simpa [Model.cmpgtEpi32, laneOf_ofLanes32 _ hi] using h i hi⟩

/-! ### Shifts -/

theorem srai_epi16_model (IMM : Std.I32) (a : Vec256) (hIMM : 0 ≤ IMM.val) :
    ∃ c, srai_epi16 IMM a = ok c ∧ bits c = Model.sraiEpi16 IMM.val.toNat (bits a) := by
  obtain ⟨c, hc, h⟩ := srai_epi16_spec IMM a hIMM
  exact ⟨c, hc, eq_of_lane16_bv fun i hi => by
    simpa [Model.sraiEpi16, laneOf_ofLanes16 _ hi] using h i hi⟩

theorem srai_epi32_model (IMM : Std.I32) (a : Vec256) (hIMM : 0 ≤ IMM.val) :
    ∃ c, srai_epi32 IMM a = ok c ∧ bits c = Model.sraiEpi32 IMM.val.toNat (bits a) := by
  obtain ⟨c, hc, h⟩ := srai_epi32_spec IMM a hIMM
  exact ⟨c, hc, eq_of_lane32_bv fun i hi => by
    simpa [Model.sraiEpi32, laneOf_ofLanes32 _ hi] using h i hi⟩

theorem srli_epi16_model (IMM : Std.I32) (a : Vec256) (hIMM : 0 ≤ IMM.val) :
    ∃ c, srli_epi16 IMM a = ok c ∧ bits c = Model.srliEpi16 IMM.val.toNat (bits a) := by
  obtain ⟨c, hc, h⟩ := srli_epi16_spec IMM a hIMM
  exact ⟨c, hc, eq_of_lane16_bv fun i hi => by
    simpa [Model.srliEpi16, laneOf_ofLanes16 _ hi] using h i hi⟩

theorem slli_epi32_model (IMM : Std.I32) (a : Vec256) (hIMM : 0 ≤ IMM.val) :
    ∃ c, slli_epi32 IMM a = ok c ∧ bits c = Model.slliEpi32 IMM.val.toNat (bits a) := by
  obtain ⟨c, hc, h⟩ := slli_epi32_spec IMM a hIMM
  exact ⟨c, hc, eq_of_lane32_bv fun i hi => by
    simpa [Model.slliEpi32, laneOf_ofLanes32 _ hi] using h i hi⟩

theorem slli_epi64_model (IMM : Std.I32) (a : Vec256) (hIMM : 0 ≤ IMM.val) :
    ∃ c, slli_epi64 IMM a = ok c ∧ bits c = Model.slliEpi64 IMM.val.toNat (bits a) := by
  obtain ⟨c, hc, h⟩ := slli_epi64_spec IMM a hIMM
  exact ⟨c, hc, eq_of_lane64_bv fun i hi => by
    simpa [Model.slliEpi64, laneOf_ofLanes64 _ hi] using h i hi⟩

theorem srli_epi64_model (IMM : Std.I32) (a : Vec256) (hIMM : 0 ≤ IMM.val) :
    ∃ c, srli_epi64 IMM a = ok c ∧ bits c = Model.srliEpi64 IMM.val.toNat (bits a) := by
  obtain ⟨c, hc, h⟩ := srli_epi64_spec IMM a hIMM
  exact ⟨c, hc, eq_of_lane64_bv fun i hi => by
    simpa [Model.srliEpi64, laneOf_ofLanes64 _ hi] using h i hi⟩

theorem srl_epi16_model (a : Vec256) (count : Vec128) :
    ∃ c, srl_epi16 a count = ok c ∧ bits c = Model.srlEpi16 (bits a) (bits' count) := by
  obtain ⟨c, hc, h⟩ := srl_epi16_spec a count
  exact ⟨c, hc, eq_of_lane16_bv fun i hi => by
    simpa [Model.srlEpi16, laneOf_ofLanes16 _ hi] using h i hi⟩

theorem srlv_epi32_model (a counts : Vec256) :
    ∃ c, srlv_epi32 a counts = ok c ∧ bits c = Model.srlvEpi32 (bits a) (bits counts) := by
  obtain ⟨c, hc, h⟩ := srlv_epi32_spec a counts
  exact ⟨c, hc, eq_of_lane32_bv fun i hi => by
    simpa [Model.srlvEpi32, laneOf_ofLanes32 _ hi] using h i hi⟩

/-! ### Shuffles, packs and lane surgery

These are the ones where the axiom's `(h, k)` decomposition and the model's flat lane index have
to be reconciled: the axiom fixes lane `16 * h + j`, the model computes lane `i`, and the two
meet at `h = i / 16`, `j = i % 16`. -/

theorem shuffle_epi8_model (a b : Vec256) :
    ∃ c, shuffle_epi8 a b = ok c ∧ bits c = Model.shuffleEpi8 (bits a) (bits b) := by
  obtain ⟨c, hc, h⟩ := shuffle_epi8_spec a b
  refine ⟨c, hc, eq_of_lane8_bv fun i hi => ?_⟩
  have hsplit : 16 * (i / 16) + i % 16 = i := by omega
  have := h (i / 16) (by omega) (i % 16) (by omega)
  rw [hsplit] at this
  simpa [Model.shuffleEpi8, laneOf_ofLanes8 _ hi] using this

theorem unpacklo_epi16_model (a b : Vec256) :
    ∃ c, unpacklo_epi16 a b = ok c ∧ bits c = Model.unpackloEpi16 (bits a) (bits b) := by
  obtain ⟨c, hc, h⟩ := unpacklo_epi16_spec a b
  refine ⟨c, hc, eq_of_lane16_bv fun i hi => ?_⟩
  obtain ⟨h₀, h₁⟩ := h (i / 8) (by omega) (i % 8 / 2) (by omega)
  by_cases he : i % 2 = 0
  · have hix : 8 * (i / 8) + 2 * (i % 8 / 2) = i := by omega
    rw [hix] at h₀
    simpa [Model.unpackloEpi16, laneOf_ofLanes16 _ hi, he] using h₀
  · have hix : 8 * (i / 8) + 2 * (i % 8 / 2) + 1 = i := by omega
    rw [hix] at h₁
    simpa [Model.unpackloEpi16, laneOf_ofLanes16 _ hi, he] using h₁

theorem unpackhi_epi16_model (a b : Vec256) :
    ∃ c, unpackhi_epi16 a b = ok c ∧ bits c = Model.unpackhiEpi16 (bits a) (bits b) := by
  obtain ⟨c, hc, h⟩ := unpackhi_epi16_spec a b
  refine ⟨c, hc, eq_of_lane16_bv fun i hi => ?_⟩
  obtain ⟨h₀, h₁⟩ := h (i / 8) (by omega) (i % 8 / 2) (by omega)
  by_cases he : i % 2 = 0
  · have hix : 8 * (i / 8) + 2 * (i % 8 / 2) = i := by omega
    rw [hix] at h₀
    simpa [Model.unpackhiEpi16, laneOf_ofLanes16 _ hi, he] using h₀
  · have hix : 8 * (i / 8) + 2 * (i % 8 / 2) + 1 = i := by omega
    rw [hix] at h₁
    simpa [Model.unpackhiEpi16, laneOf_ofLanes16 _ hi, he] using h₁

theorem unpacklo_epi32_model (a b : Vec256) :
    ∃ c, unpacklo_epi32 a b = ok c ∧ bits c = Model.unpackloEpi32 (bits a) (bits b) := by
  obtain ⟨c, hc, h⟩ := unpacklo_epi32_spec a b
  refine ⟨c, hc, eq_of_lane32_bv fun i hi => ?_⟩
  obtain ⟨h₀, h₁⟩ := h (i / 4) (by omega) (i % 4 / 2) (by omega)
  by_cases he : i % 2 = 0
  · have hix : 4 * (i / 4) + 2 * (i % 4 / 2) = i := by omega
    rw [hix] at h₀
    simpa [Model.unpackloEpi32, laneOf_ofLanes32 _ hi, he] using h₀
  · have hix : 4 * (i / 4) + 2 * (i % 4 / 2) + 1 = i := by omega
    rw [hix] at h₁
    simpa [Model.unpackloEpi32, laneOf_ofLanes32 _ hi, he] using h₁

theorem unpackhi_epi32_model (a b : Vec256) :
    ∃ c, unpackhi_epi32 a b = ok c ∧ bits c = Model.unpackhiEpi32 (bits a) (bits b) := by
  obtain ⟨c, hc, h⟩ := unpackhi_epi32_spec a b
  refine ⟨c, hc, eq_of_lane32_bv fun i hi => ?_⟩
  obtain ⟨h₀, h₁⟩ := h (i / 4) (by omega) (i % 4 / 2) (by omega)
  by_cases he : i % 2 = 0
  · have hix : 4 * (i / 4) + 2 * (i % 4 / 2) = i := by omega
    rw [hix] at h₀
    simpa [Model.unpackhiEpi32, laneOf_ofLanes32 _ hi, he] using h₀
  · have hix : 4 * (i / 4) + 2 * (i % 4 / 2) + 1 = i := by omega
    rw [hix] at h₁
    simpa [Model.unpackhiEpi32, laneOf_ofLanes32 _ hi, he] using h₁

theorem unpacklo_epi64_model (a b : Vec256) :
    ∃ c, unpacklo_epi64 a b = ok c ∧ bits c = Model.unpackloEpi64 (bits a) (bits b) := by
  obtain ⟨c, hc, h⟩ := unpacklo_epi64_spec a b
  refine ⟨c, hc, eq_of_lane64_bv fun i hi => ?_⟩
  obtain ⟨h₀, h₁⟩ := h (i / 2) (by omega)
  by_cases he : i % 2 = 0
  · have hix : 2 * (i / 2) = i := by omega
    rw [hix] at h₀
    simpa [Model.unpackloEpi64, laneOf_ofLanes64 _ hi, he, hix] using h₀
  · have hix : 2 * (i / 2) + 1 = i := by omega
    rw [hix] at h₁
    simpa [Model.unpackloEpi64, laneOf_ofLanes64 _ hi, he, hix] using h₁

theorem unpackhi_epi64_model (a b : Vec256) :
    ∃ c, unpackhi_epi64 a b = ok c ∧ bits c = Model.unpackhiEpi64 (bits a) (bits b) := by
  obtain ⟨c, hc, h⟩ := unpackhi_epi64_spec a b
  refine ⟨c, hc, eq_of_lane64_bv fun i hi => ?_⟩
  obtain ⟨h₀, h₁⟩ := h (i / 2) (by omega)
  by_cases he : i % 2 = 0
  · have hix : 2 * (i / 2) = i := by omega
    rw [hix] at h₀
    simpa [Model.unpackhiEpi64, laneOf_ofLanes64 _ hi, he, hix] using h₀
  · have hix : 2 * (i / 2) + 1 = i := by omega
    rw [hix] at h₁
    simpa [Model.unpackhiEpi64, laneOf_ofLanes64 _ hi, he, hix] using h₁

theorem selectHalf_eq (a b : Vec256) (n : Nat) :
    selectHalf a b n = Model.selectHalfBV (bits a) (bits b) n := by
  match n with
  | 0 => rfl
  | 1 => rfl
  | 2 => rfl
  | _ + 3 => rfl

theorem permute2x128_si256_model (IMM : Std.I32) (a b : Vec256) :
    ∃ c, permute2x128_si256 IMM a b = ok c ∧
      bits c = Model.permute2x128Si256 IMM.bv (bits a) (bits b) := by
  obtain ⟨c, hc, h⟩ := permute2x128_si256_spec IMM a b
  refine ⟨c, hc, eq_of_lane128_bv fun i hi => ?_⟩
  simpa [Model.permute2x128Si256, laneOf_ofLanes128 _ hi, selectHalf_eq] using h i hi

theorem permute4x64_epi64_model (IMM : Std.I32) (a : Vec256) :
    ∃ c, permute4x64_epi64 IMM a = ok c ∧
      bits c = Model.permute4x64Epi64 IMM.bv (bits a) := by
  obtain ⟨c, hc, h⟩ := permute4x64_epi64_spec IMM a
  exact ⟨c, hc, eq_of_lane64_bv fun i hi => by
    simpa [Model.permute4x64Epi64, laneOf_ofLanes64 _ hi] using h i hi⟩

theorem packs_epi32_model (a b : Vec256) :
    ∃ c, packs_epi32 a b = ok c ∧ bits c = Model.packsEpi32 (bits a) (bits b) := by
  obtain ⟨c, hc, h⟩ := packs_epi32_spec a b
  refine ⟨c, hc, eq_of_lane16_bv fun i hi => ?_⟩
  rcases Nat.lt_or_ge (i % 8) 4 with hlt | hge
  · obtain ⟨h₀, -⟩ := h (i / 8) (by omega) (i % 8) hlt
    rw [show 8 * (i / 8) + i % 8 = i by omega] at h₀
    simpa [Model.packsEpi32, laneOf_ofLanes16 _ hi, hlt] using h₀
  · obtain ⟨-, h₁⟩ := h (i / 8) (by omega) (i % 8 - 4) (by omega)
    rw [show 8 * (i / 8) + 4 + (i % 8 - 4) = i by omega] at h₁
    simpa [Model.packsEpi32, laneOf_ofLanes16 _ hi, Nat.not_lt.mpr hge] using h₁

theorem packus_epi32_model (a b : Vec256) :
    ∃ c, packus_epi32 a b = ok c ∧ bits c = Model.packusEpi32 (bits a) (bits b) := by
  obtain ⟨c, hc, h⟩ := packus_epi32_spec a b
  refine ⟨c, hc, eq_of_lane16_bv fun i hi => ?_⟩
  rcases Nat.lt_or_ge (i % 8) 4 with hlt | hge
  · obtain ⟨h₀, -⟩ := h (i / 8) (by omega) (i % 8) hlt
    rw [show 8 * (i / 8) + i % 8 = i by omega] at h₀
    simpa [Model.packusEpi32, laneOf_ofLanes16 _ hi, hlt] using h₀
  · obtain ⟨-, h₁⟩ := h (i / 8) (by omega) (i % 8 - 4) (by omega)
    rw [show 8 * (i / 8) + 4 + (i % 8 - 4) = i by omega] at h₁
    simpa [Model.packusEpi32, laneOf_ofLanes16 _ hi, Nat.not_lt.mpr hge] using h₁

theorem cvtepu16_epi32_model (a : Vec128) :
    ∃ c, cvtepu16_epi32 a = ok c ∧ bits c = Model.cvtepu16Epi32 (bits' a) := by
  obtain ⟨c, hc, h⟩ := cvtepu16_epi32_spec a
  exact ⟨c, hc, eq_of_lane32_bv fun i hi => by
    simpa [Model.cvtepu16Epi32, laneOf_ofLanes32 _ hi] using h i hi⟩

theorem castsi256_si128_model (a : Vec256) :
    ∃ c, castsi256_si128 a = ok c ∧ bits' c = Model.castsi256Si128 (bits a) := by
  obtain ⟨c, hc, h⟩ := castsi256_si128_spec a
  exact ⟨c, hc, by simpa [Model.castsi256Si128] using h⟩

theorem extracti128_si256_model (IMM : Std.I32) (a : Vec256) (hIMM : 0 ≤ IMM.val) :
    ∃ c, extracti128_si256 IMM a = ok c ∧
      bits' c = Model.extracti128Si256 IMM.val.toNat (bits a) := by
  obtain ⟨c, hc, h⟩ := extracti128_si256_spec IMM a hIMM
  exact ⟨c, hc, by simpa [Model.extracti128Si256] using h⟩

theorem broadcastsi128_si256_model (a : Vec128) :
    ∃ c, broadcastsi128_si256 a = ok c ∧ bits c = Model.broadcastsi128Si256 (bits' a) := by
  obtain ⟨c, hc, h⟩ := broadcastsi128_si256_spec a
  exact ⟨c, hc, eq_of_lane128_bv fun i hi => by
    simpa [Model.broadcastsi128Si256, laneOf_ofLanes128 _ hi] using h i hi⟩

end

end Kopis.Avx2
