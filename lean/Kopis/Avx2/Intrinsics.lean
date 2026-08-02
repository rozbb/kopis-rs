import ExtractedRustAvx2
/-!
# AVX2 intrinsics: the assumed semantics

This file is the **entire trusted base** the AVX2 backend adds to the Kopis proofs. Everything
in `src/backend/avx2/` other than `intrinsics.rs` and `cpu.rs` is extracted to Lean by
`../extract_rust_to_lean.sh` and proved; those two modules are extracted *opaquely*, which
aeneas emits as the uninterpreted constants

    axiom RustKopisAvx2.backend.avx2.intrinsics.Vec256 : Type
    axiom RustKopisAvx2.backend.avx2.intrinsics.add_epi16 : Vec256 → Vec256 → Result Vec256
    ...

and this file is what gives them meaning. Nothing below is proved, and nothing below is checked
against silicon — each axiom is a claim about what an instruction does, to be read against the
Intel SDM (Vol. 2, the `VPADDW` / `VPMULHW` / `VPSHUFB` / … entries) and against the one-line
wrapper it corresponds to in `src/backend/avx2/intrinsics.rs`. **This file is the review
surface.** An axiom that is wrong here makes every AVX2 theorem worthless, silently.

The ground truth is bits: `bits : Vec256 → BitVec 256` is the 256-bit word a vector register
holds, and each axiom fixes the result's bits in terms of the arguments'. Lane views
(`lane16`, `lane32`, …) are *derived* — they are `BitVec.extractLsb'` on that word, not separate
assumptions — so an axiom stated on 16-bit lanes and one stated on 32-bit lanes are talking
about the same object, which is what the transpose and pack sequences need.

Each axiom is stated as `∃ c, f args = ok c ∧ P c`: the shape aeneas's `progress` tactic
consumes, and the shape that says "this call succeeds, and here is what it returns". For the
memory accessors the equation is conditional on the bound the Rust wrapper asserts; outside
that bound the wrapper panics, and nothing is claimed.

## The CPU probe

`cpu::available` is opaque for the same reason as the intrinsics, but nothing about *what it
returns* is assumed: every dispatch point is proved on both branches, so the result holds
whatever CPUID says. The only thing assumed is that the probe terminates without failing —
`available_ok` below — which is far weaker than "it correctly detects AVX2".

## What is *not* assumed here

* Any relation between this model and the portable code. That is what the correspondence
  proofs are for.

## Prior art

The lane-level specifications for the arithmetic ops follow libcrux's
`libcrux/crates/utils/intrinsics/src/avx2_extract.rs` and the bit-level ones its
`fstar-helpers/fstar-bitvec/BitVec.Intrinsics.fsti`. The statements here are written fresh
against the SDM and the shuffle/permute/transpose family — which libcrux does not model — is
ours; but the architecture is theirs, and where they and we agree that is not independent
evidence.
-/
namespace Kopis.Avx2

open Aeneas Std Result

/- The extracted opaque constants. Every unqualified `Vec256`, `add_epi16`, `load_i16`, … below
is one of them — the aeneas output for `src/backend/avx2/intrinsics.rs`, in namespace
`RustKopisAvx2.backend.avx2.intrinsics`. Nothing else is opened, so anything unqualified and
lower-case is an extracted intrinsic. -/
open RustKopisAvx2.backend.avx2.intrinsics

/- The bit view below is an axiom, hence noncomputable, and so is everything phrased through
   it. -/
noncomputable section

/-! ## The bit view

`Vec256` and `Vec128` are `#[repr(transparent)]` newtypes over `__m256i` / `__m128i`, which are
exactly a 256- and a 128-bit word. `bits` / `bits'` read that word; injectivity says the word is
*all* there is to a register, so two vectors with the same bits are the same vector. -/

axiom bits : Vec256 → BitVec 256
axiom bits' : Vec128 → BitVec 128

/-- The width guard `(1..=13).contains(&bits)` terminates and does not fail.  `contains` is a
`core` comparison that charon does not lower, so aeneas emits it uninterpreted; like
`available_ok` this assumes only that it *returns*, not what it returns — both outcomes are
proved.  It appears nowhere in the serial extraction: the guard is part of the AVX2 dispatch.  -/
axiom rangeInclusive_contains_ok {Idx U : Type}
    (i1 : core.cmp.PartialOrd Idx Idx) (i2 : core.cmp.PartialOrd Idx U)
    (i3 : core.cmp.PartialOrd U Idx)
    (r : core.ops.range.RangeInclusive Idx) (x : U) :
    ∃ b, RustKopisAvx2.core.ops.range.RangeInclusive.contains i1 i2 i3 r x = ok b

/-- The CPU probe terminates and does not fail.  Nothing is assumed about *which* answer it
gives: every dispatch point is proved on both branches.  This is the whole of `cpu::available`'s
contribution to the trust base. -/
axiom available_ok : ∃ b, RustKopisAvx2.backend.avx2.cpu.available = ok b

axiom bits_inj {a b : Vec256} : bits a = bits b → a = b
axiom bits'_inj {a b : Vec128} : bits' a = bits' b → a = b

/-- Lane `i` of width `w`, counting from the least significant end — the lane numbering the
Intel manuals use, so `lane16 v 0` is `v[15:0]`. -/
def laneOf (w : Nat) {n : Nat} (x : BitVec n) (i : Nat) : BitVec w :=
  BitVec.extractLsb' (w * i) w x

@[reducible] def lane8 (v : Vec256) (i : Nat) : BitVec 8 := laneOf 8 (bits v) i
@[reducible] def lane16 (v : Vec256) (i : Nat) : BitVec 16 := laneOf 16 (bits v) i
@[reducible] def lane32 (v : Vec256) (i : Nat) : BitVec 32 := laneOf 32 (bits v) i
@[reducible] def lane64 (v : Vec256) (i : Nat) : BitVec 64 := laneOf 64 (bits v) i

/-- The `i`th 128-bit half. Most AVX2 shuffles act within a half rather than across the
register, which is what makes them cheap and what makes the transpose network non-obvious. -/
@[reducible] def half (v : Vec256) (i : Nat) : BitVec 128 := laneOf 128 (bits v) i

@[reducible] def lane8' (v : Vec128) (i : Nat) : BitVec 8 := laneOf 8 (bits' v) i
@[reducible] def lane16' (v : Vec128) (i : Nat) : BitVec 16 := laneOf 16 (bits' v) i

/-! ## Saturation

The two packing instructions differ only in which saturation they apply to their signed 32-bit
sources: `vpackssdw` clamps to the `i16` range, `vpackusdw` to the `u16` range. -/

/-- Signed 32→16 saturation, as `vpackssdw` does it. -/
def satS (x : BitVec 32) : BitVec 16 :=
  if x.toInt < -32768 then 0x8000#16
  else if 32767 < x.toInt then 0x7FFF#16
  else BitVec.setWidth 16 x

/-- Unsigned 32→16 saturation of a *signed* source, as `vpackusdw` does it: negatives clamp to
zero. -/
def satU (x : BitVec 32) : BitVec 16 :=
  if x.toInt < 0 then 0#16
  else if 65535 < x.toInt then 0xFFFF#16
  else BitVec.setWidth 16 x

/-! ## Constants and bitwise -/

/-- `vpbroadcastw` — every 16-bit lane is `a`. -/
axiom set1_epi16_spec (a : Std.I16) :
    ∃ c, set1_epi16 a = ok c ∧ ∀ i < 16, lane16 c i = a.bv

/-- `vpbroadcastd` — every 32-bit lane is `a`. -/
axiom set1_epi32_spec (a : Std.I32) :
    ∃ c, set1_epi32 a = ok c ∧ ∀ i < 8, lane32 c i = a.bv

/-- `vpxor` against itself — all 256 bits zero. -/
axiom setzero_si256_spec :
    ∃ c, setzero_si256 = ok c ∧ bits c = 0#256

/-- `vmovd` — `a` in the low 32 bits, the upper 96 zeroed. -/
axiom cvtsi32_si128_spec (a : Std.I32) :
    ∃ c, cvtsi32_si128 a = ok c ∧ bits' c = BitVec.setWidth 128 a.bv

/-- `vpand` — bitwise, all 256 bits at once. -/
axiom and_si256_spec (a b : Vec256) :
    ∃ c, and_si256 a b = ok c ∧ bits c = bits a &&& bits b

/-! ## Lane arithmetic

All four of these wrap rather than saturate, which is what `BitVec`'s `+`, `-` and `*` do. -/

/-- `vpaddw` — 16 independent wrapping 16-bit additions. -/
axiom add_epi16_spec (a b : Vec256) :
    ∃ c, add_epi16 a b = ok c ∧ ∀ i < 16, lane16 c i = lane16 a i + lane16 b i

/-- `vpsubw` — 16 independent wrapping 16-bit subtractions. -/
axiom sub_epi16_spec (a b : Vec256) :
    ∃ c, sub_epi16 a b = ok c ∧ ∀ i < 16, lane16 c i = lane16 a i - lane16 b i

/-- `vpaddd` — 8 independent wrapping 32-bit additions. -/
axiom add_epi32_spec (a b : Vec256) :
    ∃ c, add_epi32 a b = ok c ∧ ∀ i < 8, lane32 c i = lane32 a i + lane32 b i

/-- `vpsubd` — 8 independent wrapping 32-bit subtractions. -/
axiom sub_epi32_spec (a b : Vec256) :
    ∃ c, sub_epi32 a b = ok c ∧ ∀ i < 8, lane32 c i = lane32 a i - lane32 b i

/-- `vpmullw` — the *low* half of each 16×16 product. Signed and unsigned agree on the low
half, so no sign extension appears here. -/
axiom mullo_epi16_spec (a b : Vec256) :
    ∃ c, mullo_epi16 a b = ok c ∧ ∀ i < 16, lane16 c i = lane16 a i * lane16 b i

/-- `vpmulhw` — the *high* half of each **signed** 16×16 product. This one is the whole reason
the backend exists, and the sign extension is the part to check. -/
axiom mulhi_epi16_spec (a b : Vec256) :
    ∃ c, mulhi_epi16 a b = ok c ∧ ∀ i < 16,
      lane16 c i =
        BitVec.extractLsb' 16 16
          ((lane16 a i).signExtend 32 * (lane16 b i).signExtend 32)

/-- `vpmulld` — the low half of each 32×32 product. -/
axiom mullo_epi32_spec (a b : Vec256) :
    ∃ c, mullo_epi32 a b = ok c ∧ ∀ i < 8, lane32 c i = lane32 a i * lane32 b i

/-- `vpcmpgtd` — signed 32-bit `a > b`, as an all-ones / all-zeros mask per lane. -/
axiom cmpgt_epi32_spec (a b : Vec256) :
    ∃ c, cmpgt_epi32 a b = ok c ∧ ∀ i < 8,
      lane32 c i = if BitVec.slt (lane32 b i) (lane32 a i) then BitVec.allOnes 32 else 0#32

/-! ## Shifts

The immediate is an ordinary argument after extraction (aeneas turns the const generic into a
leading parameter), so each axiom quantifies over it, with the non-negativity the Rust
`static_assert_uimm_bits!` guarantees as a hypothesis. Counts at or above the lane width are
not undefined: the logical shifts produce zero and the arithmetic ones produce the sign, which
is exactly what `BitVec`'s `>>>`, `<<<` and `sshiftRight` do. -/

/-- `vpsraw` by an immediate — arithmetic, so lanes fill with their sign bit. -/
axiom srai_epi16_spec (IMM : Std.I32) (a : Vec256) (h : 0 ≤ IMM.val) :
    ∃ c, srai_epi16 IMM a = ok c ∧ ∀ i < 16,
      lane16 c i = (lane16 a i).sshiftRight IMM.val.toNat

/-- `vpsrad` by an immediate. -/
axiom srai_epi32_spec (IMM : Std.I32) (a : Vec256) (h : 0 ≤ IMM.val) :
    ∃ c, srai_epi32 IMM a = ok c ∧ ∀ i < 8,
      lane32 c i = (lane32 a i).sshiftRight IMM.val.toNat

/-- `vpsrlw` by an immediate — logical. -/
axiom srli_epi16_spec (IMM : Std.I32) (a : Vec256) (h : 0 ≤ IMM.val) :
    ∃ c, srli_epi16 IMM a = ok c ∧ ∀ i < 16,
      lane16 c i = lane16 a i >>> IMM.val.toNat

/-- `vpslld` by an immediate. -/
axiom slli_epi32_spec (IMM : Std.I32) (a : Vec256) (h : 0 ≤ IMM.val) :
    ∃ c, slli_epi32 IMM a = ok c ∧ ∀ i < 8,
      lane32 c i = lane32 a i <<< IMM.val.toNat

/-- `vpsrlw` by a register — the count is the whole low *64* bits of `count`, not a lane, so a
count of 2^16 is a count of 2^16 (and shifts everything out) rather than a count of 0. -/
axiom srl_epi16_spec (a : Vec256) (count : Vec128) :
    ∃ c, srl_epi16 a count = ok c ∧ ∀ i < 16,
      lane16 c i = lane16 a i >>> (laneOf 64 (bits' count) 0).toNat

/-- `vpsrlvd` — per-lane variable logical shift. -/
axiom srlv_epi32_spec (a counts : Vec256) :
    ∃ c, srlv_epi32 a counts = ok c ∧ ∀ i < 8,
      lane32 c i = lane32 a i >>> (lane32 counts i).toNat

/-! ## Shuffles, packs and lane surgery

This is the part with no prior model to borrow, and the part `transpose16` is built out of.
Every instruction here except `vperm2i128`, `vpermq` and `vbroadcasti128` acts on each 128-bit
half independently — the `h < 2` quantifier below is that halving, and forgetting it is the
classic AVX2 error. -/

/-- `vpshufb` — byte permute *within each half*, with the high bit of a control byte zeroing
its destination. The control index is taken mod 16 (`& 0x0F`), so it can only ever name a byte
of its own half. -/
axiom shuffle_epi8_spec (a b : Vec256) :
    ∃ c, shuffle_epi8 a b = ok c ∧ ∀ h < 2, ∀ j < 16,
      lane8 c (16 * h + j) =
        if (lane8 b (16 * h + j)).getLsbD 7 then 0#8
        else lane8 a (16 * h + (lane8 b (16 * h + j) &&& 0x0F#8).toNat)

/-- `vpunpcklwd` — interleave the low four 16-bit lanes of each half, `a` first. -/
axiom unpacklo_epi16_spec (a b : Vec256) :
    ∃ c, unpacklo_epi16 a b = ok c ∧ ∀ h < 2, ∀ k < 4,
      lane16 c (8 * h + 2 * k) = lane16 a (8 * h + k) ∧
      lane16 c (8 * h + 2 * k + 1) = lane16 b (8 * h + k)

/-- `vpunpckhwd` — the same for the high four 16-bit lanes of each half. -/
axiom unpackhi_epi16_spec (a b : Vec256) :
    ∃ c, unpackhi_epi16 a b = ok c ∧ ∀ h < 2, ∀ k < 4,
      lane16 c (8 * h + 2 * k) = lane16 a (8 * h + 4 + k) ∧
      lane16 c (8 * h + 2 * k + 1) = lane16 b (8 * h + 4 + k)

/-- `vpunpckldq` — interleave the low two 32-bit lanes of each half. -/
axiom unpacklo_epi32_spec (a b : Vec256) :
    ∃ c, unpacklo_epi32 a b = ok c ∧ ∀ h < 2, ∀ k < 2,
      lane32 c (4 * h + 2 * k) = lane32 a (4 * h + k) ∧
      lane32 c (4 * h + 2 * k + 1) = lane32 b (4 * h + k)

/-- `vpunpckhdq` — the same for the high two 32-bit lanes of each half. -/
axiom unpackhi_epi32_spec (a b : Vec256) :
    ∃ c, unpackhi_epi32 a b = ok c ∧ ∀ h < 2, ∀ k < 2,
      lane32 c (4 * h + 2 * k) = lane32 a (4 * h + 2 + k) ∧
      lane32 c (4 * h + 2 * k + 1) = lane32 b (4 * h + 2 + k)

/-- `vpunpcklqdq` — the low 64-bit lane of each half of `a`, then that of `b`. -/
axiom unpacklo_epi64_spec (a b : Vec256) :
    ∃ c, unpacklo_epi64 a b = ok c ∧ ∀ h < 2,
      lane64 c (2 * h) = lane64 a (2 * h) ∧
      lane64 c (2 * h + 1) = lane64 b (2 * h)

/-- `vpunpckhqdq` — the high 64-bit lane of each half of `a`, then that of `b`. -/
axiom unpackhi_epi64_spec (a b : Vec256) :
    ∃ c, unpackhi_epi64 a b = ok c ∧ ∀ h < 2,
      lane64 c (2 * h) = lane64 a (2 * h + 1) ∧
      lane64 c (2 * h + 1) = lane64 b (2 * h + 1)

/-- The four halves `vperm2i128` selects between: 0 and 1 are `a`'s, 2 and 3 are `b`'s. -/
def selectHalf (a b : Vec256) : Nat → BitVec 128
  | 0 => half a 0
  | 1 => half a 1
  | 2 => half b 0
  | _ => half b 1

/-- `vperm2i128` — each 128-bit half of the result is chosen by a nibble of `IMM`: bits 0-1 (or
4-5) pick one of the four source halves, and bit 3 (or 7) zeroes the destination instead. -/
axiom permute2x128_si256_spec (IMM : Std.I32) (a b : Vec256) :
    ∃ c, permute2x128_si256 IMM a b = ok c ∧ ∀ j < 2,
      half c j =
        if ((IMM.bv >>> (4 * j)) &&& 8#32) ≠ 0#32 then 0#128
        else selectHalf a b (((IMM.bv >>> (4 * j)) &&& 3#32).toNat)

/-- `vpermq` — a full cross-half permutation of the four 64-bit lanes, two `IMM` bits each. -/
axiom permute4x64_epi64_spec (IMM : Std.I32) (a : Vec256) :
    ∃ c, permute4x64_epi64 IMM a = ok c ∧ ∀ i < 4,
      lane64 c i = lane64 a (((IMM.bv >>> (2 * i)) &&& 3#32).toNat)

/-- `vpackssdw` — signed-saturating 32→16 pack. `a`'s lanes fill the low half of each 128-bit
half and `b`'s the high half, which is the interleaving the callers undo with `vpermq`. -/
axiom packs_epi32_spec (a b : Vec256) :
    ∃ c, packs_epi32 a b = ok c ∧ ∀ h < 2, ∀ k < 4,
      lane16 c (8 * h + k) = satS (lane32 a (4 * h + k)) ∧
      lane16 c (8 * h + 4 + k) = satS (lane32 b (4 * h + k))

/-- `vpackusdw` — the same shape, unsigned-saturating. -/
axiom packus_epi32_spec (a b : Vec256) :
    ∃ c, packus_epi32 a b = ok c ∧ ∀ h < 2, ∀ k < 4,
      lane16 c (8 * h + k) = satU (lane32 a (4 * h + k)) ∧
      lane16 c (8 * h + 4 + k) = satU (lane32 b (4 * h + k))

/-- `vpmovzxwd` — the eight 16-bit lanes of a half, *zero*-extended to 32 bits. -/
axiom cvtepu16_epi32_spec (a : Vec128) :
    ∃ c, cvtepu16_epi32 a = ok c ∧ ∀ i < 8,
      lane32 c i = (lane16' a i).setWidth 32

/-- The low half of a register, a no-op at the instruction level. -/
axiom castsi256_si128_spec (a : Vec256) :
    ∃ c, castsi256_si128 a = ok c ∧ bits' c = BitVec.extractLsb' 0 128 (bits a)

/-- `vextracti128` — half `IMM & 1`. -/
axiom extracti128_si256_spec (IMM : Std.I32) (a : Vec256) (h : 0 ≤ IMM.val) :
    ∃ c, extracti128_si256 IMM a = ok c ∧
      bits' c = BitVec.extractLsb' (128 * (IMM.val.toNat % 2)) 128 (bits a)

/-- `vbroadcasti128` — `a` in both halves. -/
axiom broadcastsi128_si256_spec (a : Vec128) :
    ∃ c, broadcastsi128_si256 a = ok c ∧ ∀ j < 2, half c j = bits' a

/-! ## Memory

These are not instructions but the wrappers in `intrinsics.rs`, and their axioms carry the same
bound the wrapper asserts. Each is indexed in whole vectors: `load_i16 a i` reads
`a[16i .. 16i+16]`.

The four `*_of_*` accessors are the ones to read carefully. They are where the crate's
two-blocks-in-one-buffer layout lives: `crate::arithmetic::ntt::NttElem` is `[i32; 256]` that
the AVX2 backend reads as 512 `i16`, and the pointwise accumulator is `[i64; 256]` read as 512
`i32`. The axioms state that reinterpretation as *little-endian*: element `2j` of the narrow
view is the low half of element `j` of the wide one, element `2j+1` the high half. On any
big-endian target these would be wrong — the crate is little-endian-only in this backend, which
is fine because AVX2 is. -/

/-- Loads the 16 `i16` at `src[16i ..]`. -/
axiom load_i16_spec {N : Std.Usize} (src : Array Std.I16 N) (i : Std.Usize)
    (h : 16 * (i.val + 1) ≤ N.val) :
    ∃ c, load_i16 src i = ok c ∧ ∀ k < 16, lane16 c k = (src.val[16 * i.val + k]!).bv

/-- Stores 16 `i16` at `dst[16i ..]`, leaving everything else alone. -/
axiom store_i16_spec {N : Std.Usize} (dst : Array Std.I16 N) (i : Std.Usize) (v : Vec256)
    (h : 16 * (i.val + 1) ≤ N.val) :
    ∃ dst', store_i16 dst i v = ok dst' ∧ ∀ j < N.val,
      (dst'.val[j]!).bv =
        if 16 * i.val ≤ j ∧ j < 16 * i.val + 16 then lane16 v (j - 16 * i.val)
        else (dst.val[j]!).bv

/-- Loads the 16 `u16` at `src[16i ..]`. Same bits as `load_i16`; the element type differs only
in how the rest of the crate reads them. -/
axiom load_u16_spec {N : Std.Usize} (src : Array Std.U16 N) (i : Std.Usize)
    (h : 16 * (i.val + 1) ≤ N.val) :
    ∃ c, load_u16 src i = ok c ∧ ∀ k < 16, lane16 c k = (src.val[16 * i.val + k]!).bv

/-- Stores 16 `u16` at `dst[16i ..]`. -/
axiom store_u16_spec {N : Std.Usize} (dst : Array Std.U16 N) (i : Std.Usize) (v : Vec256)
    (h : 16 * (i.val + 1) ≤ N.val) :
    ∃ dst', store_u16 dst i v = ok dst' ∧ ∀ j < N.val,
      (dst'.val[j]!).bv =
        if 16 * i.val ≤ j ∧ j < 16 * i.val + 16 then lane16 v (j - 16 * i.val)
        else (dst.val[j]!).bv

/-- Loads the 8 `i32` at `src[8i ..]`. -/
axiom load_i32_spec {N : Std.Usize} (src : Array Std.I32 N) (i : Std.Usize)
    (h : 8 * (i.val + 1) ≤ N.val) :
    ∃ c, load_i32 src i = ok c ∧ ∀ k < 8, lane32 c k = (src.val[8 * i.val + k]!).bv

/-- Loads the 32 bytes at `src[32i ..]`. -/
axiom load_u8_spec {N : Std.Usize} (src : Array Std.U8 N) (i : Std.Usize)
    (h : 32 * (i.val + 1) ≤ N.val) :
    ∃ c, load_u8 src i = ok c ∧ ∀ k < 32, lane8 c k = (src.val[32 * i.val + k]!).bv

/-- Loads the 16 bytes at `src[offset ..]` — byte-indexed, because the deserializer reads groups
at multiples of the coefficient width. -/
axiom load_u8x16_spec (src : Aeneas.Std.Slice Std.U8) (offset : Std.Usize)
    (h : offset.val + 16 ≤ src.val.length) :
    ∃ c, load_u8x16 src offset = ok c ∧
      ∀ k < 16, lane8' c k = (src.val[offset.val + k]!).bv

/-- Loads the 16 `i16` at `i16` index `16i` of `src` read as `2N` little-endian `i16`. -/
axiom load_i16_of_i32_spec {N : Std.Usize} (src : Array Std.I32 N) (i : Std.Usize)
    (h : 16 * (i.val + 1) ≤ 2 * N.val) :
    ∃ c, load_i16_of_i32 src i = ok c ∧ ∀ k < 16,
      lane16 c k =
        BitVec.extractLsb' (16 * ((16 * i.val + k) % 2)) 16
          (src.val[(16 * i.val + k) / 2]!).bv

/-- Stores 16 `i16` at `i16` index `16i` of `dst` read as `2N` little-endian `i16`. The store
covers whole `i32` elements — `i16` indices `16i .. 16i+16` are elements `8i .. 8i+8` — so no
element is half-written. -/
axiom store_i16_of_i32_spec {N : Std.Usize} (dst : Array Std.I32 N) (i : Std.Usize) (v : Vec256)
    (h : 16 * (i.val + 1) ≤ 2 * N.val) :
    ∃ dst', store_i16_of_i32 dst i v = ok dst' ∧ ∀ j < N.val,
      (dst'.val[j]!).bv =
        if 8 * i.val ≤ j ∧ j < 8 * i.val + 8 then
          lane16 v (2 * j - 16 * i.val + 1) ++ lane16 v (2 * j - 16 * i.val)
        else (dst.val[j]!).bv

/-- Loads the 8 `i32` at `i32` index `8i` of `src` read as `2N` little-endian `i32`. -/
axiom load_i32_of_i64_spec {N : Std.Usize} (src : Array Std.I64 N) (i : Std.Usize)
    (h : 8 * (i.val + 1) ≤ 2 * N.val) :
    ∃ c, load_i32_of_i64 src i = ok c ∧ ∀ k < 8,
      lane32 c k =
        BitVec.extractLsb' (32 * ((8 * i.val + k) % 2)) 32
          (src.val[(8 * i.val + k) / 2]!).bv

/-- Stores 8 `i32` at `i32` index `8i` of `dst` read as `2N` little-endian `i32`. -/
axiom store_i32_of_i64_spec {N : Std.Usize} (dst : Array Std.I64 N) (i : Std.Usize) (v : Vec256)
    (h : 8 * (i.val + 1) ≤ 2 * N.val) :
    ∃ dst', store_i32_of_i64 dst i v = ok dst' ∧ ∀ j < N.val,
      (dst'.val[j]!).bv =
        if 4 * i.val ≤ j ∧ j < 4 * i.val + 4 then
          lane32 v (2 * j - 8 * i.val + 1) ++ lane32 v (2 * j - 8 * i.val)
        else (dst.val[j]!).bv

end

end Kopis.Avx2
