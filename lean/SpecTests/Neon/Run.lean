import Kopis.Neon.Model
import Lean.Data.Json

/-!
# The NEON intrinsic model, checked against silicon

`Kopis/Neon/Intrinsics.lean` *assumes* what 46 AArch64 instructions do; `Kopis/Neon/Model.lean`
turns each assumption into a computable `BitVec` function and **proves** the two agree — so a
model that matched hardware would leave the axiom in the same position, and a model that did not
would convict it.  This runner is the second half: it replays
`../tests/neon_intrinsics_vectors.jsonl`, which `src/backend/neon/intrinsics_vectors.rs` produced
by executing the real instructions on a real core, through the models and reports any
disagreement.

Run with `lake exe neonTests` (= `make test-neon-model`), from `lean/`: the path below is
relative to the working directory, as in `SpecTests/Kopis/Run.lean`.

`tests/neon_intrinsics_vectors.jsonl` is committed: 50 176 vectors over all 46 wrappers, ≥ 1 000
each, recorded on an Apple M1 (`aarch64-apple-darwin`, which enables FEAT_SHA3 by default).  A
plain `cargo test` on any such host re-checks that file against that CPU, so drift between the
recorded vectors and real hardware is caught continuously.  To re-record it:

```
RUSTFLAGS='-C target-feature=+sha3' KOPIS_REGEN_VECTORS=1 \
  cargo test --lib neon::intrinsics_vectors
```

Every value in the file is a hex string in **memory order** — least significant byte first — so a
128-bit register is 32 hex digits with the low lane leftmost.  Buffers for the memory accessors
are dumped whole and re-chunked here into elements, which is what puts their indexing claims
under test rather than merely under assumption.

A note on what a pass means: this is a differential test over ~1000 inputs per operation, so it
is strong evidence and not a proof.  What it rules out is the failure mode that matters — an
axiom that is simply *wrong* (a rotation that goes the wrong way, a complemented operand on the
wrong side of `bcax`, a `shrn` that keeps the low half instead of the high) — which no other
check in the tree would catch.  Each of those three was tried against the recorded vectors and
each is caught by ~1000 of them; see the phase A2 entry in `NEON_VERIFICATION_PLAN.md` for the
full sweep, including the one corruption that is *not* caught and why that is correct.
-/

namespace Kopis.Neon.Test

open Lean

/-! ## Parsing -/

private def hexDigit? (c : Char) : Option Nat :=
  if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c ∧ c ≤ 'f' then some (10 + (c.toNat - 'a'.toNat))
  else if 'A' ≤ c ∧ c ≤ 'F' then some (10 + (c.toNat - 'A'.toNat))
  else none

/-- The bytes of a hex string, in the order written (which is memory order). -/
private def hexBytes (s : String) : Except String (List (BitVec 8)) :=
  go s.toList []
where
  go : List Char → List (BitVec 8) → Except String (List (BitVec 8))
  | [], acc => .ok acc.reverse
  | hi :: lo :: rest, acc =>
      match hexDigit? hi, hexDigit? lo with
      | some hi, some lo => go rest (BitVec.ofNat 8 (16 * hi + lo) :: acc)
      | _, _ => .error s!"bad hex digit in {s}"
  | _, _ => .error s!"odd-length hex string {s}"

/-- A little-endian byte list as a natural number. -/
private def natLE (bs : List (BitVec 8)) : Nat :=
  bs.foldr (fun b acc => acc * 256 + b.toNat) 0

/-- A little-endian byte list as a `w`-bit word. -/
private def bvLE (w : Nat) (bs : List (BitVec 8)) : BitVec w := BitVec.ofNat w (natLE bs)

/-- A buffer's bytes as `w`-bit little-endian elements. -/
private def words (w : Nat) (bs : List (BitVec 8)) : List (BitVec w) :=
  (bs.toChunks (w / 8)).map (bvLE w)

/-! ## Field access -/

private structure Rec where
  op : String
  j  : Json

private def Rec.hexField (r : Rec) (k : String) (w : Nat) : Except String (BitVec w) := do
  let s ← r.j.getObjValAs? String k
  return bvLE w (← hexBytes s)

private def Rec.bytesField (r : Rec) (k : String) : Except String (List (BitVec 8)) := do
  hexBytes (← r.j.getObjValAs? String k)

private def Rec.wordsField (r : Rec) (k : String) (w : Nat) : Except String (List (BitVec w)) := do
  return words w (← r.bytesField k)

private def Rec.natField (r : Rec) (k : String) : Except String Nat := do
  let n : Int ← r.j.getObjValAs? Int k
  if n < 0 then .error s!"{r.op}: negative {k}" else return n.toNat

private def expect [DecidableEq α] [ToString α] (r : Rec) (model hardware : α) :
    Except String Unit :=
  if model = hardware then .ok ()
  else .error s!"{r.op}: model gave {model}, hardware gave {hardware}"

/-! ## The check

One case per wrapper.  The left-hand side of every `expect` is a `Model.*` definition that
`Model.lean` proves is exactly what the corresponding axiom in `Intrinsics.lean` asserts, so a
failure here is a wrong axiom and not merely a wrong model. -/

def check (j : Json) : Except String Unit := do
  let op ← j.getObjValAs? String "op"
  let r : Rec := ⟨op, j⟩
  let a (_ : Unit) := r.hexField "a" 128
  let b (_ : Unit) := r.hexField "b" 128
  let c (_ : Unit) := r.hexField "c" 128
  let o (_ : Unit) := r.hexField "o" 128
  match op with
  -- broadcasts and constants
  | "dup_n_s16" => expect r (Model.dupNS16 (← r.hexField "a" 16)) (← o ())
  | "dup_n_u16" => expect r (Model.dupNU16 (← r.hexField "a" 16)) (← o ())
  | "dup_n_s32" => expect r (Model.dupNS32 (← r.hexField "a" 32)) (← o ())
  | "dup_n_u32" => expect r (Model.dupNU32 (← r.hexField "a" 32)) (← o ())
  | "dup_n_u64" => expect r (Model.dupNU64 (← r.hexField "a" 64)) (← o ())
  | "set_u64x2" =>
      expect r (Model.setU64x2 (← r.hexField "a" 64) (← r.hexField "b" 64)) (← o ())
  -- bitwise
  | "and" => expect r (Model.andV (← a ()) (← b ())) (← o ())
  | "eor" => expect r (Model.eorV (← a ()) (← b ())) (← o ())
  | "cnt_u8" => expect r (Model.cntU8 (← a ())) (← o ())
  -- 16-bit lane arithmetic
  | "add_16" => expect r (Model.add16 (← a ()) (← b ())) (← o ())
  | "sub_16" => expect r (Model.sub16 (← a ()) (← b ())) (← o ())
  | "mul_16" => expect r (Model.mul16 (← a ()) (← b ())) (← o ())
  | "sqdmulh_s16" => expect r (Model.sqdmulhS16 (← a ()) (← b ())) (← o ())
  | "shsub_s16" => expect r (Model.shsubS16 (← a ()) (← b ())) (← o ())
  | "sshr_n_s16" => expect r (Model.sshrNS16 (← r.natField "imm") (← a ())) (← o ())
  | "ushl_u16" => expect r (Model.ushlU16 (← a ()) (← b ())) (← o ())
  -- 32-bit lane arithmetic
  | "add_32" => expect r (Model.add32 (← a ()) (← b ())) (← o ())
  | "sub_32" => expect r (Model.sub32 (← a ()) (← b ())) (← o ())
  | "mla_32" => expect r (Model.mla32 (← a ()) (← b ()) (← c ())) (← o ())
  | "cmgt_s32" => expect r (Model.cmgtS32 (← a ()) (← b ())) (← o ())
  | "ushl_u32" => expect r (Model.ushlU32 (← a ()) (← b ())) (← o ())
  -- widening, narrowing and interleaves
  | "smull_low_s16" => expect r (Model.smullLowS16 (← a ()) (← b ())) (← o ())
  | "smull_high_s16" => expect r (Model.smullHighS16 (← a ()) (← b ())) (← o ())
  | "sxtl_low_s16" => expect r (Model.sxtlLowS16 (← a ())) (← o ())
  | "sxtl_high_s16" => expect r (Model.sxtlHighS16 (← a ())) (← o ())
  | "xtn_pair_32" => expect r (Model.xtnPair32 (← a ()) (← b ())) (← o ())
  | "shrn16_pair_s32" => expect r (Model.shrn16PairS32 (← a ()) (← b ())) (← o ())
  | "trn1_16" => expect r (Model.trn1L16 (← a ()) (← b ())) (← o ())
  | "trn2_16" => expect r (Model.trn2L16 (← a ()) (← b ())) (← o ())
  | "trn1_32" => expect r (Model.trn1L32 (← a ()) (← b ())) (← o ())
  | "trn2_32" => expect r (Model.trn2L32 (← a ()) (← b ())) (← o ())
  | "trn1_64" => expect r (Model.trn1L64 (← a ()) (← b ())) (← o ())
  | "trn2_64" => expect r (Model.trn2L64 (← a ()) (← b ())) (← o ())
  | "tbl1_u8" => expect r (Model.tbl1U8 (← a ()) (← b ())) (← o ())
  -- FEAT_SHA3
  | "eor3" => expect r (Model.eor3V (← a ()) (← b ()) (← c ())) (← o ())
  | "bcax" => expect r (Model.bcaxV (← a ()) (← b ()) (← c ())) (← o ())
  | "rax1" => expect r (Model.rax1V (← a ()) (← b ())) (← o ())
  | "xar" => expect r (Model.xarV (← r.natField "imm") (← a ()) (← b ())) (← o ())
  -- memory
  | "load_i16" | "load_u16" =>
      expect r (Model.loadW16 (← r.wordsField "buf" 16) (← r.natField "idx")) (← o ())
  | "load_i32" =>
      expect r (Model.loadW32 (← r.wordsField "buf" 32) (← r.natField "idx")) (← o ())
  | "load_u8x16" =>
      expect r (Model.loadW8x16 (← r.bytesField "buf") (← r.natField "idx")) (← o ())
  | "store_i16" | "store_u16" =>
      expect r (Model.storeW16 (← r.wordsField "buf" 16) (← r.natField "idx")
                  (← r.hexField "v" 128)) (← r.wordsField "o" 16)
  | "store_i32" =>
      expect r (Model.storeW32 (← r.wordsField "buf" 32) (← r.natField "idx")
                  (← r.hexField "v" 128)) (← r.wordsField "o" 32)
  | "store_u8x16" =>
      expect r (Model.storeW8x16 (← r.bytesField "buf") (← r.natField "idx")
                  (← r.hexField "v" 128)) (← r.bytesField "o")
  | _ => .error s!"unknown operation {op}"

/-! ## Coverage

A run that silently exercised 30 operations would otherwise look exactly like a run that
exercised all of them. -/

/-- Every wrapper `src/backend/neon/intrinsics_vectors.rs` records. -/
def allOps : List String :=
  ["dup_n_s16", "dup_n_u16", "dup_n_s32", "dup_n_u32", "dup_n_u64", "set_u64x2",
   "and", "eor", "cnt_u8",
   "add_16", "sub_16", "mul_16", "sqdmulh_s16", "shsub_s16", "sshr_n_s16", "ushl_u16",
   "add_32", "sub_32", "mla_32", "cmgt_s32", "ushl_u32",
   "smull_low_s16", "smull_high_s16", "sxtl_low_s16", "sxtl_high_s16",
   "xtn_pair_32", "shrn16_pair_s32",
   "trn1_16", "trn2_16", "trn1_32", "trn2_32", "trn1_64", "trn2_64", "tbl1_u8",
   "eor3", "bcax", "rax1", "xar",
   "load_i16", "load_u16", "load_i32", "load_u8x16",
   "store_i16", "store_u16", "store_i32", "store_u8x16"]

def minVectors : Nat := 1000

def run : IO Unit := do
  let path := "../tests/neon_intrinsics_vectors.jsonl"
  unless (← System.FilePath.pathExists path) do
    throw <| IO.userError
      s!"{path} not found — record it on a FEAT_SHA3 AArch64 host with \
         `RUSTFLAGS='-C target-feature=+sha3' KOPIS_REGEN_VECTORS=1 \
         cargo test --lib neon::intrinsics_vectors`"
  let content ← IO.FS.readFile path
  let mut counts : Std.HashMap String Nat := {}
  let mut failures : Array String := #[]
  let mut total := 0
  for line in content.splitOn "\n" do
    if line.isEmpty then continue
    match Json.parse line with
    | .error e => failures := failures.push s!"unparseable line: {e}"
    | .ok j =>
      total := total + 1
      match j.getObjValAs? String "op" with
      | .error e => failures := failures.push s!"missing op: {e}"
      | .ok op =>
        counts := counts.insert op (counts.getD op 0 + 1)
        match check j with
        | .ok () => pure ()
        | .error e => if failures.size < 20 then failures := failures.push e
  IO.println s!"NEON intrinsic model: {total} vectors over {counts.size} operations"
  let mut missing : Array String := #[]
  let mut thin : Array String := #[]
  for op in allOps do
    match counts[op]? with
    | none => missing := missing.push op
    | some n => if n < minVectors then thin := thin.push s!"{op} ({n})"
  let unknown := counts.toList.filter (fun (op, _) => !allOps.contains op) |>.map (·.1)
  unless missing.isEmpty do
    throw <| IO.userError s!"no vectors for: {missing.toList}"
  unless thin.isEmpty do
    throw <| IO.userError s!"fewer than {minVectors} vectors for: {thin.toList}"
  unless unknown.isEmpty do
    throw <| IO.userError s!"vectors for unknown operations: {unknown}"
  unless failures.isEmpty do
    for f in failures do IO.println s!"  MISMATCH {f}"
    throw <| IO.userError s!"{failures.size} mismatches (first 20 shown)"
  IO.println s!"all {allOps.length} wrappers agree with the model on every vector"

end Kopis.Neon.Test

def main : IO Unit := Kopis.Neon.Test.run
