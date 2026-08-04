import Kopis.Avx2
import Lean.Data.Json

/-!
# The AVX2 intrinsic model, checked against silicon

`Kopis/Avx2/Intrinsics.lean` *assumes* what 42 SIMD instructions do; `Kopis/Avx2/Model.lean`
turns each assumption into a computable `BitVec` function and **proves** the two agree — so a
model that matched hardware would leave the axiom in the same position, and a model that did not
would convict it.  This runner is the second half: it replays
`../tests/intrinsics_vectors.jsonl`, which
`src/backend/avx2/intrinsics_vectors.rs` produced by executing the real instructions on a real
CPU, through the models and reports any disagreement.

Run with `lake exe avx2Tests` (= `make test-avx2-model`), from `lean/`: the path below is
relative to the working directory, as in `SpecTests/Kopis/Run.lean`.

Every value in the file is a hex string in **memory order** — least significant byte first — so
a 256-bit register is 64 hex digits with the low lane leftmost.  Buffers for the memory
accessors are dumped whole and re-chunked here into elements, which is what puts their indexing
claims under test rather than merely under assumption.

A note on what a pass means: this is a differential test over ~1000 inputs per operation, so it
is strong evidence and not a proof.  What it rules out is the failure mode that matters — an
axiom that is simply *wrong* (a swapped saturation bound, a sign extension that should be zero,
a shuffle that crosses the 128-bit lane boundary), which no other check in the tree would catch.
-/

namespace Kopis.Avx2.Test

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

/-- The immediate, as the 32-bit word the extracted code carries it in. -/
private def Rec.immField (r : Rec) : Except String (BitVec 32) := do
  return BitVec.ofNat 32 (← r.natField "imm")

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
  -- Register operands are 32 bytes, half-registers 16, and the output width follows the
  -- operation.
  let a256 (_ : Unit) := r.hexField "a" 256
  let b256 (_ : Unit) := r.hexField "b" 256
  let o256 (_ : Unit) := r.hexField "o" 256
  let a128 (_ : Unit) := r.hexField "a" 128
  let o128 (_ : Unit) := r.hexField "o" 128
  match op with
  -- constants and bitwise
  | "setzero_si256" => expect r Model.setzeroSi256 (← o256 ())
  | "set1_epi16" => expect r (Model.set1Epi16 (← r.hexField "a" 16)) (← o256 ())
  | "set1_epi32" => expect r (Model.set1Epi32 (← r.hexField "a" 32)) (← o256 ())
  | "cvtsi32_si128" => expect r (Model.cvtsi32Si128 (← r.hexField "a" 32)) (← o128 ())
  | "and_si256" => expect r (Model.andSi256 (← a256 ()) (← b256 ())) (← o256 ())
  -- lane arithmetic
  | "add_epi16" => expect r (Model.addEpi16 (← a256 ()) (← b256 ())) (← o256 ())
  | "sub_epi16" => expect r (Model.subEpi16 (← a256 ()) (← b256 ())) (← o256 ())
  | "add_epi32" => expect r (Model.addEpi32 (← a256 ()) (← b256 ())) (← o256 ())
  | "sub_epi32" => expect r (Model.subEpi32 (← a256 ()) (← b256 ())) (← o256 ())
  | "mullo_epi16" => expect r (Model.mulloEpi16 (← a256 ()) (← b256 ())) (← o256 ())
  | "mulhi_epi16" => expect r (Model.mulhiEpi16 (← a256 ()) (← b256 ())) (← o256 ())
  | "mullo_epi32" => expect r (Model.mulloEpi32 (← a256 ()) (← b256 ())) (← o256 ())
  | "cmpgt_epi32" => expect r (Model.cmpgtEpi32 (← a256 ()) (← b256 ())) (← o256 ())
  -- shifts
  | "srai_epi16" => expect r (Model.sraiEpi16 (← r.natField "imm") (← a256 ())) (← o256 ())
  | "srai_epi32" => expect r (Model.sraiEpi32 (← r.natField "imm") (← a256 ())) (← o256 ())
  | "srli_epi16" => expect r (Model.srliEpi16 (← r.natField "imm") (← a256 ())) (← o256 ())
  | "slli_epi32" => expect r (Model.slliEpi32 (← r.natField "imm") (← a256 ())) (← o256 ())
  | "srl_epi16" => expect r (Model.srlEpi16 (← a256 ()) (← r.hexField "c" 128)) (← o256 ())
  | "srlv_epi32" => expect r (Model.srlvEpi32 (← a256 ()) (← b256 ())) (← o256 ())
  -- shuffles, packs and lane surgery
  | "shuffle_epi8" => expect r (Model.shuffleEpi8 (← a256 ()) (← b256 ())) (← o256 ())
  | "unpacklo_epi16" => expect r (Model.unpackloEpi16 (← a256 ()) (← b256 ())) (← o256 ())
  | "unpackhi_epi16" => expect r (Model.unpackhiEpi16 (← a256 ()) (← b256 ())) (← o256 ())
  | "unpacklo_epi32" => expect r (Model.unpackloEpi32 (← a256 ()) (← b256 ())) (← o256 ())
  | "unpackhi_epi32" => expect r (Model.unpackhiEpi32 (← a256 ()) (← b256 ())) (← o256 ())
  | "unpacklo_epi64" => expect r (Model.unpackloEpi64 (← a256 ()) (← b256 ())) (← o256 ())
  | "unpackhi_epi64" => expect r (Model.unpackhiEpi64 (← a256 ()) (← b256 ())) (← o256 ())
  | "permute2x128_si256" =>
      expect r (Model.permute2x128Si256 (← r.immField) (← a256 ()) (← b256 ())) (← o256 ())
  | "permute4x64_epi64" =>
      expect r (Model.permute4x64Epi64 (← r.immField) (← a256 ())) (← o256 ())
  | "packs_epi32" => expect r (Model.packsEpi32 (← a256 ()) (← b256 ())) (← o256 ())
  | "packus_epi32" => expect r (Model.packusEpi32 (← a256 ()) (← b256 ())) (← o256 ())
  | "cvtepu16_epi32" => expect r (Model.cvtepu16Epi32 (← a128 ())) (← o256 ())
  | "castsi256_si128" => expect r (Model.castsi256Si128 (← a256 ())) (← o128 ())
  | "extracti128_si256" =>
      expect r (Model.extracti128Si256 (← r.natField "imm") (← a256 ())) (← o128 ())
  | "broadcastsi128_si256" => expect r (Model.broadcastsi128Si256 (← a128 ())) (← o256 ())
  -- memory
  | "load_i16" | "load_u16" =>
      expect r (Model.loadW16 (← r.wordsField "buf" 16) (← r.natField "idx")) (← o256 ())
  | "load_i32" =>
      expect r (Model.loadW32 (← r.wordsField "buf" 32) (← r.natField "idx")) (← o256 ())
  | "load_u8" =>
      expect r (Model.loadW8 (← r.bytesField "buf") (← r.natField "idx")) (← o256 ())
  | "load_u8x16" =>
      expect r (Model.loadW8x16 (← r.bytesField "buf") (← r.natField "idx")) (← o128 ())
  | "store_i16" | "store_u16" =>
      expect r (Model.storeW16 (← r.wordsField "buf" 16) (← r.natField "idx")
                  (← r.hexField "v" 256)) (← r.wordsField "o" 16)
  | "store_i32" =>
      expect r (Model.storeW32 (← r.wordsField "buf" 32) (← r.natField "idx")
                  (← r.hexField "v" 256)) (← r.wordsField "o" 32)
  | _ => .error s!"unknown operation {op}"

/-! ## Coverage

The plan's acceptance bar is ≥ 1000 vectors per wrapper, and there are 42 of them.  A run that
silently exercised 30 operations would otherwise look exactly like a run that exercised 42. -/

/-- Every wrapper in `src/backend/avx2/intrinsics.rs`.  `setzero_si256` takes no argument and
has one possible result, so it is exempt from the vector count. -/
def allOps : List String :=
  ["set1_epi16", "set1_epi32", "setzero_si256", "cvtsi32_si128", "and_si256",
   "add_epi16", "sub_epi16", "add_epi32", "sub_epi32", "mullo_epi16", "mulhi_epi16",
   "mullo_epi32", "cmpgt_epi32",
   "srai_epi16", "srai_epi32", "srli_epi16", "slli_epi32", "srl_epi16", "srlv_epi32",
   "shuffle_epi8", "unpacklo_epi16", "unpackhi_epi16", "unpacklo_epi32", "unpackhi_epi32",
   "unpacklo_epi64", "unpackhi_epi64", "permute2x128_si256", "permute4x64_epi64",
   "packs_epi32", "packus_epi32", "cvtepu16_epi32", "castsi256_si128", "extracti128_si256",
   "broadcastsi128_si256",
   "load_i16", "store_i16", "load_u16", "store_u16", "load_i32", "store_i32", "load_u8",
   "load_u8x16"]

def minVectors : Nat := 1000

def run : IO Unit := do
  let path := "../tests/intrinsics_vectors.jsonl"
  unless (← System.FilePath.pathExists path) do
    throw <| IO.userError
      s!"{path} not found — regenerate with \
         `KOPIS_REGEN_VECTORS=1 cargo test --lib intrinsics_vectors` on an AVX2 host"
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
  IO.println s!"AVX2 intrinsic model: {total} vectors over {counts.size} operations"
  -- coverage
  let mut missing : Array String := #[]
  let mut thin : Array String := #[]
  for op in allOps do
    match counts[op]? with
    | none => missing := missing.push op
    | some n => if op ≠ "setzero_si256" ∧ n < minVectors then thin := thin.push s!"{op} ({n})"
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

end Kopis.Avx2.Test

def main : IO Unit := Kopis.Avx2.Test.run
