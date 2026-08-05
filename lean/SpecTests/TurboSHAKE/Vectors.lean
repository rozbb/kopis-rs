import SpecTests.TestUtils
import Spec.TurboSHAKE.Spec
import Lean.Data.Json

/-!
# The TurboSHAKE spec, checked against test vectors

`Spec/TurboSHAKE/Spec.lean` is a transliteration of RFC 9861, and until now nothing executed it.
That matters more than it looks: the serial backend's five `turboshake`-crate assumptions
(`Kopis/Properties/GenMatrix.lean`) say the crate *implements this spec*, so a typo here would
not be caught by any proof — it would be absorbed into the assumption and quietly make the
top-level theorems claim something other than TurboSHAKE.

This runner replays `../tests/turboshake_vectors.jsonl`, produced by
`tests/turboshake_vectors.rs` from the `turboshake` crate: 100 vectors over both rates, five
domain separators, and input and output lengths chosen around the block boundaries.

What a pass does and does not mean. The vectors come from the crate, so agreement shows the
spec and the crate compute the same function — it does not independently establish that either
is RFC 9861. The generator's companion test `matches_rfc9861` is what anchors that end, by
checking the crate against four published vectors; the two together are what make this
meaningful. Extending *this* file with the published vectors directly would be better still.

Run with `lake exe kopisTests` (= `make test-kopis-spec`), from `lean/`: the path below is
relative to the working directory, as in `SpecTests/Avx2/Run.lean`.
-/

namespace Spec.TurboSHAKE.Test

open Lean Spec.Utils

structure Case where
  description : String
  variant : Nat
  ds : Nat
  input : Array Byte
  output : Array Byte

def parseCase (j : Json) : Except String Case := do
  let description ← j.getObjValAs? String "description"
  let variant ← j.getObjValAs? Nat "variant"
  let ds ← j.getObjValAs? Nat "ds"
  let inputHex ← j.getObjValAs? String "input"
  let outputHex ← j.getObjValAs? String "output"
  let some input := Hex.toBytes? inputHex | throw s!"{description}: bad input hex"
  let some output := Hex.toBytes? outputHex | throw s!"{description}: bad output hex"
  return { description, variant, ds, input, output }

private def toHex (a : Array Byte) : String :=
  a.foldl (fun s b => (s.push (Spec.Utils.Byte.toHex (b / 16))).push
    (Spec.Utils.Byte.toHex (b % 16))) ""

def check (c : Case) : Except String Unit := do
  let msg : 𝔹 c.input.size := ⟨c.input, rfl⟩
  let D : Byte := BitVec.ofNat 8 c.ds
  let got : Array Byte ← match c.variant with
    | 128 => pure (turboSHAKE128 msg D c.output.size).toArray
    | 256 => pure (turboSHAKE256 msg D c.output.size).toArray
    | v => throw s!"{c.description}: unknown variant {v}"
  if got == c.output then .ok ()
  else .error s!"{c.description}\n      expected {toHex c.output}\n      got      {toHex got}"

def run : IO Unit := do
  let t0 ← IO.monoMsNow
  let path := "../tests/turboshake_vectors.jsonl"
  unless (← System.FilePath.pathExists path) do
    throw <| IO.userError
      s!"{path} not found — regenerate with `cargo test --test turboshake_vectors`"
  let content ← IO.FS.readFile path
  let mut total := 0
  let mut variants : Std.HashSet Nat := {}
  let mut seps : Std.HashSet Nat := {}
  let mut failures : Array String := #[]
  for line in content.splitOn "\n" do
    if line.isEmpty then continue
    match Json.parse line >>= parseCase with
    | .error e => failures := failures.push s!"unparseable line: {e}"
    | .ok c =>
      total := total + 1
      variants := variants.insert c.variant
      seps := seps.insert c.ds
      match check c with
      | .ok () => pure ()
      | .error e => if failures.size < 10 then failures := failures.push e
  unless failures.isEmpty do
    for f in failures do IO.println s!"  MISMATCH {f}"
    throw <| IO.userError s!"{failures.size} TurboSHAKE vector mismatches (first 10 shown)"
  if total = 0 then throw <| IO.userError s!"{path} contained no vectors"
  let elapsed := (← IO.monoMsNow) - t0
  IO.println s!"TurboSHAKE spec: {total} vectors agree in {elapsed} ms \
    ({variants.size} rates, {seps.size} domain separators)"

end Spec.TurboSHAKE.Test
