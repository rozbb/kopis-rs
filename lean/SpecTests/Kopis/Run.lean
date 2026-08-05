import SpecTests.Kopis.TestVectors
import SpecTests.TurboSHAKE.Vectors

/-!
# Kopis native test entry point

Run with `lake exe kopisTests`. Kept separate from `SpecTests.Kopis.TestVectors`
(which is imported by the `SpecTests` aggregator) so that its `main` does not
collide with the ML-KEM runner's `main` in the aggregator's import closure.
-/

def main : IO Unit := do
  Spec.Kopis.Test.runKopisTests
  Spec.Kopis.Test.runKopisKAT
  Spec.TurboSHAKE.Test.run
