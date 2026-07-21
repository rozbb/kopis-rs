-- Aggregator for the spec test modules.
-- Usage: `lake build SpecTests` (compile-time `#guard`s) or
--        `lake exe kopisTests` (the KAT runner, = `make test-kopis-spec`).
import SpecTests.TestUtils
import SpecTests.Kopis
