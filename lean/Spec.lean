-- Top-level Spec aggregator.
-- Re-exports the audited specifications the Kopis proofs are stated against:
-- the Kopis KEM itself plus the hash primitives it builds on.
-- Build with `lake build Spec`.
import Spec.Defs

-- Keccak-p / SHA-3 family (FIPS 202) — the permutation TurboSHAKE rides on.
import Spec.SHA3.Spec

-- TurboSHAKE (RFC 9861)
import Spec.TurboSHAKE.Spec

-- Kopis KEM (kopis-spec.md), facts about its helpers, and proof that `R` is the negacyclic ring
import Spec.Kopis.Spec
import Spec.Kopis.Lemmas
import Spec.Kopis.RingIso
