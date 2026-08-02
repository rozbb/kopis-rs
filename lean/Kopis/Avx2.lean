/-
  # Kopis/Avx2.lean — the AVX2 backend's aggregator.

  Importing this pulls in the AVX2 extraction, the assumed intrinsic semantics, the lane algebra
  those are composed with, and the computable models the differential test evaluates.  `lake
  build KopisAvx2` (= `make prove-kopis-avx2`) builds exactly this closure.
-/
import Kopis.Avx2.Intrinsics
import Kopis.Avx2.Lanes
import Kopis.Avx2.Model
