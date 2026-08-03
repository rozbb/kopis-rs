/-
  # Kopis/Avx2.lean — the AVX2 backend's aggregator.

  Importing this pulls in the AVX2 extraction, the assumed intrinsic semantics, the lane algebra
  they are composed with, the computable models the differential test evaluates, and the two
  correspondence results proved so far: `avx2_deserialize_eq` (phase C) and `avx2_cbd_eq`
  (phase D).  `lake build KopisAvx2` (= `make prove-kopis-avx2`) builds exactly this closure.

  The generated twin proof stack (`Kopis.Avx2.Properties.*`, phase E) is deliberately *not*
  imported here: it is a separate `lean_lib KopisAvx2Properties`, so that a red twin cannot
  block this target while phase E is in progress.
-/
import Kopis.Avx2.Intrinsics
import Kopis.Avx2.Lanes
import Kopis.Avx2.Model
import Kopis.Avx2.LaneArith
import Kopis.Avx2.NttReduce
import Kopis.Avx2.NttGrowth
import Kopis.Avx2.Tables
import Kopis.Avx2.Crt
import Kopis.Avx2.Transpose
import Kopis.Avx2.TransposeSpec
import Kopis.Avx2.NttMulLane
import Kopis.Avx2.SerLane
import Kopis.Avx2.SerPlan
import Kopis.Avx2.SerTail
import Kopis.Avx2.Ser
import Kopis.Avx2.SerGeneric
import Kopis.Avx2.SerEq
import Kopis.Avx2.SerDispatch
import Kopis.Avx2.Cbd
import Kopis.Avx2.CbdGeneric
import Kopis.Avx2.CbdEq
import Kopis.Avx2.CbdDispatch
