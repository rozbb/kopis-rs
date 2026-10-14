/-
  # Kopis/Neon.lean — the NEON backend's aggregator.

  Importing this pulls in the NEON extraction, the assumed intrinsic semantics, the computable
  models the differential test evaluates, and the correspondence results for each vector routine.
  `lake build KopisNeon` builds exactly this closure.

  The generated twin proof stack (`Kopis.Neon.Properties.*`) is a separate
  `lean_lib KopisNeonProperties`, as the AVX2 one is; `TopLevelTheoremsNeon` imports it.
-/
import Kopis.Neon.Intrinsics
import Kopis.Neon.Lanes
import Kopis.Neon.Model
import Kopis.Neon.SerLane
import Kopis.Neon.SerPlan
import Kopis.Neon.SerTail
import Kopis.Neon.Ser
import Kopis.Neon.SerGeneric
import Kopis.Neon.SerEq
import Kopis.Neon.SerDispatch
import Kopis.Neon.Cbd
import Kopis.Neon.CbdGeneric
import Kopis.Neon.CbdEq
import Kopis.Neon.CbdDispatch
import Kopis.Neon.LaneArith
import Kopis.Neon.Transpose
import Kopis.Neon.NttReduce
import Kopis.Neon.NttGrowth
import Kopis.Neon.Tables
import Kopis.Neon.Butterfly
import Kopis.Neon.Group
import Kopis.Neon.NttLevel
import Kopis.Neon.NttTransposed
import Kopis.Neon.NttBarrettIter
import Kopis.Neon.NttGroupLoop
import Kopis.Neon.InvNttLevel
import Kopis.Neon.NttZeta
import Kopis.Neon.NttValue
import Kopis.Neon.NttWalk
import Kopis.Neon.InvWalk
import Kopis.Neon.Reduce
import Kopis.Neon.MulT
