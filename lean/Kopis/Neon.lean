/-
  # Kopis/Neon.lean — the NEON backend's aggregator.

  Importing this pulls in the NEON extraction and the assumed intrinsic semantics.  `lake build
  KopisNeon` (= `make prove-kopis-neon`) builds exactly this closure.

  **No correspondence proof exists yet.**  This is the scaffolding-complete state the AVX2
  backend was in at commit `c5b9ad1`, and `NEON_VERIFICATION_PLAN.md` is the plan of work from
  here; the phases there add `Kopis/Neon/Model.lean`, `Kopis/Neon/Lanes.lean` and then the
  correspondence results, each of which gets an import below as it lands.

  The generated twin proof stack (`Kopis.Neon.Properties.*`) will be a separate
  `lean_lib KopisNeonProperties`, as the AVX2 one is, so that a twin which does not yet compile
  cannot block this target.
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
