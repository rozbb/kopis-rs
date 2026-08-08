/-
  # Kopis/Avx2/Crt.lean — the CRT scheme, in the AVX2 namespace.

  Nothing here.  `Kopis/Crt/Scheme.lean` holds the whole of it, because the two-prime CRT
  transform is `src/backend/crt.rs` and is shared by both vector backends — the file mentions no
  register width, no extracted constant and no instruction, which is exactly the test
  `Kopis/Bits/Lanes.lean` and `Kopis/Bits/Stream.lean` already pass.
  `NEON_VERIFICATION_PLAN.md` §1(c) says so in as many words: what is genuinely new on a second
  backend is the lane arrangement, not the mathematics.

  This file re-exports it under `Kopis.Avx2` so that no proof below `Kopis/Avx2/` changes.  The
  NEON stack has no such history to preserve and should `import Kopis.Crt.Scheme` directly.
-/
import Kopis.Crt.Scheme

namespace Kopis.Avx2

export Kopis.CrtScheme (q1 q2 crtQ crtQ_eq q1_pos q2_pos q1_q2_coprime garner_congr crt_unique
  exactness_bound_fits crt_endpoint garner_value crt_q1_inv_mont_ok garner_mult)

end Kopis.Avx2
