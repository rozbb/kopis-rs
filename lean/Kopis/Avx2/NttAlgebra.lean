/-
  # Kopis/Avx2/NttAlgebra.lean — the NTT state algebra, in the AVX2 namespace.

  Nothing here; see `Kopis/Crt/NttAlgebra.lean`.  Like `Crt.lean` beside it, this is about the
  transform rather than about any instruction set — `State`, `cst` and `nconv` are statements
  about a function `ℕ → K` for an arbitrary commutative ring `K` — so it is shared with the NEON
  stack rather than copied into it.

  Re-exported under `Kopis.Avx2.NttAlg` so that no proof below `Kopis/Avx2/` changes.  The NEON
  stack should `import Kopis.Crt.NttAlgebra` directly instead.
-/
import Kopis.Crt.NttAlgebra

namespace Kopis.Avx2.NttAlg

export Kopis.CrtScheme.NttAlg (cst cst_one cst_even cst_odd sum_range_two State State_root
  State_root_intro State_leaf State_ct cst_sq cst_leaf_pow nconv Ev_nconv State_leaf_mul State_gs)

end Kopis.Avx2.NttAlg
