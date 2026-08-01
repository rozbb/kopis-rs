/-
  # Kopis/Properties/NttReduce.lean — the NTT reduction-function value specs.

  The four scalar reductions of `src/arithmetic/ntt.rs` are the foundation of the
  transform-correctness proof.  `to_canonical_spec` lives in `Ntt.lean`; the other three each
  get their own file, and this module just collects them:

  * `NttReduceMont`    — `mont_reduce_spec`
  * `NttReduceBarrett` — `barrett_reduce_spec`
  * `NttReduceWrap`    — `to_wrapping_u16_spec`

  ## Why one theorem per file

  These are WP-monadic proofs over `i32`/`i64` bit-vector operations, and they used to be
  ruinously expensive: a single `lake build` of the combined file took ~14 minutes and ~15 GB
  resident, and failed outright with `(kernel) deep recursion detected`.

  Two changes fixed that, and both are worth preserving:

  1. **`clear_value` after the value equations.**  `set` introduces its abbreviations as
     *let-bound* locals.  Left that way, the kernel zeta-expands them when it checks the finished
     term and then has to reduce `BitVec` operations on 32- and 64-bit literals inside every
     arithmetic side condition.  Retiring them with `clear_value` (and dropping the definitional
     hypotheses) as soon as `e_i …` are known makes everything downstream ordinary integer
     arithmetic over a handful of opaque unknowns.
  2. **Euclidean decomposition instead of `omega`-over-division.**  `barrett_reduce`'s bounds
     were stated over `/ 2⁴⁸`; asking `omega` to eliminate that against 2⁶³-sized bounds is what
     produced most of the memory.  Stated over `x·M + 2⁴⁷ = q·2⁴⁸ + r`, they are linear and
     `linarith` closes them instantly.

  Together these take the three proofs from ~14 min / ~15 GB (failing) to a few seconds each.
  The one-theorem-per-file split is kept so the three still elaborate in parallel and no single
  worker's resident set grows large.
-/
import Kopis.Properties.NttReduceMont
import Kopis.Properties.NttReduceBarrett
import Kopis.Properties.NttReduceWrap
