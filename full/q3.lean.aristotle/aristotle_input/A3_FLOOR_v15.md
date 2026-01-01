# A3_FLOOR v15: digammaSeq = logDeriv GammaSeq (logDeriv lemmas)

## Definitions (Lean)
```lean
import Mathlib

open scoped BigOperators Real Nat Classical Pointwise
open Real Complex MeasureTheory Set

set_option maxHeartbeats 0
set_option maxRecDepth 4000

noncomputable section

-- digamma partial sums (same as v8/v14)
noncomputable def digammaSeq (z : Complex) (n : Nat) : Complex :=
  (Real.log n : Complex) - ∑ k ∈ Finset.range (n + 1), 1 / (z + k)
```

## Theorem Statement
```lean
lemma digammaSeq_eq_logDeriv_GammaSeq {z : Complex} {n : Nat}
    (hn : n ≠ 0) (hz : ∀ k ≤ n, z ≠ -k) :
    digammaSeq z n = logDeriv (fun w => Complex.GammaSeq w n) z := by
  -- no sorry
```

## Hints
- Prefer `logDeriv_apply`, `logDeriv_mul`, `logDeriv_div`, `logDeriv_const`, `logDeriv_prod`
  to avoid manual product rule.
- `Complex.GammaSeq` expands to:
  `(n:Complex)^w * (n! : Complex) / ∏ k ∈ Finset.range (n+1), (w + k)`
- For the factor `fun w => (n:Complex)^w`, use
  `hasStrictDerivAt_const_cpow` or `HasDerivAt.const_cpow` to show
  `deriv (fun w => (n:Complex)^w) z = (n:Complex)^z * Complex.log n`,
  then apply `logDeriv_apply`.
- For `logDeriv (fun w => w + k) z`, `simp [logDeriv_apply]`.
- Use `hz` to discharge nonzero denominators in `logDeriv_mul/div/prod`.
