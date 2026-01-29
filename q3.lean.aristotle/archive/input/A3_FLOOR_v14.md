# A3_FLOOR v14: digammaSeq = logDeriv GammaSeq (algebraic step)

## Goal
Prove the algebraic identity connecting `digammaSeq` and `Complex.GammaSeq`:

```lean
lemma digammaSeq_eq_logDeriv_GammaSeq {z : ℂ} {n : ℕ}
    (hn : n ≠ 0) (hz : ∀ k ≤ n, z ≠ -k) :
    digammaSeq z n = logDeriv (fun w => Complex.GammaSeq w n) z := by
  -- no sorry
```

This is purely algebraic (finite products), no limits/analysis.

---

## Setup (Lean)

```lean
import Mathlib

open scoped BigOperators Real Nat Classical Pointwise
open Real Complex MeasureTheory Set

set_option maxHeartbeats 0
set_option maxRecDepth 4000

noncomputable section

open Complex

-- digamma partial sums
noncomputable def digammaSeq (z : ℂ) (n : ℕ) : ℂ :=
  (Real.log n : ℂ) - ∑ k ∈ Finset.range (n + 1), 1 / (z + k)
```

---

## Target

```lean
lemma digammaSeq_eq_logDeriv_GammaSeq {z : ℂ} {n : ℕ}
    (hn : n ≠ 0) (hz : ∀ k ≤ n, z ≠ -k) :
    digammaSeq z n = logDeriv (fun w => Complex.GammaSeq w n) z := by
  -- Hints below
  sorry
```

---

## Hints

1) Unfold `Complex.GammaSeq`:
```
GammaSeq s n = (n:ℂ)^s * n! / ∏ j ∈ Finset.range (n+1), (s + j)
```

2) Use logarithmic derivative lemmas from `Mathlib/Analysis/Calculus/LogDeriv.lean`:
- `logDeriv_mul`, `logDeriv_div`, `logDeriv_const`, `logDeriv_prod`

3) Compute log derivatives termwise:
- `logDeriv (fun w => (n:ℂ)^w) z = Complex.log n` (use `hasStrictDerivAt_const_cpow` or `deriv` of `const_cpow`)
- `logDeriv (fun w => w + k) z = 1 / (z + k)`
- `logDeriv (fun _ => (n! : ℂ)) = 0`

4) `hz` ensures `z + k ≠ 0` for `k ≤ n`, so denominators are nonzero.

5) Finish by rewriting `logDeriv` as `deriv f / f` if needed:
`logDeriv_apply`.

