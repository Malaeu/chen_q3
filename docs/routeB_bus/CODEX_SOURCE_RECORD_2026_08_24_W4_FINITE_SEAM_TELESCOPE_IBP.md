# CODEX SOURCE RECORD — W4 finite seam telescope IBP

```yaml
STATUS: KERNEL_GREEN_PENDING_SEMANTIC_REFRESH
DATE: 2026-08-24
BRANCH: rh_clean
IMPLEMENTATION_PARENT: d75504eb16a56f70f6aea39a126bc1cd77a0565b
IMPLEMENTATION_SOURCE_BLOB: ce8169a5ae309345008c4419f29f58019bf0445b
OPERATIVE_VERDICT_COMMIT: c766a242
OPERATIVE_VERDICT:
  docs/routeB_bus/proshka/PROSHKA_VERDICT_GOAL058_W4_FINITE_SEAM_TELESCOPE_IBP_ARCHITECTURE_2026-08-24.md
LEAN_SOURCE:
  q3.lean.aristotle/Q3/Proofs/RouteB/G6N1SelectedFerrersPiecewiseACDerivativeIntegrability.lean
SUCCESS_TOKEN: W4_ZERO_ENDPOINT_JUMP_LEDGER_REPAIRED_AND_FIXED_K_FOURIER_DECAY_KERNEL_GREEN
```

## Frozen public surface

The implementation preserves exactly five public definitions:

```text
selectedFerrersAbelLogRepresentative
selectedFerrersAbelLogZeroExtension
selectedFerrersAbelLogSeamFreeOn
selectedFerrersAbelLogDerivativeBudget
selectedFerrersAbelLogJumpBudget
```

and exactly five public theorems:

```text
selectedFerrersLemma73SourcePacket_absolutelyContinuousOnInterval
selectedFerrersAbelLogRepresentative_absolutelyContinuousOnInterval_of_seamFree
selectedFerrersAbelLogRepresentative_intervalIntegrable_deriv_of_seamFree
selectedFerrersAbelLogZeroExtension_fourier_decay_off_zero
selectedFerrersAbelLogZeroExtension_fourier_decay
```

No public helper declaration was added. The production object remains the
complex-valued full-endpoint representative. The public jump ledger remains
`Finset.Icc 2 (k + 2)`.

## Private normal forms and equivalence record

The implementation uses two equivalent private cell encodings.

1. `selectedFerrersAbelLogCellRepresentative k j` uses the positive-index
   interval `Finset.Icc 1 j`.
2. `selectedFerrersAbelLogCell k n` uses the verdict's total fixed-active-set
   normal form: `sourcePositiveIndexFinset.filter (fun q => (q : Nat) <= n)`.

For `0 < n` and `n <= k + 2`, the theorem
`selectedFerrersAbelLogCell_eq_cellRepresentative` proves equality of these
functions. This removes proof-dependent conditionals from finite sums while
preserving the exact active set `1..n`.

The total Nat seam and partition definitions are the verdict definitions:

```text
s(k,n) = log((k+2)/n)
p(k,j) = s(k,k+2-j)
```

Private crosswalk lemmas identify them with the positive-Nat seam used by the
cell AC chain. The partition has `k+1` strictly ordered cells, from `0` to
`L_m (selectedFerrersPreAnchorIndex k)`.

## Endpoint and telescope record

For every active cell the source proves separately:

- equality with the production representative on the open cell;
- the production full value at the upper endpoint;
- the production full value minus exactly one entering seam at the lower
  endpoint;
- a.e. equality of derivatives, with no equality asserted at seam points.

At the lower endpoint the first cell value is proved equal to
`selectedFerrersAbelLogLowerRightValue k`. The finite IBP boundary terms are
telescoped before taking norms. The exact sharp estimate contains only internal
seams `2..k+1`; only afterward is
`selectedFerrersAbelLogLowerRightValue_norm_le` applied and the final public
summand `n=k+2` paid separately.

## Fourier and integrability record

The direct pinned Mathlib import is:

```lean
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
```

Each cell uses
`intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDeriv_right` with the
exact `Real.fourierChar (-(x*t))` phase and its normalized primitive. The source
also proves private whole-window interval integrability of the representative
and whole-line integrability of the zero extension before the final fixed-`k`
decay theorem.

## Validation receipt

All commands completed successfully against source blob
`ce8169a5ae309345008c4419f29f58019bf0445b`:

```text
WORKDIR q3.lean.aristotle
lake env lean Q3/Proofs/RouteB/G6N1SelectedFerrersPiecewiseACDerivativeIntegrability.lean

WORKDIR q3.lean.aristotle
lake build Q3.Proofs.RouteB.G6N1SelectedFerrersPiecewiseACDerivativeIntegrability
Build completed successfully (7851 jobs).

WORKDIR repository root
scripts/q3_check.sh Q3/Proofs/RouteB/G6N1SelectedFerrersPiecewiseACDerivativeIntegrability.lean
q3_check ok
```

All five public theorems and all four mandatory plants print exactly:

```text
[propext, Classical.choice, Quot.sound]
```

This closes the W4 kernel transaction only. It does not itself authorize W5,
Route promotion, or an RH claim. The downstream fixed-`k` shifted form-domain
assembly remains a separate transaction after semantic admission.
