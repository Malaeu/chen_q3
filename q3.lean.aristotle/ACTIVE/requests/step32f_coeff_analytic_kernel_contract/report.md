# Step32F coefficient analytic-kernel contract assembly report

## Status

Closed.

## Theorems and definitions added

- `centeredBSplineCoeffBoundaryPlusFunctional`
- `centeredBSplineCoeffBoundaryMinusFunctional`
- `centeredBSplineCoeffBoundaryPair`
- `centeredBSplineCoeffBoundaryPair_evalPlus_basis`
- `centeredBSplineCoeffBoundaryPair_evalMinus_basis`
- `centeredBSplineCoeffAnalyticKernelContract`
- `centeredBSplineCoeffFiniteWeilMatrixModel`
- `centeredBSplineCoeffAnalyticKernelContract_weil_ident`

## Files touched

- `Q3/Proofs/PSD_CenteredCardinalBSpline.lean`
- `docs/INSIGHTS.md`
- `ACTIVE/requests/step32f_coeff_analytic_kernel_contract/report.md`

## Verification

Commands run:

- `lake env lean Q3/Proofs/PSD_CenteredCardinalBSpline.lean`
- `lake env lean Q3/Proofs/PSD_BSplineTranslationIdentities.lean`
- `lake build Q3.Proofs.PSD_CenteredCardinalBSpline`
- `lake build Q3.Main`
- `rg -n "sorry|admit|exact\?" Q3/Proofs/PSD_CenteredCardinalBSpline.lean Q3/Proofs/PSD_BSplineTranslationIdentities.lean`
- `./scripts/check_axioms.sh`

Compile status: passed.

Hole scan: clean for the checked files.

Axiom check: passed with the expected current count:

- 3 standard Lean axioms
- 2 project axioms:
  - `Q3.Weil_criterion`
  - `Q3.prime_term_le_at_t_critical_axiom`

## Result

The coefficient-space B-spline packet model now has one concrete
`BSplineAnalyticKernelContract` combining:

- the two exponential boundary rows;
- the Arch coefficient receiver;
- the finite weighted Prime-sum coefficient receiver.

This exposes a finite Weil matrix model and the synthesized Weil-form identity
for the assembled Arch-minus-Prime matrix.

## Next smallest blocker

Connect the assembled coefficient-space contract to the interval-backed finite
certificate data / concrete block wrapper, then move toward the
finite-to-directed bridge.
