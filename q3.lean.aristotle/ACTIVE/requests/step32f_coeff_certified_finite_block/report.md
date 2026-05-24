# Step32F coefficient certified finite block report

## Status

Closed.

## Theorem / definitions added

- `CertifiedCenteredBSplineCoeffBlock`
- `CertifiedCenteredBSplineCoeffBlock.finiteWeilMatrixModel`
- `CertifiedCenteredBSplineCoeffBlock.toCertifiedFiniteWeilModel`
- `CertifiedCenteredBSplineCoeffBlock.weil_nonneg_on_analyticBoundary`
- `CertifiedCenteredBSplineCoeffBlock.weil_ge_theta_R_on_analyticBoundary`

## Files touched

- `Q3/Proofs/PSD_CenteredCardinalBSpline.lean`
- `docs/INSIGHTS.md`
- `ACTIVE/requests/step32f_coeff_certified_finite_block/report.md`

## Commands run

```bash
./scripts/research_oracle.py query "CertifiedBSplineConcreteBlock centeredBSplineCoeffAnalyticKernelContract FinitePenaltyCert" -c q3_docs
./scripts/research_oracle.py query "CertifiedFiniteWeilModel finite certificate B-spline analytic contract" -c q3_docs
./scripts/research_oracle.py query "Step32F coefficient analytic kernel contract interval-backed finite certificate" -c q3_docs
lake env lean Q3/Proofs/PSD_CenteredCardinalBSpline.lean
lake env lean Q3/Proofs/PSD_CenteredCardinalBSpline.lean && lake env lean Q3/Proofs/PSD_BSplineTranslationIdentities.lean && lake build Q3.Proofs.PSD_CenteredCardinalBSpline && lake build Q3.Main && (rg -n "sorry|admit|exact\\?" Q3/Proofs/PSD_CenteredCardinalBSpline.lean Q3/Proofs/PSD_BSplineTranslationIdentities.lean || true) && ./scripts/check_axioms.sh
```

## Compile status

- `lake env lean Q3/Proofs/PSD_CenteredCardinalBSpline.lean`: passed.
- `lake env lean Q3/Proofs/PSD_BSplineTranslationIdentities.lean`: passed.
- `lake build Q3.Proofs.PSD_CenteredCardinalBSpline`: passed.
- `lake build Q3.Main`: passed.
- Hole scan on touched Lean files: clean.
- `./scripts/check_axioms.sh`: passed.

## Axiom profile

`Q3.Main.RH_of_Weil_and_Q3` depends on:

```text
[propext, Classical.choice, Q3.Weil_criterion,
 Q3.prime_term_le_at_t_critical_axiom, Quot.sound]
```

This is the expected profile: 3 standard Lean axioms and 2 documented project
axioms.

## Result

The assembled coefficient-space B-spline analytic contract now feeds the
existing finite certificate consumer layer. Given a `FinitePenaltyCert` and the
quadratic split identity for the assembled `C` matrix, the new wrapper produces
a `CertifiedFiniteWeilModel (Fin 2) ι (ι -> ℂ)` and exposes analytic-boundary
nonnegativity plus the strengthened `theta R` lower bound.

## Remaining blocker

The next smallest node is to instantiate the new wrapper with a concrete
interval-backed certificate block / manifest data, then hand the resulting
`CertifiedFiniteWeilModel` into the finite-to-directed family bridge.
