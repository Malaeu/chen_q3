# Step33A.1 Sub0 Collapsed Degree-0 Rat Point-Row Audit

- schema: `q3_psdpd_step33_a1_sub0_collapsed_degree0_point_slope_rat_audit.v1`
- generatedAt: `2026-06-24T15:54:31.667588+00:00`
- proofStatus: `fail_closed_rat_point_row_budget_kill_unvalidated`
- proofGrade: `False`
- diagnosticGrade: `True`
- currentGap: `STEP33_A1_SUB0_COMBINED_ORDER16_SCALED_REMAINDER_DIRECT_ROW_SOURCE_GAP`
- previousGap: `STEP33_A1_SUB0_COMBINED_ORDER16_COLLAPSED_DEGREE0_POINT_SLOPE_RAT_POINT_ROW_BUDGET_KILL_GAP`
- unvalidatedLeanBudgetFailFileExists: `False`

## Rat Payload Surfaces

| symbol | present | line |
| --- | --- | --- |
| `primaryFiniteRow0Parent0Split100Sub0_componentProductActual_order17_point_interval_rat_generated` | `True` | `145` |
| `primaryFiniteRow0Parent0Split100Sub0_activeScaled_componentProductActual_order17_point_interval_rat_generated` | `True` | `267` |
| `primaryFiniteRow0Parent0Split100Sub0_nominalOrder16Poly_deriv_localCenter_eq_rat` | `True` | `439` |
| `primaryFiniteRow0Parent0Split100Sub0_collapsedDegree0_pointRow_generated` | `True` | `476` |

## Related Lean-Checked Kill

| symbol | present | line |
| --- | --- | --- |
| `primaryFiniteRow0Parent0Split100Sub0_rawD17_signedFactor_sharp_twoSegment_budget_fail_rat` | `True` | `31` |
| `primaryFiniteRow0Parent0Split100Sub0_rawD17_signedFactor_sharp_twoSegment_budget_not_spendable` | `True` | `41` |

## Budget Gate

Positive-row kill requires both:

- `0 <= collapsed point lower`
- `AllowedDerivAbsRat < collapsed point lower`

Negative-row kill requires both:

- `collapsed point upper <= 0`
- `AllowedDerivAbsRat < -collapsed point upper`

No Lean-validated theorem for those comparisons is present in this audit.

## Boundary

The Rat point-row payload remains useful and checked, but the current session has no Lean-validated theorem that the Rat rows instantiate positive_row_budget_impossible or negative_row_budget_impossible.  This audit is a fail-closed diagnostic and must not be used as proof of a budget kill.

## Next Patch

Use the direct whole CollapsedExpression row-source generator.  Do not spend further factorwise point-row budgets as closure.
