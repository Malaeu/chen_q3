# Step33A.1 Sub0 Collapsed Degree-0 Point-Slope Rat Payload Audit

- schema: `q3_psdpd_step33_a1_sub0_collapsed_degree0_point_slope_rat_payload.v1`
- generatedAt: `2026-06-24T15:28:11.705806+00:00`
- payloadFile: `Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16CollapsedDegree0PointSlopeRatPayload.lean`
- payloadPresent: `True`
- proofStatus: `rat_payload_present_budget_kill_not_closed`
- currentGap: `STEP33_A1_SUB0_COMBINED_ORDER16_COLLAPSED_DEGREE0_POINT_SLOPE_RAT_POINT_ROW_BUDGET_KILL_GAP`

## Required Symbols

| symbol | present | line |
| --- | --- | --- |
| `primaryFiniteRow0Parent0Split100Sub0_componentProductActual_order17_point_interval_rat_generated` | `True` | `145` |
| `primaryFiniteRow0Parent0Split100Sub0_activeScaled_componentProductActual_order17_point_interval_rat_generated` | `True` | `267` |
| `primaryFiniteRow0Parent0Split100Sub0_nominalOrder16Poly_deriv_localCenter_eq_rat` | `True` | `439` |
| `primaryFiniteRow0Parent0Split100Sub0_collapsedDegree0_pointRow_generated` | `True` | `476` |

## Boundary

Rat payload presence is not Step33A.1-A closure; budget/sign kill must be proved separately.

## Next Patch

Try positive_row_budget_impossible/negative_row_budget_impossible from the Rat PointRowCert.Valid; if exact sign or threshold fails, replace the coarse raw Rat row with a true point-specific RawProduct18 Rat mirror.
