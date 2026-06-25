# Step33A.1 Sub0 Collapsed Degree-0 Point-Slope Rows Audit

- schema: `q3_psdpd_step33_a1_sub0_collapsed_degree0_point_slope_rows.v1`
- generatedAt: `2026-06-24T15:24:43.130445+00:00`
- route: `collapsed_degree0_point_slope_signed_factor_point_rows`
- proofStatus: `rat_payload_present_budget_kill_not_closed`
- shouldEmitLeanPayload: `False`
- currentGap: `STEP33_A1_SUB0_COMBINED_ORDER16_COLLAPSED_DEGREE0_POINT_SLOPE_RAT_POINT_ROW_BUDGET_KILL_GAP`

## First Required Theorems

- `primaryFiniteRow0Parent0Split100Sub0_componentProductActual_order17_point_interval_rat_generated`
- `primaryFiniteRow0Parent0Split100Sub0_collapsedDegree0_pointRow_generated`

## Routing Guard

- `do_not_instantiate_signed_taylor_on_whole_collapsed_expression`
- `do_not_instantiate_signed_taylor_directly_on_componentProductActual`
- `apply_signed_taylor_to_OmegaActual_and_ShapeSqActual_first`
- `assemble_RawProduct18_by_exact_signed_Leibniz`
- `then_active_scale_and_subtract_exact_nominal_derivative_point_row`

## Required Symbols

| file | symbol | present | line |
| --- | --- | --- | --- |
| `Q3/Proofs/PSD_CenteredCoeffRawOmegaACenteredTaylorDerivativePointInterval18.lean` | `iteratedDeriv_mem_Icc_of_centerJet18_point` | `True` | `266` |
| `Q3/Proofs/PSD_CenteredCoeffRawOmegaACenteredTaylorDerivativePointInterval18.lean` | `centeredTaylorDerivPointLower18` | `True` | `100` |
| `Q3/Proofs/PSD_CenteredCoeffRawOmegaACenteredTaylorDerivativePointInterval18.lean` | `centeredTaylorDerivPointUpper18` | `True` | `106` |
| `Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16CollapsedDegree0PointSlopeRows.lean` | `primaryFiniteRow0Parent0Split100Sub0_collapsedDegree0_pointRowValid_of_collapsedExpressionDeriv_point_interval` | `True` | `50` |
| `Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16CollapsedDegree0PointSlopeRows.lean` | `primaryFiniteRow0Parent0Split100Sub0CollapsedDegree0SignedTaylorTransferGap` | `True` | `80` |
| `Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationActiveActualCenterJetRowsPayload.lean` | `primaryFiniteRow0Parent0Split100Sub0OmegaActualCenterJetLower` | `True` | `601` |
| `Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationActiveActualCenterJetRowsPayload.lean` | `primaryFiniteRow0Parent0Split100Sub0OmegaActualCenterJetUpper` | `True` | `610` |
| `Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationActiveActualCenterJetRowsPayload.lean` | `primaryFiniteRow0Parent0Split100Sub0ShapeSqActualCenterJetLower` | `True` | `619` |
| `Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationActiveActualCenterJetRowsPayload.lean` | `primaryFiniteRow0Parent0Split100Sub0ShapeSqActualCenterJetUpper` | `True` | `628` |
| `Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationActiveActualCenterJetRowsPayload.lean` | `primaryFiniteRow0Parent0Split100Sub0_omegaActual_signed_centerJet_interval` | `True` | `250` |
| `Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationActiveActualCenterJetRowsPayload.lean` | `primaryFiniteRow0Parent0Split100Sub0_shapeSqActual_signed_centerJet_interval` | `True` | `376` |
| `Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16CollapsedDegree0RawD17SignedFactorRows.lean` | `primaryFiniteRow0Parent0Split100Sub0RawProduct18SignedTerm` | `True` | `75` |
| `Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16CollapsedDegree0RawD17SignedFactorRows.lean` | `primaryFiniteRow0Parent0Split100Sub0_rawProductActual_order18_eq_signedLeibniz` | `True` | `84` |
| `Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16CollapsedDegree0RawD17SignedFactorRows.lean` | `primaryFiniteRow0Parent0Split100Sub0_collapsedDegree0_rawD17_interval_of_signed_factor_segment` | `True` | `368` |
| `Q3/Proofs/PSD_CenteredCoeffRawOmegaARawD17SharpLocalCenterJets18Payload.lean` | `primaryFiniteRow0Parent0Split100Sub0_omegaActual_sharpSourceCenterJet18_signed_interval` | `True` | `388` |
| `Q3/Proofs/PSD_CenteredCoeffRawOmegaARawD17SharpLocalCenterJets18Payload.lean` | `primaryFiniteRow0Parent0Split100Sub0_shapeSqActual_sharpSourceCenterJet18_signed_interval` | `True` | `434` |
| `Q3/Proofs/PSD_CenteredCoeffRawOmegaARawD17SharpLocalCenterJets18Payload.lean` | `primaryFiniteRow0Parent0Split100Sub0_omegaActual_signed_point_interval_generated` | `True` | `503` |
| `Q3/Proofs/PSD_CenteredCoeffRawOmegaARawD17SharpLocalCenterJets18Payload.lean` | `primaryFiniteRow0Parent0Split100Sub0_shapeSqActual_signed_point_interval_generated` | `True` | `573` |
| `Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16ActiveActualRawProduct18Payload.lean` | `primaryFiniteRow0Parent0Split100Sub0_componentProductActual_order17_eq_rawProduct18` | `True` | `49` |
| `Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16CollapsedDegree0NominalPolyDerivRows.lean` | `primaryFiniteRow0Parent0Split100Sub0_nominalOrder16Poly_deriv_eq_poly` | `True` | `75` |
| `Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16CollapsedDegree0NominalPolyDerivRows.lean` | `primaryFiniteRow0Parent0Split100Sub0_nominalOrder16Poly_deriv_segment_interval_generated` | `True` | `174` |

## Expected Payload Symbols

| file | symbol | present | line |
| --- | --- | --- | --- |
| `Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16CollapsedDegree0PointSlopeRatPayload.lean` | `primaryFiniteRow0Parent0Split100Sub0_componentProductActual_order17_point_interval_rat_generated` | `True` | `145` |
| `Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16CollapsedDegree0PointSlopeRatPayload.lean` | `primaryFiniteRow0Parent0Split100Sub0_collapsedDegree0_pointRow_generated` | `True` | `476` |

## First Blocking Evidence

- factor signed point rows are present as Lean theorem surfaces for `OmegaActual` and `ShapeSqActual`.
- RawProduct18 point assembly is present when `primaryFiniteRow0Parent0Split100Sub0_componentProductActual_order17_point_interval_generated` is present.
- order-17 source-center data is still symmetric, coming from the proof-grade absolute derivative majorant, but it is now wired through the signed point receiver instead of blocking the factor point row surface.
- the final collapsed point-row Rat payload is now present in `PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16CollapsedDegree0PointSlopeRatPayload.lean`; it uses the tight active-scale interval, four-corner multiplication, and exact nominal derivative point evaluation.
- this is not a Step33A.1-A closure claim: the remaining layer is the budget/sign/tightness audit needed to turn the proof-grade point row into the point-slope kill.

## Verdict

`STEP33_A1_SUB0_COMBINED_ORDER16_COLLAPSED_DEGREE0_POINT_SLOPE_RAT_POINT_ROW_BUDGET_KILL_GAP`: Rat payload exists and Lean-checks, but the point-slope budget kill is still open.
