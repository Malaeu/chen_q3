# Step33A.1-A Taylor Payload Lean Emitter Guard

This report says whether the current proof-data contract is ready for
`RawOmegaAChunkTaylorPayload.PayloadFin` Lean emission.

## Verdict

- status: `missing_proof_data_no_lean_emitted`
- reason: Proof data is incomplete; emitting a Lean payload here would turn missing Taylor/model facts into a fake trusted import.
- payload type: `RawOmegaAChunkTaylorPayload.PayloadFin`
- Step33A wrapper: `RawOmegaAChunkTaylorPayload.PayloadFin.toDirectTailWindowInputs`
- Step33B/33C wrapper: `psd_step33_rawOmega_finite_analytic_and_singleton_handoff_of_rawOmegaADirectTailWindowInputs`
- chunk proof wrapper: `RawOmegaATaylorModelCertificate.ComponentChunkProofData`
- product corner receiver: `RawOmegaATaylorModelCertificate.product_bounds_of_eight_corners`
- product scale-interval receiver: `RawOmegaATaylorModelCertificate.product_bounds_of_scale_interval_and_sixteen_corners`
- proof-data source: `q3.lean.aristotle/ACTIVE/requests/step33_bootstrap/a_chunk_taylor_payload_omega_log_seed.json`
- intended Lean output: `/Users/emalam/Documents/GitHub/rh_lean_01_2026/q3.lean.aristotle/Q3/Proofs/PSD_CenteredCoeffRawOmegaAChunkTaylorGeneratedPayloadImport.lean`
- Lean output written: `False`
- ready path implemented: `True`
- ready path requires: `lake env lean on generated payload import`

## Counts

- families: `4`
- distance rows: `92`
- chunk cells: `2392`
- complete rows: `0`
- complete cells: `0`
- missing cells: `2392`

## Families

| family | rows | chunks | cells | complete rows | complete cells | missing cells |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| primary_finite | 23 | 26 | 598 | 0 | 0 | 598 |
| primary_tail | 23 | 26 | 598 | 0 | 0 | 598 |
| control_finite | 23 | 26 | 598 | 0 | 0 | 598 |
| control_tail | 23 | 26 | 598 | 0 | 0 | 598 |

## Missing Field Counts

- `cell.coeff`: `2392`
- `cell.componentProductScaleCornerLowerLLLL`: `2392`
- `cell.componentProductScaleCornerLowerLLLU`: `2392`
- `cell.componentProductScaleCornerLowerLLUL`: `2392`
- `cell.componentProductScaleCornerLowerLLUU`: `2392`
- `cell.componentProductScaleCornerLowerLULL`: `2392`
- `cell.componentProductScaleCornerLowerLULU`: `2392`
- `cell.componentProductScaleCornerLowerLUUL`: `2392`
- `cell.componentProductScaleCornerLowerLUUU`: `2392`
- `cell.componentProductScaleCornerLowerULLL`: `2392`
- `cell.componentProductScaleCornerLowerULLU`: `2392`
- `cell.componentProductScaleCornerLowerULUL`: `2392`
- `cell.componentProductScaleCornerLowerULUU`: `2392`
- `cell.componentProductScaleCornerLowerUULL`: `2392`
- `cell.componentProductScaleCornerLowerUULU`: `2392`
- `cell.componentProductScaleCornerLowerUUUL`: `2392`
- `cell.componentProductScaleCornerLowerUUUU`: `2392`
- `cell.componentProductScaleCornerUpperLLLL`: `2392`
- `cell.componentProductScaleCornerUpperLLLU`: `2392`
- `cell.componentProductScaleCornerUpperLLUL`: `2392`
- `cell.componentProductScaleCornerUpperLLUU`: `2392`
- `cell.componentProductScaleCornerUpperLULL`: `2392`
- `cell.componentProductScaleCornerUpperLULU`: `2392`
- `cell.componentProductScaleCornerUpperLUUL`: `2392`
- `cell.componentProductScaleCornerUpperLUUU`: `2392`
- `cell.componentProductScaleCornerUpperULLL`: `2392`
- `cell.componentProductScaleCornerUpperULLU`: `2392`
- `cell.componentProductScaleCornerUpperULUL`: `2392`
- `cell.componentProductScaleCornerUpperULUU`: `2392`
- `cell.componentProductScaleCornerUpperUULL`: `2392`
- `cell.componentProductScaleCornerUpperUULU`: `2392`
- `cell.componentProductScaleCornerUpperUUUL`: `2392`
- `cell.componentProductScaleCornerUpperUUUU`: `2392`
- `cell.degree`: `2392`
- `cell.diffLower`: `2392`
- `cell.diffUpper`: `2392`
- `cell.integralLower`: `2392`
- `cell.integralUpper`: `2392`
- `cell.omegaLower`: `46`
- `cell.omegaLowerBound`: `46`
- `cell.omegaUpper`: `46`
- `cell.omegaUpperBound`: `46`
- `cell.polyLower`: `2392`
- `cell.polyLowerSum`: `2392`
- `cell.polyUpper`: `2392`
- `cell.polyUpperSum`: `2392`
- `cell.polynomialTermBounds`: `2392`
- `cell.rawLower`: `2392`
- `cell.rawUpper`: `2392`
- `cell.remainder`: `2392`
- `cell.remainderNonneg`: `2392`
- `cell.termLower`: `2392`
- `cell.termUpper`: `2392`

## Product Proof Strategy

For `hProductLower` and `hProductUpper`, the emitter accepts direct universal proof fields, the full exact-scale eight-corner packet, or a family-scale interval with sixteen scale/omega/shape/cos corners. This route is sign-generic and remains valid on early finite chunks where the raw Step22 omega weight is negative.

Direct fields:
- `componentProductLower`
- `componentProductUpper`

Corner receiver: `RawOmegaATaylorModelCertificate.product_bounds_of_eight_corners`

Lower corner fields:
- `componentProductCornerLowerLLL`
- `componentProductCornerLowerLLU`
- `componentProductCornerLowerLUL`
- `componentProductCornerLowerLUU`
- `componentProductCornerLowerULL`
- `componentProductCornerLowerULU`
- `componentProductCornerLowerUUL`
- `componentProductCornerLowerUUU`

Upper corner fields:
- `componentProductCornerUpperLLL`
- `componentProductCornerUpperLLU`
- `componentProductCornerUpperLUL`
- `componentProductCornerUpperLUU`
- `componentProductCornerUpperULL`
- `componentProductCornerUpperULU`
- `componentProductCornerUpperUUL`
- `componentProductCornerUpperUUU`

Scale-interval receiver: `RawOmegaATaylorModelCertificate.product_bounds_of_scale_interval_and_sixteen_corners`

Scale-interval fields:
- `scaleLower`
- `scaleUpper`
- `scaleLowerBound`
- `scaleUpperBound`
- `componentProductScaleCornerLowerLLLL`
- `componentProductScaleCornerLowerLLLU`
- `componentProductScaleCornerLowerLLUL`
- `componentProductScaleCornerLowerLLUU`
- `componentProductScaleCornerLowerLULL`
- `componentProductScaleCornerLowerLULU`
- `componentProductScaleCornerLowerLUUL`
- `componentProductScaleCornerLowerLUUU`
- `componentProductScaleCornerLowerULLL`
- `componentProductScaleCornerLowerULLU`
- `componentProductScaleCornerLowerULUL`
- `componentProductScaleCornerLowerULUU`
- `componentProductScaleCornerLowerUULL`
- `componentProductScaleCornerLowerUULU`
- `componentProductScaleCornerLowerUUUL`
- `componentProductScaleCornerLowerUUUU`
- `componentProductScaleCornerUpperLLLL`
- `componentProductScaleCornerUpperLLLU`
- `componentProductScaleCornerUpperLLUL`
- `componentProductScaleCornerUpperLLUU`
- `componentProductScaleCornerUpperLULL`
- `componentProductScaleCornerUpperLULU`
- `componentProductScaleCornerUpperLUUL`
- `componentProductScaleCornerUpperLUUU`
- `componentProductScaleCornerUpperULLL`
- `componentProductScaleCornerUpperULLU`
- `componentProductScaleCornerUpperULUL`
- `componentProductScaleCornerUpperULUU`
- `componentProductScaleCornerUpperUULL`
- `componentProductScaleCornerUpperUULU`
- `componentProductScaleCornerUpperUUUL`
- `componentProductScaleCornerUpperUUUU`

## Route Guard

- do not emit Lean from skeleton, null, or omitted proof fields
- do not use Arb/acb numeric probe intervals as trusted proof data
- do not mutate A CSV, ARadius, radius-floor, or LDL
- do not call Step33A.1-A closed until PayloadFin compiles
