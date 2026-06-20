# Step33A.1-A Sub0 Segmented Residual-Derivative Payload

Fail-closed skeleton.  This is not Lean proof data.

## Summary

- schema: `q3_psdpd_step33_a1_sub0_segmented_residual_deriv_interval_payload.v1`
- route: `STEP33_A1_SUB0_SEGMENTED_RESIDUAL_DERIV`
- status: `fail_closed_missing_segment_cert`
- proof mode: `exact_rational_same_expression_interval`
- target slope: `1866608532757/500000000000000000000000000000`
- segment count: `0`
- proof-safe closed fields: `0`
- Lean emitted: `False`

## Lean Interfaces

- checkerFile: `Q3/Proofs/PSD_CenteredCoeffRawOmegaAChunkTaylorChecker.lean`
- checkerStructure: `ResidualDerivativeSegmentIntervalCert`
- checkerValidity: `ResidualDerivativeSegmentIntervalCert.Valid`
- checkerTheorem: `ResidualDerivativeSegmentIntervalCert.Valid.residual_norm_le`
- landingFile: `Q3/Proofs/PSD_CenteredCoeffRawOmegaAHRawLanding.lean`
- sub0NormWrapper: `primaryFiniteRow0Parent0Split100Sub0_residual_deriv_norm_bound_of_segment_cert`
- sub0ProofDataWrapper: `primaryFiniteRow0Parent0Split100Sub0_cellSlopeExactIntegralProofData_of_checked_hRawCenterCoeffAbs_and_segment_interval_cert`

## Certificate Fields

- `segmentCount`
- `segmentL`
- `segmentU`
- `rawLower`
- `rawUpper`
- `polyLower`
- `polyUpper`
- `residualLower`
- `residualUpper`

## Rational Proof Obligations

- exact segment coverage of Set.Icc 0 (1/10)
- exact segment adjacency/no-gap proof
- residualDeriv eta = rawDeriv eta - polyDeriv eta on the cell
- proof-grade raw derivative enclosure per segment
- proof-grade polynomial derivative enclosure per segment
- same-expression direct residual derivative enclosure per segment
- for every segment: -1866608532757/500000000000000000000000000000 <= residualLower
- for every segment: residualUpper <= 1866608532757/500000000000000000000000000000

## Failure Codes

- `STEP33_A1_SUB0_RESIDUAL_DERIV_SAME_UNIT_SEGMENT_CERT_FAIL`
- `STEP33_A1_SUB0_SEGMENT_PROOF_INPUTS_MISSING`

## Guard

- not Lean proof data
- do not trust sampled direct-derivative overlay as proof
- do not spend independent raw/poly boxes unless the residual interval itself fits
- do not emit generated Lean payload until all segment obligations close
- the spendable field is the direct same-unit residual derivative interval

## Source Status

- interpolation payload status: `blocked_missing_exact_interpolation_inputs`
- interpolation first danger point: `STEP33_A1_SUB0_DERIVMODEL_BUDGET_FAIL`
- direct overlay status: `direct_derivative_overlay_seeded_missing_cell_slope_norm_proofs`

The diagnostic direct-overlay candidate remains non-spendable unless
a proof-grade same-expression segment certificate supplies the
`ResidualDerivativeSegmentIntervalCert.Valid` witness.
