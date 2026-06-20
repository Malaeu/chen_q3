# Step33A.1-A Sub0 Segmented Residual-Derivative Payload

Fail-closed skeleton.  This is not Lean proof data.

## Summary

- schema: `q3_psdpd_step33_a1_sub0_segmented_residual_deriv_interval_payload.v4`
- route: `STEP33_A1_SUB0_SEGMENTED_RESIDUAL_DERIV`
- status: `fail_closed_missing_full_taylor_residual_interval_proof`
- proof mode: `exact_rational_same_expression_interval`
- target slope: `1866608532757/500000000000000000000000000000`
- segment count: `1`
- coverage passed: `True`
- adjacency passed: `True`
- budget passed: `True`
- proof-safe closed fields: `0`
- Lean emitted: `False`

## Lean Interfaces

- checkerFile: `Q3/Proofs/PSD_CenteredCoeffRawOmegaAChunkTaylorChecker.lean`
- checkerStructure: `ResidualDerivativeSegmentIntervalCert`
- checkerSingleConstructor: `ResidualDerivativeSegmentIntervalCert.single`
- checkerPreferredValidity: `ResidualDerivativeSegmentIntervalCert.DirectValid`
- checkerPreferredSingleValidityConstructor: `ResidualDerivativeSegmentIntervalCert.DirectValid.of_single_residual_bounds`
- checkerPreferredTheorem: `ResidualDerivativeSegmentIntervalCert.DirectValid.residual_norm_le`
- checkerLedgerValidity: `ResidualDerivativeSegmentIntervalCert.Valid`
- checkerLedgerSingleValidityConstructor: `ResidualDerivativeSegmentIntervalCert.Valid.of_single_bounds`
- landingFile: `Q3/Proofs/PSD_CenteredCoeffRawOmegaAHRawLanding.lean`
- sub0ClosedFormResidualDerivativeBridge: `primaryFiniteRow0Parent0Split100Sub0_residual_deriv_eq_closedForm_sub_polynomial_deriv`
- sub0DerivmodelAdapterMismatchFence: `primaryFiniteRow0Parent0Split100Sub0_derivmodel_coeff_zero_mismatch_current_adapter_coeff`
- sub0FullTaylorCoeff: `primaryFiniteRow0Parent0Split100Sub0RawTaylorCoeff`
- sub0FullTaylorCert: `primaryFiniteRow0Parent0Split100Sub0RawTaylorCoeffCert`
- sub0FullTaylorPolynomialDerivativeCrosswalk: `primaryFiniteRow0Parent0Split100Sub0_fullTaylor_polynomial_deriv_eq_derivmodel`
- sub0FullTaylorResidualDerivativeCrosswalk: `primaryFiniteRow0Parent0Split100Sub0_fullTaylor_residual_deriv_eq_closedForm`
- sub0ConcreteSegmentData: `primaryFiniteRow0Parent0Split100Sub0DirectResidualSegmentCert`
- sub0ClosedFormValidityBridge: `primaryFiniteRow0Parent0Split100Sub0_direct_segment_cert_valid_of_closedForm_residual_bounds`
- sub0ClosedFormProofDataWrapper: `primaryFiniteRow0Parent0Split100Sub0_cellSlopeExactIntegralProofData_of_checked_hRawCenterCoeffAbs_and_closedForm_residual_bounds`
- sub0PreferredNormWrapper: `primaryFiniteRow0Parent0Split100Sub0_residual_deriv_norm_bound_of_direct_segment_cert`
- sub0PreferredProofDataWrapper: `primaryFiniteRow0Parent0Split100Sub0_cellSlopeExactIntegralProofData_of_checked_hRawCenterCoeffAbs_and_direct_segment_interval_cert`
- sub0LedgerProofDataWrapper: `primaryFiniteRow0Parent0Split100Sub0_cellSlopeExactIntegralProofData_of_checked_hRawCenterCoeffAbs_and_segment_interval_cert`

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

## Candidate Segments

- cell `0`:
  segment = `[0, 1/10]`
  residual = `[-94119513411/500000000000000000000000000000, 1866608532757/500000000000000000000000000000]`
  budgetPassesExactRational = `True`
  sourceProofStatus = `sampled_candidate_not_lean_proof`
  analyticResidualBoundsProof = `missing`

## Candidate Arithmetic

- coveragePassedExactRational: `True`
- adjacencyPassedExactRational: `True`
- segmentNonemptyPassedExactRational: `True`
- budgetPassedExactRational: `True`
- candidateReadyForLeanShape: `True`
- proofGradeResidualBoundsPresent: `False`
- proofGradeClosedFormResidualBoundsPresent: `False`
- proofGradeFullTaylorResidualBoundsPresent: `False`
- fullTaylorPolynomialDerivativeCrosswalkPresent: `True`
- fullTaylorResidualDerivativeCrosswalkPresent: `True`

## Rational Proof Obligations

- exact segment coverage of Set.Icc 0 (1/10) (candidate passes)
- exact segment adjacency/no-gap proof (candidate passes)
- proof-grade bounds for primaryFiniteRow0Parent0Split100Sub0RawIntegrandDerivClosedForm eta - rawOmegaATaylorPolynomial 15 (1/20) primaryFiniteRow0Parent0Split100Sub0ResidualDerivmodelCoeff eta on Set.Icc 0 (1/10) (missing)
- do not replace deriv current-adapter polynomial by the generated degree-15 derivmodel polynomial: Lean checks a coefficient mismatch; use the full Taylor cert crosswalk instead
- for every segment: -1866608532757/500000000000000000000000000000 <= residualLower (candidate passes)
- for every segment: residualUpper <= 1866608532757/500000000000000000000000000000 (candidate passes)
- checked full Taylor bridge: deriv residual equals the closed-form raw derivative minus the generated degree-15 derivative model
- current-adapter closed-form bridge is checked but is not the sampled full Taylor residual source
- optional ledger: proof-grade raw derivative enclosure per segment
- optional ledger: proof-grade polynomial derivative enclosure per segment

## Failure Codes

- `STEP33_A1_SUB0_RESIDUAL_DERIV_SAME_UNIT_SEGMENT_CERT_FAIL`
- `STEP33_A1_SUB0_RESIDUAL_INTERVAL_PROOF_MISSING`
- `STEP33_A1_SUB0_FULL_TAYLOR_RESIDUAL_INTERVAL_BOUNDS_MISSING`
- `STEP33_A1_SUB0_DERIVMODEL_ADAPTER_POLYNOMIAL_MISMATCH`

## Guard

- not Lean proof data
- do not trust sampled direct-derivative overlay as proof
- do not spend bounds for RawCenterCoeffOnlyCert as bounds for the full Taylor candidate
- do not spend independent raw/poly boxes unless the residual interval itself fits
- do not emit generated Lean payload until all segment obligations close
- the spendable field is the direct same-unit residual derivative interval

## Source Status

- interpolation payload status: `blocked_missing_exact_interpolation_inputs`
- interpolation first danger point: `STEP33_A1_SUB0_DERIVMODEL_BUDGET_FAIL`
- direct overlay status: `direct_derivative_overlay_seeded_missing_cell_slope_norm_proofs`
- full Taylor residual crosswalk: `checked_in_lean`

The diagnostic direct-overlay candidate now supplies a one-segment
candidate whose exact rational coverage and budget arithmetic pass.
The full Taylor residual derivative crosswalk is now checked in Lean.
The candidate remains non-spendable because the proof-grade interval
bound for that full Taylor residual expression is still missing; only
a proof-grade `ResidualDerivativeSegmentIntervalCert.DirectValid`
witness can close the preferred receiver.  The richer `Valid` witness
remains available only when a separate raw/poly ledger is also proved.
