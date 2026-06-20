# Step33A.1-A Sub0 Cancellation Residual Interval Certificate

Fail-closed ledger. This is not Lean proof data and does not close
Step33A.1-A.

## Status

- schema: `q3_psdpd_step33_a1_sub0_cancellation_residual_interval_certificate.v1`
- route: `STEP33_A1_SUB0_CANCELLATION_RESIDUAL_INTERVAL`
- status: `fail_closed_missing_component_taylor_remainder_bounds`
- first failure: `STEP33_A1_SUB0_COMPONENT_TAYLOR_BOUNDS_MISSING`
- Lean emitted: `False`
- proof-safe closed fields: `0`
- exact coefficient extraction done: `True`
- component Taylor bounds proved: `False`
- exact coefficient assembly proved: `False`
- residual range proved: `False`

## Target

- cell: `[0, 1/10]`
- center: `1/20`
- radius: `1/20`
- target lower: `-94119513411/500000000000000000000000000000`
- target upper: `1866608532757/500000000000000000000000000000`
- target width: `245091005771/62500000000000000000000000000`
- expression: `primaryFiniteRow0Parent0Split100Sub0RawIntegrandDerivClosedForm eta - rawOmegaATaylorPolynomial 15 (1/20) primaryFiniteRow0Parent0Split100Sub0ResidualDerivmodelCoeff eta`
- target theorem: `primaryFiniteRow0Parent0Split100Sub0_fullTaylor_residual_deriv_closedForm_interval`

```text
theorem primaryFiniteRow0Parent0Split100Sub0_fullTaylor_residual_deriv_closedForm_interval {eta : Real} (heta : eta in Set.Icc 0 (1/10)) : -94119513411/500000000000000000000000000000 <= targetExpression eta and targetExpression eta <= 1866608532757/500000000000000000000000000000
```

## Lean Consumers

- directSegmentData: `primaryFiniteRow0Parent0Split100Sub0DirectResidualSegmentCert` (line 2726)
- directValidityBridge: `primaryFiniteRow0Parent0Split100Sub0_fullTaylor_direct_segment_cert_valid_of_residual_bounds` (line 2815)
- proofDataWrapper: `primaryFiniteRow0Parent0Split100Sub0_fullTaylor_cellSlopeExactIntegralProofData_of_checked_hRawCenterCoeffAbs_and_residual_bounds` (line 2868)
- polynomialDerivativeCrosswalk: `primaryFiniteRow0Parent0Split100Sub0_fullTaylor_polynomial_deriv_eq_derivmodel` (line 201)
- residualDerivativeCrosswalk: `primaryFiniteRow0Parent0Split100Sub0_fullTaylor_residual_deriv_eq_closedForm` (line 1912)

## Extracted Full Taylor Polynomial Derivative Coefficients

These are extracted from the local Lean definition
`primaryFiniteRow0Parent0Split100Sub0ResidualDerivmodelCoeff`. They are exact rationals, but extraction is
bookkeeping only; it is not the missing interval proof.

| i | coeff | source line |
| --- | --- | --- |
| 0 | `2814585322345983/31250000000000000` | 49 |
| 1 | `432682670395380743/250000000000000000` | 50 |
| 2 | `-2076189217694411487/1000000000000000000` | 51 |
| 3 | `-155822302127901237/12500000000000000` | 52 |
| 4 | `248352666423100477/12500000000000000` | 53 |
| 5 | `32291651785944130749/500000000000000000` | 54 |
| 6 | `-69999411432932463909/500000000000000000` | 55 |
| 7 | `-34707798540256129409/125000000000000000` | 56 |
| 8 | `836575734719049511113/1000000000000000000` | 57 |
| 9 | `100643501888413806697/100000000000000000` | 58 |
| 10 | `-897573400754971084771/200000000000000000` | 59 |
| 11 | `-142205390337268351947/50000000000000000` | 60 |
| 12 | `5554290524724778241613/250000000000000000` | 61 |
| 13 | `916884525703826724093/250000000000000000` | 62 |
| 14 | `-19999872807938988432933/200000000000000000` | 63 |
| 15 | `62148786708414316877/2500000000000000` | 64 |

## Required Component Inputs

- `omegaCoeff[]`
- `omegaRemainderAbs`
- `omegaDerivCoeff[]`
- `omegaDerivRemainderAbs`
- `shapeCoeff[]`
- `shapeRemainderAbs`
- `shapeDerivCoeff[]`
- `shapeDerivRemainderAbs`
- `exact product/convolution assembly before interval spending`

## Required Proof-Grade Certificate

- kind: `interval_or_rational_same_expression_residual_bound`
- may feed: `ResidualDerivativeSegmentIntervalCert.DirectValid.of_single_residual_bounds`
- must prove: for all eta in Set.Icc 0 (1/10), targetLower <= RawIntegrandDerivClosedForm eta - rawOmegaATaylorPolynomial 15 (1/20) ResidualDerivmodelCoeff eta <= targetUpper

Must not use:
- sampled direct-derivative overlay as proof
- independent raw/poly interval boxes as the proof object
- RawCenterCoeffOnlyCert residual bounds for the full Taylor route

## Segmented Payload Cross-Check

- exists: `True`
- schema: `q3_psdpd_step33_a1_sub0_segmented_residual_deriv_interval_payload.v6`
- status: `fail_closed_missing_cancellation_preserving_taylor_remainder_proof`
- proof-safe closed fields: `0`
- Lean emitted: `False`
- segment count: `1`
- coverage passed: `True`
- all segments budget passed: `True`

## Source Definition Lines

- `primaryFiniteRow0Parent0Split100Sub0ResidualDerivmodelCoeff`: `46`
- `primaryFiniteRow0Parent0Split100Sub0RawTaylorCoeff`: `132`
- `primaryFiniteRow0Parent0Split100Sub0RawTaylorCoeffCert`: `190`
- `primaryFiniteRow0Parent0Split100Sub0_fullTaylor_polynomial_deriv_eq_derivmodel`: `201`
- `primaryFiniteRow0Parent0Split100Sub0_fullTaylor_residual_deriv_eq_closedForm`: `1912`
- `primaryFiniteRow0Parent0Split100Sub0DirectResidualSegmentCert`: `2726`
- `primaryFiniteRow0Parent0Split100Sub0_fullTaylor_direct_segment_cert_valid_of_residual_bounds`: `2815`
- `primaryFiniteRow0Parent0Split100Sub0_fullTaylor_cellSlopeExactIntegralProofData_of_checked_hRawCenterCoeffAbs_and_residual_bounds`: `2868`
- `primaryFiniteRow0Parent0Split100Sub0ResidualDerivmodelCoeff_end`: `65`

## Failure Codes

- `STEP33_A1_SUB0_COMPONENT_TAYLOR_BOUNDS_MISSING`
- `STEP33_A1_SUB0_ASSEMBLED_RESIDUAL_RANGE_PROOF_MISSING`
- `STEP33_A1_SUB0_CANCELLATION_INTERVAL_LEAN_PAYLOAD_MISSING`
- `STEP33_A1_SUB0_CANCELLATION_PRESERVING_TAYLOR_REMAINDER_GAP`

## Decision

The route-A Lean receiver and crosswalk names are present, and the
full Taylor derivative-model coefficients have been extracted from
the local Lean source. The current gap is narrower but still open:
there is no component Taylor/remainder certificate that assembles the
same residual expression before spending the interval remainder.
Therefore no Lean payload is emitted and Step33A.1-A remains open.
