# Step33A.1-A Sub0 Combined Cancellation Interval Certificate

Fail-closed certificate ledger.  This is not Lean proof data and does
not close Step33A.1-A.

## Summary

- schema: `q3_psdpd_step33_a1_sub0_combined_cancellation_interval_certificate.v1`
- route: `STEP33_A1_SUB0_COMBINED_CANCELLATION_INTERVAL`
- status: `fail_closed_missing_proof_grade_combined_interval_certificate`
- first failure: `STEP33_A1_SUB0_COMBINED_CANCELLATION_INTERVAL_CERT_GAP`
- target lower: `-94119513411/500000000000000000000000000000`
- target upper: `1866608532757/500000000000000000000000000000`
- target width: `245091005771/62500000000000000000000000000`

## Lean Surface

- file: `Q3/Proofs/PSD_CenteredCoeffRawOmegaAComponentTaylorCancellationCombinedInterval.lean`
- certCheckerFile: `Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationIntervalCert.lean`
- conditionalPayloadFile: `Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationIntervalPayload.lean`
- certStructure: `Step33Sub0CombinedCancellationIntervalCert`
- certValidPredicate: `Step33Sub0CombinedCancellationIntervalCert.Valid`
- certToHCombined: `Step33Sub0CombinedCancellationIntervalCert.Valid.to_hCombined`
- conditionalRemainderProp: `primaryFiniteRow0Parent0Split100Sub0CombinedCancellationRemainderSourceProp`
- conditionalPayloadTheorem: `primaryFiniteRow0Parent0Split100Sub0_combinedCancellationInterval_valid_of_remainder_bound`
- conditionalHCombinedTheorem: `primaryFiniteRow0Parent0Split100Sub0_combinedCancellation_hCombined_of_remainder_bound`
- expression: `primaryFiniteRow0Parent0Split100Sub0CombinedCancellationIntervalExpr`
- consumerTheorem: `primaryFiniteRow0Parent0Split100Sub0_fullTaylor_residual_deriv_interval_of_combined_bounds`
- closedFormTheorem: `primaryFiniteRow0Parent0Split100Sub0_fullTaylor_closedForm_residual_bounds_of_combined_bounds`
- proofDataWrapper: `primaryFiniteRow0Parent0Split100Sub0_fullTaylor_cellSlopeExactIntegralProofData_of_checked_hRawCenterCoeffAbs_and_combined_bounds`
- boundInputsFile: `Q3/Proofs/PSD_CenteredCoeffRawOmegaAComponentTaylorCancellationBoundInputs.lean`
- normReceiverFile: `Q3/Proofs/PSD_CenteredCoeffRawOmegaAComponentTaylorCancellationNormReceiver.lean`
- p45BridgeFile: `Q3/Proofs/PSD_CenteredCoeffRawOmegaAComponentTaylorCancellationP45Bridge.lean`
- landingFile: `Q3/Proofs/PSD_CenteredCoeffRawOmegaAHRawLanding.lean`

Target statement:

```text
forall eta in Set.Icc (0 : Real) ((1 : Real) / 10), (-94119513411/500000000000000000000000000000) <= primaryFiniteRow0Parent0Split100Sub0CombinedCancellationIntervalExpr eta and primaryFiniteRow0Parent0Split100Sub0CombinedCancellationIntervalExpr eta <= (1866608532757/500000000000000000000000000000)
```

Combined expression:

`rawOmegaATaylorPolynomial assembledDegree 1/20 ResidualTaylorCoeff eta + ScaledCancellationRhs eta`

## Proof Status

- isLeanProofData: `False`
- outLeanWritten: `False`
- conditionalPayloadPresent: `True`
- conditionalPayloadIsUnconditionalProof: `False`
- proofSafeClosedFields: `0`
- combinedReceiverCheckedInLean: `True`
- combinedExpressionDefinedInLean: `True`
- combinedIntervalTheoremCheckedInLean: `True`
- proofGradeCombinedBoundsPresent: `False`
- sampledCandidateIsProof: `False`
- segmentCoveragePassedExactRational: `True`
- allSegmentsBudgetPassedExactRational: `True`
- allSegmentsProofGrade: `False`

## Candidate Segments

- cell `0`:
  segment = `[0, 1/10]`
  combined = `[-94119513411/500000000000000000000000000000, 1866608532757/500000000000000000000000000000]`
  budgetPassesExactRational = `True`
  sourceProofStatus = `sampled_candidate_not_lean_proof`
  isProofGrade = `False`
  proofGradeCombinedBounds = `missing`

## Candidate Arithmetic

- coverage.coveragePassedExactRational: `True`
- coverage.adjacencyPassedExactRational: `True`
- coverage.segmentNonemptyPassedExactRational: `True`
- coverage.leftEndpoint: `0`
- coverage.rightEndpoint: `1/10`
- coverage.expectedLeftEndpoint: `0`
- coverage.expectedRightEndpoint: `1/10`
- coverage.firstFailure: `None`
- budgetPassedExactRational: `True`
- candidateReadyForLeanShape: `True`
- proofGradeCombinedBoundsPresent: `False`

## Required Certificate

- kind: `proof_grade_interval_or_rational_certificate`
- must prove: `same-expression lower/upper bound for the whole combined expression`

May use:
- rational interval arithmetic
- Lean-verifiable matrix/free polynomial interval certificate
- independently checkable generated rational output

Must not use:
- sampled JSON as proof
- separate norm bounds for residualTaylor polynomial and ScaledCancellationRhs
- independent raw/poly interval subtraction
- product-budget rows route after width-fail

## Closed Local Facts

- OmegaPrime generated Taylor remainder cert is Valid and has a public bound.
- Omega Taylor bound is obtained by integrating OmegaPrime plus anchor interval.
- rawDeriv - assembledPoly equals the scaled cancellation RHS.
- deriv residual equals residualTaylor P45 polynomial plus ScaledCancellationRhs.
- triangle split is killed by checked residualTaylor final-slope failures.
- rows0..11 independent product budget is width-killed.

## Rejected Routes

- independentTriangleSplit: killed: residualTaylor polynomial alone exceeds final slope at the center
- rowsProductBudgetRefinement: not a closure path while it preserves the independent product-budget style
- sampledSegmentPayload: diagnostic only, not proof evidence

## Candidate Source

- path: `/Users/emalam/Documents/GitHub/rh_lean_01_2026/q3.lean.aristotle/ACTIVE/requests/step33_bootstrap/step33_a1_sub0_segmented_residual_deriv_interval_payload.json`
- exists: `True`
- schema: `q3_psdpd_step33_a1_sub0_segmented_residual_deriv_interval_payload.v6`
- status: `fail_closed_missing_cancellation_preserving_taylor_remainder_proof`
- proofMode: `exact_rational_same_expression_interval`
- sourceIsProofGrade: `False`
- interpretation: `The candidate records exact rational coverage and budget checks, but its sourceProofStatus remains sampled_candidate_not_lean_proof.`

## Next Implementable Patch

- recommendation: `prove the proof-grade whole-expression remainder source consumed by the conditional combined-cancellation payload`
- firstFailureIfMissing: `STEP33_A1_SUB0_COMBINED_CANCELLATION_INTERVAL_CERT_GAP`
- leanPayloadTarget: `Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationIntervalPayload.lean`
- checkerTheorem: `primaryFiniteRow0Parent0Split100Sub0_combinedCancellationInterval_valid_of_remainder_bound`
- remainingGap: `STEP33_A1_SUB0_COMBINED_CANCELLATION_TAYLOR_MODEL_SOURCE_GAP`

## Failure Codes

- `STEP33_A1_SUB0_COMBINED_CANCELLATION_INTERVAL_CERT_GAP`
- `STEP33_A1_SUB0_COMBINED_INTERVAL_PROOF_GRADE_SOURCE_MISSING`
- `STEP33_A1_SUB0_COMBINED_INTERVAL_LEAN_PAYLOAD_MISSING`
- `STEP33_A1_SUB0_CANCELLATION_PRESERVING_TAYLOR_REMAINDER_GAP`

## Source Hashes

- `Q3/Proofs/PSD_CenteredCoeffRawOmegaAComponentTaylorCancellationCombinedInterval.lean`: `d3ce443f3d86cc33`
- `Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationIntervalCert.lean`: `172524e28455ca5b`
- `Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationIntervalPayload.lean`: `2cf0833b5b65c1f7`
- `Q3/Proofs/PSD_CenteredCoeffRawOmegaAComponentTaylorCancellationBoundInputs.lean`: `c8832f56435b42fa`
- `Q3/Proofs/PSD_CenteredCoeffRawOmegaAComponentTaylorCancellationNormReceiver.lean`: `8554b282c60d9c25`
- `Q3/Proofs/PSD_CenteredCoeffRawOmegaAComponentTaylorCancellationP45Bridge.lean`: `aabf02168d6d50fd`
- `Q3/Proofs/PSD_CenteredCoeffRawOmegaAHRawLanding.lean`: `3074c575ace73694`
- `ACTIVE/requests/step33_bootstrap/step33_a1_sub0_segmented_residual_deriv_interval_payload.json`: `df8cb8dff74f605e`
