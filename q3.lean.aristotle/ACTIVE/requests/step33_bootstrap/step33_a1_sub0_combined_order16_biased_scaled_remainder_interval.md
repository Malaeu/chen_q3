# Step33A.1-A Biased Scaled-Remainder Interval Ledger

schema: `q3_psdpd_step33_a1_sub0_combined_order16_biased_scaled_remainder_interval.v1`
route: `biased_scaled_remainder_whole_expression_interval`
proofStatus: `biased_scaled_remainder_interval_surface_checked_missing_interval_cert`

## Status

- payloadInterfacePresent: `True`
- remainderBridgePresent: `True`
- proofGrade: `False`
- wholeExpressionIntervalRowsLeanChecked: `False`
- segmentCoverLeanChecked: `False`
- budgetRowsLeanChecked: `False`
- scaledRemainderSourcePropClaimed: `False`
- residualRemainderRowsClaimed: `False`
- step33A1ClosedClaimed: `False`
- doNotSplitSummands: `True`

## Payload Symbols

- `Step33Sub0CombinedOrder16BiasedScaledRemainderIntervalSegmentCert`: `True`
- `Step33Sub0CombinedOrder16BiasedScaledRemainderIntervalSegmentCover`: `True`
- `Step33Sub0CombinedOrder16BiasedScaledRemainderIntervalFamilyCert`: `True`
- `primaryFiniteRow0Parent0Split100Sub0BiasedScaledRemainderIntervalPayloadTarget`: `True`
- `primaryFiniteRow0Parent0Split100Sub0_scaledRemainderSourceProp_of_interval_payload_target`: `True`
- `primaryFiniteRow0Parent0Split100Sub0_biasedResidualHorner_residualRemainder_of_scaledRemainder_interval_payload`: `True`

## Remainder Bridge Symbols

- `primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedResidualHornerScaledRemainder`: `True`
- `primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedResidualHornerScaledRemainderSourceProp`: `True`
- `primaryFiniteRow0Parent0Split100Sub0_biasedResidualHorner_residualRemainder_of_scaledRemainder_bound`: `True`

## Current Gap

`STEP33_A1_SUB0_COMBINED_ORDER16_BIASED_RESIDUAL_HORNER_SCALED_REMAINDER_BOUND_GAP`

Parent gap:

`STEP33_A1_SUB0_COMBINED_ORDER16_BIASED_RESIDUAL_HORNER_REMAINDER_ROWS_GAP`

First failure code if the new route fails:

`INTERVAL_CERT_GAP`

## Certificate Shape

- per segment: cellL, cellU, lower, upper, remainderAbs
- proof-grade interval for the complete signed scaled remainder
- -remainderAbs <= lower
- upper <= remainderAbs
- finite segment cover of [0, 1/10]
- global residualAbs equal to BiasedResidualRemainderAbs

## Upstream Evidence

### residualHornerLedger

- `path`: `ACTIVE/requests/step33_bootstrap/step33_a1_sub0_biased_residual_horner_payload.json`
- `exists`: `True`
- `proofStatus`: `biased_residual_horner_remainder_bridge_checked_missing_scaled_remainder_bound`
- `currentGap`: `STEP33_A1_SUB0_COMBINED_ORDER16_BIASED_RESIDUAL_HORNER_SCALED_REMAINDER_BOUND_GAP`
- `proofGrade`: `False`
- `scaledRemainderBoundLeanChecked`: `False`
- `residualRemainderInterfaceLeanChecked`: `True`

### segmentedResidualDerivativeLedger

- `path`: `ACTIVE/requests/step33_bootstrap/step33_a1_sub0_segmented_residual_deriv_interval_payload.json`
- `exists`: `True`
- `status`: `fail_closed_missing_cancellation_preserving_taylor_remainder_proof`
- `proofMode`: `exact_rational_same_expression_interval`
- `budgetPassedExactRational`: `True`
- `candidateReadyForLeanShape`: `True`
- `sameExpressionResidualIntervalProofPresent`: `False`
- `proofGradeFullTaylorResidualBoundsPresent`: `False`
- `proofGradeResidualBoundsPresent`: `False`

### order16DirectLedger

- `path`: `ACTIVE/requests/step33_bootstrap/step33_a1_sub0_combined_cancellation_order16_direct_payload.json`
- `exists`: `True`
- `proofStatus`: `raw_product17_centeredTaylor_bound_checked_but_budget_killed`
- `currentGap`: `STEP33_A1_SUB0_COMBINED_CANCELLATION_RAW_PRODUCT17_BUDGET_CONSTANT_FAIL`
- `sourceIntervalCertValidClaimed`: `False`
- `step33A1ClosedClaimed`: `False`

### signedFactorLedger

- `path`: `ACTIVE/requests/step33_bootstrap/step33_a1_sub0_combined_order16_signed_factor_rows.json`
- `exists`: `True`
- `proofStatus`: `abs_to_signed_factor_bridge_checked_but_centered_taylor_budget_killed`
- `currentGap`: `STEP33_A1_SUB0_COMBINED_CANCELLATION_DIRECT_ORDER16_TAYLOR_SOURCE_GAP`
- `proofGrade`: `False`
- `signedFactorRowsLeanChecked`: `False`
- `sourceAssemblyRowsLeanChecked`: `False`

### biasedSignedFactorLedger

- `path`: `ACTIVE/requests/step33_bootstrap/step33_a1_sub0_biased_residual_signed_factor_segments.json`
- `exists`: `True`
- `proofStatus`: `biased_residual_signed_factor_source_only_interface_checked_missing_segment_payload`
- `currentGap`: `STEP33_A1_SUB0_COMBINED_ORDER16_BIASED_RESIDUAL_SIGNED_FACTOR_SEGMENT_PAYLOAD_GAP`
- `proofGrade`: `False`
- `concreteSegmentsLeanChecked`: `False`
- `residualSourcePropClaimed`: `False`

## Next Proof Object

A rational/interval certificate for the complete signed scaled remainder expression on [0,1/10], feeding primaryFiniteRow0Parent0Split100Sub0BiasedScaledRemainderIntervalPayloadTarget.

## Guard

This ledger is not proof evidence.  Do not split the two analytic summands as the primary route and do not claim residual-Horner family Valid until a proof-grade whole-expression interval certificate instantiates the payload target.
