# Step33A.1-A Biased Scaled-Remainder Interval Ledger

schema: `q3_psdpd_step33_a1_sub0_combined_order16_biased_scaled_remainder_interval.v2`
route: `biased_scaled_remainder_whole_expression_interval`
proofStatus: `biased_scaled_remainder_zero_model_checker_checked_missing_source_bound`

## Status

- payloadInterfacePresent: `True`
- zeroModelCheckerPresent: `True`
- remainderBridgePresent: `True`
- proofGrade: `False`
- wholeExpressionIntervalRowsLeanChecked: `False`
- wholeExpressionScaledRemainderSourceBoundLeanChecked: `False`
- zeroModelPayloadTargetLeanChecked: `True`
- segmentCoverLeanChecked: `True`
- budgetRowsLeanChecked: `True`
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

## Zero Model Symbols

- `primaryFiniteRow0Parent0Split100Sub0BiasedScaledRemainderZeroModelSegment`: `True`
- `primaryFiniteRow0Parent0Split100Sub0BiasedScaledRemainderZeroModelFamily`: `True`
- `primaryFiniteRow0Parent0Split100Sub0_biasedScaledRemainder_residualAbs_nonneg`: `True`
- `primaryFiniteRow0Parent0Split100Sub0_biasedScaledRemainderZeroModel_segment_valid`: `True`
- `primaryFiniteRow0Parent0Split100Sub0_biasedScaledRemainderZeroModel_family_valid`: `True`
- `primaryFiniteRow0Parent0Split100Sub0_biasedScaledRemainderZeroModel_payload_target`: `True`
- `primaryFiniteRow0Parent0Split100Sub0_biasedResidualHorner_residualRemainder_of_scaledRemainder_zeroModel`: `True`

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

- v2 zero-model route: one segment cellL=0, cellU=1/10
- lower = -BiasedResidualRemainderAbs
- upper = BiasedResidualRemainderAbs
- remainderAbs = BiasedResidualRemainderAbs
- Lean-checked cover and budget plumbing
- still missing proof-grade complete signed scaled-remainder source bound

## Upstream Evidence

### residualHornerLedger

- `path`: `ACTIVE/requests/step33_bootstrap/step33_a1_sub0_biased_residual_horner_payload.json`
- `exists`: `True`
- `proofStatus`: `biased_residual_horner_zero_model_target_checked_missing_scaled_remainder_bound`
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

A proof-grade theorem of primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedResidualHornerScaledRemainderSourceProp at primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedResidualRemainderAbs, feeding the checked zero-model payload target.

## Guard

This ledger is not proof evidence.  Do not split the two analytic summands as the primary route and do not claim residual-Horner family Valid until a proof-grade whole-expression scaled-remainder source bound instantiates the zero-model payload target.
