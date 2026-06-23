# Step33A.1-A Biased Residual Signed-Factor Segment Ledger

schema: `q3_psdpd_step33_a1_sub0_biased_residual_signed_factor_segments.v2`
route: `biased_residual_source_only_signed_factor_segments`
proofStatus: `biased_residual_signed_factor_source_only_interface_checked_missing_segment_payload`

## Present

- sourceOnlySignedFactorCheckerPresent: `True`
- biasedResidualSignedFactorAdapterPresent: `True`
- biasedResidualSourceSegmentReceiverPresent: `True`
- biasedModelBudgetSurfacePresent: `True`
- sourceOnlyInterfaceReady: `True`
- generatorFacingFamilyCertPresent: `True`

## Checker Symbols

- `Step33Sub0CombinedCancellationOrder16SignedFactorSegmentCert`: `True`
- `structure SourceIntervalValid`: `True`
- `namespace SourceIntervalValid`: `True`
- `theorem to_leftTermRows`: `True`
- `theorem to_rightTermRows`: `True`
- `theorem to_sourceInterval`: `True`
- `theorem to_sourceIntervalValid`: `True`
- `sourceAssembly`: `True`
- `zeroModelBudget`: `True`

## Adapter Symbols

- `toBiasedResidualSourceSegment`: `True`
- `to_biasedResidualSourceSegmentValid`: `True`
- `Step33Sub0CombinedOrder16BiasedResidualSignedFactorSegmentCover`: `True`
- `primaryFiniteRow0Parent0Split100Sub0_combinedOrder16BiasedResidual_sourceProp_of_signedFactor_segment_cover`: `True`
- `primaryFiniteRow0Parent0Split100Sub0_combinedOrder16BiasedResidual_order16DirectIntervalValid_of_signedFactor_segment_cover`: `True`
- `Step33Sub0CombinedOrder16BiasedResidualSignedFactorSegmentFamilyCert`: `True`
- `structure Valid`: `True`
- `theorem to_residualSourceProp`: `True`
- `theorem to_order16DirectIntervalValid`: `True`

## Biased Residual Source-Segment Symbols

- `Step33Sub0CombinedOrder16BiasedResidualSourceSegmentCert`: `True`
- `namespace Step33Sub0CombinedOrder16BiasedResidualSourceSegmentCert`: `True`
- `structure Valid`: `True`
- `theorem to_residual_bound_on_segment`: `True`
- `Step33Sub0CombinedOrder16BiasedResidualSourceSegmentCover`: `True`
- `primaryFiniteRow0Parent0Split100Sub0_combinedOrder16BiasedResidual_sourceProp_of_source_segment_cover`: `True`
- `primaryFiniteRow0Parent0Split100Sub0_combinedOrder16BiasedResidual_order16DirectIntervalValid_of_source_segment_cover`: `True`

## Biased Model Budget Symbols

- `primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedNonzeroModelData`: `True`
- `polyLower`: `True`
- `polyUpper`: `True`
- `primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedNonzeroModelResidualSlackRat`: `True`
- `primaryFiniteRow0Parent0Split100Sub0_combinedOrder16BiasedNonzeroModel_poly_range`: `True`
- `primaryFiniteRow0Parent0Split100Sub0_combinedOrder16BiasedNonzeroModel_order16_direct_interval_valid_of_residual_bound`: `True`

## Old Zero-Model Budget Guard

- `primaryFiniteRow0Parent0Split100Sub0_combinedCancellation_order16Budget_remainder_width_fail_rat`: `True`
- `primaryFiniteRow0Parent0Split100Sub0_combinedCancellation_order16Budget_remainder_width_fail`: `True`
- oldZeroModelBudgetKilled: `True`
- oldZeroModelBudgetSpendableForBiasedResidual: `False`

## Biased Residual CenteredTaylor Budget Guard

- `primaryFiniteRow0Parent0Split100Sub0BiasedResidualCenteredTaylorNeededAbsRat`: `True`
- `primaryFiniteRow0Parent0Split100Sub0_biasedResidual_centeredTaylorNeededAbs_budget_fail_rat`: `True`
- `primaryFiniteRow0Parent0Split100Sub0_biasedResidual_centeredTaylorNeededAbs_not_budgeted_rat`: `True`
- `primaryFiniteRow0Parent0Split100Sub0_combinedOrder16BiasedResidual_centeredTaylor_budget_fail_rat`: `True`
- `primaryFiniteRow0Parent0Split100Sub0_combinedOrder16BiasedResidual_centeredTaylor_not_spendable`: `True`
- biasedResidualCenteredTaylorAbsBudgetKilled: `True`

## Missing Proof Payload

- concreteSegmentsLeanChecked: `False`
- factorRowsLeanChecked: `False`
- leibnizCornerRowsLeanChecked: `False`
- sourceAssemblyRowsLeanChecked: `False`
- biasedBudgetRowsLeanChecked: `False`
- globalCoverLeanChecked: `False`
- residualSlackComparisonLeanChecked: `False`
- residualSourcePropClaimed: `False`
- order16DirectIntervalValidClaimed: `False`
- step33A1ClosedClaimed: `False`
- proofGrade: `False`

## Current Gap

`STEP33_A1_SUB0_COMBINED_ORDER16_BIASED_RESIDUAL_SIGNED_FACTOR_SEGMENT_PAYLOAD_GAP`

## Next Proof Object

concrete signed-factor segment family proving SourceIntervalValid, a cover of [0,1/10], exact per-segment biased-model lower/upper budget rows, and residualAbs <= ResidualSlackRat

## Failure Codes

- closed interface: `STEP33_A1_SUB0_COMBINED_ORDER16_BIASED_RESIDUAL_SIGNED_FACTOR_TO_SOURCE_SEGMENT_RECEIVER_CLOSED`
- old budget reuse invalid: `STEP33_A1_SUB0_COMBINED_ORDER16_BIASED_RESIDUAL_OLD_ZERO_MODEL_BUDGET_REUSE_INVALID`
- centeredTaylor abs budget reuse invalid: `STEP33_A1_SUB0_COMBINED_ORDER16_BIASED_RESIDUAL_CENTERED_TAYLOR_ABS_BUDGET_REUSE_INVALID`
- rows missing: `STEP33_A1_SUB0_COMBINED_ORDER16_BIASED_RESIDUAL_SIGNED_FACTOR_SEGMENT_PAYLOAD_GAP`
- budget rows fail: `STEP33_A1_SUB0_COMBINED_ORDER16_BIASED_RESIDUAL_SIGNED_FACTOR_BUDGET_CONSTANT_FAIL`

## Guard

Do not reuse Step33Sub0CombinedCancellationOrder16SignedFactorSegmentCert.Valid or its zeroModelBudget row for the biased residual.  The live route uses SourceIntervalValid plus fresh same-unit budget rows against the checked biased nonzero-model polynomial range.
