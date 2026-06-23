# Step33A.1-A Biased Residual Local-Model Segment Ledger

schema: `q3_psdpd_step33_a1_sub0_biased_residual_local_model_segments.v1`
route: `biased_residual_local_model_segments`
proofStatus: `biased_residual_local_model_segment_family_receiver_checked_missing_payload`

## Present

- localModelSegmentReceiverPresent: `True`
- biasedResidualBridgePresent: `True`
- biasedNonzeroModelDirectReceiverPresent: `True`
- directResidualAdapterPresent: `True`

## Local-Model Segment Symbols

- `Step33Sub0CombinedOrder16BiasedResidualLocalModelSegmentCert`: `True`
- `structure Valid`: `True`
- `sourceInterval`: `True`
- `modelInterval`: `True`
- `lowerBudget`: `True`
- `upperBudget`: `True`
- `theorem to_residual_bound_on_segment`: `True`
- `Step33Sub0CombinedOrder16BiasedResidualLocalModelSegmentCover`: `True`
- `primaryFiniteRow0Parent0Split100Sub0_combinedOrder16BiasedResidual_sourceProp_of_local_model_segment_cover`: `True`
- `primaryFiniteRow0Parent0Split100Sub0_combinedOrder16BiasedResidual_order16DirectIntervalValid_of_local_model_segment_cover`: `True`
- `Step33Sub0CombinedOrder16BiasedResidualLocalModelSegmentFamilyCert`: `True`
- `namespace Step33Sub0CombinedOrder16BiasedResidualLocalModelSegmentFamilyCert`: `True`
- `theorem to_residualSourceProp`: `True`
- `theorem to_order16DirectIntervalValid`: `True`

## Biased Residual Bridge Symbols

- `primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedNonzeroModelResidualSourceProp`: `True`
- `Step33Sub0CombinedOrder16BiasedResidualSourceSegmentCert`: `True`
- `Step33Sub0CombinedOrder16BiasedResidualActiveActualSignedIntervalCert`: `True`

## Biased Nonzero-Model Symbols

- `primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedNonzeroModelPoly`: `True`
- `primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedNonzeroModelResidualSlackRat`: `True`
- `primaryFiniteRow0Parent0Split100Sub0_combinedOrder16BiasedNonzeroModel_order16_direct_interval_valid_of_residual_bound`: `True`

## Direct Adapter Symbols

- `primaryFiniteRow0Parent0Split100Sub0_biasedNonzeroModel_directInterval_valid_of_remainder_bound`: `True`
- `primaryFiniteRow0Parent0Split100Sub0_biasedNonzeroModel_directInterval_valid_of_slack_remainder_bound`: `True`

## Missing Proof Payload

- concreteSegmentsLeanChecked: `False`
- sourceRowsLeanChecked: `False`
- modelRowsLeanChecked: `False`
- localBudgetRowsLeanChecked: `False`
- segmentBudgetRowsLeanChecked: `False`
- globalCoverLeanChecked: `False`
- globalSlackComparisonLeanChecked: `False`
- residualSourcePropClaimed: `False`
- order16DirectIntervalValidClaimed: `False`
- step33A1ClosedClaimed: `False`
- proofGrade: `False`

## Current Gap

`STEP33_A1_SUB0_COMBINED_ORDER16_BIASED_RESIDUAL_LOCAL_MODEL_SEGMENT_PAYLOAD_GAP`

## Next Proof Object

a concrete Step33Sub0CombinedOrder16BiasedResidualLocalModelSegmentFamilyCert.Valid payload: source/model same-cell interval rows, local residual budget rows, segment residualAbs <= global residualAbs, global residualAbs <= ResidualSlackRat, and cover of [0,1/10]

## Guard

Do not spend source rows against global BiasedNonzeroModelData polyLower/polyUpper when local model rows are available.  The live target compares source and model on the same segment and then uses the existing direct biased nonzero-model receiver.

## Failure Codes

- rowsMissing: `STEP33_A1_SUB0_COMBINED_ORDER16_BIASED_RESIDUAL_LOCAL_MODEL_SEGMENT_PAYLOAD_GAP`
- budgetRowsFail: `STEP33_A1_SUB0_COMBINED_ORDER16_BIASED_RESIDUAL_LOCAL_MODEL_SEGMENT_BUDGET_CONSTANT_FAIL`
- coverFails: `STEP33_A1_SUB0_COMBINED_ORDER16_BIASED_RESIDUAL_LOCAL_MODEL_SEGMENT_COVER_GAP`
- closedInterface: `STEP33_A1_SUB0_COMBINED_ORDER16_BIASED_RESIDUAL_LOCAL_MODEL_SEGMENT_FAMILY_RECEIVER_CLOSED`
