# Step33A.1-A Biased Residual Source-Horner Ledger

schema: `q3_psdpd_step33_a1_sub0_biased_residual_source_horner_cert.v1`
route: `biased_residual_direct_source_horner_family`
proofStatus: `direct_residual_adapter_checked_missing_residual_bound`

## Present

- sourceHornerReceiverPresent: `True`
- biasedResidualSourceSegmentReceiverPresent: `True`
- biasedModelBudgetSurfacePresent: `True`
- centeredTaylorAbsBudgetKilled: `True`
- directResidualAdapterPresent: `True`
- residualHornerReceiverPresent: `True`
- sourceHornerFamilyDirectSpendableFromRemainderOnly: `False`

## Source-Horner Symbols

- `Step33Sub0CombinedOrder16BiasedResidualSourceHornerCert`: `True`
- `def poly`: `True`
- `def toSourceSegment`: `True`
- `structure Valid`: `True`
- `source_remainder`: `True`
- `poly_range`: `True`
- `theorem sourceInterval`: `True`
- `theorem to_sourceSegmentValid`: `True`
- `def hornerTail`: `True`
- `theorem hornerTail_zero_eq_poly`: `True`
- `Step33Sub0CombinedOrder16BiasedResidualSourceHornerRangeCert`: `True`
- `theorem poly_range`: `True`
- `theorem of_horner_range`: `True`
- `Step33Sub0CombinedOrder16BiasedResidualSourceHornerSegmentCover`: `True`
- `Step33Sub0CombinedOrder16BiasedResidualSourceHornerFamilyCert`: `True`
- `theorem to_segmentValid`: `True`
- `theorem to_residualSourceProp`: `True`
- `theorem to_order16DirectIntervalValid`: `True`

## Biased Residual Source-Segment Symbols

- `Step33Sub0CombinedOrder16BiasedResidualSourceSegmentCert`: `True`
- `Step33Sub0CombinedOrder16BiasedResidualSourceSegmentCover`: `True`
- `primaryFiniteRow0Parent0Split100Sub0_combinedOrder16BiasedResidual_sourceProp_of_source_segment_cover`: `True`
- `primaryFiniteRow0Parent0Split100Sub0_combinedOrder16BiasedResidual_order16DirectIntervalValid_of_source_segment_cover`: `True`

## Biased Model Budget Symbols

- `primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedNonzeroModelData`: `True`
- `primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedNonzeroModelResidualSlackRat`: `True`
- `primaryFiniteRow0Parent0Split100Sub0_combinedOrder16BiasedNonzeroModel_poly_range`: `True`
- `primaryFiniteRow0Parent0Split100Sub0_combinedOrder16BiasedNonzeroModel_order16_direct_interval_valid_of_residual_bound`: `True`
- `primaryFiniteRow0Parent0Split100Sub0_combinedOrder16Source_sub_biasedNonzeroModelPoly`: `True`

## CenteredTaylor Budget Guard

- `primaryFiniteRow0Parent0Split100Sub0BiasedResidualCenteredTaylorNeededAbsRat`: `True`
- `primaryFiniteRow0Parent0Split100Sub0_biasedResidual_centeredTaylorNeededAbs_budget_fail_rat`: `True`
- `primaryFiniteRow0Parent0Split100Sub0_combinedOrder16BiasedResidual_centeredTaylor_not_spendable`: `True`

## Direct Residual Adapter Symbols

- `primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedResidualRemainderAbs`: `True`
- `primaryFiniteRow0Parent0Split100Sub0_biasedNonzeroModel_directInterval_valid_of_remainder_bound`: `True`
- `primaryFiniteRow0Parent0Split100Sub0_biasedNonzeroModel_directInterval_valid_of_slack_remainder_bound`: `True`

## Residual-Horner Receiver Symbols

- `Step33Sub0CombinedOrder16BiasedResidualHornerCert`: `True`
- `Step33Sub0CombinedOrder16BiasedResidualHornerRangeCert`: `True`
- `Step33Sub0CombinedOrder16BiasedResidualHornerFamilyCert`: `True`
- `theorem to_residualSourceProp`: `True`
- `theorem to_order16DirectIntervalValid`: `True`

## Missing Proof Payload

- concreteSourceHornerSegmentsLeanChecked: `False`
- sourceCoefficientsLeanChecked: `False`
- hornerStageBoundsLeanChecked: `False`
- sourceRemainderBoundLeanChecked: `False`
- sourceLowerUpperRowsLeanChecked: `False`
- biasedBudgetRowsLeanChecked: `False`
- globalCoverLeanChecked: `False`
- residualSlackComparisonLeanChecked: `False`
- residualSourcePropClaimed: `False`
- order16DirectIntervalValidClaimed: `False`
- step33A1ClosedClaimed: `False`
- proofGrade: `False`

## Current Gap

`STEP33_A1_SUB0_COMBINED_ORDER16_BIASED_NONZERO_MODEL_RESIDUAL_BOUND_GAP`

## Next Proof Object

a proof-grade bound for primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedNonzeroModelResidualSourceProp at residualAbs <= ResidualSlackRat

## Failure Codes

- closed interface: `STEP33_A1_SUB0_COMBINED_ORDER16_BIASED_RESIDUAL_SOURCE_HORNER_FAMILY_RECEIVER_CLOSED`
- rows missing: `STEP33_A1_SUB0_COMBINED_ORDER16_BIASED_RESIDUAL_SOURCE_HORNER_PAYLOAD_ROWS_GAP`
- remainder missing: `STEP33_A1_SUB0_COMBINED_ORDER16_BIASED_RESIDUAL_SOURCE_HORNER_REMAINDER_BOUND_GAP`
- budget rows fail: `STEP33_A1_SUB0_COMBINED_ORDER16_BIASED_RESIDUAL_SOURCE_HORNER_BUDGET_CONSTANT_FAIL`
- normalization mismatch: `STEP33_A1_SUB0_COMBINED_ORDER16_BIASED_RESIDUAL_HORNER_NORMALIZATION_MISMATCH_GAP`

## Guard

Do not reuse the old zero-model budget or centeredTaylor rows.  Do not force SourceHornerFamilyCert.Valid from a pointwise ComponentSource - BiasedNonzeroModelPoly bound: that source-segment normalization pays independent global extrema.  Spend residual bounds through the direct biased nonzero-model receiver instead.
