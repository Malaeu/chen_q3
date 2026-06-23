# Step33A.1-A Combined Order16 Source Interval Ledger

schema: `q3_psdpd_step33_a1_sub0_combined_order16_source_interval.v1`
route: `direct_signed_whole_source_interval_for_zero_model`
proofStatus: `whole_cell_receiver_checked_missing_signed_source_interval`

## Present

- sourceIntervalCheckerPresent: `True`
- wholeCellPayloadPresent: `True`
- zeroModelRemainderBridgePresent: `True`

## Checker Symbols

- `Step33Sub0CombinedCancellationOrder16SourceSegmentCert`: `True`
- `structure Valid`: `True`
- `to_componentSource_abs_on_segment`: `True`
- `Step33Sub0CombinedCancellationOrder16SourceSegmentCover`: `True`
- `primaryFiniteRow0Parent0Split100Sub0_combinedOrder16Source_abs_of_segment_cover`: `True`
- `primaryFiniteRow0Parent0Split100Sub0_combinedOrder16DirectZeroModel_remainder_of_segment_cover`: `True`

## Whole-Cell Payload Symbols

- `primaryFiniteRow0Parent0Split100Sub0CombinedOrder16SourceWholeCellSegment`: `True`
- `primaryFiniteRow0Parent0Split100Sub0CombinedOrder16SourceWholeCellSegments`: `True`
- `primaryFiniteRow0Parent0Split100Sub0_combinedOrder16SourceWholeCell_cover`: `True`
- `primaryFiniteRow0Parent0Split100Sub0_combinedOrder16SourceWholeCell_valid_of_direct_interval`: `True`
- `primaryFiniteRow0Parent0Split100Sub0_combinedOrder16DirectZeroModel_remainder_of_wholeCell_direct_interval`: `True`
- `primaryFiniteRow0Parent0Split100Sub0_combinedOrder16DirectZeroModel_valid_of_wholeCell_direct_interval`: `True`

## Direct Bridge Symbols

- `primaryFiniteRow0Parent0Split100Sub0_combinedOrder16DirectZeroModel_remainder_of_componentSource_abs`: `True`
- `primaryFiniteRow0Parent0Split100Sub0_combinedOrder16DirectZeroModel_valid_of_remainder`: `True`

## Missing Proof Payload

- signedFactorRowsLeanChecked: `False`
- wholeSourceAssemblyLeanChecked: `False`
- globalCoverLeanChecked: `True`
- zeroModelAbsBoundLeanChecked: `False`
- zeroModelIntervalDataValidReceiverPresent: `True`
- directIntervalValidClaimed: `False`
- sourceIntervalCertValidClaimed: `False`
- step33A1ClosedClaimed: `False`
- proofGrade: `False`

## Current Gap

`STEP33_A1_SUB0_COMBINED_CANCELLATION_DIRECT_ORDER16_SIGNED_FACTOR_ROWS_GAP`

## Next Proof Object

proof-grade signed factor derivative rows, exact Leibniz term interval rows, and active-scale sourceAssembly rows instantiating the signed whole-source interval for the concrete whole-cell zero-model segment

## Refined By

ACTIVE/requests/step33_bootstrap/step33_a1_sub0_combined_order16_signed_factor_rows.json

## Failure Codes

- rows missing: `STEP33_A1_SUB0_COMBINED_CANCELLATION_DIRECT_ORDER16_SIGNED_FACTOR_ROWS_GAP`
- zero-model too small: `STEP33_A1_SUB0_COMBINED_CANCELLATION_DIRECT_ORDER16_ZERO_MODEL_CONSTANT_FAIL`

## Guard

Do not use sampled intervals or independent product-summand norm bounds as proof; the source intervals must bound the whole assembled signed expression.
