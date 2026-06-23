# Step33A.1-A Combined Order16 Signed Factor Rows Ledger

schema: `q3_psdpd_step33_a1_sub0_combined_order16_signed_factor_rows.v1`
route: `signed_leibniz_checker_then_signed_factor_rows`
proofStatus: `abs_to_signed_factor_bridge_checked_but_centered_taylor_budget_killed`

## Present

- signedLeibnizCheckerPresent: `True`
- factorToLeibnizTermCheckerPresent: `True`
- absToSignedFactorRowsBridgePresent: `True`
- sourceSegmentReceiverPresent: `True`
- zeroModelValidReceiverPresent: `True`
- signedFactorCoverReceiverPresent: `True`
- zeroModelValidOfSignedFactorCoverPresent: `True`

## Checker Symbols

- `primaryFiniteRow0Parent0Split100Sub0Order16SignedLeftTerm`: `True`
- `primaryFiniteRow0Parent0Split100Sub0Order16SignedRightTerm`: `True`
- `primaryFiniteRow0Parent0Split100Sub0_componentProductActual_order16_eq_signedLeibniz`: `True`
- `Step33Sub0CombinedCancellationOrder16SignedFactorSegmentCert`: `True`
- `leftTermCornerRows`: `True`
- `rightTermCornerRows`: `True`
- `toSourceSegment`: `True`
- `structure Valid`: `True`
- `factorRows`: `True`
- `leftTermCorners`: `True`
- `rightTermCorners`: `True`
- `sourceAssembly`: `True`
- `zeroModelBudget`: `True`
- `theorem to_leftTermRows`: `True`
- `theorem to_rightTermRows`: `True`
- `theorem to_sourceInterval`: `True`
- `theorem to_sourceSegmentValid`: `True`
- `Step33Sub0CombinedCancellationOrder16SignedFactorSegmentCover`: `True`
- `primaryFiniteRow0Parent0Split100Sub0_combinedOrder16DirectZeroModel_remainder_of_signedFactor_segment_cover`: `True`
- `primaryFiniteRow0Parent0Split100Sub0_combinedOrder16DirectZeroModel_valid_of_signedFactor_segment_cover`: `True`

## Abs Bridge Symbols

- `centeredTaylorAbsEnclosures`: `True`
- `factorRows_of_centeredTaylorAbsEnclosures`: `True`

## Source Segment Symbols

- `Step33Sub0CombinedCancellationOrder16SourceSegmentCert`: `True`
- `primaryFiniteRow0Parent0Split100Sub0_combinedOrder16DirectZeroModel_remainder_of_segment_cover`: `True`

## Payload Receiver Symbols

- `primaryFiniteRow0Parent0Split100Sub0_combinedOrder16DirectZeroModel_valid_of_wholeCell_direct_interval`: `True`

## Budget Kill Symbols

- `primaryFiniteRow0Parent0Split100Sub0_combinedCancellation_order16Budget_remainder_width_fail_rat`: `True`
- `primaryFiniteRow0Parent0Split100Sub0_combinedCancellation_order16Budget_remainder_width_fail`: `True`

## Missing Proof Payload

- signedFactorRowsLeanChecked: `False`
- factorAbsMajorantRowsLeanChecked: `False`
- centeredTaylorAbsRowsBudgetKilled: `True`
- factorAbsMajorantRowsThresholdViable: `False`
- leibnizCornerRowsLeanChecked: `False`
- leibnizTermRowsDerivedByLean: `True`
- sourceAssemblyRowsLeanChecked: `False`
- sourceAssemblyCheckerPresent: `True`
- sourceSegmentValidClaimed: `False`
- zeroModelAbsBoundLeanChecked: `False`
- directIntervalValidClaimed: `False`
- step33A1ClosedClaimed: `False`
- proofGrade: `False`

## Current Gap

`STEP33_A1_SUB0_COMBINED_CANCELLATION_DIRECT_ORDER16_TAYLOR_SOURCE_GAP`

## Next Proof Object

proof-grade direct hRemainder for the threshold zero-model, or a sharper cancellation-preserving polynomial source model

## Failure Codes

- closed checker gap: `STEP33_A1_SUB0_COMBINED_CANCELLATION_DIRECT_ORDER16_SIGNED_LEIBNIZ_CHECKER_GAP`
- closed factor-to-term checker: `STEP33_A1_SUB0_COMBINED_CANCELLATION_DIRECT_ORDER16_FACTOR_TO_LEIBNIZ_TERM_CHECKER_CLOSED`
- closed abs-to-signed-factor bridge: `STEP33_A1_SUB0_COMBINED_CANCELLATION_DIRECT_ORDER16_ABS_TO_SIGNED_FACTOR_ROWS_BRIDGE_CLOSED`
- centered-Taylor abs rows budget kill: `STEP33_A1_SUB0_CENTERED_TAYLOR_FACTOR_MAJORANT_ORDER16_BUDGET_CONSTANT_FAIL`
- rows missing: `STEP33_A1_SUB0_COMBINED_CANCELLATION_DIRECT_ORDER16_SIGNED_FACTOR_ROWS_GAP`
- zero-model too small: `STEP33_A1_SUB0_COMBINED_CANCELLATION_DIRECT_ORDER16_ZERO_MODEL_CONSTANT_FAIL`

## Guard

No sampled intervals and no independent product-summand norm budget may be treated as proof.  The centered-Taylor absolute majorant row route is not spendable after the exact budget-kill audit; the live route is direct cancellation-preserving source control.
