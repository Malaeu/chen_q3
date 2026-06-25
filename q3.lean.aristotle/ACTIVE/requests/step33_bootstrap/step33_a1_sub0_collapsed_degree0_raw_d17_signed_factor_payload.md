# Step33A.1-A Raw-D17 Signed-Factor Payload Ledger

schema: `q3_psdpd_step33_a1_sub0_collapsed_degree0_raw_d17_signed_factor_payload.v1`
route: `collapsed_degree0_raw_d17_signed_factor_payload`
proofStatus: `fail_closed_segment0_budget_not_spendable`

## Verdict

- leanPayloadWritten: `True`
- payloadProofGrade: `True`
- rawD17SignedFactorSegment0Valid: `True`
- rawPolySegment0Valid: `True`
- segment0BudgetSpendable: `False`
- currentGap: `STEP33_A1_SUB0_COMBINED_ORDER16_COLLAPSED_DEGREE0_RAW_D17_SIGNED_FACTOR_SEGMENT_BUDGET_CONSTANT_FAIL`
- firstFailureCode: `STEP33_A1_SUB0_COMBINED_ORDER16_COLLAPSED_DEGREE0_RAW_D17_SIGNED_FACTOR_SEGMENT_BUDGET_CONSTANT_FAIL`
- selectedNextPatch: `build_two_segment_raw_d17_signed_factor_payload`

## Next Patch

- script: `scripts/generate_step33_a1_sub0_collapsed_degree0_raw_d17_signed_factor_segments.py`
- leanFile: `Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16CollapsedDegree0RawD17SignedFactorTwoSegmentPayload.lean`
- segments: `['[0, 1/20]', '[1/20, 1/10]']`
- rowsFailureCode: `STEP33_A1_SUB0_COMBINED_ORDER16_COLLAPSED_DEGREE0_RAW_D17_SIGNED_FACTOR_TWO_SEGMENT_ROWS_GAP`
- budgetFailureCode: `STEP33_A1_SUB0_COMBINED_ORDER16_COLLAPSED_DEGREE0_RAW_D17_SIGNED_FACTOR_TWO_SEGMENT_BUDGET_CONSTANT_FAIL`

First required theorem names:

- `primaryFiniteRow0Parent0Split100Sub0_rawD17_signedFactor_left_valid`
- `primaryFiniteRow0Parent0Split100Sub0_rawD17_signedFactor_right_valid`
- `primaryFiniteRow0Parent0Split100Sub0_rawD17_signedFactor_twoSegment_family_valid`

## Meaning

The checked Lean file gives one full-cell smoke payload for the
raw-D17 signed-factor receiver and its same-segment raw/poly bridge.
The exact budget theorem in the same file proves that this smoke
segment is too wide and cannot be spent as the Step33A.1-A degree-0
budget.

This does not kill the direct route.  It only kills the full-cell
absolute smoke payload as a spendable certificate.  The next live
patch is the two-segment raw-D17 signed-factor payload selected by
the Computer Use route review.

## Files

- rowsFile: `Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16CollapsedDegree0RawD17SignedFactorRows.lean`
- rowsFileSha256: `61b77b223ee3531a22ab06b5a5a82ca661e5462c13c574aa4a80da64ba6b4c34`
- payloadFile: `Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16CollapsedDegree0RawD17SignedFactorPayload.lean`
- payloadFileSha256: `275365f66124a94ea0b89d65bd0fe834568d8bdd049d0beacee6c7fdba29f9cb`

## Row Receiver Symbols

- `Step33Sub0CollapsedDegree0RawD17SignedFactorSegmentCert`: present=`True`, line=`116`
- `theorem to_rawInterval`: present=`True`, line=`263`
- `theorem to_rawPolySegmentValid`: present=`True`, line=`342`
- `primaryFiniteRow0Parent0Split100Sub0_collapsedDegree0_rawD17_interval_of_signed_factor_segment`: present=`True`, line=`368`
- `primaryFiniteRow0Parent0Split100Sub0_collapsedDegree0_rawPolySegmentValid_of_rawD17_signed_factor_segment`: present=`True`, line=`383`

## Payload Symbols

- `primaryFiniteRow0Parent0Split100Sub0RawD17OmegaLower`: present=`True`, line=`68`
- `primaryFiniteRow0Parent0Split100Sub0RawD17OmegaUpper`: present=`True`, line=`72`
- `primaryFiniteRow0Parent0Split100Sub0RawD17ShapeSqLower`: present=`True`, line=`76`
- `primaryFiniteRow0Parent0Split100Sub0RawD17ShapeSqUpper`: present=`True`, line=`80`
- `primaryFiniteRow0Parent0Split100Sub0RawD17SignedFactorTermLower`: present=`True`, line=`93`
- `primaryFiniteRow0Parent0Split100Sub0RawD17SignedFactorTermUpper`: present=`True`, line=`98`
- `primaryFiniteRow0Parent0Split100Sub0RawD17SignedFactorSegment0`: present=`True`, line=`115`
- `primaryFiniteRow0Parent0Split100Sub0_rawD17_signedFactor_segment0_valid`: present=`True`, line=`267`
- `primaryFiniteRow0Parent0Split100Sub0RawD17SignedFactorRawPolySegment0`: present=`True`, line=`348`
- `primaryFiniteRow0Parent0Split100Sub0_rawD17_signedFactor_rawPoly_segment0_valid`: present=`True`, line=`359`
- `primaryFiniteRow0Parent0Split100Sub0_rawD17_signedFactor_segment0_budget_fail_rat`: present=`True`, line=`394`
- `primaryFiniteRow0Parent0Split100Sub0_rawD17_signedFactor_segment0_budget_not_spendable`: present=`True`, line=`403`

## Boundary

- No Step33A.1-A closure is claimed.
- No direct-route impossibility is claimed from this one smoke failure.
- The old symmetric RawProduct18 budget class remains non-spendable.
