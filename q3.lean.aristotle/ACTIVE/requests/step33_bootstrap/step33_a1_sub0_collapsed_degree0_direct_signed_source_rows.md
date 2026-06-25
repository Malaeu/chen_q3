# Step33A.1-A Direct Signed Source Rows Gate

schema: `q3_psdpd_step33_a1_sub0_collapsed_degree0_direct_signed_source_payload_gate.v6`
route: `collapsed_degree0_direct_signed_source_payload_gate`
proofStatus: `segment0_checked_missing_uniform_family_budget`

## Verdict

- proofGrade: `False`
- currentGap: `STEP33_A1_SUB0_COMBINED_ORDER16_COLLAPSED_DEGREE0_DIRECT_SIGNED_SOURCE_UNIFORM_SEGMENT_ROWS_GAP`
- parentGap: `STEP33_A1_SUB0_COMBINED_ORDER16_SCALED_REMAINDER_DIRECT_ROW_SOURCE_GAP`
- firstFailureCode: `STEP33_A1_SUB0_COMBINED_ORDER16_COLLAPSED_DEGREE0_DIRECT_SIGNED_SOURCE_UNIFORM_SEGMENT_ROWS_GAP`
- uniformSegmentRowsSubgap: `STEP33_A1_SUB0_COMBINED_ORDER16_COLLAPSED_DEGREE0_DIRECT_SIGNED_SOURCE_UNIFORM_SEGMENT_ROWS_GAP`
- budgetFailureCode: `STEP33_A1_SUB0_COMBINED_ORDER16_COLLAPSED_DEGREE0_BUDGET_CONSTANT_FAIL`
- computerUseChoice: `A`
- computerUseFirstTheorem: `primaryFiniteRow0Parent0Split100Sub0_collapsedDegree0_signedSource_segment0_interval_generated`
- computerUseFollowUpStatus: `answered`
- computerUseFollowUpChoice: `A`
- computerUseSegment0TaylorStatus: `answered`
- selectedProofGradeSource: `direct_rational_interval_generator_for_complete_signed_expression`
- selectedFirstRowSource: `direct_segment0_taylor_model_certificate_for_complete_signed_expression`
- activeDirectV21Contract: `True`
- segment0TaylorModelGateProofStatus: `segment0_interval_checked_missing_family_budget`
- segment0TaylorModelGateGap: `STEP33_A1_SUB0_COMBINED_ORDER16_COLLAPSED_DEGREE0_DIRECT_SIGNED_SOURCE_UNIFORM_SEGMENT_ROWS_GAP`
- segment0TaylorModelTargetPayloadPresent: `True`
- targetLeanFileExists: `True`
- segment0PayloadFileExists: `True`
- segment0PayloadPresent: `True`
- parentSegment0OnlySurfacePresent: `True`
- rawD17SharpSupportPresent: `True`
- targetPayloadPresent: `False`
- shouldEmitLeanPayload: `False`
- pointRowsPresentButInsufficient: `True`
- pointRatAuditProofStatus: `fail_closed_rat_point_row_budget_kill_unvalidated`
- rawD17FactorRouteBudgetKilled: `True`

## Target Lean Surface

- file: `Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16CollapsedDegree0DirectSignedSourcePayload.lean`

- `primaryFiniteRow0Parent0Split100Sub0_collapsedDegree0_directSignedSource_segment_family_generated`: present=`False`, line=`None`
- `primaryFiniteRow0Parent0Split100Sub0_collapsedDegree0_directSignedSource_derivAbs_budget_pass_rat`: present=`False`, line=`None`
- `primaryFiniteRow0Parent0Split100Sub0_collapsedDegree0_directSignedSource_degree0_budget_pass_rat`: present=`False`, line=`None`
- `primaryFiniteRow0Parent0Split100Sub0_combinedOrder16ScaledRemainder_collapsed_segment_remainder`: present=`False`, line=`None`

## Segment0 Payload Surface

- file: `Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16CollapsedDegree0DirectSignedSourceSegment0Payload.lean`

- `primaryFiniteRow0Parent0Split100Sub0_collapsedDegree0_signedSource_segment0_interval_generated`: present=`True`, line=`29`
- `primaryFiniteRow0Parent0Split100Sub0_collapsedDegree0_directSignedSource_segment0_valid_generated`: present=`True`, line=`47`

## Parent Segment0-Only Obstruction

- `primaryFiniteRow0Parent0Split100Sub0DirectSignedSourceSegment0OnlyFamily`: present=`True`, line=`24`
- `primaryFiniteRow0Parent0Split100Sub0_collapsedDegree0_directSignedSource_segment0_parent_valid`: present=`True`, line=`35`
- `primaryFiniteRow0Parent0Split100Sub0_collapsedDegree0_directSignedSource_segment0_only_family_not_cover`: present=`True`, line=`53`

## Raw-D17 Sharp Support-Only Kill

Lean proves this support-only two-segment class has valid segment rows and full cover, but also proves its collapsed degree-0 budget is not spendable.  It is a kill certificate, not closure.

- `primaryFiniteRow0Parent0Split100Sub0DirectSignedSourceRawD17SharpTwoSegmentFamily`: present=`True`, line=`83`
- `primaryFiniteRow0Parent0Split100Sub0_directSignedSource_rawD17SharpTwoSegment_segment_rows_valid`: present=`True`, line=`97`
- `primaryFiniteRow0Parent0Split100Sub0_directSignedSource_rawD17SharpTwoSegment_cover`: present=`True`, line=`114`
- `primaryFiniteRow0Parent0Split100Sub0_directSignedSource_rawD17SharpTwoSegment_budget_not_spendable`: present=`True`, line=`158`

## Required Rows Before Lean

### L0_segment_cover

- object: generated proof-grade cover for Set.Icc 0 (1/10)
- status: `missing`
- failureCode: `STEP33_A1_SUB0_COMBINED_ORDER16_COLLAPSED_DEGREE0_DIRECT_SIGNED_SOURCE_UNIFORM_SEGMENT_ROWS_GAP`

### L0a_segment0_interval

- object: exact Rat interval theorem for the whole signed expression on the first generated segment
- status: `checked`
- failureCode: `None`

### L0a_source_segment0_taylor_model

- object: direct segment0 Taylor-model source: modelCoeff, remainderAbs, and whole-expression remainder theorem
- status: `closed_by_local_factor_taylor18_payload`
- failureCode: `None`

### L1_uniform_direct_signed_source_segment_rows

- object: uniform lower/upper rows for ActiveScaleCoeff * D17(ComponentProductActual) - deriv(NominalOrder16Poly) on every generated segment
- status: `missing`
- failureCode: `STEP33_A1_SUB0_COMBINED_ORDER16_COLLAPSED_DEGREE0_DIRECT_SIGNED_SOURCE_UNIFORM_SEGMENT_ROWS_GAP`

### L2_deriv_abs_budget

- object: exact rational lower/upper containment in [-derivAbs, derivAbs]
- status: `missing`
- failureCode: `STEP33_A1_SUB0_COMBINED_ORDER16_COLLAPSED_DEGREE0_BUDGET_CONSTANT_FAIL`

### L3_degree0_budget

- object: exact rational proof that coeffErrorAbs + derivAbs * (1/20) <= polyErrorAbs
- status: `missing`
- failureCode: `STEP33_A1_SUB0_COMBINED_ORDER16_COLLAPSED_DEGREE0_BUDGET_CONSTANT_FAIL`

## Browser Follow-Up

- status: `answered`
- choice: `A`
- firstFile: `scripts/generate_step33_a1_sub0_collapsed_degree0_signed_source.py`
- targetLeanFile: `Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16CollapsedDegree0DirectSignedSourcePayload.lean`
- firstTheoremOrObject: `primaryFiniteRow0Parent0Split100Sub0_collapsedDegree0_directSignedSourceFamily_valid`
- firstSegmentTheorem: `primaryFiniteRow0Parent0Split100Sub0_collapsedDegree0_signedSource_segment0_interval_generated`
- whyProofGrade: The already checked degree-0 receiver, center row, nominal polynomial derivative rows, and segment-family adapter can consume a rational/interval certificate for the whole subtracted derivative. The new proof cargo must be those exact rows, not a point probe or a scalar diagnostic.

Latest segment0 Taylor-model source review:

- nextPatch: direct segment-0 Taylor-model certificate for the complete already-subtracted signed expression
- firstScript: `scripts/generate_step33_a1_sub0_collapsed_degree0_direct_signed_segment0.py`
- firstGeneratedArtifact: `ACTIVE/requests/step33_bootstrap/step33_a1_sub0_collapsed_degree0_direct_signed_segment0_taylor_model.json`
- targetLeanFile: `Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16CollapsedDegree0DirectSignedSourceSegment0Payload.lean`
- modelRemainderTheorem: `primaryFiniteRow0Parent0Split100Sub0_collapsedDegree0_signedSource_segment0_model_remainder_generated`
- failureCode: `STEP33_A1_SUB0_COMBINED_ORDER16_COLLAPSED_DEGREE0_DIRECT_SIGNED_SEGMENT0_TAYLOR_MODEL_SOURCE_GAP`
- stopRule: Do not emit Payload.lean with a conditional field. Stop if no Lean-checkable whole-expression remainder theorem can be produced from local signed jets and order18 bounds.

Source rows needed:

- exact segment cover
- signed lower/upper rows for the complete ActiveScaleCoeff * D17(ComponentProductActual) - deriv(NominalOrder16Poly)
- derivAbs = max(-lower, upper)
- exact degree-0 remainder budget
- collapsed segment remainder
- DirectHorner/final budget rows

Do not use:

- raw-D17 factorwise or two-segment payloads
- RawProduct18 absolute majorant
- activeActual-alone budget
- P45 or zero-model budgets
- sampled/float intervals
- center jets as uniform cell rows
- new alias/receiver wrappers

## Support Surfaces

### `Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16CollapsedDegree0SignedSourcePayload.lean`

- exists: `True`
- allSymbolsPresent: `True`
- sha256: `b738f63142f35c9679158af0ebe30acd2a60d37eeb5012c4a80207ee12feec46`

- `primaryFiniteRow0Parent0Split100Sub0CollapsedDegree0SignedSourceExpr`: present=`True`, line=`31`
- `Step33Sub0CollapsedDegree0SignedSourceSegmentFamilyCert`: present=`True`, line=`484`
- `primaryFiniteRow0Parent0Split100Sub0_collapsed_degree0_remainder_of_signed_segment_family_cert`: present=`True`, line=`665`
- `primaryFiniteRow0Parent0Split100Sub0_collapsedDegree0_signedSegmentValid_of_raw_poly_intervals`: present=`True`, line=`309`

### `Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16CollapsedDegree0NominalPolyDerivRows.lean`

- exists: `True`
- allSymbolsPresent: `True`
- sha256: `630853d89234ec3e47c57196c559b8be4ea824137c9822c9a2fad61928fcb9fd`

- `primaryFiniteRow0Parent0Split100Sub0_nominalOrder16Poly_deriv_segment_interval_generated`: present=`True`, line=`174`

### `Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16CollapsedDegree0PointSlopeRatPayload.lean`

- exists: `True`
- allSymbolsPresent: `True`
- sha256: `02a2b02d6f6e8dde8ea387cce83f3e251634a716a35645b717752bd60c5850da`

- `primaryFiniteRow0Parent0Split100Sub0_collapsedDegree0_pointRow_generated`: present=`True`, line=`476`
- `primaryFiniteRow0Parent0Split100Sub0_componentProductActual_order17_point_interval_rat_generated`: present=`True`, line=`145`

### `Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16CollapsedDegree0RawD17SharpTwoSegmentBudgetKill.lean`

- exists: `True`
- allSymbolsPresent: `True`
- sha256: `ff86d9e23189e45397b1596a46876fc620f0b1f468bb4fb50d49654ad661dfe3`

- `primaryFiniteRow0Parent0Split100Sub0_rawD17_signedFactor_sharp_twoSegment_budget_not_spendable`: present=`True`, line=`41`

### `Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16CollapsedDegree0RawD17SignedFactorTwoSegmentPayload.lean`

- exists: `True`
- allSymbolsPresent: `True`
- sha256: `9658b8145980ecb70c319d7f1b90c7ef19fddc92c935fc52cc99b504c2e0b5f8`

- `primaryFiniteRow0Parent0Split100Sub0_rawD17_signedFactor_twoSegment_budget_not_spendable`: present=`True`, line=`464`

## Boundary

- Point-row Rat payload is checked support, but it is not a uniform segment-family certificate.
- The sharp/two-segment raw-D17 factorwise class is retained as support evidence only; its exact budget-not-spendable theorem prevents using it as the active v21 next patch.
- Do not use point rows as uniform segment rows.
- Do not use raw-D17 factorwise/two-segment rows.
- Do not use raw-D17 sharp/two-segment budget-killed factor route as closure.
- Do not use RawProduct18 absolute majorant.
- Do not use activeActual-alone budget.
- Do not use P45/zero-model budgets.
- Do not use sampled diagnostics as proof.
- Do not use center jets as uniform bounds.
- Do not use new alias/receiver wrappers before source rows exist.
- Do not use DirectConcretePayload.lean before L0-L3 and downstream Horner rows pass.

## Next Implementable Patch

Generate/prove the remaining direct signed-source segment rows covering the rest of Set.Icc 0 (1/10), then prove the exact derivAbs and degree-0 budget rows.  Segment0 is checked, and the parent surface now Lean-proves that segment0-only is not a cover.
