# Step33A.1-A Collapsed Degree-0 Signed Source Ledger

schema: `q3_psdpd_step33_a1_sub0_collapsed_degree0_signed_source.v11`
route: `collapsed_degree0_signed_poly_deriv_source`
proofStatus: `fail_closed_missing_v21_direct_signed_source_segment_rows`

## Verdict

- proofGrade: `False`
- leanPayloadWritten: `True`
- currentGap: `STEP33_A1_SUB0_COMBINED_ORDER16_COLLAPSED_DEGREE0_POLY_DERIV_SIGNED_SOURCE_GAP`
- firstFailureCode: `STEP33_A1_SUB0_COMBINED_ORDER16_COLLAPSED_DEGREE0_POLY_DERIV_SIGNED_SOURCE_GAP`
- activeDirectV21Contract: `True`
- signedSourceSurfacePresent: `True`
- signedSourceSurfaceLeanChecked: `True`
- centerAuditLeanChecked: `True`
- nominalPolyDerivRowsLeanChecked: `True`
- rawD17SignedFactorRowsLeanChecked: `True`
- rawD17SignedFactorPayloadLeanChecked: `True`
- rawD17SignedFactorSegment0Valid: `True`
- rawD17SignedFactorRawPolySegment0Valid: `True`
- rawD17SignedFactorSegment0BudgetSpendable: `False`
- rawD17FactorRouteActiveNextPatch: `False`
- rawD17FactorRouteStatus: `superseded_by_v21_direct_whole_expression_row_source`
- coarseTriangleBudgetAuditLeanChecked: `True`
- coarseTriangleBudgetPassed: `False`
- selectedNextPatch: `emit_first_direct_signed_source_segment0_interval`
- firstConcreteSubgap: `STEP33_A1_SUB0_COMBINED_ORDER16_COLLAPSED_DEGREE0_POLY_DERIV_SIGNED_SOURCE_GAP`

## Next Patch

- script: `scripts/generate_step33_a1_sub0_collapsed_degree0_signed_source.py`
- leanFile: `Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16CollapsedDegree0DirectSignedSourcePayload.lean`
- segments: `['generated proof-grade cover of Set.Icc 0 (1/10)']`
- rowsFailureCode: `STEP33_A1_SUB0_COMBINED_ORDER16_COLLAPSED_DEGREE0_POLY_DERIV_SIGNED_SOURCE_GAP`
- budgetFailureCode: `STEP33_A1_SUB0_COMBINED_ORDER16_COLLAPSED_DEGREE0_BUDGET_CONSTANT_FAIL`
- directRowsGateProofStatus: `fail_closed_missing_direct_signed_source_payload`
- directRowsGateFirstFailureCode: `STEP33_A1_SUB0_COMBINED_ORDER16_COLLAPSED_DEGREE0_POLY_DERIV_SIGNED_SOURCE_GAP`
- directRowsGateFollowUpStatus: `answered`
- directRowsGateFollowUpChoice: `A`
- computerUseChoice: `A`
- computerUseFirstTheorem: `primaryFiniteRow0Parent0Split100Sub0_collapsedDegree0_signedSource_segment0_interval_generated`

First required theorem names:

- `primaryFiniteRow0Parent0Split100Sub0_collapsedDegree0_signedSource_segment0_interval_generated`
- `primaryFiniteRow0Parent0Split100Sub0_collapsedDegree0_directSignedSource_segment_family_generated`
- `primaryFiniteRow0Parent0Split100Sub0_collapsedDegree0_directSignedSource_derivAbs_budget_pass_rat`
- `primaryFiniteRow0Parent0Split100Sub0_collapsedDegree0_directSignedSource_degree0_budget_pass_rat`
- `primaryFiniteRow0Parent0Split100Sub0_combinedOrder16ScaledRemainder_collapsed_segment_remainder`

## Direct v21 Handoff

- sourceLedger: `ACTIVE/requests/step33_bootstrap/step33_a1_sub0_combined_order16_scaled_remainder_direct_payload.json`
- active: `True`
- firstFailureCodeIfRowsMissing: `STEP33_A1_SUB0_COMBINED_ORDER16_COLLAPSED_DEGREE0_POLY_DERIV_SIGNED_SOURCE_GAP`
- parentFailureCodeIfRowsMissing: `STEP33_A1_SUB0_COMBINED_ORDER16_SCALED_REMAINDER_DIRECT_ROW_SOURCE_GAP`
- budgetFailureCode: `STEP33_A1_SUB0_COMBINED_ORDER16_COLLAPSED_DEGREE0_BUDGET_CONSTANT_FAIL`

Required direct rows before any concrete Lean payload:

- `L0_segment_cover`: Step33Sub0CollapsedDegree0SignedSourceSegmentCover for the generated segments covering Set.Icc 0 (1/10)
  status=`missing`, failureCode=`STEP33_A1_SUB0_COMBINED_ORDER16_COLLAPSED_DEGREE0_POLY_DERIV_SIGNED_SOURCE_GAP`
- `L1_signed_source_segment_rows`: proof-grade lower/upper rows for ActiveScaleCoeff * D17(ComponentProductActual) - deriv(NominalOrder16Poly) on each segment
  status=`missing`, failureCode=`STEP33_A1_SUB0_COMBINED_ORDER16_COLLAPSED_DEGREE0_POLY_DERIV_SIGNED_SOURCE_GAP`
- `L2_deriv_abs_budget`: exact rational proof that the generated lower/upper rows are contained in [-derivAbs, derivAbs]
  status=`missing`, failureCode=`STEP33_A1_SUB0_COMBINED_ORDER16_COLLAPSED_DEGREE0_BUDGET_CONSTANT_FAIL`
- `L3_degree0_remainder_budget`: exact rational proof that coeffErrorAbs + derivAbs * (1/20) <= polyErrorAbs
  status=`missing`, failureCode=`STEP33_A1_SUB0_COMBINED_ORDER16_COLLAPSED_DEGREE0_BUDGET_CONSTANT_FAIL`
- `L4_collapsed_segment_remainder`: primaryFiniteRow0Parent0Split100Sub0_combinedOrder16ScaledRemainder_collapsed_segment_remainder
  status=`missing_until_L0_L3_pass`, failureCode=`STEP33_A1_SUB0_COMBINED_ORDER16_SCALED_REMAINDER_DIRECT_ROW_SOURCE_GAP`
- `L5_horner_and_final_budget_rows`: Horner stage bounds, segment cover for the direct family, and final +/- BiasedResidualRemainderAbs rows
  status=`missing`, failureCode=`STEP33_A1_SUB0_COMBINED_ORDER16_COLLAPSED_SOURCE_INTERVAL_ROWS_GAP`

## Target

- expression:

```text
ActiveScaleCoeff * iteratedDeriv 17 ComponentProductActual eta
  - deriv NominalOrder16Poly eta
```

- interval theorem expected from a future generated payload:

```text
forall eta in Set.Icc 0 (1/10),
  lower <= signedExpr eta and signedExpr eta <= upper
```

## Generator Contract

The next proof-producing patch must emit proof-grade segment-local
rows.  It may either emit direct lower/upper rows for the already
subtracted whole expression or use the checked same-segment raw/poly
interval subtraction bridge.  A separate direct-norm receiver is not
the selected route because the checked `Valid.to_hSignedD17PolyDeriv`
and segment-family bridges already convert lower/upper rows to the
required norm bound.

- interval theorem: `primaryFiniteRow0Parent0Split100Sub0_collapsedDegree0_polyDeriv_signed_interval_generated`
- segmented theorem: `primaryFiniteRow0Parent0Split100Sub0_collapsedDegree0_signedSource_segment0_interval_generated`
- raw/poly subtraction bridge: `primaryFiniteRow0Parent0Split100Sub0_collapsedDegree0_signedSegmentValid_of_raw_poly_intervals`
- raw/poly family bridge: `primaryFiniteRow0Parent0Split100Sub0_collapsed_degree0_remainder_of_raw_poly_segment_family_cert`
- raw-D17 signed-factor bridge: `primaryFiniteRow0Parent0Split100Sub0_collapsedDegree0_rawD17_interval_of_signed_factor_segment`
- raw/poly signed-factor bridge: `primaryFiniteRow0Parent0Split100Sub0_collapsedDegree0_rawPolySegmentValid_of_rawD17_signed_factor_segment`
- abs theorem bridge: `primaryFiniteRow0Parent0Split100Sub0_collapsedDegree0_hSignedD17PolyDeriv_generated`
- segmented abs bridge: `primaryFiniteRow0Parent0Split100Sub0_collapsedDegree0_hSignedD17PolyDeriv_of_signed_segment_cover`
- budget theorem: `primaryFiniteRow0Parent0Split100Sub0_collapsedDegree0_budget_pass_rat`
- final bridge: `primaryFiniteRow0Parent0Split100Sub0_collapsed_degree0_remainder_of_signed_interval_and_budget`
- segmented final bridge: `primaryFiniteRow0Parent0Split100Sub0_collapsed_degree0_remainder_of_signed_segment_family_cert`

Required generated constants:

- `primaryFiniteRow0Parent0Split100Sub0CollapsedDegree0DerivLower`
- `primaryFiniteRow0Parent0Split100Sub0CollapsedDegree0DerivUpper`
- `primaryFiniteRow0Parent0Split100Sub0CollapsedDegree0DerivAbs`
- `primaryFiniteRow0Parent0Split100Sub0DirectCollapsedDegree0PolyErrorAbs`

## Required Rows

### A0_raw_d17_signed_factor_rows

- object: `segment-local signed factor interval rows for OmegaActual and ShapeSqActual derivatives through order 18`
- status: `checked_full_cell_smoke_payload_not_budget_spendable`
- failureCode: `STEP33_A1_SUB0_COMBINED_ORDER16_COLLAPSED_DEGREE0_POLY_DERIV_SIGNED_SOURCE_GAP`

### A0b_raw_d17_term_corner_rows

- object: `exact corner rows for choose(18,k) * D^(18-k)OmegaActual * D^kShapeSqActual`
- status: `checked_for_full_cell_smoke_only_missing_tighter_local_rows`
- failureCode: `STEP33_A1_SUB0_COMBINED_ORDER16_COLLAPSED_DEGREE0_POLY_DERIV_SIGNED_SOURCE_GAP`

### A0c_scaled_raw_d17_assembly_rows

- object: `rawLower <= ActiveScaleCoeff * sum termLower and ActiveScaleCoeff * sum termUpper <= rawUpper`
- status: `checked_for_full_cell_smoke_only_missing_tighter_local_rows`
- failureCode: `STEP33_A1_SUB0_COMBINED_ORDER16_COLLAPSED_DEGREE0_POLY_DERIV_SIGNED_SOURCE_GAP`

### A1_poly_segment_interval_rows

- object: `segment-local lower/upper interval theorems for deriv(NominalOrder16Poly)`
- status: `checked_proof_grade_full_cell_row`
- failureCode: `NONE`

### A2_signed_subtraction_rows

- object: `exact rational rows lower <= rawLower - polyUpper and rawUpper - polyLower <= upper`
- status: `checked_for_full_cell_smoke_only_not_budget_spendable`
- failureCode: `STEP33_A1_SUB0_COMBINED_ORDER16_COLLAPSED_DEGREE0_POLY_DERIV_SIGNED_SOURCE_GAP`

### A3_segment_cover

- object: `exact cover of Set.Icc 0 (1/10) by generated segments`
- status: `missing_tighter_local_family`
- failureCode: `STEP33_A1_SUB0_COMBINED_ORDER16_COLLAPSED_DEGREE0_POLY_DERIV_SIGNED_SOURCE_GAP`

### B_deriv_abs_budget

- object: `for every segment, -derivAbs <= lower_i and upper_i <= derivAbs`
- status: `failed_for_full_cell_smoke_segment0`
- failureCode: `STEP33_A1_SUB0_COMBINED_ORDER16_COLLAPSED_DEGREE0_POLY_DERIV_SIGNED_SOURCE_GAP`

### C_degree0_budget

- object: `coeffErrorAbs + derivAbs / 20 <= polyErrorAbs`
- status: `failed_for_full_cell_smoke_segment0`
- failureCode: `STEP33_A1_SUB0_COMBINED_ORDER16_COLLAPSED_DEGREE0_POLY_DERIV_SIGNED_SOURCE_GAP`

### D_final_bridge

- object: `apply primaryFiniteRow0Parent0Split100Sub0_collapsed_degree0_remainder_of_signed_segment_family_cert`
- status: `checked_receiver_present`
- failureCode: `STEP33_A1_SUB0_COMBINED_ORDER16_COLLAPSED_DEGREE0_POLY_DERIV_SIGNED_SOURCE_GAP`

## Guard

- activeActual-alone D17 norm budget
- separate deriv(NominalOrder16Poly) norm budget
- raw-D17 factorwise/two-segment rows
- RawProduct18 absolute majorant
- factor/P45/zero-model killed budgets
- sampled rows or center jets as uniform full-cell bounds

## Raw-D17 Signed-Factor Smoke Payload

- file: `Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16CollapsedDegree0RawD17SignedFactorPayload.lean`
- payloadLedger: `ACTIVE/requests/step33_bootstrap/step33_a1_sub0_collapsed_degree0_raw_d17_signed_factor_payload.json`
- segment0Valid: `True`
- rawPolySegment0Valid: `True`
- segment0BudgetSpendable: `False`
- activeNextPatch: `False`
- routeStatus: `superseded_by_v21_direct_whole_expression_row_source`
- segment0BudgetFailureCode: `STEP33_A1_SUB0_COMBINED_ORDER16_COLLAPSED_DEGREE0_RAW_D17_SIGNED_FACTOR_SEGMENT_BUDGET_CONSTANT_FAIL`
- segment0BudgetFailureTheorem: `primaryFiniteRow0Parent0Split100Sub0_rawD17_signedFactor_segment0_budget_not_spendable`

The smoke payload validates the receiver and raw/poly bridge for one
full-cell segment, but its exact budget theorem proves this coarse
segment is not spendable.  Under the active v21 direct contract this
payload is retained only as support evidence; it is not the selected
next patch and must not resurrect the factorwise route as closure.

## Coarse Triangle Budget Audit

- file: `Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16CollapsedDegree0SignedSourceBudgetAudit.lean`
- candidateClass: `independent_abs_triangle`
- budgetPassed: `False`
- auditFailureIfMissing: `STEP33_A1_SUB0_COMBINED_ORDER16_COLLAPSED_DEGREE0_COARSE_TRIANGLE_BUDGET_AUDIT_GAP`
- liveGapAfterAudit: `STEP33_A1_SUB0_COMBINED_ORDER16_COLLAPSED_DEGREE0_POLY_DERIV_SIGNED_SOURCE_GAP`

This audit kills only the independent absolute/triangle estimate.
It does not prove that the true signed whole-expression row fails.

## Computer Use Route Review

- used: `True`
- latestRequest: `Step33A.1-A direct row-source gate after v21`
- latestStatus: `answered`
- recommendedOption: `A`
- localDecision: `A`
- decision: Build the first Lean-checkable direct signed-source segment for the already-subtracted expression.  Keep the raw-D17 smoke payload as support evidence, but do not use it as the active next patch after its budget failure.

- `primaryFiniteRow0Parent0Split100Sub0CollapsedDegree0TriangleDerivAbsRat`: present=`True`, line=`40`
- `primaryFiniteRow0Parent0Split100Sub0_collapsedDegree0_triangle_budget_fail_rat`: present=`True`, line=`49`
- `primaryFiniteRow0Parent0Split100Sub0_collapsedDegree0_triangle_budget_not_spendable`: present=`True`, line=`58`

## Symbol Audit

### Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16CollapsedDegree0SignedSourcePayload.lean

- `primaryFiniteRow0Parent0Split100Sub0CollapsedDegree0SignedSourceExpr`: present=`True`, line=`31`
- `primaryFiniteRow0Parent0Split100Sub0CollapsedDegree0SignedSourceTarget`: present=`True`, line=`39`
- `Step33Sub0CollapsedDegree0SignedSourceCert`: present=`True`, line=`54`
- `structure Valid`: present=`True`, line=`69`
- `sourceInterval`: present=`True`, line=`65`
- `derivAbsBudget`: present=`True`, line=`74`
- `degree0Budget`: present=`True`, line=`77`
- `theorem valid_of_signed_interval_and_budget`: present=`True`, line=`86`
- `theorem to_hSignedD17PolyDeriv`: present=`True`, line=`109`
- `theorem to_collapsed_degree0_remainder`: present=`True`, line=`135`
- `primaryFiniteRow0Parent0Split100Sub0_collapsedDegree0_hSignedD17PolyDeriv_of_signed_interval`: present=`True`, line=`157`
- `primaryFiniteRow0Parent0Split100Sub0_collapsed_degree0_remainder_of_signed_interval_and_budget`: present=`True`, line=`190`
- `Step33Sub0CollapsedDegree0SignedSourceSegmentCert`: present=`True`, line=`215`
- `Step33Sub0CollapsedDegree0RawPolySegmentCert where`: present=`True`, line=`340`
- `def toSignedSegmentCert`: present=`True`, line=`353`
- `namespace Step33Sub0CollapsedDegree0RawPolySegmentCert`: present=`True`, line=`350`
- `theorem valid_of_raw_poly_intervals`: present=`True`, line=`245`
- `primaryFiniteRow0Parent0Split100Sub0_collapsedDegree0_signedSegmentValid_of_raw_poly_intervals`: present=`True`, line=`309`
- `Step33Sub0CollapsedDegree0SignedSourceSegmentCover`: present=`True`, line=`404`
- `primaryFiniteRow0Parent0Split100Sub0_collapsedDegree0_hSignedD17PolyDeriv_of_signed_segment_cover`: present=`True`, line=`416`
- `primaryFiniteRow0Parent0Split100Sub0_collapsed_degree0_remainder_of_signed_segment_cover_and_budget`: present=`True`, line=`453`
- `Step33Sub0CollapsedDegree0SignedSourceSegmentFamilyCert`: present=`True`, line=`484`
- `Step33Sub0CollapsedDegree0RawPolySegmentCover`: present=`True`, line=`546`
- `Step33Sub0CollapsedDegree0RawPolySegmentFamilyCert`: present=`True`, line=`556`
- `theorem to_signedSegmentFamilyValid`: present=`True`, line=`589`
- `primaryFiniteRow0Parent0Split100Sub0_collapsed_degree0_remainder_of_raw_poly_segment_family_cert`: present=`True`, line=`635`
- `primaryFiniteRow0Parent0Split100Sub0_collapsed_degree0_remainder_of_signed_segment_family_cert`: present=`True`, line=`665`
- `primaryFiniteRow0Parent0Split100Sub0_collapsed_degree0_remainder_of_signed_source_cert`: present=`True`, line=`650`

### Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16ScaledRemainderDirectCollapsedDegree0CenterAudit.lean

- `primaryFiniteRow0Parent0Split100Sub0DirectCollapsedDegree0Coeff0`: present=`True`, line=`26`
- `primaryFiniteRow0Parent0Split100Sub0DirectCollapsedDegree0CoeffErrorAbs`: present=`True`, line=`31`
- `primaryFiniteRow0Parent0Split100Sub0_directCollapsed_degree0_hCenter_generated`: present=`True`, line=`46`
- `primaryFiniteRow0Parent0Split100Sub0_combinedOrder16ScaledRemainder_collapsed_degree0_remainder_of_center_and_polyDeriv_source`: present=`True`, line=`80`

### Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16CollapsedDegree0NominalPolyDerivRows.lean

- `primaryFiniteRow0Parent0Split100Sub0NominalOrder16PolyDerivCoeff`: present=`True`, line=`35`
- `primaryFiniteRow0Parent0Split100Sub0NominalOrder16PolyDerivAbsRat`: present=`True`, line=`43`
- `primaryFiniteRow0Parent0Split100Sub0_nominalOrder16Poly_deriv_eq_poly`: present=`True`, line=`75`
- `primaryFiniteRow0Parent0Split100Sub0_nominalOrder16Poly_deriv_abs_le`: present=`True`, line=`90`
- `primaryFiniteRow0Parent0Split100Sub0NominalOrder16PolyDerivSegmentCount`: present=`True`, line=`118`
- `primaryFiniteRow0Parent0Split100Sub0_nominalOrder16Poly_deriv_segment_cover`: present=`True`, line=`149`
- `primaryFiniteRow0Parent0Split100Sub0_nominalOrder16Poly_deriv_segment_interval_generated`: present=`True`, line=`174`

### Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16CollapsedDegree0RawD17SignedFactorRows.lean

- `primaryFiniteRow0Parent0Split100Sub0RawProduct18SignedTerm`: present=`True`, line=`75`
- `primaryFiniteRow0Parent0Split100Sub0_rawProductActual_order18_eq_signedLeibniz`: present=`True`, line=`84`
- `Step33Sub0CollapsedDegree0RawD17SignedFactorSegmentCert`: present=`True`, line=`116`
- `def termCornerRows`: present=`True`, line=`131`
- `def toRawPolySegmentCert`: present=`True`, line=`168`
- `structure Valid`: present=`True`, line=`182`
- `factorRows`: present=`True`, line=`188`
- `termCorners`: present=`True`, line=`203`
- `rawAssembly`: present=`True`, line=`205`
- `theorem to_termRows`: present=`True`, line=`215`
- `theorem to_rawInterval`: present=`True`, line=`263`
- `theorem to_rawPolySegmentValid`: present=`True`, line=`342`
- `primaryFiniteRow0Parent0Split100Sub0_collapsedDegree0_rawD17_interval_of_signed_factor_segment`: present=`True`, line=`368`
- `primaryFiniteRow0Parent0Split100Sub0_collapsedDegree0_rawPolySegmentValid_of_rawD17_signed_factor_segment`: present=`True`, line=`383`

### Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16CollapsedDegree0RawD17SignedFactorPayload.lean

- `primaryFiniteRow0Parent0Split100Sub0RawD17SignedFactorSegment0`: present=`True`, line=`115`
- `primaryFiniteRow0Parent0Split100Sub0_rawD17_signedFactor_segment0_valid`: present=`True`, line=`267`
- `primaryFiniteRow0Parent0Split100Sub0RawD17SignedFactorRawPolySegment0`: present=`True`, line=`348`
- `primaryFiniteRow0Parent0Split100Sub0_rawD17_signedFactor_rawPoly_segment0_valid`: present=`True`, line=`359`
- `primaryFiniteRow0Parent0Split100Sub0_rawD17_signedFactor_segment0_budget_fail_rat`: present=`True`, line=`394`
- `primaryFiniteRow0Parent0Split100Sub0_rawD17_signedFactor_segment0_budget_not_spendable`: present=`True`, line=`403`

## Boundary

This ledger is not a proof-grade source row certificate.  It records
the exact Lean surface and keeps the node fail-closed until the
lower/upper interval theorem and exact rational budget rows exist.
