# Step33A.1-A Direct Signed Segment0 Taylor-Model Gate

schema: `q3_psdpd_step33_a1_sub0_collapsed_degree0_direct_signed_segment0_taylor_model_gate.v4`
route: `collapsed_degree0_direct_signed_segment0_taylor_model`
proofStatus: `segment0_interval_checked_missing_family_budget`

## Verdict

- proofGrade: `False`
- currentGap: `STEP33_A1_SUB0_COMBINED_ORDER16_COLLAPSED_DEGREE0_DIRECT_SIGNED_SOURCE_UNIFORM_SEGMENT_ROWS_GAP`
- parentGap: `STEP33_A1_SUB0_COMBINED_ORDER16_COLLAPSED_DEGREE0_POLY_DERIV_SIGNED_SOURCE_GAP`
- firstFailureCode: `STEP33_A1_SUB0_COMBINED_ORDER16_COLLAPSED_DEGREE0_DIRECT_SIGNED_SOURCE_UNIFORM_SEGMENT_ROWS_GAP`
- budgetFailureCode: `STEP33_A1_SUB0_COMBINED_ORDER16_COLLAPSED_DEGREE0_DIRECT_SIGNED_SEGMENT0_BUDGET_CONSTANT_FAIL`
- targetLeanFile: `Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16CollapsedDegree0DirectSignedSourceSegment0Payload.lean`
- targetLeanFileExists: `True`
- targetPayloadPresent: `True`
- shouldEmitLeanPayload: `False`

## Browser / Computer Use Route Review

- status: `answered`
- nextPatch: direct segment-0 Taylor-model certificate for the complete already-subtracted signed expression
- firstScript: `scripts/generate_step33_a1_sub0_collapsed_degree0_direct_signed_segment0.py`
- firstLeanFile: `Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16CollapsedDegree0DirectSignedSourceSegment0Payload.lean`
- firstGeneratedArtifact: `ACTIVE/requests/step33_bootstrap/step33_a1_sub0_collapsed_degree0_direct_signed_segment0_taylor_model.json`
- firstGenericLeanBridge: `Q3/Proofs/PSD_CenteredCoeffRawOmegaACenteredTaylorDerivativeModel18.lean`
- followupChoice: `C`
- followupFirstFile: `Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16CollapsedDegree0LocalFactorTaylorModelBridge.lean`
- modelRemainderTheorem: `primaryFiniteRow0Parent0Split100Sub0_collapsedDegree0_signedSource_segment0_model_remainder_generated`
- segmentIntervalTheorem: `primaryFiniteRow0Parent0Split100Sub0_collapsedDegree0_signedSource_segment0_interval_generated`
- failureCodeIfNotProducibleNow: `STEP33_A1_SUB0_COMBINED_ORDER16_COLLAPSED_DEGREE0_LOCAL_FACTOR_JETS_TO_WHOLE_EXPRESSION_TAYLOR_MODEL_GAP`

Exact existing theorem names observed in the Browser answer:

- `primaryFiniteRow0Parent0Split100Sub0_omegaActual_localCenterJet18_sharp_interval_generated`
- `primaryFiniteRow0Parent0Split100Sub0_shapeSqActual_localCenterJet18_sharp_interval_generated`
- `iteratedDeriv_norm_le_centeredTaylorDerivMajorant18`
- `primaryFiniteRow0Parent0Split100Sub0_rawProductActual_order18_eq_signedLeibniz`
- `primaryFiniteRow0Parent0Split100Sub0_componentProductActual_order17_eq_rawProduct18`
- `primaryFiniteRow0Parent0Split100Sub0_nominalOrder16Poly_deriv_eq_poly`
- `primaryFiniteRow0Parent0Split100Sub0_activeScale_mem_tightInterval`
- `primaryFiniteRow0Parent0Split100Sub0_collapsedDegree0_signedSource_segment0_remainder_of_localFactorTaylor18`

## Segment0 Convention

- cellL: `0`
- cellU: `1/20`
- center: `1/40`
- radius: `1/40`
- polynomialDegree: `28`
- expression: `primaryFiniteRow0Parent0Split100Sub0CollapsedDegree0SignedSourceExpr`

## Source Material Audit

- firstUnmetInput: `full_segment_family_cover_and_derivAbs_degree0_budget_rows`

Usable support:

- local signed factor center-jet intervals at 1/40 and 3/40, plus factor order18 bounds
- signed Leibniz equality/receiver for raw-D17 factor segments
- nominal polynomial derivative interval rows in the target subtraction
- signed-source segment-family receiver and final degree-0 bridge
- Lean-checked local factor Taylor18 bridge from segment0 factor models into the signed-source segment receiver

Now proof cargo:

- `Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16CollapsedDegree0LocalFactorTaylorModelPayload.lean`
- `Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16CollapsedDegree0DirectSignedSourceSegment0Payload.lean`
- `primaryFiniteRow0Parent0Split100Sub0_collapsedDegree0_signedSource_segment0_interval_generated`

Not yet proof cargo:

- final segment-family cover, derivAbs budget, and degree-0 budget rows

Why insufficient:

The segment0 interval row is Lean-checked.  It still covers only `[0, 1/20]` and does not provide the full segment-family cover, the global `derivAbs` containment, or the degree-0 budget row.  Point rows, factorwise intervals, and budget-killed raw-D17 payloads do not provide those missing rows.


## Component Assembly Audit

- verdict: `support_present_but_not_segment0_whole_expression_source`
- segment0TargetCenter: `1/40`
- segment0TargetRadius: `1/40`
- componentAssemblyCenter: `1/20`
- centerCrosswalkStatus: missing: available component assembly is centered at 1/20; the active segment0 target is centered at 1/40
- exactAssemblyStatus: `algebraic_assembly_payload_checked_remainder_source_open`
- exactAssemblyFirstFailure: `STEP33_A1_SUB0_SHAPESQ_DERIV_EXPLICIT_CAUCHY_ROWS_2_TO_15_ORDER16_GAP`
- residualPayloadStatus: `fail_closed_shapesq_same_coeff_payload_checked_component_remainder_gap`
- residualPayloadFirstFailure: `STEP33_A1_SUB0_COMPONENT_TAYLOR_REMAINDER_SOURCE_GAP`
- streamLedgerStatus: `fail_closed_algebraic_assembly_and_shapesq_same_coeff_payload_checked_component_remainder_source_gap`
- failureCodeIfUsedAsClosure: `STEP33_A1_SUB0_COMBINED_ORDER16_COLLAPSED_DEGREE0_LOCAL_FACTOR_JETS_TO_WHOLE_EXPRESSION_TAYLOR_MODEL_GAP`

Field summary:

- exactAssembly.assembledRawDerivCoeff: present=`True`, kind=`list`, length=`46`
- exactAssembly.residualTaylorCoeff: present=`True`, kind=`list`, length=`46`
- exactAssembly.componentPropagationRemainderAbs: present=`False`, kind=`missing`, length=`None`
- exactAssembly.residualTaylorRemainderAbs: present=`False`, kind=`missing`, length=`None`
- residualPayload.modelDerivCoeff: present=`True`, kind=`list`, length=`16`
- residualPayload.modelDerivCoeffPaddedToAssembledDegree: present=`True`, kind=`list`, length=`46`

These artifacts are useful coefficient/support evidence, but they do not provide a same-center segment0 theorem for the complete already-subtracted expression with modelCoeff, remainderAbs, Horner bounds, and sourceLower/sourceUpper.


## Target Symbols

- `primaryFiniteRow0Parent0Split100Sub0_collapsedDegree0_signedSource_segment0_interval_generated`: present=`True`, line=`29`
- `primaryFiniteRow0Parent0Split100Sub0_collapsedDegree0_directSignedSource_segment0_valid_generated`: present=`True`, line=`47`

## Required Exact Data

### cell

- needed: cellL=0, cellU=1/20, center=1/40, radius=1/40
- status: `specified`

### signed_center_jets

- needed: OmegaActual and ShapeSqActual signed center jets sufficient to assemble the complete D17 product row before interval widening
- status: `partial_support_only`

### uniform_order18_bounds

- needed: uniform order18 bounds for the factors on segment0
- status: `support_present_but_not_whole_expression_source`

### signed_leibniz_assembly

- needed: exact signed Leibniz assembly for the product-derivative and remainder terms underlying activeScale * D17(ComponentProductActual) - deriv(NominalOrder16Poly)
- status: `checked_for_segment0`
- failureCode: `None`

### whole_expression_model

- needed: concrete LocalFactorTaylor18Segment0Cert rows producing the same-segment signed-source interval
- status: `checked_for_segment0_via_local_factor_taylor18_payload`
- failureCode: `None`

### whole_expression_remainder

- needed: derived segment0 sourceLower/sourceUpper plus final derivAbs and degree-0 budget rows
- status: `blocked_until_uniform_family_and_budget_rows_exist`
- failureCode: `STEP33_A1_SUB0_COMBINED_ORDER16_COLLAPSED_DEGREE0_DIRECT_SIGNED_SOURCE_UNIFORM_SEGMENT_ROWS_GAP`

### horner_interval

- needed: Horner stageLower/stageUpper, modelLower/modelUpper
- status: `blocked_until_model_exists`

### final_source_interval

- needed: final sourceLower/sourceUpper for SignedSourceExpr
- status: `blocked_until_model_exists`

## Support Surfaces

### `Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16CollapsedDegree0SignedSourcePayload.lean`

- exists: `True`
- allSymbolsPresent: `True`
- sha256: `b738f63142f35c9679158af0ebe30acd2a60d37eeb5012c4a80207ee12feec46`

- `primaryFiniteRow0Parent0Split100Sub0CollapsedDegree0SignedSourceExpr`: present=`True`, line=`31`
- `Step33Sub0CollapsedDegree0SignedSourceSegmentCert`: present=`True`, line=`215`
- `Step33Sub0CollapsedDegree0SignedSourceSegmentFamilyCert`: present=`True`, line=`484`

### `Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16CollapsedDegree0NominalPolyDerivRows.lean`

- exists: `True`
- allSymbolsPresent: `True`
- sha256: `630853d89234ec3e47c57196c559b8be4ea824137c9822c9a2fad61928fcb9fd`

- `primaryFiniteRow0Parent0Split100Sub0_nominalOrder16Poly_deriv_eq_poly`: present=`True`, line=`75`
- `primaryFiniteRow0Parent0Split100Sub0_nominalOrder16Poly_deriv_segment_interval_generated`: present=`True`, line=`174`

### `Q3/Proofs/PSD_CenteredCoeffRawOmegaARawD17SharpLocalCenterJets18Payload.lean`

- exists: `True`
- allSymbolsPresent: `True`
- sha256: `dee0ec422749899121a5b54e3d4f0da02e61109d6367d1eb162d03255d147463`

- `primaryFiniteRow0Parent0Split100Sub0OmegaActualDerivativeMajorant18Rat`: present=`True`, line=`172`
- `primaryFiniteRow0Parent0Split100Sub0ShapeSqActualSharpDerivativeMajorant18Rat`: present=`True`, line=`182`
- `primaryFiniteRow0Parent0Split100Sub0_omegaActual_localCenterJet18_sharp_interval`: present=`True`, line=`831`
- `primaryFiniteRow0Parent0Split100Sub0_shapeSqActual_localCenterJet18_sharp_interval`: present=`True`, line=`855`
- `primaryFiniteRow0Parent0Split100Sub0_omegaActual_derivative_twoSegment_sharp_interval`: present=`True`, line=`941`
- `primaryFiniteRow0Parent0Split100Sub0_shapeSqActual_derivative_twoSegment_sharp_interval`: present=`True`, line=`999`
- `primaryFiniteRow0Parent0Split100Sub0_omegaActual_order18_on_rawD17Segment_sharp`: present=`True`, line=`254`
- `primaryFiniteRow0Parent0Split100Sub0_shapeSqActual_order18_on_rawD17Segment_sharp`: present=`True`, line=`275`

### `Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationActiveActualCenterJetRowsPayload.lean`

- exists: `True`
- allSymbolsPresent: `True`
- sha256: `724577b57337b00d52eda470d47b245dd558c913d289e5153f464227c65f62f4`

- `primaryFiniteRow0Parent0Split100Sub0_activeActual_centerJet_row_interval_from_factor_rows`: present=`True`, line=`927`
- `primaryFiniteRow0Parent0Split100Sub0_omegaActual_signed_centerJet_interval`: present=`True`, line=`250`
- `primaryFiniteRow0Parent0Split100Sub0_shapeSqActual_signed_centerJet_interval`: present=`True`, line=`376`

### `Q3/Proofs/PSD_CenteredCoeffRawOmegaAComponentTaylorCoeffAssembly.lean`

- exists: `True`
- allSymbolsPresent: `True`
- sha256: `bfa94f3f7865292733f65705ffb6d813abbc658c5efa66fb87fb3f6957d3fbba`

- `primaryFiniteRow0Parent0Split100Sub0OmegaTaylorCoeff`: present=`True`, line=`278`
- `primaryFiniteRow0Parent0Split100Sub0ShapeSqTaylorCoeff`: present=`True`, line=`426`
- `primaryFiniteRow0Parent0Split100Sub0OmegaShapeSqDerivProductCoeff`: present=`True`, line=`1121`

### `Q3/Proofs/PSD_CenteredCoeffRawOmegaACenteredTaylorDerivativeMajorant18.lean`

- exists: `True`
- allSymbolsPresent: `True`
- sha256: `54da6c8ce5cacc7c5de63ef256fd81a878f96fd3f356d6d32c1ca70fab84bcaa`

- `centeredTaylorDerivMajorant18`: present=`True`, line=`168`
- `iteratedDeriv_norm_le_centeredTaylorDerivMajorant18`: present=`True`, line=`202`

### `Q3/Proofs/PSD_CenteredCoeffRawOmegaACenteredTaylorDerivativePointInterval18.lean`

- exists: `True`
- allSymbolsPresent: `True`
- sha256: `29cccd9536ab2cc24fee7b6016b7f0cab844cb8079e7848f60a6727e6ab0ae93`

- `centeredTaylorDerivPointLower18`: present=`True`, line=`100`
- `centeredTaylorDerivPointUpper18`: present=`True`, line=`106`
- `iteratedDeriv_mem_Icc_of_centerJet18_point_remainder`: present=`True`, line=`197`

### `Q3/Proofs/PSD_CenteredCoeffRawOmegaACenteredTaylorDerivativeModel18.lean`

- exists: `True`
- allSymbolsPresent: `True`
- sha256: `71c68144cf09be3f043c718b0de71ecac9c21c79450c88195c9890c8d9831fa3`

- `centeredTaylorDerivPolynomial18`: present=`True`, line=`26`
- `centeredTaylorDerivError18`: present=`True`, line=`38`
- `centeredTaylorDerivPolynomial18_abs_bound`: present=`True`, line=`52`
- `iteratedDeriv_sub_centeredTaylorDerivPolynomial18_norm_le`: present=`True`, line=`138`

### `Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16CollapsedDegree0LocalFactorTaylorModelBridge.lean`

- exists: `True`
- allSymbolsPresent: `True`
- sha256: `af7d30e64d4f09e121a344b0d236cf2d043ae5def8946474221fd203c196d220`

- `Step33Sub0CollapsedDegree0LocalFactorTaylor18Segment0Cert`: present=`True`, line=`99`
- `structure Valid`: present=`True`, line=`207`
- `to_rawD17SignedFactorSegmentValid`: present=`True`, line=`452`
- `to_rawPolySegmentValid`: present=`True`, line=`466`
- `to_signedSegmentValid`: present=`True`, line=`476`
- `primaryFiniteRow0Parent0Split100Sub0_collapsedDegree0_signedSource_segment0_remainder_of_localFactorTaylor18`: present=`True`, line=`491`

### `Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16ActiveActualRawProduct18Source.lean`

- exists: `True`
- allSymbolsPresent: `True`
- sha256: `a5c3f5968ec55f259c292e18135ceb785a979b6e776b5a4638342c45dc425c68`

- `primaryFiniteRow0Parent0Split100Sub0_rawProductActual_order18_abs_generated`: present=`True`, line=`147`
- `primaryFiniteRow0Parent0Split100Sub0_componentProductActual_order17_abs_generated`: present=`True`, line=`160`

### `Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16CollapsedDegree0RawD17SignedFactorRows.lean`

- exists: `True`
- allSymbolsPresent: `True`
- sha256: `ea16467b384dc6b62215e488dd8191df5aaf95d8d86f8bfe0f74f8642412353f`

- `primaryFiniteRow0Parent0Split100Sub0RawProduct18SignedTerm`: present=`True`, line=`75`
- `primaryFiniteRow0Parent0Split100Sub0_rawProductActual_order18_eq_signedLeibniz`: present=`True`, line=`84`
- `Step33Sub0CollapsedDegree0RawD17SignedFactorSegmentCert`: present=`True`, line=`116`
- `primaryFiniteRow0Parent0Split100Sub0_collapsedDegree0_rawD17_interval_of_signed_factor_segment`: present=`True`, line=`368`

### `Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16CollapsedDegree0RawD17SignedFactorPayload.lean`

- exists: `True`
- allSymbolsPresent: `True`
- sha256: `275365f66124a94ea0b89d65bd0fe834568d8bdd049d0beacee6c7fdba29f9cb`

- `primaryFiniteRow0Parent0Split100Sub0RawD17SignedFactorSegment0`: present=`True`, line=`115`
- `primaryFiniteRow0Parent0Split100Sub0_rawD17_signedFactor_segment0_valid`: present=`True`, line=`267`
- `primaryFiniteRow0Parent0Split100Sub0_rawD17_signedFactor_segment0_budget_not_spendable`: present=`True`, line=`403`

## Do Not Use

- independent Omega/ShapeSq final intervals
- raw-D17 factorwise budget
- RawProduct18 symmetric majorant
- activeActual-alone norm budget
- P45 / zero-model budgets
- sampled or floating-point rows
- point rows as uniform segment rows
- manual row-by-row Lean replay
- conditional Payload.lean fields

## Stop Rule

Stop and report CURRENT_GAP if the generator cannot produce a Lean-checkable whole-expression remainder theorem from local signed jets and order18 bounds.  Do not emit Payload.lean with a conditional field.

## Next Proof-Producing Patch

Generate/prove the remaining direct signed-source segment rows for the full cell, then prove exact derivAbs and degree-0 budget rows.  The segment0 interval theorem is checked.
