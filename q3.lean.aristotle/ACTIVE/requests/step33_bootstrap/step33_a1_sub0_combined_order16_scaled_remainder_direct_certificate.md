# Step33A.1-A Direct Scaled-Remainder Certificate Preflight

schema: `q3_psdpd_step33_a1_sub0_combined_order16_scaled_remainder_direct_certificate.v12`
route: `direct_whole_expression_scaled_remainder_certificate`
proofStatus: `lean_payload_generation_blocked_missing_collapsed_segment_rows`

## Verdict

- proofGrade: `False`
- receiverReady: `True`
- leanPayloadAllowed: `False`
- leanPayloadWritten: `False`
- currentGap: `STEP33_A1_SUB0_COMBINED_ORDER16_SCALED_REMAINDER_NONZERO_MODEL_INTERVAL_CERT_GAP`
- firstFailureCode: `STEP33_A1_SUB0_COMBINED_ORDER16_SCALED_REMAINDER_DIRECT_ROW_SOURCE_GAP`
- nominalPolynomialBridgePresent: `True`
- nominalPolynomialBridgeLeanChecked: `True`
- activeActualRemainderBridgePresent: `True`
- activeActualRemainderBridgeLeanChecked: `True`
- activeActualHornerSegmentReceiverPresent: `True`
- activeActualHornerSegmentReceiverLeanChecked: `True`
- activeActualHornerFamilyBridgePresent: `True`
- activeActualHornerFamilyBridgeLeanChecked: `True`
- firstConcreteUpstreamFailureCode: `STEP33_A1_SUB0_ACTIVE_ACTUAL_ORDER16_SEGMENT_REMAINDER_ROW_SOURCE_GAP`
- Computer Use route review: `C`

## Active-Actual Horner Row-Source Ledger

- file: `ACTIVE/requests/step33_bootstrap/step33_a1_sub0_active_actual_horner_row_source.json`
- exists: `True`
- schema: `q3_psdpd_step33_a1_sub0_active_actual_horner_row_source.v3`
- proofStatus: `interface_ready_rows_missing`
- proofGrade: `False`
- proofSafeClosedFields: `0`
- allPayloadObligationsPassed: `False`
- firstFailureCode: `STEP33_A1_SUB0_ACTIVE_ACTUAL_ORDER16_SEGMENT_REMAINDER_ROW_SOURCE_GAP`

This ledger is a generator contract only.  It is not a proof row and does not permit Lean payload emission while `allPayloadObligationsPassed` is false.

## Target

- Lean file: `Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16ScaledRemainderDirectConcretePayload.lean`
- theorem: `primaryFiniteRow0Parent0Split100Sub0_combinedOrder16ScaledRemainder_nonzeroModel_interval_generated`
- source-prop theorem: `primaryFiniteRow0Parent0Split100Sub0_combinedOrder16ScaledRemainder_nonzeroModel_sourceProp_generated`
- expression: `primaryFiniteRow0Parent0Split100Sub0CombinedCancellationOrder16ComponentSource eta - primaryFiniteRow0Parent0Split100Sub0CombinedOrder16NonzeroModelPoly eta`
- budget: `primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedResidualRemainderAbs`

## Proof Row Inputs

- `directNonzeroModelIntervalRowsLeanChecked`: `False`
- `directNonzeroModelSourcePropLeanChecked`: `False`
- `directHornerReceiverPresent`: `True`
- `directHornerReceiverLeanChecked`: `True`
- `directHornerSmokePresent`: `True`
- `directHornerSmokeLeanChecked`: `True`
- `directSourceBridgePresent`: `True`
- `directSourceBridgeLeanChecked`: `True`
- `directHornerSourceBridgePresent`: `True`
- `directHornerSourceBridgeLeanChecked`: `True`
- `directConcretePayloadPresent`: `False`
- `directHornerLakeEnvLeanChecked`: `False`
- `sourceRemainderBoundLeanChecked`: `False`
- `localModelSourceRowsLeanChecked`: `False`
- `localModelModelRowsLeanChecked`: `False`

## Payload Ledger Interface

- path: `ACTIVE/requests/step33_bootstrap/step33_a1_sub0_combined_order16_scaled_remainder_direct_payload.json`
- schema: `q3_psdpd_step33_a1_sub0_combined_order16_scaled_remainder_direct_payload.v18`
- expectedDataObject: `primaryFiniteRow0Parent0Split100Sub0CombinedOrder16ScaledRemainderDirectHornerData`
- expectedValidityTheorem: `primaryFiniteRow0Parent0Split100Sub0_combinedOrder16ScaledRemainderDirectHorner_valid`
- certificateDataObject: `primaryFiniteRow0Parent0Split100Sub0CombinedOrder16ScaledRemainderDirectHornerData`
- certificateValidityTheorem: `primaryFiniteRow0Parent0Split100Sub0_combinedOrder16ScaledRemainderDirectHorner_valid`
- matchesCertificate: `True`
- failureCodeIfMismatch: `STEP33_A1_SUB0_COMBINED_ORDER16_SCALED_REMAINDER_DIRECT_HORNER_LEDGER_INTERFACE_MISMATCH`

## Latest Computer Use Row Review

- used: `True`
- url: `https://chatgpt.com/g/g-p-69ad65d9bcfc8191a6931ea6f2c78f13/c/6a32cac5-cc54-83eb-b010-097faa30ac6b`
- recommendedOption: `A_for_active_actual_horner_family_bridge_then_fail_closed_rows`
- advisoryOnly: `True`
- decision: After the activeActual Horner segment receiver, add an isolated activeActual Horner family bridge into the existing DirectHorner family receiver.  It is conditional only; the proof-row generator remains blocked until rational/interval activeActual segment rows, range rows, cover rows, and budget rows exist.
- firstFileToEdit: `Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16NominalPolynomialBridge.lean`
- firstFileToCreate: `Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16ActiveActualHornerSegmentCert.lean`
- secondFileCreated: `Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16ActiveActualHornerFamilyBridge.lean`
- firstLeanDataObject: `Step33Sub0ActiveActualOrder16HornerSegmentCert`
- familyBridgeDataObject: `Step33Sub0ActiveActualOrder16HornerFamilyCert`
- firstLeanValidityTheorem: `primaryFiniteRow0Parent0Split100Sub0_activeActual_order16_segment_remainder_of_horner_cert`
- familyBridgeValidityTheorem: `primaryFiniteRow0Parent0Split100Sub0_directHornerFamily_valid_of_activeActualHornerFamily`
- familyBridgePayloadTheorem: `primaryFiniteRow0Parent0Split100Sub0_directPayloadTarget_of_activeActualHornerFamily`
- activeActualMissingRemainderTheorem: `primaryFiniteRow0Parent0Split100Sub0_activeActual_order16_segment_remainder`
- failureCodeIfRowsMissing: `STEP33_A1_SUB0_ACTIVE_ACTUAL_ORDER16_SEGMENT_REMAINDER_ROW_SOURCE_GAP`
- failureCodeIfFamilyBridgeMissing: `STEP33_A1_SUB0_ACTIVE_ACTUAL_ORDER16_HORNER_FAMILY_ALIGNMENT_GAP`

### Minimal Row Data Required

- exact segment cover for Set.Icc 0 (1/10)
- proof-grade scaled-active-actual rational coefficient stream
- proof-grade primaryFiniteRow0Parent0Split100Sub0_activeActual_order16_segment_remainder_of_horner_cert rows
- transport through activeActual remainder adapter into collapsed rows
- Horner stage lower/upper bounds
- proof-grade primaryFiniteRow0Parent0Split100Sub0_combinedOrder16ScaledRemainder_collapsed_segment_remainder rows
- final +/- BiasedResidualRemainderAbs budget rows

### Route Fork Follow-up

- used: `True`
- recommendedOption: `A_for_partial_nominal_bridge`
- decision: The partial nominal polynomial bridge is useful as exact rational extraction of the subtracted nominal polynomial.
- whyNotB: B is already subsumed by Step33Sub0CombinedOrder16ScaledRemainderDirectHornerCert.Valid.of_collapsed_horner_range and the family bridge.
- whyNotD: The route is not killed; the exact missing row-source interface is now named.

### What Must Not Be Reused

- killed factor majorants
- activeActual center jets as uniform cell bounds
- separate actual/nominal norm budgets
- zero-model budget
- sampled rows
- P45 machinery without a same-target theorem
- coarse P45/product budgets
- componentTaylorRemainder as an obligatory intermediate layer
- nominalOrder16Poly as an independent spendable budget

## Direct Horner Row Stream Status

- targetFile: `Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16ScaledRemainderDirectConcretePayload.lean`
- targetFileExists: `False`
- rowStreamPresent: `False`
- proofGrade: `False`
- failureCode: `STEP33_A1_SUB0_COMBINED_ORDER16_SCALED_REMAINDER_DIRECT_ROW_SOURCE_GAP`

### Required Symbols

- `primaryFiniteRow0Parent0Split100Sub0CombinedOrder16ScaledRemainderDirectHornerData`: present=`False`, line=`None`
- `primaryFiniteRow0Parent0Split100Sub0_combinedOrder16ScaledRemainderDirectHorner_valid`: present=`False`, line=`None`
- `primaryFiniteRow0Parent0Split100Sub0_combinedOrder16ScaledRemainder_nonzeroModel_interval_generated`: present=`False`, line=`None`
- `primaryFiniteRow0Parent0Split100Sub0_combinedOrder16ScaledRemainder_nonzeroModel_sourceProp_generated`: present=`False`, line=`None`

## Validation

- directLeanPathMode: `passed`
- lakeEnvLean.status: `not_completed_entrypoint_timeout`
- lakeEnvLean.command: `lake env lean Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16ScaledRemainderDirectHornerCertSmoke.lean`
- lakeEnvLean.note: The direct Lean check generated .olean/.ilean files; lake env lean remained nonresponsive in a bounded run.

### Direct Lean Commands

- `LEAN_PATH=<repo and package olean paths> lean -j 1 -s 65536 -o .lake/build/lib/lean/Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16ScaledRemainderDirectPayload.olean -i .lake/build/lib/lean/Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16ScaledRemainderDirectPayload.ilean Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16ScaledRemainderDirectPayload.lean`
- `LEAN_PATH=<repo and package olean paths> lean -j 1 -s 65536 -o .lake/build/lib/lean/Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16ScaledRemainderDirectHornerCert.olean -i .lake/build/lib/lean/Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16ScaledRemainderDirectHornerCert.ilean Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16ScaledRemainderDirectHornerCert.lean`
- `LEAN_PATH=<repo and package olean paths> lean -j 1 -s 65536 -o .lake/build/lib/lean/Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16ScaledRemainderDirectHornerCertSmoke.olean -i .lake/build/lib/lean/Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16ScaledRemainderDirectHornerCertSmoke.ilean Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16ScaledRemainderDirectHornerCertSmoke.lean`
- `LEAN_PATH=<repo and package olean paths> lean -j 1 -s 65536 -o .lake/build/lib/lean/Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16ScaledRemainderDirectSourceBridge.olean -i .lake/build/lib/lean/Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16ScaledRemainderDirectSourceBridge.ilean Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16ScaledRemainderDirectSourceBridge.lean`
- `LEAN_PATH=<repo and package olean paths> lean -j 1 -s 65536 -o .lake/build/lib/lean/Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16ScaledRemainderDirectHornerSourceBridge.olean -i .lake/build/lib/lean/Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16ScaledRemainderDirectHornerSourceBridge.ilean Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16ScaledRemainderDirectHornerSourceBridge.lean`

## Computer Use Route Review

- used: `True`
- url: `https://chatgpt.com/g/g-p-69ad65d9bcfc8191a6931ea6f2c78f13/c/6a32cac5-cc54-83eb-b010-097faa30ac6b`
- recommendedOption: `C`
- decision: Keep the direct route open, but do not build DirectConcretePayload.lean until the collapsedExpression coefficient stream and segment remainder theorem are present.
- failureCodeIfFails: `STEP33_A1_SUB0_COMBINED_ORDER16_SCALED_REMAINDER_DIRECT_ROW_SOURCE_GAP`

### First Artifacts

- `scripts/generate_step33_a1_sub0_combined_order16_scaled_remainder_direct_payload.py`
- `ACTIVE/requests/step33_bootstrap/step33_a1_sub0_combined_order16_scaled_remainder_direct_row_source_audit.json`
- `ACTIVE/requests/step33_bootstrap/step33_a1_sub0_combined_order16_scaled_remainder_direct_row_source_audit.md`

### Theorem Shape

```text
theorem primaryFiniteRow0Parent0Split100Sub0_combinedOrder16ScaledRemainder_collapsed_segment_remainder
  (i : Fin segmentCount) :
  forall eta in Set.Icc (cellL i : Real) (cellU i : Real),
    norm (CollapsedExpression eta -
      rawOmegaATaylorPolynomial degree (center i) (coeff i) eta) <=
    (polyErrorAbs i : Real)
```

### Must Check Before Progress Claim

- generated target is definitionally or theorem-wise equal to the current target
- segment cover is exact if segmented mode is used
- every Horner/rational propagation row is Lean-checked
- analytic remainder row is proof-grade, not sampled
- final +/- BiasedResidualRemainderAbs budget passes exactly
- the interval_generated theorem compiles unconditionally

### Internal Technique Only

- Horner split
- local-model segments
- source-Horner segments

### Not Proof Evidence

- centered-Taylor factor majorants killed by exact budget
- P45/full-Taylor machinery for the wrong target
- zero-model/direct-source budget
- independent bounds on product summands
- center jets as uniform full-cell intervals
- sampled/probe interval rows

## Computer Use Smoke Review

- used: `True`
- url: `https://chatgpt.com/g/g-p-69ad65d9bcfc8191a6931ea6f2c78f13/c/6a32cac5-cc54-83eb-b010-097faa30ac6b`
- recommendedOption: `B`
- decision: Before proof-row generation, validate the direct Horner receiver surface with an isolated smoke file.
- firstFile: `Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16ScaledRemainderDirectHornerCertSmoke.lean`
- firstTheoremObject: `primaryFiniteRow0Parent0Split100Sub0_scaledRemainderDirectHorner_receiver_smoke`
- failureCodeIfFails: `STEP33_A1_SUB0_COMBINED_ORDER16_SCALED_REMAINDER_DIRECT_HORNER_RECEIVER_VALIDATION_GAP`

### Must Check Before Progress Claim

- direct Lean pass for the smoke file
- .olean generation
- exact target-expression match
- clean marker scan

### What Not To Reuse

- killed factor-majorants
- P45/full-Taylor wrong target
- zero-model budget
- sampled rows
- separate product-summand norm bounds

## Upstream Row-Source Audit

- directFailureCode: `STEP33_A1_SUB0_COMBINED_ORDER16_SCALED_REMAINDER_DIRECT_ROW_SOURCE_GAP`
- firstConcreteUpstreamFailureCode: `STEP33_A1_SUB0_COMPONENT_TAYLOR_REMAINDER_SOURCE_GAP`
- componentTaylorRemainderGapActive: `True`
- proofGradeForDirectCertificate: `False`
- verdict: ShapeSqDeriv tight same-coefficient support is checked but nonfinal.  The component Taylor remainder gap is a recorded upstream obstruction, but the Computer Use route-fork review selects the direct whole-expression row stream as the active next patch, so componentTaylorRemainder is not an obligatory intermediate layer.
- nextImplementablePatch: Build the direct whole-expression rational/interval Horner row stream for the checked collapsedExpression target.

### Component Taylor Residual Ledger

- `path`: `ACTIVE/requests/step33_bootstrap/step33_a1_sub0_component_taylor_residual_payload.json`
- `exists`: `True`
- `schema`: `q3_psdpd_step33_a1_sub0_component_taylor_residual_payload.v19`
- `status`: `fail_closed_shapesq_same_coeff_payload_checked_component_remainder_gap`
- `firstFailure`: `STEP33_A1_SUB0_COMPONENT_TAYLOR_REMAINDER_SOURCE_GAP`
- `routeReviewRecommendedOption`: `B`
- `failureCodeIfRowsMissing`: `STEP33_A1_SUB0_COMPONENT_TAYLOR_REMAINDER_SIGNED_ROW_SOURCE_GAP`
- `failureCodeIfBudgetFalse`: `STEP33_A1_SUB0_COMPONENT_TAYLOR_REMAINDER_BUDGET_CONSTANT_FAIL`
- `firstTheoremObject`: `primaryFiniteRow0Parent0Split100Sub0_componentTaylor_remainder_source_generated`
- `shapeSqDerivTightValid`: `primaryFiniteRow0Parent0Split100Sub0_shapeSqDeriv_tight_valid`
- `shapeSqDerivTightTaylorSource`: `primaryFiniteRow0Parent0Split100Sub0_shapeSqDerivTightTaylorSource`
- `componentPropagationRemainderAbs`: `None`
- `residualTaylorRemainderAbs`: `None`

### ShapeSqDeriv Tight Ledger

- `path`: `ACTIVE/requests/step33_bootstrap/step33_a1_sub0_shapesq_deriv_tight_payload.json`
- `exists`: `True`
- `status`: `same_coefficient_tight_payload_checked_budget_nonfinal`
- `firstFailure`: `STEP33_A1_SUB0_COMPONENT_TAYLOR_REMAINDER_SOURCE_GAP`
- `nextPatch`: `Use the checked same-coefficient ShapeSqDeriv source as a proof object for the component route, but do not spend it as the final residual interval.  The next proof-producing patch is STEP33_A1_SUB0_COMPONENT_TAYLOR_REMAINDER_SOURCE_GAP: build the component Taylor remainder source consumed by exact raw-derivative assembly.`
- `guardPasses`: `True`
- `tightCoeffObjectsPresentInLean`: `True`
- `tightTaylorSourceTheoremPresentInLean`: `True`
- `tightValidTheoremPresentInLean`: `True`

### Do Not Use As Closure

- ShapeSqDeriv tight payload alone
- old rows0..11 product assembly budget
- stale ShapeSqDeriv rows gap

## Implementation Modes

### single_full_cell_interval

- `target`: `primaryFiniteRow0Parent0Split100Sub0_combinedOrder16ScaledRemainder_nonzeroModel_interval_generated`
- `status`: `blocked_missing_whole_expression_rows`
- `finalTheoremTarget`: `True`

### segmented_direct_family

- `target`: `Step33Sub0CombinedOrder16ScaledRemainderDirectFamilyCert.Valid`
- `status`: `receiver_ready_rows_missing`
- `finalTheoremTarget`: `True`

### direct_horner_family

- `target`: `Step33Sub0CombinedOrder16ScaledRemainderDirectHornerFamilyCert.Valid`
- `status`: `receiver_lean_checked_rows_missing`
- `finalTheoremTarget`: `True`
- `useOnlyAsInternalTechnique`: `True`
- `leanValidation`: `direct_lean_pass`
- `lakeEnvLeanValidation`: `not_completed_entrypoint_timeout`

### direct_collapsed_expression_source_bridge

- `target`: `primaryFiniteRow0Parent0Split100Sub0_combinedOrder16ScaledRemainder_eq_collapsedExpression`
- `status`: `source_bridge_lean_checked`
- `finalTheoremTarget`: `False`
- `useOnlyAsBridgeBeforeRows`: `True`
- `leanValidation`: `direct_lean_pass`

### direct_collapsed_horner_source_bridge

- `target`: `Step33Sub0CombinedOrder16ScaledRemainderDirectHornerCert.Valid.of_collapsed_horner_range`
- `familyTarget`: `Step33Sub0CombinedOrder16ScaledRemainderDirectHornerFamilyCert.valid_of_collapsed_horner_rows`
- `status`: `collapsed_horner_source_bridge_lean_checked`
- `finalTheoremTarget`: `False`
- `useOnlyAsBridgeBeforeRows`: `True`
- `leanValidation`: `direct_lean_pass`

### nominal_polynomial_bridge

- `target`: `primaryFiniteRow0Parent0Split100Sub0_combinedOrder16CollapsedExpression_eq_activeActual_sub_nominalOrder16Poly`
- `status`: `nominal_polynomial_bridge_lean_checked`
- `finalTheoremTarget`: `False`
- `useOnlyAsCoefficientCrosswalkBeforeRows`: `True`
- `leanValidation`: `direct_lean_pass`

### active_actual_remainder_bridge

- `target`: `primaryFiniteRow0Parent0Split100Sub0_collapsed_segment_remainder_of_activeActual`
- `coefficientTarget`: `primaryFiniteRow0Parent0Split100Sub0CombinedOrder16CollapsedCoeffOf`
- `status`: `active_actual_remainder_bridge_lean_checked`
- `finalTheoremTarget`: `False`
- `useOnlyAsBridgeBeforeRows`: `True`
- `leanValidation`: `direct_lean_pass`
- `nextMissingTheorem`: `primaryFiniteRow0Parent0Split100Sub0_activeActual_order16_segment_remainder`
- `failureCodeIfRowsMissing`: `STEP33_A1_SUB0_ACTIVE_ACTUAL_ORDER16_SEGMENT_REMAINDER_SOURCE_GAP`

### direct_horner_receiver_smoke

- `target`: `primaryFiniteRow0Parent0Split100Sub0_scaledRemainderDirectHorner_receiver_smoke`
- `status`: `smoke_lean_checked`
- `finalTheoremTarget`: `False`
- `useOnlyAsGateBeforeRows`: `True`
- `leanValidation`: `direct_lean_pass`
- `lakeEnvLeanValidation`: `not_completed_entrypoint_timeout`
- `failureCodeIfFails`: `STEP33_A1_SUB0_COMBINED_ORDER16_SCALED_REMAINDER_DIRECT_HORNER_RECEIVER_VALIDATION_GAP`

### local_model_segments

- `target`: `Step33Sub0CombinedOrder16BiasedResidualLocalModelSegmentFamilyCert.Valid`
- `status`: `STEP33_A1_SUB0_COMBINED_ORDER16_BIASED_RESIDUAL_LOCAL_MODEL_SEGMENT_PAYLOAD_GAP`
- `finalTheoremTarget`: `False`
- `useOnlyAsInternalTechnique`: `True`

### source_horner_segments

- `target`: `Step33Sub0CombinedOrder16BiasedResidualSourceHornerFamilyCert.Valid`
- `status`: `STEP33_A1_SUB0_COMBINED_ORDER16_BIASED_NONZERO_MODEL_RESIDUAL_BOUND_GAP`
- `finalTheoremTarget`: `False`
- `useOnlyAsInternalTechnique`: `True`

## Required Rows

### C0_target_normalization

- `status`: `checked_surface_present`
- `proofObject`: `primaryFiniteRow0Parent0Split100Sub0_biasedScaledRemainder_eq_nonzeroModelResidual`

### C1_segment_cover

- `status`: `missing_if_segmented_mode`
- `proofObject`: `cover of Set.Icc 0 (1/10)`

### C1b_collapsed_source_bridge

- `status`: `checked_surface_present`
- `proofObject`: `primaryFiniteRow0Parent0Split100Sub0_combinedOrder16ScaledRemainder_eq_collapsedExpression`
- `proofGradeRowsPresent`: `False`

### C1c_collapsed_horner_receiver_bridge

- `status`: `checked_surface_present`
- `proofObject`: `Step33Sub0CombinedOrder16ScaledRemainderDirectHornerCert.Valid.of_collapsed_horner_range`
- `familyProofObject`: `Step33Sub0CombinedOrder16ScaledRemainderDirectHornerFamilyCert.valid_of_collapsed_horner_rows`
- `proofGradeRowsPresent`: `False`
- `meaning`: `Future row data may prove a collapsedExpression remainder and transport it into the directRemainder field.`

### C1d_nominal_polynomial_bridge

- `status`: `checked_surface_present`
- `proofObject`: `primaryFiniteRow0Parent0Split100Sub0_combinedOrder16CollapsedExpression_eq_activeActual_sub_nominalOrder16Poly`
- `proofGradeRowsPresent`: `False`
- `meaning`: `The rational nominal order-16 polynomial is available as a partial coefficient crosswalk, but it is not a complete collapsedExpression coefficient stream and is not a budget.`

### C1e_active_actual_remainder_adapter

- `status`: `checked_surface_present`
- `proofObject`: `primaryFiniteRow0Parent0Split100Sub0_collapsed_segment_remainder_of_activeActual`
- `proofGradeRowsPresent`: `False`
- `meaning`: `A future scaled-active-actual segment remainder row can be transported to the collapsed-expression remainder row by subtracting nominalOrder16Poly inside one coefficient stream.`
- `nextMissingTheorem`: `primaryFiniteRow0Parent0Split100Sub0_activeActual_order16_segment_remainder`
- `failureCodeIfRowsMissing`: `STEP33_A1_SUB0_ACTIVE_ACTUAL_ORDER16_SEGMENT_REMAINDER_SOURCE_GAP`

### C2_collapsed_segment_remainder_rows

- `status`: `missing`
- `proofObject`: `primaryFiniteRow0Parent0Split100Sub0_combinedOrder16ScaledRemainder_collapsed_segment_remainder`
- `firstLeanDataObject`: `primaryFiniteRow0Parent0Split100Sub0CombinedOrder16ScaledRemainderDirectHornerData`
- `firstLeanValidityTheorem`: `primaryFiniteRow0Parent0Split100Sub0_combinedOrder16ScaledRemainderDirectHorner_valid`
- `failureCode`: `STEP33_A1_SUB0_COMBINED_ORDER16_SCALED_REMAINDER_DIRECT_ROW_SOURCE_GAP`
- `upstreamFailureCode`: `STEP33_A1_SUB0_ACTIVE_ACTUAL_ORDER16_SEGMENT_REMAINDER_ROW_SOURCE_GAP`

### C3_horner_or_local_model_rows

- `status`: `direct_horner_smoke_lean_checked_rows_missing`
- `proofObject`: `per-segment rational model and Horner stage bounds`
- `preRowGate`: `primaryFiniteRow0Parent0Split100Sub0_scaledRemainderDirectHorner_receiver_smoke`
- `collapsedPreRowGate`: `Step33Sub0CombinedOrder16ScaledRemainderDirectHornerCert.Valid.of_collapsed_horner_range`
- `failureCode`: `STEP33_A1_SUB0_COMBINED_ORDER16_SCALED_REMAINDER_DIRECT_HORNER_RECEIVER_VALIDATION_GAP`

### C4_analytic_remainder_rows

- `status`: `missing`
- `proofObject`: `proof-grade collapsedExpression segment remainder bound, not sampled/probe rows`
- `upstreamFailureCode`: `STEP33_A1_SUB0_ACTIVE_ACTUAL_ORDER16_SEGMENT_REMAINDER_ROW_SOURCE_GAP`

### C5_budget_rows

- `status`: `missing`
- `proofObject`: `lower/upper rows against primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedResidualRemainderAbs`

### C6_unconditional_lean_payload

- `status`: `blocked_until_C2_to_C5`
- `proofObject`: `Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16ScaledRemainderDirectConcretePayload.lean`

## Symbol Audit

### Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16ScaledRemainderDirectPayload.lean

- `Step33Sub0CombinedOrder16ScaledRemainderDirectSegmentCert`: present=`True`, line=`31`
- `Step33Sub0CombinedOrder16ScaledRemainderDirectFamilyCert`: present=`True`, line=`99`
- `primaryFiniteRow0Parent0Split100Sub0CombinedOrder16ScaledRemainderDirectPayloadTarget`: present=`True`, line=`140`
- `primaryFiniteRow0Parent0Split100Sub0_combinedOrder16ScaledRemainder_nonzeroModel_sourceProp_of_direct_payload`: present=`True`, line=`149`
- `primaryFiniteRow0Parent0Split100Sub0_combinedOrder16ScaledRemainder_nonzeroModel_sourceProp_of_full_cell_interval`: present=`True`, line=`175`

### Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16BiasedScaledRemainderZeroModelPayload.lean

- `primaryFiniteRow0Parent0Split100Sub0CombinedOrder16ScaledRemainderNonzeroModelSourceProp`: present=`True`, line=`61`
- `primaryFiniteRow0Parent0Split100Sub0_biasedScaledRemainder_eq_nonzeroModelResidual`: present=`True`, line=`70`
- `primaryFiniteRow0Parent0Split100Sub0_biasedScaledRemainderZeroModel_payload_target_of_nonzeroModelResidual`: present=`True`, line=`179`

### Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16NonzeroModel.lean

- `primaryFiniteRow0Parent0Split100Sub0CombinedOrder16NonzeroModelPoly`: present=`True`, line=`43`
- `primaryFiniteRow0Parent0Split100Sub0_combinedOrder16Source_sub_nonzeroModelPoly`: present=`True`, line=`1441`
- `primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedNonzeroModelResidualSlackRat`: present=`True`, line=`1024`

### Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16BiasedResidualLocalModelSegmentCert.lean

- `Step33Sub0CombinedOrder16BiasedResidualLocalModelSegmentFamilyCert`: present=`True`, line=`175`
- `theorem to_residualSourceProp`: present=`True`, line=`203`
- `theorem to_order16DirectIntervalValid`: present=`True`, line=`212`

### Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16BiasedResidualSourceHornerCert.lean

- `Step33Sub0CombinedOrder16BiasedResidualSourceHornerFamilyCert`: present=`True`, line=`331`
- `theorem to_residualSourceProp`: present=`True`, line=`419`
- `theorem to_order16DirectIntervalValid`: present=`True`, line=`432`

### Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16BiasedResidualSourceHornerPayload.lean

- `primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedResidualRemainderAbs`: present=`True`, line=`26`
- `primaryFiniteRow0Parent0Split100Sub0_biasedNonzeroModel_directInterval_valid_of_slack_remainder_bound`: present=`True`, line=`53`

### Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16ScaledRemainderDirectHornerCert.lean

- `Step33Sub0CombinedOrder16ScaledRemainderDirectHornerCert`: present=`True`, line=`38`
- `def poly`: present=`True`, line=`54`
- `def toDirectSegment`: present=`True`, line=`60`
- `structure Valid`: present=`True`, line=`70`
- `theorem directInterval`: present=`True`, line=`103`
- `theorem to_directSegmentValid`: present=`True`, line=`148`
- `def hornerTail`: present=`True`, line=`169`
- `theorem hornerTail_zero_eq_poly`: present=`True`, line=`179`
- `Step33Sub0CombinedOrder16ScaledRemainderDirectHornerRangeCert`: present=`True`, line=`191`
- `theorem polyRange`: present=`True`, line=`220`
- `theorem of_horner_range`: present=`True`, line=`261`
- `Step33Sub0CombinedOrder16ScaledRemainderDirectHornerFamilyCert`: present=`True`, line=`311`
- `def toDirectFamily`: present=`True`, line=`321`
- `theorem to_directFamilyValid`: present=`True`, line=`394`
- `theorem to_directPayloadTarget`: present=`True`, line=`408`
- `theorem to_nonzeroModelSourceProp`: present=`True`, line=`418`

### Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16ScaledRemainderDirectHornerCertSmoke.lean

- `primaryFiniteRow0Parent0Split100Sub0_scaledRemainderDirectHorner_receiver_smoke`: present=`True`, line=`24`
- `Step33Sub0CombinedOrder16ScaledRemainderDirectHornerFamilyCert`: present=`True`, line=`25`
- `primaryFiniteRow0Parent0Split100Sub0CombinedOrder16ScaledRemainderNonzeroModelSourceProp`: present=`True`, line=`30`

### Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16ScaledRemainderDirectSourceBridge.lean

- `primaryFiniteRow0Parent0Split100Sub0CombinedOrder16ScaledRemainderCollapsedExpression`: present=`True`, line=`33`
- `primaryFiniteRow0Parent0Split100Sub0_combinedOrder16ScaledRemainder_eq_collapsedExpression`: present=`True`, line=`45`
- `primaryFiniteRow0Parent0Split100Sub0_combinedOrder16ScaledRemainder_sourceProp_of_collapsed_interval`: present=`True`, line=`61`
- `primaryFiniteRow0Parent0Split100Sub0_combinedOrder16ScaledRemainder_canonicalSourceProp_of_collapsed_interval`: present=`True`, line=`81`

### Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16ScaledRemainderDirectHornerSourceBridge.lean

- `theorem of_collapsed_horner_range`: present=`True`, line=`43`
- `theorem valid_of_collapsed_horner_rows`: present=`True`, line=`95`

### Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16ActiveActualHornerSegmentCert.lean

- `Step33Sub0ActiveActualOrder16HornerSegmentCert`: present=`True`, line=`32`
- `structure Valid`: present=`True`, line=`52`
- `theorem to_activeActual_order16_segment_remainder`: present=`True`, line=`73`
- `theorem to_collapsed_segment_remainder`: present=`True`, line=`90`
- `primaryFiniteRow0Parent0Split100Sub0_activeActual_order16_segment_remainder_of_horner_cert`: present=`True`, line=`113`
- `primaryFiniteRow0Parent0Split100Sub0_collapsed_segment_remainder_of_activeActualHorner`: present=`True`, line=`129`

### Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16ScaledRemainderDirectConcretePayload.lean

- `primaryFiniteRow0Parent0Split100Sub0CombinedOrder16ScaledRemainderDirectHornerData`: present=`False`, line=`None`
- `primaryFiniteRow0Parent0Split100Sub0_combinedOrder16ScaledRemainderDirectHorner_valid`: present=`False`, line=`None`
- `primaryFiniteRow0Parent0Split100Sub0_combinedOrder16ScaledRemainder_nonzeroModel_interval_generated`: present=`False`, line=`None`
- `primaryFiniteRow0Parent0Split100Sub0_combinedOrder16ScaledRemainder_nonzeroModel_sourceProp_generated`: present=`False`, line=`None`

### Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16BudgetPayload.lean

- `primaryFiniteRow0Parent0Split100Sub0_combinedCancellation_order16Budget_remainder_width_fail`: present=`True`, line=`114`

## Do Not Reuse

- centered-Taylor factor majorants killed by exact budget
- P45/full-Taylor machinery: wrong target
- zero-model/direct-source budget
- independent product-summand norm bounds
- center jets as uniform full-cell intervals
- sampled/probe interval rows

## Guard

This generator must not write the Lean payload until the whole signed expression interval rows are proof-grade.  The current run is a fail-closed preflight, not Step33A.1-A closure.
