# Step33A.1-A Direct Scaled-Remainder Payload Ledger

schema: `q3_psdpd_step33_a1_sub0_combined_order16_scaled_remainder_direct_payload.v3`
route: `direct_nonzero_model_scaled_remainder_interval`
proofStatus: `direct_nonzero_model_row_worklist_emitted_missing_interval_cert`

## Status

- proofGrade: `False`
- directPayloadSurfacePresent: `True`
- zeroModelBridgePresent: `True`
- intervalPayloadSurfacePresent: `True`
- remainderBridgePresent: `True`
- p45FullTaylorBridgePresent: `True`
- order16NonzeroModelBridgePresent: `True`
- directIntervalPayloadPresent: `True`
- directModelPayloadPresent: `True`
- biasedSourceHornerPresent: `False`
- biasedSignedFactorAdapterPresent: `True`
- directNonzeroModelIntervalRowsLeanChecked: `False`
- directNonzeroModelSourcePropLeanChecked: `False`
- zeroModelPayloadTargetLeanChecked: `True`
- step33A1ClosedClaimed: `False`
- doNotSplitSummands: `True`
- rowWorklistEmitted: `True`
- rowWorklistFile: `ACTIVE/requests/step33_bootstrap/step33_a1_sub0_combined_order16_scaled_remainder_direct_row_obligations.json`
- firstMissingProofObject: `primaryFiniteRow0Parent0Split100Sub0_combinedOrder16ScaledRemainder_nonzeroModel_interval_generated`
- firstRowFailureCode: `STEP33_A1_SUB0_COMBINED_ORDER16_SCALED_REMAINDER_DIRECT_ROW_SOURCE_GAP`

## Current Gap

`STEP33_A1_SUB0_COMBINED_ORDER16_SCALED_REMAINDER_NONZERO_MODEL_INTERVAL_CERT_GAP`

Parent gap:

`STEP33_A1_SUB0_COMBINED_ORDER16_BIASED_RESIDUAL_HORNER_SCALED_REMAINDER_BOUND_GAP`

First failure code if the direct route fails:

`STEP33_A1_SUB0_COMBINED_ORDER16_SCALED_REMAINDER_NONZERO_MODEL_INTERVAL_CERT_GAP`

First row-source failure code if the row generator fails:

`STEP33_A1_SUB0_COMBINED_ORDER16_SCALED_REMAINDER_DIRECT_ROW_SOURCE_GAP`

P45/full-Taylor reuse verdict:

`not_spendable_for_order16_direct_source_bound`

P45/full-Taylor reuse failure code:

`STEP33_A1_SUB0_P45_FULL_TAYLOR_ORDER16_SOURCE_MISMATCH`

## Target

- expression: `primaryFiniteRow0Parent0Split100Sub0CombinedCancellationOrder16ComponentSource eta - primaryFiniteRow0Parent0Split100Sub0CombinedOrder16NonzeroModelPoly eta`
- budget: `primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedResidualRemainderAbs`
- prop: `primaryFiniteRow0Parent0Split100Sub0CombinedOrder16ScaledRemainderNonzeroModelSourceProp`
- payload: `primaryFiniteRow0Parent0Split100Sub0CombinedOrder16ScaledRemainderDirectPayloadTarget`
- first interval theorem: `primaryFiniteRow0Parent0Split100Sub0_combinedOrder16ScaledRemainder_nonzeroModel_interval_generated`
- first source-prop theorem: `primaryFiniteRow0Parent0Split100Sub0_combinedOrder16ScaledRemainder_nonzeroModel_sourceProp_generated`

## Route Review

- decision: `CHOSEN: A`
- question: Does the existing P45/full-Taylor interval machinery prove the order-16 ComponentSource - NonzeroModelPoly source bound, or is a separate direct certificate target still needed?
- answer: A: proceed with the direct rational/Horner interval generator; P45/full-Taylor bounds a different derivative-level expression and does not prove the uniform order-16 source-minus-nonzero-model interval.
- row worklist decision: `CHOSEN: A`
- row worklist answer: First patch should emit exact row obligations; an immediate Lean certificate would still be conditional without proof-grade whole-expression remainder source rows.

## Why P45/full-Taylor Is Not Enough

The P45/full-Taylor bridge rewrites a derivative-level residual error into the scaled cancellation RHS. The current direct target is the order-16 source residual ComponentSource - NonzeroModelPoly, which Lean identifies with ActiveScaleCoeff * D^16(ComponentProductCancellationResidual) plus the same-unit scale-mismatch nominal-product term. No local theorem converts the P45/full-Taylor interval into this order-16 source interval.

## Theorem Shape

prove a signed interval on [0,1/10] for ComponentSource - NonzeroModelPoly inside +/- BiasedResidualRemainderAbs; then use primaryFiniteRow0Parent0Split100Sub0_combinedOrder16ScaledRemainder_nonzeroModel_sourceProp_of_full_cell_interval or a direct family payload target

## Certificate Shape

- segment cells covering [0,1/10]
- whole signed expression polynomial/range rows
- whole-expression remainder rows
- per-segment lower/upper budget rows
- global residualAbs = BiasedResidualRemainderAbs

## Row Obligations

### R0_cell_cover

- `object`: `segment cells cover Set.Icc 0 (1/10)`
- `requiredFor`: `Step33Sub0CombinedOrder16ScaledRemainderDirectSegmentCover`
- `status`: `interface_ready_rows_missing`
- `proofGrade`: `False`

### R1_whole_signed_expression_range

- `object`: `primaryFiniteRow0Parent0Split100Sub0_combinedOrder16ScaledRemainder_nonzeroModel_interval_generated`
- `statement`: `for all eta in [0,1/10], -BiasedResidualRemainderAbs <= ComponentSource eta - NonzeroModelPoly eta and ComponentSource eta - NonzeroModelPoly eta <= BiasedResidualRemainderAbs`
- `status`: `missing_first_proof_object`
- `proofGrade`: `False`

### R2_horner_or_interval_rows

- `object`: `proof-grade rational/interval rows for the assembled signed expression`
- `requiredFor`: `primaryFiniteRow0Parent0Split100Sub0_combinedOrder16ScaledRemainder_nonzeroModel_interval_generated`
- `status`: `missing`
- `proofGrade`: `False`

### R3_budget_rows

- `object`: `lowerBudget and upperBudget against BiasedResidualRemainderAbs`
- `requiredFor`: `Step33Sub0CombinedOrder16ScaledRemainderDirectSegmentCert.Valid`
- `status`: `missing`
- `proofGrade`: `False`

### R4_source_prop_adapter

- `object`: `primaryFiniteRow0Parent0Split100Sub0_combinedOrder16ScaledRemainder_nonzeroModel_sourceProp_generated`
- `requiredFor`: `primaryFiniteRow0Parent0Split100Sub0CombinedOrder16ScaledRemainderNonzeroModelSourceProp`
- `status`: `interface_ready_depends_on_R1`
- `proofGrade`: `False`

### R5_zero_model_payload_target

- `object`: `primaryFiniteRow0Parent0Split100Sub0_biasedScaledRemainderZeroModel_payload_target_of_direct_payload`
- `requiredFor`: `biased residual-Horner zero-model handoff`
- `status`: `checked_bridge_depends_on_R4`
- `checkedBridge`: `True`
- `proofGrade`: `False`

## Candidate Reuse Routes

### p45_full_taylor

- `file`: `Q3/Proofs/PSD_CenteredCoeffRawOmegaAComponentTaylorCancellationNormReceiver.lean`
- `surfacePresent`: `True`
- `verdict`: `rejected_not_same_expression`
- `failureCode`: `STEP33_A1_SUB0_P45_FULL_TAYLOR_ORDER16_SOURCE_MISMATCH`

### direct_payload_surface

- `file`: `Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16ScaledRemainderDirectPayload.lean`
- `surfacePresent`: `True`
- `verdict`: `usable_interface_no_rows`
- `failureCode`: `STEP33_A1_SUB0_COMBINED_ORDER16_SCALED_REMAINDER_NONZERO_MODEL_INTERVAL_CERT_GAP`

### direct_interval_payload

- `file`: `Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16DirectIntervalPayload.lean`
- `surfacePresent`: `True`
- `verdict`: `old_source_interval_interface_not_scaled_nonzero_model_interval`
- `failureCode`: `STEP33_A1_SUB0_COMBINED_ORDER16_SCALED_REMAINDER_NONZERO_MODEL_INTERVAL_CERT_GAP`

### direct_model_payload

- `file`: `Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16DirectModelPayload.lean`
- `surfacePresent`: `True`
- `verdict`: `conditional_checker_only_hard_remainder_premise_is_current_gap`
- `failureCode`: `STEP33_A1_SUB0_COMBINED_ORDER16_SCALED_REMAINDER_NONZERO_MODEL_INTERVAL_CERT_GAP`

### biased_source_horner

- `file`: `Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16BiasedResidualSourceHornerCert.lean`
- `surfacePresent`: `False`
- `verdict`: `not_same_target_without_new_bridge`
- `failureCode`: `STEP33_A1_SUB0_COMBINED_ORDER16_SCALED_REMAINDER_NONZERO_MODEL_INTERVAL_CERT_GAP`

### biased_signed_factor_adapter

- `file`: `Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16BiasedResidualSignedFactorAdapter.lean`
- `surfacePresent`: `True`
- `verdict`: `adapter_for_biased_route_only_not_direct_nonzero_model_rows`
- `failureCode`: `STEP33_A1_SUB0_COMBINED_ORDER16_SCALED_REMAINDER_NONZERO_MODEL_INTERVAL_CERT_GAP`

## Source Availability Audit

### order16_nonzero_model_normal_forms

- `file`: `Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16NonzeroModel.lean`
- `artifactStatus`: `lean_surface_present`
- `sameTarget`: `True`
- `proofGradeRowsPresent`: `False`
- `spendableForCurrentTarget`: `False`
- `reason`: `Exact normal-form names exist for the current residual, but there is no generated signed interval theorem proving the whole expression inside BiasedResidualRemainderAbs.`
- `firstMissingProofObject`: `primaryFiniteRow0Parent0Split100Sub0_combinedOrder16ScaledRemainder_nonzeroModel_interval_generated`
- `failureCode`: `STEP33_A1_SUB0_COMBINED_ORDER16_SCALED_REMAINDER_DIRECT_ROW_SOURCE_GAP`

### direct_scaled_remainder_payload_surface

- `file`: `Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16ScaledRemainderDirectPayload.lean`
- `artifactStatus`: `lean_receiver_present`
- `sameTarget`: `True`
- `proofGradeRowsPresent`: `False`
- `spendableForCurrentTarget`: `False`
- `reason`: `The receiver can consume a proof-grade direct payload, but the segment rows and whole-expression range certificate are still missing.`
- `firstMissingProofObject`: `primaryFiniteRow0Parent0Split100Sub0_combinedOrder16ScaledRemainder_nonzeroModel_interval_generated`
- `failureCode`: `STEP33_A1_SUB0_COMBINED_ORDER16_SCALED_REMAINDER_NONZERO_MODEL_INTERVAL_CERT_GAP`

### combined_cancellation_order16_direct_zero_model_ledger

- `ledger`: `ACTIVE/requests/step33_bootstrap/step33_a1_sub0_combined_cancellation_order16_direct_payload.json`
- `artifactStatus`: `local_ledger_present`
- `sameTarget`: `False`
- `proofGradeRowsPresent`: `False`
- `spendableForCurrentTarget`: `False`
- `reason`: `This threshold zero-model route records a checked interface but is killed by the rawProduct17 centered-Taylor budget and does not bound ComponentSource - NonzeroModelPoly.`
- `blockingGap`: `STEP33_A1_SUB0_COMBINED_CANCELLATION_RAW_PRODUCT17_BUDGET_CONSTANT_FAIL`
- `failureCode`: `STEP33_A1_SUB0_COMBINED_CANCELLATION_RAW_PRODUCT17_BUDGET_CONSTANT_FAIL`

### combined_order16_source_interval_ledger

- `ledger`: `ACTIVE/requests/step33_bootstrap/step33_a1_sub0_combined_order16_source_interval.json`
- `artifactStatus`: `local_ledger_present`
- `sameTarget`: `False`
- `proofGradeRowsPresent`: `False`
- `spendableForCurrentTarget`: `False`
- `reason`: `This is a zero-model whole-source interval receiver; its current gap is signed-factor/source rows, not the nonzero model residual interval needed here.`
- `blockingGap`: `STEP33_A1_SUB0_COMBINED_CANCELLATION_DIRECT_ORDER16_SIGNED_FACTOR_ROWS_GAP`
- `failureCode`: `STEP33_A1_SUB0_COMBINED_CANCELLATION_DIRECT_ORDER16_SIGNED_FACTOR_ROWS_GAP`

### combined_order16_signed_factor_rows_ledger

- `ledger`: `ACTIVE/requests/step33_bootstrap/step33_a1_sub0_combined_order16_signed_factor_rows.json`
- `artifactStatus`: `local_ledger_present`
- `sameTarget`: `False`
- `proofGradeRowsPresent`: `False`
- `spendableForCurrentTarget`: `False`
- `reason`: `The signed Leibniz checker interface is alive, but the centered-Taylor abs-row route is budget-killed and does not supply the direct nonzero-model source interval.`
- `blockingGap`: `STEP33_A1_SUB0_COMBINED_CANCELLATION_DIRECT_ORDER16_TAYLOR_SOURCE_GAP`
- `failureCode`: `STEP33_A1_SUB0_CENTERED_TAYLOR_FACTOR_MAJORANT_ORDER16_BUDGET_CONSTANT_FAIL`

### p45_full_taylor_bridge

- `file`: `Q3/Proofs/PSD_CenteredCoeffRawOmegaAComponentTaylorCancellationNormReceiver.lean`
- `artifactStatus`: `lean_surface_present`
- `sameTarget`: `False`
- `proofGradeRowsPresent`: `True`
- `spendableForCurrentTarget`: `False`
- `reason`: `P45/full-Taylor controls a derivative-level residual error; no local theorem converts it to the order-16 ComponentSource - NonzeroModelPoly interval.`
- `failureCode`: `STEP33_A1_SUB0_P45_FULL_TAYLOR_ORDER16_SOURCE_MISMATCH`


## Direct Payload Symbols

- `Step33Sub0CombinedOrder16ScaledRemainderDirectSegmentCert`: `True`
- `Step33Sub0CombinedOrder16ScaledRemainderDirectSegmentCover`: `True`
- `Step33Sub0CombinedOrder16ScaledRemainderDirectFamilyCert`: `True`
- `primaryFiniteRow0Parent0Split100Sub0CombinedOrder16ScaledRemainderDirectPayloadTarget`: `True`
- `primaryFiniteRow0Parent0Split100Sub0_combinedOrder16ScaledRemainder_nonzeroModel_sourceProp_of_direct_payload`: `True`
- `primaryFiniteRow0Parent0Split100Sub0_biasedScaledRemainderZeroModel_payload_target_of_direct_payload`: `True`
- `primaryFiniteRow0Parent0Split100Sub0_combinedOrder16ScaledRemainder_nonzeroModel_sourceProp_of_full_cell_interval`: `True`

## Zero Model Symbols

- `primaryFiniteRow0Parent0Split100Sub0CombinedOrder16ScaledRemainderNonzeroModelSourceProp`: `True`
- `primaryFiniteRow0Parent0Split100Sub0_biasedScaledRemainder_eq_nonzeroModelResidual`: `True`
- `primaryFiniteRow0Parent0Split100Sub0_biasedScaledRemainderSourceProp_of_nonzeroModelResidual`: `True`
- `primaryFiniteRow0Parent0Split100Sub0_biasedScaledRemainderZeroModel_payload_target_of_nonzeroModelResidual`: `True`
- `primaryFiniteRow0Parent0Split100Sub0_biasedResidualHorner_residualRemainder_of_scaledRemainder_zeroModel`: `True`

## Interval Payload Symbols

- `Step33Sub0CombinedOrder16BiasedScaledRemainderIntervalSegmentCert`: `True`
- `Step33Sub0CombinedOrder16BiasedScaledRemainderIntervalFamilyCert`: `True`
- `primaryFiniteRow0Parent0Split100Sub0BiasedScaledRemainderIntervalPayloadTarget`: `True`

## Remainder Bridge Symbols

- `primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedResidualHornerScaledRemainder`: `True`
- `primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedResidualHornerScaledRemainderSourceProp`: `True`
- `primaryFiniteRow0Parent0Split100Sub0_biasedResidualHorner_residualRemainder_of_scaledRemainder_bound`: `True`

## P45/full-Taylor Bridge Symbols

- `primaryFiniteRow0Parent0Split100Sub0_fullTaylor_residual_deriv_error_eq_scaledCancellationRhs`: `True`
- `primaryFiniteRow0Parent0Split100Sub0_fullTaylor_residual_deriv_error_bound_of_scaledCancellationRhs_bound`: `True`
- `primaryFiniteRow0Parent0Split100Sub0_fullTaylor_cellSlopeExactIntegralProofData_of_checked_hRawCenterCoeffAbs_and_scaledCancellationRhs_bound`: `True`

## Order16 Nonzero-Model Symbols

- `primaryFiniteRow0Parent0Split100Sub0_combinedOrder16Source_sub_nonzeroModelPoly`: `True`
- `primaryFiniteRow0Parent0Split100Sub0_combinedOrder16Source_sub_nonzeroModelSource`: `True`

## Direct Interval Payload Symbols

- `primaryFiniteRow0Parent0Split100Sub0CombinedCancellationOrder16DirectIntervalTarget`: `True`
- `Step33Sub0CombinedCancellationOrder16DirectIntervalCert`: `True`
- `primaryFiniteRow0Parent0Split100Sub0_combinedCancellation_order16_direct_interval_to_source_field`: `True`

## Direct Model Payload Symbols

- `primaryFiniteRow0Parent0Split100Sub0CombinedOrder16DirectRemainderSourceProp`: `True`
- `primaryFiniteRow0Parent0Split100Sub0_combinedOrder16DirectInterval_valid_of_horner_remainder`: `True`
- `primaryFiniteRow0Parent0Split100Sub0CombinedOrder16DirectZeroModelRemainderSourceProp`: `True`

## Biased Source Horner Symbols

- `Step33Sub0CombinedOrder16BiasedResidualSourceHornerCert`: `True`
- `Step33Sub0CombinedOrder16BiasedResidualSourceHornerRangeCert`: `True`
- `primaryFiniteRow0Parent0Split100Sub0_combinedOrder16BiasedResidual_sourceProp_of_source_horner_family`: `False`

## Biased Signed-Factor Adapter Symbols

- `primaryFiniteRow0Parent0Split100Sub0_combinedOrder16BiasedResidual_sourceProp_of_signedFactor_segment_cover`: `True`
- `Step33Sub0CombinedOrder16BiasedResidualSignedFactorSegmentFamilyCert`: `True`

## Prior Ledgers

### biasedScaledRemainderInterval

- `path`: `ACTIVE/requests/step33_bootstrap/step33_a1_sub0_combined_order16_biased_scaled_remainder_interval.json`
- `exists`: `True`
- `proofStatus`: `biased_scaled_remainder_zero_model_checker_checked_missing_source_bound`
- `currentGap`: `STEP33_A1_SUB0_COMBINED_ORDER16_BIASED_RESIDUAL_HORNER_SCALED_REMAINDER_BOUND_GAP`
- `proofGrade`: `False`
- `nonzeroModelResidualBridgeLeanChecked`: `True`
- `nonzeroModelResidualSourceBoundLeanChecked`: `False`

### biasedResidualHornerPayload

- `path`: `ACTIVE/requests/step33_bootstrap/step33_a1_sub0_biased_residual_horner_payload.json`
- `exists`: `True`
- `proofStatus`: `biased_residual_horner_direct_nonzero_model_payload_checked_missing_interval_cert`
- `currentGap`: `STEP33_A1_SUB0_COMBINED_ORDER16_BIASED_RESIDUAL_HORNER_SCALED_REMAINDER_BOUND_GAP`
- `proofGrade`: `False`
- `scaledRemainderBoundLeanChecked`: `False`
- `nonzeroModelResidualBridgeLeanChecked`: `True`
- `nonzeroModelResidualSourceBoundLeanChecked`: `False`

## Guard

This is an interface and fail-closed ledger only.  It does not prove the interval rows, and it must not be treated as Step33A.1-A closure until the direct nonzero-model source proposition is Lean-checked or backed by proof-grade generated rows.
