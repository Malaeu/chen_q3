# Step33A.1-A Active-Actual Horner Row-Source Ledger

schema: `q3_psdpd_step33_a1_sub0_active_actual_horner_row_source.v1`
route: `active_actual_order16_horner_row_source`
proofStatus: `interface_ready_rows_missing`

## Verdict

- proofGrade: `False`
- proofSafeClosedFields: `0`
- interfaceClosedFields: `5`
- outLeanWritten: `False`
- leanValidationStatus: `not_run_rows_missing`
- currentGap: `STEP33_A1_SUB0_ACTIVE_ACTUAL_ORDER16_SEGMENT_REMAINDER_ROW_SOURCE_GAP`
- firstFailureCode: `STEP33_A1_SUB0_ACTIVE_ACTUAL_ORDER16_SEGMENT_REMAINDER_ROW_SOURCE_GAP`

## Target Lean Surface

- `segmentDataObject`: `Step33Sub0ActiveActualOrder16HornerSegmentCert`
- `segmentValidPredicate`: `Step33Sub0ActiveActualOrder16HornerSegmentCert.Valid`
- `segmentReceiverTheorem`: `primaryFiniteRow0Parent0Split100Sub0_activeActual_order16_segment_remainder_of_horner_cert`
- `collapsedReceiverTheorem`: `primaryFiniteRow0Parent0Split100Sub0_collapsed_segment_remainder_of_activeActualHorner`
- `familyDataObject`: `Step33Sub0ActiveActualOrder16HornerFamilyCert`
- `familyValidPredicate`: `Step33Sub0ActiveActualOrder16HornerFamilyCert.Valid`
- `familyBridgeTheorem`: `primaryFiniteRow0Parent0Split100Sub0_directHornerFamily_valid_of_activeActualHornerFamily`
- `payloadTargetTheorem`: `primaryFiniteRow0Parent0Split100Sub0_directPayloadTarget_of_activeActualHornerFamily`
- `sourcePropTheorem`: `primaryFiniteRow0Parent0Split100Sub0_nonzeroModelSourceProp_of_activeActualHornerFamily`
- `targetBudgetConstant`: `primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedResidualRemainderAbs`
- `futureLeanPayloadFileWhenRowsPass`: `Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16ActiveActualHornerConcretePayload.lean`

## Row Data Contract

### familyFields

- n
- residualAbs
- seg
- range

### segmentFields

- cellL
- cellU
- coeff : Fin 30 -> Rat
- polyErrorAbs
- polyLower
- polyUpper
- lower
- upper
- residualAbs

### rangeFields

- stageLower : Fin (degree + 1) -> Rat
- stageUpper : Fin (degree + 1) -> Rat

### segmentValidFields

- cellSubset
- polyErrorNonneg
- remainderBound for activeScale * D^16(ComponentProductActual)

### familyValidFields

- activeValid
- rangeValid
- intervalLowerBudget
- intervalUpperBudget
- segmentResidualNonneg
- segmentLowerBudget
- segmentUpperBudget
- segmentBudget
- cover

- `center`: `1/20`
- `degree`: `29`
- `cell`: `Set.Icc 0 (1/10)`

## Required Rows

### A0_segment_cover

- `object`: `cover of Set.Icc 0 (1/10)`
- `leanField`: `Step33Sub0CombinedOrder16ScaledRemainderDirectHornerSegmentCover`
- `status`: `missing`
- `failureCode`: `STEP33_A1_SUB0_ACTIVE_ACTUAL_ORDER16_HORNER_COVER_ROWS_GAP`

### A1_active_actual_coefficients

- `object`: `proof-grade coeff : Fin 30 -> Rat for scaled activeActual`
- `leanField`: `Step33Sub0ActiveActualOrder16HornerSegmentCert.coeff`
- `status`: `missing`
- `failureCode`: `STEP33_A1_SUB0_ACTIVE_ACTUAL_ORDER16_HORNER_COEFF_ROWS_GAP`

### A2_active_actual_remainder

- `object`: `uniform activeActual order-16 segment remainder bound`
- `leanField`: `Step33Sub0ActiveActualOrder16HornerSegmentCert.Valid.remainderBound`
- `status`: `missing`
- `failureCode`: `STEP33_A1_SUB0_ACTIVE_ACTUAL_ORDER16_HORNER_REMAINDER_ROWS_GAP`

### A3_horner_range

- `object`: `stageLower/stageUpper Horner bounds`
- `leanField`: `Step33Sub0ActiveActualOrder16HornerDirectRangeCert.Valid`
- `status`: `missing`
- `failureCode`: `STEP33_A1_SUB0_ACTIVE_ACTUAL_ORDER16_HORNER_RANGE_ROWS_GAP`

### A4_interval_budget

- `object`: `polyLower/polyUpper/lower/upper interval budget rows`
- `leanField`: `intervalLowerBudget and intervalUpperBudget`
- `status`: `missing`
- `failureCode`: `STEP33_A1_SUB0_ACTIVE_ACTUAL_ORDER16_HORNER_INTERVAL_BUDGET_ROWS_GAP`

### A5_final_budget

- `object`: `segment residualAbs <= family residualAbs and residualAbs equals target budget`
- `leanField`: `segmentBudget plus hResidualAbs`
- `status`: `missing`
- `failureCode`: `STEP33_A1_SUB0_ACTIVE_ACTUAL_ORDER16_HORNER_FINAL_BUDGET_ROWS_GAP`

## Validation Gates

- `interfaceReady`: `True`
- `segmentReceiverLeanChecked`: `True`
- `familyBridgeLeanChecked`: `True`
- `directHornerReceiverLeanChecked`: `True`
- `collapsedSourceBridgeLeanChecked`: `True`
- `allSegmentsProvided`: `False`
- `allCoefficientRowsRational`: `False`
- `activeActualRemainderRowsChecked`: `False`
- `hornerRangeRowsChecked`: `False`
- `intervalBudgetRowsChecked`: `False`
- `segmentCoverChecked`: `False`
- `finalResidualBudgetRowsChecked`: `False`
- `residualAbsEqualityChecked`: `False`
- `exactRationalArithmeticPassed`: `False`
- `allPayloadObligationsPassed`: `False`
- `directPayloadTargetChecked`: `False`
- `outLeanWritten`: `False`
- `leanValidationStatus`: `not_run_rows_missing`

## Failure Priority

- `STEP33_A1_SUB0_ACTIVE_ACTUAL_ORDER16_HORNER_ROW_SOURCE_STALE_RECEIVER_SCHEMA_FAIL`
- `STEP33_A1_SUB0_ACTIVE_ACTUAL_ORDER16_HORNER_SEGMENT_RECEIVER_GAP`
- `STEP33_A1_SUB0_ACTIVE_ACTUAL_ORDER16_HORNER_FAMILY_ALIGNMENT_GAP`
- `STEP33_A1_SUB0_ACTIVE_ACTUAL_ORDER16_SEGMENT_REMAINDER_ROW_SOURCE_GAP`
- `STEP33_A1_SUB0_ACTIVE_ACTUAL_ORDER16_HORNER_COEFF_ROWS_GAP`
- `STEP33_A1_SUB0_ACTIVE_ACTUAL_ORDER16_HORNER_REMAINDER_ROWS_GAP`
- `STEP33_A1_SUB0_ACTIVE_ACTUAL_ORDER16_HORNER_RANGE_ROWS_GAP`
- `STEP33_A1_SUB0_ACTIVE_ACTUAL_ORDER16_HORNER_INTERVAL_BUDGET_ROWS_GAP`
- `STEP33_A1_SUB0_ACTIVE_ACTUAL_ORDER16_HORNER_COVER_ROWS_GAP`
- `STEP33_A1_SUB0_ACTIVE_ACTUAL_ORDER16_HORNER_FINAL_BUDGET_ROWS_GAP`
- `STEP33_A1_SUB0_ACTIVE_ACTUAL_ORDER16_HORNER_LEAN_PAYLOAD_VALIDATION_GAP`

## Symbol Audit

### Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16ActiveActualHornerSegmentCert.lean

- `Step33Sub0ActiveActualOrder16HornerSegmentCert`: present=`True`, line=`32`
- `structure Valid`: present=`True`, line=`52`
- `cellSubset`: present=`True`, line=`55`
- `polyErrorNonneg`: present=`True`, line=`58`
- `remainderBound`: present=`True`, line=`49`
- `theorem to_activeActual_order16_segment_remainder`: present=`True`, line=`73`
- `theorem to_collapsed_segment_remainder`: present=`True`, line=`90`
- `primaryFiniteRow0Parent0Split100Sub0_activeActual_order16_segment_remainder_of_horner_cert`: present=`True`, line=`113`
- `primaryFiniteRow0Parent0Split100Sub0_collapsed_segment_remainder_of_activeActualHorner`: present=`True`, line=`129`

### Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16ActiveActualHornerFamilyBridge.lean

- `Step33Sub0ActiveActualOrder16HornerDirectSegmentCert`: present=`True`, line=`37`
- `Step33Sub0ActiveActualOrder16HornerDirectRangeCert`: present=`True`, line=`83`
- `Step33Sub0ActiveActualOrder16HornerFamilyCert`: present=`True`, line=`109`
- `structure Valid`: present=`True`, line=`135`
- `activeValid`: present=`True`, line=`138`
- `rangeValid`: present=`True`, line=`140`
- `intervalLowerBudget`: present=`True`, line=`142`
- `intervalUpperBudget`: present=`True`, line=`147`
- `segmentResidualNonneg`: present=`True`, line=`152`
- `segmentLowerBudget`: present=`True`, line=`155`
- `segmentUpperBudget`: present=`True`, line=`159`
- `segmentBudget`: present=`True`, line=`163`
- `cover`: present=`True`, line=`14`
- `theorem to_directHornerFamilyValid`: present=`True`, line=`177`
- `primaryFiniteRow0Parent0Split100Sub0_directHornerFamily_valid_of_activeActualHornerFamily`: present=`True`, line=`254`
- `primaryFiniteRow0Parent0Split100Sub0_directPayloadTarget_of_activeActualHornerFamily`: present=`True`, line=`265`
- `primaryFiniteRow0Parent0Split100Sub0_nonzeroModelSourceProp_of_activeActualHornerFamily`: present=`True`, line=`280`

### Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16ScaledRemainderDirectHornerCert.lean

- `Step33Sub0CombinedOrder16ScaledRemainderDirectHornerCert`: present=`True`, line=`38`
- `Step33Sub0CombinedOrder16ScaledRemainderDirectHornerRangeCert`: present=`True`, line=`191`
- `Step33Sub0CombinedOrder16ScaledRemainderDirectHornerFamilyCert`: present=`True`, line=`311`
- `Step33Sub0CombinedOrder16ScaledRemainderDirectHornerSegmentCover`: present=`True`, line=`302`
- `structure Valid`: present=`True`, line=`70`
- `theorem to_directPayloadTarget`: present=`True`, line=`408`
- `theorem to_nonzeroModelSourceProp`: present=`True`, line=`418`

### Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16ScaledRemainderDirectHornerSourceBridge.lean

- `primaryFiniteRow0Parent0Split100Sub0CombinedOrder16ScaledRemainderCollapsedExpression`: present=`True`, line=`52`
- `primaryFiniteRow0Parent0Split100Sub0_combinedOrder16ScaledRemainder_eq_collapsedExpression`: present=`True`, line=`80`
- `theorem of_collapsed_horner_range`: present=`True`, line=`43`
- `theorem valid_of_collapsed_horner_rows`: present=`True`, line=`95`

## Source File Digests

- `Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16ActiveActualHornerSegmentCert.lean`: `26bc3873205b8196731bdb86015318d8457f4a51d1b76e9675e174ffd6c19238`
- `Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16ActiveActualHornerFamilyBridge.lean`: `7779f7ada25fa2422977eacae90788724294a965944e50d0d69c37d9fd314676`
- `Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16ScaledRemainderDirectHornerCert.lean`: `3f3d6cf5e0d217ab8177fbc121fc1272740914c7b9beb210db3cef993d55936b`
- `Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16ScaledRemainderDirectHornerSourceBridge.lean`: `e78af17bb313fec8e155d2e0dab906b3ed2c53c2c44e0c9c413ef1afde94e6f3`

## Direct Ledger Inputs

### directPayload

- `path`: `ACTIVE/requests/step33_bootstrap/step33_a1_sub0_combined_order16_scaled_remainder_direct_payload.json`
- `exists`: `True`
- `schema`: `q3_psdpd_step33_a1_sub0_combined_order16_scaled_remainder_direct_payload.v18`
- `proofGrade`: `False`
- `currentGap`: `STEP33_A1_SUB0_COMBINED_ORDER16_SCALED_REMAINDER_NONZERO_MODEL_INTERVAL_CERT_GAP`
- `firstConcreteUpstreamFailureCode`: `STEP33_A1_SUB0_ACTIVE_ACTUAL_ORDER16_SEGMENT_REMAINDER_ROW_SOURCE_GAP`
- `firstFailureCode`: `STEP33_A1_SUB0_COMBINED_ORDER16_SCALED_REMAINDER_NONZERO_MODEL_INTERVAL_CERT_GAP`

### directCertificate

- `path`: `ACTIVE/requests/step33_bootstrap/step33_a1_sub0_combined_order16_scaled_remainder_direct_certificate.json`
- `exists`: `True`
- `schema`: `q3_psdpd_step33_a1_sub0_combined_order16_scaled_remainder_direct_certificate.v12`
- `proofGrade`: `False`
- `currentGap`: `STEP33_A1_SUB0_COMBINED_ORDER16_SCALED_REMAINDER_NONZERO_MODEL_INTERVAL_CERT_GAP`
- `firstConcreteUpstreamFailureCode`: `STEP33_A1_SUB0_ACTIVE_ACTUAL_ORDER16_SEGMENT_REMAINDER_ROW_SOURCE_GAP`
- `firstFailureCode`: `STEP33_A1_SUB0_COMBINED_ORDER16_SCALED_REMAINDER_DIRECT_ROW_SOURCE_GAP`

## Computer Use Decision

- used: `True`
- advisoryOnly: `True`
- recommendedOption: `A`
- decision: Synchronize a fail-closed activeActual Horner row-source generator with the checked receiver before emitting any Lean payload.
- notProofEvidence: `True`

## Do Not Use As Proof

- sampled or float rows
- activeActual center jets as uniform segment bounds
- killed factor-majorant budgets
- P45/full-Taylor wrong-target rows
- separate activeActual and nominal independent norm budgets
- DirectConcretePayload.lean before this ledger has all payload obligations passed

## Next Implementable Patch

Fill this row-source contract with rational/interval segment rows, then emit an isolated Lean payload proving Step33Sub0ActiveActualOrder16HornerFamilyCert.Valid.
