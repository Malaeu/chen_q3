# Step33A.1-A ActiveActual Order-16 Horner Payload Gate

schema: `q3_psdpd_step33_a1_sub0_active_actual_order16_horner_payload.v10`
route: `active_actual_order16_horner_payload_smoke_segment`

## Verdict

- proofStatus: `blocked_missing_d16_center_d17_uniform_source`
- proofGrade: `False`
- proofSafeClosedFields: `1`
- interfaceReady: `True`
- outLeanWritten: `False`
- currentGap: `STEP33_A1_SUB0_ACTIVE_ACTUAL_ORDER16_SEGMENT_REMAINDER_ROW_SOURCE_GAP`
- firstFailureCode: `STEP33_A1_SUB0_ACTIVE_ACTUAL_ORDER16_SEGMENT_REMAINDER_ROW_SOURCE_GAP`
- firstConcreteSubgap: `STEP33_A1_SUB0_ACTIVE_ACTUAL_ORDER16_D16_CENTER_D17_UNIFORM_SOURCE_GAP`
- leanValidationStatus: `not_run_payload_not_emitted`

## Target Lean Surface

- `dataObject`: `primaryFiniteRow0Parent0Split100Sub0ActiveActualOrder16HornerSegment0`
- `validTheorem`: `primaryFiniteRow0Parent0Split100Sub0_activeActual_order16_segment0_valid`
- `remainderTheorem`: `primaryFiniteRow0Parent0Split100Sub0_activeActual_order16_segment0_remainder_generated`
- `degree0SourceTheorem`: `primaryFiniteRow0Parent0Split100Sub0_activeActual_order16_segment_remainder_of_degree0_source`
- `degree0ContDiff17SourceTheorem`: `primaryFiniteRow0Parent0Split100Sub0_activeActual_order16_segment_remainder_of_degree0_source_contDiff17`
- `degree0CheckedContDiff17SourceTheorem`: `primaryFiniteRow0Parent0Split100Sub0_activeActual_order16_segment_remainder_of_degree0_source_checked_contDiff17`
- `familyValidTarget`: `Step33Sub0ActiveActualOrder16HornerFamilyCert.Valid`
- `payloadTarget`: `primaryFiniteRow0Parent0Split100Sub0_directPayloadTarget_of_activeActualHornerFamily`

## Smoke Segment

- `cellL`: `0`
- `cellU`: `1/10`
- `center`: `1/20`
- `degree`: `29`
- `cell`: `Set.Icc 0 (1/10)`
- `payloadAllowed`: `False`
- `outLeanWritten`: `False`
- `degree29IsContainerOnly`: `True`

## Degree-0 Preflight

- `path`: `ACTIVE/requests/step33_bootstrap/step33_a1_sub0_active_actual_order16_degree0_payload.json`
- `markdown`: `ACTIVE/requests/step33_bootstrap/step33_a1_sub0_active_actual_order16_degree0_payload.md`
- `schema`: `q3_psdpd_step33_a1_sub0_active_actual_order16_degree0_payload.v5`
- `proofGrade`: `False`
- `budgetPassed`: `None`
- `firstFailure`: `STEP33_A1_SUB0_ACTIVE_ACTUAL_ORDER16_D16_CENTER_D17_UNIFORM_SOURCE_GAP`
- `receiverReady`: `True`
- `activeScaleAbs`: `95492965855137201461330258024/1000000000000000000000000000000`
- `activeScaleProofGrade`: `True`
- `rawProduct18BridgeReady`: `True`
- `rawProduct18MajorantReceiverReady`: `True`
- `rawProduct18UniformSourceChecked`: `True`
- `omegaPrimeOrder17AnalyticTsumSourceChecked`: `True`
- `omegaPrimeOrder17UniformSourceChecked`: `True`
- `omegaPrimeOrder17Abs`: `1024379792916537436656292891459584/152587890625`
- `realSincFin19DerivativeSourceChecked`: `True`
- `realSincOrder18DerivativeSourceChecked`: `True`
- `shapeSqOrder18UniformSourceChecked`: `True`

## Degree-29 Container Policy

- `targetFunction`: `activeScale * D^16(ComponentProductActual)`
- `containerDegree`: `29`
- `containerCoeffType`: `Fin 30 -> Rat`
- `lowDegreeAccepted`: `True`
- `lowDegreeBridge`: `Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16ActiveActualLowDegreeBridge.lean`
- `zeroExtendDef`: `primaryFiniteRow0Parent0Split100Sub0ActiveActualCoeffZeroExtend29`
- `transferTheorem`: `primaryFiniteRow0Parent0Split100Sub0_activeActual_order16_segment_remainder_of_lowDegree`
- `degree0SourceBridge`: `Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16ActiveActualDegree0Source.lean`
- `degree0SourceTheorem`: `primaryFiniteRow0Parent0Split100Sub0_activeActual_order16_segment_remainder_of_degree0_source`
- `degree0ContDiff17SourceTheorem`: `primaryFiniteRow0Parent0Split100Sub0_activeActual_order16_segment_remainder_of_degree0_source_contDiff17`
- `degree0CheckedContDiff17SourceTheorem`: `primaryFiniteRow0Parent0Split100Sub0_activeActual_order16_segment_remainder_of_degree0_source_checked_contDiff17`
- `firstConcreteSubgap`: `STEP33_A1_SUB0_ACTIVE_ACTUAL_ORDER16_D16_CENTER_D17_UNIFORM_SOURCE_GAP`
- `d17UniformRoute`: `{'selectedRoute': 'B_rawProduct18', 'bridgeSource': 'Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16ActiveActualRawProduct18Payload.lean', 'bridgeReady': True, 'majorantReceiverSource': 'Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16ActiveActualRawProduct18MajorantReceiver.lean', 'majorantReceiverReady': True, 'uniformSource': 'Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16ActiveActualRawProduct18Source.lean', 'uniformSourceReady': True, 'failureIfUniformSourceMissing': 'STEP33_A1_SUB0_ACTIVE_ACTUAL_ORDER16_RAW_PRODUCT18_UNIFORM_SOURCE_GAP', 'shapeSqOrder18Source': 'Q3/Proofs/PSD_CenteredCoeffRawOmegaAShapeSqOrder18Payload.lean', 'shapeSqOrder18SourceReady': True, 'omegaPrimeOrder17AnalyticSource': 'Q3/Proofs/PSD_CenteredCoeffRawOmegaAOmegaPrimeDerivativeOrder17Payload.lean', 'omegaPrimeOrder17AnalyticSourceReady': True, 'omegaPrimeOrder17RationalSource': 'Q3/Proofs/PSD_CenteredCoeffRawOmegaAOmegaPrimeDerivativeOrder17RationalPayload.lean', 'omegaPrimeOrder17RationalPayload': 'ACTIVE/requests/step33_bootstrap/step33_a1_sub0_omega_prime_order17_payload.json', 'omegaPrimeOrder17RationalSourceReady': True, 'omegaPrimeOrder17Abs': '1024379792916537436656292891459584/152587890625', 'remainingFactorSources': []}`
- `fullDegree29Specialization`: `{'coefficientJetOrdersNeeded': '16..45', 'uniformRemainderDerivativeOrderNeeded': 46, 'firstMissingSubgapIfChosen': 'STEP33_A1_SUB0_ACTIVE_ACTUAL_ORDER16_D46_UNIFORM_REMAINDER_SOURCE_GAP'}`

## Required Inputs

### S0_smoke_segment_domain

- `status`: `planned`
- `cellL`: `0`
- `cellU`: `1/10`
- `center`: `1/20`
- `degree`: `29`

### S1_low_degree_activeActual_row

- `status`: `missing`
- `required`: `Use the degree-0 source first: supply a Rat coeff0 for activeScale * D^16(ComponentProductActual) at center 1/20`
- `degreePolicy`: `low-degree row accepted via checked zero-extension into Fin30`
- `failureCode`: `STEP33_A1_SUB0_ACTIVE_ACTUAL_ORDER16_D16_CENTER_D17_UNIFORM_SOURCE_GAP`

### S2_low_degree_uniform_remainder

- `status`: `missing`
- `required`: `D16 center enclosure, D17 uniform bound, and exact rational budget`
- `analyticOrderForDegree0`: `D16 center plus D17 uniform derivative source`
- `failureCode`: `STEP33_A1_SUB0_ACTIVE_ACTUAL_ORDER16_D16_CENTER_D17_UNIFORM_SOURCE_GAP`

### S2a_degree0_source_interface

- `status`: `checked`
- `source`: `Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16ActiveActualDegree0Source.lean`
- `coeffDef`: `primaryFiniteRow0Parent0Split100Sub0ActiveActualDegree0Coeff`
- `componentProductActualContDiff17`: `primaryFiniteRow0Parent0Split100Sub0_componentProductActual_contDiff17`
- `theorem`: `primaryFiniteRow0Parent0Split100Sub0_activeActual_order16_segment_remainder_of_degree0_source_checked_contDiff17`
- `failureCode`: `STEP33_A1_SUB0_ACTIVE_ACTUAL_ORDER16_D16_CENTER_D17_UNIFORM_SOURCE_GAP`

### S2b_rawProduct18_d17_uniform_bridge

- `status`: `checked`
- `source`: `Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16ActiveActualRawProduct18Payload.lean`
- `equalityTheorem`: `primaryFiniteRow0Parent0Split100Sub0_componentProductActual_order17_eq_rawProduct18`
- `absTransferTheorem`: `primaryFiniteRow0Parent0Split100Sub0_componentProductActual_order17_abs_of_rawProduct18_abs`
- `requiredNextSource`: `proof-grade uniform D18(RawProductActual) bound`
- `failureCode`: `STEP33_A1_SUB0_ACTIVE_ACTUAL_ORDER16_RAW_PRODUCT18_UNIFORM_SOURCE_GAP`

### S2c_rawProduct18_factor_leibniz_receiver

- `status`: `checked`
- `source`: `Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16ActiveActualRawProduct18MajorantReceiver.lean`
- `majorantDef`: `primaryFiniteRow0Parent0Split100Sub0RawProductActualOrder18Majorant`
- `rawProductTheorem`: `primaryFiniteRow0Parent0Split100Sub0_rawProductActual_order18_abs_of_factor_derivative_abs`
- `componentTransferTheorem`: `primaryFiniteRow0Parent0Split100Sub0_componentProductActual_order17_abs_of_rawProduct18_factor_derivative_abs`
- `requiredNextSources`: `[]`
- `failureCode`: `STEP33_A1_SUB0_RAW_PRODUCT18_FACTOR_LEIBNIZ_RECEIVER_GAP`

### S2d_omegaPrime_order17_analytic_tsum_source

- `status`: `checked`
- `source`: `Q3/Proofs/PSD_CenteredCoeffRawOmegaAOmegaPrimeDerivativeOrder17Payload.lean`
- `theorem`: `Step33Sub0OmegaPrimeOrder17Payload.primaryFiniteRow0Parent0Split100Sub0_omegaPrime_iteratedDeriv17_norm_le_tsum`
- `requiredNextSource`: `rational/interval tail payload bounding the order-17 tsum majorant`
- `failureCode`: `STEP33_A1_SUB0_OMEGAPRIME_ORDER17_RATIONAL_TAIL_PAYLOAD_GAP`

### S2e_omegaPrime_order17_rational_uniform_source

- `status`: `checked`
- `source`: `Q3/Proofs/PSD_CenteredCoeffRawOmegaAOmegaPrimeDerivativeOrder17RationalPayload.lean`
- `payload`: `ACTIVE/requests/step33_bootstrap/step33_a1_sub0_omega_prime_order17_payload.json`
- `theorem`: `Step33Sub0OmegaPrimeOrder17Payload.primaryFiniteRow0Parent0Split100Sub0_omegaPrime_iteratedDeriv17_norm_le_generated`
- `order17Abs`: `1024379792916537436656292891459584/152587890625`
- `requiredNextSource`: `RawProduct18 rational majorant assembly and degree-0 budget`
- `failureCode`: `STEP33_A1_SUB0_OMEGAPRIME_ORDER17_RATIONAL_TAIL_PAYLOAD_GAP`

### S2f_rawProduct18_uniform_source

- `status`: `checked`
- `source`: `Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16ActiveActualRawProduct18Source.lean`
- `rawProductTheorem`: `primaryFiniteRow0Parent0Split100Sub0_rawProductActual_order18_abs_generated`
- `componentTransferTheorem`: `primaryFiniteRow0Parent0Split100Sub0_componentProductActual_order17_abs_generated`
- `requiredNextSource`: `exact Rat scalar export for RawProductActualOrder18MajorantGenerated before the degree-0 budget formula can be checked`
- `failureCode`: `STEP33_A1_SUB0_RAW_PRODUCT18_FACTOR_ARRAY_ASSEMBLY_GAP`

### S3_zero_extend_low_degree_to_Fin30

- `status`: `checked`
- `source`: `Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16ActiveActualLowDegreeBridge.lean`
- `def`: `primaryFiniteRow0Parent0Split100Sub0ActiveActualCoeffZeroExtend29`
- `theorem`: `primaryFiniteRow0Parent0Split100Sub0_activeActual_order16_segment_remainder_of_lowDegree`
- `failureCode`: `STEP33_A1_SUB0_ACTIVE_ACTUAL_ORDER16_LOW_DEGREE_TO_FIN30_ALIGNMENT_GAP`

### S4_horner_range_rows

- `status`: `blocked_on_low_degree_source`
- `required`: `stageLower/stageUpper rows for the converted direct segment`
- `failureCode`: `STEP33_A1_SUB0_ACTIVE_ACTUAL_ORDER16_SEGMENT_REMAINDER_ROW_SOURCE_GAP`

### S5_budget_rows

- `status`: `blocked_on_low_degree_source`
- `required`: `polyLower/polyUpper/lower/upper/residualAbs rows`
- `failureCode`: `STEP33_A1_SUB0_ACTIVE_ACTUAL_ORDER16_SEGMENT_REMAINDER_ROW_SOURCE_GAP`

## Validation Gates

- `segmentReceiverReady`: `True`
- `familyBridgeReady`: `True`
- `lowDegreeBridgeReady`: `True`
- `degree0SourceInterfaceReady`: `True`
- `rawProduct18BridgeReady`: `True`
- `rawProduct18MajorantReceiverReady`: `True`
- `rawProduct18UniformSourceChecked`: `True`
- `omegaPrimeOrder17AnalyticTsumSourceChecked`: `True`
- `omegaPrimeOrder17UniformSourceChecked`: `True`
- `omegaPrimeOrder17RationalPayloadChecked`: `True`
- `realSincFin19DerivativeSourceChecked`: `True`
- `realSincOrder18DerivativeSourceChecked`: `True`
- `shapeSqOrder18UniformSourceChecked`: `True`
- `degree0PreflightWritten`: `True`
- `degree0BudgetPassed`: `None`
- `activeScaleBoundChecked`: `True`
- `activeActualLowDegreeSegmentRemainderSourceChecked`: `False`
- `activeActualD16CenterD17UniformSourceChecked`: `False`
- `activeActualD46UniformRemainderSourceChecked`: `False`
- `activeActualCoeffOrders16To45Checked`: `False`
- `smokeSegmentValidChecked`: `False`
- `hornerRangeRowsChecked`: `False`
- `budgetRowsChecked`: `False`
- `allPayloadObligationsPassed`: `False`

## Available Upstream Evidence

### activeActualCenterJetRows

- `path`: `Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationActiveActualCenterJetRowsPayload.lean`
- `exists`: `True`
- `hasFin16Rows`: `True`
- `hasActiveActualCenterRowInterval`: `True`
- `proofGradeForCenterJetsOnly`: `True`
- `availableOrders`: `0..15`
- `neededForFullDegree29Only`: `{'coefficientOrders': '16..45', 'remainderOrder': 46, 'firstSubgapIfFullDegree29IsUsed': 'STEP33_A1_SUB0_ACTIVE_ACTUAL_ORDER16_D46_UNIFORM_REMAINDER_SOURCE_GAP'}`
- `usableAsLowDegreeCoefficientSeedOnly`: `True`
- `usableForSmokeSegmentRemainder`: `False`

## Row Source Ledger

- `path`: `ACTIVE/requests/step33_bootstrap/step33_a1_sub0_active_actual_horner_row_source.json`
- `schema`: `q3_psdpd_step33_a1_sub0_active_actual_horner_row_source.v6`
- `proofStatus`: `interface_ready_rows_missing`
- `proofGrade`: `False`
- `firstFailureCode`: `STEP33_A1_SUB0_ACTIVE_ACTUAL_ORDER16_SEGMENT_REMAINDER_ROW_SOURCE_GAP`

## Computer Use Decision

- `used`: `True`
- `advisoryOnly`: `True`
- `recommendedOption`: `A`
- `firstFileToEdit`: `scripts/generate_step33_a1_sub0_active_actual_order16_horner_payload.py`
- `exactOutputObject`: `ACTIVE/requests/step33_bootstrap/step33_a1_sub0_active_actual_order16_degree0_payload.json`
- `decision`: `Add a fail-closed degree-0 preflight for the checked Degree0Source receiver before D18, higher degree, D46, or Lean payload emission.`
- `budgetFailureCode`: `STEP33_A1_SUB0_ACTIVE_ACTUAL_ORDER16_DEGREE0_REMAINDER_BUDGET_CONSTANT_FAIL`
- `d17SourceFailureCode`: `STEP33_A1_SUB0_ACTIVE_ACTUAL_ORDER16_D17_UNIFORM_SOURCE_GAP`
- `rawProduct18UniformSourceFailureCode`: `STEP33_A1_SUB0_ACTIVE_ACTUAL_ORDER16_RAW_PRODUCT18_UNIFORM_SOURCE_GAP`
- `notProofEvidence`: `True`

## Computer Use RawProduct18 Decision

- `used`: `True`
- `advisoryOnly`: `True`
- `recommendedOption`: `B`
- `firstFileToEdit`: `Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16ActiveActualRawProduct18Payload.lean`
- `bridgeTheorem`: `primaryFiniteRow0Parent0Split100Sub0_componentProductActual_order17_eq_rawProduct18`
- `uniformSourceFailureCode`: `STEP33_A1_SUB0_ACTIVE_ACTUAL_ORDER16_RAW_PRODUCT18_UNIFORM_SOURCE_GAP`
- `budgetFailureCode`: `STEP33_A1_SUB0_ACTIVE_ACTUAL_ORDER16_DEGREE0_REMAINDER_BUDGET_CONSTANT_FAIL`
- `notProofEvidence`: `True`

## Computer Use RawProduct18 Receiver Decision

- `used`: `True`
- `advisoryOnly`: `True`
- `recommendedOption`: `A`
- `firstFileToEdit`: `Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16ActiveActualRawProduct18MajorantReceiver.lean`
- `firstTheorem`: `primaryFiniteRow0Parent0Split100Sub0_rawProductActual_order18_abs_of_factor_derivative_abs`
- `receiverFailureCode`: `STEP33_A1_SUB0_RAW_PRODUCT18_FACTOR_LEIBNIZ_RECEIVER_GAP`
- `omegaPrimeOrder17SourceFailureCode`: `STEP33_A1_SUB0_OMEGAPRIME_ORDER17_UNIFORM_SOURCE_GAP`
- `omegaPrimeOrder17RationalTailFailureCode`: `STEP33_A1_SUB0_OMEGAPRIME_ORDER17_RATIONAL_TAIL_PAYLOAD_GAP`
- `shapeSqOrder18SourceFailureCode`: `STEP33_A1_SUB0_SHAPESQ_ORDER18_UNIFORM_SOURCE_GAP`
- `notProofEvidence`: `True`

## Computer Use OmegaPrime Order17 Decision

- `used`: `True`
- `advisoryOnly`: `True`
- `recommendedOption`: `A`
- `firstFileToEdit`: `Q3/Proofs/PSD_CenteredCoeffRawOmegaAOmegaPrimeDerivativeOrder17Payload.lean`
- `firstTheorem`: `Step33Sub0OmegaPrimeOrder17Payload.primaryFiniteRow0Parent0Split100Sub0_omegaPrime_iteratedDeriv17_norm_le_tsum`
- `analyticTsumSourceChecked`: `True`
- `remainingFailureCode`: `STEP33_A1_SUB0_OMEGAPRIME_ORDER17_RATIONAL_TAIL_PAYLOAD_GAP`
- `notProofEvidence`: `True`

## Computer Use OmegaPrime Order17 Rational Decision

- `used`: `True`
- `advisoryOnly`: `True`
- `recommendedOption`: `A`
- `firstFileToEdit`: `Q3/Proofs/PSD_CenteredCoeffRawOmegaAOmegaPrimeDerivativeOrder17RationalPayload.lean`
- `generator`: `scripts/generate_step33_a1_sub0_omega_prime_order17_payload.py`
- `theorem`: `Step33Sub0OmegaPrimeOrder17Payload.primaryFiniteRow0Parent0Split100Sub0_omegaPrime_iteratedDeriv17_norm_le_generated`
- `rationalPayloadChecked`: `True`
- `order17Abs`: `1024379792916537436656292891459584/152587890625`
- `remainingFailureCode`: `STEP33_A1_SUB0_ACTIVE_ACTUAL_ORDER16_RAW_PRODUCT18_UNIFORM_SOURCE_GAP`
- `notProofEvidence`: `True`

## Computer Use RawProduct18 Source Decision

- `used`: `True`
- `advisoryOnly`: `True`
- `recommendedOption`: `A`
- `firstFileToEdit`: `Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16ActiveActualRawProduct18Source.lean`
- `firstTheorem`: `primaryFiniteRow0Parent0Split100Sub0_omegaActual_iteratedDeriv18_eq_omegaPrime17`
- `rawProductTheorem`: `primaryFiniteRow0Parent0Split100Sub0_rawProductActual_order18_abs_generated`
- `componentTransferTheorem`: `primaryFiniteRow0Parent0Split100Sub0_componentProductActual_order17_abs_generated`
- `sourceChecked`: `True`
- `remainingFailureCode`: `STEP33_A1_SUB0_RAW_PRODUCT18_FACTOR_ARRAY_ASSEMBLY_GAP`
- `budgetFailureCode`: `STEP33_A1_SUB0_ACTIVE_ACTUAL_ORDER16_DEGREE0_REMAINDER_BUDGET_CONSTANT_FAIL`
- `notProofEvidence`: `True`

## Computer Use ShapeSq Order18 Decision

- `used`: `True`
- `advisoryOnly`: `True`
- `recommendedOption`: `B`
- `firstFileToEdit`: `Q3/Proofs/PSD_CenteredCoeffRawOmegaARealSincDerivativeOrder18Payload.lean`
- `firstTheorem`: `primaryFiniteRow0Parent0Split100Sub0_realSinc_iteratedDeriv18_norm_le_two`
- `secondFile`: `Q3/Proofs/PSD_CenteredCoeffRawOmegaAShapeSqOrder18Payload.lean`
- `shapeSqThrough18Theorem`: `primaryFiniteRow0Parent0Split100Sub0_shapeSqActual_derivative_abs_of_sharp18`
- `internalSupportFile`: `Q3/Proofs/PSD_CenteredCoeffRawOmegaARealSincDerivativeCert19.lean`
- `failureCode`: `STEP33_A1_SUB0_SHAPESQ_ORDER18_UNIFORM_SOURCE_GAP`
- `notProofEvidence`: `True`

## Do Not Use As Proof

- sampled activeActual rows
- center-jet rows as uniform segment remainder rows
- coarse P45/factor-majorant route
- separate activeActual and nominal error budgets
- Lean payload file before S1/S2 proof-grade inputs exist
- D46 backend as mandatory before the low-degree source is tested

## Next Implementable Patch

Export an exact Rat scalar mirror for RawProductActualOrder18MajorantGenerated, then combine it with the D16 center enclosure, coeffErrorAbs, and polyErrorAbs in the degree-0 budget comparison before emitting any Lean payload.
