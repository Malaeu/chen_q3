# Step33A.1-A Sub0 Combined Cancellation Interval Certificate

Fail-closed certificate ledger.  This is not Lean proof data and does
not close Step33A.1-A.

## Summary

- schema: `q3_psdpd_step33_a1_sub0_combined_cancellation_interval_certificate.v11`
- route: `STEP33_A1_SUB0_COMBINED_CANCELLATION_HIGH_ORDER_TAYLOR`
- status: `fail_closed_missing_high_order_valid_payload`
- first failure: `STEP33_A1_SUB0_COMBINED_CANCELLATION_HIGH_ORDER_VALID_PAYLOAD_GAP`
- target lower: `-94119513411/500000000000000000000000000000`
- target upper: `1866608532757/500000000000000000000000000000`
- target width: `245091005771/62500000000000000000000000000`

## Lean Surface

- file: `Q3/Proofs/PSD_CenteredCoeffRawOmegaAComponentTaylorCancellationCombinedInterval.lean`
- certCheckerFile: `Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationIntervalCert.lean`
- conditionalPayloadFile: `Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationIntervalPayload.lean`
- highOrderSourceFile: `Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationHighOrderTaylorSource.lean`
- sourceModelBridgeFile: `Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationSourceModelBridge.lean`
- sourceModelOrder16Source: `primaryFiniteRow0Parent0Split100Sub0CombinedCancellationOrder16ComponentSource`
- sourceModelOrder16Theorem: `primaryFiniteRow0Parent0Split100Sub0_combinedCancellation_order16_eq_componentSource`
- sourceModelOrder16BoundAdapter: `primaryFiniteRow0Parent0Split100Sub0_combinedCancellation_order16_bound_of_componentSource`
- sourceModelCenterJetBoundsAdapter: `primaryFiniteRow0Parent0Split100Sub0_combinedCancellation_centerJet_bounds_of_componentSource`
- sourceModelHighOrderValidConstructor: `primaryFiniteRow0Parent0Split100Sub0_combinedCancellation_highOrderValid_of_componentSource_bounds`
- sourceModelHighOrderIntervalConstructor: `primaryFiniteRow0Parent0Split100Sub0_combinedCancellation_highOrderValid_of_componentSource_interval`
- sourceIntervalCertFile: `Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationSourceIntervalCert.lean`
- sourceIntervalCertStructure: `Step33Sub0CombinedCancellationSourceIntervalCert`
- sourceIntervalCertValidPredicate: `Step33Sub0CombinedCancellationSourceIntervalCert.Valid`
- sourceIntervalCertToHighOrderValid: `Step33Sub0CombinedCancellationSourceIntervalCert.Valid.to_highOrderValid`
- sourceIntervalCertToHCombined: `Step33Sub0CombinedCancellationSourceIntervalCert.Valid.to_hCombined`
- sourceIntervalCertToResidualInterval: `Step33Sub0CombinedCancellationSourceIntervalCert.Valid.to_fullTaylor_residual_deriv_interval`
- sourceNormalFormFile: `Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationSourceNormalForm.lean`
- sourceNormalFormCancellationCauchy: `primaryFiniteRow0Parent0Split100Sub0_cancellationResidualCauchy_eq_actual_sub_nominal`
- sourceNormalFormConditionalCenterJet: `primaryFiniteRow0Parent0Split100Sub0_combinedCancellation_centerJet_eq_activeActual_sub_model_of_residualJet`
- sourceNormalFormResidualJetBridge: `primaryFiniteRow0Parent0Split100Sub0_residualTaylor_centerJet_low_eq_nominalProduct_sub_model`
- sourceNormalFormNonconditionalCenterJet: `primaryFiniteRow0Parent0Split100Sub0_combinedCancellation_centerJet_eq_activeActual_sub_model`
- sourceNormalFormActiveActualInterval: `primaryFiniteRow0Parent0Split100Sub0_combinedCancellation_sourceCenterInterval_of_activeActual_interval`
- sourceNormalFormActiveActualValidConstructor: `primaryFiniteRow0Parent0Split100Sub0_combinedCancellation_highOrderValid_of_activeActual_interval`
- certStructure: `Step33Sub0CombinedCancellationIntervalCert`
- certValidPredicate: `Step33Sub0CombinedCancellationIntervalCert.Valid`
- certToHCombined: `Step33Sub0CombinedCancellationIntervalCert.Valid.to_hCombined`
- highOrderCertStructure: `Step33Sub0CombinedCancellationHighOrderTaylorCert`
- highOrderValidPredicate: `Step33Sub0CombinedCancellationHighOrderTaylorCert.Valid`
- highOrderRemainderTheorem: `Step33Sub0CombinedCancellationHighOrderTaylorCert.Valid.remainder_bound`
- highOrderToIntervalTheorem: `Step33Sub0CombinedCancellationHighOrderTaylorCert.Valid.to_interval_valid`
- highOrderToHCombinedTheorem: `Step33Sub0CombinedCancellationHighOrderTaylorCert.Valid.to_hCombined`
- highOrderToResidualTheorem: `Step33Sub0CombinedCancellationHighOrderTaylorCert.Valid.to_fullTaylor_residual_deriv_interval`
- highOrderReceiverTheorem: `primaryFiniteRow0Parent0Split100Sub0_combinedCancellation_remainder_bound_of_centerJet15_order16`
- highOrderAliasTheorem: `primaryFiniteRow0Parent0Split100Sub0_combinedCancellation_centerTaylor15_remainder_of_order16`
- conditionalRemainderProp: `primaryFiniteRow0Parent0Split100Sub0CombinedCancellationRemainderSourceProp`
- conditionalPayloadTheorem: `primaryFiniteRow0Parent0Split100Sub0_combinedCancellationInterval_valid_of_remainder_bound`
- conditionalHCombinedTheorem: `primaryFiniteRow0Parent0Split100Sub0_combinedCancellation_hCombined_of_remainder_bound`
- expression: `primaryFiniteRow0Parent0Split100Sub0CombinedCancellationIntervalExpr`
- consumerTheorem: `primaryFiniteRow0Parent0Split100Sub0_fullTaylor_residual_deriv_interval_of_combined_bounds`
- closedFormTheorem: `primaryFiniteRow0Parent0Split100Sub0_fullTaylor_closedForm_residual_bounds_of_combined_bounds`
- proofDataWrapper: `primaryFiniteRow0Parent0Split100Sub0_fullTaylor_cellSlopeExactIntegralProofData_of_checked_hRawCenterCoeffAbs_and_combined_bounds`
- boundInputsFile: `Q3/Proofs/PSD_CenteredCoeffRawOmegaAComponentTaylorCancellationBoundInputs.lean`
- normReceiverFile: `Q3/Proofs/PSD_CenteredCoeffRawOmegaAComponentTaylorCancellationNormReceiver.lean`
- p45BridgeFile: `Q3/Proofs/PSD_CenteredCoeffRawOmegaAComponentTaylorCancellationP45Bridge.lean`
- landingFile: `Q3/Proofs/PSD_CenteredCoeffRawOmegaAHRawLanding.lean`

## High-Order Payload Target

- certStructure: `Step33Sub0CombinedCancellationHighOrderTaylorCert`
- validPredicate: `Step33Sub0CombinedCancellationHighOrderTaylorCert.Valid`

Must provide:
- smooth proof for primaryFiniteRow0Parent0Split100Sub0CombinedCancellationIntervalExpr
- coeff : Fin 16 -> Rat
- coeffErrorAbs : Fin 16 -> Rat
- coeffErrorNonneg proof
- remainderNonneg proof
- centerJet rows j = 0..15 at center 1/20
- component-source centerJet lower/upper rows j = 0..15
- uniform order16Abs on Set.Icc 0 (1/10)
- component-source order16 lower/upper rows on Set.Icc 0 (1/10)
- remainderBudget proof
- polyLower and polyUpper for the degree-15 polynomial
- Step33Sub0CombinedCancellationHornerRangeCert.Valid
- target lower budget proof
- target upper budget proof

Adapter chain:
- `Step33Sub0CombinedCancellationSourceIntervalCert.Valid.to_highOrderValid`
- `Step33Sub0CombinedCancellationSourceIntervalCert.Valid.to_hCombined`
- `Step33Sub0CombinedCancellationSourceIntervalCert.Valid.to_fullTaylor_residual_deriv_interval`
- `primaryFiniteRow0Parent0Split100Sub0_combinedCancellation_highOrderValid_of_componentSource_interval`
- `primaryFiniteRow0Parent0Split100Sub0_combinedCancellation_highOrderValid_of_componentSource_bounds`
- `Step33Sub0CombinedCancellationHighOrderTaylorCert.Valid.remainder_bound`
- `Step33Sub0CombinedCancellationHighOrderTaylorCert.Valid.to_interval_valid`
- `Step33Sub0CombinedCancellationHighOrderTaylorCert.Valid.to_hCombined`
- `Step33Sub0CombinedCancellationHighOrderTaylorCert.Valid.to_fullTaylor_residual_deriv_interval`

Target statement:

```text
forall eta in Set.Icc (0 : Real) ((1 : Real) / 10), (-94119513411/500000000000000000000000000000) <= primaryFiniteRow0Parent0Split100Sub0CombinedCancellationIntervalExpr eta and primaryFiniteRow0Parent0Split100Sub0CombinedCancellationIntervalExpr eta <= (1866608532757/500000000000000000000000000000)
```

Combined expression:

`rawOmegaATaylorPolynomial assembledDegree 1/20 ResidualTaylorCoeff eta + ScaledCancellationRhs eta`

## Proof Status

- isLeanProofData: `False`
- outLeanWritten: `False`
- conditionalPayloadPresent: `True`
- conditionalPayloadIsUnconditionalProof: `False`
- highOrderSourceFilePresent: `True`
- highOrderValidPayloadPresent: `False`
- highOrderCenterJetRowsPresent: `False`
- highOrderOrder16RowsPresent: `False`
- highOrderHornerRangeRowsPresent: `False`
- highOrderTargetBudgetRowsPresent: `False`
- wholeExpressionSourceModelPresent: `True`
- centerJetSourceModelPresent: `True`
- order16SourceModelPresent: `True`
- fullSourceModelBridgePresent: `True`
- sourceBoundsToHighOrderValidConstructorPresent: `True`
- sourceIntervalRowsToHighOrderValidConstructorPresent: `True`
- sourceIntervalCertStructurePresent: `True`
- sourceIntervalCertValidPredicatePresent: `True`
- sourceIntervalCertToHighOrderValidPresent: `True`
- sourceIntervalCertToHCombinedPresent: `True`
- sourceIntervalCertToResidualIntervalPresent: `True`
- sourceNormalFormCancellationCauchyPresent: `True`
- sourceNormalFormConditionalCenterJetPresent: `True`
- sourceNormalFormSupportPresent: `True`
- sourceNormalFormResidualJetBridgePresent: `True`
- sourceNormalFormNonconditionalPresent: `True`
- sourceNormalFormActiveActualIntervalPresent: `True`
- sourceNormalFormActiveActualValidConstructorPresent: `True`
- sourceNormalFormActiveActualInterfacePresent: `True`
- sourceIntervalCertPayloadPresent: `False`
- omegaPrimePayloadReusableForWholeExpression: `False`
- residualTaylorCoeffPayloadPresent: `True`
- componentAssemblyLedgerPresent: `True`
- proofSafeClosedFields: `0`
- combinedReceiverCheckedInLean: `True`
- combinedExpressionDefinedInLean: `True`
- combinedIntervalTheoremCheckedInLean: `True`
- proofGradeCombinedBoundsPresent: `False`
- sampledCandidateIsProof: `False`
- segmentCoveragePassedExactRational: `True`
- allSegmentsBudgetPassedExactRational: `True`
- allSegmentsProofGrade: `False`

## Source Model Inventory

- status: `source_interval_cert_target_checked_payload_missing`
- firstSourceFailure: `STEP33_A1_SUB0_COMBINED_CANCELLATION_CENTER_JETS_ORDER16_PAYLOAD_GAP`
- centerJetFailure: `None`
- order16Failure: `None`

Source-interval certificate target:
- file: `Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationSourceIntervalCert.lean`
- structure: `{'file': 'Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationSourceIntervalCert.lean', 'symbol': 'Step33Sub0CombinedCancellationSourceIntervalCert', 'lookupSymbol': 'structure Step33Sub0CombinedCancellationSourceIntervalCert', 'line': 36, 'exists': True}`
- validPredicate: `{'file': 'Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationSourceIntervalCert.lean', 'symbol': 'Step33Sub0CombinedCancellationSourceIntervalCert.Valid', 'lookupSymbol': 'structure Valid', 'line': 56, 'exists': True}`
- toHighOrderValid: `{'file': 'Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationSourceIntervalCert.lean', 'symbol': 'Step33Sub0CombinedCancellationSourceIntervalCert.Valid.to_highOrderValid', 'lookupSymbol': 'theorem to_highOrderValid', 'line': 98, 'exists': True}`
- toHCombined: `{'file': 'Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationSourceIntervalCert.lean', 'symbol': 'Step33Sub0CombinedCancellationSourceIntervalCert.Valid.to_hCombined', 'lookupSymbol': 'theorem to_hCombined', 'line': 112, 'exists': True}`
- toResidualInterval: `{'file': 'Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationSourceIntervalCert.lean', 'symbol': 'Step33Sub0CombinedCancellationSourceIntervalCert.Valid.to_fullTaylor_residual_deriv_interval', 'lookupSymbol': 'theorem to_fullTaylor_residual_deriv_interval', 'line': 138, 'exists': True}`
- structurePresent: `True`
- validPredicatePresent: `True`
- toHighOrderValidPresent: `True`
- toHCombinedPresent: `True`
- toResidualIntervalPresent: `True`
- targetPresent: `True`
- payloadPresent: `False`
- status: `checked_target_payload_missing`
- whyNotEnough: `This packages the component-source lower/upper row obligations into a Lean-checked certificate target and routes any Valid payload to HighOrderTaylorCert.Valid and the final residual-derivative interval receiver. It does not emit concrete lower/upper rows, Horner rows, target-budget rows, or a Valid payload.`

Source normal-form support:
- file: `Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationSourceNormalForm.lean`
- cancellationResidualCauchy: `{'file': 'Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationSourceNormalForm.lean', 'symbol': 'primaryFiniteRow0Parent0Split100Sub0_cancellationResidualCauchy_eq_actual_sub_nominal', 'lookupSymbol': 'theorem primaryFiniteRow0Parent0Split100Sub0_cancellationResidualCauchy_eq_actual_sub_nominal', 'line': 233, 'exists': True}`
- conditionalCenterJetNormalForm: `{'file': 'Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationSourceNormalForm.lean', 'symbol': 'primaryFiniteRow0Parent0Split100Sub0_combinedCancellation_centerJet_eq_activeActual_sub_model_of_residualJet', 'lookupSymbol': 'theorem primaryFiniteRow0Parent0Split100Sub0_combinedCancellation_centerJet_eq_activeActual_sub_model_of_residualJet', 'line': 399, 'exists': True}`
- residualJetBridge: `{'file': 'Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationSourceNormalForm.lean', 'symbol': 'primaryFiniteRow0Parent0Split100Sub0_residualTaylor_centerJet_low_eq_nominalProduct_sub_model', 'lookupSymbol': 'theorem primaryFiniteRow0Parent0Split100Sub0_residualTaylor_centerJet_low_eq_nominalProduct_sub_model', 'line': 324, 'exists': True}`
- nonconditionalCenterJetNormalForm: `{'file': 'Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationSourceNormalForm.lean', 'symbol': 'primaryFiniteRow0Parent0Split100Sub0_combinedCancellation_centerJet_eq_activeActual_sub_model', 'lookupSymbol': 'theorem primaryFiniteRow0Parent0Split100Sub0_combinedCancellation_centerJet_eq_activeActual_sub_model', 'line': 423, 'exists': True}`
- activeActualIntervalAdapter: `{'file': 'Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationSourceNormalForm.lean', 'symbol': 'primaryFiniteRow0Parent0Split100Sub0_combinedCancellation_sourceCenterInterval_of_activeActual_interval', 'lookupSymbol': 'theorem primaryFiniteRow0Parent0Split100Sub0_combinedCancellation_sourceCenterInterval_of_activeActual_interval', 'line': 445, 'exists': True}`
- activeActualValidConstructor: `{'file': 'Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationSourceNormalForm.lean', 'symbol': 'primaryFiniteRow0Parent0Split100Sub0_combinedCancellation_highOrderValid_of_activeActual_interval', 'lookupSymbol': 'theorem primaryFiniteRow0Parent0Split100Sub0_combinedCancellation_highOrderValid_of_activeActual_interval', 'line': 483, 'exists': True}`
- supportPresent: `True`
- residualJetBridgePresent: `True`
- nonconditionalNormalFormPresent: `True`
- activeActualInterfacePresent: `True`
- status: `checked_nonconditional_normal_form_payload_missing`
- firstFailure: `STEP33_A1_SUB0_COMBINED_CANCELLATION_CENTER_JETS_ORDER16_PAYLOAD_GAP`
- missingBridge: `None`
- whyNotEnough: `The residual Taylor center-jet alignment bridge and nonconditional active-actual normal form are now Lean-checked, including a generator-facing active-actual interval adapter. This is still not a generated source interval payload: concrete lower/upper rows, Horner rows, target-budget rows, and a Valid payload are still missing.`

Checked source-model bridge:
- file: `Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationSourceModelBridge.lean`
- smoothTheorem: `{'file': 'Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationSourceModelBridge.lean', 'symbol': 'primaryFiniteRow0Parent0Split100Sub0_combinedCancellation_contDiff16', 'line': 456, 'exists': True}`
- centerJetTheorem: `{'file': 'Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationSourceModelBridge.lean', 'symbol': 'primaryFiniteRow0Parent0Split100Sub0_combinedCancellation_centerJet_eq_componentSource', 'line': 808, 'exists': True}`
- order16Source: `{'file': 'Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationSourceModelBridge.lean', 'symbol': 'primaryFiniteRow0Parent0Split100Sub0CombinedCancellationOrder16ComponentSource', 'line': 964, 'exists': True}`
- order16Theorem: `{'file': 'Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationSourceModelBridge.lean', 'symbol': 'primaryFiniteRow0Parent0Split100Sub0_combinedCancellation_order16_eq_componentSource', 'line': 983, 'exists': True}`
- order16BoundAdapter: `{'file': 'Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationSourceModelBridge.lean', 'symbol': 'primaryFiniteRow0Parent0Split100Sub0_combinedCancellation_order16_bound_of_componentSource', 'line': 1159, 'exists': True}`
- centerJetBoundsAdapter: `{'file': 'Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationSourceModelBridge.lean', 'symbol': 'primaryFiniteRow0Parent0Split100Sub0_combinedCancellation_centerJet_bounds_of_componentSource', 'line': 1181, 'exists': True}`
- highOrderValidConstructor: `{'file': 'Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationSourceModelBridge.lean', 'symbol': 'primaryFiniteRow0Parent0Split100Sub0_combinedCancellation_highOrderValid_of_componentSource_bounds', 'line': 1221, 'exists': True}`
- highOrderIntervalConstructor: `{'file': 'Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationSourceModelBridge.lean', 'symbol': 'primaryFiniteRow0Parent0Split100Sub0_combinedCancellation_highOrderValid_of_componentSource_interval', 'line': 1268, 'exists': True}`
- smoothPresent: `True`
- centerJetPresent: `True`
- order16Present: `True`
- sourceBoundsConstructorPresent: `True`
- sourceIntervalConstructorPresent: `True`
- status: `checked_source_interval_rows_to_valid_constructor`
- whyNotEnough: `This proves the whole-expression smooth bridge, all-row component-source center-jet crosswalk, and an exact order-16 source-model/norm adapter, plus the constructor from source-bounds to HighOrderTaylorCert.Valid and the interval-row constructor for component-source rows. The nonconditional source normal form is also checked. It still does not emit rational coeff rows, a proof-grade order16Abs source bound, Horner range rows, target-budget rows, or a concrete Valid payload.`

Target function:
- meaning: `whole expression, not a component: residualTaylor degree-45 polynomial plus ScaledCancellationRhs`
- formula: `rawOmegaATaylorPolynomial AssembledRawDerivDegree (1/20) ResidualTaylorCoeff eta + ScaledCancellationRhs eta`
- definition: `{'file': 'Q3/Proofs/PSD_CenteredCoeffRawOmegaAComponentTaylorCancellationCombinedInterval.lean', 'symbol': 'primaryFiniteRow0Parent0Split100Sub0CombinedCancellationIntervalExpr', 'line': 29, 'exists': True}`

Rational polynomial part:
- status: `present_but_not_sufficient`
- degree: `45`
- definition: `{'file': 'Q3/Proofs/PSD_CenteredCoeffRawOmegaAComponentTaylorCoeffAssembly.lean', 'symbol': 'def primaryFiniteRow0Parent0Split100Sub0ResidualTaylorCoeff', 'line': 1142, 'exists': True}`
- payload: `{'file': 'Q3/Proofs/PSD_CenteredCoeffRawOmegaAComponentTaylorCoeffAssemblyPayload.lean', 'symbol': 'def primaryFiniteRow0Parent0Split100Sub0ResidualTaylorCoeffPayload', 'line': 74, 'exists': True}`
- payloadEquality: `{'file': 'Q3/Proofs/PSD_CenteredCoeffRawOmegaAComponentTaylorCoeffAssemblyPayload.lean', 'symbol': 'theorem primaryFiniteRow0Parent0Split100Sub0_residualTaylorCoeff_payload_eq', 'line': 128, 'exists': True}`
- whyNotEnough: `This materializes the algebraic residual polynomial, but the high-order Valid object needs center jets and a uniform 16th-derivative bound for the whole combined expression.`

ScaledCancellationRhs:

- status: `source_model_checked_for_center_jets_and_order16`
- definition: `{'file': 'Q3/Proofs/PSD_CenteredCoeffRawOmegaAComponentTaylorCancellationNormReceiver.lean', 'symbol': 'def primaryFiniteRow0Parent0Split100Sub0ScaledCancellationRhs', 'line': 34, 'exists': True}`
- activeScale: `{'file': 'Q3/Proofs/PSD_CenteredCoeffRawOmegaAComponentTaylorCancellationNormReceiver.lean', 'symbol': 'def primaryFiniteRow0Parent0Split100Sub0ActiveScaleCoeff', 'line': 31, 'exists': True}`
- formula: `ActiveScaleCoeff * ComponentProductCancellationResidual + (ActiveScaleCoeff - NominalScaleCoeff) * ComponentProductNominal`
- normalizationHazard: `ActiveScaleCoeff is ((3/10)/Real.pi), while the residual polynomial payload is rational and nominal-scale based.`
- missing:
  - concrete rational center-jet rows j=0..15 for the combined expression
  - proof-grade uniform order16 bound for the order16 component source
  - same-surface addition with the residualTaylor polynomial in the high-order receiver normalization

Reusable but not sufficient:

- omegaPrimePayload: `{'path': 'ACTIVE/requests/step33_bootstrap/step33_a1_sub0_omega_prime_taylor_payload.json', 'exists': True, 'status': 'proof_grade_for_omega_prime_only', 'whyNotEnough': 'It certifies step22OmegaArchWeightDerivClosedForm, not the whole CombinedCancellationIntervalExpr.'}`
- hornerRangeChecker: `{'definition': {'file': 'Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationPolynomialRange.lean', 'symbol': 'structure Step33Sub0CombinedCancellationHornerRangeCert', 'line': 63, 'exists': True}, 'status': 'ready_after_coefficients', 'whyNotEnough': 'It consumes a degree-15 polynomial range; it does not produce center jets or order16 source bounds.'}`
- componentAssemblyLedger: `{'path': 'ACTIVE/requests/step33_bootstrap/step33_a1_sub0_component_assembly_stream_ledger.json', 'exists': True, 'status': 'algebraic_coefficients_checked_remainder_source_open', 'whyNotEnough': 'It records exact assembly/payload facts but still marks component remainder/source-model closure open.'}`

Required bridge shape:

- component-source lower/upper row intervals may be used via the checked interval-row constructor, but the concrete rows are still missing
- prove active-actual lower/upper row intervals and feed them through the checked active-actual interval adapter
- forall j : Fin 16, norm(iteratedDeriv j CombinedCancellationIntervalExpr center / j! - coeff[j]) <= coeffErrorAbs[j]
- forall eta in Icc 0 (1/10), norm(iteratedDeriv 16 CombinedCancellationIntervalExpr eta) <= order16Abs
- sum_j coeffErrorAbs[j] * radius^j + order16Abs * radius^16 / 16! <= remainderAbs
- Horner range for rawOmegaATaylorPolynomial 15 center coeff
- target lower/upper budget after subtracting/adding remainderAbs
- nextPatchRecommendation: `Generate/prove concrete SourceIntervalCert.Valid rows through the checked active-actual interval adapter.`

## Candidate Segments

- cell `0`:
  segment = `[0, 1/10]`
  combined = `[-94119513411/500000000000000000000000000000, 1866608532757/500000000000000000000000000000]`
  budgetPassesExactRational = `True`
  sourceProofStatus = `sampled_candidate_not_lean_proof`
  isProofGrade = `False`
  proofGradeCombinedBounds = `missing`

## Candidate Arithmetic

- coverage.coveragePassedExactRational: `True`
- coverage.adjacencyPassedExactRational: `True`
- coverage.segmentNonemptyPassedExactRational: `True`
- coverage.leftEndpoint: `0`
- coverage.rightEndpoint: `1/10`
- coverage.expectedLeftEndpoint: `0`
- coverage.expectedRightEndpoint: `1/10`
- coverage.firstFailure: `None`
- budgetPassedExactRational: `True`
- candidateReadyForLeanShape: `True`
- proofGradeCombinedBoundsPresent: `False`

## Required Certificate

- kind: `proof_grade_high_order_taylor_and_horner_payload`
- must prove: `a concrete Step33Sub0CombinedCancellationSourceIntervalCert.Valid payload plus Horner range and target-budget inequalities`

May use:
- rational interval arithmetic
- Lean-verifiable matrix/free polynomial interval certificate
- independently checkable generated rational output

Must not use:
- sampled JSON as proof
- separate norm bounds for residualTaylor polynomial and ScaledCancellationRhs
- independent raw/poly interval subtraction
- product-budget rows route after width-fail

## Closed Local Facts

- OmegaPrime generated Taylor remainder cert is Valid and has a public bound.
- Omega Taylor bound is obtained by integrating OmegaPrime plus anchor interval.
- rawDeriv - assembledPoly equals the scaled cancellation RHS.
- deriv residual equals residualTaylor P45 polynomial plus ScaledCancellationRhs.
- triangle split is killed by checked residualTaylor final-slope failures.
- rows0..11 independent product budget is width-killed.
- High-order Taylor receiver surface is the target adapter; it still needs concrete proof rows.
- Whole-expression smoothness and all-row component-source center-jet crosswalk are Lean-checked.
- Whole-expression order-16 component-source bridge and norm adapter are Lean-checked.
- Source-bounds-to-HighOrderTaylorCert.Valid constructor is Lean-checked.
- Component-source lower/upper interval rows can feed HighOrderTaylorCert.Valid through a Lean-checked constructor.
- Source-interval certificate target routes component-source lower/upper rows to HighOrderTaylorCert.Valid and final combined interval receivers.
- Nonconditional source-normal-form support is Lean-checked: cancellationResidualCauchy = actualCauchy - nominalCauchy, the residual Taylor center-jet alignment bridge is checked, and the active-actual center-jet normal form no longer has a residual-jet hypothesis.

## Rejected Routes

- independentTriangleSplit: killed: residualTaylor polynomial alone exceeds final slope at the center
- rowsProductBudgetRefinement: not a closure path while it preserves the independent product-budget style
- sampledSegmentPayload: diagnostic only, not proof evidence

## Candidate Source

- path: `/Users/emalam/Documents/GitHub/rh_lean_01_2026/q3.lean.aristotle/ACTIVE/requests/step33_bootstrap/step33_a1_sub0_segmented_residual_deriv_interval_payload.json`
- exists: `True`
- schema: `q3_psdpd_step33_a1_sub0_segmented_residual_deriv_interval_payload.v6`
- status: `fail_closed_missing_cancellation_preserving_taylor_remainder_proof`
- proofMode: `exact_rational_same_expression_interval`
- sourceIsProofGrade: `False`
- interpretation: `The candidate records exact rational coverage and budget checks, but its sourceProofStatus remains sampled_candidate_not_lean_proof. It cannot instantiate the high-order Valid payload.`

## Next Implementable Patch

- recommendation: `build proof-grade source interval rows/payload for the nonconditional active-actual source normal form`
- firstFailureIfMissing: `STEP33_A1_SUB0_COMBINED_CANCELLATION_CENTER_JETS_ORDER16_PAYLOAD_GAP`
- leanPayloadTarget: `Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationSourceIntervalCert.lean`
- checkerTheorem: `Step33Sub0CombinedCancellationHighOrderTaylorCert.Valid.to_hCombined`
- remainingGap: `STEP33_A1_SUB0_COMBINED_CANCELLATION_CENTER_JETS_ORDER16_PAYLOAD_GAP`
- doNot:
  - do not build C1 point-separation first
  - do not use sampled/probe rows
  - do not revive component triangle/product split
  - do not reuse OmegaPrime payload as a certificate for the whole expression
  - do not mark Valid/finalBudgetPassed before Lean-checked rows

## Failure Codes

- `STEP33_A1_SUB0_COMBINED_CANCELLATION_HIGH_ORDER_VALID_PAYLOAD_GAP`
- `STEP33_A1_SUB0_COMBINED_CANCELLATION_HIGH_ORDER_TAYLOR_RECEIVER_GAP`
- `STEP33_A1_SUB0_COMBINED_CANCELLATION_CENTER_JETS_ORDER16_PAYLOAD_GAP`
- `STEP33_A1_SUB0_COMBINED_CANCELLATION_WHOLE_EXPRESSION_SOURCE_MODEL_GAP`
- `STEP33_A1_SUB0_COMBINED_CANCELLATION_CENTER_JET_SOURCE_MODEL_GAP`
- `STEP33_A1_SUB0_COMBINED_CANCELLATION_ORDER16_SOURCE_MODEL_GAP`
- `STEP33_A1_SUB0_COMBINED_CANCELLATION_CENTER_JET_ROWS_MISSING`
- `STEP33_A1_SUB0_COMBINED_CANCELLATION_ORDER16_ROWS_MISSING`
- `STEP33_A1_SUB0_COMBINED_CANCELLATION_HORNER_RANGE_ROWS_MISSING`
- `STEP33_A1_SUB0_COMBINED_CANCELLATION_TARGET_BUDGET_ROWS_MISSING`
- `STEP33_A1_SUB0_COMBINED_INTERVAL_PROOF_GRADE_SOURCE_MISSING`
- `STEP33_A1_SUB0_COMBINED_INTERVAL_LEAN_PAYLOAD_MISSING`
- `STEP33_A1_SUB0_CANCELLATION_PRESERVING_TAYLOR_REMAINDER_GAP`

## Source Hashes

- `Q3/Proofs/PSD_CenteredCoeffRawOmegaAComponentTaylorCancellationCombinedInterval.lean`: `d3ce443f3d86cc33`
- `Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationIntervalCert.lean`: `172524e28455ca5b`
- `Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationIntervalPayload.lean`: `2cf0833b5b65c1f7`
- `Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationHighOrderTaylorSource.lean`: `3f95fa0605fd469c`
- `Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationSourceModelBridge.lean`: `84628671b07f836b`
- `Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationSourceIntervalCert.lean`: `05fae4f366bb39df`
- `Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationSourceNormalForm.lean`: `187d8f22bc9689d7`
- `Q3/Proofs/PSD_CenteredCoeffRawOmegaAComponentTaylorCancellationBoundInputs.lean`: `c8832f56435b42fa`
- `Q3/Proofs/PSD_CenteredCoeffRawOmegaAComponentTaylorCancellationNormReceiver.lean`: `8554b282c60d9c25`
- `Q3/Proofs/PSD_CenteredCoeffRawOmegaAComponentTaylorCancellationP45Bridge.lean`: `aabf02168d6d50fd`
- `Q3/Proofs/PSD_CenteredCoeffRawOmegaAHRawLanding.lean`: `3074c575ace73694`
- `Q3/Proofs/PSD_CenteredCoeffRawOmegaAComponentTaylorCoeffAssemblyPayload.lean`: `b143a7bacb1c90fd`
- `ACTIVE/requests/step33_bootstrap/step33_a1_sub0_component_assembly_stream_ledger.json`: `83da8ec8067da8a7`
- `ACTIVE/requests/step33_bootstrap/step33_a1_sub0_omega_prime_taylor_payload.json`: `d76ad77551996b39`
- `ACTIVE/requests/step33_bootstrap/step33_a1_sub0_segmented_residual_deriv_interval_payload.json`: `df8cb8dff74f605e`
