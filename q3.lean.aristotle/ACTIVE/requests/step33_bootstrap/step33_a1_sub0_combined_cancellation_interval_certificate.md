# Step33A.1-A Sub0 Combined Cancellation Interval Certificate

Fail-closed certificate ledger.  This is not Lean proof data and does
not close Step33A.1-A.

## Summary

- schema: `q3_psdpd_step33_a1_sub0_combined_cancellation_interval_certificate.v20`
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
- sourceNormalFormActiveActualSourceIntervalValid: `primaryFiniteRow0Parent0Split100Sub0_combinedCancellation_sourceIntervalValid_of_activeActual_interval`
- activeActualCenterJetRowsFile: `Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationActiveActualCenterJetRowsPayload.lean`
- activeActualCenterJetIntervalOfAbs: `primaryFiniteRow0Parent0Split100Sub0_centerJet_interval_of_abs`
- activeActualShapeSqDerivSingleAbsSigned: `primaryFiniteRow0Parent0Split100Sub0_shapeSqDeriv_singleAbs_signed_centerJet_interval`
- activeActualShapeSqDerivRows01234567891011Signed: `primaryFiniteRow0Parent0Split100Sub0_shapeSqDerivRows01234567891011_signed_centerJet_interval`
- activeActualOmegaPrimeSignedRows: `primaryFiniteRow0Parent0Split100Sub0_omegaPrimeActual_signed_centerJet_interval`
- activeActualOmegaSignedRows: `primaryFiniteRow0Parent0Split100Sub0_omegaActual_signed_centerJet_interval`
- activeActualShapeSqSignedRows: `primaryFiniteRow0Parent0Split100Sub0_shapeSqActual_signed_centerJet_interval`
- activeActualSumIntervalReceiver: `primaryFiniteRow0Parent0Split100Sub0_sum_interval_of_term_intervals`
- activeActualCauchyIntervalReceiver: `primaryFiniteRow0Parent0Split100Sub0_normalizedJetConvolution_interval_of_term_intervals`
- activeActualComponentProductCauchyIntervalReceiver: `primaryFiniteRow0Parent0Split100Sub0_componentProductActualCauchy_interval`
- activeActualScaleNonneg: `primaryFiniteRow0Parent0Split100Sub0_activeScale_nonneg`
- activeActualRowIntervalReceiver: `primaryFiniteRow0Parent0Split100Sub0_activeActual_centerJet_row_interval_of_product_interval`
- activeActualComponentProductAbs: `primaryFiniteRow0Parent0Split100Sub0ComponentProductActualCauchyAbs`
- activeActualComponentProductAbsInterval: `primaryFiniteRow0Parent0Split100Sub0_componentProductActualCauchy_abs_interval`
- activeActualComponentProductAbsNonneg: `primaryFiniteRow0Parent0Split100Sub0_componentProductActualCauchyAbs_nonneg`
- activeActualCenterRowLower: `primaryFiniteRow0Parent0Split100Sub0ActiveActualCenterJetRowLower`
- activeActualCenterRowUpper: `primaryFiniteRow0Parent0Split100Sub0ActiveActualCenterJetRowUpper`
- activeActualCenterRowIntervalFromFactorRows: `primaryFiniteRow0Parent0Split100Sub0_activeActual_centerJet_row_interval_from_factor_rows`
- centerJetPayloadFile: `Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationCenterJetPayload.lean`
- centerJetCoeff: `primaryFiniteRow0Parent0Split100Sub0CombinedCancellationCoeff`
- centerJetCoeffErrorAbs: `primaryFiniteRow0Parent0Split100Sub0CombinedCancellationCoeffErrorAbs`
- centerJetCoeffErrorAbsNonneg: `primaryFiniteRow0Parent0Split100Sub0_combinedCancellation_coeffErrorAbs_nonneg`
- centerJetComponentSourceAbsGenerated: `primaryFiniteRow0Parent0Split100Sub0_combinedCancellation_componentSource_centerJet_abs_generated`
- centerJetAbsGenerated: `primaryFiniteRow0Parent0Split100Sub0_combinedCancellation_centerJet_abs_generated`
- order16FactorMajorantFile: `Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16FactorMajorant.lean`
- order16SourceEqActiveActual: `primaryFiniteRow0Parent0Split100Sub0_combinedCancellationOrder16Source_eq_activeActual`
- order16FactorDerivativeReceiverFile: `Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16FactorDerivativeReceiver.lean`
- order16FactorDerivativeMajorantBridgeFile: `Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationFactorDerivativeMajorantBridge.lean`
- order16BudgetPayloadFile: `Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16BudgetPayload.lean`
- order16ComponentProductMajorant: `primaryFiniteRow0Parent0Split100Sub0ComponentProductActualOrder16Majorant`
- order16ComponentProductAbsReceiver: `primaryFiniteRow0Parent0Split100Sub0_componentProductActual_order16_abs_of_factor_derivative_abs`
- order16SourceAbsReceiver: `primaryFiniteRow0Parent0Split100Sub0_combinedCancellationOrder16Source_abs_of_factor_derivative_abs`
- order16SourceIntervalReceiver: `primaryFiniteRow0Parent0Split100Sub0_combinedCancellationOrder16Source_interval_of_factor_derivative_abs`
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
- highOrderCenterJetRowsPresent: `True`
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
- sourceNormalFormActiveActualSourceIntervalValidPresent: `True`
- sourceNormalFormActiveActualInterfacePresent: `True`
- activeActualCenterJetRowsFilePresent: `True`
- activeActualSingleAbsToSignedCenterJetCrosswalkPresent: `True`
- activeActualShapeSqDerivSingleAbsSignedRowsPresent: `True`
- activeActualShapeSqDerivRows01234567891011SignedPresent: `True`
- activeActualOmegaPrimeSignedRowsPresent: `True`
- activeActualOmegaSignedRowsPresent: `True`
- activeActualShapeSqSignedRowsPresent: `True`
- activeActualAllFactorSignedRowsPresent: `True`
- activeActualFactorIntervalReceiverPresent: `True`
- activeActualSumIntervalReceiverPresent: `True`
- activeActualCauchyIntervalReceiverPresent: `True`
- activeActualComponentProductCauchyIntervalReceiverPresent: `True`
- activeActualScaleNonnegPresent: `True`
- activeActualRowIntervalReceiverPresent: `True`
- activeActualComponentProductAbsPresent: `True`
- activeActualComponentProductAbsIntervalPresent: `True`
- activeActualComponentProductAbsNonnegPresent: `True`
- activeActualCenterRowLowerPresent: `True`
- activeActualCenterRowUpperPresent: `True`
- activeActualCenterRowIntervalFromFactorRowsPresent: `True`
- activeActualProductRowIntervalsPresent: `True`
- centerJetPayloadFilePresent: `True`
- centerJetCoeffPresent: `True`
- centerJetCoeffErrorAbsPresent: `True`
- centerJetCoeffErrorAbsNonnegPresent: `True`
- centerJetComponentSourceAbsGeneratedPresent: `True`
- centerJetAbsGeneratedPresent: `True`
- centerJetAbsPayloadPresent: `True`
- order16FactorMajorantFilePresent: `True`
- order16SourceEqActiveActualPresent: `True`
- order16StructuralReductionPresent: `True`
- order16FactorDerivativeReceiverFilePresent: `True`
- order16ComponentProductMajorantPresent: `True`
- order16ComponentProductAbsReceiverPresent: `True`
- order16SourceAbsReceiverPresent: `True`
- order16SourceIntervalReceiverPresent: `True`
- order16FactorDerivativeReceiverPresent: `True`
- order16CenteredTaylorFactorMajorantBridgePresent: `True`
- order16BudgetPayloadFilePresent: `True`
- order16ActiveScaleAbsPresent: `True`
- order16BudgetLeDeclaredAbsPresent: `True`
- order16RemainderWidthFailRatPresent: `True`
- order16RemainderWidthFailPresent: `True`
- order16CenteredTaylorFactorRouteBudgetKilled: `True`
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
- activeActualSourceIntervalValid: `{'file': 'Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationSourceNormalForm.lean', 'symbol': 'primaryFiniteRow0Parent0Split100Sub0_combinedCancellation_sourceIntervalValid_of_activeActual_interval', 'lookupSymbol': 'theorem primaryFiniteRow0Parent0Split100Sub0_combinedCancellation_sourceIntervalValid_of_activeActual_interval', 'line': 545, 'exists': True}`
- supportPresent: `True`
- residualJetBridgePresent: `True`
- nonconditionalNormalFormPresent: `True`
- activeActualInterfacePresent: `True`
- status: `checked_nonconditional_normal_form_payload_missing`
- firstFailure: `STEP33_A1_SUB0_COMBINED_CANCELLATION_CENTER_JETS_ORDER16_PAYLOAD_GAP`
- missingBridge: `None`
- whyNotEnough: `The residual Taylor center-jet alignment bridge and nonconditional active-actual normal form are now Lean-checked, including a generator-facing active-actual interval adapter and source-interval Valid constructor. This is still not a generated source interval payload: concrete lower/upper rows, Horner rows, target-budget rows, and a Valid payload are still missing.`

Checked source-model bridge:
- file: `Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationSourceModelBridge.lean`
- smoothTheorem: `{'file': 'Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationSourceModelBridge.lean', 'symbol': 'primaryFiniteRow0Parent0Split100Sub0_combinedCancellation_contDiff16', 'line': 456, 'exists': True}`
- centerJetTheorem: `{'file': 'Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationSourceModelBridge.lean', 'symbol': 'primaryFiniteRow0Parent0Split100Sub0_combinedCancellation_centerJet_eq_componentSource', 'line': 808, 'exists': True}`
- order16Source: `{'file': 'Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationSourceModelBridge.lean', 'symbol': 'primaryFiniteRow0Parent0Split100Sub0CombinedCancellationOrder16ComponentSource', 'line': 964, 'exists': True}`
- order16Theorem: `{'file': 'Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationSourceModelBridge.lean', 'symbol': 'primaryFiniteRow0Parent0Split100Sub0_combinedCancellation_order16_eq_componentSource', 'line': 983, 'exists': True}`
- order16BoundAdapter: `{'file': 'Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationSourceModelBridge.lean', 'symbol': 'primaryFiniteRow0Parent0Split100Sub0_combinedCancellation_order16_bound_of_componentSource', 'line': 1159, 'exists': True}`
- order16StructuralReduction: `{'file': 'Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16FactorMajorant.lean', 'symbol': 'primaryFiniteRow0Parent0Split100Sub0_combinedCancellationOrder16Source_eq_activeActual', 'line': 313, 'exists': True}`
- order16FactorDerivativeReceiverFile: `Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16FactorDerivativeReceiver.lean`
- order16FactorDerivativeMajorantBridgeFile: `Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationFactorDerivativeMajorantBridge.lean`
- order16BudgetPayloadFile: `Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16BudgetPayload.lean`
- order16ComponentProductMajorant: `{'file': 'Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16FactorDerivativeReceiver.lean', 'symbol': 'primaryFiniteRow0Parent0Split100Sub0ComponentProductActualOrder16Majorant', 'line': 28, 'exists': True}`
- order16ComponentProductAbsReceiver: `{'file': 'Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16FactorDerivativeReceiver.lean', 'symbol': 'primaryFiniteRow0Parent0Split100Sub0_componentProductActual_order16_abs_of_factor_derivative_abs', 'line': 123, 'exists': True}`
- order16SourceAbsReceiver: `{'file': 'Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16FactorDerivativeReceiver.lean', 'symbol': 'primaryFiniteRow0Parent0Split100Sub0_combinedCancellationOrder16Source_abs_of_factor_derivative_abs', 'line': 244, 'exists': True}`
- order16SourceIntervalReceiver: `{'file': 'Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16FactorDerivativeReceiver.lean', 'symbol': 'primaryFiniteRow0Parent0Split100Sub0_combinedCancellationOrder16Source_interval_of_factor_derivative_abs', 'line': 314, 'exists': True}`
- order16CenteredTaylorFactorMajorantsReceiver: `{'file': 'Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationFactorDerivativeMajorantBridge.lean', 'symbol': 'primaryFiniteRow0Parent0Split100Sub0_combinedCancellationOrder16Source_interval_of_centeredTaylor_factor_majorants', 'line': 464, 'exists': True}`
- order16ActiveScaleAbs: `{'file': 'Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16BudgetPayload.lean', 'symbol': 'primaryFiniteRow0Parent0Split100Sub0_combinedCancellation_order16_activeScaleAbs', 'line': 104, 'exists': True}`
- order16BudgetLeDeclaredAbs: `{'file': 'Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16BudgetPayload.lean', 'symbol': 'primaryFiniteRow0Parent0Split100Sub0_combinedCancellation_order16BudgetRat_le_declaredAbs', 'line': 109, 'exists': True}`
- order16RemainderWidthFailRat: `{'file': 'Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16BudgetPayload.lean', 'symbol': 'primaryFiniteRow0Parent0Split100Sub0_combinedCancellation_order16Budget_remainder_width_fail_rat', 'line': 114, 'exists': True}`
- order16RemainderWidthFail: `{'file': 'Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16BudgetPayload.lean', 'symbol': 'primaryFiniteRow0Parent0Split100Sub0_combinedCancellation_order16Budget_remainder_width_fail', 'line': 114, 'exists': True}`
- centerJetBoundsAdapter: `{'file': 'Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationSourceModelBridge.lean', 'symbol': 'primaryFiniteRow0Parent0Split100Sub0_combinedCancellation_centerJet_bounds_of_componentSource', 'line': 1181, 'exists': True}`
- highOrderValidConstructor: `{'file': 'Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationSourceModelBridge.lean', 'symbol': 'primaryFiniteRow0Parent0Split100Sub0_combinedCancellation_highOrderValid_of_componentSource_bounds', 'line': 1221, 'exists': True}`
- highOrderIntervalConstructor: `{'file': 'Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationSourceModelBridge.lean', 'symbol': 'primaryFiniteRow0Parent0Split100Sub0_combinedCancellation_highOrderValid_of_componentSource_interval', 'line': 1268, 'exists': True}`
- smoothPresent: `True`
- centerJetPresent: `True`
- order16Present: `True`
- order16StructuralReductionPresent: `True`
- order16FactorDerivativeReceiverPresent: `True`
- order16CenteredTaylorFactorMajorantBridgePresent: `True`
- order16CenteredTaylorFactorRouteBudgetKilled: `True`
- order16CenteredTaylorFactorBudgetFailure: `STEP33_A1_SUB0_CENTERED_TAYLOR_FACTOR_MAJORANT_ORDER16_BUDGET_CONSTANT_FAIL`
- sourceBoundsConstructorPresent: `True`
- sourceIntervalConstructorPresent: `True`
- status: `checked_centered_taylor_factor_route_budget_killed`
- whyNotEnough: `This proves the whole-expression smooth bridge, all-row component-source center-jet crosswalk, and an exact order-16 source-model/norm adapter, plus the constructor from source-bounds to HighOrderTaylorCert.Valid and the interval-row constructor for component-source rows. The nonconditional source normal form is also checked, and the order-16 component source structurally reduces to activeScale times the actual component-product order-16 derivative. A separate checked receiver now shows that proof-grade factor derivative bounds through order 16 would feed a signed order16 source interval. It still does not emit rational coeff rows, concrete factor derivative bounds, a proof-grade order16Abs source bound, Horner range rows, target-budget rows, or a concrete Valid payload.`
- budgetKillMeaning: `The centered-Taylor factor-majorant bridge now supplies the four uniform factor-derivative families and an adapter to a signed order16 source interval, but the existing exact budget audit proves this route is too wide for the current combined-cancellation half-width. It is therefore a checked kill certificate/pattern, not the current closure route.`

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
- centeredTaylorFactorDerivativeRoute: `{'bridgeFile': 'Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationFactorDerivativeMajorantBridge.lean', 'budgetFile': 'Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16BudgetPayload.lean', 'status': 'checked_but_budget_killed', 'failureCode': 'STEP33_A1_SUB0_CENTERED_TAYLOR_FACTOR_MAJORANT_ORDER16_BUDGET_CONSTANT_FAIL', 'whyNotEnough': 'It proves a useful receiver/pattern for future sharper factor rows, but current centered-Taylor majorants do not fit the active budget. The live proof object remains a whole-expression interval certificate for ComponentSource - NonzeroModelPoly.'}`

Required bridge shape:

- active-actual lower/upper center-row intervals are now available from the signed factor rows and checked factor-product receiver
- midpoint/error center-jet abs rows are now available for the whole combined expression
- forall j : Fin 16, norm(iteratedDeriv j CombinedCancellationIntervalExpr center / j! - coeff[j]) <= coeffErrorAbs[j]
- forall eta in Icc 0 (1/10), norm(iteratedDeriv 16 CombinedCancellationIntervalExpr eta) <= order16Abs
- sum_j coeffErrorAbs[j] * radius^j + order16Abs * radius^16 / 16! <= remainderAbs
- Horner range for rawOmegaATaylorPolynomial 15 center coeff
- target lower/upper budget after subtracting/adding remainderAbs
- nextPatchRecommendation: `Build the order16 source interval payload in the same source normalization. Do not instantiate SourceIntervalCert.Valid until order16 source interval, Horner range, and target-budget rows are all proof-grade.`

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
- ShapeSqDeriv singleAbs/partial-sharp Valid rows can now be transported to signed center-jet intervals for the ShapeSqDerivActual factor.
- OmegaPrimeActual, OmegaActual, ShapeSqActual, and ShapeSqDerivActual now have Lean-checked signed center-jet interval row sources.
- A Lean-checked receiver now transports termwise factor-product intervals through Cauchy convolution, activeScale, and ResidualDerivmodelCoeff subtraction to active-actual center-row intervals.
- Concrete rational active-actual center-row lower/upper definitions and row interval proof are Lean-checked from the signed factor rows and scale upper bound.
- The signed active-actual lower/upper rows now feed midpoint/error coeff rows and a Lean-checked center-jet abs theorem for the whole combined expression.
- Order-16 component-source algebra now Lean-reduces to activeScale times the actual component-product order-16 derivative.
- A Lean-checked order16 factor-derivative receiver now reduces the source interval row to concrete factor derivative bounds for OmegaPrimeActual, OmegaActual, ShapeSqActual, and ShapeSqDerivActual through order 16 plus a scalar active-scale budget comparison.
- The centered-Taylor factor-majorant adapter for those four factor families is now locally present, but the exact rational budget audit is killed by the checked order16 remainder-width failure.

## Rejected Routes

- independentTriangleSplit: killed: residualTaylor polynomial alone exceeds final slope at the center
- rowsProductBudgetRefinement: not a closure path while it preserves the independent product-budget style
- centeredTaylorFactorDerivativeRoute: checked adapter/pattern but budget-killed at current constants; use STEP33_A1_SUB0_CENTERED_TAYLOR_FACTOR_MAJORANT_ORDER16_BUDGET_CONSTANT_FAIL
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

- recommendation: `build the proof-grade whole-expression interval certificate for ComponentSource - NonzeroModelPoly in the active nonzero-model scaled-remainder normalization; the current centered-Taylor factor-derivative route is checked as a pattern but budget-killed`
- firstFailureIfMissing: `STEP33_A1_SUB0_COMBINED_ORDER16_SCALED_REMAINDER_NONZERO_MODEL_INTERVAL_CERT_GAP`
- leanPayloadTarget: `Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16ScaledRemainderDirectPayload.lean`
- checkerTheorem: `primaryFiniteRow0Parent0Split100Sub0_combinedOrder16ScaledRemainder_nonzeroModel_interval_generated`
- remainingGap: `STEP33_A1_SUB0_COMBINED_ORDER16_SCALED_REMAINDER_NONZERO_MODEL_INTERVAL_CERT_GAP`
- nextRouteLevelGapAfterSuccess: `STEP33_A1_SUB0_COMBINED_ORDER16_BIASED_RESIDUAL_HORNER_REMAINDER_ROWS_GAP`
- killedAlternative: `STEP33_A1_SUB0_CENTERED_TAYLOR_FACTOR_MAJORANT_ORDER16_BUDGET_CONSTANT_FAIL`
- doNot:
  - do not build C1 point-separation first
  - do not use sampled/probe rows
  - do not revive component triangle/product split
  - do not reuse OmegaPrime payload as a certificate for the whole expression
  - do not mark Valid/finalBudgetPassed before Lean-checked rows
  - do not call coarse singleAbs rows tight; they are only proof-grade intervals
  - do not treat active-actual product row intervals as a SourceIntervalCert.Valid payload
  - do not treat center-jet abs rows as a SourceIntervalCert.Valid payload
  - do not treat the order16 structural reduction as a numeric bound
  - do not treat the factor-derivative receiver as a concrete closure payload
  - do not spend the centered-Taylor factor-majorant route at current constants; it is budget-killed
  - do not mark Valid/finalBudgetPassed before order16, Horner, and target-budget rows are checked

## Failure Codes

- `STEP33_A1_SUB0_COMBINED_CANCELLATION_HIGH_ORDER_VALID_PAYLOAD_GAP`
- `STEP33_A1_SUB0_COMBINED_CANCELLATION_HIGH_ORDER_TAYLOR_RECEIVER_GAP`
- `STEP33_A1_SUB0_COMBINED_CANCELLATION_CENTER_JETS_ORDER16_PAYLOAD_GAP`
- `STEP33_A1_SUB0_COMPONENT_PRODUCT_ACTUAL_SINGLEABS_TO_SIGNED_CENTERJET_CROSSWALK_GAP`
- `STEP33_A1_SUB0_COMPONENT_PRODUCT_ACTUAL_SIGNED_FACTOR_JET_ROWS_GAP`
- `STEP33_A1_SUB0_ACTIVE_ACTUAL_FACTOR_INTERVAL_TO_ROW_RECEIVER_GAP`
- `STEP33_A1_SUB0_ACTIVE_ACTUAL_PRODUCT_ROW_INTERVALS_GAP`
- `STEP33_A1_SUB0_COMBINED_CANCELLATION_SIGNED_ROWS_TO_CENTERJET_ABS_GAP`
- `STEP33_A1_SUB0_COMPONENT_PRODUCT_ACTUAL_FACTOR_DERIVATIVE_BOUNDS_0_TO_16_GAP`
- `STEP33_A1_SUB0_CENTERED_TAYLOR_FACTOR_MAJORANT_ORDER16_BUDGET_CONSTANT_FAIL`
- `STEP33_A1_SUB0_COMPONENT_PRODUCT_ACTUAL_FACTOR_DERIVATIVE_BUDGET_CONSTANT_FAIL`
- `STEP33_A1_SUB0_COMBINED_CANCELLATION_ORDER16_SOURCE_INTERVAL_PAYLOAD_GAP`
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
- `Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationSourceNormalForm.lean`: `154d430ef1dc8eef`
- `Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16FactorMajorant.lean`: `f405fe44902d592b`
- `Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16FactorDerivativeReceiver.lean`: `b2aa17bf2f805083`
- `Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationFactorDerivativeMajorantBridge.lean`: `15747c8075590c1b`
- `Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16BudgetPayload.lean`: `cb2e4601f2ad6425`
- `Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationActiveActualCenterJetRowsPayload.lean`: `724577b57337b00d`
- `Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationCenterJetPayload.lean`: `9d7e6b13254e7482`
- `Q3/Proofs/PSD_CenteredCoeffRawOmegaAComponentTaylorCancellationBoundInputs.lean`: `c8832f56435b42fa`
- `Q3/Proofs/PSD_CenteredCoeffRawOmegaAComponentTaylorCancellationNormReceiver.lean`: `8554b282c60d9c25`
- `Q3/Proofs/PSD_CenteredCoeffRawOmegaAComponentTaylorCancellationP45Bridge.lean`: `aabf02168d6d50fd`
- `Q3/Proofs/PSD_CenteredCoeffRawOmegaAHRawLanding.lean`: `3074c575ace73694`
- `Q3/Proofs/PSD_CenteredCoeffRawOmegaAComponentTaylorCoeffAssemblyPayload.lean`: `b143a7bacb1c90fd`
- `ACTIVE/requests/step33_bootstrap/step33_a1_sub0_component_assembly_stream_ledger.json`: `83da8ec8067da8a7`
- `ACTIVE/requests/step33_bootstrap/step33_a1_sub0_omega_prime_taylor_payload.json`: `d76ad77551996b39`
- `ACTIVE/requests/step33_bootstrap/step33_a1_sub0_segmented_residual_deriv_interval_payload.json`: `df8cb8dff74f605e`
