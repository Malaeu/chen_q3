# Step33A.1-A Direct Scaled-Remainder Payload Ledger

schema: `q3_psdpd_step33_a1_sub0_combined_order16_scaled_remainder_direct_payload.v18`
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
- directHornerReceiverPresent: `True`
- directHornerSmokePresent: `True`
- directSourceBridgePresent: `True`
- directHornerSourceBridgePresent: `True`
- nominalPolynomialBridgePresent: `True`
- activeActualRemainderBridgePresent: `True`
- activeActualRemainderBridgeLeanChecked: `True`
- activeActualHornerSegmentReceiverPresent: `True`
- activeActualHornerSegmentReceiverLeanChecked: `True`
- activeActualHornerFamilyBridgePresent: `True`
- activeActualHornerFamilyBridgeLeanChecked: `True`
- biasedSourceHornerPresent: `False`
- biasedResidualSourceSegmentPresent: `True`
- biasedSignedFactorAdapterPresent: `True`
- viaBiasedResidualBridgePresent: `True`
- directNonzeroModelIntervalRowsLeanChecked: `False`
- directNonzeroModelSourcePropLeanChecked: `False`
- directHornerRowsLeanChecked: `False`
- zeroModelPayloadTargetLeanChecked: `True`
- step33A1ClosedClaimed: `False`
- doNotSplitSummands: `True`
- doNotUseIndependentSummandBudgets: `True`
- rowWorklistEmitted: `True`
- rowWorklistFile: `ACTIVE/requests/step33_bootstrap/step33_a1_sub0_combined_order16_scaled_remainder_direct_row_obligations.json`
- rowSourceAuditEmitted: `True`
- rowSourceAuditFile: `ACTIVE/requests/step33_bootstrap/step33_a1_sub0_combined_order16_scaled_remainder_direct_row_source_audit.json`
- rowSourceAuditMarkdownFile: `ACTIVE/requests/step33_bootstrap/step33_a1_sub0_combined_order16_scaled_remainder_direct_row_source_audit.md`
- firstMissingProofObject: `primaryFiniteRow0Parent0Split100Sub0_combinedOrder16ScaledRemainder_nonzeroModel_interval_generated`
- firstRowFailureCode: `STEP33_A1_SUB0_COMBINED_ORDER16_SCALED_REMAINDER_DIRECT_ROW_SOURCE_GAP`
- firstConcreteUpstreamFailureCode: `STEP33_A1_SUB0_ACTIVE_ACTUAL_ORDER16_SEGMENT_REMAINDER_ROW_SOURCE_GAP`

## Current Gap

`STEP33_A1_SUB0_COMBINED_ORDER16_SCALED_REMAINDER_NONZERO_MODEL_INTERVAL_CERT_GAP`

Parent gap:

`STEP33_A1_SUB0_COMBINED_ORDER16_BIASED_RESIDUAL_HORNER_SCALED_REMAINDER_BOUND_GAP`

First failure code if the direct route fails:

`STEP33_A1_SUB0_COMBINED_ORDER16_SCALED_REMAINDER_NONZERO_MODEL_INTERVAL_CERT_GAP`

First row-source failure code if the row generator fails:

`STEP33_A1_SUB0_COMBINED_ORDER16_SCALED_REMAINDER_DIRECT_ROW_SOURCE_GAP`

Bias-shift bridge failure code if the adapter breaks:

`STEP33_A1_SUB0_COMBINED_ORDER16_BIASED_RESIDUAL_TO_DIRECT_TARGET_BIAS_SHIFT_GAP`

Bias-shift budget failure code for the current direct budget:

`STEP33_A1_SUB0_COMBINED_ORDER16_BIASED_RESIDUAL_TO_DIRECT_TARGET_BIAS_BUDGET_FAIL`

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

## Direct Horner Row Route Review

- used: `True`
- destination: `in-app ChatGPT Pro / Louise browser`
- recommended option: `B`
- decision: `order16_shifted_residual_direct_horner_rows`
- first file to edit: `scripts/generate_step33_a1_sub0_combined_order16_scaled_remainder_direct_payload.py`
- first Lean file when rows pass: `Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16ScaledRemainderDirectConcretePayload.lean`
- first object: `primaryFiniteRow0Parent0Split100Sub0CombinedOrder16ScaledRemainderDirectHornerData`
- valid theorem: `primaryFiniteRow0Parent0Split100Sub0_combinedOrder16ScaledRemainderDirectHorner_valid`
- final theorem: `primaryFiniteRow0Parent0Split100Sub0_combinedOrder16ScaledRemainder_nonzeroModel_interval_generated`
- theorem shape: for all eta in Set.Icc 0 (1/10), -R <= ComponentSource eta - NonzeroModelPoly eta and ComponentSource eta - NonzeroModelPoly eta <= R, with R = CombinedOrder16BiasedResidualRemainderAbs
- failure code if fails: `STEP33_A1_SUB0_COMBINED_ORDER16_SCALED_REMAINDER_DIRECT_ROW_SOURCE_GAP`
- proof claim allowed now: `False`
- reason: The coarse P45 source exists but its spendable budget is Lean-killed.  The order16 direct receiver subtracts NonzeroModelPoly and preserves the needed cancellation, so it is the smallest proof-grade route for the current gate.

Required rows:

- exact segment cover
- same-target rational polynomial coefficients
- Lean-checked Horner stage bounds
- proof-grade whole-expression remainder rows
- exact final +/- R budget rows

## Direct Split Identity

- theorem: `primaryFiniteRow0Parent0Split100Sub0_combinedOrder16Source_sub_nonzeroModelPoly`
- file: `Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16NonzeroModel.lean`
- present: `True`
- leftHandSide: `primaryFiniteRow0Parent0Split100Sub0CombinedCancellationOrder16ComponentSource eta - primaryFiniteRow0Parent0Split100Sub0CombinedOrder16NonzeroModelPoly eta`
- rightHandSide: `primaryFiniteRow0Parent0Split100Sub0ActiveScaleCoeff * iteratedDeriv 16 primaryFiniteRow0Parent0Split100Sub0ComponentProductCancellationResidual eta + (primaryFiniteRow0Parent0Split100Sub0ActiveScaleCoeff - (primaryFiniteRow0Parent0Split100Sub0NominalScaleCoeff : Real)) * iteratedDeriv 16 primaryFiniteRow0Parent0Split100Sub0ComponentProductNominal eta`
- collapsedWholeExpressionRhs: `primaryFiniteRow0Parent0Split100Sub0ActiveScaleCoeff * iteratedDeriv 16 primaryFiniteRow0Parent0Split100Sub0ComponentProductActual eta - (primaryFiniteRow0Parent0Split100Sub0NominalScaleCoeff : Real) * iteratedDeriv 16 primaryFiniteRow0Parent0Split100Sub0ComponentProductNominal eta`
- receiverField: `Step33Sub0CombinedOrder16ScaledRemainderDirectHornerCert.Valid.directRemainder`
- usableAsRowSourceCrosswalk: `True`
- proofGradeRowsPresent: `False`
- budgetSpendAllowed: `False`
- guard: This identity is bookkeeping/crosswalk evidence only until a generator supplies proof-grade directRemainder rows and final budget rows.  It does not itself prove the interval.

## Split Summands Policy

- algebraicSplitAllowedForRowSource: `True`
- independentNormSpendAllowed: `False`
- finalReceiverTargetMustBeWholeExpression: `True`
- proshkaFollowupDecision: `CHOSEN: C`
- oneCoefficientStreamRequired: `True`
- reason: The local Lean split names the exact target expression, but the proof-grade row object must still be one coefficient stream for the complete signed expression.  The nominal polynomial bridge is allowed only as a coefficient crosswalk; separate product-summand budgets are not spendable, because they revive the killed triangle-loss route.

## Direct Whole-Expression Row Review

- recommended option: `C`
- decision: `fail_closed_collapsed_row_source_audit`
- first file to edit: `scripts/generate_step33_a1_sub0_combined_order16_scaled_remainder_direct_payload.py`
- first Lean file when rows pass: `Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16ScaledRemainderDirectConcretePayload.lean`
- first object: `primaryFiniteRow0Parent0Split100Sub0CombinedOrder16ScaledRemainderDirectHornerData`
- row theorem: `primaryFiniteRow0Parent0Split100Sub0_combinedOrder16ScaledRemainder_collapsed_segment_remainder`
- row theorem shape: for every segment, norm of collapsedExpression eta minus the segment polynomial is at most polyErrorAbs; the existing Lean bridge then transports that row into directRemainder
- collapsed expression: `primaryFiniteRow0Parent0Split100Sub0ActiveScaleCoeff * iteratedDeriv 16 primaryFiniteRow0Parent0Split100Sub0ComponentProductActual eta - (primaryFiniteRow0Parent0Split100Sub0NominalScaleCoeff : Real) * iteratedDeriv 16 primaryFiniteRow0Parent0Split100Sub0ComponentProductNominal eta`
- failure code if fails: `STEP33_A1_SUB0_COMBINED_ORDER16_SCALED_REMAINDER_DIRECT_ROW_SOURCE_GAP`
- proof claim allowed now: `False`

Required rows:

- exact collapse from cancellation+scale-mismatch split to activeActual-minus-nominal form (checked in DirectSourceBridge)
- one rational coefficient stream for the complete signed expression
- proof-grade collapsedExpression segment remainder row
- exact Horner stageLower/stageUpper rows
- exact [0,1/10] coverage
- final +/- BiasedResidualRemainderAbs budget rows

Do not produce:

- DirectConcretePayload.lean before the collapsed segment remainder theorem exists
- separate error budgets for the two split summands
- triangle-loss resurrection of the killed factor-majorant route
- biased residual/local-model detour before this row source is killed

## Direct Row-Source Implementation Review

- usedComputerUse: `True`
- advisoryOnly: `True`
- recommended option: `A_for_partial_nominal_bridge_then_fail_closed_rows`
- decision label: `CHOSEN: A`
- first file to create: `Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16NominalPolynomialBridge.lean`
- audit object: `primaryFiniteRow0Parent0Split100Sub0CombinedOrder16ScaledRemainderCollapsedRowSourceAudit`
- audit object is Lean theorem: `False`
- first Lean payload when rows exist: `Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16ScaledRemainderDirectConcretePayload.lean`
- first Lean data object when rows exist: `primaryFiniteRow0Parent0Split100Sub0CombinedOrder16ScaledRemainderDirectHornerData`
- first Lean validity theorem when rows exist: `primaryFiniteRow0Parent0Split100Sub0_combinedOrder16ScaledRemainderDirectHorner_valid`
- coefficient source status: `PARTIAL_NOMINAL_POLY_BRIDGE_PRESENT_COMPLETE_STREAM_ABSENT`
- partial bridge file: `Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16NominalPolynomialBridge.lean`
- partial bridge theorem: `primaryFiniteRow0Parent0Split100Sub0_combinedOrder16CollapsedExpression_eq_activeActual_sub_nominalOrder16Poly`
- missing theorem: `primaryFiniteRow0Parent0Split100Sub0_combinedOrder16ScaledRemainder_collapsed_segment_remainder`
- failure code if rows missing: `STEP33_A1_SUB0_COMBINED_ORDER16_SCALED_REMAINDER_DIRECT_ROW_SOURCE_GAP`
- proof claim allowed now: `False`
- step33A1ClosedClaimed: `False`

Decision:

Add the partial nominal polynomial coefficient bridge, but keep the direct row generator fail-closed until a single proof-grade whole-expression coefficient/remainder row exists for collapsedExpression.

Coefficient-source notes:

- primaryFiniteRow0Parent0Split100Sub0ResidualTaylorCoeff is a model coefficient source, not the direct collapsed-expression residual coefficient stream.
- primaryFiniteRow0Parent0Split100Sub0CombinedOrder16NonzeroModelCoeff is the already-subtracted model coefficient source, not coefficients for ComponentSource - NonzeroModelPoly.
- The nominal polynomial bridge extracts the rational nominal subtracted polynomial only; it is not a complete coefficient stream for collapsedExpression.
- The checked collapse and nominal polynomial bridge do not produce Horner rows or an analytic remainder bound.

Missing theorem statement:

```lean
theorem primaryFiniteRow0Parent0Split100Sub0_combinedOrder16ScaledRemainder_collapsed_segment_remainder
    (i : Fin segmentCount) :
    forall eta in Set.Icc (cellL i : Real) (cellU i : Real),
      norm (primaryFiniteRow0Parent0Split100Sub0CombinedOrder16ScaledRemainderCollapsedExpression eta -
        rawOmegaATaylorPolynomial degree (center i) (coeff i) eta) <=
      (polyErrorAbs i : Real)
```

## Active-Actual Remainder Adapter

- file: `Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16ActiveActualRemainderBridge.lean`
- present: `True`
- Lean checked this run: `True`
- closed subgap: `STEP33_A1_SUB0_COMBINED_ORDER16_ACTIVE_ACTUAL_NOMINAL_POLY_ALIGNMENT_CLOSED`
- next missing theorem: `primaryFiniteRow0Parent0Split100Sub0_activeActual_order16_segment_remainder`
- next failure code if rows are still missing: `STEP33_A1_SUB0_ACTIVE_ACTUAL_ORDER16_SEGMENT_REMAINDER_ROW_SOURCE_GAP`

Meaning: a future proof-grade scaled-active-actual segment approximation can be transported to the collapsed-expression remainder row by subtracting `nominalOrder16Poly` inside the same coefficient stream.  This is not a row certificate and does not close Step33A.1-A.

## Active-Actual Horner Segment Receiver

- file: `Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16ActiveActualHornerSegmentCert.lean`
- present: `True`
- Lean checked this run: `True`
- conditional activeActual theorem: `primaryFiniteRow0Parent0Split100Sub0_activeActual_order16_segment_remainder_of_horner_cert`
- collapsed receiver theorem: `primaryFiniteRow0Parent0Split100Sub0_collapsed_segment_remainder_of_activeActualHorner`
- next failure code if rows are still missing: `STEP33_A1_SUB0_ACTIVE_ACTUAL_ORDER16_SEGMENT_REMAINDER_ROW_SOURCE_GAP`

Meaning: a future proof-grade activeActual Horner row can now feed the checked activeActual/nominal adapter.  This receiver is conditional and supplies no concrete coefficients or interval row data.

## Active-Actual Horner Family Bridge

- file: `Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16ActiveActualHornerFamilyBridge.lean`
- present: `True`
- Lean checked this run: `True`
- conditional family theorem: `primaryFiniteRow0Parent0Split100Sub0_directHornerFamily_valid_of_activeActualHornerFamily`
- conditional payload theorem: `primaryFiniteRow0Parent0Split100Sub0_directPayloadTarget_of_activeActualHornerFamily`
- next failure code if rows are still missing: `STEP33_A1_SUB0_ACTIVE_ACTUAL_ORDER16_SEGMENT_REMAINDER_ROW_SOURCE_GAP`
- failure code if this bridge breaks: `STEP33_A1_SUB0_ACTIVE_ACTUAL_ORDER16_HORNER_FAMILY_ALIGNMENT_GAP`

Meaning: valid activeActual Horner segment rows can now be packaged as the existing DirectHorner family receiver expects.  This is a conditional bridge only; the activeActual segment rows, Horner range rows, cover rows, and budget rows are still missing.

## Active-Actual Horner Row-Source Ledger

- file: `ACTIVE/requests/step33_bootstrap/step33_a1_sub0_active_actual_horner_row_source.json`
- exists: `True`
- schema: `q3_psdpd_step33_a1_sub0_active_actual_horner_row_source.v2`
- proofStatus: `interface_ready_rows_missing`
- proofGrade: `False`
- proofSafeClosedFields: `0`
- outLeanWritten: `False`
- firstFailureCode: `STEP33_A1_SUB0_ACTIVE_ACTUAL_ORDER16_SEGMENT_REMAINDER_ROW_SOURCE_GAP`

Meaning: this is the fail-closed generator contract selected by Computer Use / Proshka.  It records the exact segment/family/range/budget rows required before any activeActual Horner payload may be written; it is not a proof object.

Minimal row data:

- exact segment cover
- proof-grade rational coeff[i][j] for the complete collapsed expression
- Lean-checked Horner stage lower/upper bounds
- primaryFiniteRow0Parent0Split100Sub0_combinedOrder16ScaledRemainder_collapsed_segment_remainder for every segment
- exact final +/- BiasedResidualRemainderAbs budget rows

Do not reuse:

- killed factor majorants
- P45/fullTaylor wrong target
- zero-model budget
- center jets as uniform bounds
- sampled rows
- separate actual/nominal norm budgets
- nominalOrder16Poly as an independent spendable budget

Route options rejected:

- why no DirectConcretePayload yet: The partial nominal polynomial bridge is not the full collapsedExpression coefficient stream and does not prove the collapsed-segment remainder theorem.
- whyNotB: B is already subsumed by Step33Sub0CombinedOrder16ScaledRemainderDirectHornerCert.Valid.of_collapsed_horner_range; adding another alias is not the first proof-producing row source.
- whyNotD: The route is not impossible; the exact missing proof-row source is now named.

## Biased Residual Reuse Review

- reuse: `YES_WITH_EXPLICIT_BIAS_SHIFT`
- decision: `reuse_biased_residual_source_segment_receiver_via_checked_bias_shift`
- current budget verdict: `KILLED_FOR_CANONICAL_DIRECT_R`
- bridge file: `Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16ScaledRemainderViaBiasedResidualPayload.lean`
- source segment file: `Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16BiasedResidualInterval.lean`
- Lean bridge checked: `True`
- first generator patch: `scripts/generate_step33_a1_sub0_combined_order16_scaled_remainder_direct_payload.py`
- first Lean payload file: `Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16ScaledRemainderViaBiasedResidualPayload.lean`
- first missing proof-grade row: `the direct whole-expression row; the biased-residual reuse route is killed by DirectR < BiasRat`
- failure code if bridge missing: `STEP33_A1_SUB0_COMBINED_ORDER16_BIASED_RESIDUAL_TO_DIRECT_TARGET_BIAS_SHIFT_GAP`
- failure code if rows missing: `STEP33_A1_SUB0_COMBINED_ORDER16_SCALED_REMAINDER_DIRECT_ROW_SOURCE_GAP`
- failure code if budget fails: `STEP33_A1_SUB0_COMBINED_ORDER16_BIASED_RESIDUAL_TO_DIRECT_TARGET_BIAS_BUDGET_FAIL`
- budget kill theorem: `primaryFiniteRow0Parent0Split100Sub0_scaledRemainder_biasShift_upperBudget_impossible_of_nonneg`
- proof claim allowed now: `False`
- warning: Source - BiasedModel is not Source - NonzeroModel; the fixed BiasRat shift and the BiasRat +/- biasedAbs budget rows must be checked in the direct target normalization.  In the current canonical budget they fail because DirectR < BiasRat.

Required rows:

- direct whole-expression proof row for ComponentSource - NonzeroModelPoly
- exact bias shift theorem from direct residual to biased residual
- budget-kill theorem showing DirectR < BiasRat
- fallback exact segment cover/Horner rows for the direct target

## Post-Budget-Kill Route Review

- decision: `CHOSEN: A`
- context: The centered-Taylor factor-derivative receiver route was tried as a proof/kill test and is budget-killed by STEP33_A1_SUB0_CENTERED_TAYLOR_FACTOR_MAJORANT_ORDER16_BUDGET_CONSTANT_FAIL.
- answer: Build a proof-grade rational/interval generator for the whole signed expression ComponentSource - NonzeroModelPoly on [0,1/10].  A Horner split is only an implementation technique inside that direct certificate.
- killed factor route: `STEP33_A1_SUB0_CENTERED_TAYLOR_FACTOR_MAJORANT_ORDER16_BUDGET_CONSTANT_FAIL`

## Next Proof-Producing Patch

- generator: `scripts/generate_step33_a1_sub0_combined_order16_scaled_remainder_direct_certificate.py`
- Lean file: `Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16ScaledRemainderDirectConcretePayload.lean`
- theorem: `primaryFiniteRow0Parent0Split100Sub0_combinedOrder16ScaledRemainder_nonzeroModel_interval_generated`
- missing remainder theorem: `primaryFiniteRow0Parent0Split100Sub0_combinedOrder16ScaledRemainder_collapsed_segment_remainder`
- source-prop theorem: `primaryFiniteRow0Parent0Split100Sub0_combinedOrder16ScaledRemainder_nonzeroModel_sourceProp_generated`
- failure code if rows still missing: `STEP33_A1_SUB0_ACTIVE_ACTUAL_ORDER16_SEGMENT_REMAINDER_ROW_SOURCE_GAP`
- proof claim allowed now: `False`

Next implementable patch:

Use the fail-closed activeActual Horner row-source ledger as the generator contract.  The next proof-producing patch must fill it with rational/interval row data satisfying primaryFiniteRow0Parent0Split100Sub0_activeActual_order16_segment_remainder_of_horner_cert; the receiver and adapter then transport it through primaryFiniteRow0Parent0Split100Sub0_directHornerFamily_valid_of_activeActualHornerFamily to primaryFiniteRow0Parent0Split100Sub0_combinedOrder16ScaledRemainder_collapsed_segment_remainder. Do not emit DirectConcretePayload.lean before the transported collapsed rows, Horner rows, and final budget rows exist.

## Why P45/full-Taylor Is Not Enough

The P45/full-Taylor bridge rewrites a derivative-level residual error into the scaled cancellation RHS. The current direct target is the order-16 source residual ComponentSource - NonzeroModelPoly, which Lean identifies with ActiveScaleCoeff * D^16(ComponentProductCancellationResidual) plus the same-unit scale-mismatch nominal-product term. No local theorem converts the P45/full-Taylor interval into this order-16 source interval.

## Theorem Shape

prove a signed interval on [0,1/10] for ComponentSource - NonzeroModelPoly inside +/- BiasedResidualRemainderAbs; then use primaryFiniteRow0Parent0Split100Sub0_combinedOrder16ScaledRemainder_nonzeroModel_sourceProp_of_full_cell_interval or a direct family payload target

## Certificate Shape

- exact target-expression hash/name
- segment cells covering [0,1/10]
- per-segment rational polynomial coefficients if a model is used
- exact Horner stage bounds if a Horner model is used
- proof-grade whole-expression remainder rows
- primaryFiniteRow0Parent0Split100Sub0_combinedOrder16ScaledRemainder_collapsed_segment_remainder for every segment
- final lower/upper budget rows against BiasedResidualRemainderAbs
- the Lean split theorem may be used to generate the row source
- no independent product-summand norm budgets unless recombined into the directRemainder row
- global residualAbs = BiasedResidualRemainderAbs

## Do Not Reuse After Post-Budget-Kill

- centered-Taylor factor majorants killed by exact budget
- P45/full-Taylor machinery: wrong target
- zero-model/direct-source budget
- independent product-summand norm bounds
- center jets as uniform full-cell intervals
- sampled/probe interval rows

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
- `upstreamFailureCode`: `STEP33_A1_SUB0_ACTIVE_ACTUAL_ORDER16_SEGMENT_REMAINDER_ROW_SOURCE_GAP`
- `proofGrade`: `False`

### R2_horner_or_interval_rows

- `object`: `proof-grade rational/interval rows for the assembled signed expression`
- `requiredFor`: `primaryFiniteRow0Parent0Split100Sub0_combinedOrder16ScaledRemainder_nonzeroModel_interval_generated`
- `status`: `direct_horner_receiver_ready_source_bridge_checked_rows_missing`
- `upstreamFailureCode`: `STEP33_A1_SUB0_ACTIVE_ACTUAL_ORDER16_SEGMENT_REMAINDER_ROW_SOURCE_GAP`
- `componentTaylorGapBypassedByDirectHornerRoute`: `False`
- `sourceSplitTheorem`: `primaryFiniteRow0Parent0Split100Sub0_combinedOrder16Source_sub_nonzeroModelPoly`
- `collapsedExpressionBridgeTheorem`: `primaryFiniteRow0Parent0Split100Sub0_combinedOrder16ScaledRemainder_eq_collapsedExpression`
- `collapsedHornerReceiverBridgeTheorem`: `Step33Sub0CombinedOrder16ScaledRemainderDirectHornerCert.Valid.of_collapsed_horner_range`
- `collapsedHornerFamilyBridgeTheorem`: `Step33Sub0CombinedOrder16ScaledRemainderDirectHornerFamilyCert.valid_of_collapsed_horner_rows`
- `receiverField`: `Step33Sub0CombinedOrder16ScaledRemainderDirectHornerCert.Valid.directRemainder`
- `guard`: `The Lean split theorem is allowed as the row-source crosswalk.  With the collapsed Horner source bridge, a future row may prove the remainder against CollapsedExpression and transport it into directRemainder.  The coefficient stream, range rows, and budget rows are still missing.`
- `proofGrade`: `False`

### R2b_biased_residual_bias_shift

- `object`: `reuse biased-residual source-segment bounds through the checked bias-shift bridge`
- `requiredFor`: `primaryFiniteRow0Parent0Split100Sub0_combinedOrder16ScaledRemainder_nonzeroModel_sourceProp_generated`
- `status`: `bias_shift_bridge_checked_but_current_direct_budget_killed`
- `bridgeFile`: `Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16ScaledRemainderViaBiasedResidualPayload.lean`
- `bridgeTheorem`: `primaryFiniteRow0Parent0Split100Sub0_scaledRemainder_nonzeroModel_sourceProp_of_biasedResidual`
- `generalBridgeTheorem`: `primaryFiniteRow0Parent0Split100Sub0_scaledRemainder_nonzeroModel_sourceProp_of_biasedResidualSourceProp`
- `firstMissingProofObject`: `primaryFiniteRow0Parent0Split100Sub0_combinedOrder16ScaledRemainder_wholeExpression_row`
- `missingRows`: `['direct whole-expression row for ComponentSource - NonzeroModelPoly', 'exact lower bias budget: -DirectR <= BiasRat - biasedAbs', 'exact upper bias budget: BiasRat + biasedAbs <= DirectR']`
- `failureCode`: `STEP33_A1_SUB0_COMBINED_ORDER16_BIASED_RESIDUAL_TO_DIRECT_TARGET_BIAS_BUDGET_FAIL`
- `biasShiftFailureCode`: `STEP33_A1_SUB0_COMBINED_ORDER16_BIASED_RESIDUAL_TO_DIRECT_TARGET_BIAS_SHIFT_GAP`
- `budgetKillTheorem`: `primaryFiniteRow0Parent0Split100Sub0_scaledRemainder_biasShift_upperBudget_impossible_of_nonneg`
- `proofGrade`: `False`

### R3_budget_rows

- `object`: `lowerBudget and upperBudget against BiasedResidualRemainderAbs, including bias-shift rows if using the biased-residual receiver`
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

### direct_collapsed_expression_source_bridge

- `file`: `Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16ScaledRemainderDirectSourceBridge.lean`
- `surfacePresent`: `True`
- `verdict`: `usable_source_bridge_no_interval_rows`
- `failureCode`: `STEP33_A1_SUB0_COMBINED_ORDER16_SCALED_REMAINDER_DIRECT_ROW_SOURCE_GAP`

### biased_source_horner

- `file`: `Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16BiasedResidualSourceHornerCert.lean`
- `surfacePresent`: `False`
- `verdict`: `not_same_target_without_new_bridge`
- `failureCode`: `STEP33_A1_SUB0_COMBINED_ORDER16_SCALED_REMAINDER_NONZERO_MODEL_INTERVAL_CERT_GAP`

### biased_residual_source_segments_via_bias_shift

- `file`: `Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16ScaledRemainderViaBiasedResidualPayload.lean`
- `sourceSegmentFile`: `Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16BiasedResidualInterval.lean`
- `surfacePresent`: `True`
- `sourceSegmentReceiverPresent`: `True`
- `verdict`: `checked_bridge_but_canonical_direct_budget_killed_by_bias_shift`
- `firstMissingProofObject`: `primaryFiniteRow0Parent0Split100Sub0_combinedOrder16ScaledRemainder_wholeExpression_row`
- `failureCode`: `STEP33_A1_SUB0_COMBINED_ORDER16_BIASED_RESIDUAL_TO_DIRECT_TARGET_BIAS_BUDGET_FAIL`
- `biasShiftFailureCode`: `STEP33_A1_SUB0_COMBINED_ORDER16_BIASED_RESIDUAL_TO_DIRECT_TARGET_BIAS_SHIFT_GAP`
- `budgetKillTheorem`: `primaryFiniteRow0Parent0Split100Sub0_scaledRemainder_biasShift_upperBudget_impossible_of_nonneg`

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

### direct_horner_receiver

- `file`: `Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16ScaledRemainderDirectHornerCert.lean`
- `smokeFile`: `Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16ScaledRemainderDirectHornerCertSmoke.lean`
- `artifactStatus`: `lean_receiver_present_smoke_present`
- `sameTarget`: `True`
- `proofGradeRowsPresent`: `False`
- `spendableForCurrentTarget`: `False`
- `reason`: `The receiver can consume order16 shifted-residual direct Horner rows for ComponentSource - NonzeroModelPoly, but no concrete segment data, Horner stage bounds, or proof-grade remainder rows exist yet.`
- `firstMissingProofObject`: `primaryFiniteRow0Parent0Split100Sub0_combinedOrder16ScaledRemainder_nonzeroModel_interval_generated`
- `failureCode`: `STEP33_A1_SUB0_COMBINED_ORDER16_SCALED_REMAINDER_DIRECT_ROW_SOURCE_GAP`

### direct_collapsed_expression_source_bridge

- `file`: `Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16ScaledRemainderDirectSourceBridge.lean`
- `artifactStatus`: `lean_source_bridge_present`
- `sameTarget`: `True`
- `proofGradeRowsPresent`: `False`
- `spendableForCurrentTarget`: `False`
- `reason`: `The exact collapse from ComponentSource - NonzeroModelPoly to one activeActual-minus-nominal expression is checked, and a proof-grade full-cell interval for that collapsed expression can feed the direct source proposition.  No Horner, remainder, or final budget rows are supplied by this bridge.`
- `closedSubgap`: `STEP33_A1_SUB0_COMBINED_ORDER16_SCALED_REMAINDER_DIRECT_COLLAPSE_BRIDGE_CLOSED`
- `firstMissingProofObject`: `primaryFiniteRow0Parent0Split100Sub0_combinedOrder16ScaledRemainder_nonzeroModel_interval_generated`
- `failureCode`: `STEP33_A1_SUB0_COMBINED_ORDER16_SCALED_REMAINDER_DIRECT_ROW_SOURCE_GAP`

### direct_horner_collapsed_expression_source_bridge

- `file`: `Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16ScaledRemainderDirectHornerSourceBridge.lean`
- `artifactStatus`: `lean_collapsed_horner_receiver_bridge_present`
- `sameTarget`: `True`
- `proofGradeRowsPresent`: `False`
- `spendableForCurrentTarget`: `False`
- `reason`: `A Lean-checked receiver bridge now transports a proof-grade collapsedExpression Horner remainder row into the existing directRemainder field.  It still supplies no coefficients, no Horner range rows, and no final budget rows.`
- `closedSubgap`: `STEP33_A1_SUB0_COMBINED_ORDER16_SCALED_REMAINDER_DIRECT_HORNER_COLLAPSED_SOURCE_BRIDGE_CLOSED`
- `firstMissingProofObject`: `primaryFiniteRow0Parent0Split100Sub0_combinedOrder16ScaledRemainder_collapsed_segment_remainder`
- `failureCode`: `STEP33_A1_SUB0_COMBINED_ORDER16_SCALED_REMAINDER_DIRECT_ROW_SOURCE_GAP`

### nominal_polynomial_bridge

- `file`: `Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16NominalPolynomialBridge.lean`
- `artifactStatus`: `lean_nominal_polynomial_bridge_present`
- `sameTarget`: `True`
- `proofGradeRowsPresent`: `False`
- `spendableForCurrentTarget`: `False`
- `reason`: `The Lean bridge extracts the rational nominal order-16 polynomial and rewrites collapsedExpression as activeActual minus nominalOrder16Poly.  This is a coefficient crosswalk only; the generator still needs one proof-grade whole-expression collapsed segment remainder row.`
- `closedSubgap`: `STEP33_A1_SUB0_COMBINED_ORDER16_NOMINAL_POLY_COEFF_CROSSWALK_CLOSED`
- `firstMissingProofObject`: `primaryFiniteRow0Parent0Split100Sub0_combinedOrder16ScaledRemainder_collapsed_segment_remainder`
- `failureCode`: `STEP33_A1_SUB0_COMBINED_ORDER16_SCALED_REMAINDER_DIRECT_ROW_SOURCE_GAP`

### active_actual_remainder_bridge

- `file`: `Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16ActiveActualRemainderBridge.lean`
- `artifactStatus`: `lean_active_actual_remainder_adapter_present`
- `sameTarget`: `True`
- `proofGradeRowsPresent`: `False`
- `spendableForCurrentTarget`: `False`
- `reason`: `The Lean adapter transports a future proof-grade approximation for scaled D^16(ComponentProductActual) into the collapsed expression remainder by subtracting nominalOrder16Poly inside one coefficient stream.  It still supplies no activeActual coefficients, no analytic remainder theorem, no Horner rows, and no final budget rows.`
- `closedSubgap`: `STEP33_A1_SUB0_COMBINED_ORDER16_ACTIVE_ACTUAL_NOMINAL_POLY_ALIGNMENT_CLOSED`
- `firstMissingProofObject`: `primaryFiniteRow0Parent0Split100Sub0_activeActual_order16_segment_remainder`
- `missingCollapsedRemainderTheorem`: `primaryFiniteRow0Parent0Split100Sub0_combinedOrder16ScaledRemainder_collapsed_segment_remainder`
- `failureCode`: `STEP33_A1_SUB0_ACTIVE_ACTUAL_ORDER16_SEGMENT_REMAINDER_SOURCE_GAP`
- `failureCodeIfAdapterBreaks`: `STEP33_A1_SUB0_COMBINED_ORDER16_ACTIVE_ACTUAL_NOMINAL_POLY_ALIGNMENT_GAP`

### active_actual_horner_segment_receiver

- `file`: `Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16ActiveActualHornerSegmentCert.lean`
- `artifactStatus`: `lean_active_actual_horner_segment_receiver_present`
- `sameTarget`: `True`
- `proofGradeRowsPresent`: `False`
- `spendableForCurrentTarget`: `False`
- `reason`: `The Lean receiver fixes the exact future row contract for scaled D^16(ComponentProductActual): degree-29 coefficients centered at 1/20 plus a proof-grade `remainderBound`.  It transports a valid activeActual row through the checked activeActual-to-collapsed adapter, but still supplies no concrete coefficients or interval/rational row source.`
- `closedSubgap`: `STEP33_A1_SUB0_ACTIVE_ACTUAL_ORDER16_HORNER_SEGMENT_RECEIVER_CLOSED`
- `firstMissingProofObject`: `primaryFiniteRow0Parent0Split100Sub0_activeActual_order16_segment_remainder`
- `conditionalReceiverTheorem`: `primaryFiniteRow0Parent0Split100Sub0_activeActual_order16_segment_remainder_of_horner_cert`
- `collapsedReceiverTheorem`: `primaryFiniteRow0Parent0Split100Sub0_collapsed_segment_remainder_of_activeActualHorner`
- `missingCollapsedRemainderTheorem`: `primaryFiniteRow0Parent0Split100Sub0_combinedOrder16ScaledRemainder_collapsed_segment_remainder`
- `failureCode`: `STEP33_A1_SUB0_ACTIVE_ACTUAL_ORDER16_SEGMENT_REMAINDER_ROW_SOURCE_GAP`
- `failureCodeIfReceiverMissing`: `STEP33_A1_SUB0_ACTIVE_ACTUAL_ORDER16_HORNER_SEGMENT_RECEIVER_GAP`

### active_actual_horner_family_bridge

- `file`: `Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16ActiveActualHornerFamilyBridge.lean`
- `artifactStatus`: `lean_active_actual_horner_family_bridge_present`
- `sameTarget`: `True`
- `proofGradeRowsPresent`: `False`
- `spendableForCurrentTarget`: `False`
- `reason`: `The Lean bridge packages valid activeActual Horner segment rows as the existing DirectHorner family receiver expects them, using the checked collapsed coefficient stream.  It still supplies no activeActual coefficients, no Horner range rows, no segment cover rows, and no final budget rows.`
- `closedSubgap`: `STEP33_A1_SUB0_ACTIVE_ACTUAL_ORDER16_HORNER_FAMILY_BRIDGE_CLOSED`
- `conditionalFamilyTheorem`: `primaryFiniteRow0Parent0Split100Sub0_directHornerFamily_valid_of_activeActualHornerFamily`
- `conditionalPayloadTheorem`: `primaryFiniteRow0Parent0Split100Sub0_directPayloadTarget_of_activeActualHornerFamily`
- `firstMissingProofObject`: `primaryFiniteRow0Parent0Split100Sub0_activeActual_order16_segment_remainder`
- `missingCollapsedRemainderTheorem`: `primaryFiniteRow0Parent0Split100Sub0_combinedOrder16ScaledRemainder_collapsed_segment_remainder`
- `failureCode`: `STEP33_A1_SUB0_ACTIVE_ACTUAL_ORDER16_SEGMENT_REMAINDER_ROW_SOURCE_GAP`
- `failureCodeIfBridgeMissing`: `STEP33_A1_SUB0_ACTIVE_ACTUAL_ORDER16_HORNER_FAMILY_ALIGNMENT_GAP`

### biased_residual_source_segment_receiver_via_bias_shift

- `file`: `Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16ScaledRemainderViaBiasedResidualPayload.lean`
- `sourceSegmentFile`: `Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16BiasedResidualInterval.lean`
- `artifactStatus`: `lean_bias_shift_bridge_checked`
- `sameTarget`: `True`
- `proofGradeRowsPresent`: `False`
- `spendableForCurrentTarget`: `False`
- `reason`: `The checked bridge converts a biased-residual source-segment bound into the direct ComponentSource - NonzeroModelPoly payload, but the canonical direct budget cannot absorb the positive BiasRat shift: DirectR < BiasRat.`
- `firstMissingProofObject`: `primaryFiniteRow0Parent0Split100Sub0_combinedOrder16ScaledRemainder_wholeExpression_row`
- `failureCode`: `STEP33_A1_SUB0_COMBINED_ORDER16_BIASED_RESIDUAL_TO_DIRECT_TARGET_BIAS_BUDGET_FAIL`
- `biasShiftFailureCode`: `STEP33_A1_SUB0_COMBINED_ORDER16_BIASED_RESIDUAL_TO_DIRECT_TARGET_BIAS_SHIFT_GAP`
- `budgetKillTheorem`: `primaryFiniteRow0Parent0Split100Sub0_scaledRemainder_biasShift_upperBudget_impossible_of_nonneg`

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

## Upstream Row-Source Audit

- directFailureCode: `STEP33_A1_SUB0_COMBINED_ORDER16_SCALED_REMAINDER_DIRECT_ROW_SOURCE_GAP`
- firstConcreteUpstreamFailureCode: `STEP33_A1_SUB0_COMPONENT_TAYLOR_REMAINDER_SOURCE_GAP`
- componentTaylorRemainderGapActive: `True`
- verdict: ShapeSqDeriv tight same-coefficient payload is checked support, but it is not a final residual interval.  The current upstream proof-source gap is the component Taylor remainder source.
- nextImplementablePatch: Build the component Taylor remainder source consumed by exact raw-derivative assembly, then regenerate the direct nonzero-model scaled-remainder certificate.

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
- `primaryFiniteRow0Parent0Split100Sub0ActiveScaleCoeff`: `True`
- `primaryFiniteRow0Parent0Split100Sub0NominalScaleCoeff`: `True`
- `primaryFiniteRow0Parent0Split100Sub0ComponentProductCancellationResidual`: `True`
- `primaryFiniteRow0Parent0Split100Sub0ComponentProductNominal`: `True`

## Direct Interval Payload Symbols

- `primaryFiniteRow0Parent0Split100Sub0CombinedCancellationOrder16DirectIntervalTarget`: `True`
- `Step33Sub0CombinedCancellationOrder16DirectIntervalCert`: `True`
- `primaryFiniteRow0Parent0Split100Sub0_combinedCancellation_order16_direct_interval_to_source_field`: `True`

## Direct Model Payload Symbols

- `primaryFiniteRow0Parent0Split100Sub0CombinedOrder16DirectRemainderSourceProp`: `True`
- `primaryFiniteRow0Parent0Split100Sub0_combinedOrder16DirectInterval_valid_of_horner_remainder`: `True`
- `primaryFiniteRow0Parent0Split100Sub0CombinedOrder16DirectZeroModelRemainderSourceProp`: `True`

## Direct Horner Symbols

- `Step33Sub0CombinedOrder16ScaledRemainderDirectHornerCert`: `True`
- `Step33Sub0CombinedOrder16ScaledRemainderDirectHornerRangeCert`: `True`
- `Step33Sub0CombinedOrder16ScaledRemainderDirectHornerFamilyCert`: `True`
- `structure Valid`: `True`
- `to_nonzeroModelSourceProp`: `True`

## Direct Horner Smoke Symbols

- `primaryFiniteRow0Parent0Split100Sub0_scaledRemainderDirectHorner_receiver_smoke`: `True`

## Direct Source Bridge Symbols

- `primaryFiniteRow0Parent0Split100Sub0CombinedOrder16ScaledRemainderCollapsedExpression`: `True`
- `primaryFiniteRow0Parent0Split100Sub0_combinedOrder16ScaledRemainder_eq_collapsedExpression`: `True`
- `primaryFiniteRow0Parent0Split100Sub0_combinedOrder16ScaledRemainder_sourceProp_of_collapsed_interval`: `True`
- `primaryFiniteRow0Parent0Split100Sub0_combinedOrder16ScaledRemainder_canonicalSourceProp_of_collapsed_interval`: `True`

## Direct Horner Source Bridge Symbols

- `theorem of_collapsed_horner_range`: `True`
- `theorem valid_of_collapsed_horner_rows`: `True`

## Active-Actual Horner Segment Symbols

- `Step33Sub0ActiveActualOrder16HornerSegmentCert`: `True`
- `structure Valid`: `True`
- `theorem to_activeActual_order16_segment_remainder`: `True`
- `theorem to_collapsed_segment_remainder`: `True`
- `primaryFiniteRow0Parent0Split100Sub0_activeActual_order16_segment_remainder_of_horner_cert`: `True`
- `primaryFiniteRow0Parent0Split100Sub0_collapsed_segment_remainder_of_activeActualHorner`: `True`

## Active-Actual Horner Family Bridge Symbols

- `Step33Sub0ActiveActualOrder16HornerDirectSegmentCert`: `True`
- `Step33Sub0ActiveActualOrder16HornerDirectRangeCert`: `True`
- `Step33Sub0ActiveActualOrder16HornerFamilyCert`: `True`
- `theorem to_directHornerFamilyValid`: `True`
- `primaryFiniteRow0Parent0Split100Sub0_directHornerFamily_valid_of_activeActualHornerFamily`: `True`
- `primaryFiniteRow0Parent0Split100Sub0_directPayloadTarget_of_activeActualHornerFamily`: `True`
- `primaryFiniteRow0Parent0Split100Sub0_nonzeroModelSourceProp_of_activeActualHornerFamily`: `True`

## Biased Source Horner Symbols

- `Step33Sub0CombinedOrder16BiasedResidualSourceHornerCert`: `True`
- `Step33Sub0CombinedOrder16BiasedResidualSourceHornerRangeCert`: `True`
- `primaryFiniteRow0Parent0Split100Sub0_combinedOrder16BiasedResidual_sourceProp_of_source_horner_family`: `False`

## Biased Residual Source Segment Symbols

- `Step33Sub0CombinedOrder16BiasedResidualSourceSegmentCert`: `True`
- `namespace Step33Sub0CombinedOrder16BiasedResidualSourceSegmentCert`: `True`
- `theorem to_residual_bound_on_segment`: `True`
- `Step33Sub0CombinedOrder16BiasedResidualSourceSegmentCover`: `True`
- `primaryFiniteRow0Parent0Split100Sub0_combinedOrder16BiasedResidual_sourceProp_of_source_segment_cover`: `True`
- `primaryFiniteRow0Parent0Split100Sub0_combinedOrder16BiasedResidual_order16DirectIntervalValid_of_source_segment_cover`: `True`

## Biased Signed-Factor Adapter Symbols

- `primaryFiniteRow0Parent0Split100Sub0_combinedOrder16BiasedResidual_sourceProp_of_signedFactor_segment_cover`: `True`
- `Step33Sub0CombinedOrder16BiasedResidualSignedFactorSegmentFamilyCert`: `True`

## Via Biased Residual Bridge Symbols

- `primaryFiniteRow0Parent0Split100Sub0_scaledRemainder_sub_bias_eq_biasedResidual`: `True`
- `primaryFiniteRow0Parent0Split100Sub0_scaledRemainderDirectSegmentOfBiasedResidual`: `True`
- `primaryFiniteRow0Parent0Split100Sub0_scaledRemainderDirectSegment_valid_of_biasedResidual`: `True`
- `primaryFiniteRow0Parent0Split100Sub0_scaledRemainder_nonzeroModel_sourceProp_of_biasedResidualSourceProp`: `True`
- `primaryFiniteRow0Parent0Split100Sub0_scaledRemainderDirectFamilyOfBiasedResidual`: `True`
- `primaryFiniteRow0Parent0Split100Sub0_scaledRemainderDirectFamily_valid_of_biasedResidual`: `True`
- `primaryFiniteRow0Parent0Split100Sub0_scaledRemainderDirect_payloadTarget_of_biasedResidual`: `True`
- `primaryFiniteRow0Parent0Split100Sub0_scaledRemainder_nonzeroModel_sourceProp_of_biasedResidual`: `True`
- `primaryFiniteRow0Parent0Split100Sub0_scaledRemainder_bias_exceeds_direct_budget_rat`: `True`
- `primaryFiniteRow0Parent0Split100Sub0_scaledRemainder_biasShift_upperBudget_impossible_of_nonneg`: `True`

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
