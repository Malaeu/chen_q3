# Step33A.1-A Direct Row-Source Audit

schema: `q3_psdpd_step33_a1_sub0_combined_order16_scaled_remainder_direct_payload.v21.row_source_audit`
route: `direct_nonzero_model_scaled_remainder_interval`
proofGrade: `False`
currentGap: `STEP33_A1_SUB0_COMBINED_ORDER16_SCALED_REMAINDER_DIRECT_ROW_SOURCE_GAP`
firstRowFailureCode: `STEP33_A1_SUB0_COMBINED_ORDER16_SCALED_REMAINDER_DIRECT_ROW_SOURCE_GAP`

## Verdict

- recommended option: `A_for_partial_nominal_bridge_then_fail_closed_rows`
- decision label: `CHOSEN: A`
- first file to create: `Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16NominalPolynomialBridge.lean`
- proof claim allowed now: `False`
- step33A1ClosedClaimed: `False`
- audit object: `primaryFiniteRow0Parent0Split100Sub0CombinedOrder16ScaledRemainderCollapsedRowSourceAudit`
- audit object is Lean theorem: `False`

Add the partial nominal polynomial coefficient bridge, but keep the direct row generator fail-closed until a single proof-grade whole-expression coefficient/remainder row exists for collapsedExpression.

## Target

- expression: `primaryFiniteRow0Parent0Split100Sub0CombinedCancellationOrder16ComponentSource eta - primaryFiniteRow0Parent0Split100Sub0CombinedOrder16NonzeroModelPoly eta`
- budget: `primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedResidualRemainderAbs`
- target prop: `primaryFiniteRow0Parent0Split100Sub0CombinedOrder16ScaledRemainderNonzeroModelSourceProp`
- first interval theorem: `primaryFiniteRow0Parent0Split100Sub0_combinedOrder16ScaledRemainder_nonzeroModel_interval_generated`
- direct source bridge present: `True`
- direct source bridge file: `Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16ScaledRemainderDirectSourceBridge.lean`

## Exact Coefficient Source

- status: `PARTIAL_NOMINAL_POLY_BRIDGE_PRESENT_COMPLETE_STREAM_ABSENT`
- partial bridge file: `Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16NominalPolynomialBridge.lean`
- partial bridge theorem: `primaryFiniteRow0Parent0Split100Sub0_combinedOrder16CollapsedExpression_eq_activeActual_sub_nominalOrder16Poly`

- primaryFiniteRow0Parent0Split100Sub0ResidualTaylorCoeff is a model coefficient source, not the direct collapsed-expression residual coefficient stream.
- primaryFiniteRow0Parent0Split100Sub0CombinedOrder16NonzeroModelCoeff is the already-subtracted model coefficient source, not coefficients for ComponentSource - NonzeroModelPoly.
- The nominal polynomial bridge extracts the rational nominal subtracted polynomial only; it is not a complete coefficient stream for collapsedExpression.
- The checked collapse and nominal polynomial bridge do not produce Horner rows or an analytic remainder bound.

## Missing Remainder Theorem

- name: `primaryFiniteRow0Parent0Split100Sub0_combinedOrder16ScaledRemainder_collapsed_segment_remainder`

```lean
theorem primaryFiniteRow0Parent0Split100Sub0_combinedOrder16ScaledRemainder_collapsed_segment_remainder
    (i : Fin segmentCount) :
    forall eta in Set.Icc (cellL i : Real) (cellU i : Real),
      norm (primaryFiniteRow0Parent0Split100Sub0CombinedOrder16ScaledRemainderCollapsedExpression eta -
        rawOmegaATaylorPolynomial degree (center i) (coeff i) eta) <=
      (polyErrorAbs i : Real)
```

## Minimal Row Data

- exact segment cover
- proof-grade rational coeff[i][j] for the complete collapsed expression
- Lean-checked Horner stage lower/upper bounds
- primaryFiniteRow0Parent0Split100Sub0_combinedOrder16ScaledRemainder_collapsed_segment_remainder for every segment
- exact final +/- BiasedResidualRemainderAbs budget rows

## Do Not Reuse

- killed factor majorants
- P45/fullTaylor wrong target
- zero-model budget
- center jets as uniform bounds
- sampled rows
- separate actual/nominal norm budgets
- nominalOrder16Poly as an independent spendable budget

## Preferred Collapsed Low-Degree Row-Source Contract

- choice: `A`
- source: `preferred_collapsed_low_degree_signed_source_contract`
- status: `fail_closed_contract_only`
- proofGrade: `False`
- generator to patch: `scripts/generate_step33_a1_sub0_combined_order16_scaled_remainder_direct_payload.py`
- Lean file to emit only when rows pass: `Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16ScaledRemainderDirectConcretePayload.lean`
- final theorem when rows pass: `primaryFiniteRow0Parent0Split100Sub0_combinedOrder16ScaledRemainder_nonzeroModel_interval_generated`
- row theorem when rows pass: `primaryFiniteRow0Parent0Split100Sub0_combinedOrder16ScaledRemainder_collapsed_segment_remainder`
- first failure if rows are missing: `STEP33_A1_SUB0_COMBINED_ORDER16_COLLAPSED_DEGREE0_POLY_DERIV_SIGNED_SOURCE_GAP`
- parent failure if rows are missing: `STEP33_A1_SUB0_COMBINED_ORDER16_SCALED_REMAINDER_DIRECT_ROW_SOURCE_GAP`
- budget failure code: `STEP33_A1_SUB0_COMBINED_ORDER16_COLLAPSED_DEGREE0_BUDGET_CONSTANT_FAIL`

The direct collapsed degree-0 receiver is the smallest current whole-expression route: it keeps activeActual-minus-nominal cancellation inside one target, uses the checked center row, and requires only a signed derivative source row plus exact rational budgets before Horner/final-budget emission.

### Receiver Chain

- `checked`: `primaryFiniteRow0Parent0Split100Sub0_directCollapsed_degree0_hCenter_generated`
  file: `Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16ScaledRemainderDirectCollapsedDegree0CenterAudit.lean`
  failureCodeIfMissing: `STEP33_A1_SUB0_COMBINED_ORDER16_SCALED_REMAINDER_DIRECT_ROW_SOURCE_GAP`
- `checked`: `primaryFiniteRow0Parent0Split100Sub0_collapsedExpression_deriv_eq_activeActualD17_sub_nominalOrder16PolyDeriv`
  file: `Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16ScaledRemainderDirectCollapsedDegree0DerivativeShift.lean`
  failureCodeIfMissing: `STEP33_A1_SUB0_COMBINED_ORDER16_COLLAPSED_DEGREE0_POLY_DERIV_SIGNED_SOURCE_GAP`
- `checked`: `primaryFiniteRow0Parent0Split100Sub0_combinedOrder16ScaledRemainder_collapsed_degree0_remainder_of_signedD17_source`
  file: `Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16ScaledRemainderDirectCollapsedLowDegreeSource.lean`
  failureCodeIfMissing: `STEP33_A1_SUB0_COMBINED_ORDER16_COLLAPSED_DEGREE0_D17_SIGNED_SOURCE_GAP`
- `checked_receiver_rows_missing`: `Step33Sub0CollapsedDegree0SignedSourceSegmentFamilyCert.Valid.to_collapsed_degree0_remainder`
  file: `Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16CollapsedDegree0SignedSourcePayload.lean`
  failureCodeIfMissing: `STEP33_A1_SUB0_COMBINED_ORDER16_COLLAPSED_DEGREE0_POLY_DERIV_SIGNED_SOURCE_GAP`

### Required Exact Rows Before Lean Emission

- `L0_segment_cover`: `missing`
  object: `Step33Sub0CollapsedDegree0SignedSourceSegmentCover for the generated segments covering Set.Icc 0 (1/10)`
  failureCode: `STEP33_A1_SUB0_COMBINED_ORDER16_COLLAPSED_DEGREE0_POLY_DERIV_SIGNED_SOURCE_GAP`
- `L1_signed_source_segment_rows`: `missing`
  object: `proof-grade lower/upper rows for ActiveScaleCoeff * D17(ComponentProductActual) - deriv(NominalOrder16Poly) on each segment`
  failureCode: `STEP33_A1_SUB0_COMBINED_ORDER16_COLLAPSED_DEGREE0_POLY_DERIV_SIGNED_SOURCE_GAP`
- `L2_deriv_abs_budget`: `missing`
  object: `exact rational proof that the generated lower/upper rows are contained in [-derivAbs, derivAbs]`
  failureCode: `STEP33_A1_SUB0_COMBINED_ORDER16_COLLAPSED_DEGREE0_BUDGET_CONSTANT_FAIL`
- `L3_degree0_remainder_budget`: `missing`
  object: `exact rational proof that coeffErrorAbs + derivAbs * (1/20) <= polyErrorAbs`
  failureCode: `STEP33_A1_SUB0_COMBINED_ORDER16_COLLAPSED_DEGREE0_BUDGET_CONSTANT_FAIL`
- `L4_collapsed_segment_remainder`: `missing_until_L0_L3_pass`
  object: `primaryFiniteRow0Parent0Split100Sub0_combinedOrder16ScaledRemainder_collapsed_segment_remainder`
  failureCode: `STEP33_A1_SUB0_COMBINED_ORDER16_SCALED_REMAINDER_DIRECT_ROW_SOURCE_GAP`
- `L5_horner_and_final_budget_rows`: `missing`
  object: `Horner stage bounds, segment cover for the direct family, and final +/- BiasedResidualRemainderAbs rows`
  failureCode: `STEP33_A1_SUB0_COMBINED_ORDER16_COLLAPSED_SOURCE_INTERVAL_ROWS_GAP`

### Contract Do Not Use

- activeActual degree0 polyErrorAbs as the final direct budget
- factorwise RawD17/two-segment budget kills as closure
- separate activeActual and nominal independent norm budgets
- sampled point rows or Python diagnostics as proof
- DirectConcretePayload.lean before all L0-L5 rows pass

## Route Options

- why no DirectConcretePayload yet: The partial nominal polynomial bridge is not the full collapsedExpression coefficient stream and does not prove the collapsed-segment remainder theorem.
- whyNotB: B is already subsumed by Step33Sub0CombinedOrder16ScaledRemainderDirectHornerCert.Valid.of_collapsed_horner_range; adding another alias is not the first proof-producing row source.
- whyNotD: The route is not impossible; the exact missing proof-row source is now named.

## Active-Actual Horner Row-Source Ledger

- `path`: `ACTIVE/requests/step33_bootstrap/step33_a1_sub0_active_actual_horner_row_source.json`
- `exists`: `True`
- `schema`: `q3_psdpd_step33_a1_sub0_active_actual_horner_row_source.v6`
- `proofStatus`: `superseded_by_direct_collapsed_expression_budget_kill`
- `proofGrade`: `False`
- `proofSafeClosedFields`: `0`
- `currentGap`: `STEP33_A1_SUB0_ACTIVE_ACTUAL_ORDER16_DEGREE0_DIRECT_BUDGET_CONSTANT_FAIL_FOR_PAYLOAD`
- `firstFailureCode`: `STEP33_A1_SUB0_ACTIVE_ACTUAL_ORDER16_DEGREE0_DIRECT_BUDGET_CONSTANT_FAIL_FOR_PAYLOAD`
- `outLeanWritten`: `False`
- `leanValidationStatus`: `not_run_rows_missing`

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

### direct_collapsed_taylor_receiver

- `file`: `Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16ScaledRemainderDirectCollapsedTaylorSource.lean`
- `artifactStatus`: `lean_collapsed_taylor_receiver_present`
- `sameTarget`: `True`
- `proofGradeRowsPresent`: `False`
- `spendableForCurrentTarget`: `False`
- `reason`: `The Lean receiver converts segment-wise center-jet/order-16 Taylor proof data for the whole collapsedExpression into the existing direct Horner receiver.  It intentionally supplies no center jets, no order-16 derivative rows, no Horner range rows, and no final budget rows.`
- `closedSubgap`: `STEP33_A1_SUB0_COMBINED_ORDER16_COLLAPSED_TAYLOR_RECEIVER_CLOSED`
- `receiverTheorem`: `primaryFiniteRow0Parent0Split100Sub0_combinedOrder16ScaledRemainder_collapsed_segment_remainder_of_centerJet15_order16`
- `adapterTheorem`: `Step33Sub0CombinedOrder16ScaledRemainderDirectCollapsedTaylorCert.Valid.to_directHorner_valid`
- `firstMissingProofObject`: `proof-grade lower/upper source-interval rows for collapsedExpression`
- `hiddenMismatchesToGuard`: `['degree-15/Fin 16 rows must match the DirectHorner degree field', 'CollapsedExpression already contains D16, so an order-16 row is a high derivative requirement on the source products', 'segment centers must be local; the full-cell center 1/20 is not a universal local-row substitute']`
- `failureCode`: `STEP33_A1_SUB0_COMBINED_ORDER16_SCALED_REMAINDER_DIRECT_ROW_SOURCE_GAP`

### direct_collapsed_low_degree_receiver

- `file`: `Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16ScaledRemainderDirectCollapsedLowDegreeSource.lean`
- `artifactStatus`: `lean_collapsed_low_degree_receiver_present`
- `sameTarget`: `True`
- `proofGradeRowsPresent`: `False`
- `spendableForCurrentTarget`: `False`
- `reason`: `The Lean receiver reduces the whole CollapsedExpression segment remainder to a degree-0 center row, a signed activeD17-minus-nominal-polynomial-derivative source row, and a rational budget comparison.  It avoids the degree-15/order-16 source row, but still emits no numeric source rows and no final Horner budget rows.`
- `closedSubgap`: `STEP33_A1_SUB0_COMBINED_ORDER16_COLLAPSED_DEGREE0_RECEIVER_CLOSED`
- `receiverTheorem`: `primaryFiniteRow0Parent0Split100Sub0_combinedOrder16ScaledRemainder_collapsed_degree0_remainder_of_signedD17_source`
- `derivativeShiftFile`: `Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16ScaledRemainderDirectCollapsedDegree0DerivativeShift.lean`
- `derivativeShiftPresent`: `True`
- `derivativeShiftTheorem`: `primaryFiniteRow0Parent0Split100Sub0_collapsedExpression_deriv_eq_activeActualD17_sub_nominalOrder16PolyDeriv`
- `centerAuditFile`: `Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16ScaledRemainderDirectCollapsedDegree0CenterAudit.lean`
- `centerAuditPresent`: `True`
- `centerAuditTheorem`: `primaryFiniteRow0Parent0Split100Sub0_directCollapsed_degree0_hCenter_generated`
- `signedSourceFile`: `Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16CollapsedDegree0SignedSourcePayload.lean`
- `signedSourcePresent`: `True`
- `signedSourceTheorem`: `primaryFiniteRow0Parent0Split100Sub0_collapsed_degree0_remainder_of_signed_source_cert`
- `polyDerivReceiverTheorem`: `primaryFiniteRow0Parent0Split100Sub0_combinedOrder16ScaledRemainder_collapsed_degree0_remainder_of_polyDeriv_signedD17_source`
- `firstMissingProofObject`: `proof-grade signed activeD17-minus-deriv(NominalOrder16Poly) source row`
- `failureCode`: `STEP33_A1_SUB0_COMBINED_ORDER16_SCALED_REMAINDER_DIRECT_ROW_SOURCE_GAP`

### direct_collapsed_source_interval_adapter

- `file`: `Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16ScaledRemainderDirectCollapsedSourceIntervalCert.lean`
- `artifactStatus`: `lean_collapsed_source_interval_adapter_present`
- `sameTarget`: `True`
- `proofGradeRowsPresent`: `False`
- `spendableForCurrentTarget`: `False`
- `reason`: `The Lean adapter converts future rational lower/upper source intervals for the whole collapsedExpression into the checked absolute-error Taylor receiver.  It supplies no source rows, no Horner range rows, and no final budget rows.`
- `closedSubgap`: `STEP33_A1_SUB0_COMBINED_ORDER16_COLLAPSED_SOURCE_INTERVAL_CERT_CLOSED`
- `sourceIntervalTheorem`: `primaryFiniteRow0Parent0Split100Sub0_combinedOrder16ScaledRemainder_collapsedTaylorValid_of_source_interval`
- `firstMissingProofObject`: `proof-grade rational lower/upper source-interval rows`
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
- `upstreamFailureCode`: `STEP33_A1_SUB0_COMBINED_ORDER16_COLLAPSED_DEGREE0_RAW_D17_SHARP_TWO_SEGMENT_BUDGET_CONSTANT_FAIL`
- `proofGrade`: `False`

### R2_horner_or_interval_rows

- `object`: `proof-grade rational/interval rows for the assembled signed expression`
- `requiredFor`: `primaryFiniteRow0Parent0Split100Sub0_combinedOrder16ScaledRemainder_nonzeroModel_interval_generated`
- `status`: `collapsed_source_interval_adapter_checked_rows_missing`
- `upstreamFailureCode`: `STEP33_A1_SUB0_COMBINED_ORDER16_COLLAPSED_DEGREE0_RAW_D17_SHARP_TWO_SEGMENT_BUDGET_CONSTANT_FAIL`
- `directCollapsedTaylorReceiverFile`: `Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16ScaledRemainderDirectCollapsedTaylorSource.lean`
- `directCollapsedTaylorReceiverPresent`: `True`
- `directCollapsedTaylorReceiverTheorem`: `primaryFiniteRow0Parent0Split100Sub0_combinedOrder16ScaledRemainder_collapsed_segment_remainder_of_centerJet15_order16`
- `directCollapsedTaylorFailureCode`: `STEP33_A1_SUB0_COMBINED_ORDER16_SCALED_REMAINDER_DIRECT_ROW_SOURCE_GAP`
- `componentTaylorGapBypassedByDirectHornerRoute`: `False`
- `sourceSplitTheorem`: `primaryFiniteRow0Parent0Split100Sub0_combinedOrder16Source_sub_nonzeroModelPoly`
- `collapsedExpressionBridgeTheorem`: `primaryFiniteRow0Parent0Split100Sub0_combinedOrder16ScaledRemainder_eq_collapsedExpression`
- `collapsedHornerReceiverBridgeTheorem`: `Step33Sub0CombinedOrder16ScaledRemainderDirectHornerCert.Valid.of_collapsed_horner_range`
- `collapsedHornerFamilyBridgeTheorem`: `Step33Sub0CombinedOrder16ScaledRemainderDirectHornerFamilyCert.valid_of_collapsed_horner_rows`
- `receiverField`: `Step33Sub0CombinedOrder16ScaledRemainderDirectHornerCert.Valid.directRemainder`
- `guard`: `The Lean split theorem is allowed as the row-source crosswalk.  With the collapsed Horner source bridge, a future row may prove the remainder against CollapsedExpression and transport it into directRemainder.  The checked collapsed Taylor receiver now fixes the center-jet/order-16 row interface, but the coefficient stream, derivative rows, Horner range rows, and budget rows are still missing.`
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

## Guard

This is an interface and fail-closed ledger only.  It does not prove the interval rows, and it must not be treated as Step33A.1-A closure until the direct nonzero-model source proposition is Lean-checked or backed by proof-grade generated rows.
