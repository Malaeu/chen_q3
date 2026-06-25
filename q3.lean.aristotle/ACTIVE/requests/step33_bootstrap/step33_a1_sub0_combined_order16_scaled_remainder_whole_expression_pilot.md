# Step33A.1-A Whole-Expression Pilot Source-Data Gate

schema: `q3_psdpd_step33_a1_sub0_combined_order16_scaled_remainder_whole_expression_pilot.v1`
route: `Step33A.1-A direct whole-expression CollapsedExpression pilot`
status: `source_data_gap`
phase2ResultNow: `NOT_RUN_SOURCE_DATA_GAP`
pilotVerdict: `None`
proofGrade: `False`
sourceDataReady: `False`
currentGap: `STEP33_A1_SUB0_COMBINED_ORDER16_SCALED_REMAINDER_WHOLE_EXPRESSION_PILOT_SOURCE_DATA_GAP`

## Target

- expression: `primaryFiniteRow0Parent0Split100Sub0CombinedOrder16ScaledRemainderCollapsedExpression`
- receiver: `primaryFiniteRow0Parent0Split100Sub0_combinedOrder16ScaledRemainder_collapsed_segment_remainder`
- interval: `Set.Icc (0 : Real) ((1 : Real) / 10)`
- preserveCancellation: `True`

## Accepted Pilot Verdicts

- `PASS_STABLE_MARGIN`
- `NEGATIVE_MARGIN`
- `UNSTABLE_MARGIN`
- `SEGMENT_EXPLOSION`

This run produced none of those verdicts because the required whole-expression source data is not present.

## Missing Artifacts

### complete_collapsed_expression_coeff_stream

- present: `False`
- required: proof-grade rational coefficients for the complete CollapsedExpression on each chosen segment
- currentEvidence: `PARTIAL_NOMINAL_POLY_BRIDGE_PRESENT_COMPLETE_STREAM_ABSENT`

### collapsed_segment_remainder_rows

- present: `False`
- required: Lean-visible rows proving CollapsedExpression minus the generated rawOmegaATaylorPolynomial is bounded on every segment
- theorem: `primaryFiniteRow0Parent0Split100Sub0_combinedOrder16ScaledRemainder_collapsed_segment_remainder`

### source_interval_generated_or_direct_horner_valid

- present: `False`
- required: either a concrete source-interval generated theorem feeding the checked receiver, or a concrete DirectHorner valid theorem
- acceptedInterface: `primaryFiniteRow0Parent0Split100Sub0_combinedOrder16ScaledRemainder_collapsed_segment_remainder_of_source_interval`
- acceptedInterface: `primaryFiniteRow0Parent0Split100Sub0_combinedOrder16ScaledRemainderDirectHorner_valid`

### direct_concrete_payload_file

- present: `False`
- required: DirectConcretePayload.lean only after segment rows, Horner rows, exact cover, and budget rows exist
- file: `Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16ScaledRemainderDirectConcretePayload.lean`

## Checked Support

### directSourceBridge

- file: `Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16ScaledRemainderDirectSourceBridge.lean`
- exists: `True`
- `primaryFiniteRow0Parent0Split100Sub0CombinedOrder16ScaledRemainderCollapsedExpression`: `True`
- `combinedOrder16ScaledRemainder_eq_collapsedExpression`: `True`
- `combinedOrder16ScaledRemainder_sourceProp_of_collapsed_interval`: `True`

### nominalPolynomialBridge

- file: `Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16NominalPolynomialBridge.lean`
- exists: `True`
- `primaryFiniteRow0Parent0Split100Sub0NominalOrder16Coeff`: `True`
- `combinedOrder16CollapsedExpression_eq_activeActual_sub_nominalOrder16Poly`: `True`

### collapsedSourceIntervalReceiver

- file: `Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16ScaledRemainderDirectCollapsedSourceIntervalCert.lean`
- exists: `True`
- `Step33Sub0CombinedOrder16ScaledRemainderDirectCollapsedSourceIntervalCert`: `True`
- `primaryFiniteRow0Parent0Split100Sub0_combinedOrder16ScaledRemainder_collapsed_segment_remainder_of_source_interval`: `True`

### collapsedTaylorReceiver

- file: `Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16ScaledRemainderDirectCollapsedTaylorSource.lean`
- exists: `True`
- `Step33Sub0CombinedOrder16ScaledRemainderDirectCollapsedTaylorCert`: `True`
- `collapsed_segment_remainder_of_centerJet15_order16`: `True`

### directHornerSourceBridge

- file: `Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16ScaledRemainderDirectHornerSourceBridge.lean`
- exists: `True`
- `valid_of_collapsed_horner_rows`: `True`
- `of_collapsed_horner_range`: `True`

## Payload Ledger Source Status

- payloadLedger: `ACTIVE/requests/step33_bootstrap/step33_a1_sub0_combined_order16_scaled_remainder_direct_payload.json`
- exactCoefficientSource.status: `PARTIAL_NOMINAL_POLY_BRIDGE_PRESENT_COMPLETE_STREAM_ABSENT`
- note: primaryFiniteRow0Parent0Split100Sub0ResidualTaylorCoeff is a model coefficient source, not the direct collapsed-expression residual coefficient stream.
- note: primaryFiniteRow0Parent0Split100Sub0CombinedOrder16NonzeroModelCoeff is the already-subtracted model coefficient source, not coefficients for ComponentSource - NonzeroModelPoly.
- note: The nominal polynomial bridge extracts the rational nominal subtracted polynomial only; it is not a complete coefficient stream for collapsedExpression.
- note: The checked collapse and nominal polynomial bridge do not produce Horner rows or an analytic remainder bound.

## Next Certificate Interface

- preferred: `interval_or_rational_source_interval_rows`
- receiver: `primaryFiniteRow0Parent0Split100Sub0_combinedOrder16ScaledRemainder_collapsed_segment_remainder_of_source_interval`
- alternative: `primaryFiniteRow0Parent0Split100Sub0_combinedOrder16ScaledRemainderDirectHorner_valid`
- mustInclude: exact segment cover of Set.Icc 0 (1/10)
- mustInclude: same-target collapsedExpression coefficients
- mustInclude: proof-grade remainder rows per segment
- mustInclude: Horner lower/upper rows if using the Horner receiver
- mustInclude: final +/- BiasedResidualRemainderAbs budget rows

## Proof Truth

- step33A1AClosed: `False`
- directConcretePayloadWritten: `False`
- acceptedPilotVerdictProduced: `False`
- numericSamplingUsedAsProof: `False`
- leanFilesModified: `False`

## Next Patch

Produce the same-target collapsedExpression coefficient stream plus proof-grade source-interval or direct-Horner remainder rows; then rerun this pilot.
