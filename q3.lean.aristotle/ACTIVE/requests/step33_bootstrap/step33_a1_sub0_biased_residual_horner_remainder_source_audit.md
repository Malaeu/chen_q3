# Step33A.1-A Biased Residual-Horner Remainder Source Audit

Status: `GAP_EXACTLY_NAMED`

This audit is not Lean proof data and does not close Step33A.1-A.  It records
the first local obstruction after the residual-Horner coefficient bridge.

## Checked Local Bridge

File:

```text
Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16BiasedResidualHornerConcretePayload.lean
```

Checked split:

```lean
primaryFiniteRow0Parent0Split100Sub0_biasedResidualTarget_eq_hornerPoly_add_scaledRemainder
```

Meaning:

```text
residualTarget =
  residual-Horner polynomial
  +
  (ActiveScaleCoeff * D^16(ComponentProductCancellationResidual)
   + (ActiveScaleCoeff - NominalScaleCoeff) * D^16(ComponentProductNominal))
```

The polynomial part is Lean-checked.  The analytic scaled remainder is not
bounded yet.

## Current Residual-Horner Gap

```text
STEP33_A1_SUB0_COMBINED_ORDER16_BIASED_RESIDUAL_HORNER_REMAINDER_ROWS_GAP
```

Required proof object:

```lean
∀ eta ∈ Set.Icc (cellL : Real) (cellU : Real),
  ‖Step33Sub0CombinedOrder16BiasedResidualHornerCert.residualTarget eta -
    rawOmegaATaylorPolynomial 29 ((1 : Rat) / 20)
      primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedResidualHornerCoeff eta‖
    <= (remainderAbs : Real)
```

or an equivalent proof-grade segment family in the
`Step33Sub0CombinedOrder16BiasedResidualHornerCert.Valid` normalization.

## Local Evidence Inventory

### Component Assembly Ledger

Source:

```text
ACTIVE/requests/step33_bootstrap/step33_a1_sub0_component_assembly_stream_ledger.json
```

Relevant fields:

```text
residualTaylorCoeffLeanPresent = true
algebraicAssemblyPayloadCertificatePresent = true
componentTaylorProofsPresent = false
residualTaylorRemainderAbsPresent = false
localAssemblyGap = STEP33_A1_SUB0_COMPONENT_TAYLOR_REMAINDER_SOURCE_GAP
routeLevelGap = STEP33_A1_SUB0_COMPONENT_TAYLOR_REMAINDER_SOURCE_GAP
```

Meaning: coefficient algebra is available, but the proof-grade component Taylor
remainder source is still absent.

### Component Taylor Residual Payload

Source:

```text
ACTIVE/requests/step33_bootstrap/step33_a1_sub0_component_taylor_residual_payload.md
```

Relevant status:

```text
status = fail_closed_shapesq_same_coeff_payload_checked_component_remainder_gap
first failure = STEP33_A1_SUB0_COMPONENT_TAYLOR_REMAINDER_SOURCE_GAP
residualTaylorRemainderAbs = None
componentTaylorProofsPresent = false
```

The later local supplements checked algebraic and coarse enclosure bridges, but
they did not install a spendable final residual Taylor remainder source.

### Segmented Residual Derivative Payload

Source:

```text
ACTIVE/requests/step33_bootstrap/step33_a1_sub0_segmented_residual_deriv_interval_payload.md
```

Relevant status:

```text
coverage passed = true
budget passed = true
proofGradeResidualBoundsPresent = false
proofGradeClosedFormResidualBoundsPresent = false
proofGradeFullTaylorResidualBoundsPresent = false
sameExpressionResidualIntervalProofPresent = false
analyticResidualBoundsProof = missing
```

Meaning: the one-segment rational geometry and budget candidate pass, but it is
not a proof object because the same-expression residual interval proof is
missing.

## Decision

Do not emit or claim a concrete
`Step33Sub0CombinedOrder16BiasedResidualHornerFamilyCert.Valid` until the
analytic scaled remainder has proof-grade rows.

The immediate upstream blocker is:

```text
STEP33_A1_SUB0_COMPONENT_TAYLOR_REMAINDER_SOURCE_GAP
```

For the residual-Horner route, report it through the current live gate as:

```text
STEP33_A1_SUB0_COMBINED_ORDER16_BIASED_RESIDUAL_HORNER_REMAINDER_ROWS_GAP
```

## Next Proof-Producing Patch

Build one of the following, in this order of preference:

1. A proof-grade component Taylor remainder source that sets
   `residualTaylorRemainderAbsPresent = true` and feeds the analytic scaled
   remainder in the checked residual-Horner split.
2. A direct same-expression interval certificate for the analytic scaled
   remainder on `[0, 1/10]`, then package it as the
   `residual_remainder` field of the residual-Horner segment cert.

Do not use sampled/probe residual candidates as proof rows.

## 2026-06-23 Addendum: Remainder Bridge Checked

The subtraction form of the coefficient bridge is now Lean-checked in:

```text
Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16BiasedResidualHornerRemainderBridge.lean
```

Checked symbols:

```lean
primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedResidualHornerScaledRemainder
primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedResidualHornerScaledRemainderSourceProp
primaryFiniteRow0Parent0Split100Sub0_biasedResidualTarget_sub_hornerPoly_eq_scaledRemainder
primaryFiniteRow0Parent0Split100Sub0_biasedResidualHorner_residualRemainder_of_scaledRemainder_bound
primaryFiniteRow0Parent0Split100Sub0_biasedResidualHorner_segmentResidualRemainder_of_scaledRemainder_bound
```

Refined current gap:

```text
STEP33_A1_SUB0_COMBINED_ORDER16_BIASED_RESIDUAL_HORNER_SCALED_REMAINDER_BOUND_GAP
```

Parent gap remains:

```text
STEP33_A1_SUB0_COMBINED_ORDER16_BIASED_RESIDUAL_HORNER_REMAINDER_ROWS_GAP
```

Boundary: the bridge proves only that a future bound for
`primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedResidualHornerScaledRemainderSourceProp`
is the exact `residual_remainder` row needed by the residual-Horner cert. It
does not prove that bound and does not claim a concrete family `Valid` theorem.

## 2026-06-23 Addendum: Interval Payload Surface Checked

The generator-facing whole-expression interval target is now Lean-checked in:

```text
Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16BiasedScaledRemainderIntervalPayload.lean
```

Checked handoff:

```lean
primaryFiniteRow0Parent0Split100Sub0BiasedScaledRemainderIntervalPayloadTarget
primaryFiniteRow0Parent0Split100Sub0_scaledRemainderSourceProp_of_interval_payload_target
primaryFiniteRow0Parent0Split100Sub0_biasedResidualHorner_residualRemainder_of_scaledRemainder_interval_payload
```

Generated fail-closed ledger:

```text
ACTIVE/requests/step33_bootstrap/step33_a1_sub0_combined_order16_biased_scaled_remainder_interval.{json,md}
```

Ledger status:

```text
biased_scaled_remainder_interval_surface_checked_missing_interval_cert
INTERVAL_CERT_GAP
```

Boundary: this still does not prove the scaled remainder bound. It only pins
the next proof-producing payload target for a proof-grade whole-expression
interval/rational certificate on `[0,1/10]`.

## 2026-06-23 Addendum: Zero-Model Checker Checked

The one-cell zero-model checker is now Lean-checked in:

```text
Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16BiasedScaledRemainderZeroModelPayload.lean
```

Checked handoff:

```lean
primaryFiniteRow0Parent0Split100Sub0_biasedScaledRemainderZeroModel_payload_target
primaryFiniteRow0Parent0Split100Sub0_biasedResidualHorner_residualRemainder_of_scaledRemainder_zeroModel
```

Generated fail-closed ledger status:

```text
biased_scaled_remainder_zero_model_checker_checked_missing_source_bound
INTERVAL_CERT_GAP
```

Boundary: this closes only the one-cell cover/budget checker for the canonical
`BiasedResidualRemainderAbs` budget. It still requires a proof-grade theorem of
`primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedResidualHornerScaledRemainderSourceProp`
before any residual-Horner family `Valid` or Step33A.1-A closure can be claimed.
