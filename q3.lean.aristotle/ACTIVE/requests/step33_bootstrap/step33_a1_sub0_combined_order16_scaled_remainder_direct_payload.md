# Step33A.1-A Direct Scaled-Remainder Payload Ledger

schema: `q3_psdpd_step33_a1_sub0_combined_order16_scaled_remainder_direct_payload.v1`
route: `direct_nonzero_model_scaled_remainder_interval`
proofStatus: `direct_nonzero_model_payload_surface_checked_missing_interval_cert`

## Status

- proofGrade: `False`
- directPayloadSurfacePresent: `True`
- zeroModelBridgePresent: `True`
- intervalPayloadSurfacePresent: `True`
- remainderBridgePresent: `True`
- directNonzeroModelIntervalRowsLeanChecked: `False`
- directNonzeroModelSourcePropLeanChecked: `False`
- zeroModelPayloadTargetLeanChecked: `True`
- step33A1ClosedClaimed: `False`
- doNotSplitSummands: `True`

## Current Gap

`STEP33_A1_SUB0_COMBINED_ORDER16_SCALED_REMAINDER_NONZERO_MODEL_INTERVAL_CERT_GAP`

Parent gap:

`STEP33_A1_SUB0_COMBINED_ORDER16_BIASED_RESIDUAL_HORNER_SCALED_REMAINDER_BOUND_GAP`

First failure code if the direct route fails:

`STEP33_A1_SUB0_COMBINED_ORDER16_SCALED_REMAINDER_NONZERO_MODEL_INTERVAL_CERT_GAP`

## Target

- expression: `primaryFiniteRow0Parent0Split100Sub0CombinedCancellationOrder16ComponentSource eta - primaryFiniteRow0Parent0Split100Sub0CombinedOrder16NonzeroModelPoly eta`
- budget: `primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedResidualRemainderAbs`
- prop: `primaryFiniteRow0Parent0Split100Sub0CombinedOrder16ScaledRemainderNonzeroModelSourceProp`
- payload: `primaryFiniteRow0Parent0Split100Sub0CombinedOrder16ScaledRemainderDirectPayloadTarget`

## Theorem Shape

prove a signed interval on [0,1/10] for ComponentSource - NonzeroModelPoly inside +/- BiasedResidualRemainderAbs; then use primaryFiniteRow0Parent0Split100Sub0_combinedOrder16ScaledRemainder_nonzeroModel_sourceProp_of_full_cell_interval or a direct family payload target

## Certificate Shape

- segment cells covering [0,1/10]
- whole signed expression polynomial/range rows
- whole-expression remainder rows
- per-segment lower/upper budget rows
- global residualAbs = BiasedResidualRemainderAbs

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
