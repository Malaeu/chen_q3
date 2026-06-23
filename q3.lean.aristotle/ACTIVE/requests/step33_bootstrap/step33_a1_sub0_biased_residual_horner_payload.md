# Step33A.1-A Biased Residual-Horner Payload Ledger

schema: `q3_psdpd_step33_a1_sub0_biased_residual_horner_payload.v4`
route: `biased_residual_horner_family_payload`
proofStatus: `biased_residual_horner_remainder_bridge_checked_missing_scaled_remainder_bound`

## Present

- payloadInterfacePresent: `True`
- hornerFamilyReceiverPresent: `True`
- directResidualAdapterPresent: `True`
- coefficientBridgePresent: `True`
- remainderBridgePresent: `True`
- scaledRemainderIntervalPayloadInterfacePresent: `True`

## Payload Interface Symbols

- `primaryFiniteRow0Parent0Split100Sub0BiasedResidualHornerFamilyPayloadTarget`: `True`
- `primaryFiniteRow0Parent0Split100Sub0_biasedResidualHornerFamily_residualSourceProp_of_payload_target`: `True`
- `primaryFiniteRow0Parent0Split100Sub0_biasedNonzeroModel_directInterval_valid_of_biasedResidualHornerFamily_payload`: `True`
- `primaryFiniteRow0Parent0Split100Sub0_biasedNonzeroModel_directInterval_valid_of_biasedResidualHornerFamily_valid`: `True`
- `STEP33_A1_SUB0_COMBINED_ORDER16_BIASED_RESIDUAL_HORNER_FAMILY_PAYLOAD_GAP`: `True`

## Residual-Horner Receiver Symbols

- `Step33Sub0CombinedOrder16BiasedResidualHornerCert`: `True`
- `Step33Sub0CombinedOrder16BiasedResidualHornerRangeCert`: `True`
- `Step33Sub0CombinedOrder16BiasedResidualHornerFamilyCert`: `True`
- `theorem to_residualSourceProp`: `True`
- `theorem to_order16DirectIntervalValid`: `True`

## Direct Residual Adapter Symbols

- `primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedResidualRemainderAbs`: `True`
- `primaryFiniteRow0Parent0Split100Sub0_biasedNonzeroModel_directInterval_valid_of_remainder_bound`: `True`
- `primaryFiniteRow0Parent0Split100Sub0_biasedNonzeroModel_directInterval_valid_of_slack_remainder_bound`: `True`

## Concrete Coefficient Bridge Symbols

- `primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedResidualHornerCoeff`: `True`
- `primaryFiniteRow0Parent0Split100Sub0_biasedResidualHornerCoeff_eq_neg_biasCoeff`: `True`
- `primaryFiniteRow0Parent0Split100Sub0_biasedResidualHornerCoeff_poly_eq_nonzero_sub_biased`: `True`
- `primaryFiniteRow0Parent0Split100Sub0_biasedResidualHornerCoeff_poly_eq_neg_bias`: `True`
- `primaryFiniteRow0Parent0Split100Sub0_biasedResidualTarget_eq_hornerPoly_add_scaledRemainder`: `True`

## Remainder Bridge Symbols

- `primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedResidualHornerScaledRemainder`: `True`
- `primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedResidualHornerScaledRemainderSourceProp`: `True`
- `primaryFiniteRow0Parent0Split100Sub0_biasedResidualTarget_sub_hornerPoly_eq_scaledRemainder`: `True`
- `primaryFiniteRow0Parent0Split100Sub0_biasedResidualHorner_residualRemainder_of_scaledRemainder_bound`: `True`
- `primaryFiniteRow0Parent0Split100Sub0_biasedResidualHorner_segmentResidualRemainder_of_scaledRemainder_bound`: `True`

## Scaled Remainder Interval Payload Symbols

- `Step33Sub0CombinedOrder16BiasedScaledRemainderIntervalSegmentCert`: `True`
- `Step33Sub0CombinedOrder16BiasedScaledRemainderIntervalFamilyCert`: `True`
- `primaryFiniteRow0Parent0Split100Sub0BiasedScaledRemainderIntervalPayloadTarget`: `True`
- `primaryFiniteRow0Parent0Split100Sub0_scaledRemainderSourceProp_of_interval_payload_target`: `True`
- `primaryFiniteRow0Parent0Split100Sub0_biasedResidualHorner_residualRemainder_of_scaledRemainder_interval_payload`: `True`

## Missing Proof Payload

- coefficientBridgeLeanChecked: `True`
- residualRemainderInterfaceLeanChecked: `True`
- concreteFamilyDataLeanChecked: `False`
- segmentRowsLeanChecked: `False`
- hornerRangeRowsLeanChecked: `False`
- residualRemainderRowsLeanChecked: `False`
- scaledRemainderBoundLeanChecked: `False`
- scaledRemainderIntervalRowsLeanChecked: `False`
- residualBudgetRowsLeanChecked: `False`
- coverLeanChecked: `False`
- canonicalResidualAbsLeanChecked: `False`
- payloadTargetClaimed: `False`
- residualSourcePropClaimed: `False`
- order16DirectIntervalValidClaimed: `False`
- step33A1ClosedClaimed: `False`
- proofGrade: `False`

## Current Gap

`STEP33_A1_SUB0_COMBINED_ORDER16_BIASED_RESIDUAL_HORNER_SCALED_REMAINDER_BOUND_GAP`

Parent gap:

`STEP33_A1_SUB0_COMBINED_ORDER16_BIASED_RESIDUAL_HORNER_REMAINDER_ROWS_GAP`

## Next Proof Object

proof-grade bound for primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedResidualHornerScaledRemainderSourceProp; the generator-facing whole-expression interval target is primaryFiniteRow0Parent0Split100Sub0BiasedScaledRemainderIntervalPayloadTarget; then a concrete Step33Sub0CombinedOrder16BiasedResidualHornerFamilyCert with Horner range rows, residual budget rows, cover of [0,1/10], and residualAbs equal to primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedResidualRemainderAbs

## Failure Codes

- closedInterface: `STEP33_A1_SUB0_COMBINED_ORDER16_BIASED_RESIDUAL_HORNER_PAYLOAD_INTERFACE_CLOSED`
- familyRowsMissing: `STEP33_A1_SUB0_COMBINED_ORDER16_BIASED_RESIDUAL_HORNER_FAMILY_PAYLOAD_GAP`
- remainderRowsMissing: `STEP33_A1_SUB0_COMBINED_ORDER16_BIASED_RESIDUAL_HORNER_REMAINDER_ROWS_GAP`
- scaledRemainderBoundMissing: `STEP33_A1_SUB0_COMBINED_ORDER16_BIASED_RESIDUAL_HORNER_SCALED_REMAINDER_BOUND_GAP`
- scaledRemainderIntervalCertMissing: `INTERVAL_CERT_GAP`
- budgetRowsFail: `STEP33_A1_SUB0_COMBINED_ORDER16_BIASED_RESIDUAL_HORNER_BUDGET_CONSTANT_FAIL`

## Guard

Do not claim Step33A.1-A from the interface alone.  The payload must prove the residual-Horner family Valid predicate and the canonical residual budget in Lean.
