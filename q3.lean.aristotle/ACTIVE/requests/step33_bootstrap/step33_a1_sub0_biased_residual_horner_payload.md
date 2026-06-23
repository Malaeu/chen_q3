# Step33A.1-A Biased Residual-Horner Payload Ledger

schema: `q3_psdpd_step33_a1_sub0_biased_residual_horner_payload.v1`
route: `biased_residual_horner_family_payload`
proofStatus: `biased_residual_horner_payload_interface_checked_missing_family_rows`

## Present

- payloadInterfacePresent: `True`
- hornerFamilyReceiverPresent: `True`
- directResidualAdapterPresent: `True`

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

## Missing Proof Payload

- concreteFamilyDataLeanChecked: `False`
- segmentRowsLeanChecked: `False`
- hornerRangeRowsLeanChecked: `False`
- residualRemainderRowsLeanChecked: `False`
- residualBudgetRowsLeanChecked: `False`
- coverLeanChecked: `False`
- canonicalResidualAbsLeanChecked: `False`
- payloadTargetClaimed: `False`
- residualSourcePropClaimed: `False`
- order16DirectIntervalValidClaimed: `False`
- step33A1ClosedClaimed: `False`
- proofGrade: `False`

## Current Gap

`STEP33_A1_SUB0_COMBINED_ORDER16_BIASED_RESIDUAL_HORNER_FAMILY_PAYLOAD_GAP`

## Next Proof Object

a concrete Step33Sub0CombinedOrder16BiasedResidualHornerFamilyCert with segment data, Horner range rows, residual remainder rows, residual budget rows, cover of [0,1/10], and residualAbs equal to primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedResidualRemainderAbs

## Failure Codes

- closedInterface: `STEP33_A1_SUB0_COMBINED_ORDER16_BIASED_RESIDUAL_HORNER_PAYLOAD_INTERFACE_CLOSED`
- familyRowsMissing: `STEP33_A1_SUB0_COMBINED_ORDER16_BIASED_RESIDUAL_HORNER_FAMILY_PAYLOAD_GAP`
- remainderRowsMissing: `STEP33_A1_SUB0_COMBINED_ORDER16_BIASED_RESIDUAL_HORNER_REMAINDER_ROWS_GAP`
- budgetRowsFail: `STEP33_A1_SUB0_COMBINED_ORDER16_BIASED_RESIDUAL_HORNER_BUDGET_CONSTANT_FAIL`

## Guard

Do not claim Step33A.1-A from the interface alone.  The payload must prove the residual-Horner family Valid predicate and the canonical residual budget in Lean.
