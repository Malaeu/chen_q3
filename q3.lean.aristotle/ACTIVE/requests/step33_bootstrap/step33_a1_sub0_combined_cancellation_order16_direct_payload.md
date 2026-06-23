# Step33A.1-A Direct Order16 Payload Ledger

schema: `q3_psdpd_step33_a1_sub0_combined_order16_direct_payload.v1`
proofStatus: `raw_product17_centeredTaylor_bound_checked_but_budget_killed`
concretePayloadKind: `threshold_zero_model`

## Present

- directIntervalAdapterPresent: `True`
- directModelConditionalCheckerPresent: `True`
- directZeroModelConcreteRowsPresent: `True`
- zeroModelRemainderAbsBridgePresent: `True`
- rawProduct17NormalFormPresent: `True`
- rawProduct17CenteredTaylorBudgetKilled: `True`

## Model Symbols

- `primaryFiniteRow0Parent0Split100Sub0CombinedOrder16DirectRemainderSourceProp`: `True`
- `primaryFiniteRow0Parent0Split100Sub0CombinedOrder16DirectIntervalData`: `True`
- `primaryFiniteRow0Parent0Split100Sub0_combinedOrder16DirectInterval_valid_of_horner_remainder`: `True`

## Concrete Zero-Model Symbols

- `primaryFiniteRow0Parent0Split100Sub0CombinedOrder16DirectZeroModelOrder16Abs`: `True`
- `primaryFiniteRow0Parent0Split100Sub0CombinedOrder16DirectZeroModelData`: `True`
- `primaryFiniteRow0Parent0Split100Sub0CombinedOrder16DirectZeroModelHornerRangeData`: `True`
- `primaryFiniteRow0Parent0Split100Sub0CombinedOrder16DirectZeroModelSourceLower`: `True`
- `primaryFiniteRow0Parent0Split100Sub0CombinedOrder16DirectZeroModelSourceUpper`: `True`
- `primaryFiniteRow0Parent0Split100Sub0CombinedOrder16DirectZeroModelIntervalData`: `True`
- `primaryFiniteRow0Parent0Split100Sub0CombinedOrder16DirectZeroModelRemainderSourceProp`: `True`
- `primaryFiniteRow0Parent0Split100Sub0_combinedOrder16DirectZeroModel_remainder_of_componentSource_abs`: `True`
- `primaryFiniteRow0Parent0Split100Sub0_combinedOrder16DirectZeroModel_horner_valid`: `True`
- `primaryFiniteRow0Parent0Split100Sub0_combinedOrder16DirectZeroModel_source_lower_budget`: `True`
- `primaryFiniteRow0Parent0Split100Sub0_combinedOrder16DirectZeroModel_source_upper_budget`: `True`
- `primaryFiniteRow0Parent0Split100Sub0_combinedOrder16DirectZeroModel_order16_budget`: `True`
- `primaryFiniteRow0Parent0Split100Sub0_combinedOrder16DirectZeroModel_order16_remainder_width_pass_rat`: `True`
- `primaryFiniteRow0Parent0Split100Sub0_combinedOrder16DirectZeroModel_valid_of_remainder`: `True`

## Adapter Symbols

- `Step33Sub0CombinedCancellationOrder16DirectIntervalCert`: `True`
- `structure Valid`: `True`
- `to_order16SourceInterval`: `True`
- `to_order16Budget`: `True`
- `to_componentSource_abs_bound`: `True`
- `to_combinedCancellation_order16_abs_bound`: `True`

## Normal-Form Symbols

- `primaryFiniteRow0Parent0Split100Sub0RawProductActual`: `True`
- `primaryFiniteRow0Parent0Split100Sub0RawProductActualOrder17Majorant`: `True`
- `primaryFiniteRow0Parent0Split100Sub0OmegaActualDerivativeMajorant17`: `True`
- `primaryFiniteRow0Parent0Split100Sub0ShapeSqActualDerivativeMajorant17`: `True`
- `step22OmegaArchWeight_contDiff17_normalForm`: `True`
- `primaryFiniteRow0Parent0Split100Sub0_omegaActual_derivative_abs17`: `True`
- `primaryFiniteRow0Parent0Split100Sub0_shapeSqActual_derivative_abs17`: `True`
- `primaryFiniteRow0Parent0Split100Sub0_rawProductActual_order17_abs_of_factor_derivative_abs`: `True`
- `primaryFiniteRow0Parent0Split100Sub0_rawProductActual_order17_abs_of_centeredTaylor17`: `True`
- `primaryFiniteRow0Parent0Split100Sub0_componentProductActual_eq_rawProductDeriv`: `True`
- `primaryFiniteRow0Parent0Split100Sub0_componentProductActual_order16_eq_rawProduct17`: `True`
- `primaryFiniteRow0Parent0Split100Sub0_combinedCancellationOrder16Source_eq_rawProduct17`: `True`
- `primaryFiniteRow0Parent0Split100Sub0_combinedOrder16DirectZeroModel_remainder_of_rawProduct17_abs`: `True`
- `primaryFiniteRow0Parent0Split100Sub0_combinedOrder16DirectZeroModel_remainder_of_centeredTaylor_rawProduct17_budget`: `True`

## RawProduct17 Budget-Audit Symbols

- `primaryFiniteRow0Parent0Split100Sub0RawProductActualOrder17MajorantRat`: `True`
- `primaryFiniteRow0Parent0Split100Sub0RawProduct17LowerScaleBudgetRat`: `True`
- `primaryFiniteRow0Parent0Split100Sub0RawProduct17NominalScaleBudgetRat`: `True`
- `primaryFiniteRow0Parent0Split100Sub0_rawProduct17_lowerScaleBudget_fail_rat`: `True`
- `primaryFiniteRow0Parent0Split100Sub0_rawProduct17_nominalScaleBudget_fail_rat`: `True`

## Concrete Payload Fields

- concretePolynomialDataPresent: `True`
- hornerStageRowsPresent: `True`
- polyRangeRowsPresent: `True`
- sourceLowerUpperRowsPresent: `True`
- order16AbsArithmeticPresent: `True`
- sourceExpressionHashPresent: `True`
- sourceExpressionHash: `4c2561f694c847777dd6ac20441538df364a28d491d2713adf6431bd0e3c0a9f`

## Boundary

- sourceIntervalCertValidClaimed: `False`
- step33A1ClosedClaimed: `False`

## Closed Subgap

`STEP33_A1_SUB0_COMBINED_CANCELLATION_RAW_PRODUCT17_BOUND_INTERFACE_CLOSED`

## Remaining Analytic Premise

centeredTaylor rawProduct17 budget is killed even with TightScaleLower; need a sharper segmented/polynomial certificate for D^17(RawProductActual) or a nonzero cancellation-preserving source model

## Current Gap

`STEP33_A1_SUB0_COMBINED_CANCELLATION_RAW_PRODUCT17_BUDGET_CONSTANT_FAIL`

## Failure Code If Concrete Horner Budget Fails

`STEP33_A1_SUB0_COMBINED_CANCELLATION_DIRECT_ORDER16_CONCRETE_HORNER_BUDGET_GAP`

## Failure Code If RawProduct17 Bound Fails

`STEP33_A1_SUB0_COMBINED_CANCELLATION_RAW_PRODUCT17_BUDGET_CONSTANT_FAIL`

## Next Patch

Do not spend the centeredTaylor rawProduct17 majorant. Choose a sharper segmented interval/Horner certificate for D^17(RawProductActual), or a nonzero cancellation-preserving polynomial model after route review.
