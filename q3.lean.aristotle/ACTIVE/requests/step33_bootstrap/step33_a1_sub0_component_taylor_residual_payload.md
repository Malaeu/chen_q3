# Step33A.1-A Sub0 Component Taylor Residual Payload

Fail-closed route-B payload. This is not Lean proof data and does
not close Step33A.1-A.

## Status

- schema: `q3_psdpd_step33_a1_sub0_component_taylor_residual_payload.v18`
- route: `STEP33_A1_SUB0_COMPONENT_TAYLOR_RESIDUAL`
- chosen route: `B`
- status: `fail_closed_shapesq_same_coeff_payload_checked_component_remainder_gap`
- first failure: `STEP33_A1_SUB0_COMPONENT_TAYLOR_REMAINDER_SOURCE_GAP`
- closed historical failures: `STEP33_A1_SUB0_OMEGA_OMEGAPRIME_TAYLOR_REMAINDER_GAP, STEP33_A1_SUB0_OMEGAPRIME_CENTER_JET_PAYLOAD_GAP, STEP33_A1_SUB0_OMEGAPRIME_ORDER16_INTEGER_BUDGET_PAYLOAD_GAP, STEP33_A1_SUB0_OMEGAPRIME_REMAINDER_BUDGET_PAYLOAD_GAP, STEP33_A1_SUB0_OMEGA_TAYLOR_INTEGRATED_POLY_DERIV_CROSSWALK_GAP, STEP33_A1_SUB0_OMEGA_TAYLOR_CENTER_ANCHOR_PAYLOAD_GAP, STEP33_A1_SUB0_SHAPESQ_INTEGRATED_POLY_DERIV_CROSSWALK_GAP, STEP33_A1_SUB0_SHAPESQ_DERIV_TAYLOR_SOURCE_GAP, STEP33_A1_SUB0_SHAPESQ_DERIV_ORDER16_INTERVAL_CERT_RECEIVER_GAP, STEP33_A1_SUB0_SHAPESQ_DERIV_CENTER_COEFF_BRIDGE_GAP, STEP33_A1_SUB0_SHAPESQ_DERIV_COEFF_INTERVAL_RECEIVER_GAP, STEP33_A1_SUB0_SHAPESQ_DERIV_POWER_SERIES_COEFF0_ROW_GAP, STEP33_A1_SUB0_SHAPESQ_DERIV_POWER_SERIES_COEFF1_ROW_GAP, STEP33_A1_SUB0_SHAPESQ_DERIV_ORDER_SHIFT_RECEIVER_GAP, STEP33_A1_SUB0_SHAPESQ_DERIV_SHAPESQ_DERIVATIVE_RECEIVER_GAP, STEP33_A1_SUB0_SHAPESQ_DERIV_PRODUCT_LEIBNIZ_BOUNDS_PAYLOAD_GAP, STEP33_A1_SUB0_SHAPESQ_DERIV_MAJORANT_RECEIVER_GAP, STEP33_A1_SUB0_SHAPE_POW12_MAJORANT_RECURRENCE_GAP, STEP33_A1_SUB0_SCALED_REALSINC_NORMALIZATION_GAP, STEP33_A1_SUB0_REALSINC_DERIVATIVE_BOUNDS_0_TO_17_GAP, STEP33_A1_SUB0_SHAPESQ_DERIV_TIGHT_SAME_COEFF_TAYLOR_PAYLOAD_GAP, STEP33_A1_SUB0_SHAPESQ_DERIV_EXPLICIT_CAUCHY_ROWS_2_TO_15_ORDER16_GAP`
- advisory source: `browser_proshka_route_advice_not_proof_evidence`
- proof-safe closed fields: `19`
- Lean emitted: `False`

## Local Lean Supplement (2026-06-22)

This generated payload is not regenerated in this patch and remains
fail-closed.  A later local Lean supplement added:

- `Q3/Proofs/PSD_CenteredCoeffRawOmegaAShapeSqTightFullCellSource.lean`
- `Q3/Proofs/PSD_CenteredCoeffRawOmegaAComponentTaylorTightProductSource.lean`

Checked supplement theorems:

- `primaryFiniteRow0Parent0Split100Sub0_shapeSqTightFullCellTaylorSource`
- `primaryFiniteRow0Parent0Split100Sub0_tight_component_product_source`

Meaning: the same-coefficient full-cell ShapeSq source and a proof-grade
nonfinal tight component product source are now Lean-checked.  This does not
set `residualTaylorRemainderAbs`, `componentTaylorProofsPresent`, or
`exactCoefficientAssemblyPassed`.

Current local first gap after the supplement:
`STEP33_A1_SUB0_RAW_DERIV_CLOSED_FORM_TO_TIGHT_PRODUCT_REMAINDER_BRIDGE_GAP`.

## Local Lean Supplement 2 (2026-06-22)

A later local Lean supplement added:

- `Q3/Proofs/PSD_CenteredCoeffRawOmegaAComponentTaylorRawBridge.lean`
- `Q3/Proofs/PSD_CenteredCoeffRawOmegaAComponentTaylorP45Bridge.lean`

Checked supplement theorems:

- `primaryFiniteRow0Parent0Split100Sub0_rawDerivClosedForm_tightProductSource`
- `primaryFiniteRow0Parent0Split100Sub0_assembledRawDerivCoeff_poly_eq_nominalProduct`
- `primaryFiniteRow0Parent0Split100Sub0_fullTaylor_residual_deriv_tight_enclosure`

Meaning: the raw closed form, nominal component product, degree-45 assembled
polynomial, and residual Taylor convention are now connected by a proof-grade
coarse enclosure.  The enclosure constant is
`primaryFiniteRow0Parent0Split100Sub0TightProductAssemblyErrorBudget`; it has
not been proved to meet the final target budget.

Current local first gap after supplement 2:
`STEP33_A1_SUB0_TIGHT_PRODUCT_BUDGET_FINAL_COMPARISON_GAP`.

## Target

- theorem: `primaryFiniteRow0Parent0Split100Sub0_fullTaylor_residual_deriv_taylor_enclosure`
- file: `Q3/Proofs/PSD_CenteredCoeffRawOmegaAEndpointHighOrderSupport.lean`
- component degree: `15`
- assembled degree: `45`
- center: `1/20`
- radius: `1/20`
- target interval: `[-94119513411/500000000000000000000000000000, 1866608532757/500000000000000000000000000000]`

```text
theorem primaryFiniteRow0Parent0Split100Sub0_fullTaylor_residual_deriv_taylor_enclosure {eta : Real} (heta : eta in Set.Icc 0 (1/10)) : norm ((RawIntegrandDerivClosedForm eta - rawOmegaATaylorPolynomial 15 (1/20) ResidualDerivmodelCoeff eta) - rawOmegaATaylorPolynomial 45 (1/20) ResidualTaylorCoeff eta) <= ResidualTaylorRemainderAbs
```

## Model Derivative Coefficients

Extracted from local Lean definition `primaryFiniteRow0Parent0Split100Sub0ResidualDerivmodelCoeff`.

| i | coeff | source line |
| --- | --- | --- |
| 0 | `2814585322345983/31250000000000000` | 49 |
| 1 | `432682670395380743/250000000000000000` | 50 |
| 2 | `-2076189217694411487/1000000000000000000` | 51 |
| 3 | `-155822302127901237/12500000000000000` | 52 |
| 4 | `248352666423100477/12500000000000000` | 53 |
| 5 | `32291651785944130749/500000000000000000` | 54 |
| 6 | `-69999411432932463909/500000000000000000` | 55 |
| 7 | `-34707798540256129409/125000000000000000` | 56 |
| 8 | `836575734719049511113/1000000000000000000` | 57 |
| 9 | `100643501888413806697/100000000000000000` | 58 |
| 10 | `-897573400754971084771/200000000000000000` | 59 |
| 11 | `-142205390337268351947/50000000000000000` | 60 |
| 12 | `5554290524724778241613/250000000000000000` | 61 |
| 13 | `916884525703826724093/250000000000000000` | 62 |
| 14 | `-19999872807938988432933/200000000000000000` | 63 |
| 15 | `62148786708414316877/2500000000000000` | 64 |

## Required Component Fields

- `omegaCoeff[0..15]`
- `omegaDerivCoeff[0..15]`
- `shapeCoeff[0..15]`
- `shapeDerivCoeff[0..15]`
- `omegaRemainderAbs`
- `omegaDerivRemainderAbs`
- `shapeRemainderAbs`
- `shapeDerivRemainderAbs`
- `assembledRawDerivCoeff[0..45]`
- `residualTaylorCoeff[0..45]`
- `residualTaylorRemainderAbs`
- `residualPolynomialLower` / `residualPolynomialUpper`
- `finalResidualLower` / `finalResidualUpper`

## Component Closure Ledger

- omega: `formal_center_anchor_available_missing_component_assembly`
- omegaDeriv: `formal_available_not_assembled`
- shape: `same_coefficient_shapesq_deriv_payload_formal_missing_component_taylor_remainder_source`
- shapeDeriv: `endpoint_deriv_bounds_formal_missing_component_taylor_receiver`

## OmegaDeriv Taylor Source

- proof-grade: `True`
- valid theorem: `Step33Sub0OmegaPrimeTaylorRemainderCert.omegaPrimeGeneratedRemainderCert_valid`
- theorem found: `True`
- payload generated valid cert proved: `True`
- coeff source: `omegaPrimePayload.generatorFields.coeff`
- remainder source: `omegaPrimePayload.generatorFields.remainder.remainderAbs`

## OmegaTaylor Crosswalk Source

- proof-grade: `True`
- theorem: `Step33Sub0OmegaPrimeTaylorRemainderCert.integratedPoly_deriv_eq_poly`
- theorem found: `True`
- first missing: `STEP33_A1_SUB0_SHAPE_TAYLOR_REMAINDER_GAP`

## OmegaTaylor Center Anchor Source

- proof-grade: `True`
- theorem: `primaryFiniteRow0Parent0Split100Sub0_omegaTaylor_center_anchor`
- theorem found: `True`
- anchor coeff: `-106643293527304552591821287391961407544994279623740339344557023924606219973211357105502357/20000000000000000000000000000000000000000000000000000000000000000000000000000000000000000`
- anchor error abs: `44158940358707181789873075635276724557718455490191678953816505502357/80000000000000000000000000000000000000000000000000000000000000000000000000000000000000000`

## Component Taylor Status

- omegaDerivTaylor: `FORMAL`
- omegaDerivTaylor Lean theorem: `Step33Sub0OmegaPrimeTaylorRemainderCert.omegaPrimeGeneratedRemainderCert_valid`
- omegaTaylor: `CROSSWALK_AND_CENTER_ANCHOR_FORMAL_MISSING_COMPONENT_ASSEMBLY`
- shapeTaylor: `SHAPESQ_DERIV_SAME_COEFF_PAYLOAD_FORMAL_MISSING_COMPONENT_REMAINDER_SOURCE`
- shapeDerivTaylor: `ENDPOINT_DERIV_BOUNDS_FORMAL_MISSING_TAYLOR_COEFF_REMAINDER_RECEIVER`
- shape endpoint bounds available: `True`
- shapeSq integrated receiver available: `True`
- shapeSq deriv Taylor source available: `True`
- shapeSq deriv interval cert receiver available: `True`
- shapeSq deriv center-coeff bridge available: `True`
- shapeSq deriv center-coeff interval receiver available: `True`
- shapeSq deriv coeff0 row available: `True`
- shapeSq deriv coeff1 row available: `True`
- shapeSq deriv order-shift receiver available: `True`
- shapeSq deriv shape-square derivative receiver available: `True`
- coarse ShapeSqDeriv valid payload available: `True`
- same-coeff ShapeSqDeriv tight payload available: `True`
- shapeSq deriv coeff rows closed: `2 / 16`
- shapeSq deriv order16 uniform bound available: `True`
- shapeSq value Taylor source available: `True`
- shape Taylor receiver gap: `STEP33_A1_SUB0_COMPONENT_TAYLOR_REMAINDER_SOURCE_GAP`
- shapeDeriv Taylor receiver gap: `STEP33_A1_SUB0_SHAPEDERIV_ENDPOINT_TO_TAYLOR_COEFF_REMAINDER_RECEIVER_GAP`
- assembly Lean written: `False`
- overall proof safe: `False`

## Shape Endpoint Source

- endpoint proof-grade: `True`
- Taylor payload proof-grade: `False`
- shapeSq endpoint theorem: `primaryFiniteRow0Parent0Split100Sub0ShapeSqEndpointBounds_generated`
- shapeSq endpoint theorem found: `True`
- shape value bounds theorem: `primaryFiniteRow0Parent0Split100Sub0ShapeValueBounds_of_deriv_bounds_and_anchor_generated`
- shape value bounds theorem found: `True`
- shape deriv anchor bounds theorem: `primaryFiniteRow0Parent0Split100Sub0ShapeDerivAnchorBounds_generated`
- shape deriv anchor bounds theorem found: `True`
- shape deriv interval theorem: `primaryFiniteRow0Parent0Split100Sub0ShapeDerivClosedForm_interval_bounds_of_anchor_second_deriv_bound_generated`
- shape deriv interval theorem found: `True`
- receiver needed: A proof-grade Taylor source for the derivative of the shape-square term, then the checked integrated receiver can produce the value Taylor enclosure.  Endpoint/value/deriv interval facts alone do not provide the high-order Taylor source.
- why not Taylor payload: The existing shape endpoint facts bound the shape-square value and first derivative on the subchunk.  They do not provide shapeCoeff[0..15], shapeDerivCoeff[0..15], shapeRemainderAbs, or shapeDerivRemainderAbs in the component Taylor payload convention.

## ShapeSq Integrated Taylor Receiver

- proof-grade: `True`
- receiver theorem: `shapeSqTaylor_bound_of_shapeSqDerivTaylor_bound`
- receiver theorem found: `True`
- integrated crosswalk theorem: `integratedTaylorPolynomial_deriv_eq_base`
- integrated crosswalk theorem found: `True`
- failure closed: `STEP33_A1_SUB0_SHAPESQ_INTEGRATED_POLY_DERIV_CROSSWALK_GAP`
- next missing: `STEP33_A1_SUB0_SHAPESQ_DERIV_TAYLOR_SOURCE_GAP`
- boundary: This receiver is not a shape Taylor certificate by itself.  It requires a proof-grade Taylor/remainder source for the derivative of shape-square, plus a center anchor budget.

## ShapeSq Deriv Taylor Source

- proof-grade: `True`
- bridge theorem: `shapeSqDerivTaylor_bound_of_endpoint_bounds`
- bridge theorem found: `True`
- source theorem: `primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivTaylorSource_generated`
- source theorem found: `True`
- coeff def: `primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivTaylorCoeff_generated`
- remainder def: `primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivTaylorRemainderAbs_generated`
- constant center: `-3/40`
- constant remainder abs: `3/40`
- failure closed: `STEP33_A1_SUB0_SHAPESQ_DERIV_TAYLOR_SOURCE_GAP`
- next missing: `STEP33_A1_SUB0_SHAPESQ_CONSTANT_DERIV_TAYLOR_BUDGET_GAP`
- boundary: This is a proof-grade constant Taylor source for deriv(E^2), not a final component Taylor closure.  The coarse remainder 3/40 must still pass the shape-square integrated budget and then the raw-derivative assembly budget.

## ShapeSq Deriv Interval Cert Receiver

- proof-grade receiver: `True`
- source def: `primaryFiniteRow0Parent0Split100Sub0ShapeSqDeriv`
- source def found: `True`
- cert structure: `ShapeSqDerivTaylorIntervalCert`
- cert structure found: `True`
- valid predicate: `ShapeSqDerivTaylorIntervalCert.Valid`
- valid predicate found: `True`
- Taylor input theorem: `ShapeSqDerivTaylorIntervalCert.Valid.toTaylorInputs`
- Taylor input theorem found: `True`
- source theorem: `ShapeSqDerivTaylorIntervalCert.Valid.toShapeSqDerivTaylorSource`
- source theorem found: `True`
- one-segment constructor: `ShapeSqDerivTaylorIntervalCert.single`
- one-segment constructor found: `True`
- one-segment validity constructor: `ShapeSqDerivTaylorIntervalCert.Valid.of_single_segment`
- one-segment validity constructor found: `True`
- one-segment bookkeeping closed: `True`
- compact abs constructor: `ShapeSqDerivTaylorIntervalCert.singleAbs`
- compact abs constructor found: `True`
- compact abs validity constructor: `ShapeSqDerivTaylorIntervalCert.Valid.of_single_abs`
- compact abs validity constructor found: `True`
- compact abs bookkeeping closed: `True`
- failure closed: `STEP33_A1_SUB0_SHAPESQ_DERIV_ORDER16_INTERVAL_CERT_RECEIVER_GAP`
- next missing: `STEP33_A1_SUB0_SHAPESQ_DERIV_ORDER16_ZERO_CELL_PROOF_GAP`
- boundary: This is only the Lean-checked interval-certificate receiver for future rational center-jet and order-16 rows.  The one-segment and compact absolute-error constructors close zero-cell bookkeeping only; they are not the generated ShapeSqDeriv payload and they do not close the coarse constant-source budget failure.

## ShapeSq Deriv Center-Coeff Bridge

- proof-grade bridge: `True`
- power series def: `primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivPowerSeriesAtCenter`
- power series def found: `True`
- HasFPowerSeries theorem: `primaryFiniteRow0Parent0Split100Sub0_shapeSqDeriv_hasFPowerSeriesAt_center`
- HasFPowerSeries theorem found: `True`
- center jet theorem: `primaryFiniteRow0Parent0Split100Sub0_shapeSqDeriv_centerJet_eq_powerSeriesCoeff`
- center jet theorem found: `True`
- valid wrapper theorem: `primaryFiniteRow0Parent0Split100Sub0_shapeSqDeriv_valid_of_powerSeriesCoeff_abs`
- valid wrapper theorem found: `True`
- interval wrapper theorem: `primaryFiniteRow0Parent0Split100Sub0_shapeSqDeriv_valid_of_powerSeriesCoeff_interval`
- interval wrapper theorem found: `True`
- proof-grade interval receiver: `True`
- failure closed: `STEP33_A1_SUB0_SHAPESQ_DERIV_CENTER_COEFF_BRIDGE_GAP`
- interval receiver failure closed: `STEP33_A1_SUB0_SHAPESQ_DERIV_COEFF_INTERVAL_RECEIVER_GAP`
- next missing: `STEP33_A1_SUB0_SHAPESQ_DERIV_EXPLICIT_CAUCHY_POWER_SERIES_GAP`
- boundary: This is only the Lean-checked bridge from the ShapeSqDeriv center jet to power-series coefficients and the compact absolute-error/interval certificate wrappers.  It does not provide exact rational coefficient rows or the order-16 uniform bound needed by ShapeSqDerivTaylorIntervalCert.Valid.

## ShapeSq Deriv Order-Shift Receiver

- proof-grade receiver: `True`
- order-shift theorem: `primaryFiniteRow0Parent0Split100Sub0_shapeSqDeriv_iteratedDeriv_eq_shapeSq_succ`
- order-shift theorem found: `True`
- coefficient receiver theorem: `primaryFiniteRow0Parent0Split100Sub0_shapeSqDeriv_powerSeriesCoeff_abs_of_shapeSq_succ_abs`
- coefficient receiver theorem found: `True`
- order16 receiver theorem: `primaryFiniteRow0Parent0Split100Sub0_shapeSqDeriv_order16_abs_of_shapeSq_order17_abs`
- order16 receiver theorem found: `True`
- failure closed: `STEP33_A1_SUB0_SHAPESQ_DERIV_ORDER_SHIFT_RECEIVER_GAP`
- next missing: `STEP33_A1_SUB0_SHAPESQ_DERIV_ITERATED_LEIBNIZ_CROSSWALK_GAP`
- boundary: This is only the Lean-checked structural receiver iteratedDeriv^j(ShapeSqDeriv) = iteratedDeriv^(j+1)(shape^2), plus coefficient-row and order-16 receiver interfaces.  It does not provide the product-Leibniz/Cauchy bounds for derivatives of the shape function, and it does not close rows 2..15 or the order-16 uniform bound.

## ShapeSq Deriv Shape-Square Derivative Receiver

- proof-grade receiver: `True`
- theorem: `primaryFiniteRow0Parent0Split100Sub0_shapeSqDeriv_valid_of_shapeSq_derivative_abs`
- theorem found: `True`
- failure closed: `STEP33_A1_SUB0_SHAPESQ_DERIV_SHAPESQ_DERIVATIVE_RECEIVER_GAP`
- next missing: `STEP33_A1_SUB0_SHAPESQ_DERIV_PRODUCT_LEIBNIZ_BOUNDS_PAYLOAD_GAP`
- boundary: This is only the Lean-checked normalization receiver from bounds on iterated derivatives of the shape-square function into ShapeSqDerivTaylorIntervalCert.Valid.  It does not prove the product-Leibniz formula or any Cauchy/derivative bounds for the shape function itself.

## ShapeSq Deriv Product-Bounds Receiver

- proof-grade receiver: `True`
- Lean file: `/Users/emalam/Documents/GitHub/rh_lean_01_2026/q3.lean.aristotle/Q3/Proofs/PSD_CenteredCoeffRawOmegaAShapeSqProductBounds.lean`
- theorem: `primaryFiniteRow0Parent0Split100Sub0_shapeSq_derivative_abs_of_shape_derivative_abs`
- theorem found: `True`
- failure closed: `STEP33_A1_SUB0_SHAPESQ_DERIV_PRODUCT_LEIBNIZ_BOUNDS_PAYLOAD_GAP`
- next missing: `STEP33_A1_SUB0_SHAPESQ_DERIV_SHAPE_DERIVATIVE_BOUNDS_PAYLOAD_GAP`
- boundary: This is only the Lean-checked Mathlib product-bound receiver from proof-grade derivative bounds on the active shape function to derivative bounds for the square of that shape function.  It does not provide those shape derivative bounds, rational rows 2..15, or the order-17 full-cell bound consumed by the ShapeSqDeriv interval certificate.

## ShapeSq Deriv Majorant Receiver

- proof-grade receiver: `True`
- Lean file: `/Users/emalam/Documents/GitHub/rh_lean_01_2026/q3.lean.aristotle/Q3/Proofs/PSD_CenteredCoeffRawOmegaAShapeSqDerivMajorantReceiver.lean`
- theorem: `primaryFiniteRow0Parent0Split100Sub0_shapeSqDeriv_valid_of_shape_derivative_abs`
- theorem found: `True`
- failure closed: `STEP33_A1_SUB0_SHAPESQ_DERIV_MAJORANT_RECEIVER_GAP`
- next missing: `STEP33_A1_SUB0_SHAPE_DERIVATIVE_BOUNDS_0_TO_17_PAYLOAD_GAP`
- boundary: This is only the Lean-checked receiver from proof-grade derivative majorants for the active shape function into ShapeSqDerivTaylorIntervalCert.Valid.  It does not provide the shape derivative majorants through order 17, rational rows 2..15, the order-17 full-cell bound, or raw-derivative assembly.

## Shape Derivative Pow12 Majorant Receiver

- proof-grade receiver: `True`
- Lean file: `/Users/emalam/Documents/GitHub/rh_lean_01_2026/q3.lean.aristotle/Q3/Proofs/PSD_CenteredCoeffRawOmegaAShapeDerivativeMajorantReceiver.lean`
- theorem: `primaryFiniteRow0Parent0Split100Sub0_shape_derivative_abs_of_scaledSinc_abs`
- theorem found: `True`
- failure closed: `STEP33_A1_SUB0_SHAPE_POW12_MAJORANT_RECURRENCE_GAP`
- next missing: `STEP33_A1_SUB0_SCALED_REALSINC_DERIVATIVE_BOUNDS_0_TO_17_GAP`
- boundary: This is only the Lean-checked receiver from proof-grade derivative majorants for the active scaled realSinc factor into proof-grade derivative majorants for the active shape function. It does not provide scaled-realSinc derivative bounds through order 17, component Taylor rows, or raw-derivative assembly.

## Scaled RealSinc Normalization Receiver

- proof-grade receiver: `True`
- Lean file: `/Users/emalam/Documents/GitHub/rh_lean_01_2026/q3.lean.aristotle/Q3/Proofs/PSD_CenteredCoeffRawOmegaAShapeDerivativeMajorantReceiver.lean`
- theorem: `primaryFiniteRow0Parent0Split100Sub0_scaledSinc_derivative_abs_of_realSinc_abs`
- theorem found: `True`
- failure closed: `STEP33_A1_SUB0_SCALED_REALSINC_NORMALIZATION_GAP`
- next missing: `STEP33_A1_SUB0_REALSINC_DERIVATIVE_BOUNDS_0_TO_17_GAP`
- boundary: This is only the Lean-checked affine-scale normalization receiver from proof-grade derivative majorants for realSinc itself on Set.Icc 0 (1/400) into derivative majorants for the active scaled realSinc factor eta |-> realSinc (eta / 40). It does not provide the realSinc derivative majorants through order 17, component Taylor rows, or raw-derivative assembly.

## Coarse RealSinc-to-ShapeSq Payload

- proof-grade coarse ShapeSqDeriv Valid: `True`
- realSinc payload file: `/Users/emalam/Documents/GitHub/rh_lean_01_2026/q3.lean.aristotle/Q3/Proofs/PSD_CenteredCoeffRawOmegaARealSincDerivativePayload.lean`
- realSinc majorant theorem: `coarseTwoBaseAbs_providesAnalyticMajorant`
- realSinc majorant theorem found: `True`
- scaled realSinc theorem: `primaryFiniteRow0Parent0Split100Sub0_scaledSinc_derivative_abs_of_coarseTwo`
- scaled realSinc theorem found: `True`
- shape derivative theorem: `primaryFiniteRow0Parent0Split100Sub0_shape_derivative_abs_of_coarseTwo_rational`
- shape derivative theorem found: `True`
- ShapeSqDeriv Valid theorem: `primaryFiniteRow0Parent0Split100Sub0_shapeSqDeriv_valid_of_coarseTwo`
- ShapeSqDeriv Valid theorem found: `True`
- next missing: `STEP33_A1_SUB0_SHAPESQ_DERIV_EXPLICIT_CAUCHY_ROWS_2_TO_15_ORDER16_GAP`
- route-level failure: `STEP33_A1_SUB0_SHAPESQ_DERIV_TIGHT_SAME_COEFF_TAYLOR_PAYLOAD_GAP`
- boundary: The coarseTwo chain is a Lean-checked proof-grade ShapeSqDerivTaylorIntervalCert.Valid source.  It retires the old unscaled-realSinc detector gap for the coarse path, but it uses zero coefficients with a huge uniform budget.  It is not the tight same-coefficient payload consumed by the active component Taylor residual route.

## ShapeSq Deriv Same-Coeff Tight Payload

- proof-grade same-coeff payload: `True`
- Lean file: `/Users/emalam/Documents/GitHub/rh_lean_01_2026/q3.lean.aristotle/Q3/Proofs/PSD_CenteredCoeffRawOmegaAShapeSqDerivTightPayload.lean`
- tight coeff def: `primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivTightCoeff`
- tight coeff def found: `True`
- same-coeff theorem: `primaryFiniteRow0Parent0Split100Sub0_shapeSqDeriv_tightCoeff_eq_generated`
- same-coeff theorem found: `True`
- valid theorem: `primaryFiniteRow0Parent0Split100Sub0_shapeSqDeriv_tight_valid`
- valid theorem found: `True`
- Taylor source theorem: `primaryFiniteRow0Parent0Split100Sub0_shapeSqDerivTightTaylorSource`
- Taylor source theorem found: `True`
- generated coeff def: `primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivTaylorCoeff_generated`
- generated coeff def found: `True`
- budget kind: `coarse_same_coefficient_nonfinal`
- failure closed: `STEP33_A1_SUB0_SHAPESQ_DERIV_EXPLICIT_CAUCHY_ROWS_2_TO_15_ORDER16_GAP`
- next missing: `STEP33_A1_SUB0_COMPONENT_TAYLOR_REMAINDER_SOURCE_GAP`
- boundary: This is a Lean-checked same-coefficient ShapeSqDeriv Taylor source: its coefficient stream is the active generated stream used by component assembly.  Its row/order budgets are still coarse, so it does not prove the final component Taylor remainder budget or the residual interval theorem.

## ShapeSq Deriv Center-Coeff Rows

- proof-grade row0: `True`
- proof-grade row1: `True`
- Lean file: `/Users/emalam/Documents/GitHub/rh_lean_01_2026/q3.lean.aristotle/Q3/Proofs/PSD_CenteredCoeffRawOmegaAShapeSqDerivCoeffRows.lean`
- row0 lower def: `primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivCoeff0Lower_generated`
- row0 lower def found: `True`
- row0 upper def: `primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivCoeff0Upper_generated`
- row0 upper def found: `True`
- row0 interval theorem: `primaryFiniteRow0Parent0Split100Sub0_shapeSqDeriv_powerSeriesCoeff0_interval_generated`
- row0 interval theorem found: `True`
- row1 lower def: `primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivCoeff1Lower_generated`
- row1 lower def found: `True`
- row1 upper def: `primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivCoeff1Upper_generated`
- row1 upper def found: `True`
- row1 interval theorem: `primaryFiniteRow0Parent0Split100Sub0_shapeSqDeriv_powerSeriesCoeff1_interval_generated`
- row1 interval theorem found: `True`
- rows closed: `2 / 16`
- missing rows: `[2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]`
- order16 uniform bound present: `False`
- failure closed: `STEP33_A1_SUB0_SHAPESQ_DERIV_POWER_SERIES_COEFF0_ROW_GAP`
- next missing: `STEP33_A1_SUB0_SHAPESQ_DERIV_EXPLICIT_CAUCHY_ROWS_2_TO_15_ORDER16_GAP`
- boundary: This source closes only the j=0 and j=1 rational interval rows for the ShapeSqDeriv center power series.  Rows 2..15 and the full-cell order-16 uniform bound are still missing, so it is not yet a ShapeSqDerivTaylorIntervalCert.Valid payload.

## ShapeSq Value Taylor Source

- proof-grade: `True`
- receiver theorem: `shapeSqTaylor_bound_of_shapeSqDerivTaylor_bound`
- receiver theorem found: `True`
- source theorem: `primaryFiniteRow0Parent0Split100Sub0ShapeSqTaylorSource_generated`
- source theorem found: `True`
- coeff def: `primaryFiniteRow0Parent0Split100Sub0ShapeSqTaylorCoeff_generated`
- anchor coeff def: `primaryFiniteRow0Parent0Split100Sub0ShapeSqTaylorAnchorCoeff_generated`
- anchor error def: `primaryFiniteRow0Parent0Split100Sub0ShapeSqTaylorAnchorErrorAbs_generated`
- remainder def: `primaryFiniteRow0Parent0Split100Sub0ShapeSqTaylorRemainderAbs_generated`
- constant remainder abs: `1/250`
- failure closed: `None`
- next missing: `STEP33_A1_SUB0_SHAPESQ_CONSTANT_DERIV_TAYLOR_BUDGET_GAP`
- boundary: This is a proof-grade value Taylor enclosure for shape-square built from the checked constant derivative source and the center anchor budget.  It is not raw-derivative assembly and the coarse 1/250 remainder is expected to be too wide for the final residual budget unless a later exact assembly test proves otherwise.

## Proof Status

- exactCoefficientAssemblyPassed: `False`
- componentTaylorProofsPresent: `False`
- omegaTaylorIntegratedPolyDerivCrosswalkProofPresent: `True`
- omegaTaylorCenterAnchorPayloadPresent: `True`
- omegaDerivTaylorProofPresent: `True`
- shapeEndpointBoundsProofPresent: `True`
- shapeSqIntegratedTaylorReceiverPresent: `True`
- shapeSqDerivTaylorSourcePresent: `True`
- shapeSqDerivIntervalCertReceiverPresent: `True`
- shapeSqDerivCenterCoeffBridgePresent: `True`
- shapeSqDerivCenterCoeffIntervalReceiverPresent: `True`
- shapeSqDerivCenterCoeff0RowPresent: `True`
- shapeSqDerivCenterCoeff1RowPresent: `True`
- shapeSqDerivOrderShiftReceiverPresent: `True`
- shapeSqDerivShapeSqDerivativeReceiverPresent: `True`
- shapeSqDerivProductBoundsReceiverPresent: `True`
- shapeSqDerivMajorantReceiverPresent: `True`
- shapeDerivativePow12MajorantReceiverPresent: `True`
- scaledRealSincNormalizationReceiverPresent: `True`
- coarseRealSincDerivativeMajorantPresent: `True`
- coarseScaledRealSincBoundsPresent: `True`
- coarseShapeDerivativeBoundsPresent: `True`
- coarseShapeSqDerivValidPresent: `True`
- shapeSqDerivTightSameCoeffPayloadPresent: `True`
- shapeSqDerivCenterCoeffRowsClosedCount: `2`
- shapeSqDerivCenterCoeffRowsRequiredCount: `16`
- shapeSqDerivOrder16UniformBoundPresent: `True`
- shapeSqTaylorSourcePresent: `True`
- shapeTaylorReceiverPresent: `True`
- shapeDerivTaylorReceiverPresent: `False`
- omegaDerivTaylorProofAssembledIntoRawDerivative: `False`
- residualPolynomialRangePassed: `False`
- finalBudgetPassed: `False`
- proofSafeClosedFields: `19`
- outLeanWritten: `False`

## Existing Lean Inputs

- modelDerivCoeffSource: `primaryFiniteRow0Parent0Split100Sub0ResidualDerivmodelCoeff`
- modelDerivCoeffCount: `16`
- fullTaylorPolynomialDerivativeCrosswalk: `primaryFiniteRow0Parent0Split100Sub0_fullTaylor_polynomial_deriv_eq_derivmodel`
- fullTaylorResidualDerivativeCrosswalk: `primaryFiniteRow0Parent0Split100Sub0_fullTaylor_residual_deriv_eq_closedForm`
- fullTaylorDirectValidityBridge: `primaryFiniteRow0Parent0Split100Sub0_fullTaylor_direct_segment_cert_valid_of_residual_bounds`
- omegaDerivTaylorValidCert: `Step33Sub0OmegaPrimeTaylorRemainderCert.omegaPrimeGeneratedRemainderCert_valid`
- omegaTaylorIntegratedPolyDerivCrosswalk: `Step33Sub0OmegaPrimeTaylorRemainderCert.integratedPoly_deriv_eq_poly`
- omegaTaylorCenterAnchor: `primaryFiniteRow0Parent0Split100Sub0_omegaTaylor_center_anchor`
- shapeSqEndpointBounds: `primaryFiniteRow0Parent0Split100Sub0ShapeSqEndpointBounds_generated`
- shapeSqEndpointReceiver: `ShapeSqEndpointBoundsCert`
- shapeSqIntegratedTaylorReceiver: `shapeSqTaylor_bound_of_shapeSqDerivTaylor_bound`
- shapeSqIntegratedTaylorCrosswalk: `integratedTaylorPolynomial_deriv_eq_base`
- shapeSqDerivTaylorBridge: `shapeSqDerivTaylor_bound_of_endpoint_bounds`
- shapeSqDerivTaylorSource: `primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivTaylorSource_generated`
- shapeSqDerivIntervalCertReceiver: `ShapeSqDerivTaylorIntervalCert.Valid.toShapeSqDerivTaylorSource`
- shapeSqDerivIntervalCertSingle: `ShapeSqDerivTaylorIntervalCert.single`
- shapeSqDerivIntervalCertSingleValid: `ShapeSqDerivTaylorIntervalCert.Valid.of_single_segment`
- shapeSqDerivIntervalCertSingleAbs: `ShapeSqDerivTaylorIntervalCert.singleAbs`
- shapeSqDerivIntervalCertSingleAbsValid: `ShapeSqDerivTaylorIntervalCert.Valid.of_single_abs`
- shapeSqDerivCenterPowerSeries: `primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivPowerSeriesAtCenter`
- shapeSqDerivCenterHasFPowerSeries: `primaryFiniteRow0Parent0Split100Sub0_shapeSqDeriv_hasFPowerSeriesAt_center`
- shapeSqDerivCenterJetCoeff: `primaryFiniteRow0Parent0Split100Sub0_shapeSqDeriv_centerJet_eq_powerSeriesCoeff`
- shapeSqDerivCenterDerivFormula: `primaryFiniteRow0Parent0Split100Sub0_shapeSqDeriv_center_deriv_formula`
- shapeSqDerivCenterCoeffValid: `primaryFiniteRow0Parent0Split100Sub0_shapeSqDeriv_valid_of_powerSeriesCoeff_abs`
- shapeSqDerivCenterCoeffIntervalValid: `primaryFiniteRow0Parent0Split100Sub0_shapeSqDeriv_valid_of_powerSeriesCoeff_interval`
- shapeSqDerivOrderShift: `primaryFiniteRow0Parent0Split100Sub0_shapeSqDeriv_iteratedDeriv_eq_shapeSq_succ`
- shapeSqDerivCoeffAbsFromShapeSqSucc: `primaryFiniteRow0Parent0Split100Sub0_shapeSqDeriv_powerSeriesCoeff_abs_of_shapeSq_succ_abs`
- shapeSqDerivOrder16FromShapeSqOrder17: `primaryFiniteRow0Parent0Split100Sub0_shapeSqDeriv_order16_abs_of_shapeSq_order17_abs`
- shapeSqDerivValidFromShapeSqDerivativeAbs: `primaryFiniteRow0Parent0Split100Sub0_shapeSqDeriv_valid_of_shapeSq_derivative_abs`
- shapeSqDerivProductBounds: `primaryFiniteRow0Parent0Split100Sub0_shapeSq_derivative_abs_of_shape_derivative_abs`
- shapeSqDerivMajorantReceiver: `primaryFiniteRow0Parent0Split100Sub0_shapeSqDeriv_valid_of_shape_derivative_abs`
- shapeDerivativePow12MajorantReceiver: `primaryFiniteRow0Parent0Split100Sub0_shape_derivative_abs_of_scaledSinc_abs`
- scaledRealSincNormalizationReceiver: `primaryFiniteRow0Parent0Split100Sub0_scaledSinc_derivative_abs_of_realSinc_abs`
- coarseRealSincMajorant: `coarseTwoBaseAbs_providesAnalyticMajorant`
- coarseScaledRealSincBounds: `primaryFiniteRow0Parent0Split100Sub0_scaledSinc_derivative_abs_of_coarseTwo`
- coarseShapeDerivativeBounds: `primaryFiniteRow0Parent0Split100Sub0_shape_derivative_abs_of_coarseTwo_rational`
- coarseShapeSqDerivValid: `primaryFiniteRow0Parent0Split100Sub0_shapeSqDeriv_valid_of_coarseTwo`
- shapeSqDerivTightCoeff: `primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivTightCoeff`
- shapeSqDerivTightCoeffEqGenerated: `primaryFiniteRow0Parent0Split100Sub0_shapeSqDeriv_tightCoeff_eq_generated`
- shapeSqDerivTightValid: `primaryFiniteRow0Parent0Split100Sub0_shapeSqDeriv_tight_valid`
- shapeSqDerivTightTaylorSource: `primaryFiniteRow0Parent0Split100Sub0_shapeSqDerivTightTaylorSource`
- shapeSqDerivCenterCoeff0Lower: `primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivCoeff0Lower_generated`
- shapeSqDerivCenterCoeff0Upper: `primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivCoeff0Upper_generated`
- shapeSqDerivCenterCoeff0Interval: `primaryFiniteRow0Parent0Split100Sub0_shapeSqDeriv_powerSeriesCoeff0_interval_generated`
- shapeSqDerivCenterCoeff1Lower: `primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivCoeff1Lower_generated`
- shapeSqDerivCenterCoeff1Upper: `primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivCoeff1Upper_generated`
- shapeSqDerivCenterCoeff1Interval: `primaryFiniteRow0Parent0Split100Sub0_shapeSqDeriv_powerSeriesCoeff1_interval_generated`
- shapeSqTaylorSource: `primaryFiniteRow0Parent0Split100Sub0ShapeSqTaylorSource_generated`
- shapeSqTaylorCoeff: `primaryFiniteRow0Parent0Split100Sub0ShapeSqTaylorCoeff_generated`
- shapeValueBounds: `primaryFiniteRow0Parent0Split100Sub0ShapeValueBounds_of_deriv_bounds_and_anchor_generated`
- shapeDerivAnchorBounds: `primaryFiniteRow0Parent0Split100Sub0ShapeDerivAnchorBounds_generated`
- shapeDerivIntervalBounds: `primaryFiniteRow0Parent0Split100Sub0ShapeDerivClosedForm_interval_bounds_of_anchor_second_deriv_bound_generated`

## Coarse ShapeSq Taylor Payload Route Kill

- failure code: `STEP33_A1_SUB0_COARSE_SHAPESQ_TAYLOR_PRIMARY_RESIDUAL_CROSSWALK_FAIL`
- checked source retained: `primaryFiniteRow0Parent0Split100Sub0_shapeSqTaylorSource_of_coarseTwo`
- wrong coefficient object: `primaryFiniteRow0Parent0Split100Sub0CoarseTwoShapeSqTaylorCoeff`
- active certificate object: `primaryFiniteRow0Parent0Split100Sub0RawTaylorCoeffCert`
- live receiver target: `1866608532757 / 500000000000000000000000000000`
- decision: Do not spend the coarse ShapeSq Taylor source as full-Taylor Step33A.1-A payload evidence.

## Proshka Decision

- chosen: `B_component_taylor_route`
- latest review: `2026_06_22_same_expression_interval_fork`
- route-level first patch: `primaryFiniteRow0Parent0Split100Sub0_shapeSqDeriv_tight_valid`
- route-level failure code: `STEP33_A1_SUB0_SHAPESQ_DERIV_TIGHT_SAME_COEFF_TAYLOR_PAYLOAD_GAP`
- local first subgap: `STEP33_A1_SUB0_COMPONENT_TAYLOR_REMAINDER_SOURCE_GAP`
- latest why: Build the tight same-coefficient ShapeSqDeriv Taylor payload before attempting the final residual interval theorem.  A direct same-expression interval proof is a monolith until the tight component source exists, and another receiver would add no proof data.
- latest do not: Do not set coeff = 0, do not subtract independent raw/poly boxes, do not add another receiver, and do not attack the final residual interval before the Lean-checked tight source and coefficient-assembly crosswalk exist.
- follow-up chosen: `B_component_taylor_remainder_source_after_same_coeff_shapesq_payload`
- follow-up failure closed: `STEP33_A1_SUB0_SHAPESQ_DERIV_TIGHT_SAME_COEFF_TAYLOR_PAYLOAD_GAP`
- follow-up first missing: `STEP33_A1_SUB0_COMPONENT_TAYLOR_REMAINDER_SOURCE_GAP`
- why not A: Earlier endpoint finite-cover machinery still lacked proof-grade Omega/OmegaPrime/E/EPrime remainder sources; it would create another empty checker first.
- why not C: A monolithic direct Lean proof would mix component expansions, product assembly, model subtraction, and range proof in one hard-to-audit theorem.
- follow-up why A: The same-coefficient ShapeSqDeriv Taylor payload is now Lean-checked and tied by theorem to the active generated coefficient stream.  It is still a coarse/nonfinal budget, so the smallest next proof-moving patch is the component Taylor remainder source that assembles this payload into the raw-derivative residual route.

## Failure Codes

- `STEP33_A1_SUB0_COMPONENT_TAYLOR_REMAINDER_SOURCE_GAP`
- `STEP33_A1_SUB0_SHAPESQ_DERIV_TIGHT_SAME_COEFF_TAYLOR_PAYLOAD_GAP`
- `STEP33_A1_SUB0_SHAPESQ_ENDPOINT_TO_TAYLOR_COEFF_REMAINDER_RECEIVER_GAP`
- `STEP33_A1_SUB0_SHAPESQ_INTEGRATED_POLY_DERIV_CROSSWALK_GAP`
- `STEP33_A1_SUB0_SHAPESQ_DERIV_TAYLOR_SOURCE_GAP`
- `STEP33_A1_SUB0_SHAPESQ_CONSTANT_DERIV_TAYLOR_BUDGET_GAP`
- `STEP33_A1_SUB0_SHAPESQ_DERIV_ORDER16_INTERVAL_CERT_RECEIVER_GAP`
- `STEP33_A1_SUB0_SHAPESQ_DERIV_CENTER_COEFF_BRIDGE_GAP`
- `STEP33_A1_SUB0_SHAPESQ_DERIV_COEFF_INTERVAL_RECEIVER_GAP`
- `STEP33_A1_SUB0_SHAPESQ_DERIV_POWER_SERIES_COEFF0_ROW_GAP`
- `STEP33_A1_SUB0_SHAPESQ_DERIV_POWER_SERIES_COEFF1_ROW_GAP`
- `STEP33_A1_SUB0_SHAPESQ_DERIV_ORDER_SHIFT_RECEIVER_GAP`
- `STEP33_A1_SUB0_SHAPESQ_DERIV_SHAPESQ_DERIVATIVE_RECEIVER_GAP`
- `STEP33_A1_SUB0_SHAPESQ_DERIV_PRODUCT_LEIBNIZ_BOUNDS_PAYLOAD_GAP`
- `STEP33_A1_SUB0_SHAPESQ_DERIV_MAJORANT_RECEIVER_GAP`
- `STEP33_A1_SUB0_SHAPE_POW12_MAJORANT_RECURRENCE_GAP`
- `STEP33_A1_SUB0_SCALED_REALSINC_NORMALIZATION_GAP`
- `STEP33_A1_SUB0_SHAPESQ_DERIV_EXPLICIT_CAUCHY_POWER_SERIES_GAP`
- `STEP33_A1_SUB0_SHAPESQ_DERIV_EXPLICIT_CAUCHY_ROWS_1_TO_15_ORDER16_GAP`
- `STEP33_A1_SUB0_SHAPESQ_DERIV_EXPLICIT_CAUCHY_ROWS_2_TO_15_ORDER16_GAP`
- `STEP33_A1_SUB0_SHAPESQ_DERIV_ITERATED_LEIBNIZ_CROSSWALK_GAP`
- `STEP33_A1_SUB0_SHAPESQ_DERIV_SHAPE_DERIVATIVE_BOUNDS_PAYLOAD_GAP`
- `STEP33_A1_SUB0_SHAPE_DERIVATIVE_BOUNDS_0_TO_17_PAYLOAD_GAP`
- `STEP33_A1_SUB0_SCALED_REALSINC_DERIVATIVE_BOUNDS_0_TO_17_GAP`
- `STEP33_A1_SUB0_REALSINC_DERIVATIVE_BOUNDS_0_TO_17_GAP`
- `STEP33_A1_SUB0_SHAPESQ_DERIV_ORDER16_ZERO_CELL_PROOF_GAP`
- `STEP33_A1_SUB0_SHAPEDERIV_ENDPOINT_TO_TAYLOR_COEFF_REMAINDER_RECEIVER_GAP`
- `STEP33_A1_SUB0_SHAPE_TAYLOR_REMAINDER_GAP`
- `STEP33_A1_SUB0_SHAPE_SHAPEDERIV_TAYLOR_REMAINDER_GAP`
- `STEP33_A1_SUB0_RAW_DERIV_EXACT_ASSEMBLY_GAP`
- `STEP33_A1_SUB0_RESIDUAL_POLYNOMIAL_RANGE_GAP`
- `STEP33_A1_SUB0_COMPONENT_TAYLOR_RESIDUAL_LEAN_PAYLOAD_MISSING`

## Decision

The Omega integrated-polynomial derivative crosswalk, center
anchor payload, shape-square integrated Taylor receiver,
coarse constant shape-square Taylor source, ShapeSqDeriv
interval-certificate receiver, the ShapeSqDeriv center-coeff
bridge, coefficient rows `j = 0,1`, the structural
ShapeSqDeriv order-shift receiver, the direct shape-square
derivative receiver, the isolated product-bound receiver,
the ShapeSqDeriv majorant receiver, the active shape pow-12
scaled-sinc majorant receiver, the affine scale-normalization
receiver, the coarse `coarseTwo` realSinc-to-ShapeSqDeriv
payload, and the same-coefficient ShapeSqDeriv Taylor payload
are Lean-checked.
The new payload consumes the active generated coefficient stream
rather than the dead zero-coefficient coarse stream.  It closes
the old first guard at rows `2..15` plus order `16` in proof-object
form, but its budget is still coarse/nonfinal.  The first live
proof gap is now the component Taylor remainder source that can
be assembled into the raw derivative residual route.
Raw-derivative assembly, residual polynomial bounds, and the
final interval theorem remain open.

## Local Lean Supplement 3 (2026-06-22)

A later local Lean supplement added:

- `Q3/Proofs/PSD_CenteredCoeffRawOmegaAComponentTaylorTightBudgetKill.lean`

Checked supplement theorem:

- `primaryFiniteRow0Parent0Split100Sub0_tightProductAssemblyErrorBudget_width_fail`

Meaning: Lean now proves the active target residual interval width is
strictly smaller than
`2 * primaryFiniteRow0Parent0Split100Sub0TightProductAssemblyErrorBudget`.
Therefore the current proof-grade coarse enclosure cannot close the final
target interval receiver.

Boundary: this is not Step33A.1-A closure and does not kill the route.  It
only marks the current coarse source as proof-grade-but-too-wide.
`residualTaylorRemainderAbs`, `componentTaylorProofsPresent`, and
`exactCoefficientAssemblyPassed` remain false/null in the generated payload.

Current local first gap after supplement 3:
`STEP33_A1_SUB0_SHAPESQ_DERIV_SHARP_REMAINDER_SOURCE_GAP`.

## Local Lean Supplement 4 (2026-06-22)

A later local Lean supplement added:

- `Q3/Proofs/PSD_CenteredCoeffRawOmegaAShapeSqDerivPartialSharpPayload.lean`

Checked supplement theorems:

- `primaryFiniteRow0Parent0Split100Sub0_shapeSqDeriv_partialSharpCoeff_eq_generated`
- `primaryFiniteRow0Parent0Split100Sub0_shapeSqDeriv_partialSharp_valid`
- `primaryFiniteRow0Parent0Split100Sub0_shapeSqDerivPartialSharpTaylorSource`
- `primaryFiniteRow0Parent0Split100Sub0_partialSharpShapeSqDerivRows2To15_width_fail`

Meaning: Lean now proves a partial-sharp ShapeSqDeriv Taylor source in the
same active coefficient stream and `ShapeSqDerivTaylorIntervalCert.singleAbs`
normalization.  The source spends the checked center rows `0` and `1`, leaves
rows `2..15` and order `16` on the coarse budget, and then proves this is
still too wide for the active target residual interval.

Boundary: this is not Step33A.1-A closure and does not kill the route.  Rows
`0` and `1` are no longer the live obstruction; rows `2..15` plus order `16`
remain open.  `residualTaylorRemainderAbs`, `componentTaylorProofsPresent`,
`exactCoefficientAssemblyPassed`, and `finalBudgetPassed` remain false/null in
the generated payload.

Current local first gap after supplement 4:
`STEP33_A1_SUB0_SHAPESQ_DERIV_ROWS_2_TO_15_ORDER16_SHARP_SOURCE_GAP`.

## Local Lean Supplement 5 (2026-06-22)

A later local Lean supplement added:

- `Q3/Proofs/PSD_CenteredCoeffRawOmegaAShapeSqDerivPartialSharpRows012Payload.lean`

Checked supplement theorems:

- `primaryFiniteRow0Parent0Split100Sub0_shapeSqDeriv_rows012Coeff_eq_generated`
- `primaryFiniteRow0Parent0Split100Sub0_shapeSqDeriv_centerJet2_coarseSmall_abs`
- `primaryFiniteRow0Parent0Split100Sub0_shapeSqDeriv_rows012_valid`
- `primaryFiniteRow0Parent0Split100Sub0_shapeSqDerivRows012TaylorSource`
- `primaryFiniteRow0Parent0Split100Sub0_rows012ShapeSqDerivRows3To15_width_fail`

Meaning: Lean now proves row `2` in the same active generated coefficient
stream and `ShapeSqDerivTaylorIntervalCert.singleAbs` normalization.  This uses
the existing coarse shape-derivative majorant at exact product order `n = 3`
and divides by `2!`, instead of spending the global order-17 budget.

Boundary: this is not Step33A.1-A closure and does not kill the route.  Rows
`0`, `1`, and `2` are no longer the live obstruction.  Rows `3..15` plus order
`16` remain open, and Lean proves the rows-0/1/2 partial-sharp source is still
too wide for the active target interval.  `residualTaylorRemainderAbs`,
`componentTaylorProofsPresent`, `exactCoefficientAssemblyPassed`, and
`finalBudgetPassed` remain false/null in the generated payload.

Current local first gap after supplement 5:
`STEP33_A1_SUB0_SHAPESQ_DERIV_ROWS_3_TO_15_ORDER16_SHARP_SOURCE_GAP`.

## Local Lean Supplement 6 (2026-06-22)

A later local Lean supplement added:

- `Q3/Proofs/PSD_CenteredCoeffRawOmegaAShapeSqDerivPartialSharpRows0123Payload.lean`

Checked supplement theorems:

- `primaryFiniteRow0Parent0Split100Sub0_shapeSqDeriv_rows0123Coeff_eq_generated`
- `primaryFiniteRow0Parent0Split100Sub0_shapeSqDeriv_centerJet3_coarseSmall_abs`
- `primaryFiniteRow0Parent0Split100Sub0_shapeSqDeriv_rows0123_valid`
- `primaryFiniteRow0Parent0Split100Sub0_shapeSqDerivRows0123TaylorSource`
- `primaryFiniteRow0Parent0Split100Sub0_rows0123ShapeSqDerivRows4To15_width_fail`

Meaning: Lean now proves row `3` in the same active generated coefficient
stream and `ShapeSqDerivTaylorIntervalCert.singleAbs` normalization.  This uses
the existing coarse shape-derivative majorant at exact product order `n = 4`
and divides by `3!`, instead of spending the global order-17 budget.

Boundary: this is not Step33A.1-A closure and does not kill the route.  Rows
`0`, `1`, `2`, and `3` are no longer the live obstruction.  Rows `4..15` plus
order `16` remain open, and Lean proves the rows-0/1/2/3 partial-sharp source
is still too wide for the active target interval.  `residualTaylorRemainderAbs`,
`componentTaylorProofsPresent`, `exactCoefficientAssemblyPassed`, and
`finalBudgetPassed` remain false/null in the generated payload.

Current local first gap after supplement 6:
`STEP33_A1_SUB0_SHAPESQ_DERIV_ROWS_4_TO_15_ORDER16_SHARP_SOURCE_GAP`.

## Local Lean Supplement 7 (2026-06-22)

A later local Lean supplement added:

- `Q3/Proofs/PSD_CenteredCoeffRawOmegaAShapeSqDerivPartialSharpRows01234Payload.lean`

Checked supplement theorems:

- `primaryFiniteRow0Parent0Split100Sub0_shapeSqDeriv_rows01234Coeff_eq_generated`
- `primaryFiniteRow0Parent0Split100Sub0_shapeSqDeriv_centerJet4_coarseSmall_abs`
- `primaryFiniteRow0Parent0Split100Sub0_shapeSqDeriv_rows01234_valid`
- `primaryFiniteRow0Parent0Split100Sub0_shapeSqDerivRows01234TaylorSource`
- `primaryFiniteRow0Parent0Split100Sub0_rows01234ShapeSqDerivRows5To15_width_fail`

Meaning: Lean now proves row `4` in the same active generated coefficient
stream and `ShapeSqDerivTaylorIntervalCert.singleAbs` normalization.  This uses
the existing coarse shape-derivative majorant at exact product order `n = 5`
and divides by `4!`, instead of spending the global order-17 budget.

Boundary: this is not Step33A.1-A closure and does not kill the route.  Rows
`0`, `1`, `2`, `3`, and `4` are no longer the live obstruction.  Rows `5..15`
plus order `16` remain open, and Lean proves the rows-0/1/2/3/4 partial-sharp
source is still too wide for the active target interval.
`residualTaylorRemainderAbs`, `componentTaylorProofsPresent`,
`exactCoefficientAssemblyPassed`, and `finalBudgetPassed` remain false/null in
the generated payload.

Current local first gap after supplement 7:
`STEP33_A1_SUB0_SHAPESQ_DERIV_ROWS_5_TO_15_ORDER16_SHARP_SOURCE_GAP`.

## Local Lean Supplement 8 (2026-06-22)

A later local Lean supplement added:

- `Q3/Proofs/PSD_CenteredCoeffRawOmegaAShapeSqDerivPartialSharpRows012345Payload.lean`

Checked supplement theorems:

- `primaryFiniteRow0Parent0Split100Sub0_shapeSqDeriv_rows012345Coeff_eq_generated`
- `primaryFiniteRow0Parent0Split100Sub0_shapeSqDeriv_centerJet5_coarseSmall_abs`
- `primaryFiniteRow0Parent0Split100Sub0_shapeSqDeriv_rows012345_valid`
- `primaryFiniteRow0Parent0Split100Sub0_shapeSqDerivRows012345TaylorSource`
- `primaryFiniteRow0Parent0Split100Sub0_rows012345ShapeSqDerivRows6To15_width_fail`

Meaning: Lean now proves row `5` in the same active generated coefficient
stream and `ShapeSqDerivTaylorIntervalCert.singleAbs` normalization.  This uses
the existing coarse shape-derivative majorant at exact product order `n = 6`
and divides by `5!`, instead of spending the global order-17 budget.

Boundary: this is not Step33A.1-A closure and does not kill the route.  Rows
`0`, `1`, `2`, `3`, `4`, and `5` are no longer the live obstruction.  Rows
`6..15` plus order `16` remain open, and Lean proves the rows-0/1/2/3/4/5
partial-sharp source is still too wide for the active target interval.
`residualTaylorRemainderAbs`, `componentTaylorProofsPresent`,
`exactCoefficientAssemblyPassed`, and `finalBudgetPassed` remain false/null in
the generated payload.

Current local first gap after supplement 8:
`STEP33_A1_SUB0_SHAPESQ_DERIV_ROWS_6_TO_15_ORDER16_SHARP_SOURCE_GAP`.

## Local Lean Supplement 9 (2026-06-22)

A later local Lean supplement added:

- `Q3/Proofs/PSD_CenteredCoeffRawOmegaAShapeSqDerivPartialSharpRows0123456Payload.lean`

Checked supplement theorems:

- `primaryFiniteRow0Parent0Split100Sub0_shapeSqDeriv_rows0123456Coeff_eq_generated`
- `primaryFiniteRow0Parent0Split100Sub0_shapeSqDeriv_centerJet6_coarseSmall_abs`
- `primaryFiniteRow0Parent0Split100Sub0_shapeSqDeriv_rows0123456_valid`
- `primaryFiniteRow0Parent0Split100Sub0_shapeSqDerivRows0123456TaylorSource`
- `primaryFiniteRow0Parent0Split100Sub0_rows0123456ShapeSqDerivRows7To15_width_fail`

Meaning: Lean now proves row `6` in the same active generated coefficient
stream and `ShapeSqDerivTaylorIntervalCert.singleAbs` normalization.  This uses
the existing coarse shape-derivative majorant at exact product order `n = 7`
and divides by `6!`, instead of spending the global order-17 budget.

Boundary: this is not Step33A.1-A closure and does not kill the route.  Rows
`0`, `1`, `2`, `3`, `4`, `5`, and `6` are no longer the live obstruction.
Rows `7..15` plus order `16` remain open, and Lean proves the
rows-0/1/2/3/4/5/6 partial-sharp source is still too wide for the active target
interval.  `residualTaylorRemainderAbs`, `componentTaylorProofsPresent`,
`exactCoefficientAssemblyPassed`, and `finalBudgetPassed` remain false/null in
the generated payload.

Current local first gap after supplement 9:
`STEP33_A1_SUB0_SHAPESQ_DERIV_ROWS_7_TO_15_ORDER16_SHARP_SOURCE_GAP`.

## Local Lean Supplement 10 (2026-06-22)

A later local Lean supplement added:

- `Q3/Proofs/PSD_CenteredCoeffRawOmegaAShapeSqDerivPartialSharpRows01234567Payload.lean`

Checked supplement theorems:

- `primaryFiniteRow0Parent0Split100Sub0_shapeSqDeriv_rows01234567Coeff_eq_generated`
- `primaryFiniteRow0Parent0Split100Sub0_shapeSqDeriv_centerJet7_coarseSmall_abs`
- `primaryFiniteRow0Parent0Split100Sub0_shapeSqDeriv_rows01234567_valid`
- `primaryFiniteRow0Parent0Split100Sub0_shapeSqDerivRows01234567TaylorSource`
- `primaryFiniteRow0Parent0Split100Sub0_rows01234567ShapeSqDerivRows8To15_width_fail`

Meaning: Lean now proves row `7` in the same active generated coefficient
stream and `ShapeSqDerivTaylorIntervalCert.singleAbs` normalization.  This uses
the existing coarse shape-derivative majorant at exact product order `n = 8`
and divides by `7!`, instead of spending the global order-17 budget.

Boundary: this is not Step33A.1-A closure and does not kill the route.  Rows
`0`, `1`, `2`, `3`, `4`, `5`, `6`, and `7` are no longer the live obstruction.
Rows `8..15` plus order `16` remain open, and Lean proves the
rows-0/1/2/3/4/5/6/7 partial-sharp source is still too wide for the active
target interval.  `residualTaylorRemainderAbs`, `componentTaylorProofsPresent`,
`exactCoefficientAssemblyPassed`, and `finalBudgetPassed` remain false/null in
the generated payload.

Current local first gap after supplement 10:
`STEP33_A1_SUB0_SHAPESQ_DERIV_ROWS_8_TO_15_ORDER16_SHARP_SOURCE_GAP`.

## Local Lean Supplement 11 (2026-06-22)

A later local Lean supplement added:

- `Q3/Proofs/PSD_CenteredCoeffRawOmegaAShapeSqDerivPartialSharpRows012345678Payload.lean`

Checked supplement theorems:

- `primaryFiniteRow0Parent0Split100Sub0_shapeSqDeriv_rows012345678Coeff_eq_generated`
- `primaryFiniteRow0Parent0Split100Sub0_shapeSqDeriv_centerJet8_coarseSmall_abs`
- `primaryFiniteRow0Parent0Split100Sub0_shapeSqDeriv_rows012345678_valid`
- `primaryFiniteRow0Parent0Split100Sub0_shapeSqDerivRows012345678TaylorSource`
- `primaryFiniteRow0Parent0Split100Sub0_rows012345678ShapeSqDerivRows9To15_width_fail`

Meaning: Lean now proves row `8` in the same active generated coefficient
stream and `ShapeSqDerivTaylorIntervalCert.singleAbs` normalization.  This uses
the existing coarse shape-derivative majorant at exact product order `n = 9`
and divides by `8!`, instead of spending the global order-17 budget.

Boundary: this is not Step33A.1-A closure and does not kill the route.  Rows
`0`, `1`, `2`, `3`, `4`, `5`, `6`, `7`, and `8` are no longer the live
obstruction.  Rows `9..15` plus order `16` remain open, and Lean proves the
rows-0/1/2/3/4/5/6/7/8 partial-sharp source is still too wide for the active
target interval.  `residualTaylorRemainderAbs`,
`componentTaylorProofsPresent`, `exactCoefficientAssemblyPassed`, and
`finalBudgetPassed` remain false/null in the generated payload.

Current local first gap after supplement 11:
`STEP33_A1_SUB0_SHAPESQ_DERIV_ROWS_9_TO_15_ORDER16_SHARP_SOURCE_GAP`.

## Local Lean Supplement 12 (2026-06-22)

A later local Lean supplement added:

- `Q3/Proofs/PSD_CenteredCoeffRawOmegaAShapeSqDerivPartialSharpRows0123456789Payload.lean`

Checked supplement theorems:

- `primaryFiniteRow0Parent0Split100Sub0_shapeSqDeriv_rows0123456789Coeff_eq_generated`
- `primaryFiniteRow0Parent0Split100Sub0_shapeSqDeriv_centerJet9_coarseSmall_abs`
- `primaryFiniteRow0Parent0Split100Sub0_shapeSqDeriv_rows0123456789_valid`
- `primaryFiniteRow0Parent0Split100Sub0_shapeSqDerivRows0123456789TaylorSource`
- `primaryFiniteRow0Parent0Split100Sub0_rows0123456789ShapeSqDerivRows10To15_width_fail`

Meaning: Lean now proves row `9` in the same active generated coefficient
stream and `ShapeSqDerivTaylorIntervalCert.singleAbs` normalization.  This uses
the existing coarse shape-derivative majorant at exact product order `n = 10`
and divides by `9!`, instead of spending the global order-17 budget.

Boundary: this is not Step33A.1-A closure and does not kill the route.  Rows
`0`, `1`, `2`, `3`, `4`, `5`, `6`, `7`, `8`, and `9` are no longer the live
obstruction.  Rows `10..15` plus order `16` remain open, and Lean proves the
rows-0/1/2/3/4/5/6/7/8/9 partial-sharp source is still too wide for the active
target interval.  `residualTaylorRemainderAbs`,
`componentTaylorProofsPresent`, `exactCoefficientAssemblyPassed`, and
`finalBudgetPassed` remain false/null in the generated payload.

Current local first gap after supplement 12:
`STEP33_A1_SUB0_SHAPESQ_DERIV_ROWS_10_TO_15_ORDER16_SHARP_SOURCE_GAP`.

## Local Lean Supplement 13 (2026-06-22)

A later local Lean supplement added:

- `Q3/Proofs/PSD_CenteredCoeffRawOmegaAShapeSqDerivPartialSharpRows012345678910Payload.lean`

Checked supplement theorems:

- `primaryFiniteRow0Parent0Split100Sub0_shapeSqDeriv_rows012345678910Coeff_eq_generated`
- `primaryFiniteRow0Parent0Split100Sub0_shapeSqDeriv_centerJet10_coarseSmall_abs`
- `primaryFiniteRow0Parent0Split100Sub0_shapeSqDeriv_rows012345678910_valid`
- `primaryFiniteRow0Parent0Split100Sub0_shapeSqDerivRows012345678910TaylorSource`
- `primaryFiniteRow0Parent0Split100Sub0_rows012345678910ShapeSqDerivRows11To15_width_fail`

Meaning: Lean now proves row `10` in the same active generated coefficient
stream and `ShapeSqDerivTaylorIntervalCert.singleAbs` normalization.  This uses
the existing coarse shape-derivative majorant at exact product order `n = 11`
and divides by `10!`, instead of spending the global order-17 budget.

Boundary: this is not Step33A.1-A closure and does not kill the route.  Rows
`0`, `1`, `2`, `3`, `4`, `5`, `6`, `7`, `8`, `9`, and `10` are no longer the
live obstruction.  Rows `11..15` plus order `16` remain open, and Lean proves
the rows-0/1/2/3/4/5/6/7/8/9/10 partial-sharp source is still too wide for the
active target interval.  `residualTaylorRemainderAbs`,
`componentTaylorProofsPresent`, `exactCoefficientAssemblyPassed`, and
`finalBudgetPassed` remain false/null in the generated payload.

Current local first gap after supplement 13:
`STEP33_A1_SUB0_SHAPESQ_DERIV_ROWS_11_TO_15_ORDER16_SHARP_SOURCE_GAP`.

## Local Lean Supplement 14 (2026-06-22)

A later local Lean supplement added:

- `Q3/Proofs/PSD_CenteredCoeffRawOmegaAShapeSqDerivPartialSharpRows01234567891011Payload.lean`

Checked supplement theorems:

- `primaryFiniteRow0Parent0Split100Sub0_shapeSqDeriv_rows01234567891011Coeff_eq_generated`
- `primaryFiniteRow0Parent0Split100Sub0_shapeSqDeriv_centerJet11_coarseSmall_abs`
- `primaryFiniteRow0Parent0Split100Sub0_shapeSqDeriv_rows01234567891011_valid`
- `primaryFiniteRow0Parent0Split100Sub0_shapeSqDerivRows01234567891011TaylorSource`
- `primaryFiniteRow0Parent0Split100Sub0_rows01234567891011ShapeSqDerivRows12To15_width_pass`

Meaning: Lean now proves row `11` in the same active generated coefficient
stream and `ShapeSqDerivTaylorIntervalCert.singleAbs` normalization.  This uses
the existing coarse shape-derivative majorant at exact product order `n = 12`
and divides by `11!`, instead of spending the global order-17 budget.

Boundary: this is not Step33A.1-A closure and does not prove
`finalBudgetPassed`.  Rows `0`, `1`, `2`, `3`, `4`, `5`, `6`, `7`, `8`, `9`,
`10`, and `11` are spendable in the local ShapeSqDeriv source, and the local
row-by-row width test now passes.  The existing product/P45 bridge still
consumes the old `primaryFiniteRow0Parent0Split100Sub0TightProductAssemblyErrorBudget`,
so the row11 Taylor source must still be bridged into the component Taylor
product receiver.  `residualTaylorRemainderAbs`,
`componentTaylorProofsPresent`, `exactCoefficientAssemblyPassed`, and
`finalBudgetPassed` remain false/null in the generated payload.

Current local first gap after supplement 14:
`STEP33_A1_SUB0_SHAPESQ_DERIV_ROWS01234567891011_TAYLOR_SOURCE_PRODUCT_BRIDGE_GAP`.

## Local Lean Supplement 15 (2026-06-22)

A later local Lean supplement added:

- `Q3/Proofs/PSD_CenteredCoeffRawOmegaAComponentTaylorRows01234567891011ProductBridge.lean`

Checked supplement theorems:

- `primaryFiniteRow0Parent0Split100Sub0_rows01234567891011_component_product_source`
- `primaryFiniteRow0Parent0Split100Sub0_rawDerivClosedForm_rows01234567891011ProductSource`
- `primaryFiniteRow0Parent0Split100Sub0_fullTaylor_residual_deriv_rows01234567891011_enclosure`

Meaning: the row11 partial-sharp ShapeSqDeriv Taylor source is now consumed by
the component Taylor product/P45 receiver.  The bridge reuses the existing
assembled coefficient stream because the row11 ShapeSqDeriv coefficient stream
is definitionally the generated stream.

Boundary: this is not Step33A.1-A closure and does not prove
`finalBudgetPassed`.  The remaining target is the final comparison for
`primaryFiniteRow0Parent0Split100Sub0Rows01234567891011ProductAssemblyErrorBudget`.
A direct `norm_num` comparison attempt left generated/integrated coefficient
abs-budget surfaces opaque, so no truth value is claimed yet for that final
comparison.

Current local first gap after supplement 15:
`STEP33_A1_SUB0_ROWS01234567891011_PRODUCT_BUDGET_FINAL_COMPARISON_GAP`.

First observed subfailure:
`STEP33_A1_SUB0_ROWS01234567891011_PRODUCT_BUDGET_COEFF_UNFOLD_GAP`.
