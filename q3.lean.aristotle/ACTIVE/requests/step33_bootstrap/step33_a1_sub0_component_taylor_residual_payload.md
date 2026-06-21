# Step33A.1-A Sub0 Component Taylor Residual Payload

Fail-closed route-B payload. This is not Lean proof data and does
not close Step33A.1-A.

## Status

- schema: `q3_psdpd_step33_a1_sub0_component_taylor_residual_payload.v10`
- route: `STEP33_A1_SUB0_COMPONENT_TAYLOR_RESIDUAL`
- chosen route: `B`
- status: `fail_closed_missing_shapesq_deriv_explicit_cauchy_power_series_order16_cert`
- first failure: `STEP33_A1_SUB0_SHAPESQ_DERIV_EXPLICIT_CAUCHY_POWER_SERIES_GAP`
- closed historical failures: `STEP33_A1_SUB0_OMEGA_OMEGAPRIME_TAYLOR_REMAINDER_GAP, STEP33_A1_SUB0_OMEGAPRIME_CENTER_JET_PAYLOAD_GAP, STEP33_A1_SUB0_OMEGAPRIME_ORDER16_INTEGER_BUDGET_PAYLOAD_GAP, STEP33_A1_SUB0_OMEGAPRIME_REMAINDER_BUDGET_PAYLOAD_GAP, STEP33_A1_SUB0_OMEGA_TAYLOR_INTEGRATED_POLY_DERIV_CROSSWALK_GAP, STEP33_A1_SUB0_OMEGA_TAYLOR_CENTER_ANCHOR_PAYLOAD_GAP, STEP33_A1_SUB0_SHAPESQ_INTEGRATED_POLY_DERIV_CROSSWALK_GAP, STEP33_A1_SUB0_SHAPESQ_DERIV_TAYLOR_SOURCE_GAP, STEP33_A1_SUB0_SHAPESQ_DERIV_ORDER16_INTERVAL_CERT_RECEIVER_GAP, STEP33_A1_SUB0_SHAPESQ_DERIV_CENTER_COEFF_BRIDGE_GAP, STEP33_A1_SUB0_SHAPESQ_DERIV_COEFF_INTERVAL_RECEIVER_GAP`
- advisory source: `browser_proshka_route_advice_not_proof_evidence`
- proof-safe closed fields: `9`
- Lean emitted: `False`

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
- shape: `center_coeff_bridge_formal_missing_explicit_cauchy_rows_order16_bound`
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
- shapeTaylor: `SHAPESQ_DERIV_CENTER_COEFF_BRIDGE_FORMAL_MISSING_EXPLICIT_ROWS`
- shapeDerivTaylor: `ENDPOINT_DERIV_BOUNDS_FORMAL_MISSING_TAYLOR_COEFF_REMAINDER_RECEIVER`
- shape endpoint bounds available: `True`
- shapeSq integrated receiver available: `True`
- shapeSq deriv Taylor source available: `True`
- shapeSq deriv interval cert receiver available: `True`
- shapeSq deriv center-coeff bridge available: `True`
- shapeSq deriv center-coeff interval receiver available: `True`
- shapeSq value Taylor source available: `True`
- shape Taylor receiver gap: `STEP33_A1_SUB0_SHAPESQ_DERIV_EXPLICIT_CAUCHY_POWER_SERIES_GAP`
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
- shapeSqTaylorSourcePresent: `True`
- shapeTaylorReceiverPresent: `True`
- shapeDerivTaylorReceiverPresent: `False`
- omegaDerivTaylorProofAssembledIntoRawDerivative: `False`
- residualPolynomialRangePassed: `False`
- finalBudgetPassed: `False`
- proofSafeClosedFields: `9`
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
- shapeSqDerivCenterCoeffValid: `primaryFiniteRow0Parent0Split100Sub0_shapeSqDeriv_valid_of_powerSeriesCoeff_abs`
- shapeSqDerivCenterCoeffIntervalValid: `primaryFiniteRow0Parent0Split100Sub0_shapeSqDeriv_valid_of_powerSeriesCoeff_interval`
- shapeSqTaylorSource: `primaryFiniteRow0Parent0Split100Sub0ShapeSqTaylorSource_generated`
- shapeSqTaylorCoeff: `primaryFiniteRow0Parent0Split100Sub0ShapeSqTaylorCoeff_generated`
- shapeValueBounds: `primaryFiniteRow0Parent0Split100Sub0ShapeValueBounds_of_deriv_bounds_and_anchor_generated`
- shapeDerivAnchorBounds: `primaryFiniteRow0Parent0Split100Sub0ShapeDerivAnchorBounds_generated`
- shapeDerivIntervalBounds: `primaryFiniteRow0Parent0Split100Sub0ShapeDerivClosedForm_interval_bounds_of_anchor_second_deriv_bound_generated`

## Proshka Decision

- chosen: `B_component_taylor_route`
- follow-up chosen: `A_shapesq_deriv_power_series_coeff_interval_receiver`
- follow-up failure closed: `STEP33_A1_SUB0_SHAPESQ_DERIV_COEFF_INTERVAL_RECEIVER_GAP`
- follow-up first missing: `STEP33_A1_SUB0_SHAPESQ_DERIV_EXPLICIT_CAUCHY_POWER_SERIES_GAP`
- why not A: Earlier endpoint finite-cover machinery still lacked proof-grade Omega/OmegaPrime/E/EPrime remainder sources; it would create another empty checker first.
- why not C: A monolithic direct Lean proof would mix component expansions, product assembly, model subtraction, and range proof in one hard-to-audit theorem.
- follow-up why A: After the center-coefficient bridge became Lean-checked and the worklist was synchronized, the smallest proof-moving patch is the interval coefficient receiver: future generated lower/upper coefficient rows can feed the existing compact absolute-error certificate without a new analytic layer.

## Failure Codes

- `STEP33_A1_SUB0_SHAPESQ_DERIV_EXPLICIT_CAUCHY_POWER_SERIES_GAP`
- `STEP33_A1_SUB0_SHAPESQ_ENDPOINT_TO_TAYLOR_COEFF_REMAINDER_RECEIVER_GAP`
- `STEP33_A1_SUB0_SHAPESQ_INTEGRATED_POLY_DERIV_CROSSWALK_GAP`
- `STEP33_A1_SUB0_SHAPESQ_DERIV_TAYLOR_SOURCE_GAP`
- `STEP33_A1_SUB0_SHAPESQ_CONSTANT_DERIV_TAYLOR_BUDGET_GAP`
- `STEP33_A1_SUB0_SHAPESQ_DERIV_ORDER16_INTERVAL_CERT_RECEIVER_GAP`
- `STEP33_A1_SUB0_SHAPESQ_DERIV_CENTER_COEFF_BRIDGE_GAP`
- `STEP33_A1_SUB0_SHAPESQ_DERIV_COEFF_INTERVAL_RECEIVER_GAP`
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
interval-certificate receiver, and the ShapeSqDeriv
center-coefficient bridge are now Lean-checked.
The compact center bridge connects center jets to power-series
coefficients and the absolute-error/interval certificate wrappers,
but it adds no exact rational rows.  The first live gate is now
the explicit Cauchy/power-series coefficient source and order-16
uniform bound needed by `ShapeSqDerivTaylorIntervalCert.Valid`.
Raw-derivative assembly, residual polynomial bounds, and the
final interval theorem remain open.
