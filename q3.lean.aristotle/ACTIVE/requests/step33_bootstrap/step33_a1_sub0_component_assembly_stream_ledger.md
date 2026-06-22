# Step33A.1-A Sub0 Component Assembly Stream Ledger

Schema: `q3_psdpd_step33_a1_sub0_component_assembly_stream_ledger.v1`

Status: `fail_closed_nominal_object_coeffs_present_scale_source_bridge_gap`

First failure: `STEP33_A1_SUB0_RAW_DERIV_EXACT_ASSEMBLY_SCALE_SOURCE_BRIDGE_GAP`

Local assembly gap: `STEP33_A1_SUB0_RAW_DERIV_EXACT_ASSEMBLY_SCALE_SOURCE_BRIDGE_GAP`

Route-level gap: `STEP33_A1_SUB0_SHAPESQ_DERIV_TIGHT_SAME_COEFF_TAYLOR_PAYLOAD_GAP`

Zero-extension bridge gap: `None`

Boundary: A Lean-checked parameterized active-model crosswalk exists, including the same-degree subtraction bridge and degree-45/degree-15 zero-extension bridge.  The generic Cauchy product coefficient bridge is checked if recorded in the guard below. Named nominal coefficient objects are checked if recorded in the guard below.  They do not prove the active raw closed form until the scale/source bridge is checked in the same normalization. Step33A.1-A is not closed.

## Browser/Proshka Decision

- chosen: `A_component_assembly_coefficient_stream_ledger_first`
- first patch/theorem: `primaryFiniteRow0Parent0Split100Sub0_componentTaylor_residualCoeff_crosswalk`
- failure code if fails: `STEP33_A1_SUB0_COMPONENT_TAYLOR_ACTIVE_MODEL_COEFF_MISMATCH`
- why smallest: Rows 2..15 can prove bounds for the correct function but still feed the wrong polynomial payload unless the component coefficient stream is first fixed in the active RawTaylorCoeffCert residual convention.

Do not:
- do not unfold all Fin 46 coefficients with norm_num/ring_nf
- do not generate ShapeSqDeriv rows 2..15 before the crosswalk
- do not declare arbitrary ShapeSqDerivTightCoeff objects
- do not move to the direct residual interval theorem
- do not add a new receiver
- do not set componentTaylorProofsPresent=true without Lean check

## Browser/Proshka Follow-up Decision

- chosen: `A_cauchy_product_crosswalk_first`
- first patch/theorem: `rawOmegaATaylorPolynomial_mul_coeff`
- coefficient definition: `rawOmegaTaylorCauchyCoeff`
- failure code if fails: `STEP33_A1_SUB0_COMPONENT_TAYLOR_CAUCHY_PRODUCT_CROSSWALK_GAP`
- mismatch code after product bridge: `STEP33_A1_SUB0_COMPONENT_TAYLOR_ACTIVE_MODEL_COEFF_MISMATCH`
- why smallest: Fix the exact degree/factorial/center/Cauchy normalization before generating more rows; otherwise bounds can target the right function but the wrong polynomial payload.

Do not:
- do not set exactCoefficientAssemblyPassed=true
- do not treat rational scaleCenter as exact ((3/10)/Real.pi)
- do not treat NominalScaleCoeff as the active closed-form scale
- do not hardcode assembledDegree=45 as the real product degree; 15-by-16 products give degree 31 before zero-padding
- do not generate tight rows before exact coefficient-ledger comparison
- do not unfold 46-term sums with ring_nf/norm_num

## Target Theorem Contract

- name: `primaryFiniteRow0Parent0Split100Sub0_componentTaylor_residualCoeff_crosswalk`
- file: `Q3/Proofs/PSD_CenteredCoeffRawOmegaAComponentTaylorCoeffAssembly.lean`
- status: `OBJECT_THEOREM_LEAN_CHECKED_NOMINAL_NOT_PROOF_GRADE`

```text
rawOmegaATaylorPolynomial AssembledRawDerivDegree (1/20) AssembledRawDerivCoeff eta - rawOmegaATaylorPolynomial 15 (1/20) ResidualDerivmodelCoeff eta = rawOmegaATaylorPolynomial AssembledRawDerivDegree (1/20) ResidualTaylorCoeff eta
```

Partial Lean-checked same-degree theorem:

- name: `primaryFiniteRow0Parent0Split100Sub0_componentTaylor_residualCoeff_sameDegree_crosswalk_of_assembled`
- failure code if not enough: `STEP33_A1_SUB0_P45_PADDED_EQ_ACTIVE_P15_POLYNOMIAL_CROSSWALK_GAP`
- zero-extension theorem: `primaryFiniteRow0Parent0Split100Sub0_padded_residualDerivmodel_poly_eq`
- parameterized full theorem: `primaryFiniteRow0Parent0Split100Sub0_componentTaylor_residualCoeff_crosswalk_of_assembled`

```text
rawOmegaATaylorPolynomial AssembledRawDerivDegree (1/20) assembled eta - rawOmegaATaylorPolynomial AssembledRawDerivDegree (1/20) ResidualDerivmodelCoeffPadded eta = rawOmegaATaylorPolynomial AssembledRawDerivDegree (1/20) (ResidualTaylorCoeffOf assembled) eta
```

Required coefficient definitions:
- `primaryFiniteRow0Parent0Split100Sub0AssembledRawDerivDegree`
- `primaryFiniteRow0Parent0Split100Sub0AssembledRawDerivCoeff`
- `primaryFiniteRow0Parent0Split100Sub0ResidualTaylorCoeff`

## Assembly Formula

- scale: `((3 : Real) / 10) / Real.pi`
- raw closed form: `scale * (omegaPrime * shapeSq + omega * shapeSqDeriv)`
- assembled raw derivative coeff: `scale * (cauchy(omegaPrimeCoeff, shapeSqCoeff) + cauchy(omegaCoeff, shapeSqDerivCoeff))`
- residual Taylor coeff: `assembledRawDerivCoeff - zeroExtend15(ResidualDerivmodelCoeff)`
- center: `1/20`
- component degree: `15`
- assembled degree: `45`
- warning: Do not identify a ShapeSqDeriv coefficient stream with the active residual coefficient stream. It feeds through the product assembly with omega and omegaPrime first.

## Source Files

### landing

- path: `Q3/Proofs/PSD_CenteredCoeffRawOmegaAHRawLanding.lean`
- exists: `True`
- `primaryFiniteRow0Parent0Split100Sub0RawIntegrandDerivClosedForm`: found=`True`, line=`1820`
- `primaryFiniteRow0Parent0Split100Sub0RawTaylorCoeffCert`: found=`True`, line=`190`
- `primaryFiniteRow0Parent0Split100Sub0ResidualDerivmodelCoeff`: found=`True`, line=`46`
- `primaryFiniteRow0Parent0Split100Sub0_fullTaylor_polynomial_deriv_eq_derivmodel`: found=`True`, line=`201`
- `primaryFiniteRow0Parent0Split100Sub0_fullTaylor_residual_deriv_eq_closedForm`: found=`True`, line=`1912`
- `primaryFiniteRow0Parent0Split100Sub0_componentTaylor_residualCoeff_crosswalk`: found=`False`, line=`None`
- `primaryFiniteRow0Parent0Split100Sub0AssembledRawDerivCoeff`: found=`False`, line=`None`
- `primaryFiniteRow0Parent0Split100Sub0ResidualTaylorCoeff`: found=`False`, line=`None`

### componentAssembly

- path: `Q3/Proofs/PSD_CenteredCoeffRawOmegaAComponentTaylorCoeffAssembly.lean`
- exists: `True`
- `primaryFiniteRow0Parent0Split100Sub0AssembledRawDerivDegree`: found=`True`, line=`24`
- `primaryFiniteRow0Parent0Split100Sub0ResidualDerivmodelCoeffPadded`: found=`True`, line=`27`
- `primaryFiniteRow0Parent0Split100Sub0_padded_residualDerivmodel_poly_eq`: found=`True`, line=`310`
- `primaryFiniteRow0Parent0Split100Sub0ResidualTaylorCoeffOf`: found=`True`, line=`37`
- `rawOmegaATaylorPolynomial_sub_coeff`: found=`True`, line=`46`
- `rawOmegaTaylorCauchyCoeff`: found=`True`, line=`66`
- `rawOmegaATaylorPolynomial_mul_coeff`: found=`True`, line=`75`
- `primaryFiniteRow0Parent0Split100Sub0_omegaPrime_shapeSq_product_crosswalk`: found=`True`, line=`284`
- `primaryFiniteRow0Parent0Split100Sub0_omega_shapeSqDeriv_product_crosswalk`: found=`True`, line=`297`
- `primaryFiniteRow0Parent0Split100Sub0_componentTaylor_residualCoeff_sameDegree_crosswalk_of_assembled`: found=`True`, line=`382`
- `primaryFiniteRow0Parent0Split100Sub0_componentTaylor_residualCoeff_crosswalk_of_assembled`: found=`True`, line=`411`
- `primaryFiniteRow0Parent0Split100Sub0_componentTaylor_residualCoeff_crosswalk`: found=`True`, line=`431`
- `primaryFiniteRow0Parent0Split100Sub0AssembledRawDerivCoeff`: found=`True`, line=`269`
- `primaryFiniteRow0Parent0Split100Sub0ResidualTaylorCoeff`: found=`True`, line=`278`
- `primaryFiniteRow0Parent0Split100Sub0NominalScaleCoeff`: found=`True`, line=`247`
- `primaryFiniteRow0Parent0Split100Sub0NominalOmegaTaylorAnchorCoeff`: found=`True`, line=`229`

### chunkTaylorChecker

- path: `Q3/Proofs/PSD_CenteredCoeffRawOmegaAChunkTaylorChecker.lean`
- exists: `True`
- `rawOmegaATaylorPolynomial`: found=`True`, line=`31`
- `integratedTaylorCoeff`: found=`True`, line=`50`
- `shapeSqTaylor_bound_of_shapeSqDerivTaylor_bound`: found=`True`, line=`194`
- `ShapeSqDerivTaylorIntervalCert`: found=`True`, line=`10504`

### componentPayload

- path: `ACTIVE/requests/step33_bootstrap/step33_a1_sub0_component_taylor_residual_payload.json`
- exists: `True`
- schema: `q3_psdpd_step33_a1_sub0_component_taylor_residual_payload.v18`
- status: `fail_closed_coarse_shapesq_payload_not_same_coefficient_tight_source`
- firstFailure: `STEP33_A1_SUB0_SHAPESQ_DERIV_EXPLICIT_CAUCHY_ROWS_2_TO_15_ORDER16_GAP`

### tightPayload

- path: `ACTIVE/requests/step33_bootstrap/step33_a1_sub0_shapesq_deriv_tight_payload.json`
- exists: `True`
- schema: `q3_psdpd_step33_a1_sub0_shapesq_deriv_tight_payload.v1`
- status: `fail_closed_tight_coeff_stream_not_identified`
- firstFailure: `STEP33_A1_SUB0_SHAPESQ_DERIV_TIGHT_COEFF_STREAM_GAP`

## Current Component Field State

- `payloadExists`: `True`
- `payloadSchema`: `q3_psdpd_step33_a1_sub0_component_taylor_residual_payload.v18`
- `payloadStatus`: `fail_closed_coarse_shapesq_payload_not_same_coefficient_tight_source`
- `payloadFirstFailure`: `STEP33_A1_SUB0_SHAPESQ_DERIV_EXPLICIT_CAUCHY_ROWS_2_TO_15_ORDER16_GAP`
- `componentTaylorAssemblyLeanWritten`: `False`
- `componentTaylorOverallProofSafe`: `False`
- `exactCoefficientAssemblyPassed`: `False`
- `componentTaylorProofsPresent`: `False`
- `omegaDerivTaylorProofPresent`: `True`
- `omegaTaylorIntegratedPolyDerivCrosswalkProofPresent`: `True`
- `omegaTaylorCenterAnchorPayloadPresent`: `True`
- `shapeSqDerivCenterCoeffRowsClosedCount`: `2`
- `shapeSqDerivCenterCoeffRowsRequiredCount`: `16`
- `shapeSqDerivOrder16UniformBoundPresent`: `False`
- `assembledRawDerivCoeffPresent`: `False`
- `residualTaylorCoeffPresent`: `False`
- `residualTaylorRemainderAbsPresent`: `False`
- `assembledRawDerivCoeffLeanPresent`: `True`
- `residualTaylorCoeffLeanPresent`: `True`
- `nominalScaleCoeffLeanPresent`: `True`
- `nominalOmegaAnchorCoeffLeanPresent`: `True`
- `targetObjectCrosswalkLeanPresent`: `True`
- `nominalObjectBridgePresent`: `True`

## Guard

- `checkedFullCrosswalkTheoremPresent`: `True`
- `checkedSameDegreeCrosswalkTheoremPresent`: `True`
- `checkedParameterizedActiveModelCrosswalkTheoremPresent`: `True`
- `paddedDegree45EqualsActiveDegree15BridgePresent`: `True`
- `checkedCauchyProductBridgePresent`: `True`
- `checkedNominalObjectBridgePresent`: `True`
- `paddedDegree45EqualsActiveDegree15BridgeGap`: `None`
- `assembledRawDerivCoeffGeneratorFieldPresent`: `False`
- `residualTaylorCoeffGeneratorFieldPresent`: `False`
- `assembledRawDerivCoeffLeanPresent`: `True`
- `residualTaylorCoeffLeanPresent`: `True`
- `exactCoefficientAssemblyPassed`: `False`
- `guardPasses`: `False`

## Decision

- can generate rows 2..15 now: `False`
- can use parameterized Lean crosswalk now: `True`
- can emit object-level crosswalk now: `True`
- next failure if Cauchy bridge missing: `None`
- next patch: Prove the same-normalization scale/source bridge: replace the nominal scale and nominal omega anchor by proof-grade interval or exact sources that connect the component product stream to the active raw closed-form derivative coefficient budget.

Downstream after this closes:
- generate proof-grade ShapeSqDeriv rows 2..15 and order16
- prove primaryFiniteRow0Parent0Split100Sub0_shapeSqDeriv_tight_valid
- assemble raw derivative residual interval payload
- prove the final direct residual interval theorem
