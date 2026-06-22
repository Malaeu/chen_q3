# Step33A.1-A Sub0 Component Assembly Stream Ledger

Schema: `q3_psdpd_step33_a1_sub0_component_assembly_stream_ledger.v1`

Status: `fail_closed_raw_product_coeff_source_gap_after_same_degree_bridge`

First failure: `STEP33_A1_SUB0_RAW_DERIV_EXACT_ASSEMBLY_GAP`

Local assembly gap: `STEP33_A1_SUB0_RAW_DERIV_EXACT_ASSEMBLY_GAP`

Route-level gap: `STEP33_A1_SUB0_SHAPESQ_DERIV_TIGHT_SAME_COEFF_TAYLOR_PAYLOAD_GAP`

Zero-extension bridge gap: `STEP33_A1_SUB0_P45_PADDED_EQ_ACTIVE_P15_POLYNOMIAL_CROSSWALK_GAP`

Boundary: A Lean-checked same-degree coefficient-subtraction bridge exists, but the full degree-15 active-model crosswalk and proof-grade raw product coefficient source are still open. Step33A.1-A is not closed.

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

## Target Theorem Contract

- name: `primaryFiniteRow0Parent0Split100Sub0_componentTaylor_residualCoeff_crosswalk`
- file: `Q3/Proofs/PSD_CenteredCoeffRawOmegaAComponentTaylorCoeffAssembly.lean`
- status: `FULL_NOT_WRITTEN_PARTIAL_SAME_DEGREE_LEAN_CHECKED`

```text
rawOmegaATaylorPolynomial AssembledRawDerivDegree (1/20) AssembledRawDerivCoeff eta - rawOmegaATaylorPolynomial 15 (1/20) ResidualDerivmodelCoeff eta = rawOmegaATaylorPolynomial AssembledRawDerivDegree (1/20) ResidualTaylorCoeff eta
```

Partial Lean-checked same-degree theorem:

- name: `primaryFiniteRow0Parent0Split100Sub0_componentTaylor_residualCoeff_sameDegree_crosswalk_of_assembled`
- failure code if not enough: `STEP33_A1_SUB0_P45_PADDED_EQ_ACTIVE_P15_POLYNOMIAL_CROSSWALK_GAP`

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
- `primaryFiniteRow0Parent0Split100Sub0ResidualTaylorCoeffOf`: found=`True`, line=`37`
- `rawOmegaATaylorPolynomial_sub_coeff`: found=`True`, line=`46`
- `primaryFiniteRow0Parent0Split100Sub0_componentTaylor_residualCoeff_sameDegree_crosswalk_of_assembled`: found=`True`, line=`70`
- `primaryFiniteRow0Parent0Split100Sub0_componentTaylor_residualCoeff_crosswalk`: found=`False`, line=`None`
- `primaryFiniteRow0Parent0Split100Sub0AssembledRawDerivCoeff`: found=`False`, line=`None`
- `primaryFiniteRow0Parent0Split100Sub0ResidualTaylorCoeff`: found=`False`, line=`None`

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

## Guard

- `checkedFullCrosswalkTheoremPresent`: `False`
- `checkedSameDegreeCrosswalkTheoremPresent`: `True`
- `paddedDegree45EqualsActiveDegree15BridgePresent`: `False`
- `paddedDegree45EqualsActiveDegree15BridgeGap`: `STEP33_A1_SUB0_P45_PADDED_EQ_ACTIVE_P15_POLYNOMIAL_CROSSWALK_GAP`
- `assembledRawDerivCoeffPresent`: `False`
- `residualTaylorCoeffPresent`: `False`
- `exactCoefficientAssemblyPassed`: `False`
- `guardPasses`: `False`

## Decision

- can generate rows 2..15 now: `False`
- can emit Lean crosswalk now: `True`
- next patch: Build proof-grade exact rational assembledRawDerivCoeff and ResidualTaylorCoeff objects, then prove the zero-extension bridge from the active degree-15 residual model to the degree-45 padded model. Only after that promote the full componentTaylor_residualCoeff_crosswalk.

Downstream after this closes:
- generate proof-grade ShapeSqDeriv rows 2..15 and order16
- prove primaryFiniteRow0Parent0Split100Sub0_shapeSqDeriv_tight_valid
- assemble raw derivative residual interval payload
- prove the final direct residual interval theorem
