# Step33A.1-A Sub0 Residual-Derivative Interpolation Payload

Fail-closed skeleton.  This is not Lean proof data.

## Summary

- schema: `q3_psdpd_step33_a1_sub0_residual_deriv_interpolation_payload.v4`
- status: `blocked_missing_exact_interpolation_inputs`
- cert: `primaryFiniteRow0Parent0Split100Sub0RawCenterCoeffOnlyCert`
- receiver: `RawOmegaATaylorModelCertificate.ResidualDerivativeDirectNormCert.Valid.of_interpolation_error_bound`
- sub0 landing receiver: `RawOmegaATaylorModelCertificate.primaryFiniteRow0Parent0Split100Sub0_cellSlopeExactIntegralProofData_of_checked_hRawCenterCoeffAbs_and_deriv_interpolation_error_bound`
- sub0 polynomial-model landing receiver: `RawOmegaATaylorModelCertificate.primaryFiniteRow0Parent0Split100Sub0_cellSlopeExactIntegralProofData_of_checked_hRawCenterCoeffAbs_and_deriv_polynomial_model_error_bound`
- cell: `Set.Icc (0 : Real) ((1 : Real) / 10)`
- derivSlope: `1866608532757/500000000000000000000000000000`
- candidate source status: `blocked_no_proof_grade_derivative_model_source_for_sub0`
- proof-safe closed fields: `0`
- Lean emitted: `False`

## Exact Budget

- relation: `interpolationError + modelBound <= derivSlope`
- lhs: `None`
- rhs: `1866608532757/500000000000000000000000000000`
- margin: `None`
- passes: `None`

## Missing Inputs

- `STEP33_A1_SUB0_DERIVATIVE_MODEL_SOURCE_GAP`
- `STEP33_A1_SUB0_POLYNOMIAL_MODEL_EXACT_ARITHMETIC_GAP`
- `STEP33_A1_SUB0_INTERPOLATION_ERROR_EXACT_REMAINDER_GAP`

## Candidate Source Inventory

- status: `blocked_no_proof_grade_derivative_model_source_for_sub0`
- proof-grade derivative model source: `False`
- derivative-model candidate file present: `False`
- decision: `Do not use raw Taylor coefficients or sampled derivative intervals as modelDeriv.  Generate a derivative-residual polynomial source or prove the interpolation error directly.`

### Raw Polynomial Candidate

- path: `/Users/emalam/Documents/GitHub/rh_lean_01_2026/q3.lean.aristotle/ACTIVE/requests/step33_bootstrap/a_chunk_taylor_payload_refined_subchunk_candidate_overlay_primary_finite_0_0_denom1e30.json`
- exists: `True`
- status: `candidate_overlay_not_proof_data`
- function kind: `raw_integrand_taylor_polynomial_candidate_not_derivative_model`
- proof use: `not_allowed_as_modelDeriv_source_for_deriv_residual`

### Direct Derivative Overlay

- path: `/Users/emalam/Documents/GitHub/rh_lean_01_2026/q3.lean.aristotle/ACTIVE/requests/step33_bootstrap/a_chunk_taylor_payload_refined_subchunk_direct_derivative_overlay_primary_finite_0_0_denom1e30.json`
- exists: `True`
- status: `direct_derivative_overlay_seeded_missing_cell_slope_norm_proofs`
- source audit status: `sampled_interval_finite_cover_candidate_passed_rejected_envelopes_overestimated`
- function kind: `sampled_residual_derivative_interval_candidate_not_polynomial_model`
- proof use: `not_allowed_as_modelDeriv_source_without_universal_Lean_proof`

### Expected Derivative Model Candidate

- path: `/Users/emalam/Documents/GitHub/rh_lean_01_2026/q3.lean.aristotle/ACTIVE/requests/step33_bootstrap/a_chunk_taylor_payload_refined_subchunk_candidate_overlay_primary_finite_0_0_denom1e30_derivfit.json`
- exists: `False`
- expected kind: `derivative_residual_polynomial_model_candidate`

## Receiver Shape

`modelDeriv : Real -> Real, hModel : forall eta in cell, ||modelDeriv eta|| <= modelBound, hError : forall eta in cell, ||deriv cert.residual eta - modelDeriv eta|| <= interpolationError, hBudget : interpolationError + modelBound <= data.derivSlope`

## Sub0 Landing Shape

`modelDeriv : Real -> Real, hModel : forall eta in Set.Icc 0 (1/10), ||modelDeriv eta|| <= modelBound, hError : forall eta in Set.Icc 0 (1/10), ||deriv cert.residual eta - modelDeriv eta|| <= interpolationError, hBudget : interpolationError + modelBound <= 1866608532757/500000000000000000000000000000`

## Polynomial Model Landing Shape

`modelDegree : Nat, modelCenter : Rat, modelCoeff : Fin (modelDegree + 1) -> Rat, hModelRadius : forall eta in Set.Icc 0 (1/10), |eta - modelCenter| <= modelRadius, hModelSum : sum_i |modelCoeff_i| * modelRadius^i <= modelBound, hError : forall eta in Set.Icc 0 (1/10), ||deriv cert.residual eta - rawOmegaATaylorPolynomial modelDegree modelCenter modelCoeff eta|| <= interpolationError, hBudget : interpolationError + modelBound <= 1866608532757/500000000000000000000000000000`

`For polynomial modelDeriv = rawOmegaATaylorPolynomial, the semantic hModel input is reduced to exact rational radius containment plus sum_abs_coeff arithmetic.`

## Guard

- not Lean proof data
- does not import or trust sampled derivative JSON
- does not emit a Lean payload theorem
- sub0 landing receiver is checked separately in Lean
- polynomial-model landing receiver is checked separately in Lean
- raw Taylor polynomial candidates are not derivative-model sources
- sampled derivative intervals are not modelDeriv proof data
- modelBound must be derived by exact rational interval operations
- interpolationError must bound ||deriv residual - modelDeriv|| uniformly on [0, 1/10]
- a positive exact budget margin is required before Lean emission is enabled
