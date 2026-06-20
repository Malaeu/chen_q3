# Step33A.1-A Sub0 Residual-Derivative Interpolation Payload

Fail-closed skeleton.  This is not Lean proof data.

## Summary

- schema: `q3_psdpd_step33_a1_sub0_residual_deriv_interpolation_payload.v7`
- status: `blocked_missing_exact_interpolation_inputs`
- cert: `primaryFiniteRow0Parent0Split100Sub0RawCenterCoeffOnlyCert`
- receiver: `RawOmegaATaylorModelCertificate.ResidualDerivativeDirectNormCert.Valid.of_interpolation_error_bound`
- sub0 landing receiver: `RawOmegaATaylorModelCertificate.primaryFiniteRow0Parent0Split100Sub0_cellSlopeExactIntegralProofData_of_checked_hRawCenterCoeffAbs_and_deriv_interpolation_error_bound`
- sub0 polynomial-model landing receiver: `RawOmegaATaylorModelCertificate.primaryFiniteRow0Parent0Split100Sub0_cellSlopeExactIntegralProofData_of_checked_hRawCenterCoeffAbs_and_deriv_polynomial_model_error_bound`
- cell: `Set.Icc (0 : Real) ((1 : Real) / 10)`
- derivSlope: `1866608532757/500000000000000000000000000000`
- candidate source status: `derivmodel_candidate_budget_fail_triangle_receiver_dead`
- proof-safe closed fields: `0`
- Lean emitted: `False`

## Exact Budget

- relation: `interpolationError + modelBound <= derivSlope`
- lhs: `None`
- rhs: `1866608532757/500000000000000000000000000000`
- margin: `None`
- passes: `None`

## Missing Inputs

- `STEP33_A1_SUB0_DERIVMODEL_BUDGET_FAIL`

## Candidate Source Inventory

- status: `derivmodel_candidate_budget_fail_triangle_receiver_dead`
- proof-grade derivative model source: `False`
- derivative-model candidate file present: `True`
- derivfit raw candidate file present: `True`
- decision: `The existing derivfit file is a raw-polynomial refresh.  The separate derivmodel candidate records exact derivative coefficients, but its modelBound exceeds the entire direct residual-derivative slope budget, so the triangle receiver route is killed before any crosswalk theorem would be spendable.`

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

### Residualfit Candidate

- path: `/Users/emalam/Documents/GitHub/rh_lean_01_2026/q3.lean.aristotle/ACTIVE/requests/step33_bootstrap/a_chunk_taylor_payload_refined_subchunk_candidate_overlay_primary_finite_0_0_denom1e30_residualfit.json`
- exists: `True`
- status: `candidate_overlay_remainder_refreshed_not_proof_data`
- candidates: `100`
- proof use: `not_allowed_as_modelDeriv_source_without_crosswalk`

### Derivfit Candidate

- path: `/Users/emalam/Documents/GitHub/rh_lean_01_2026/q3.lean.aristotle/ACTIVE/requests/step33_bootstrap/a_chunk_taylor_payload_refined_subchunk_candidate_overlay_primary_finite_0_0_denom1e30_derivfit.json`
- exists: `True`
- expected kind: `raw_integrand_candidate_with_derivative_remainder_refresh_not_derivative_model`
- status: `candidate_overlay_derivative_remainder_refreshed_not_proof_data`
- candidates: `100`
- proof use: `not_allowed_as_modelDeriv_source_when_coefficients_match_raw_polynomial`

### Derivfit Raw-Coefficient Equality

- all files exist: `True`
- raw equals residualfit: `True`
- raw equals derivfit: `True`
- residualfit equals derivfit: `True`
- verdict: `derivfit_coefficients_are_raw_polynomial_coefficients`

### Derivmodel Candidate

- path: `/Users/emalam/Documents/GitHub/rh_lean_01_2026/q3.lean.aristotle/ACTIVE/requests/step33_bootstrap/step33_a1_sub0_derivmodel_candidate.json`
- exists: `True`
- status: `derivmodel_candidate_budget_fail_not_spendable`
- model degree: `15`
- model coeff count: `16`
- modelBound: `60128873212381686241540561835466089/327680000000000000000000000000000000`
- first danger point: `STEP33_A1_SUB0_DERIVMODEL_BUDGET_FAIL`
- proof use: `dead_for_current_triangle_receiver_because_modelBound_exceeds_derivSlope`
- direct triangle budget: `DERIVMODEL_BUDGET_FAIL_modelBound_exceeds_derivSlope`
- budget passes: `False`
- budget margin: `-60128873212381685018239993807838569/327680000000000000000000000000000000`
- Lean kill theorem: `primaryFiniteRow0Parent0Split100Sub0ResidualDerivmodel_budget_impossible`

### Derivfit Direct Derivative Overlay

- path: `/Users/emalam/Documents/GitHub/rh_lean_01_2026/q3.lean.aristotle/ACTIVE/requests/step33_bootstrap/a_chunk_taylor_payload_refined_subchunk_direct_derivative_overlay_primary_finite_0_0_denom1e30_derivfit.json`
- exists: `True`
- status: `direct_derivative_overlay_seeded_missing_cell_slope_norm_proofs`
- source audit status: `sampled_interval_finite_cover_candidate_passed_rejected_envelopes_overestimated`
- proof use: `not_allowed_as_modelDeriv_source_without_hResidualDerivBoundOnCell`

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
- derivfit coefficients match raw-polynomial coefficients unless the equality check says otherwise
- derivmodel candidates are not proof-grade without uniform remainder and Lean arithmetic emission
- the active derivmodel triangle route is killed if modelBound exceeds derivSlope
- modelBound must be derived by exact rational interval operations
- interpolationError must bound ||deriv residual - modelDeriv|| uniformly on [0, 1/10]
- a positive exact budget margin is required before Lean emission is enabled
