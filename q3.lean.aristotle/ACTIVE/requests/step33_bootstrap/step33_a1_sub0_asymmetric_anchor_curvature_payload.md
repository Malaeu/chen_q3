# Step33A.1-A Sub0 Asymmetric Anchor-Curvature Audit

Fail-closed skeleton.  This is not Lean proof data.

## Summary

- schema: `q3_psdpd_step33_a1_sub0_asymmetric_anchor_curvature_payload.v1`
- status: `asymmetric_anchor_curvature_current_v7_source_budget_fail_not_route_dead`
- target gap: `STEP33_A1_SUB0_ASYMMETRIC_ANCHOR_CURVATURE_PAYLOAD_GAP`
- first blocker: `STEP33_A1_SUB0_ASYMMETRIC_ANCHOR_CURVATURE_SOURCE_BUDGET_FAIL`
- route-death condition: `STEP33_A1_SUB0_ASYMMETRIC_ANCHOR_CURVATURE_CONSTANT_FAIL`
- route death reached: `False`
- receiver: `RawOmegaATaylorModelCertificate.primaryFiniteRow0Parent0Split100Sub0_cellSlopeExactIntegralProofData_of_checked_hRawCenterCoeffAbs_and_anchor_envelope`
- interval receiver: `RawOmegaATaylorModelCertificate.primaryFiniteRow0Parent0Split100Sub0_residual_deriv_interval_bounds_of_anchor_envelope`
- cell: `Set.Icc (0 : Real) ((1 : Real) / 10)`
- mesh: `1/10`
- proof-safe closed fields: `0`
- Lean emitted: `False`

not reached: current candidate zero-curvature asymmetric slack is positive in the denom1e30 source, and these v7 fields are diagnostic rather than proof-grade constants

## Required Inputs

- derivAnchorLower <= deriv cert.residual 0
- deriv cert.residual 0 <= derivAnchorUpper
- 0 <= derivSlope
- DifferentiableAt Real (fun t => deriv cert.residual t) on [0, 1/10]
- proof-grade curvature envelope ||deriv (deriv cert.residual) eta|| <= derivSlope on [0, 1/10]
- lower budget: sampled lower <= derivAnchorLower - derivSlope * (1/10)
- upper budget: derivAnchorUpper + derivSlope * (1/10) <= sampled upper

## Exact Source Budgets

| source | status | curvature | max allowed curvature | ratio | lower slack at 0 | upper slack at 0 | lowerPasses | upperPasses | route-death by candidate constants | firstFailure |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| `denom1e30` | `sampled_interval_finite_cover_candidate_passed_rejected_envelopes_overestimated` | `685968816833992725150437603/1000000000000000000000000000000` | `279846042433/50000000000000000000000000000` | `122561822005795.484250631050445504443322` | `279846042433/500000000000000000000000000000` | `3279218883459/1000000000000000000000000000000` | `False` | `False` | `False` | `STEP33_A1_SUB0_ASYMMETRIC_ANCHOR_CURVATURE_SOURCE_BUDGET_FAIL` |
| `denom1e30_residualfit` | `sampled_interval_finite_cover_candidate_passed_rejected_envelopes_overestimated` | `685968816833992725150437603/1000000000000000000000000000000` | `279846042433/50000000000000000000000000000` | `122561822005795.484250631050445504443322` | `279846042433/500000000000000000000000000000` | `3279218883459/1000000000000000000000000000000` | `False` | `False` | `False` | `STEP33_A1_SUB0_ASYMMETRIC_ANCHOR_CURVATURE_SOURCE_BUDGET_FAIL` |
| `denom1e30_derivfit` | `sampled_interval_finite_cover_candidate_passed_rejected_envelopes_overestimated` | `685968816833992725150437603/1000000000000000000000000000000` | `279846042433/50000000000000000000000000000` | `122561822005795.484250631050445504443322` | `279846042433/500000000000000000000000000000` | `3279218883459/1000000000000000000000000000000` | `False` | `False` | `False` | `STEP33_A1_SUB0_ASYMMETRIC_ANCHOR_CURVATURE_SOURCE_BUDGET_FAIL` |

## Source Notes

### denom1e30

- path: `/Users/emalam/Documents/GitHub/rh_lean_01_2026/q3.lean.aristotle/ACTIVE/requests/step33_bootstrap/a_chunk_taylor_payload_refined_subchunk_derivative_bound_audit_primary_finite_0_0_denom1e30.json`
- exists: `True`
- schema: `q3_psdpd_step33_a_refined_subchunk_derivative_bound_audit.v7`
- status: `sampled_interval_finite_cover_candidate_passed_rejected_envelopes_overestimated`
- proof use: `diagnostic_only_not_allowed_as_Lean_payload`
- rational anchor fields: `candidate_interval_fields_not_proof_evidence`
- decimal anchor residual diagnostics: `diagnostic_decimal_only_not_Lean_payload`
- anchorDerivativeResidualLower: `4.127256200498391208E-19`
- anchorDerivativeResidualUpper: `4.127256200498391208E-19`
- sampled envelope passes: `True`
- second-derivative envelope passes: `False`
- interval envelope passes: `False`
- jet envelope passes: `False`
- legacy diagnostic derivSlope: `13719376336679845423045110947/1000000000000000000000000000000`

### denom1e30_residualfit

- path: `/Users/emalam/Documents/GitHub/rh_lean_01_2026/q3.lean.aristotle/ACTIVE/requests/step33_bootstrap/a_chunk_taylor_payload_refined_subchunk_derivative_bound_audit_primary_finite_0_0_denom1e30_residualfit.json`
- exists: `True`
- schema: `q3_psdpd_step33_a_refined_subchunk_derivative_bound_audit.v7`
- status: `sampled_interval_finite_cover_candidate_passed_rejected_envelopes_overestimated`
- proof use: `diagnostic_only_not_allowed_as_Lean_payload`
- rational anchor fields: `candidate_interval_fields_not_proof_evidence`
- decimal anchor residual diagnostics: `diagnostic_decimal_only_not_Lean_payload`
- anchorDerivativeResidualLower: `4.127256200498391208E-19`
- anchorDerivativeResidualUpper: `4.127256200498391208E-19`
- sampled envelope passes: `True`
- second-derivative envelope passes: `False`
- interval envelope passes: `False`
- jet envelope passes: `False`
- legacy diagnostic derivSlope: `13719376336679845423045110947/1000000000000000000000000000000`

### denom1e30_derivfit

- path: `/Users/emalam/Documents/GitHub/rh_lean_01_2026/q3.lean.aristotle/ACTIVE/requests/step33_bootstrap/a_chunk_taylor_payload_refined_subchunk_derivative_bound_audit_primary_finite_0_0_denom1e30_derivfit.json`
- exists: `True`
- schema: `q3_psdpd_step33_a_refined_subchunk_derivative_bound_audit.v7`
- status: `sampled_interval_finite_cover_candidate_passed_rejected_envelopes_overestimated`
- proof use: `diagnostic_only_not_allowed_as_Lean_payload`
- rational anchor fields: `candidate_interval_fields_not_proof_evidence`
- decimal anchor residual diagnostics: `diagnostic_decimal_only_not_Lean_payload`
- anchorDerivativeResidualLower: `4.127256200498391208E-19`
- anchorDerivativeResidualUpper: `4.127256200498391208E-19`
- sampled envelope passes: `True`
- second-derivative envelope passes: `False`
- interval envelope passes: `False`
- jet envelope passes: `False`
- legacy diagnostic derivSlope: `13719376336679845423045110947/1000000000000000000000000000000`

## Guard

- not Lean proof data
- does not emit a Lean payload theorem
- uses derivative_bound_audit.v7 only as diagnostic source inventory
- rational derivAnchorLower/derivAnchorUpper fields are candidate intervals, not proof evidence
- decimal-only anchorDerivativeResidual fields are diagnostics only
- current secondDerivativeSlope field is too large for the asymmetric budget
- does not kill the checked asymmetric anchor-envelope receiver
- does not declare route death; route death requires proof-grade constants

## Decision

The current v7 diagnostic source is not spendable for the live asymmetric anchor/curvature payload.  The exact zero-curvature slack is positive for the main source, so the route remains open; the next proof object must provide proof-grade asymmetric anchor bounds and a much sharper direct residual curvature bound.

## Next Recommended Patch

Build a proof-grade generator for asymmetric anchor interval at 0 and direct residual curvature on [0,1/10], targeting STEP33_A1_SUB0_ASYMMETRIC_ANCHOR_CURVATURE_PAYLOAD_GAP.
