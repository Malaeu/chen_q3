# Step33A.1-A Sub0 Anchor-Abs Second-Deriv Payload Audit

Fail-closed skeleton.  This is not Lean proof data.

## Summary

- schema: `q3_psdpd_step33_a1_sub0_anchor_abs_second_deriv_payload.v1`
- status: `anchor_abs_second_deriv_budget_fail_from_current_derivative_audit_not_spendable`
- receiver: `RawOmegaATaylorModelCertificate.primaryFiniteRow0Parent0Split100Sub0_cellSlopeExactIntegralProofData_of_checked_hRawCenterCoeffAbs_and_anchor_abs_second_deriv_envelope`
- cell: `Set.Icc (0 : Real) ((1 : Real) / 10)`
- mesh: `1/10`
- first blocker: `STEP33_A1_SUB0_ANCHOR_ABS_SECOND_DERIV_BUDGET_FAIL`
- Lean kill theorem: `primaryFiniteRow0Parent0Split100Sub0_anchorAbsSecondDeriv_budget_impossible`
- proof-safe closed fields: `0`
- Lean emitted: `False`

## Worklist Derivative Interval

- sampled lower: `-94119513411/500000000000000000000000000000`
- sampled lower decimal: `-0.000000000000000000188239`
- sampled upper: `1866608532757/500000000000000000000000000000`
- sampled upper decimal: `0.000000000000000003733217`

## Exact Source Budgets

| source | status | secondDerivSlope | upperRequired | sampledUpper | upperPasses | lowerRequired | sampledLower | lowerPasses | firstFailure |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| `denom1e30` | `sampled_interval_finite_cover_candidate_passed_rejected_envelopes_overestimated` | `685968816833992725150437603/1000000000000000000000000000000` | `685968816833997265132258153/10000000000000000000000000000000` | `1866608532757/500000000000000000000000000000` | `False` | `-685968816833997265132258153/10000000000000000000000000000000` | `-94119513411/500000000000000000000000000000` | `False` | `STEP33_A1_SUB0_ANCHOR_ABS_SECOND_DERIV_BUDGET_FAIL` |
| `denom1e30_residualfit` | `sampled_interval_finite_cover_candidate_passed_rejected_envelopes_overestimated` | `685968816833992725150437603/1000000000000000000000000000000` | `685968816833997265132258153/10000000000000000000000000000000` | `1866608532757/500000000000000000000000000000` | `False` | `-685968816833997265132258153/10000000000000000000000000000000` | `-94119513411/500000000000000000000000000000` | `False` | `STEP33_A1_SUB0_ANCHOR_ABS_SECOND_DERIV_BUDGET_FAIL` |
| `denom1e30_derivfit` | `sampled_interval_finite_cover_candidate_passed_rejected_envelopes_overestimated` | `685968816833992725150437603/1000000000000000000000000000000` | `685968816833997265132258153/10000000000000000000000000000000` | `1866608532757/500000000000000000000000000000` | `False` | `-685968816833997265132258153/10000000000000000000000000000000` | `-94119513411/500000000000000000000000000000` | `False` | `STEP33_A1_SUB0_ANCHOR_ABS_SECOND_DERIV_BUDGET_FAIL` |

## Source Notes

### denom1e30

- path: `/Users/emalam/Documents/GitHub/rh_lean_01_2026/q3.lean.aristotle/ACTIVE/requests/step33_bootstrap/a_chunk_taylor_payload_refined_subchunk_derivative_bound_audit_primary_finite_0_0_denom1e30.json`
- exists: `True`
- schema: `q3_psdpd_step33_a_refined_subchunk_derivative_bound_audit.v7`
- status: `sampled_interval_finite_cover_candidate_passed_rejected_envelopes_overestimated`
- proof use: `diagnostic_only_not_allowed_as_Lean_payload`
- usable as anchor-abs/second-deriv payload: `False`
- sampled envelope passes: `True`
- second-derivative envelope passes: `False`
- interval envelope passes: `False`
- jet envelope passes: `False`
- legacy diagnostic derivSlope: `13719376336679845423045110947/1000000000000000000000000000000`
- sampled lower matches worklist: `True`
- sampled upper matches worklist: `True`

### denom1e30_residualfit

- path: `/Users/emalam/Documents/GitHub/rh_lean_01_2026/q3.lean.aristotle/ACTIVE/requests/step33_bootstrap/a_chunk_taylor_payload_refined_subchunk_derivative_bound_audit_primary_finite_0_0_denom1e30_residualfit.json`
- exists: `True`
- schema: `q3_psdpd_step33_a_refined_subchunk_derivative_bound_audit.v7`
- status: `sampled_interval_finite_cover_candidate_passed_rejected_envelopes_overestimated`
- proof use: `diagnostic_only_not_allowed_as_Lean_payload`
- usable as anchor-abs/second-deriv payload: `False`
- sampled envelope passes: `True`
- second-derivative envelope passes: `False`
- interval envelope passes: `False`
- jet envelope passes: `False`
- legacy diagnostic derivSlope: `13719376336679845423045110947/1000000000000000000000000000000`
- sampled lower matches worklist: `True`
- sampled upper matches worklist: `True`

### denom1e30_derivfit

- path: `/Users/emalam/Documents/GitHub/rh_lean_01_2026/q3.lean.aristotle/ACTIVE/requests/step33_bootstrap/a_chunk_taylor_payload_refined_subchunk_derivative_bound_audit_primary_finite_0_0_denom1e30_derivfit.json`
- exists: `True`
- schema: `q3_psdpd_step33_a_refined_subchunk_derivative_bound_audit.v7`
- status: `sampled_interval_finite_cover_candidate_passed_rejected_envelopes_overestimated`
- proof use: `diagnostic_only_not_allowed_as_Lean_payload`
- usable as anchor-abs/second-deriv payload: `False`
- sampled envelope passes: `True`
- second-derivative envelope passes: `False`
- interval envelope passes: `False`
- jet envelope passes: `False`
- legacy diagnostic derivSlope: `13719376336679845423045110947/1000000000000000000000000000000`
- sampled lower matches worklist: `True`
- sampled upper matches worklist: `True`

## Guard

- not Lean proof data
- does not emit a Lean payload theorem
- uses derivative_bound_audit.v7 only as diagnostic source inventory
- does not claim |deriv residual 0| bound is proved
- does not claim second-derivative envelope is proved
- does not kill the checked anchor-envelope receiver
- does not kill direct residual or future cancellation-aware routes

## Lean Kill Theorem

`primaryFiniteRow0Parent0Split100Sub0_anchorAbsSecondDeriv_budget_impossible`

The symmetric anchor-abs budget is impossible for the current derivSampleRadius even with secondDerivSlope = 0.  This is a kill theorem for the current symmetric source shape, not a payload theorem and not a route kill for asymmetric anchors.

## Decision

The current derivative_bound_audit.v7 source is not spendable for the v21 anchor-abs/second-deriv payload.  Its second-derivative slope makes both rational budget comparisons fail by many orders of magnitude.

## Next Recommended Patch

Build a sharper proof-grade same-cell second-derivative envelope, or replace this source with a cancellation-aware direct residual payload; do not spend the current v7 diagnostic audit.
