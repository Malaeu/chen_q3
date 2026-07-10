PROSHKA_ROUTE_REVIEW

Gate:
NConvergenceTriage / Route B TwoLevelSpectralLadder

Verdict:
NCONV_TRIAGE_ANCHOR_CONFIRMED_RHO_P1_MISMATCH

Route status:
NOT_KILLED. Diagnostic only. No RH claim. Phase 2 not run.

Files written:
- ACTIVE/requests/routeB_twolevel_spectral_ladder/report.md
- ACTIVE/requests/routeB_twolevel_spectral_ladder/out/nconv_triage.json
- ACTIVE/requests/routeB_twolevel_spectral_ladder/out/nconv_anchor_lambda_sq_13_N_120.json
- ACTIVE/requests/routeB_twolevel_spectral_ladder/out/nconv_anchor_block_cache_lambda_sq_13_N_120.json
- ACTIVE/requests/routeB_twolevel_spectral_ladder/out/nconv_anchor_progress.log
- ACTIVE/requests/routeB_twolevel_spectral_ladder/loop_state.json
- ACTIVE/requests/routeB_twolevel_spectral_ladder/handoff_to_proshka.md

What happened:
- T1 did NOT fire N_NOT_CONVERGING: no mu_i has rho <= 1.2.
- But the registered p~1 model failed: mu-rho min is about 4.363 and max is about 69.415, outside [1.5,2.5].
- T3 is FIT_NOT_LAW for mu1, mu2, and Delta; eta1 has insufficient extrapolated points.
- The single allowed anchor (lambda_sq=13,N=120) succeeded.
- Static S0 reproduces saved/fresh mu1,mu2,mu3 with max relative error about 3.823e-8.
- Direct LU vs deflated spectral K_schur agreement is about 8.079e-54.
- LU residual is about 5.289e-63; spectral residual is about 9.725e-71.
- Fresh xi_i, m_i/y_i cache, mass bands, top coefficients, and static dressed-vector probes are persisted.
- First five low C modes contribute only about 4.078e-25 of total K_schur norm, supporting broad-tail self-energy rather than low-tail domination.

Key answer:
Preflight was right to refuse certification from unseen vectors, but the new anchor now supplies the missing vector/block evidence for (13,120). The scalar p~1 N-model is rejected; the hidden static-Schur effective packet mechanism is strengthened.

Question for Proshka:
What is the next exact gate?

Options:
1. StaticSchurEffectivePacketAudit_v2_from_cached_column_solver:
   rerun/finish the static-Schur audit using the request-local block cache and column-wise C solver, starting with the previously blocked N=120 cells.
2. OperatorStaticSchurStabilityGate:
   stop chasing scalar p~1 N-convergence and test stability of the effective Schur operator/S0 mechanism directly.
3. AdditionalSingleAnchor:
   buy exactly one more anchor, likely (lambda_sq=12,N=120), to complete the missing hard case before returning to grid-wide claims.
4. Stop here with this diagnostic and request a theorem/interface reformulation.

Codex recommendation:
Choose option 1 if the goal is to discharge the previous STATIC_SCHUR_AUDIT_BLOCKED object with the fixed solver. Choose option 2 if the scalar rho mismatch means the correct next mathematical object is operator-level stability rather than more raw finite-N scalar ratios.

ROUTE_STATUS = NOT_KILLED

## PROSHKA_RESPONSE

Status:
CHOOSE OPTION 2

Next gate:
OperatorStaticSchurStabilityGate

Proshka interpretation:
- Scalar p~1 N-model is rejected.
- Static Schur mechanism is strengthened.
- The next question is operator-level stability of `S0 = G - B^* C^(-1) B` after aligning the 3D packet coordinates.
- Do not keep repairing raw `mu_i(N)` scalar fits.
- Do not run BoundaryOperatorConstructionAudit, ProlateBranchBasisConstructionAudit, full Phase 2, slope refit, or raw scalar N-convergence repair now.

Allowed internal purchase:
- Buy exactly one `(lambda_sq,N)=(12,120)` anchor inside the operator stability gate if it is the only missing hard anchor required for the comparison.

Recommended next status:
- FAILURE_CODE = N_LIMIT_NOT_STABLE
- PRIMARY_DIAGNOSIS = STATIC_SCHUR_MECHANISM_STRENGTHENED
- SECONDARY_DIAGNOSIS = SCALAR_P1_N_MODEL_REJECTED
- TERTIARY_DIAGNOSIS = BROAD_TAIL_SELF_ENERGY_CONFIRMED
- NEXT_GATE = OperatorStaticSchurStabilityGate
- ROUTE_STATUS = NOT_KILLED

## USER_APPEND_TO_NEXT_GOAL

Append file:
- `operator_static_schur_stability_goal_append.md`

Mandatory additions for `OperatorStaticSchurStabilityGate`:
- O2+ `PARITY-ZERO STRUCTURAL JUDGE`: run first at every anchor. Since `T` preserves parity and `k1,k2_even` are even while `k2_odd` is odd, the odd/even cross entries of `G`, `K_schur`, and `S0` must vanish. Report `abs(S0_{k1,odd})/||S0||` and `abs(S0_{even2,odd})/||S0||`; registered threshold `<= 1e-25`. Violation is `PARITY_CONTAMINATION` and stops drift interpretation.
- O2 block exploit: treat `S0` as `(2x2 even) direct_sum (1x1 odd)`, report odd scalar `S0_oo`, `eig(even 2x2)`, and `Delta_eff = S0_oo - eig1(even 2x2)` separately. Expected: second level is odd, matching saved `parity(xi2) = -1`.
- O2 alignment note: `V_n` is nested in `N`; zero-pad `N_low` packet vectors before 3x3 Procrustes.
- O3+ dimensionless invariants: report `theta2/theta1` and `theta3/theta1` across `N`; registered Case-B signature is ratio drift `90->120` at least `10x` smaller than raw theta drift.
- O2++ geometric N-model: for aligned `S0` entries and `eig(S0)`, compute `rho = drift(60->90)/drift(90->120)`. Registered `rho >= 3`; if true, report geometric extrapolation `X_inf = X_120 + drift(90->120)/(rho-1)` and residual, labeled `FIT_NOT_LAW`.
- O1+ fresh `(12,120)` acceptance: parity-zero judge must pass and deflated-vs-direct agreement must be at least 25 digits, as at `(13,120)`.
