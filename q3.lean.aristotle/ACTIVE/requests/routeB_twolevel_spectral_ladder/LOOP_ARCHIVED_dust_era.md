# Superseded by ROUTE_B_STATE.md 2026-07-07; archived dust-era LOOP.md.

# Route B TwoLevelSpectralLadder Persistent Loop

## Purpose

This loop is a diagnostic/falsification loop for Route B / Connes-prolate branch.

It is NOT a proof of RH.
It is NOT the PSD-pd/Q3 mainline.
It attacks only the Route B spectral gap / packet ladder diagnostics unless Proshka explicitly changes the gate.

## Global state

Current route:
  Route B / Connes-prolate / TwoLevelSpectralLadder

Current known status:
  FAILURE_CODE = N_LIMIT_NOT_STABLE
  PRIMARY_DIAGNOSIS = FULL_LOW_SPECTRUM_BELOW_PACKET
  SECONDARY_DIAGNOSIS = NU_FLOOR_FIXED_TAIL_FAIL
  TERTIARY_DIAGNOSIS = MISSING_PROLATE_COMPARISON_BASIS
  ROUTE_STATUS = NOT KILLED

Current next gate:
  FullLowEigenvectorBlockLedgerAudit

Do not proceed to G3 residual estimates until FullLowEigenvectorBlockLedgerAudit is reviewed by Proshka.

## Loop protocol

For every gate:

1. Execute only the current gate.
2. Do not broaden the task.
3. Do not prove RH.
4. Do not change definitions unless the gate explicitly says so.
5. Save a report file.
6. Save compact evidence JSON if needed.
7. Write handoff_to_proshka.md in the exact format below.
8. If browser bridge is available, send handoff_to_proshka.md to Proshka/ChatGPT.
9. If browser bridge is unavailable, stop and wait for user to paste handoff_to_proshka.md manually.
10. Do not continue to next gate until Proshka verdict is received.

## Handoff format

Every handoff_to_proshka.md must be short and must contain:

PROSHKA_ROUTE_REVIEW

Gate:
Verdict:
Files written:
Top numbers:
What was NOT changed:
Interpretation:
Question for Proshka:
Suggested next gates:
Failure/status codes:

Do not include full logs unless asked.

## Current gate: FullLowEigenvectorBlockLedgerAudit

Context:
RogueTailLevelPlacementAudit found:
  nu_tail = 3.296e-53
  lambda1_G ~ 3.93e-28
  lambda2_G ~ 7.51e-28
  lambda3_G ~ 1.16e-27
  actual mu1 ~ 1.46e-64
  actual mu2 ~ 1.67e-60
  actual mu3 ~ 9.38e-57

Therefore actual full low spectrum lies far below both packet M levels and repaired complement tail nu.

Task:
Audit actual full-matrix eigenvectors xi1, xi2, xi3 for lambda_sq=14, N=120.

For each xi_i, i=1,2,3:
1. eigenvalue mu_i;
2. residual ||T xi_i - mu_i xi_i||;
3. norm and precision stability if available;
4. parity score under n -> -n;
5. projection onto packet M:
   ||P_M xi_i||, ||P_Mperp xi_i||,
   overlaps with k1, k2_odd, k2_even;
6. projection onto rogue tail vector |<xi_i, w_tail>|;
7. block energy ledger:
   m = P_M xi_i
   y = P_Mperp xi_i
   E_M = <m,Tm>
   E_tail = <y,Ty>
   E_cross = 2 Re <m,Ty>
   total = E_M + E_tail + E_cross
   Verify total equals mu_i.
8. Schur/Feshbach signal:
   report whether low value comes mainly from negative cross term.
9. localization:
   top coefficient indices n by |xi_i,n|;
   mass in low/mid/high Fourier index bands.
10. admissibility:
   if boundary map Q exists, compute ||Q xi_i|| and compare to ||Q k1||.
   if Q does not exist, report BOUNDARY_OPERATOR_MISSING.
11. missing branch comparison:
   if additional prolate branch vectors are available, compare xi_i to:
   h26, h048, h8, h410, h610, h812, next zero-integral combos.
   If unavailable, report MISSING_PROLATE_COMPARISON_BASIS.

Output:
  ACTIVE/requests/routeB_twolevel_spectral_ladder/full_low_eigenvector_audit.md
  ACTIVE/requests/routeB_twolevel_spectral_ladder/out/full_low_eig_*.json

Headline lines required in report:
1. Are actual xi1,xi2,xi3 admissible/boundary-null? YES/NO/UNKNOWN
2. Are actual xi1,xi2,xi3 explained by known/missing prolate branches? YES/NO/UNKNOWN
3. Is the low spectrum caused by M-Mperp hybridization/cross cancellation? YES/NO/UNKNOWN
4. Verdict code.

Allowed verdict codes:
- FULL_LOW_EIGENVECTORS_NUMERICAL_ARTIFACT
- FULL_LOW_EIGENVECTORS_BOUNDARY_LEAK
- FULL_LOW_EIGENVECTORS_PACKET_HYBRIDIZATION
- FULL_LOW_EIGENVECTORS_MISSING_PROLATE_BRANCH
- FULL_LOW_EIGENVECTORS_VALID_BELOW_PACKET
- BOUNDARY_OPERATOR_MISSING
- MISSING_PROLATE_COMPARISON_BASIS
- FULL_LOW_EIGENVECTOR_AUDIT_BLOCKED

## Next-gate decision table

After FullLowEigenvectorBlockLedgerAudit:

If verdict = FULL_LOW_EIGENVECTORS_NUMERICAL_ARTIFACT:
  next gate candidate = NumericalStabilityRepair
  stop and ask Proshka.

If verdict = FULL_LOW_EIGENVECTORS_BOUNDARY_LEAK:
  next gate candidate = BoundaryAdmissibilityProjection
  stop and ask Proshka.

If verdict = FULL_LOW_EIGENVECTORS_PACKET_HYBRIDIZATION:
  next gate candidate = FeshbachSchurComplementModel
  stop and ask Proshka.

If verdict = FULL_LOW_EIGENVECTORS_MISSING_PROLATE_BRANCH:
  next gate candidate = ExpandProlatePacketByIdentifiedBranch
  stop and ask Proshka.

If verdict = FULL_LOW_EIGENVECTORS_VALID_BELOW_PACKET:
  next gate candidate = RouteB_LadderModelReview
  stop and ask Proshka.

If verdict = BOUNDARY_OPERATOR_MISSING:
  next gate candidate = BoundaryOperatorConstructionAudit
  stop and ask Proshka.

If verdict = MISSING_PROLATE_COMPARISON_BASIS:
  next gate candidate = ProlateBranchBasisConstructionAudit
  stop and ask Proshka.

If verdict = FULL_LOW_EIGENVECTOR_AUDIT_BLOCKED:
  stop and ask Proshka with exact blocker.

## Hard forbidden

- No RH claims.
- No zero-side matching as proof.
- No Phase 2.
- No full ladder rerun.
- No changes to QW formulas.
- No changes to packet definitions unless Proshka explicitly says so.
- No edits outside ACTIVE/requests/routeB_twolevel_spectral_ladder.
- No continuing after handoff_to_proshka.md is written.
