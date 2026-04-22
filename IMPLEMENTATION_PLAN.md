# Implementation Plan

Updated: 2026-04-22

## Queue Rules

- Exactly `1` task may be `ACTIVE`.
- At most `3` tasks may be `QUEUED`.
- At most `2` tasks may be `BLOCKED`.
- Every task must fit the schema:
  `id | gate | target | files | verify | done_when | if_fail_then`

## ACTIVE

`PO3-square.2d3.actual-Ak-split | gate=H-bridge | target=Resolve the current hard blocker for the live wall by first reducing the real `A_k` tower to its honest local normal form: derive one exact theorem-shape showing that near a moving top point the reciprocal-product avatar has a local log-slope `Λ_k(ξ)=∑_{j=1}^{k+1}(ξ-(N+j))^{-1}` (equivalently a digamma-difference) and therefore behaves like a local exponential packet on scale `1/|Λ_k(ξ)|`; then either feed that normal form into a finite `po3_gamma_packet + remainder` split or record the exact incompatibility if near-maximizers of the real tower do not live in the regular `|Λ_k(ξ)| ≍ log k` regime | files=q3.lean.aristotle/Q3/Proofs/PO3Cert/PO3SquareSignedDominanceCertificate_2026_04_21.lean; q3.lean.aristotle/Q3/Proofs/PO3Cert/README.md; q3.lean.aristotle/docs/INSIGHTS.md; q3.lean.aristotle/docs/insights/h1_po3_route_ladder_2026_04_19.md; q3.lean.aristotle/docs/insights/h1_po2_cross_sign_bulk_exactness_2026_03_16.md; q3.lean.aristotle/ACTIVE/graphs/ROUTE_KILL_REGISTRY.md | verify=rg -n -F "po3_gamma_packet_eq_sum_prod" q3.lean.aristotle/Q3/Proofs/PO3Cert/PO3SquareSignedDominanceCertificate_2026_04_21.lean && rg -n -e "local log-slope" -e "1/|Λ_k(ξ)|" -e "actual A_k split" -e "hard blocker" q3.lean.aristotle/docs/INSIGHTS.md q3.lean.aristotle/ACTIVE/PHASE_MONITOR.md && cd q3.lean.aristotle && lake build Q3.Proofs.PO3Cert | done_when=the repo contains either one honest local normal-form bridge from the actual reciprocal-product tower to a local exponential packet model strong enough to feed the frozen `po3_gamma_packet + remainder` certificate shape, or one explicit incompatibility note showing that the naive `1/log k` top-window simplification is not a valid mainline reduction | if_fail_then=write the exact incompatibility in `docs/INSIGHTS.md` and, if needed, escalate it to `ACTIVE/graphs/ROUTE_KILL_REGISTRY.md``

## QUEUED

`H-bridge.12 | gate=H-bridge | target=Once `PO3-square.2d3` is honestly closed, resynchronize the downstream theorem shells: confirm that `PO4/PO5` and `H2^f/H3^f/H4^f` consume only the now-frozen `PO3` interface and do not secretly rely on a stronger pre-wall statement | files=q3.lean.aristotle/docs/insights/h1_po4_same_sign_boundary_identification_2026_03_18.md; q3.lean.aristotle/docs/insights/h1_po5_cap_separation_2026_03_19.md; q3.lean.aristotle/docs/insights/h2_filtered_cap_reduction_2026_03_19.md; q3.lean.aristotle/docs/insights/h3_filtered_gap_transfer_2026_03_19.md; q3.lean.aristotle/docs/insights/h4_suzuki_endpoint_to_rh_2026_03_20.md; q3.lean.aristotle/docs/INSIGHTS.md | verify=rg -n -F "PO3" q3.lean.aristotle/docs/insights/h1_po4_same_sign_boundary_identification_2026_03_18.md q3.lean.aristotle/docs/insights/h1_po5_cap_separation_2026_03_19.md && rg -n -F "H4" q3.lean.aristotle/docs/insights/h4_suzuki_endpoint_to_rh_2026_03_20.md | done_when=the downstream package is explicitly certified as consuming only the honest post-wall `PO3` handoff and no hidden stronger assumption remains | if_fail_then=record the mismatch in `docs/INSIGHTS.md` and split the offending handoff into a dedicated blocker packet`

## BLOCKED

`PO3-submit | gate=H-bridge | target=Submit the first `PO3` Aristotle job only after the prompt is drafted, the Lean landing zone is fixed, and the user has explicitly approved the exact request text | files=q3.lean.aristotle/aristotle_input/ARISTOTLE_PROMPT_GUIDELINES.md; q3.lean.aristotle/ACTIVE/aristotle/ARISTOTLE_WORKFLOW.md; q3.lean.aristotle/aristotle_input/project_ids.txt | verify=source /Users/emalam/Documents/GitHub/rh_lean_01_2026/.venv/bin/activate && aristotle list --limit 1 >/dev/null | done_when=the reviewed prompt is ready and only user approval blocks submission | if_fail_then=keep the task blocked and continue with local receiver tightening`

`Legacy-queue | gate=background | target=Leave old pre-`PO2` sprint tasks archival-only; do not let stale queue items override the active `PO3-square.2d3` execution work | files=IMPLEMENTATION_PLAN.md; q3.lean.aristotle/PROJECT_ORCHESTRATOR.md; q3.lean.aristotle/ACTIVE/PHASE_MONITOR.md | verify=rg -n -F "PO3-square.2d3.actual-Ak-split" IMPLEMENTATION_PLAN.md && rg -n -F "current_step_id: PO3-square.2d3" q3.lean.aristotle/ACTIVE/PHASE_MONITOR.md && ! rg -n -F "ACTIVE/SPRINT_MONITOR.md" IMPLEMENTATION_PLAN.md | done_when=the execution queue no longer points to stale pre-wall tasks as if they were active | if_fail_then=trim the queue further and keep only current-route items`
