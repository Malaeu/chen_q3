# Implementation Plan

Updated: 2026-04-25

## Queue Rules

- Exactly `1` task may be `ACTIVE`.
- At most `3` tasks may be `QUEUED`.
- At most `2` tasks may be `BLOCKED`.
- Every task must fit the schema:
  `id | gate | target | files | verify | done_when | if_fail_then`

## ACTIVE

`PO3-square.2d3.endpoint-row-orientation-corollaries | gate=H-bridge | target=Specialize the orientation-safe product asymptotic to concrete endpoint rows: left-edge upper extension gives integer rows `exp(-p t)`, while right-edge later-base lower truncation gives only fractional rows `exp(beta t)` for `0<=beta<=1`; record the false right-edge integer `p>1` shape as an obstruction, then feed fractional generalized Vandermonde rows into bounded-separated projection | files=q3.lean.aristotle/Q3/Proofs/PO3Cert/PO3SquareSignedDominanceCertificate_2026_04_21.lean; q3.lean.aristotle/docs/insights/h1_po3_square_2d3_endpoint_row_orientation_corollaries_2026_04_25.md; q3.lean.aristotle/docs/insights/h1_po3_square_2d3_endpoint_row_product_asymptotic_2026_04_25.md; q3.lean.aristotle/docs/INSIGHTS.md; q3.lean.aristotle/ACTIVE/PHASE_MONITOR.md; q3.lean.aristotle/ACTIVE/graphs/ROUTE_KILL_REGISTRY.md | verify=rg -n -e "po3_left_edge_upper_extension_endpoint_row_asymptotic" -e "po3_right_edge_lower_truncation_endpoint_row_asymptotic" -e "po3_right_edge_lower_truncation_ratio_le_one_asymptotically" -e "fractional" q3.lean.aristotle/Q3/Proofs/PO3Cert/PO3SquareSignedDominanceCertificate_2026_04_21.lean q3.lean.aristotle/docs/INSIGHTS.md q3.lean.aristotle/docs/insights/h1_po3_square_2d3_endpoint_row_orientation_corollaries_2026_04_25.md q3.lean.aristotle/ACTIVE/PHASE_MONITOR.md q3.lean.aristotle/ACTIVE/graphs/ROUTE_KILL_REGISTRY.md IMPLEMENTATION_PLAN.md && cd q3.lean.aristotle && lake build Q3.Proofs.PO3Cert | done_when=the repo records the two endpoint orientation corollaries and the right-edge ratio<=1 obstruction, with the active blocker narrowed to proving the concrete theta-slope estimates or consuming fractional generalized Vandermonde rows | if_fail_then=record the false right-edge integer-row obstruction in `ACTIVE/graphs/ROUTE_KILL_REGISTRY.md` and switch to fractional rows before Vandermonde capture`

## QUEUED

`H-bridge.12 | gate=H-bridge | target=Once `PO3-square.2d3` is honestly closed, resynchronize the downstream theorem shells: confirm that `PO4/PO5` and `H2^f/H3^f/H4^f` consume only the now-frozen `PO3` interface and do not secretly rely on a stronger pre-wall statement | files=q3.lean.aristotle/docs/insights/h1_po4_same_sign_boundary_identification_2026_03_18.md; q3.lean.aristotle/docs/insights/h1_po5_cap_separation_2026_03_19.md; q3.lean.aristotle/docs/insights/h2_filtered_cap_reduction_2026_03_19.md; q3.lean.aristotle/docs/insights/h3_filtered_gap_transfer_2026_03_19.md; q3.lean.aristotle/docs/insights/h4_suzuki_endpoint_to_rh_2026_03_20.md; q3.lean.aristotle/docs/INSIGHTS.md | verify=rg -n -F "PO3" q3.lean.aristotle/docs/insights/h1_po4_same_sign_boundary_identification_2026_03_18.md q3.lean.aristotle/docs/insights/h1_po5_cap_separation_2026_03_19.md && rg -n -F "H4" q3.lean.aristotle/docs/insights/h4_suzuki_endpoint_to_rh_2026_03_20.md | done_when=the downstream package is explicitly certified as consuming only the honest post-wall `PO3` handoff and no hidden stronger assumption remains | if_fail_then=record the mismatch in `docs/INSIGHTS.md` and split the offending handoff into a dedicated blocker packet`

## BLOCKED

`PO3-submit | gate=H-bridge | target=Submit the first `PO3` Aristotle job only after the prompt is drafted, the Lean landing zone is fixed, and the user has explicitly approved the exact request text | files=q3.lean.aristotle/aristotle_input/ARISTOTLE_PROMPT_GUIDELINES.md; q3.lean.aristotle/ACTIVE/aristotle/ARISTOTLE_WORKFLOW.md; q3.lean.aristotle/aristotle_input/project_ids.txt | verify=source /Users/emalam/Documents/GitHub/rh_lean_01_2026/.venv/bin/activate && aristotle list --limit 1 >/dev/null | done_when=the reviewed prompt is ready and only user approval blocks submission | if_fail_then=keep the task blocked and continue with local receiver tightening`

`Legacy-queue | gate=background | target=Leave old pre-`PO2` sprint tasks archival-only; do not let stale queue items override the active `PO3-square.2d3` execution work | files=IMPLEMENTATION_PLAN.md; q3.lean.aristotle/PROJECT_ORCHESTRATOR.md; q3.lean.aristotle/ACTIVE/PHASE_MONITOR.md | verify=rg -n -F "PO3-square.2d3.shift-orientation-audit" IMPLEMENTATION_PLAN.md && rg -n -F "current_step_id: PO3-square.2d3" q3.lean.aristotle/ACTIVE/PHASE_MONITOR.md && ! rg -n -F "ACTIVE/SPRINT_MONITOR.md" IMPLEMENTATION_PLAN.md | done_when=the execution queue no longer points to stale pre-wall tasks as if they were active | if_fail_then=trim the queue further and keep only current-route items`
