# Phase Monitor

status: ACTIVE
phase: H1_real_proof_attack
started: 2026-03-20
mainline: T0-pd -> H-bridge -> H4 -> RH
macro_route: Door1((+,-) adapter) -> Door2((++) boundary+cap) -> Door3(compression neutrality) -> H2^f -> H3^f -> H4^f -> RH
macro_position: PO3-square.2d3 live wall / transform-side Gamma tower dominant-packet attack
main_kill_gate: the route fails if the real transform-side Gamma tower admits a genuine infinite-support signed self-cancellation that defeats rightmost dominance versus mirror suppression
kill_writeback: q3.lean.aristotle/ACTIVE/graphs/ROUTE_KILL_REGISTRY.md
rollback_target_if_killed: rollback to the last real branch point H-bridge vs PSD-pd in PROJECT_ORCHESTRATOR.md
current_lane: A
current_step_id: PO3-square.2d3
current_step_title: transform-side Gamma tower dominant-packet estimate
current_owner: local-agent
current_artifact: ACTIVE/pipeline/oracle_questions/2026_04_21_po3_square_2d3_real_signed_rightmost_dominance_eventual_lower_bound_one_sided_gamma_tower_a_k_mirror_suppression_transform_side_wall.md
worker_protocol: q3.lean.aristotle/ACTIVE/AGENT_PROTOCOL.md
worker_request: q3.lean.aristotle/ACTIVE/requests/proshka_h1_po3_cross_sign_boundary_2026_03_16/node.md
worker_report: q3.lean.aristotle/ACTIVE/requests/proshka_h1_po3_cross_sign_boundary_2026_03_16/report.md
last_completed_phase: H4_suzuki_endpoint_attack
last_completed_artifact: docs/insights/h4_suzuki_endpoint_to_rh_2026_03_20.md
last_completed_commit: 83e973ac
last_completed_step_id: PO2
last_completed_step_artifact: docs/insights/h1_po2_cross_sign_bulk_exactness_2026_03_16.md
last_completed_step_commit: 414464f3
next_deliverable: the lower-shell feeder through `PO3-square.2d2` is now frozen, the abstract dominant-packet bridge shell is frozen in `Q3/Proofs/HBridge_PO3_Shell.lean`, and the direct certificate feeder is frozen in `Q3/Proofs/PO3Cert/PO3SquareSignedDominanceCertificate_2026_04_21.lean`; the next real attack is therefore no longer shell design but exact formula/data localization for the actual transform-side tower: pin down the manuscript/repo home of the real `A_k` side, the mirror `B_k` side, the support geometry `Y_a = {x_γ, x_γ - 1}`, and the first honest Lean landing surface for the true dominant-packet estimate that should feed the new certificate
next_verify: rg -n -F "PO3-square.2d3.formula-locate" IMPLEMENTATION_PLAN.md && rg -n -F "PO3SquareDominantPacketCertificate" q3.lean.aristotle/Q3/Proofs/PO3Cert/PO3SquareSignedDominanceCertificate_2026_04_21.lean && rg -n -F "dominant-packet feeder for `PO3-square.2d3`" q3.lean.aristotle/Q3/Proofs/PO3Cert/README.md

This file is the operational single source of truth after the Q_zeta sprint is
closed.

## Startup response contract

If this file exists and `status: ACTIVE`, the first new-session message should
be:

```text
Фаза активна: <phase>, текущий шаг <current_step_id> — <current_step_title>.
Сейчас открываю <current_artifact> и добиваю <next_deliverable>; если blocker
не появится, другие control docs не перечитываю.
```

## Phase contract

- no return to coordination-first work unless the theorem phase stalls;
- lane `A` now treats the upper bridge `H2^f -> H3^f -> H4^f` as packaged but
  conditional, and therefore uses `PO3` as the first unresolved lower-shell
  proof packet back in `H1`;
- lane `B` stays frozen at the canonical smallest-block certificate;
- no rank/basis language as theorem content;
- no new RH architecture.
- parallel worker agents must read this file before any closed sprint monitor.

## Worker loop

If a parallel worker is used during this phase, it should:

- read `SESSION_ENTRY.md`;
- read this phase monitor;
- read `AGENT_PROTOCOL.md`;
- read `worker_request`;
- return a narrow result to the orchestrator;
- let the orchestrator maintain the canonical `worker_report`.

## Current step

### `PO3-square.2d3` — transform-side Gamma tower dominant-packet estimate

Goal:

- keep the lower-shell feeder
  `PO3-shell.5/.6 -> PO3a-A2-real -> PO3a.4-real -> PO3-rig.1b.cert-real -> PO3-tail.1-real -> PO3-square.2d0a/.1/.2`
  frozen and do not reopen it;
- use the already-frozen shell landing surface in
  `Q3/Proofs/HBridge_PO3_Shell.lean`
  and the new `PO3Cert` feeder
  `PO3SquareDominantPacketCertificate`
  as fixed interfaces, not as new mathematical work;
- attack the only live burden directly:
  identify and then estimate the actual transform-side dominant packet on the
  `A_k` side strongly enough to beat the suppressed mirror `B_k` side.

Required output:

- one exact formula home and notation map for the real transform-side tower
  (`A_k`, `B_k`, `Y_a`, dominant packet candidates);
- one explicit Lean landing surface for the future real packet estimate;
- one route-kill criterion if the actual tower admits genuine infinite-support
  signed self-cancellation that defeats rightmost dominance.

Exact success criterion:

- the next theorem attempt is no longer shell refactoring or certificate design,
  but one honest real packet estimate feeding the frozen `PO3-square.2d3`
  certificate.

Exact failure criterion:

- if the actual transform-side formulas cannot be reconciled with the frozen
  dominant-packet certificate shape, record that incompatibility explicitly
  rather than reopening lower-shell architecture.

## Macro view

This phase should now be read in the compressed route language:

- Door 1 = `(+,-)` adapter:
  `P1` tail defect setup, `P2` bulk exactness, `P3` boundary cancellation;
- Door 2 = `(++)` boundary-plus-cap theorem block;
- Door 3 = compression neutrality;
- Final = `H2^f -> H3^f -> H4^f -> RH`.

Current position:

- `H1^f -> H2^f -> H3^f -> H4^f` is packaged tightly enough at theorem-shell level;
- RH is still not proved because that bridge remains conditional on unresolved
  `H1` proof input;
- the first real proof-critical gate on the route is still inside `PO3`,
  but its live mathematical point is now much narrower:
  `PO3-square.2d3`, the transform-side dominant-packet estimate on the actual
  Gamma tower.
