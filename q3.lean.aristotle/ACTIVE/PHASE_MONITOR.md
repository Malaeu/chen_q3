# Phase Monitor

status: ACTIVE
phase: H1_real_proof_attack
started: 2026-03-20
mainline: T0-pd -> H-bridge -> H4 -> RH
macro_route: Door1((+,-) adapter) -> Door2((++) boundary+cap) -> Door3(compression neutrality) -> H2^f -> H3^f -> H4^f -> RH
macro_position: Real proof-critical reset / H1 cross-sign boundary cancellation
main_kill_gate: the route fails if PO3 leaves a genuine non-cap cross-sign boundary residue
kill_writeback: q3.lean.aristotle/ACTIVE/graphs/ROUTE_KILL_REGISTRY.md
rollback_target_if_killed: rollback to the last real branch point H-bridge vs PSD-pd in PROJECT_ORCHESTRATOR.md
current_lane: A
current_step_id: PO3
current_step_title: cross-sign boundary cancellation
current_owner: local-agent
current_artifact: docs/insights/h1_po3_cross_sign_boundary_cancellation_2026_03_16.md
worker_protocol: q3.lean.aristotle/ACTIVE/AGENT_PROTOCOL.md
worker_request: q3.lean.aristotle/ACTIVE/requests/proshka_h1_po3_cross_sign_boundary_2026_03_16/node.md
worker_report: q3.lean.aristotle/ACTIVE/requests/proshka_h1_po3_cross_sign_boundary_2026_03_16/report.md
last_completed_phase: H4_suzuki_endpoint_attack
last_completed_artifact: docs/insights/h4_suzuki_endpoint_to_rh_2026_03_20.md
last_completed_commit: 83e973ac
last_completed_step_id: PO2
last_completed_step_artifact: docs/insights/h1_po2_cross_sign_bulk_exactness_2026_03_16.md
last_completed_step_commit: 414464f3
next_deliverable: `PO2` now lands in the admissible fallback form `\mathcal D_{a,N}^{+-}=\mathcal D_{a,\partial}^{+-}+\mathcal D_{a,\mathrm{cap}}^{+-}`; the next forced packet is therefore `PO3`, which must kill the named cross-sign boundary channel `\mathcal D_{a,\partial}^{+-}` without reopening bulk arithmetic, and then hand the mixed block to the cap-only endpoint before Door 2
next_verify: rg -n -F "D2g33. Post-" q3.lean.aristotle/docs/insights/h1_po2_cross_sign_bulk_exactness_2026_03_16.md && rg -n -F "PO3a." q3.lean.aristotle/docs/insights/h1_po3_cross_sign_boundary_cancellation_2026_03_16.md && rg -n -F "cross-sign boundary cancellation" q3.lean.aristotle/ACTIVE/PHASE_MONITOR.md

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
  conditional, and therefore attacks the first unresolved proof-critical gate
  back in `H1`, now `PO3`;
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

### `PO3` — cross-sign boundary cancellation

Goal:

- kill the named cross-sign boundary channel
  `\mathcal D_{a,\partial}^{+-}`;
- keep the mixed block cap-only on the `(+,-)` side:
  `\mathcal D_{a,N}^{+-}=\mathcal D_{a,\mathrm{cap}}^{+-}`;
- close the `(-,+)` boundary channel by symmetry, not by reopening a second
  mixed theorem;
- prepare a clean handoff from Door 1 to Door 2, not a return to bulk
  arithmetic.

Required output:

- one theorem-shaped boundary-cancellation statement `PO3a`;
- one cap-only corollary `PO3b`;
- one symmetry handoff statement `PO3c`;
- one explicit route-kill condition for a surviving non-cap boundary residue.

Exact success criterion:

- the next theorem attempt is no longer about any cross-sign channel, but
  moves to Door 2: same-sign boundary identification / cap separation.

Exact failure criterion:

- if `PO3` leaves a genuine non-cap cross-sign boundary residue, then the
  current `H-bridge` theorem shape is killed or near-killed and must be
  written back to `ACTIVE/graphs/ROUTE_KILL_REGISTRY.md` before rollback to
  the `PSD-pd` branch.

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
- the first real proof-critical gate on the route is therefore now `PO3`.
