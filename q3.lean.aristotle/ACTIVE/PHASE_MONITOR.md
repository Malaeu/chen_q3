# Phase Monitor

status: ACTIVE
phase: H1_real_proof_attack
started: 2026-03-20
mainline: T0-pd -> H-bridge -> H4 -> RH
macro_route: Door1((+,-) adapter) -> Door2((++) boundary+cap) -> Door3(compression neutrality) -> H2^f -> H3^f -> H4^f -> RH
macro_position: Real proof-critical reset / PO3 boundary proof-packet audit
main_kill_gate: the route fails if PO3 leaves a genuine non-cap cross-sign boundary residue
kill_writeback: q3.lean.aristotle/ACTIVE/graphs/ROUTE_KILL_REGISTRY.md
rollback_target_if_killed: rollback to the last real branch point H-bridge vs PSD-pd in PROJECT_ORCHESTRATOR.md
current_lane: A
current_step_id: PO3
current_step_title: cross-sign boundary cancellation proof packet
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
next_deliverable: `PO2` now lands in the admissible fallback form `\mathcal D_{a,N}^{+-}=\mathcal D_{a,\partial}^{+-}+\mathcal D_{a,\mathrm{cap}}^{+-}` and the historical `PO3` theorem shell matches that interface, but the mathematical proof packet for `PO3a` is still missing; the next forced task is therefore to derive an explicit mixed boundary formula for `\mathcal D_{a,\partial}^{+-}`, isolate the exact cancellation mechanism, and only then use `Q3/Proofs/HBridge_PO3_Shell.lean` as the landing shell
next_verify: rg -n -F "PO3 boundary proof-packet audit" q3.lean.aristotle/ACTIVE/PHASE_MONITOR.md && rg -n -F "proof packet for `PO3a` is still missing" q3.lean.aristotle/docs/INSIGHTS.md && rg -n -F "proof packet for `PO3a`" IMPLEMENTATION_PLAN.md

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

### `PO3` — cross-sign boundary cancellation proof packet

Goal:

- preserve the already frozen mathematical shell `PO3a/PO3b/PO3c` without
  reopening bulk arithmetic;
- isolate the missing explicit formula for the mixed boundary channel
  `\mathcal D_{a,\partial}^{+-}`;
- identify the exact cancellation mechanism that should force that channel to
  vanish;
- keep `Q3/Proofs/HBridge_PO3_Shell.lean` only as an auxiliary landing shell
  until the actual proof packet exists.

Required output:

- one exact list of mathematical inputs that would imply `PO3a`;
- one explicit missing lemma statement for the mixed boundary formula;
- one route-kill criterion if the mixed boundary channel cannot be forced to
  vanish;
- one note on how the auxiliary Lean shell is to be used once the packet is real.

Exact success criterion:

- the next theorem attempt is no longer a broad search, but one exact
  boundary-cancellation lemma with a concrete source stack and failure mode.

Exact failure criterion:

- if no explicit mixed-boundary formula and no exact cancellation mechanism can
  be identified, record that as a genuine mathematical blocker on `PO3a`
  rather than pretending the shell is ready for proof submission.

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
- the first real proof-critical gate on the route is therefore still `PO3`,
  and the live burden is the missing proof packet for `PO3a`.
