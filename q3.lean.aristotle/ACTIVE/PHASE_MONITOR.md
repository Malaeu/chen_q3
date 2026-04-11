# Phase Monitor

status: ACTIVE
phase: H1_real_proof_attack
started: 2026-03-20
mainline: T0-pd -> H-bridge -> H4 -> RH
macro_route: Door1((+,-) adapter) -> Door2((++) boundary+cap) -> Door3(compression neutrality) -> H2^f -> H3^f -> H4^f -> RH
macro_position: Real proof-critical reset / PO3 theorem-shell formalization
main_kill_gate: the route fails if PO3 leaves a genuine non-cap cross-sign boundary residue
kill_writeback: q3.lean.aristotle/ACTIVE/graphs/ROUTE_KILL_REGISTRY.md
rollback_target_if_killed: rollback to the last real branch point H-bridge vs PSD-pd in PROJECT_ORCHESTRATOR.md
current_lane: A
current_step_id: PO3
current_step_title: cross-sign boundary cancellation formalization
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
next_deliverable: `PO2` now lands in the admissible fallback form `\mathcal D_{a,N}^{+-}=\mathcal D_{a,\partial}^{+-}+\mathcal D_{a,\mathrm{cap}}^{+-}` and the historical `PO3` theorem shell already matches that interface; the first executable receiver now exists as `Q3/Proofs/HBridge_PO3_Shell.lean`, so the next forced task is to attach the genuine Q3 objects to that shell and prepare a prompt-ready Aristotle draft for the first nontrivial analytic bridge into `PO3a/PO3b/PO3c`
next_verify: rg -n -F "PO3 theorem-shell formalization" q3.lean.aristotle/ACTIVE/PHASE_MONITOR.md && rg -n -F "HBridge_PO3_Shell.lean" q3.lean.aristotle/docs/INSIGHTS.md && rg -n -F "PO3a/PO3b/PO3c" IMPLEMENTATION_PLAN.md

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
  conditional, and therefore uses `PO3` as the first executable lower-shell
  formalization gate back in `H1`;
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

### `PO3` — cross-sign boundary cancellation formalization

Goal:

- preserve the already frozen mathematical shell `PO3a/PO3b/PO3c` without
  reopening bulk arithmetic;
- identify the first honest Lean landing zone for the mixed boundary packet;
- prepare a prompt-ready Aristotle receiver for that shell, but do not submit
  before user review;
- verify that `PO4/PO5` and the packaged upper bridge still consume exactly
  this interface.

Required output:

- one explicit formalization receiver for `PO3a/PO3b/PO3c`
  (currently `Q3/Proofs/HBridge_PO3_Shell.lean`);
- one prompt-ready Aristotle draft path or equivalent receiver note;
- one downstream synchronization check showing that `PO4/PO5` still read the
  same mixed-side interface;
- one exact blocker statement if the needed objects are not yet represented in
  Lean tightly enough.

Exact success criterion:

- the next theorem attempt is a concrete Lean/Aristotle shell for `PO3`,
  rather than a new search for cross-sign boundary geometry.

Exact failure criterion:

- if no honest Lean landing zone can be identified for `PO3a/PO3b/PO3c`
  without inventing a new architecture, record that as a formalization blocker
  and split the task into receiver-creation before any proof submission.

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
  but the live execution burden is now its formalization receiver rather than
  fresh mixed-block theorem discovery.
