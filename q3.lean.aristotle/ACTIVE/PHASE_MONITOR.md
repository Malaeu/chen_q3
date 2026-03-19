# Phase Monitor

status: ACTIVE
phase: H1_PO1_direct_attack
started: 2026-03-16
mainline: T0-pd -> H-bridge -> H4 -> RH
macro_route: Door1((+,-) adapter) -> Door2((++) boundary+cap) -> Door3(compression neutrality) -> H2^f -> H3^f -> H4^f -> RH
macro_position: H1 final packaging / P7
main_kill_gate: H1 packaging fails if it reopens an earlier gate or reintroduces a third theorem-shaped channel
current_lane: A
current_step_id: P7
current_step_title: final filtered theorem package
current_owner: local-agent
current_artifact: docs/insights/h1_po7_final_filtered_package_2026_03_19.md
worker_protocol: q3.lean.aristotle/ACTIVE/AGENT_PROTOCOL.md
worker_request: q3.lean.aristotle/ACTIVE/requests/proshka_h1_po7_final_package_2026_03_19/node.md
worker_report: q3.lean.aristotle/ACTIVE/requests/proshka_h1_po7_final_package_2026_03_19/report.md
last_completed_phase: Q_zeta_core_short_circuit
last_completed_artifact: docs/insights/q_zeta_core_sprint_decision_2026_03_16.md
last_completed_commit: 6752a732
last_completed_step_id: P6
last_completed_step_artifact: docs/insights/h1_po6_compression_neutrality_2026_03_19.md
last_completed_step_commit: d0269bdd
next_deliverable: freeze the final mixed-line, same-sign-line, and symmetry packaging with no reopening of earlier gates
next_verify: rg -n -e "PO7|final filtered theorem package|symmetry|route-kill" q3.lean.aristotle/docs/insights/h1_po7_final_filtered_package_2026_03_19.md

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
- lane `A` has now closed Door 1 tightly enough and continues with Door 2 from
  `PO4` onward;
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

### `P7` — final filtered theorem package

Goal:

- freeze the final filtered theorem package for `H1^f`;
- keep the remaining two blocks at symmetry level only;
- prepare a clean handoff to `H2^f`.

Required output:

- one theorem-shaped mixed line;
- one theorem-shaped same-sign line;
- one symmetry closure for the remaining two blocks;
- one explicit kill condition for any reopening of earlier gates.

Exact success criterion:

- the next theorem attempt is no longer “what remains inside `H1`?”, but the
  upper bridge continuation `H2^f -> H3^f -> H4^f`.

## Macro view

This phase should now be read in the compressed route language:

- Door 1 = `(+,-)` adapter:
  `P1` tail defect setup, `P2` bulk exactness, `P3` boundary cancellation;
- Door 2 = `(++)` boundary-plus-cap theorem block;
- Door 3 = compression neutrality;
- Final = `H2^f -> H3^f -> H4^f -> RH`.

Current position:

- Door 1 stays closed;
- Door 2 stays closed;
- Door 3 is now treated as closed tightly enough through `P6`;
- `P7` is the local H1 packaging gate before the upper bridge resumes.
