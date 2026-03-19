# Phase Monitor

status: ACTIVE
phase: H1_PO1_direct_attack
started: 2026-03-16
mainline: T0-pd -> H-bridge -> H4 -> RH
macro_route: Door1((+,-) adapter) -> Door2((++) boundary+cap) -> Door3(compression neutrality) -> H2^f -> H3^f -> H4^f -> RH
macro_position: Door2 / cap separation / P5
main_kill_gate: Door2 same-sign boundary-vs-cap separation, with earlier near-route-kill if non-cap cross-sign boundary survives at P3
current_lane: A
current_step_id: P5
current_step_title: cap separation
current_owner: local-agent
current_artifact: docs/insights/h1_po5_cap_separation_2026_03_19.md
worker_protocol: q3.lean.aristotle/ACTIVE/AGENT_PROTOCOL.md
worker_request: q3.lean.aristotle/ACTIVE/requests/proshka_h1_po5_cap_separation_2026_03_19/node.md
worker_report: q3.lean.aristotle/ACTIVE/requests/proshka_h1_po5_cap_separation_2026_03_19/report.md
last_completed_phase: Q_zeta_core_short_circuit
last_completed_artifact: docs/insights/q_zeta_core_sprint_decision_2026_03_16.md
last_completed_commit: 6752a732
last_completed_step_id: P4
last_completed_step_artifact: docs/insights/h1_po4_same_sign_boundary_identification_2026_03_18.md
last_completed_step_commit: 89db6f3e
next_deliverable: freeze the exact cap-identification claim, the boundary-plus-cap split, and the route-kill condition for any drifting or unnamed finite remainder channel
next_verify: rg -n -e "PO5|cap separation|C_a\\^\\{\\\\mathrm\\{cap\\}\\}|third channel|route-kill" q3.lean.aristotle/docs/insights/h1_po5_cap_separation_2026_03_19.md

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

### `P5` — cap separation

Goal:

- freeze the exact cap-identification claim;
- separate the finite cap term from the named same-sign boundary operator;
- prepare a clean handoff to compression neutrality.

Required output:

- one theorem-shaped statement of `\mathcal D_{a,\mathrm{cap}}^{++}=C_a^{\mathrm{cap}}`;
- one exact boundary-plus-cap split for the same-sign block;
- one explicit kill condition for any drifting or third finite remainder
  channel.

Exact success criterion:

- the next theorem attempt is no longer “what remains after the boundary is
  named?”, but one exact cap-identification lemma plus a clean handoff to
  `PO6`.

## Macro view

This phase should now be read in the compressed route language:

- Door 1 = `(+,-)` adapter:
  `P1` tail defect setup, `P2` bulk exactness, `P3` boundary cancellation;
- Door 2 = `(++)` boundary-plus-cap theorem block;
- Door 3 = compression neutrality;
- Final = `H2^f -> H3^f -> H4^f -> RH`.

Current position:

- Door 1 stays closed;
- `P5` is the second gate inside Door 2;
- if `P5` lands, Door 2 has the intended boundary-plus-cap theorem shape and
  the route can move to compression neutrality.
