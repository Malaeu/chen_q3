# Phase Monitor

status: ACTIVE
phase: H1_PO1_direct_attack
started: 2026-03-16
mainline: T0-pd -> H-bridge -> H4 -> RH
macro_route: Door1((+,-) adapter) -> Door2((++) boundary+cap) -> Door3(compression neutrality) -> H2^f -> H3^f -> H4^f -> RH
macro_position: Door2 / boundary identification / P4
main_kill_gate: Door2 same-sign boundary-vs-cap separation, with earlier near-route-kill if non-cap cross-sign boundary survives at P3
current_lane: A
current_step_id: P4
current_step_title: same-sign boundary identification
current_owner: local-agent
current_artifact: docs/insights/h1_po4_same_sign_boundary_identification_2026_03_18.md
worker_protocol: q3.lean.aristotle/ACTIVE/AGENT_PROTOCOL.md
worker_request: q3.lean.aristotle/ACTIVE/requests/proshka_h1_po4_same_sign_boundary_2026_03_18/node.md
worker_report: q3.lean.aristotle/ACTIVE/requests/proshka_h1_po4_same_sign_boundary_2026_03_18/report.md
last_completed_phase: Q_zeta_core_short_circuit
last_completed_artifact: docs/insights/q_zeta_core_sprint_decision_2026_03_16.md
last_completed_commit: 6752a732
last_completed_step_id: P3
last_completed_step_artifact: docs/insights/h1_po3_cross_sign_boundary_cancellation_2026_03_16.md
last_completed_step_commit: 28d6c255
next_deliverable: freeze the exact same-sign boundary identification claim, the admissible operator shapes for H_a^{ss}, and the route-kill condition for any unnamed same-sign moving residue
next_verify: rg -n -e "PO4|same-sign boundary|H_a\\^\\{\\\\mathrm\\{ss\\}\\}|route-kill" q3.lean.aristotle/docs/insights/h1_po4_same_sign_boundary_identification_2026_03_18.md

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
- write only to `worker_report`.

## Current step

### `P4` — same-sign boundary identification

Goal:

- freeze the exact same-sign boundary identification claim;
- force the surviving `(++)` correction into one named operator channel;
- prepare a clean handoff to cap separation.

Required output:

- one theorem-shaped statement of `\mathcal D_{a,\partial}^{++}=H_a^{\mathrm{ss}}`;
- one admissible list of operator shapes for `H_a^{\mathrm{ss}}`;
- one explicit kill condition for an unnamed same-sign moving residue.

Exact success criterion:

- the next theorem attempt is no longer “what survives in `(++)`?”, but one
  exact operator-identification lemma plus a clean handoff to `PO5`.

## Macro view

This phase should now be read in the compressed route language:

- Door 1 = `(+,-)` adapter:
  `P1` tail defect setup, `P2` bulk exactness, `P3` boundary cancellation;
- Door 2 = `(++)` boundary-plus-cap theorem block;
- Door 3 = compression neutrality;
- Final = `H2^f -> H3^f -> H4^f -> RH`.

Current position:

- Door 1 is now treated as closed tightly enough for local theorem work;
- `P4` is the first gate inside Door 2;
- if `P4` lands, the route can move from same-sign boundary identification to
  cap separation without reopening the mixed block.
