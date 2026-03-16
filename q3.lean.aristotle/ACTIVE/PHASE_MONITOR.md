# Phase Monitor

status: ACTIVE
phase: H1_PO1_direct_attack
started: 2026-03-16
mainline: T0-pd -> H-bridge -> H4 -> RH
macro_route: Door1((+,-) adapter) -> Door2((++) boundary+cap) -> Door3(compression neutrality) -> H2^f -> H3^f -> H4^f -> RH
macro_position: Door1 / boundary half / P3
main_kill_gate: Door2 same-sign boundary-vs-cap separation, with earlier near-route-kill if non-cap cross-sign boundary survives at P3
current_lane: A
current_step_id: P3
current_step_title: cross-sign boundary cancellation
current_owner: local-agent
current_artifact: docs/insights/h1_po3_cross_sign_boundary_cancellation_2026_03_16.md
worker_protocol: q3.lean.aristotle/ACTIVE/AGENT_PROTOCOL.md
worker_request: q3.lean.aristotle/ACTIVE/requests/proshka_h1_po3_cross_sign_boundary_2026_03_16/node.md
worker_report: q3.lean.aristotle/ACTIVE/requests/proshka_h1_po3_cross_sign_boundary_2026_03_16/report.md
last_completed_phase: Q_zeta_core_short_circuit
last_completed_artifact: docs/insights/q_zeta_core_sprint_decision_2026_03_16.md
last_completed_commit: 6752a732
last_completed_step_id: P2
last_completed_step_artifact: docs/insights/h1_po2_cross_sign_bulk_exactness_2026_03_16.md
last_completed_step_commit: 288fcb6c
next_deliverable: freeze the exact cross-sign boundary cancellation claim, the cap-only fallback receiver, and the route-kill condition for any surviving non-cap cross-sign boundary term
next_verify: rg -n -e "PO3|boundary cancellation|cap-only|non-cap cross-sign boundary" q3.lean.aristotle/docs/insights/h1_po3_cross_sign_boundary_cancellation_2026_03_16.md

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
- lane `A` attacks `PO1 -> PO3` first;
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

### `P3` — cross-sign boundary cancellation

Goal:

- freeze the exact cross-sign boundary cancellation claim;
- leave only a cap-only admissible fallback on the `(+,-)` side;
- make the next asymmetry gate explicit.

Required output:

- one theorem-shaped statement of `\mathcal D_{a,\partial}^{+-}=0`;
- one exact cap-only fallback receiver for `(+,-)`;
- one explicit kill condition for surviving non-cap cross-sign boundary residue.

Exact success criterion:

- the next theorem attempt is no longer “classify cross-sign remainders”, but
  one exact boundary-cancellation lemma plus a cap-only theorem fork for the
  final `(+,-)` package.

## Macro view

This phase should now be read in the compressed route language:

- Door 1 = `(+,-)` adapter:
  `P1` tail defect setup, `P2` bulk exactness, `P3` boundary cancellation;
- Door 2 = `(++)` boundary-plus-cap theorem block;
- Door 3 = compression neutrality;
- Final = `H2^f -> H3^f -> H4^f -> RH`.

Current position:

- `P3` is not a standalone global gate;
- it is the boundary half of Door 1;
- if it lands, Door 1 becomes very close to closure.
