# Phase Monitor

status: ACTIVE
phase: H1_PO1_direct_attack
started: 2026-03-16
mainline: T0-pd -> H-bridge -> H4 -> RH
current_lane: A
current_step_id: P2
current_step_title: cross-sign bulk exactness
current_owner: local-agent
current_artifact: docs/insights/h1_po2_cross_sign_bulk_exactness_2026_03_16.md
worker_protocol: q3.lean.aristotle/ACTIVE/AGENT_PROTOCOL.md
worker_request: q3.lean.aristotle/ACTIVE/requests/proshka_h1_po2_cross_sign_bulk_2026_03_16/node.md
worker_report: q3.lean.aristotle/ACTIVE/requests/proshka_h1_po2_cross_sign_bulk_2026_03_16/report.md
last_completed_phase: Q_zeta_core_short_circuit
last_completed_artifact: docs/insights/q_zeta_core_sprint_decision_2026_03_16.md
last_completed_commit: 6752a732
last_completed_step_id: P1
last_completed_step_artifact: docs/insights/h1_po1_tail_defect_attack_2026_03_16.md
last_completed_step_commit: 5cc9943f
next_deliverable: freeze the exact cross-sign bulk claim, its admissible remainder channels, and the route-kill condition for unnamed bulk residue
next_verify: rg -n -e "PO2|bulk exactness|route-kill|boundary/cap only" q3.lean.aristotle/docs/insights/h1_po2_cross_sign_bulk_exactness_2026_03_16.md

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

### `P2` — cross-sign bulk exactness

Goal:

- freeze the exact bulk claim on `\mathcal D_{a,N}^{+-}`;
- isolate the only admissible non-bulk remainder channels;
- make the first route-kill criterion explicit.

Required output:

- one theorem-shaped statement of `\mathcal D_{a,\mathrm{bulk}}^{+-}=0`;
- equivalent decomposition
  `\mathcal D_{a,N}^{+-}=\mathcal D_{a,\partial}^{+-}+\mathcal D_{a,\mathrm{cap}}^{+-}`;
- one explicit kill condition for unnamed bulk residue.

Exact success criterion:

- the next theorem attempt is no longer “understand the cross-sign defect”, but
  one exact bulk-vanishing lemma plus one explicit fork into boundary/cap-only
  remainder.
