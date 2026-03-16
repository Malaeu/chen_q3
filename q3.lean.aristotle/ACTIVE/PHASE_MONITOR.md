# Phase Monitor

status: ACTIVE
phase: H1_PO1_direct_attack
started: 2026-03-16
mainline: T0-pd -> H-bridge -> H4 -> RH
current_lane: A
current_step_id: P1
current_step_title: tail defect definition and blockwise split
current_owner: local-agent
current_artifact: docs/insights/h1_po1_tail_defect_attack_2026_03_16.md
worker_protocol: q3.lean.aristotle/ACTIVE/AGENT_PROTOCOL.md
worker_request: q3.lean.aristotle/ACTIVE/requests/proshka_h1_po1_tail_defect_2026_03_16/node.md
worker_report: q3.lean.aristotle/ACTIVE/requests/proshka_h1_po1_tail_defect_2026_03_16/report.md
last_completed_phase: Q_zeta_core_short_circuit
last_completed_artifact: docs/insights/q_zeta_core_sprint_decision_2026_03_16.md
last_completed_commit: 6752a732
next_deliverable: freeze the exact tail-level defect object, its blockwise split, and the first lemma packet PO1a/PO1b
next_verify: rg -n -e "PO1a|PO1b|tail defect|blockwise split|Hermitian mirrors" q3.lean.aristotle/docs/insights/h1_po1_tail_defect_attack_2026_03_16.md

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

### `P1` — tail defect definition and blockwise split

Goal:

- freeze the exact infinite-tail defect object;
- split it into the four sign blocks and Hermitian mirrors;
- make the first real lemma packet explicit.

Required output:

- exact formula for `\mathcal D_{a,N}`;
- exact formulas for `\mathcal D_{a,N}^{++}`, `\mathcal D_{a,N}^{+-}`;
- symmetry recovery of `(-+)`, `(--)`;
- first lemma packet `PO1a/PO1b`.

Exact success criterion:

- the next theorem attempt is no longer “start H1”, but an exact tail-level
  definition lemma plus a block-splitting lemma.
