# Phase Monitor

status: ACTIVE
phase: H3_filtered_gap_attack
started: 2026-03-19
mainline: T0-pd -> H-bridge -> H4 -> RH
macro_route: Door1((+,-) adapter) -> Door2((++) boundary+cap) -> Door3(compression neutrality) -> H2^f -> H3^f -> H4^f -> RH
macro_position: Upper bridge / H3 filtered gap transfer
main_kill_gate: H3 fails if the filtered Q3 gap plus cap positivity does not kill the kernel of G_g[a]
current_lane: A
current_step_id: H3
current_step_title: filtered gap transfer
current_owner: local-agent
current_artifact: docs/insights/h3_filtered_gap_transfer_2026_03_19.md
worker_protocol: q3.lean.aristotle/ACTIVE/AGENT_PROTOCOL.md
worker_request: q3.lean.aristotle/ACTIVE/requests/proshka_h3_filtered_gap_2026_03_19/node.md
worker_report: q3.lean.aristotle/ACTIVE/requests/proshka_h3_filtered_gap_2026_03_19/report.md
last_completed_phase: H2_filtered_cap_attack
last_completed_artifact: docs/insights/h2_filtered_cap_reduction_2026_03_19.md
last_completed_commit: 1ba3c44d
last_completed_step_id: H2
last_completed_step_artifact: docs/insights/h2_filtered_cap_reduction_2026_03_19.md
last_completed_step_commit: 1ba3c44d
next_deliverable: freeze the finite Q3 gap hypothesis, the filtered transfer to B_{M,N_a}, the tail-space coercive lower bound, and the cap-matrix-to-kernel-kill line
next_verify: rg -n -e "H3|filtered gap transfer|ker G_g\\[a\\]|q_\\{G,a\\}|route-kill" q3.lean.aristotle/docs/insights/h3_filtered_gap_transfer_2026_03_19.md

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
- lane `A` has now closed `H2^f` tightly enough and continues the upper
  bridge through `H3^f`;
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

### `H3` — filtered gap transfer

Goal:

- freeze the finite Q3 gap hypothesis in the upper bridge language;
- transfer that gap to the filtered metric side on the tail space;
- prepare a clean handoff to `H4^f`.

Required output:

- one theorem-shaped filtered gap hypothesis;
- one theorem-shaped transfer to `\widetilde Q_{M,N_a}\ge c(a)B_{M,N_a}`;
- one coercive lower bound on `V_a^{\mathrm{tail}}`;
- one explicit kernel-elimination line using cap positivity.

Exact success criterion:

- the next theorem attempt is no longer “can the gap transfer work?”, but the
  endpoint step `H4^f`.

## Macro view

This phase should now be read in the compressed route language:

- Door 1 = `(+,-)` adapter:
  `P1` tail defect setup, `P2` bulk exactness, `P3` boundary cancellation;
- Door 2 = `(++)` boundary-plus-cap theorem block;
- Door 3 = compression neutrality;
- Final = `H2^f -> H3^f -> H4^f -> RH`.

Current position:

- `H1^f` is now treated as packaged enough for handoff;
- `H2^f` is treated as closed enough for the upper bridge to continue;
- the active gate is `H3^f`.
