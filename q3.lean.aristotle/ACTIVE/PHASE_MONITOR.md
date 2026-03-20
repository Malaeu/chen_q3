# Phase Monitor

status: ACTIVE
phase: H4_suzuki_endpoint_attack
started: 2026-03-20
mainline: T0-pd -> H-bridge -> H4 -> RH
macro_route: Door1((+,-) adapter) -> Door2((++) boundary+cap) -> Door3(compression neutrality) -> H2^f -> H3^f -> H4^f -> RH
macro_position: Final upper bridge / H4 Suzuki endpoint to RH
main_kill_gate: H4 fails if the H3 kernel-kill output does not match Suzuki Theorem 1.4 cleanly for every a>0
current_lane: A
current_step_id: H4
current_step_title: Suzuki endpoint to RH
current_owner: local-agent
current_artifact: docs/insights/h4_suzuki_endpoint_to_rh_2026_03_20.md
worker_protocol: q3.lean.aristotle/ACTIVE/AGENT_PROTOCOL.md
worker_request: q3.lean.aristotle/ACTIVE/requests/proshka_h4_suzuki_endpoint_2026_03_20/node.md
worker_report: q3.lean.aristotle/ACTIVE/requests/proshka_h4_suzuki_endpoint_2026_03_20/report.md
last_completed_phase: H3_filtered_gap_attack
last_completed_artifact: docs/insights/h3_filtered_gap_transfer_2026_03_19.md
last_completed_commit: cd4937a4
last_completed_step_id: H3
last_completed_step_artifact: docs/insights/h3_filtered_gap_transfer_2026_03_19.md
last_completed_step_commit: cd4937a4
next_deliverable: freeze the exact endpoint implication H1^f+H2^f+H3^f => 0 not an eigenvalue of G_g[a] for every a>0, and the final appeal to Suzuki Theorem 1.4
next_verify: rg -n -e "H4|Suzuki Theorem 1.4|not an eigenvalue|sigma_p\\(G_g\\[a\\]\\)|route-kill" q3.lean.aristotle/docs/insights/h4_suzuki_endpoint_to_rh_2026_03_20.md

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
- lane `A` has now closed `H3^f` tightly enough and continues the upper
  bridge through `H4^f`;
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

### `H4` — Suzuki endpoint to RH

Goal:

- freeze the exact endpoint implication
  `H1^f + H2^f + H3^f => 0 \notin \sigma_p(G_g[a])` for every `a>0`;
- make the final appeal to Suzuki Theorem 1.4 explicit;
- close the filtered Suzuki--Q3 bridge without reopening earlier gates.

Required output:

- one theorem-shaped endpoint hypothesis;
- one theorem-shaped no-zero-eigenvalue conclusion;
- one explicit final implication to RH;
- one explicit route-kill condition if the endpoint does not read exactly.

Exact success criterion:

- the next theorem attempt is no longer inside the `H`-bridge, but outside it:
  either final manuscript packaging or formalization of the bridge.

## Macro view

This phase should now be read in the compressed route language:

- Door 1 = `(+,-)` adapter:
  `P1` tail defect setup, `P2` bulk exactness, `P3` boundary cancellation;
- Door 2 = `(++)` boundary-plus-cap theorem block;
- Door 3 = compression neutrality;
- Final = `H2^f -> H3^f -> H4^f -> RH`.

Current position:

- `H1^f` is now treated as packaged enough for handoff;
- `H2^f` and `H3^f` are treated as closed enough for the upper bridge to continue;
- the active gate is `H4^f`.
