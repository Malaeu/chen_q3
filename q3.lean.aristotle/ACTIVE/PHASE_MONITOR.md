# Phase Monitor

status: ACTIVE
phase: H1_PO1_direct_attack
started: 2026-03-16
mainline: T0-pd -> H-bridge -> H4 -> RH
macro_route: Door1((+,-) adapter) -> Door2((++) boundary+cap) -> Door3(compression neutrality) -> H2^f -> H3^f -> H4^f -> RH
macro_position: Door3 / compression neutrality / P6
main_kill_gate: Door3 fails if finite compression introduces a new theorem-shaped channel instead of pure bookkeeping
current_lane: A
current_step_id: P6
current_step_title: compression neutrality
current_owner: local-agent
current_artifact: docs/insights/h1_po6_compression_neutrality_2026_03_19.md
worker_protocol: q3.lean.aristotle/ACTIVE/AGENT_PROTOCOL.md
worker_request: q3.lean.aristotle/ACTIVE/requests/proshka_h1_po6_compression_neutrality_2026_03_19/node.md
worker_report: q3.lean.aristotle/ACTIVE/requests/proshka_h1_po6_compression_neutrality_2026_03_19/report.md
last_completed_phase: Q_zeta_core_short_circuit
last_completed_artifact: docs/insights/q_zeta_core_sprint_decision_2026_03_16.md
last_completed_commit: 6752a732
last_completed_step_id: P5
last_completed_step_artifact: docs/insights/h1_po5_cap_separation_2026_03_19.md
last_completed_step_commit: b60599d9
next_deliverable: freeze the exact compression-neutrality claim, the bookkeeping-only fallback, and the route-kill condition for any new theorem-shaped compression channel
next_verify: rg -n -e "PO6|compression neutrality|E_\\{a,\\\\mathrm\\{comp\\}\\}|bookkeeping|route-kill" q3.lean.aristotle/docs/insights/h1_po6_compression_neutrality_2026_03_19.md

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

### `P6` — compression neutrality

Goal:

- freeze the exact compression-neutrality claim;
- keep finite compression at bookkeeping level only;
- prepare a clean handoff to the final filtered `H1^f` packaging.

Required output:

- one theorem-shaped statement of
  `E_{a,\mathrm{comp}}^{+-}=0` and `E_{a,\mathrm{comp}}^{++}=0`, or a precise
  bookkeeping-only fallback;
- one exact packaging line
  `D_{a,M,N}=P_{M,N}\mathcal D_{a,N}P_{M,N}+\mathcal E_{a,M,N}`;
- one explicit kill condition for any new theorem-shaped compression channel.

Exact success criterion:

- the next theorem attempt is no longer “does finite sectioning create a new
  defect?”, but one final filtered `H1^f` packaging step with compression
  already demoted to bookkeeping.

## Macro view

This phase should now be read in the compressed route language:

- Door 1 = `(+,-)` adapter:
  `P1` tail defect setup, `P2` bulk exactness, `P3` boundary cancellation;
- Door 2 = `(++)` boundary-plus-cap theorem block;
- Door 3 = compression neutrality;
- Final = `H2^f -> H3^f -> H4^f -> RH`.

Current position:

- Door 1 stays closed;
- Door 2 is now treated as closed tightly enough through `P5`;
- `P6` is the Door-3 gate that decides whether finite descent stays clean.
