# Phase Monitor

status: ACTIVE
phase: H1_real_proof_attack
started: 2026-03-20
mainline: T0-pd -> H-bridge -> H4 -> RH
macro_route: Door1((+,-) adapter) -> Door2((++) boundary+cap) -> Door3(compression neutrality) -> H2^f -> H3^f -> H4^f -> RH
macro_position: Real proof-critical reset / H1 cross-sign bulk exactness
main_kill_gate: the route fails if PO2 leaves a genuine unnamed cross-sign bulk residue
kill_writeback: q3.lean.aristotle/ACTIVE/graphs/ROUTE_KILL_REGISTRY.md
rollback_target_if_killed: rollback to the last real branch point H-bridge vs PSD-pd in PROJECT_ORCHESTRATOR.md
current_lane: A
current_step_id: PO2
current_step_title: cross-sign bulk exactness
current_owner: local-agent
current_artifact: docs/insights/h1_po2_cross_sign_bulk_exactness_2026_03_16.md
worker_protocol: q3.lean.aristotle/ACTIVE/AGENT_PROTOCOL.md
worker_request: q3.lean.aristotle/ACTIVE/requests/proshka_h1_po2_cross_sign_bulk_2026_03_20/node.md
worker_report: q3.lean.aristotle/ACTIVE/requests/proshka_h1_po2_cross_sign_bulk_2026_03_20/report.md
last_completed_phase: H4_suzuki_endpoint_attack
last_completed_artifact: docs/insights/h4_suzuki_endpoint_to_rh_2026_03_20.md
last_completed_commit: 83e973ac
last_completed_step_id: H4
last_completed_step_artifact: docs/insights/h4_suzuki_endpoint_to_rh_2026_03_20.md
last_completed_step_commit: 83e973ac
next_deliverable: the Krein/localization branch remains demoted to backup, and both compactness versions of D3 are now blocked; `D2g29e` closes the ultra-near integer-resonance half of the direct arithmetic reduction by the normalized positive-definite route, so `PO2` is no longer waiting on `D2g29`; after rereading `D2g21`, the remaining direct arithmetic wall from `D2g22` is the stronger logarithmic one-sided microcluster branch `D2g30c/D2g30d`, and `D2g30e` records that the generic short-interval `S(T)` literature is false-for-now as a closure tool here; `D2g31` then compresses this to the genuine-packet geometry of `D2g17a/D2g18`, while `D2g19a` already kills the bounded Hermite-captured branch after reinstating the true amplitudes `q_\gamma=O(M^{-3})`; the active live address is therefore now `D2g31c`: prove extraction-to-compressed-gap, i.e. that any surviving logarithmic microcluster must keep falling into compressed-subgap descent and hence genuinely enter `D2f3`
next_verify: rg -n -F "D2g31c. Extraction-to-compressed-gap theorem target." q3.lean.aristotle/docs/insights/h1_po2_cross_sign_bulk_exactness_2026_03_16.md && rg -n -F "active next address is now `D2g31c`" q3.lean.aristotle/docs/INSIGHTS.md && rg -n -F "the active live address is therefore now `D2g31c`" q3.lean.aristotle/ACTIVE/PHASE_MONITOR.md

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
  conditional, and therefore attacks the first unresolved proof-critical gate
  back in `H1`, namely `PO2`;
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

### `PO2` — cross-sign bulk exactness

Goal:

- prove that the cross-sign filtered tail block carries no genuine bulk residue;
- keep the primary theorem target pure:
  `\mathcal D_{a,\mathrm{bulk}}^{+-}=0`;
- allow only the explicit fallback
  `\mathcal D_{a,N}^{+-}=\mathcal D_{a,\partial}^{+-}+\mathcal D_{a,\mathrm{cap}}^{+-}`;
- prepare a clean handoff to `PO3`, not a return to upper-bridge packaging.

Required output:

- one theorem-shaped bulk-vanishing statement;
- one theorem-shaped boundary/cap-only fallback statement;
- one explicit route-kill condition for a surviving unnamed bulk residue;
- one clean handoff to `PO3`.

Exact success criterion:

- the next theorem attempt is no longer “is the mixed block bulk-exact?”, but
  only `PO3`: cross-sign boundary cancellation.

Exact failure criterion:

- if `PO2` leaves a genuine unnamed cross-sign bulk residue that cannot be
  reclassified as boundary/cap, then the current `H-bridge` theorem shape is
  killed and must be written back to `ACTIVE/graphs/ROUTE_KILL_REGISTRY.md`
  before rollback to the `PSD-pd` branch.

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
- the first real proof-critical gate on the route is therefore back at `PO2`.
