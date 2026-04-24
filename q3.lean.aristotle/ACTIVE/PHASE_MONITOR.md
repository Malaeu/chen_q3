# Phase Monitor

status: ACTIVE
phase: H1_real_proof_attack
started: 2026-03-20
mainline: T0-pd -> H-bridge -> H4 -> RH
macro_route: Door1((+,-) adapter) -> Door2((++) boundary+cap) -> Door3(compression neutrality) -> H2^f -> H3^f -> H4^f -> RH
macro_position: PO3-square.2d3 live wall / reciprocal-product slope trichotomy
main_kill_gate: the route fails if the real transform-side Gamma tower admits a genuine infinite-support signed self-cancellation that defeats rightmost dominance versus mirror suppression
kill_writeback: q3.lean.aristotle/ACTIVE/graphs/ROUTE_KILL_REGISTRY.md
rollback_target_if_killed: rollback to the last real branch point H-bridge vs PSD-pd in PROJECT_ORCHESTRATOR.md
current_lane: A
current_step_id: PO3-square.2d3
current_step_title: reciprocal-product slope trichotomy
current_owner: local-agent
current_artifact: Q3/Proofs/PO3Cert/PO3SquareSignedDominanceCertificate_2026_04_21.lean
worker_protocol: q3.lean.aristotle/ACTIVE/AGENT_PROTOCOL.md
worker_request: q3.lean.aristotle/ACTIVE/requests/proshka_h1_po3_cross_sign_boundary_2026_03_16/node.md
worker_report: q3.lean.aristotle/ACTIVE/requests/proshka_h1_po3_cross_sign_boundary_2026_03_16/report.md
last_completed_phase: H4_suzuki_endpoint_attack
last_completed_artifact: docs/insights/h4_suzuki_endpoint_to_rh_2026_03_20.md
last_completed_commit: 83e973ac
last_completed_step_id: PO2
last_completed_step_artifact: docs/insights/h1_po2_cross_sign_bulk_exactness_2026_03_16.md
last_completed_step_commit: 414464f3
next_deliverable: the transform-side landing surface, exact Gamma-to-product bridge, and finite packet avatar are frozen in Lean: `Q3/Proofs/PO3Cert/PO3SquareSignedDominanceCertificate_2026_04_21.lean` names `po3_gamma_profile`, `po3_gamma_profile_eq_prod`, `po3_gamma_packet`, and `po3_gamma_packet_eq_sum_prod`; the next real attack is now the slope trichotomy: derive `Λ_k(ξ)=ψ(r+θ)-ψ(k-r+2-θ)+π cot(πθ)` for `ξ=N+r+θ`, split near-maximizers into pole-near, edge-log, and balanced-bulk, and only allow the `1/log k` local exponential packet after pole-near and balanced-bulk are killed
next_verify: rg -n -F "PO3-square.2d3.slope-trichotomy" IMPLEMENTATION_PLAN.md && rg -n -F "po3_gamma_packet_eq_sum_prod" q3.lean.aristotle/Q3/Proofs/PO3Cert/PO3SquareSignedDominanceCertificate_2026_04_21.lean && rg -n -e "slope trichotomy" -e "pole-near" -e "edge-log" -e "balanced-bulk" q3.lean.aristotle/docs/INSIGHTS.md q3.lean.aristotle/ACTIVE/PHASE_MONITOR.md

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
  conditional, and therefore uses `PO3` as the first unresolved lower-shell
  proof packet back in `H1`;
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

### `PO3-square.2d3` — reciprocal-product slope trichotomy

Goal:

- keep the lower-shell feeder
  `PO3-shell.5/.6 -> PO3a-A2-real -> PO3a.4-real -> PO3-rig.1b.cert-real -> PO3-tail.1-real -> PO3-square.2d0a/.1/.2`
  frozen and do not reopen it;
- use the already-frozen shell landing surface in
  `Q3/Proofs/HBridge_PO3_Shell.lean`
  and the new `PO3Cert` feeder
  `PO3SquareDominantPacketCertificate`
  as fixed interfaces, not as new mathematical work;
- treat the formula-localization pass and the transform-side landing surface as
  closed:
  `Y_a = {x_γ, x_γ - 1}` is already pinned to the old `PO2` note,
  the live `A_k/B_k` route language is already pinned to the `PO3` ladder,
  and the Gamma-profile ancestor
  `u_k(x) = (-1)^k Γ(N+1-x) / Γ(k+N+1-x)` is already pinned in
  `docs/INSIGHTS.md`,
  while the Lean packet
  `PO3SquareTransformPacketCertificate`
  already names the real `A_k`, `B_k`, and `Y_a` data expected by the future
  proof;
- do not add more packet plumbing until the real formula bridge exists:
  the current hard blocker is that the repo still lacks one exact theorem-shape
  rewriting the actual transform-side `A_k` tower into
  `dominantPacket + remainder` in the frozen `po3_gamma_packet` language;
- the first honest simplification of that blocker is now also clear:
  the naive phrase “`1/log k`-scale local exponential rigidity” is only a
  heuristic shortcut; the exact local model must come from the reciprocal-
  product avatar itself, whose log-slope at a moving top point `ξ` is
  `Λ_k(ξ)=∑_{j=1}^{k+1}(ξ-(N+j))^{-1}` (equivalently a digamma-difference),
  so the natural window width is `1/|Λ_k(ξ)|`, not automatically `1/log k`;
- the exact slope decomposition is now the next object to freeze:
  for `ξ=N+r+θ`, `0<θ<1`,
  `Λ_k(ξ)=ψ(r+θ)-ψ(k-r+2-θ)+π cot(πθ)`;
  this gives three regimes:
  pole-near when `θ` is close to `0` or `1`, edge-log when one side of the
  pole block is short and the other is length `~k`, and balanced-bulk when both
  sides are length `~k`;
- attack the only live burden directly:
  first freeze this trichotomy, then kill pole-near and balanced-bulk before
  using the edge-log `1/log k` packet model.

Required output:

- one exact theorem-shape feeding
  `PO3SquareTransformPacketCertificate` on the real `A_k` side, beginning with
  the slope trichotomy of the reciprocal-product tower, or one explicitly
  isolated obstruction saying that the current repo formulas do not yet provide
  such a simplification;
- one exact pointer from that theorem-shape or obstruction back into the
  already-frozen transform-side landing surface
  `PO3SquareTransformPacketCertificate`;
- one route-kill criterion if the actual tower admits genuine infinite-support
  signed self-cancellation that defeats rightmost dominance.

Exact success criterion:

- the next theorem attempt is one honest exact split of the real `A_k` tower
  feeding the transform-side certificate landing surface, or one explicit
  obstruction that honestly blocks this route shape.

Exact failure criterion:

- if the actual transform-side formulas cannot be reconciled with the frozen
  dominant-packet certificate shape, record that incompatibility explicitly
  rather than reopening lower-shell architecture.

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
- the first real proof-critical gate on the route is still inside `PO3`,
  but its live mathematical point is now much narrower:
  `PO3-square.2d3`, the slope-regime analysis needed before the actual
  transform-side `A_k` tower can feed the frozen dominant-packet certificate
  language.
