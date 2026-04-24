# Phase Monitor

status: ACTIVE
phase: H1_real_proof_attack
started: 2026-03-20
mainline: T0-pd -> H-bridge -> H4 -> RH
macro_route: Door1((+,-) adapter) -> Door2((++) boundary+cap) -> Door3(compression neutrality) -> H2^f -> H3^f -> H4^f -> RH
macro_position: PO3-square.2d3 live wall / two-endpoint shifted-error control
main_kill_gate: the route fails if the real transform-side Gamma tower admits a genuine infinite-support signed self-cancellation that defeats rightmost dominance versus mirror suppression
kill_writeback: q3.lean.aristotle/ACTIVE/graphs/ROUTE_KILL_REGISTRY.md
rollback_target_if_killed: rollback to the last real branch point H-bridge vs PSD-pd in PROJECT_ORCHESTRATOR.md
current_lane: A
current_step_id: PO3-square.2d3
current_step_title: two-endpoint shifted-error control for edge-log constraints
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
next_deliverable: formulate the exact two-endpoint adaptive shifted-error theorem: after isolating an edge-log top packet and choosing endpoint-oriented adaptive shifts, prove or precisely isolate the assumptions under which the shifted remainder plus mirror is `o(1)` after normalization in every Vandermonde row
next_verify: rg -n -e "two-endpoint shifted-error" -e "Vandermonde row" -e "shifted remainder plus mirror" q3.lean.aristotle/docs/INSIGHTS.md q3.lean.aristotle/ACTIVE/PHASE_MONITOR.md && cd q3.lean.aristotle && lake build Q3.Proofs.PO3Cert

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

### `PO3-square.2d3` — two-endpoint shifted-error control for edge-log constraints

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
- the slope trichotomy is now frozen as the first exact simplification:
  pole-near and balanced-bulk are not legitimate reasons to assume a
  `1/log k` window, while the edge-log branch is the only branch where the
  local exponential packet model is honest;
- the current edge-log attack should not use fixed shifts
  `s=0,1,...,L-2`, because those rows are almost constant across a
  `1/log k` packet and can lose rank;
- the next exact theorem-shape is adaptive:
  use the shifted identity
  `A_{k+s}(x)=A_k(x)∏_{j=k+1}^{k+s}(x-(N+j))^{-1}` and the future-slope
  `μ_k(s;ξ)=∑_{j=k+1}^{k+s}(ξ-(N+j))^{-1}`;
  choose shifts `s_{k,p}` so that `μ_k(s_{k,p};ξ_k)/Λ_k(ξ_k)→p`;
  after edge-log rescaling `x_{k,i}=ξ_k+t_i/Λ_k(ξ_k)+o(1/log k)`,
  the normalized rows should converge to `exp(-p t_i)`;
- this limiting rectangular Vandermonde block has rank `L-1` on compact
  separated `t_i` configurations, so if the shifted remainder plus mirror is
  `o(1)` in those rows, the packet is forced into the exponential
  finite-difference/Hermite line;
- self-check correction: upper-end shifts alone are not symmetric enough.
  In interval notation `A_{L,U}(x)=∏_{j=L}^{U}(x-j)^{-1}`, the edge-log slope
  comes from the long endpoint side.  A left-edge packet can be tested by
  upper-end truncations/shifts, but a right-edge packet needs lower-end
  shifts, i.e. variation of the base `N`;
- the immediate proof obligation is therefore quantifier-level:
  confirm that the gamma wall produced by tail-zero is available for variable
  base `N` so that both endpoints can be shifted.  If `N` is frozen, the
  right-edge edge-log orientation is a new hard blocker and must be killed
  separately before residue-incompatibility can finish the wall.

Required output:

- one exact theorem-shape feeding
  `PO3SquareTransformPacketCertificate` on the real `A_k` side, now using the
  endpoint-oriented adaptive-shift constraint matrix in the edge-log branch,
  or one explicitly isolated obstruction saying that the available wall
  equations do not provide the lower-end shifts needed for right-edge packets;
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

## Result (2026-04-24) — base monotonicity bridge closed

- `Q3/Proofs/HBridge_PO3_Shell.lean` now exports the monotonicity bridge
  needed by the shift-orientation audit:
  `po3_tail_zero_mono`, `po3_square_tail_zero_mono`,
  `po3_bilateral_integer_tail_zero_mono`, and `po3_square2d1_target_mono`;
- therefore tail-zero after `N` gives the same strict-tail conclusion after
  every later base `N' ≥ N`, including the square and transform-side targets;
- this closes the quantifier-level concern about lower-end rebasing for the
  right-edge edge-log branch.  The live blocker is now analytic:
  prove normalized two-endpoint shifted-error control for the adaptive
  Vandermonde rows, or record the precise obstruction if the real wall identity
  does not provide it.

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
