# Phase Monitor

status: ACTIVE
phase: H1_real_proof_attack
started: 2026-03-20
mainline: T0-pd -> H-bridge -> H4 -> RH
macro_route: Door1((+,-) adapter) -> Door2((++) boundary+cap) -> Door3(compression neutrality) -> H2^f -> H3^f -> H4^f -> RH
macro_position: PO3-square.2d3 live wall / stable projection conditioning for threshold packets
main_kill_gate: the route fails if the real transform-side Gamma tower admits a genuine infinite-support signed self-cancellation that defeats rightmost dominance versus mirror suppression
kill_writeback: q3.lean.aristotle/ACTIVE/graphs/ROUTE_KILL_REGISTRY.md
rollback_target_if_killed: rollback to the last real branch point H-bridge vs PSD-pd in PROJECT_ORCHESTRATOR.md
current_lane: A
current_step_id: PO3-square.2d3
current_step_title: prove endpoint-row stable projection or route-kill
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
next_deliverable: prove `EndpointRowStableProjectionOrRouteKill`: a stable projection/conditioning estimate `C_k * ||epsilon_k|| -> 0` for the threshold packet, or route-kill via growing packets, wrong kernel dimension, or ill-conditioned/confluent clusters
next_verify: rg -n -e "po3_variable_comparable_packet_capture_of_stable_projection" -e "EndpointRowStableProjectionOrRouteKill" -e "stable projection" -e "sigma_min" q3.lean.aristotle/Q3/Proofs/PO3Cert/PO3SquareSignedDominanceCertificate_2026_04_21.lean q3.lean.aristotle/docs/INSIGHTS.md q3.lean.aristotle/docs/insights/h1_po3_square_2d3_variable_packet_capture_2026_04_25.md q3.lean.aristotle/ACTIVE/PHASE_MONITOR.md q3.lean.aristotle/ACTIVE/graphs/ROUTE_KILL_REGISTRY.md IMPLEMENTATION_PLAN.md && cd q3.lean.aristotle && lake build Q3.Proofs.PO3Cert

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

### `PO3-square.2d3` — stable projection conditioning for threshold packets

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

## Result (2026-04-24) — two-endpoint shifted-error target pinned

- the next analytic theorem is now stated as one normalized row-error problem,
  not as another packet-capture slogan;
- for each endpoint-adaptive row `rho`, the wall is split as
  `top packet = mirror_rho - exterior remainder_rho` and normalized by
  `M_k m_rho(xi_k)`;
- the required input for adaptive Vandermonde capture is precisely
  `epsilon_rho -> 0`, i.e. both
  `RemainderRowSmall` and `MirrorRowSmall` in every selected row;
- if the same top packet is not stable under these rows, or if either row
  error estimate fails, this is the first real obstruction and must be written
  to the route-kill registry before any residue/Hermite-incompatibility claim.

## Result (2026-04-24) — `MirrorRowSmall` requires absolute row-mass control

- the first row-error audit shows that shell-level `mirror_decay` is not
  enough after normalization by the moving packet scale
  `M_k m_rho(xi_k)`;
- pointwise mirror suppression has the exact ratio
  `|B_I(x)|/|A_I(x)|=prod_{j in I}|x-j|/|x+j|`, but on unbounded support this
  only closes the mirror row after a near/far split and absolute exterior
  `A`-mass control;
- therefore the next theorem is stronger and cleaner:
  prove endpoint-row `AbsoluteRowMassControl` for the exterior main mass plus
  a far mirror-tail estimate.  This single input gives `MirrorRowSmall`,
  signed `RemainderRowSmall`, and top-packet stability for the adaptive rows.

## Result (2026-04-25) — Oracle review narrows absolute row-mass to packet isolation

- `RH_März_2026` agrees with the mirror-row audit but rejects the unconditional
  implication from only `Y_a={x_gamma,x_gamma-1}` and
  `|c_gamma|=O(gamma^-3)`;
- the next proof-facing theorem is
  `EndpointRowAbsoluteMassControl_from_packet_isolation`: choose an exhaustive
  row-effective region `E_{k,rho}`, prove exterior absolute `A`-mass inside
  `E_{k,rho}\setminus P_k`, prove the `A`-ineffective tail, and prove the far
  mirror tail;
- the exact route fork is now:
  prove packet isolation, or exhibit a bounded-local-coordinate exterior
  competitor `y_k=xi_k+(t+o(1))/Lambda_k(xi_k)` whose endpoint-row contribution
  remains comparable to `M_k|m_rho(xi_k)|`;
- until this fork is resolved, Hermite/Vandermonde residue capture cannot be
  used as a closure argument.

## Result (2026-04-25) — log-loss mirror split replaces unconditional absolute mass

- the sharper audit says `AbsoluteRowMassControl = o(D_{k,rho})` is still too
  strong from the allowed inputs alone: zero counting gives at most
  `O(log xi_k)` local row-mass loss and no spacing on the endpoint-row scale;
- the mirror side should now be attacked by
  `EndpointRowLogMassMirrorControl`: combine the log-loss absolute row-mass
  estimate with the stronger pointwise condition
  `eta_{k,rho} log(2+xi_k)->0`, plus the far mirror tail;
- the main `A`-remainder is a separate blocker named `RowClusterExhaustion`:
  every row-scale support point with comparable normalized contribution must
  be included in `P_k`, or its aggregate contribution must be `o(D_{k,rho})`;
- the route-kill criterion is now concrete: an omitted
  bounded-local-coordinate exterior competitor, or an unbounded number of
  comparable row-scale support points, invalidates the fixed finite
  Vandermonde packet route at this node.

## Result (2026-04-25) — log-loss mirror consumer frozen in Lean

- `Q3/Proofs/PO3Cert/PO3SquareSignedDominanceCertificate_2026_04_21.lean`
  now contains the abstract consumer
  `po3_endpoint_row_log_mass_mirror_control`;
- the theorem says: if a mirror row is bounded by
  `eta * nearAMass + farMirror`, the near `A`-mass has a log-loss bound
  against the packet scale, `eta * logLoss -> 0`, and the far mirror tail is
  small relative to the same scale, then the mirror row is small relative to
  the packet scale;
- this closes only the shell part of `EndpointRowLogMassMirrorControl`.  The
  remaining analytic blocker is `RowClusterExhaustion`, needed for the main
  `A`-remainder before any Hermite/Vandermonde capture can be used.

## Result (2026-04-25) — threshold packet replaces fixed cluster exhaustion

- the latest `RH_Maerz_2026` review rejects fixed finite
  `RowClusterExhaustion` as an unconditional theorem shape: zero-counting
  gives `O(log xi_k)` local density, not a fixed finite exhaustive packet;
- the corrected target is `ThresholdExhaustivePacketRowError`: choose
  `delta_k` with `delta_k log(2+xi_k)->0` and define `P_k(delta_k)` to contain
  every row-effective point whose normalized endpoint-row contribution is at
  least `delta_k` of the row scale;
- the omitted row-effective mass is then `o(D_{k,rho})` by counting:
  each omitted point is `< delta_k D_{k,rho}` and there are
  `O(log(2+xi_k))` of them;
- after row errors are closed, the remaining live blocker is
  `VariableComparablePacketCapture`: if the threshold packet is bounded and
  separated, use the existing finite Vandermonde/Hermite branch; if it grows
  or becomes ill-conditioned, require a singular-value estimate or record a
  route kill before residue/Hermite incompatibility is invoked.

## Result (2026-04-25) — variable packet capture reduced to stable projection

- the next `RH_Maerz_2026` review gives the clean finite-dimensional consumer:
  if endpoint-row equations have form `V_k q_k = epsilon_k` and there is a
  projection onto the expected Vandermonde/Hermite kernel satisfying
  `||q - Proj q|| <= C_k ||V_k q||`, then
  `dist(q_k, ker V_k) <= C_k ||epsilon_k||`;
- this is now frozen in Lean as
  `po3_variable_comparable_packet_capture_of_stable_projection` in
  `Q3/Proofs/PO3Cert/PO3SquareSignedDominanceCertificate_2026_04_21.lean`;
- the active analytic blocker is therefore not another row-error shell, but
  `EndpointRowStableProjectionOrRouteKill`: prove
  `C_k ||epsilon_k|| -> 0` for the threshold packet, or record route-kill by
  growing packet size, wrong kernel dimension, or ill-conditioned/confluent
  clusters;
- remember the norm correction: if only row sup-error is controlled and there
  are `r_k` rows, then `||epsilon_k||_2 <= sqrt(r_k) max_p |epsilon_{k,p}|`.

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
