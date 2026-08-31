# PROJECT ORCHESTRATOR — Q3

Updated: 2026-08-06

## Role

This file records stable architecture, gate meaning, route rank, and major
decisions. It is not a task queue, current monitor, bus, or proof verdict.

## Authority and precedence

If files disagree:

1. platform safety, explicit operational instruction, and
   `docs/CODEX_CONTROL.md`;
2. task-local physical state: goal/answer, live bus, execution JSON, active
   monitor, source and production build;
3. this orchestrator for stable architecture and gate meaning;
4. `docs/PAPER_MAINLINE_TRACKER.md` for manuscript typing and theorem map;
5. generated views, `docs/INSIGHTS.md`, dashboards and archives.

`IMPLEMENTATION_PLAN.md` is a frozen historical snapshot. It selects no work.

## Public mainline

`T0-pd -> H-bridge -> H4 -> RH`

- `T0-pd`: Guinand–Weil crosswalk on the corrected positive-definite cone
  `W_K^pd / W^pd`.
- `H-bridge`: Suzuki/Yoshida generalized form-pair bridge
  `H1^f -> H2^f -> H3^f -> H4^f`.
- `H4`: Suzuki Theorem 1.4 endpoint
  `0 ∉ sigma_p(G_g[a])` for every `a > 0`.

The broad cone `W_K / W` is background only. The compact `S1/S2/S3/S4`
package is diagnostic only. Neither is a public RH contract.

Fallback corrected-cone route:

`A1-pd -> packet-Rayleigh-pd -> PSD-pd -> A2-pd -> LF-pd -> G6`

It remains a fallback, not a second claim of completion.

## Current operational selector

<!-- PROJECT_STATE:START -->
<!-- project_state_sha256: e7d259915d2f200c0693e2d2907ddfe639e0930c2b73fa68f95434677698f020 -->
Project-level current status is generated from
`orchestrator/state/PROJECT_STATE.json`.
Human views: `docs/generated/PROJECT_STATUS.md` and
`docs/generated/WORK_QUEUE.md`.
Current projection: RH proof `NO`; Route B `CHALLENGER / NOT_RH`; goal `058`.
<!-- PROJECT_STATE:END -->

No generic monitor selects work automatically:

| Surface | State | Selection rule |
| --- | --- | --- |
| `ACTIVE/PHASE_MONITOR.md` | `PARKED_CLOSED` | only an explicit H1/PO3/H-bridge request |
| `ACTIVE/PSD_STEP33_MONITOR.md` | `DORMANT_2026-06-25` | only an explicit Step33 request |
| `ACTIVE/SPRINT_MONITOR.md` | `DONE_CLOSED` | historical only |
| `IMPLEMENTATION_PLAN.md` | frozen | never selects work |

The live task selector is `SESSION_ENTRY.md` plus physical task state.

## Route B challenger overlay

Route B is permanently scoped here as:

```text
CHALLENGER / NOT_RH
```

It does not replace the public mainline, prove RH, or authorize promotion.
Its current step is never copied from a monitor. Read, in order:

1. `ACTIVE/requests/routeB_twolevel_spectral_ladder/ROUTE_B_EXECUTION_STATE.json`;
2. `ACTIVE/requests/routeB_twolevel_spectral_ladder/ROUTE_B_EXECUTION_CONTROL.md`;
3. `docs/routeB_bus/BUS_PROTOCOL.md` and physical `docs/routeB_bus/`;
4. `routeb_status.py --check`.

The bounded generated block above supplies the current physical-goal projection.
Stable restrictions remain `BUS_010: VOID`, `GOAL_055: HOLD`, G2/CCM frozen,
and no Route B promotion or RH claim.

## Gate table

| Gate | Meaning | Current architectural state |
| --- | --- | --- |
| `T0`, `T0.1`, `T0-pd` | Weil crosswalk and corrected target cone | done; normalization locked |
| `A1-pd` | density of autocorrelation packets in `W_K^pd` | frozen theorem block |
| `packet-Rayleigh-pd` | exact finite Toeplitz quadratic-form identity | frozen theorem block |
| `S-pd` | scalar compact target `W_K(u) >= 0` | rejected as public route; diagnostic only |
| `A3-pd` | uniform packet-symbol floor on a dense family | rejected theorem shape |
| `PSD-pd` | PSD of the packet kernel on a dense compatible subspace | fallback; operationally dormant |
| `H-bridge` | filtered generalized form-pair bridge | canonical mainline; operationally parked |
| `H4` | Suzuki/Yoshida endpoint | conditional on honest H-bridge closure |
| `A2-pd` | corrected-cone continuity | inherited input |
| `LF-pd` | inductive-limit lift | blocked on local positivity |
| `G6` | Weil linkage to RH | frozen; no claim |

## Compiled-route honesty

The compiled export

```text
Q3.Main -> Q3.RH_of_shifted_atom_route -> PaperMainlineAtomRoute
        -> CompatibilityReduction -> Q_nonneg_t_critical
```

preserves useful theorem payloads but remains a background broad-cone export.
A green build, an archive, a dashboard, numeric evidence, or generated Lean is
not a semantic proof verdict. Inspect theorem statements, holes, axioms,
dependencies and the production-toolchain build.

## Decision ledger

- 2026-03-06: compiled narrative reset from legacy `tau=0` to the shifted-atom
  route; legacy status narratives became reference-only.
- 2026-03-07: `T0.1` closed with `pivot required`; the public target moved from
  the broad cone to the positive-definite/autocorrelation cone.
- 2026-03-07: naive same-family and uniform-floor shapes were rejected; exact
  packet-Rayleigh survived and `PSD-pd` became the honest fallback.
- 2026-03-08: the scalar compact route was rejected as a public mainline and
  retained only as diagnostic reduction.
- 2026-03-08: Suzuki/Yoshida generalized form-pair work became the canonical
  H-bridge architecture; raw exact intertwining was rejected in favour of a
  filtered defect-aware theorem shape.
- 2026-05-27: the H1/PO3 monitor was parked; it no longer self-selects work.
- 2026-06-25: PSD Step33 became dormant; its entry-hbox state is preserved for
  explicit resumption only.
- 2026-07-10: Route B was added as a separate challenger with physical bus and
  request-local execution state; it did not change the public mainline.
- 2026-07-12 through 2026-08-06: Route B accumulated verified local Lean and
  certificate payloads under `CHALLENGER / NOT_RH`; those results do not imply
  route promotion.
- 2026-08-05: G2/CCM reached a source-data boundary; `GOAL_055` remains `HOLD`
  and its draft stays outside the live bus.
- 2026-08-06: `docs/CODEX_CONTROL.md`, Spine, `knowledge.db`, observability and
  one-phase Proshka governance became the active control/memory contour.
- 2026-08-06: Goal 056 family `056..056u` closed its finite projective,
  log-window, Hilbert-basis and physical Fourier-energy subchain; the next
  Unified Chain program remains pending delegated strategic review.

## Route death, closeout and owner boundary

- A killed theorem shape is written to the canonical kill/knowledge contour;
  reopen it only with a new explicit obstruction-killer.
- Route B closeout writes `SEARCH_FLAGS`, verdict/stop-code, arsenal line and
  required autopsy; `ROUTE_B_STATE.md` is updated last.
- Codex and Proshka decide all mathematical strategy outside the sole owner
  boundary `PX_RH_CLAIM`.
- This file never authorizes a promotion or an RH claim.

The removed March frontier, milestone and blocker prose is preserved at
`docs/archive/PROJECT_ORCHESTRATOR_MARCH_SNAPSHOT_2026-03-08.md`.
