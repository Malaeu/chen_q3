# Proshka Context Pack
Generated: 2026-08-14T02:01:16
Repo: /Users/emalam/GitHub/rh_lean_01_2026
Branch: rh_clean
HEAD: 90bd221a
Range: 937b702f..90bd221a

## Working tree
```text
## rh_clean...origin/rh_clean
```

## Commit list (oneline)
```text
90bd221a [MacOS][rh_clean][Control] Record current Spine source
2ef549b7 [MacOS][rh_clean][Control] Refresh Spine after Goal058 G3 step
46bca13c [MacOS][rh_clean][Goal058] Advance G3 to prolate rate floor
0fb4023a [MacOS][rh_clean][Goal058] Refresh RouteB inventory
a64a9ea3 [MacOS][rh_clean][Goal058] Prove explicit CCM limit inversion
9b384948 [MacOS][rh_clean][Control] Activate Goal058 G3 task
c4431209 [MacOS][rh_clean][Goal058] Select explicit G3 limit packet
```

## Range diff summary
```text
SESSION_PROTOKOLL_2026-08-13.md                    |  23 +
 docs/Codex/CURRENT.md                              |   8 +-
 ..._2026-08-14_goal058_g3_explicit_limit_packet.md |  41 ++
 ...ASK_2026-08-14_goal058_g3_prolate_rate_floor.md |  50 +++
 docs/Progress_Log.md                               |  41 ++
 docs/cartographer/inventory_RouteB.json            | 394 +++++++++++++++-
 orchestrator/state/SPINE_STATE.json                | 152 +++----
 orchestrator/state/SPINE_VIEW.md                   |   6 +-
 ...CM_LIMIT_FOURIER_POISSON_CLOSEOUT_2026-08-14.md | 127 ++++++
 .../IMPLEMENTATION_PLAN.md                         |  27 +-
 .../ROUTE_B_EXECUTION_STATE.json                   |  16 +-
 .../ROUTE_B_STATE.md                               |  23 +-
 .../loop_state.json                                |   6 +-
 .../RouteB/D0PstarExplicitCCMLimitFourier.lean     | 500 +++++++++++++++++++++
 q3.lean.aristotle/aristotle_db/knowledge.db        | Bin 12414976 -> 12427264 bytes
 15 files changed, 1292 insertions(+), 122 deletions(-)
```

## Per-commit stats
```text
90bd221a [MacOS][rh_clean][Control] Record current Spine source
 orchestrator/state/SPINE_STATE.json | 2 +-
 1 file changed, 1 insertion(+), 1 deletion(-)
```
```text
2ef549b7 [MacOS][rh_clean][Control] Refresh Spine after Goal058 G3 step
 docs/Codex/CURRENT.md                       |   4 +-
 orchestrator/state/SPINE_STATE.json         | 172 ++++++++++++++--------------
 orchestrator/state/SPINE_VIEW.md            |   6 +-
 q3.lean.aristotle/aristotle_db/knowledge.db | Bin 12427264 -> 12427264 bytes
 4 files changed, 91 insertions(+), 91 deletions(-)
```
```text
46bca13c [MacOS][rh_clean][Goal058] Advance G3 to prolate rate floor
 docs/Codex/CURRENT.md                              |  6 +--
 ...ASK_2026-08-14_goal058_g3_prolate_rate_floor.md | 50 ++++++++++++++++++++++
 .../IMPLEMENTATION_PLAN.md                         | 25 ++++++-----
 .../ROUTE_B_EXECUTION_STATE.json                   | 14 +++---
 .../ROUTE_B_STATE.md                               | 21 ++++-----
 .../loop_state.json                                |  6 +--
 6 files changed, 88 insertions(+), 34 deletions(-)
```
```text
0fb4023a [MacOS][rh_clean][Goal058] Refresh RouteB inventory
 docs/cartographer/inventory_RouteB.json | 394 +++++++++++++++++++++++++++++++-
 1 file changed, 389 insertions(+), 5 deletions(-)
```
```text
a64a9ea3 [MacOS][rh_clean][Goal058] Prove explicit CCM limit inversion
 SESSION_PROTOKOLL_2026-08-13.md                    |  23 +
 docs/Progress_Log.md                               |  41 ++
 ...CM_LIMIT_FOURIER_POISSON_CLOSEOUT_2026-08-14.md | 127 ++++++
 .../RouteB/D0PstarExplicitCCMLimitFourier.lean     | 500 +++++++++++++++++++++
 q3.lean.aristotle/aristotle_db/knowledge.db        | Bin 12414976 -> 12427264 bytes
 5 files changed, 691 insertions(+)
```
```text
9b384948 [MacOS][rh_clean][Control] Activate Goal058 G3 task
 docs/Codex/CURRENT.md               |   8 +--
 orchestrator/state/SPINE_STATE.json | 136 ++++++++++++++++++------------------
 orchestrator/state/SPINE_VIEW.md    |   6 +-
 3 files changed, 75 insertions(+), 75 deletions(-)
```
```text
c4431209 [MacOS][rh_clean][Goal058] Select explicit G3 limit packet
 ..._2026-08-14_goal058_g3_explicit_limit_packet.md | 41 ++++++++++++++++++++++
 .../IMPLEMENTATION_PLAN.md                         | 24 ++++++-------
 .../ROUTE_B_EXECUTION_STATE.json                   | 16 ++++-----
 .../ROUTE_B_STATE.md                               | 22 ++++++------
 .../loop_state.json                                |  6 ++--
 5 files changed, 75 insertions(+), 34 deletions(-)
```

## File snapshots

### full/q3.lean.aristotle/PROJECT_ORCHESTRATOR.md
```text
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

Physical snapshot at this update:

```text
GOAL_056_PHASE4L_CLOSED_UNIFIED_CHAIN_DELEGATED_REVIEW_PENDING
BUS: closed=056..056u active=NONE next-number=057 selected-next=NONE
```

Goal 057 is not minted by this snapshot or by arithmetic. The pending standing
direction must first pass its delegated strategic-review contract. Stable
restrictions remain `BUS_010: VOID`, `GOAL_055: HOLD`, G2/CCM frozen, and no
Route B promotion or RH claim.

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
```

### full/q3.lean.aristotle/docs/INSIGHTS.md
```text
# Project Insights

Короткие записи + ссылки на подробности. Здесь держим только:
- проблему;
- как быстро ее детектить;
- ссылку на подробный разбор.

Полный список файлов: `docs/insights/INDEX.md`.

---

## Навигация (кратко)

## Synthesis (2026-08-08, in progress) -- Goal 057 B3.0G source W02 mode pairing

- The primary source defines `W_0,2`, its one-sided distribution `W_0,2#`,
  and the exact ordered mode entry in equations (3.11), (3.14), and (4.2).
- Source Lemma 4.1 identifies that entry as a rank-two matrix; its displayed
  formula matches production `ccmW02Entry` literally and with positive sign.
- Production already fixes `L = log m = 2 log sqrt(m)`, the normalized modes,
  the literal integer mode order, and the source-correlation/`ccmQKernel`
  crosswalk.
- Exact declaration search finds no production `W02` functional,
  `W02#`, endpoint moment, or independent `sourceW02ModePairing` object.
- The honest audit result is therefore a missing Lean source object, not a
  missing theorem in the paper: `SOURCE_W02_FUNCTIONAL_PRODUCTION_OBJECT_MISSING`.
- A direct alias to `ccmW02Entry` would be C10 surrogate-by-formula and is
  forbidden even though it makes the desired equality definitionally true.
- Cheapest candidate is the one-sided source integral with weight
  `exp(x/2)+exp(-x/2)` if it consumes the existing source-correlation parent;
  the more structural alternative materializes the two endpoint moments.
- B3.0G remains audit-only pending one decision in the same living Proshka
  chat.  B3.0, all ten coarse checkpoints, H4a1b, promotion, PX and RH stay open.

## Synthesis (2026-08-08, closed node) -- Goal 057 B3.0F finite archimedean sesquilinear matrix lift

- Production lifts the closed all-mode E4C identity coefficientwise over the
  literal carrier `CCMModeFinite i.N`, with `star (c j)` in the first slot and
  `d k` linear in the second.
- The official CCM source fixes this convention: the Hilbert pairing is
  antilinear in the first argument, the Weil form is obtained by polarization,
  and its finite restriction is represented by the source matrix on `V_n`.
- The one public theorem rewrites every ordered `(j,k)` entry by E4C and pulls
  the common negative sign through the finite double sum.  No matrix symmetry,
  real projection, helper definition or surrogate form premise is used.
- Exact harness-to-production materialization removed only five controls and
  the final axiom print.  Direct Lean, target/full builds, q3-check, proof DB
  1/1, 80/80 tests, strict Spine and all three SQLite checks pass.
- Nine independent plants fire under the repaired contract.  The premise-only
  and generated-PSD mutations compile but are rejected by the C10 provenance
  gate and the static dependency gate; the nonsymmetric `Fin 2` harness pins
  entry orientation.
- The global `j/k` swap is killed and not counted: dummy reindexing plus
  `ccmWREntry` symmetry makes that mutation non-discriminating.
- Boundary: B3.0F is closed but B3.0 remains open.  There is still no source
  `W02` pairing, prime pairing, complete Weil form, associated operator graph,
  checkpoint closure, H4a1b invocation, promotion, PX or RH claim.
- Next atom is audit-only:
  `GOAL057_B3_0G_SOURCE_W02_MODE_PAIRING_EQ_CCM_W02_ENTRY` with discriminator
  `B3_0G_W02_SOURCE_MODE_PAIRING_SOURCE_AUDIT`; production is not authorized.

## Synthesis (2026-08-08, closed node) -- Goal 057 B3.0E4C all-mode CCM-WR case assembly

- Exact target: prove
  `sourceArchimedeanModePairing i n r =
  -(Q3.RouteB.ccmWREntry (L_m i) n r : ℂ)` for arbitrary integer modes.
- Local semantic search confirms that the two required source-locked branches
  already exist as production theorems: the off-diagonal `_of_ne` result and
  the diagonal `_diag` result.  No third analytic supplier is missing.
- The official source itself separates `n ≠ r` and `n = r` in equations
  (2.9)--(2.10), while equation (4.4) supplies the common archimedean entry;
  therefore a literal `by_cases h : n = r` is source-faithful packaging.
- Preflight imports only the closed off-diagonal and diagonal crosswalk
  modules, introduces exactly one public theorem, no definition and no
  private helper, and proves the branches only by `subst`/the two parents.
- Production now contains exactly one theorem and the two-parent `by_cases`
  proof. Direct Lean, target/full build, q3-check, the standard axiom triple,
  proof DB 1/1, 80/80 tests, strict Spine and all three SQLite checks pass.
- Six independent plants fire. The proposed mode-order plant is correctly
  killed and not counted: `ccmWREntry_symm` makes the swapped RHS
  extensionally identical, so it cannot detect orientation loss.
- The independent C10 provenance plant is load-bearing: an all-mode premise
  can make Lean green while bypassing both source-constructed parents, and is
  therefore rejected semantically rather than reported as a proof success.
- Boundary: B3.0E4C and parent B3.0E are closed. B3.0 remains open for the
  finite coefficient-form lift, W02/prime source pairings, complete source
  Weil form and associated operator. All ten coarse checkpoints, H4a1b,
  promotion, PX and RH remain open.

## Synthesis (2026-08-08, closed node) -- Goal 057 B3.0E4B2 diagonal archimedean / CCM-WR crosswalk

- Exact target: prove the missing diagonal case
  `sourceArchimedeanModePairing i n n =
  -(Q3.RouteB.ccmWREntry (L_m i) n n : ℂ)` for every source mode.
- No new source analysis is needed.  On `0 < x <= L_m i`, twice the diagonal
  kernel-mode fiber is `ccmWRIntegrand` plus
  `2 * (1 - exp (-x)) / (exp x - exp (-x))`; beyond the support it is the
  negative tail `-2 * exp (-x) / (exp x - exp (-x))`.
- `sourceModeCosineCorrelation_control_diag_zero` fixes the bare-mode mass to
  one, while `two_mul_sourceModeCosineCorrelation_eq_ccmQKernel_or_zero`
  supplies the full diagonal compact-support profile.
- Joint absolute integrability from B3.0E2 is the sole Fubini carrier.  The
  E4A private proof helpers may be reproduced locally, but no parent module is
  refactored during the discriminator.
- The already-closed B3.0E4B1 endpoint ledger combines the finite regularizer
  and tail with `-log pi`; the remaining `-EulerGamma` and CCM-WR integral then
  give exactly the negative diagonal `ccmWREntry`.
- Mandatory controls are `n = 0`, `n = 1`, support boundary `x = L_m i`, and
  one outside-support point.  Any sign, factor-two, coercion, or endpoint-scale
  mismatch stops the node rather than changing the source convention.
- Production theorem
  `sourceArchimedeanModePairing_eq_neg_ccmWREntry_diag` is now Lean-checked,
  sorry-free and recorded as 19/19 proved declarations with the standard
  axiom triple.  The exact harness proof was retained; only four controls and
  the final axiom-print command were omitted from production.
- Proshka accepted the theorem and proof unchanged, but correctly expanded
  the audit from eight to twelve plants: joint-Fubini consumption, E4B1
  consumption, explicit real/complex coercion and generated-backend
  injection are independent proof edges.  All 12/12 mutations fired.
- Boundary: B3.0E4B2 is closed.  B3.0E remains open for one all-mode case
  assembly; the source Weil form, associated operator graph, all 10 coarse
  checkpoints, H4a1b, promotion, PX and RH remain open.

## Synthesis (2026-08-08, closed node) -- Goal 057 B3.0E4B1 diagonal endpoint ledger

- Exact target: for `0 < L`, prove the scalar identity equating the paired
  finite-region regularizer plus the convergent `Ioi L` tail with
  `-Real.log (4 * Real.pi * ((Real.exp L - 1) / (Real.exp L + 1)))`.
- The source lock is CCM arXiv:2511.22755v1, equation (4.4): this is the
  diagonal endpoint constant only, not the later mode-dependent diagonal
  pairing or an all-entry `ccmWREntry` theorem.
- Preserve the cancellation-bearing finite integrand.  On `Ioc 0 L`, rewrite
  `2 * (1 - exp (-x)) / (exp x - exp (-x))` as `2 / (exp x + 1)`; never split
  its two numerator terms near zero.
- Use the global antiderivative
  `F x = 2 * x - 2 * Real.log (Real.exp x + 1)` and the interval FTC after
  converting the `Ioc` set integral to the oriented interval integral.
- For the tail, use
  `G x = Real.log (1 - Real.exp (-2 * x))`; on `Ici L`, `G'` is exactly
  `2 * exp (-x) / (exp x - exp (-x))`, is nonnegative, and `G -> 0` at `atTop`.
- Mathlib's `integral_Ioi_of_hasDerivAt_of_nonneg'` closes the improper tail
  without separately postulating integrability; positivity follows from
  `hL`, monotonicity of `exp`, and `exp (-2*x) < 1`.
- Final algebra uses only proved positivity/nonzero facts for every
  `Real.log_mul` and `Real.log_div`.  The production theorem is
  `sourceArchimedeanDiagonalRegularizer_endpointLedger`, with exactly the
  standard axiom triple and one foundational Mathlib import.
- The final falsifier set has nine independent plants: finite and tail signs,
  both factors two, paired cancellation, common split boundary, log-ratio
  orientation, endpoint scale `4π`, and the positive-length domain.
- Reusable tooling lesson: Lean declarations may begin with several modifiers
  (`private noncomputable def`); the proof-DB parser must accept a modifier
  sequence or it silently undercounts a valid public/private surface.
- Boundary: B3.0E4B1 is closed.  B3.0E4B2, the all-mode crosswalk, source Weil
  form/operator, all 10 coarse checkpoints, H4a1b, promotion, PX and RH remain
  open.

## Synthesis (2026-08-08, in progress) -- Goal 057 B3.0E4A off-diagonal archimedean / CCM-WR crosswalk

- Exact target: for `n ≠ r`, prove
  `sourceArchimedeanModePairing i n r =
  -(Q3.RouteB.ccmWREntry (L_m i) n r : ℂ)` without touching the postponed
  diagonal endpoint constant.
- Source wiring is literal: CCM equations (2.7)--(2.10) fix the
  antilinear-first off-diagonal sine order, while equation (4.4) defines the
  archimedean entry as its endpoint constant plus the integral on `[0,L]`.
- `hnr` gives `ccmQKernel (L_m i) n r 0 = 0`; the same orthogonality kills
  the constant part of `sourceArchimedeanMultiplier` and the `exp (-x)`
  regularizer term after integration over the Fourier coordinate.
- `D0PstarSourceArchKernelModeProductL1` is the load-bearing Fubini carrier;
  a fiberwise-only exchange is forbidden.
- `D0PstarSourceModeCosineCCMQKernel` supplies twice the cosine correlation:
  it is `ccmQKernel` on `0 ≤ x ≤ L_m i` and zero for `x > L_m i`.
- Consequently the outer `-2` in the exact hyperbolic multiplier cancels the
  correlation factor `1/2`, leaving exactly the negative CCM-WR integral.
- Mandatory ordered controls are `(n,r)=(0,1)` and `(1,0)`; a sign, Fubini,
  coercion, support, or orientation mismatch stops E4A without changing the
  source object.
- Boundary: B3.0E4B, the full source Weil form, the associated operator,
  every coarse checkpoint, H4a1b, promotion, PX and RH remain open.

## Synthesis (2026-08-08, in progress) -- Goal 057 B3.0E3 source cosine-correlation preflight

- Exact target: for `0 <= x`, identify twice the conjugate-first Fourier-mode
  cosine pairing with `ccmQKernel (L_m i) n r x` on `x <= L_m i`, and with
  zero outside the log window.
- The primary CCM source fixes the compact-support zero extension, the
  antilinear-first pairing, and equations (2.7)--(2.10); these determine the
  diagonal factor `2`, the off-diagonal sine order, and the right-endpoint
  value without a convention choice.
- Mathlib's direct sesquilinear Fubini theorem is not applicable here:
  `cos * 𝓕(logWindowZeroExtendedMode i r)` need not be integrable.  Treating
  that factor as `L1` would hide the actual analytic step.
- The viable route is correlation first: express the two compactly supported
  zero-extended modes as a convolution/correlation, prove that its Fourier
  transform is the conjugate-first mode product, and use pointwise Fourier
  inversion.  The already-proved resonance-safe mode bounds supply the
  required `L1` product carrier.
- The source-side overlap integral is then elementary and source-locked:
  diagonal gives `2 * (L-x)/L * cos(2*pi*n*x/L)`; off-diagonal gives the
  ordered sine difference divided by `pi*(n-r)`.
- Five mandatory controls are preserved as separate checks: central diagonal,
  central off-diagonal, interior off-diagonal sign/order, right boundary, and
  outside-window zero.
- Planned dependencies are `D0PstarVModeFourierFormula.lean`,
  `D0PstarSourceArchKernelModeProductL1.lean`, Mathlib Fourier inversion and
  convolution, and `CCMFiniteWeilSourceMatrixN1.lean`.  If the convolution
  transform or continuity-at-evaluation carrier cannot be closed without a
  new imported theorem, the preflight must stop at that exact wall rather
  than replace the source identity by a numeric or formal surrogate.

## Synthesis (2026-08-08, in progress) -- Goal 057 B3.0E2 joint kernel-mode Fubini preflight

- Exact target: for fixed `i : PairIndex` and `n r : ℤ`, prove joint
  `Integrable` on `ℝ_t × (0,∞)_x` for the conjugate-first Fourier-mode product
  multiplied by `sourceArchimedeanRegularizedKernel t x`.
- Wiring: B3.0E1 proves every fixed-`t` kernel section is integrable on
  `Ioi 0`; B3.0B1 proves the logarithmically weighted Fourier modes belong to
  `L²`.  Mathlib's `integrable_prod_iff` reduces the new carrier to strong
  measurability, almost-everywhere section integrability, and integrability of
  the inner norm integral.
- The missing analytic atom is a cancellation-preserving estimate of the form
  `∫ x in Ioi 0, ‖sourceArchimedeanRegularizedKernel t x‖ ≤
  C * vModeLogGrowthEnvelope t`, with an absolute constant `C`.
- Planned source proof splits the paired `u = 2*x` kernel at reciprocal
  frequency and at `u = 1`: Taylor cancellation on the first interval,
  the honest `1/u` logarithm in the middle, and the existing exponential tail
  beyond one.  Splitting the two singular numerator terms is forbidden.
- If Lean yields only a polynomial-in-`t` majorant, the discriminator fails:
  the available resonance-safe mode decay does not pay that cost, and the
  route must move to a source distribution-action representation instead of
  asserting Fubini.
- Boundary: this entry authorizes only one untracked no-`sorry` preflight.
  It changes no production Lean, B3.0E crosswalk, route state, coarse ledger,
  promotion status, `PX_RH_CLAIM`, or RH status.
- The discriminator now passes without needing the provisional sharp
  logarithmic kernel-norm estimate.  The checked near bound costs only
  `sqrt |t| / sqrt x`; `x^(-1/2)` is locally integrable and the two public
  resonance-safe fixed-mode decays turn the frequency majorant into
  `(1+|t|)^(-3/2)`.
- `/tmp/Goal057B3_0E2_Scratch.lean` has 27,927 bytes, 696 lines, SHA-256
  `1ff1ef467028a6a62a9d2722c2b96e0ec6aff94366645e32bab91ff5f82f7bde`,
  zero hole tokens, and direct Lean exit `0`.
- The exact conclusion is joint `Integrable` for the conjugate-first
  kernel-mode product under
  `volume.prod (volume.restrict (Ioi 0))`.  Near and exponential-tail product
  carriers are proved separately and united without relabelling the positive
  `x` measure.
- Both public objects print only `propext`, `Classical.choice`, and
  `Quot.sound`.  This is a successful untracked preflight, not production
  authority: the exact harness returns to the unchanged Proshka chat for one
  release before any B3.0E2 production or state mutation.
- Proshka released exactly one child, and production
  `D0PstarSourceArchKernelModeProductL1.lean` now proves the exact joint
  carrier. Direct Lean, target 7,762-job build, full 7,817-job build,
  `q3_check`, 80/80 tests, 24/24 proof-DB declarations, 7/7 plants, strict
  Spine and all three SQLite checks pass.
- The production theorem remains fixed-mode and carrier-only: it proves no
  public swapped-integral equality, `ccmQKernel` correlation, one-sided
  half-factor, `ccmWREntry` crosswalk, source Weil form or operator graph.
  B3.0E and the ten coarse checkpoints therefore remain open.
- Recursive provenance corrects one overstrong preflight sentence: the new
  module adds no generated backend, but inherits the tracked and hole-free
  `aristotle_output.d1524982_aristotle` through the already-closed B3.0E1
  digamma chain. No new Step33/hbox/payload/Aristotle dependency was added.
- The exact next atom is
  `GOAL057_B3_0E3_ZERO_EXTENDED_MODE_COSINE_CORRELATION_EQ_CCM_QKERNEL`;
  only its untracked no-`sorry` discriminator is authorized before the next
  same-chat release.

## Synthesis (2026-08-08, source-audit wall; B3.0E1 closed) -- Goal 057 B3.0E CCM-WR sign/normalization crosswalk

- Target: identify the proved B3.0D cycles-frequency pairing with the literal
  CCM archimedean matrix entry, without guessing its sign, `2*pi` scale, slot
  orientation, or real/complex coercion.
- The primary CCM source fixes the angular transform and
  `W_R = -W_infinity`, while the full Weil form contains `-W_R`; its frequency
  contribution is `integral |Fhat(s)|^2 * 2*theta'(s)/(2*pi) ds`.
- The production multiplier satisfies
  `sourceArchimedeanMultiplier(t) = -log pi + Re digamma(1/4+i*pi*t)
  = 2*theta'(2*pi*t)`.  Under `s = 2*pi*t`, Mathlib's cycles-frequency
  transform absorbs the Jacobian and introduces no residual `2*pi` factor.
- Therefore the source audit predicts the exact ordered crosswalk
  `sourceArchimedeanModePairing i n r =
  -(ccmWREntry (L_m i) n r : C)`: first index antilinear, second linear,
  no transpose and no extra conjugation.  This remains an audited target, not
  a Lean theorem.
- Four local semantic queries and exact identifier search found no existing
  theorem connecting `sourceArchimedeanMultiplier` or the B3.0D pairing to
  `ccmWREntry`.  Mathlib supplies Fourier integrals and sesquilinear exchange,
  but no ready theorem equating the digamma multiplier integral to CCM's
  regularized one-sided `W_R` formula.
- The existing `Q3.DigammaRemainder` proves a Stieltjes representation, but it
  is not the hyperbolic-kernel representation needed by CCM equation (4.4).
  A direct one-shot equality would therefore hide a substantial analytic
  Fubini/distribution bridge.
- Recommended next atom for delegated review: preflight the smallest source
  theorem converting the digamma multiplier to the one-sided CCM kernel,
  with explicit integrability/Fubini obligations; only then wrap the fixed
  modes into the displayed negative-`ccmWREntry` identity.
- Boundary: no crosswalk, CCM sign theorem, full Weil decomposition, operator
  graph, uniform/cofinal control, coarse-checkpoint closure, promotion, PX, or
  RH is claimed until the bridge compiles in Lean.
- Proshka independently confirmed the final minus sign, cancellation of the
  angular/cycles `2*pi` scale, and the source `n,r` slot orientation, but
  returned
  `WALL_GOAL057_B3_0E_SOURCE_ARCH_CCM_WR_BRIDGE_MISSING`: the requested
  final equality is not yet a Lean theorem and no production child is
  released.
- The first missing formal theorem is now exact:
  `sourceArchimedeanMultiplier` equals `-log pi - gamma` minus twice the
  integral of the paired regularized hyperbolic kernel on `Ioi 0`.
  Splitting its two numerator terms near `x=0` is forbidden because each
  separate term has a nonintegrable `1/x` singularity.
- The preferred repair route starts from the already formalized digamma
  series, converts paired reciprocal differences to Laplace integrals, and
  sums the geometric series without destroying cancellation.  The stronger
  distribution-action route remains the fallback if the cancellation-aware
  scalar proof fails.
- Next and only authorized discriminator:
  `B3_0E1_SCALAR_HYPERBOLIC_IDENTITY_NO_SORRY_PREFLIGHT`, performed in one
  untracked harness.  Pass returns to the same chat for one release; failure
  retains the wall.  The coarse ledger remains exactly 0/10.
- The discriminator now passes.  `/tmp/Goal057B3_0E1_Scratch.lean` has
  23,556 bytes, 597 lines, SHA-256
  `49425edef5c5b972d93f4f1c9f84877b4f9c23063fe736b06856cc0bae16af47`,
  zero hole tokens, and direct Lean exit `0` with the sole explicit import
  `D0PstarExactArchSymbolLogDomination`.
- The harness proves the exact proposed kernel, its `IntegrableOn (Ioi 0)`
  certificate, and the multiplier identity.  The integral/tsum exchange uses
  `hasSum_integral_of_dominated_convergence`; the norm series sums exactly to
  the norm of the paired quotient already proved integrable, so endpoint
  cancellation is never split.
- `#print axioms` for all three public objects reports only `propext`,
  `Classical.choice`, and `Quot.sound`.  This is a successful untracked
  preflight, not production authority: the exact harness is returned to the
  same Proshka chat for one operational release before creating the proposed
  production file.  The coarse ledger remains 0/10.
- Proshka released exactly that harness with no mathematical proof change.
  Production `D0PstarSourceArchHyperbolicKernel.lean` has SHA-256
  `4fb022d88ded0d0afecbab8767f0b07642c7a0a97e1108736682687198e7a25d`;
  direct Lean, target 7,761-job build, full 7,817-job build, `q3_check`,
  80/80 tests, 36/36 proof-DB declarations, 6/6 plants, strict Spine, and all
  three SQLite integrity checks pass.
- Exact closed class: scalar source multiplier equals `-log pi - gamma` minus
  twice the integral of the paired regularized hyperbolic kernel.  The paired
  zero-endpoint cancellation, dominated integral/series exchange, and exact
  `u = 2*x` minus/Jacobian are load-bearing and retained.
- B3.0E1 is closed, but B3.0E remains open.  The next missing carrier is joint
  absolute integrability of the regularized kernel times the fixed mode
  product, followed by mode correlation and one-sided endpoint assembly.
  Therefore no `ccmWREntry` crosswalk, source Weil form, operator graph,
  checkpoint closure, H4a1b, promotion, PX, or RH follows.  Ledger stays 0/10.

## Synthesis (2026-08-08, closed node) -- Goal 057 B3.0D source mode-pairing Hermitianity

- Target: define the fixed-mode archimedean pairing integral from B3.0C and
  prove `pairing i r n = conj (pairing i n r)` with the established
  antilinear-first orientation.
- Wiring: B3.0C supplies `Integrable` for every fixed `(n,r)`; B3.0D is the
  next child of open B3.0 and still advances, but does not close, the first of
  ten coarse Goal-057 checkpoints.
- Four `q3_docs` queries returned B3.0C and its verdict as the exact local
  predecessors; no stronger pre-existing source-pairing theorem was found.
- The source multiplier is definitionally real-valued
  (`sourceArchimedeanMultiplier : ℝ → ℝ`), so complex conjugation fixes its
  coerced value pointwise.
- Mathlib's official `integral_conj` theorem commutes conjugation with the
  Bochner integral:
  https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/Integral/Bochner/ContinuousLinearMap.html#integral_conj.
- A source-exact scratch with one definition and one theorem compiles: unfold
  the pairing, rewrite by `← integral_conj`, simplify conjugated products, and
  finish the commutative scalar identity by `ring`.
- Minimal production candidate: one import of B3.0C, one noncomputable
  definition, one Hermitian-symmetry theorem; no new analytic premise and no
  generated PSD/Step33 supplier.
- Boundary: fixed-mode archimedean kernel and Hermitianity only; no source
  Weil-form decomposition, prime/pole side, operator graph/domain, uniform
  cofinal bound, compression, continuum numerator, H4a1b, promotion, PX, or RH.
  Production was forbidden until one same-chat Proshka release.
- Proshka released exactly one noncomputable pairing definition and one
  conjugate-symmetry theorem.  Production
  `D0PstarSourceArchModePairingKernel.lean` has SHA-256
  `02a382679fd1f401141d1e5c1ba6b3967fe5a10271281a4bc7b86daf3d620974`;
  direct Lean, target 7,764-job build, full 7,817-job build, `q3_check`,
  80/80 unit tests, 2/2 proof-DB declarations, and 10/10 plants pass.
- Exact closed class: fixed-mode source pairing kernel with antilinear-first
  Hermitianity.  No integral evaluation, diagonal sign, CCM-WR entry
  crosswalk, source Weil form, operator graph/domain, compression, uniform
  cofinal estimate, continuum numerator, H4a1b, promotion, PX, or RH follows.
- Next gap is
  `GOAL057_B3_0E_SOURCE_ARCHIMEDEAN_PAIRING_CCM_WR_SIGN_NORMALIZATION_CROSSWALK`;
  it is named but not authorized and requires a fresh source audit before the
  next same-chat delegated review.

## Synthesis (2026-08-05, closed node) -- G5 direct determinant-sign endpoint receiver

- Target: bypass the unnecessary general Sturm-inertia formalization at the
  public interface and derive the cofinal root bracket directly from strict
  signs of the committed Hermitian Schur determinant.
- Five targeted `q3_docs` searches for a Lean Sturm-count/principal-minor law,
  Sylvester inertia, and general Hermitian `LDL` machinery returned no
  candidates.  Mathlib's `Analysis.Matrix.LDL` is specialized to positive
  definite matrices and is not a ready indefinite-inertia receiver.
- The needed route is already available locally:
  `det_mode4HermitianSchurMatrix_eq_mode4SchurMatrix_det` followed by
  `mode4SchurMatrix_det_sign_eq_rootFunction_sign`.  Therefore strict positive
  and negative determinant endpoints transfer exactly to strict positive and
  negative values of the same scalar root function.
- Implemented
  `exists_mode4RootFunction_eq_zero_of_hermitianSchur_det_pos_neg`; its only
  concrete endpoint payload is `0 < det ALower` and `det AUpper < 0`.
  Hermitianity, determinant crosswalk, continuity, and orientation are
  internal.  The two one-sided transfer lemmas are public separately.
- Direct Lean, targeted 7750-job build, full 7817-job build, and `q3_check`
  pass.  All three new public theorems have only
  `[propext, Classical.choice, Quot.sound]`; no holes, project axioms, or
  `native_decide` occur.
- Boundary: this receiver will not assert either endpoint sign, choose endpoint
  formulas, prove a cofinal threshold, close G5/S1, or change the route/bus
  state.  Counts `2`/`3` remain a sufficient optional supplier, not the public
  minimum.

## Synthesis (2026-08-05, closed node) -- canonical mode-4 tail split

- The elementary choice `K = 4 * mProject` now discharges the quantitative
  tail-separation premise for every `mProject >= 2`.  The proof uses only the
  exact project definitions, `Real.pi_lt_d2`, and ordered-ring arithmetic.
- Implemented `mode4Jacobi_tail_separated_at_four_mul` and the specialized
  direct receiver
  `exists_mode4RootFunction_eq_zero_at_four_mul_of_hermitianSchur_det_pos_neg`.
  The latter fixes the split and internalizes both `3 <= K` and the universal
  tail inequality.
- Consequently the canonical-split root bracket now needs only the endpoint
  order, `LambdaUpper <= 20`, and the two strict determinants at
  `K = 4 * mProject`.  It does not assert those signs or any spheroidal
  eigenvalue.
- Direct Lean passes for both edited files; the target build passes 7750 jobs,
  the full build passes 7817 jobs, and `q3_check` is `ok`.  Both new public
  theorems use exactly `[propext, Classical.choice, Quot.sound]`.

## Synthesis (2026-08-05, source theorem found) -- explicit PSWF eigenvalue separator

- Primary source: Bonami--Karoui, arXiv:1405.3676v2, Theorem
  `chi-between2` / equation `boundschi2`.  For every `c > 0` and `n >= 2`,
  it proves the strict enclosure
  `c * tildePhi (pi*n/(2*c)) < sqrt (chi_n c) <
  c * tildePhi (pi*(n+1)/(2*c))`; `tildePhi` is strictly increasing and
  the width between adjacent endpoints is less than `1`.
- With the project convention `G = c^2` and shifted spectral parameter
  `Lambda = chi - G`, the source therefore separates the even indices
  `n = 2, 4, 6` by the explicit candidates
  `LambdaLower = c^2 * tildePhi (3*pi/(2*c))^2 - G` and
  `LambdaUpper = c^2 * tildePhi (3*pi/c)^2 - G`:
  `chi_2 < LambdaLower + G < chi_4 < LambdaUpper + G < chi_6`.
- Here every `chi_n` is Bonami--Karoui's ordered **differential**
  Sturm--Liouville eigenvalue.  It is not the repository field
  `ProlatePair.chi2`, which denotes the finite-Fourier scalar attached to the
  degree-4 time mode (`h4 <-> chi2` in the separate even-sector Fourier
  indexing).  Thus using differential indices `2,4,6` here preserves, rather
  than violates, the locked degree-4 object dictionary.
- This is a materially stronger source lock than the Dunster fixed-mode
  asymptotic `Lambda_4 = -G + 9*sqrt G + O(1)`: no unknown remainder
  constant or finite threshold occurs in the Bonami--Karoui statement.
- It is not yet a Lean endpoint-sign supplier.  The current exact
  `mode4HermitianSchurMatrix` contains the infinite recessive tail through a
  Schur complement.  A formal receiver must still identify its negative
  eigenvalue count (or determinant sign) with the ordered PSWF spectrum below
  the chosen endpoint.  The repository source dossier establishes this
  ordering and parity at statement level, but no Lean `chi_n` spectral family
  or Schur-complement/infinite-Jacobi count crosswalk exists yet.
- Mathlib has no ready complete-elliptic-integral implementation for
  `tildePhi`.  Consequently a direct formalization of the displayed endpoint
  formulas is substantial; the preferred next node is the smallest abstract
  source-spectrum-to-Schur-count receiver that keeps the Bonami--Karoui
  inequalities as explicit future inputs.  No diagnostic `8/10` asymptotic
  endpoint is authorized.

## Synthesis (2026-08-05, in progress) -- G5 source-locked endpoint count fork

- Exact remaining target after the committed determinant, inertia, and
  same-determinant Hermitian suppliers: for one source-locked cofinal pair
  `ΛLower ≤ ΛUpper ≤ 20` and an admissible split `K`, prove that the two
  Hermitian Schur matrices are nonsingular and have respectively `2` and `3`
  negative eigenvalues.
- Five targeted `q3_docs` searches for mode-four spheroidal eigenvalue
  localization, the third even branch, Jacobi Sturm counts, and explicit
  cofinal brackets returned no indexed candidates.
- Primary-source inventory: DLMF §30.3 gives strict eigenvalue ordering,
  analyticity in the squared spheroidal parameter, and the value at parameter
  zero; DLMF §30.8 gives the exact three-term coefficient recurrence; DLMF
  §30.9 gives the large-positive-parameter asymptotic with
  `q = 2 (n - m) + 1`; DLMF §30.16 gives convergent finite tridiagonal
  approximants.  None of those pages, as inspected, supplies the explicit
  finite cofinal threshold and endpoint inequalities required by the current
  Lean receiver.
- A high-precision diagnostic of the committed recurrence places successive
  crossings near `-G + c * sqrt G` with `c = 1, 5, 9, 13`; consequently the
  pair `c = 8, 10` is a plausible bracket for the third even branch.  This is
  deliberately **not** a source lock, theorem, or authorized project
  definition, and it has not been materialized in Lean or route state.
- Proshka's earlier verdict is recorded locally only by message id and a
  timing-ledger summary: it recovered a cofinal spectral-localization sublemma
  but stopped at the then-missing residual-orientation bridge and selected the
  parameterized Jacobi/Schur/Sturm fork.  Commits `a777cb49`, `0bca583c`, and
  `d4361675` now close that bridge through the exact same scalar root function.
- Browser transport is still unavailable to Codex: the controllable browser
  profile is unauthenticated and the signed-in in-app tab is not exposed by
  the current browser tools.  Therefore no new Proshka request is claimed as
  sent, and no response time is invented.

## PRO_REVIEW_REQUEST

Route: Route B challenger, G5/S1
Current step: G5_MODE4_R1A source-locked cofinal root bracket
Current theorem: `exists_mode4RootFunction_eq_zero_of_hermitianSchur_counts_two_three`
File: `Q3/Proofs/RouteB/D0Mode4SchurHermitianSymmetrization.lean`
Lean error / blocker: none; the receiver compiles, but its four endpoint facts
are not source-locked.
Options:
A. Recover the exact theorem statement from Proshka message
`ddb6364a-2d9b-4162-84b3-fa6ea6f0176a` and instantiate its cofinal
localization after auditing commits `a777cb49`, `0bca583c`, and `d4361675`.
B. Supply a new explicit source/Sturm proof of nonsingularity and negative
counts `2`/`3`, including endpoint formulas, split `K`, and all cofinal
quantifiers.
C. If neither is source-admissible, stop with the exact smallest missing
endpoint-localization theorem instead of minting `-G + 8 sqrt G` and
`-G + 10 sqrt G` as project definitions.
Codex recommendation: A first; the previously missing determinant/residual
orientation is now Lean-proved, so re-adjudication may turn the recovered
localization into the four exact endpoint facts without a new analytic route.
Question for Louise: Do the three committed bridges discharge the only blocker
in the recovered cofinal localization, and if so what are the verbatim
endpoint formulas, split rule, cofinal threshold, and theorem interface?

## Synthesis (2026-08-05, closed node) -- G5 same-determinant Hermitian Schur supplier

- Target: discharge the abstract same-determinant Hermitian-matrix input of the
  committed G5 inertia receiver without changing the scalar root function.
- Implemented `D0Mode4SchurHermitianSymmetrization.lean`.  Its explicit
  off-diagonal is `-sqrt (L_(q+1) * U_q)`; nonnegativity of every lower
  coefficient and positivity of every upper coefficient make this real.
- `mode4HermitianSchurMatrix_isHermitian` proves the matrix is Hermitian by
  entrywise symmetry.  The determinant recurrence uses
  `sqrt (L_(q+1) * U_q)^2 = L_(q+1) * U_q`, hence
  `det_mode4HermitianSchurMatrix_eq_mode4SchurMatrix_det` is an exact equality,
  not a sign-only comparison or an assumed similarity.
- The specialized root-bracket receiver now discharges Hermitianity and the
  determinant crosswalk internally.  Its only remaining endpoint inputs are
  two determinant-nonzero facts and the negative-eigenvalue counts `2` and
  `3`; continuity and determinant-to-root orientation are already supplied.
- Direct Lean validation passes and every printed public theorem has only
  `[propext, Classical.choice, Quot.sound]`.  No `sorry`, `admit`, declared
  project axiom, or `native_decide` is used.
- Boundary: this node does not assert the concrete endpoint counts.  The next
  live G5 task is their source/Sturm materialization together with endpoint
  nonsingularity.  Lamport `STATE.json` is synchronized at revision 55 while
  preserving its idle control sentinel; external Proshka ratification remains
  pending and no Bus 010 or route promotion was created.

## Synthesis (2026-08-05, closed node) -- G5 Hermitian inertia-to-root-sign receiver

- Target: turn a source/Sturm negative-eigenvalue count for a Hermitian matrix
  with the same determinant as `mode4SchurMatrix` into the two strict signs of
  `mode4RootFunction`.
- Five `q3_docs` queries for Hermitian determinant signs, inertia, Sturm
  sequences, and Jacobi symmetrization returned no candidates.
- Mathlib's `Mathlib.Analysis.Matrix.Spectrum` supplies the exact kernel fact
  `Matrix.IsHermitian.det_eq_prod_eigenvalues`; no ready theorem packaging the
  parity of the negative-eigenvalue count into a determinant sign was found.
- Implemented `D0Mode4SchurInertiaOrientation.lean`: the finite negative count,
  `sign(det A)=(-1)^count` for nonsingular Hermitian `A`, strict positive and
  negative residual signs for counts `2` and `3`, and the complete conditional
  intermediate-value root-bracket receiver.
- Targeted 7749-job build and `q3_check` pass.  Every printed theorem has only
  `[propext, Classical.choice, Quot.sound]`; no holes or project axioms occur.
- Boundary: the receiver does not invent the same-determinant Hermitian
  symmetrization, endpoint nonsingularity, or source/Sturm counts.  Those are
  now the exact remaining concrete inputs to the G5 bracket.

## Synthesis (2026-08-04, closed node) -- G5 mode-4 Schur/continuant orientation

- Target: `det_mode4SchurMatrix_eq_upperProd_mul_rootFunction` in
  `Q3/Proofs/RouteB/D0Mode4JacobiSchurContinuant.lean`.
- Five `q3_docs` queries for tridiagonal/continuant/Schur determinant reuse
  returned no candidates.
- Mathlib supplies generic determinant expansion and determinant-preserving
  row/column operations, but no ready tridiagonal continuant theorem was found.
- Implemented the rigorous route: `mode4LeftContinuantMatrix` reverses the
  finite Jacobi index order so first-row Laplace expansion exactly matches the
  denominator-cleared left recurrence; `mode4SchurMatrix` replaces its newest
  diagonal by `C_(K-1) - U_(K-1) R_K`.
- `det_mode4SchurMatrix_eq_schurContinuant` proves the literal matrix
  determinant identity.  The composed theorem
  `det_mode4SchurMatrix_eq_upperProd_mul_rootFunction` fixes the orientation as
  `det = (prod_{q<K} U_q) * mode4RootFunction`, and
  `mode4SchurMatrix_det_sign_eq_rootFunction_sign` uses positivity of every
  upper factor to transfer the sign exactly.
- Direct Lean validation, the targeted 7748-job build, `q3_check`, and the
  full 7817-job project build pass with no holes or project axioms; every
  printed public theorem has exactly the standard axiom profile
  `[propext, Classical.choice, Quot.sound]`.
- Boundary preserved: this closes the determinant/root-function crosswalk.  It
  does not itself supply a source-locked spectral count or the two strict
  endpoint signs needed for the cofinal root bracket.
- External Proshka ratification is still pending because the controllable
  ChatGPT browser session was unauthenticated; Route B state therefore remains
  unchanged (`CHALLENGER / NOT_RH`, no Bus 010).

## Insight (2026-07-07, Route B state hygiene) -- TroughRelabel_and_BusSync_v1

- Route B request state had a two-copy split: `/Users/emalam/GitHub/rh_lean_01_2026`
  contained the canonical `AnchorLocked_Extraction_v1` state, while
  `/Users/emalam/Documents/GitHub/rh_lean_01_2026` retained useful older
  request artifacts and a richer pre-extraction `loop_state.json`.
- Both copies had the same git HEAD, so canonical selection used the active
  Codex workspace and the newer extraction section in `ROUTE_B_STATE.md`.
- Missing request-local artifacts were merged into the canonical copy without
  overwriting canonical files; the stale twin now has only a pointer file for
  this request state.
- Reviewer ruling applied:
  `TAIL_FLATTENING_REFUTED -> TAIL_MASS_LEVEL_CONFIRMED + TAIL_PROFILE_TROUGH`.
  The strict DeltaS rows `[2.02180339103, 4.63439244204, 1.39442397632]`
  remain the law-judge refutation of a single `p=1` law; the budget envelope
  judge passes for the lemma-budget state.
- `TroughBoundary` is registered at gamma `[1419,2515]`, with
  `C_eff=2.7e-29..3.0e-29` vs plateau `0.78e-28..1.05e-28`; interpretation is
  smooth-part amplitude calibration around `3e-29` (medium confidence).
- `LOOP.md` in the canonical request directory is now pointer-only; the old
  dust-era loop is archived as `LOOP_ARCHIVED_dust_era.md`.  No RH claim, no
  Phase 2, no new computation, and no next mathematical gate selected.

## Synthesis (2026-06-14, in progress) -- Track B E5' edge-defect contract

- Target lemma: prove `Edge_K(h) <= mu_K Norm_K(h)` for `h in C_K cap kerQ`,
  equivalently certify `mu_K G_K - E_edge,K >= 0` on `ker(Q_K)` for the active
  Track B cells `K=2,3,3.5`; this is not a full-RH claim and does not touch
  `Q3.Main`.
- Local embedding search did not find an existing E5' domination theorem; it
  returned only the corrected positive-definite packet cone, matrix-guard, and
  old lower-bound/penalty infrastructure. External search likewise found only
  general Beurling-Selberg/CLV/Weil-positive-definite tools, not an off-the-shelf
  restricted raw-edge PSD theorem.
- Option 1 (active): use the proof contract in
  `docs/trackB/TRACKB_E5P_PROOF_CONTRACT.md`, set `m_old=0` unless a new
  pre-edge ledger is proved, and target a direct penalty certificate
  `mu_K G_K - E_edge,K + tau Q_K^T Q_K >= 0`.
- Option 2 (fallback): if `mu_K` is missing or incomparable, use
  `docs/trackB/MU_BUDGET_INTERFACE.md`; the correct comparison is

[truncated after 650 lines]
```

### full/q3.lean.aristotle/docs/PROSHKA_ENTRYPOINT.md
```text
# PROSHKA ENTRYPOINT (READ THIS FIRST)

Purpose: Provide the minimal, current context for Q3 formalization.
All other files are optional and linked below.

## 1) Contract (must match RH_Q3)
- docs/PROJECT_SPECS.md
- docs/insights/rh_q3_invariants_contract_2026_01_16.md

## 2) Current status and next step
- PROJECT_ORCHESTRATOR.md (Active Next Step)
- PROJECT_WORKFLOW.md

## 3) Drift checklist (red flags)
- A3 symbol must be P_A (period-1); do not use a_star as A3 symbol.
- Toeplitz in A3 must be Fourier/Rayleigh, not sampling P(π(i-j)/M).
- Prime operator must be compression/rank-one sum with w_Q.
- Keep t_sym and t_rkhs distinct; do not mix w_Q and w_RKHS.

## 4) If stuck
- docs/INSIGHTS.md + docs/insights/INDEX.md
- docs/ERRORS_DESTROYER.md

## 5) Current Proshka request
- PROSHKA_REQUEST_4.md (single-scale closure pack; 3 open axioms)

## 6) Packed context (one file)
- PROSHKA_CONTEXT_SINGLE_SCALE_2026_01_24.md
 - Build script: scripts/build_proshka_brief.py

## 7) Policy (canonical set)
- docs/PROSHKA_POLICY.md

## 8) Legacy
- PROSHKA_REQUEST_3.md (archive only)
```

### full/q3.lean.aristotle/PROSHKA_REQUEST_4.md
```text
# PROSHKA REQUEST v5: SingleScale closure pack (3 axioms)

---

## §0. Статус и цель

**Цель:** закрыть ровно 3 открытые single‑scale аксиомы (mainline) и связать их в единый мост
к положительности на атомах при `t = t_critical`.

**Контекст (важно):** цепочка на бумаге полная, с проверяемыми константами и шагами.
Остаются **3 атомарных узла** (см. ниже), которые могут быть тяжёлыми аналитически.
Нужно закрыть их **строго**, без “интуитивных” вставок, и обеспечить независимую
проверяемость (Lean + бумага). Роль Прошки — искать **синергию и кратчайшие
решения**, объединяя лучшие подходы (анализ / Toeplitz / RKHS) и ускоряя формализацию.

**Открытые аксиомы (mainline):**
- `SingleScale.continuous_P_A_shift`
- `SingleScale.rayleigh_basis0_shift_ge_cstar_quarter`
- `SingleScale.rho_oneK_tcritical_le_cstar_quarter`

Источник правды:
- `ACTIVE/chain_status.md`
- `ACTIVE/orchestrator.md`

**Результат, который хотим от Прошки:**
- конкретные Lean‑леммы (без `sorry`/`exact?`),
- минимальные цепочки зависимостей,
- чёткий файл‑план: где писать и чем закрывать,
- связка трёх лемм в одну схему «A3 floor + RKHS cap ⇒ positivity на атомах».

---

## §1. Входные точки (используй их как оглавление)

**Главный индекс знаний:** `ACTIVE/KNOWLEDGE_BASE.md`

**Спецификации и мэппинг:**
- `ACTIVE/refs/SPECS_INDEX.md`
- `ACTIVE/refs/Q3_BLOCK_MAP.md`
- `ACTIVE/refs/paper_lean_mapping.md`
- `ACTIVE/refs/q3_structure_mapping.md`

**Проектные правила/контракт:**
- `ACTIVE/chain_status.md`
- `ACTIVE/orchestrator.md`
- `ACTIVE/pipeline/PROBLEM_SOLVER_PROMPT_RU.md`

**Внимание (красные флаги):**
- **НЕ** смешивать `t_sym` и `t_rkhs`.
- **НЕ** использовать `a_star` вместо `P_A`.
- **НЕ** требовать Szegő–Böttcher как блокер.
- **НЕ** путать `w_Q` и `w_RKHS`.

---

## §2. Контракт single‑scale (обязателен)

- `t_critical = 3/20`
- `c_star = 11/10`
- `B_min = 3`
- Основная линия: **τ = 0** (base atom cone)
- `Q⋆` с коэффициентом `(2M+1)` **только** у prime‑части

---

## §3. Проблемы (требуются решения)

### Проблема 1: `SingleScale.continuous_P_A_shift`

**Смысл:** непрерывность периодизированного сдвинутого символа
`P_A_shift B t_critical tau` по θ.

**Ожидаемая форма:**
```
axiom continuous_P_A_shift (B tau : ℝ) :
  Continuous (Q3.P_A_shift B t_critical tau)
```

**Желаемый результат:** заменить аксиому на доказанную лемму.

**Ожидаемая структура доказательства:**
1) Непрерывность `phi_shift`, `g_shift`.
2) Локальная конечность периодизации ⇒ `tsum` = `Finset.sum`.
3) Конечная сумма непрерывных ⇒ непрерывно.

**Где смотреть:**
- `Q3/Proofs/ShiftedWindows.lean`
- `Q3/Proofs/P_A_Toeplitz_bridge_defs.lean`
- `Q3/Proofs/HeatKernelParams.lean`

**Контекст (из свежего запроса к Aristotle):**
`full/q3.lean.aristotle/aristotle_input/continuous_P_A_shift_tcritical.md`.

**Нужен ответ от Прошки:**
- чёткая Lean‑цепочка лемм
- какие именно леммы уже есть и какие надо добавить
- минимальный proof‑skeleton без аналитического ада

---

### Проблема 2: `SingleScale.rayleigh_basis0_shift_ge_cstar_quarter`

**Смысл:** Rayleigh‑нижняя оценка для Toeplitz‑блока на `t_critical`.
Цель — получить **c_star/4** на базисном векторе (или эквивалентную форму).

**Ожидаемая форма (примерно):**
```
axiom rayleigh_basis0_shift_ge_cstar_quarter (B : ℝ) :
  ... ≥ c_star / 4
```

**Где смотреть:**
- `Q3/Proofs/Rayleigh_basis0_of_A3.lean`
- `Q3/Proofs/Rayleigh_Q_identification.lean`
- `Q3/Proofs/P_A_Toeplitz_bridge.lean`
- `Q3/Proofs/P_A_Toeplitz_bridge_defs.lean`

**Ожидаемый смысловой мост:**
- Toeplitz‑квадратичная форма = интеграл по `P_A` (Rayleigh)
- A3 floor на `P_A_shift` ⇒ lower bound для Rayleigh‑части
- Привязка к `e0` (basis0) ⇒ нужная оценка

**Нужен ответ от Прошки:**
- точная Lean‑формулировка
- цепочка: какие леммы переиспользовать
- где фиксировать `t_critical`

---

### Проблема 3: `SingleScale.rho_oneK_tcritical_le_cstar_quarter`

**Смысл:** RKHS‑cap на `t_critical` (prime operator norm ≤ c_star/4).

**Ожидаемая форма (примерно):**
```
axiom rho_oneK_tcritical_le_cstar_quarter (K : ℝ) :
  rho_oneK t_critical K ≤ c_star / 4
```

**Где смотреть:**
- `Q3/Proofs/RKHS_cap_rayleigh.lean`
- `Q3/Proofs/T_P_comp_utils.lean`
- `Q3/Axioms.lean`

**Нужен ответ от Прошки:**
- минимальная цепочка лемм,
- как аккуратно “протащить” bound на `t_critical`,
- если надо — какие точечные леммы добавить.

---

## §4. Связка трёх лемм → positivity на атомах

Нужен короткий мост (в логике проекта):
- A3 floor (Rayleigh) + RKHS cap ⇒ `Q⋆(t_critical; Φ_{B,t}) ≥ 0` для генераторов
- далее A1′ + A2 → Q≥0 на W_K → RH

Прошка, пожалуйста, **покажи схему склейки**, с именами лемм и файлами.

---

## §5. Ограничения (важно)

- Никакой двухмасштабности.
- Никаких ERS‑конструкций.
- Никаких новых «креативных» теорем — только из проекта или стандартная математика.
- В Lean: без `sorry`/`exact?`.
- **Не проверять статус RH** (не обсуждать “открыта/доказана/принята”).
  Мы строим и формализуем доказательство в рамках проекта.
  **Никакого веб‑поиска** “доказана ли RH”.

---

## §6. Формат ответа

1) **Карта решения** (3 задачи → по шагам)
2) Для каждой задачи:
   - точная Lean‑формулировка
   - список нужных лемм
   - где писать (файл)
   - минимальный proof‑outline
3) **Склейка** (как 3 факта дают positivity на атомах)


**Спасибо! Нужна максимально “машинная” версия, чтобы агент мог сразу формализовать.**

**∎ END OF PROSHKA REQUEST v5**
```

### docs/Codex/TASK_2026-08-14_goal058_g3_prolate_rate_floor.md
```text
# Codex task — Goal 058 G3 prolate rate and floor

Date: 2026-08-14
Source commit: `0fb4023ab401ab3f68e1a507197e379e9261cc3c`

## Selected source front

Continue the owner-authorized Goal 058 G1/G3 closure loop at the remaining G3
source theorem. The explicit CCM Eq. (7.1) packet, its Fourier invariance, its
`E_star` inversion symmetry, the physical inversion-to-coefficient crosswalk,
and the denominator mechanism are already kernel checked.

The active obligation is to connect the actual normalized two-mode prolate
family to those consumers:

```text
actual h_lambda on current PairIndex family
  -> uniform CCM Lemma 7.2 O(lambda^-2) estimate to explicitCCMLimitH
  -> E_star/window approximation and nonzero central overlap
  -> eventual projected denominator floor
  -> one precommitted coupled (m,N) schedule
```

## Required evidence boundary

- Use the actual production `ProlatePair`, `hTrial_m`, `gTrial_m`, `P_m_N`,
  and `PairIndex` objects; do not introduce a parallel family with stronger
  fields and call it the source family.
- A theorem taking the approximation rate, central overlap, denominator floor,
  or cofinal tracking as binders is a receiver and does not close this task.
- Source-lock the normalization, phase, scaling, and degree `0/4` selection.
- Preserve the one-family invariant and the P59 `_normalized` supplier lock.
- Keep G1 open as the parallel spectral front. Beta/commutator identities alone
  do not imply simplicity or a positive uniform gap.
- No G3, Route B, or RH promotion before the actual rate, floor, and coupled
  schedule are kernel checked.

## First action

Audit the current `ProlatePair`/constructor surface against CCM Lemma 7.2 and
its pinned primary source. Identify the smallest missing source constructor or
theorem head. Reuse existing exact consumers; do not build another conditional
receiver.

## Validators

Direct Lean, target build, full build at node close, `q3_check`, forbidden-token
scan, public axiom audit, strict Spine, RouteB status, and inventory/semantic
freshness. External review is requested only if the source theorem cannot be
resolved locally.
```

### q3.lean.aristotle/ACTIVE/requests/routeB_lamport_rh_closure/GOAL058_EXPLICIT_CCM_LIMIT_FOURIER_POISSON_CLOSEOUT_2026-08-14.md
```text
# Goal 058 explicit CCM limit Fourier/Poisson closeout

Date: 2026-08-14

## Verdict

```yaml
TARGET_ID: GOAL058_EXPLICIT_CCM_LIMIT_FOURIER_POISSON
VERDICT: PASS_EXACT_LIMIT_PACKET_AND_INVERSION
SUCCESS: GOAL058_EXPLICIT_CCM_LIMIT_FOURIER_POISSON_PROVED
SCOPE: EXACT_ANALYTIC_SUPPLIER
VERIFIER: LEAN
PROLATE_RATE: OPEN_SOURCE_THEOREM
CENTRAL_OVERLAP_FLOOR: OPEN_SOURCE_ESTIMATE
COUPLED_SCHEDULE: OPEN
G1: OPEN
G3: OPEN
ROUTE: CHALLENGER_NOT_RH
ROUTE_PROMOTION: false
RH_CLAIM: false
```

## Integrated theorem

```text
Q3/Proofs/RouteB/D0PstarExplicitCCMLimitFourier.lean
```

The production file defines the literal CCM Eq. (7.1) packet

```text
h(x) = (pi/2) x^2 (2*pi*x^2 - 3) exp(-pi*x^2)
```

and proves two public supplier theorems.

1. `fourier_explicitCCMLimitH` derives `Fourier h = h` in the repository's
   plus-phase convention.  The proof constructs the polynomial Gaussian from
   second and fourth Fourier moments and Mathlib's derivative identity; it
   does not take Fourier invariance as a hypothesis.
2. `E_star_explicitCCMLimitH_inv` proves, for every `u > 0`,

   ```text
   E_star h (u^-1) = E_star h u.
   ```

   The proof establishes rapid enough decay, applies Mathlib's Poisson
   summation theorem to every positive rescaling of the literal packet,
   converts the integer sum to the positive-integer `E_star` sum using
   evenness and `h(0)=0`, and transports the square-root scale exactly.

This is the concrete supplier consumed by the already proved production
inversion-to-coefficient crosswalk.  No source-row symmetrization, abstract
Fourier-eigenfunction binder, or assumed inversion identity is used.

## Source lock

The formula and `E` convention are pinned to
`literature/zotero/H8ULBMAL/fulltext.md:1256-1274` (CCM Eq. (7.1), Eq. (7.2),
and Lemma 7.1).  The same source states the prolate approximation estimate in
Lemma 7.2 at lines 1299-1308 and uses Poisson inversion in the proof of Lemma
7.3 at lines 1410-1468.

## Production validation

```text
file SHA-256: 92495b631116e29f3e6e1a6cf0c60cdf5f6d5fbf6396cfbd1bc8415293a28aa9
shape: 19072 bytes, 500 newline-terminated lines
direct lake env lean: PASS
target lake build: PASS (7755 jobs)
full lake build: PASS (7817 jobs)
q3_check: PASS
forbidden-token scan: PASS
public theorem axioms: [propext, Classical.choice, Quot.sound]
```

The warnings are pre-existing style-linter classes (`unnecessarySeqFocus` and
two no-op `push_cast` calls); there are no holes or added axioms.

## Exact remaining source obligation

The explicit limit and its inversion are now kernel checked.  G3 still needs
one source-faithful family theorem, not another receiver:

1. construct the actual normalized two-mode prolate `h_lambda` on the current
   `PairIndex` family;
2. export the CCM Lemma 7.2 uniform estimate
   `sup_[−lambda,lambda] |h_lambda-h| <= C*lambda^-2` with a literal constant
   or eventual bound;
3. transport it through the current `E_star`, window projection, and existing
   coefficient crosswalk;
4. prove a nonzero central overlap and an eventual projected-norm floor on one
   precommitted coupled `(m,N)` schedule;
5. combine the same-family odd-mass and even-sector Rayleigh-excess rates.

G1 remains independent.  The structured beta/commutator identities do not
imply simplicity; the surviving route needs literal quantitative even-sector
cyclicity/arithmetic and strict even-versus-odd ground ordering on that same
schedule.

## Exact evidence boundary

This closeout proves the literal limiting packet, its Fourier invariance, and
the exact positive-half-line inversion symmetry of `E_star h`.  It does not
construct the prolate source family, prove its approximation rate, establish a
central-overlap or normalization floor, choose a cofinal schedule, prove G1 or
G3, promote Route B, or prove RH.

```yaml
SEARCH_FLAGS:
  - GOAL058_EXPLICIT_CCM_LIMIT_PACKET
  - GOAL058_POLYNOMIAL_GAUSSIAN_FOURIER
  - GOAL058_E_STAR_POISSON_INVERSION
  - GOAL058_PROLATE_RATE_AND_FLOOR_OPEN
ARSENAL_USED:
  - exact Gaussian Fourier transform
  - Fourier derivative moments
  - cocompact rpow decay
  - Poisson summation
  - positive-integer sum reflection
REJECTED:
  - Fourier invariance as an input
  - inversion symmetry as an input
  - source-row symmetrization
  - explicit-limit inversion as G3 closure
AUTOPSY: dropped=DEPENDENCY; note=The concrete limit supplier is exact; the actual prolate approximation rate, central floor, and coupled schedule remain source obligations.
```
```

### q3.lean.aristotle/Q3/Proofs/RouteB/ProlateLayer.lean
```text
import Mathlib

set_option linter.mathlibStandardSet false

open Complex MeasureTheory Set

noncomputable section

namespace Q3.RouteB.D0Pstar

/-- The formal prolate differential expression

`PW_lambda f = -d/dx ((lambda^2-x^2) d/dx f)
  + (2*pi*lambda*x)^2 f`.

This is only the pointwise expression.  It carries no operator domain,
self-adjointness, spectral, or existence assertion.

Source lock:
`ACTIVE/requests/routeB_lamport_rh_closure/011_concrete_htrial_source_lock.answer.md:69-73`;
`docs/PEN_3_3_G04_OBJECT_DICTIONARY.md:33-43`;
`literature/zotero/H8ULBMAL/fulltext.md:1293-1297`.
-/
def prolateWaveExpression
    (lambda : ℝ)
    (f : ℝ → ℂ)
    (x : ℝ) : ℂ :=
  -fderiv ℝ
      (fun y : ℝ =>
        (((lambda ^ 2 - y ^ 2 : ℝ) : ℂ) * (fderiv ℝ f y) 1))
      x 1
    + (((2 * Real.pi * lambda * x) ^ 2 : ℝ) : ℂ) * f x

/-- Data wrapper for the formal prolate differential expression.

`action_eq` pins the stored action to `prolateWaveExpression`; this structure
does not assert a domain, symmetry, self-adjointness, or any eigenfunction.
-/
structure ProlateOperatorData where
  lambda : ℝ
  action : (ℝ → ℂ) → ℝ → ℂ
  action_eq : action = prolateWaveExpression lambda

/-- A source-indexed pair of prolate-mode candidates.

All analytic facts are fields (hypotheses), not existence theorems.  The index
lock is `h0 <-> chi0` and `h4 <-> chi2`; in particular there is no `chi4`
field.  No sign or ordering hypothesis is included.

Source lock:
`docs/PEN_3_3_G04_OBJECT_DICTIONARY.md:45-75,93-112,232-243`;
`ACTIVE/requests/routeB_lamport_rh_closure/D0_5_GROUND_AND_TRIAL_TYPES.md:55-75`.
-/
structure ProlatePair where
  pw : ProlateOperatorData
  h0 : ℝ → ℂ
  h4 : ℝ → ℂ
  chi0 : ℝ
  chi2 : ℝ
  I0 : ℝ
  I4 : ℝ
  h0_even : Function.Even h0
  h4_even : Function.Even h4
  h0_support : Function.support h0 ⊆ Icc (-pw.lambda) pw.lambda
  h4_support : Function.support h4 ⊆ Icc (-pw.lambda) pw.lambda
  h0_integrable : Integrable h0
  h4_integrable : Integrable h4
  h0_sqNorm_integrable : Integrable (fun x : ℝ => ‖h0 x‖ ^ 2)
  h4_sqNorm_integrable : Integrable (fun x : ℝ => ‖h4 x‖ ^ 2)
  h0_normalized : (∫ x : ℝ, ‖h0 x‖ ^ 2) = 1
  h4_normalized : (∫ x : ℝ, ‖h4 x‖ ^ 2) = 1
  I0_eq_integral : (I0 : ℂ) = ∫ x : ℝ, h0 x
  I4_eq_integral : (I4 : ℂ) = ∫ x : ℝ, h4 x
  h0_fourier_center : (I0 : ℂ) = (chi0 : ℂ) * h0 0
  h4_fourier_center : (I4 : ℂ) = (chi2 : ℂ) * h4 0

/-- The source denominator `sqrt(I0^2 + I4^2)`.

Nonvanishing is intentionally not asserted in the type layer.
-/
def ProlatePair.normalizingDenominator (P : ProlatePair) : ℝ :=
  Real.sqrt (P.I0 ^ 2 + P.I4 ^ 2)

/-- The canonical plus-phase two-mode packet

`(I4*h0 - I0*h4) / sqrt(I0^2 + I4^2)`.

This supplies the `hTrial_m` input of the existing D0 `E_star -> gTrial_m`
chain.  Nonzero normalization and all sign claims belong to later layers.

Source lock:
`ACTIVE/requests/routeB_lamport_rh_closure/D0_5_GROUND_AND_TRIAL_TYPES.md:55-92`;
`docs/PEN_3_3_G04_OBJECT_DICTIONARY.md:93-112`.
-/
def prolateCombination (P : ProlatePair) (x : ℝ) : ℂ :=
  ((P.I4 : ℂ) * P.h0 x - (P.I0 : ℂ) * P.h4 x) /
    (P.normalizingDenominator : ℂ)

@[simp] theorem ProlateOperatorData.action_apply
    (P : ProlateOperatorData) (f : ℝ → ℂ) (x : ℝ) :
    P.action f x = prolateWaveExpression P.lambda f x := by
  rw [P.action_eq]

@[simp] theorem ProlatePair.normalizingDenominator_eq
    (P : ProlatePair) :
    P.normalizingDenominator = Real.sqrt (P.I0 ^ 2 + P.I4 ^ 2) :=
  rfl

@[simp] theorem prolateCombination_apply
    (P : ProlatePair) (x : ℝ) :
    prolateCombination P x =
      ((P.I4 : ℂ) * P.h0 x - (P.I0 : ℂ) * P.h4 x) /
        (P.normalizingDenominator : ℂ) :=
  rfl

#print axioms prolateWaveExpression
#print axioms ProlateOperatorData
#print axioms ProlatePair
#print axioms ProlatePair.normalizingDenominator
#print axioms prolateCombination
#print axioms ProlateOperatorData.action_apply
#print axioms ProlatePair.normalizingDenominator_eq
#print axioms prolateCombination_apply

end Q3.RouteB.D0Pstar
```

### q3.lean.aristotle/Q3/Proofs/RouteB/D0ProlateKTrialSource.lean
```text
import Q3.Proofs.RouteB.D0KTrialStage3
import Q3.Proofs.RouteB.ProlateLayer

set_option linter.mathlibStandardSet false

open Complex MeasureTheory Set
open scoped ENNReal NNReal

noncomputable section

namespace Q3.RouteB.D0Pstar

open CanonicalRHRoute

/-!
# Source-faithful prolate-to-kTrial contract

This module closes only the XW.8 type-level provenance seam.  It packages the
existing exact construction

`prolateCombination -> E_star -> gTrial_m -> gTrial_m_N -> kTrial_m_N -> c_n`

as the `CoefficientFamily` consumed by `centeredPstarFamily`.  Every analytic
supplier and the cofinal schedule remain explicit data.  In particular, this
module proves no existence theorem for prolate modes, no ground-state
identification, no convergence theorem, and no `SlotS2` statement.
-/

/-- Exact source data needed to construct the D0 coefficient row from the
canonical two-mode prolate packet.  The consumed source trial is determined
by `m`; `N` enters only through the finite projection and its certificates.

The equality `lambda_eq` prevents the free bandwidth stored in `ProlatePair`
from drifting away from the production convention `lambda_m i = sqrt i.m`.
The remaining fields are precisely the existing carrier and nonzero
certificates required by `c_n`; they are not synthesized here.  This contract
proves no projection-tail or regularity theorem.
-/
structure ProlateKTrialSourceData where
  pair : PairIndex → ProlatePair
  prolateCombination_eq_of_same_m :
    ∀ i j : PairIndex, i.m = j.m →
      prolateCombination (pair i) =
        prolateCombination (pair j)
  lambda_eq : ∀ i, (pair i).pw.lambda = lambda_m i
  eStar_memLp :
    ∀ i,
      MemLp (E_star (prolateCombination (pair i))) 2
        (dStar.restrict (I_m i))
  trialNonzero :
    ∀ i,
      TrialNonzero i (prolateCombination (pair i)) (eStar_memLp i)

/-- Applying `E_star` preserves the exact same-`m` source identity.  The
projection certificates remain allowed to depend on the full pair index.
-/
@[simp] theorem ProlateKTrialSourceData.E_star_eq_of_same_m
    (S : ProlateKTrialSourceData)
    (i j : PairIndex)
    (hm : i.m = j.m) :
    E_star (prolateCombination (S.pair i)) =
      E_star (prolateCombination (S.pair j)) := by
  rw [S.prolateCombination_eq_of_same_m i j hm]

namespace ProlateKTrialSourceData

/-- The production coefficient family whose row is definitionally the Fourier
coefficient of the normalized projected starred sum of the same
`prolateCombination` stored in `S`.
-/
def coefficientFamily (S : ProlateKTrialSourceData) : CoefficientFamily where
  kTrial := fun i n =>
    c_n i (prolateCombination (S.pair i))
      (S.eStar_memLp i) (S.trialNonzero i) n

/-- XW.8's exact finite-row provenance is definitional; there is no
independently supplied coefficient selector.
-/
@[simp] theorem coefficientFamily_kTrial
    (S : ProlateKTrialSourceData) (i : PairIndex) (n : ℤ) :
    S.coefficientFamily.kTrial i n =
      c_n i (prolateCombination (S.pair i))
        (S.eStar_memLp i) (S.trialNonzero i) n :=
  rfl

end ProlateKTrialSourceData

/-- A production `CanonicalData` together with the exact proof that its
coefficient family is the prolate-derived family above.

Keeping the already-dependent `CanonicalData` as one field avoids duplicating
its `CentralIndex` dependency in this wrapper.  Its `parent` and `extract`
therefore remain literally the production suppliers, while `kTrial_eq` rules
out an independent coefficient family.
-/
structure ProlateCanonicalSourceData where
  source : ProlateKTrialSourceData
  canonical : CanonicalData
  kTrial_eq : canonical.kTrial = source.coefficientFamily

namespace ProlateCanonicalSourceData

/-- The coefficient row stored in the production `CanonicalData` is exactly
the Fourier coefficient of the normalized projected starred sum of the same
source packet.
-/
@[simp] theorem canonical_kTrial
    (S : ProlateCanonicalSourceData) (i : PairIndex) (n : ℤ) :
    S.canonical.kTrial.kTrial i n =
      c_n i (prolateCombination (S.source.pair i))
        (S.source.eStar_memLp i) (S.source.trialNonzero i) n := by
  rw [S.kTrial_eq]
  rfl

/-- The exact selected-family expansion on the same `parent ∘ extract`
sequence.  Combined with `coefficientFamily_kTrial`, this exposes the complete
type-level path from the source packet to the production family.
-/
@[simp] theorem selectedFamily_apply
    (S : ProlateCanonicalSourceData) (k : ℕ) :
    selectedFamily (canonicalApproximation S.canonical) k =
      centeredPstarFamily S.canonical.kTrial
        (S.canonical.parent (S.canonical.extract k)) :=
  rfl

end ProlateCanonicalSourceData

#print axioms ProlateKTrialSourceData.coefficientFamily_kTrial
#print axioms ProlateKTrialSourceData.E_star_eq_of_same_m
#print axioms ProlateCanonicalSourceData.canonical_kTrial
#print axioms ProlateCanonicalSourceData.selectedFamily_apply

end Q3.RouteB.D0Pstar
```

### q3.lean.aristotle/Q3/Proofs/RouteB/D0PstarExplicitCCMLimitFourier.lean
```text
import Q3.Proofs.RouteB.D0KTrialStage2
import Mathlib.Analysis.SpecialFunctions.Gaussian.PoissonSummation
import Mathlib.Analysis.Fourier.FourierTransformDeriv

set_option linter.mathlibStandardSet false

open Complex MeasureTheory
open scoped FourierTransform

noncomputable section

namespace Q3.RouteB.D0Pstar

/-!
# Fourier invariance of the explicit CCM limiting packet

The source formula is CCM Eq. (7.1), pinned locally at
`literature/zotero/H8ULBMAL/fulltext.md:1262-1267`:

`h(x) = (pi / 2) * x^2 * (2 * pi * x^2 - 3) * exp (-pi * x^2)`.

The proof derives the second and fourth Gaussian moments from Mathlib's
Fourier/derivative identity.  It does not assume Fourier invariance as an
input.  The Poisson summation transport to `E_star` is a separate downstream
step.
-/

/-- The literal polynomial-Gaussian limiting packet of CCM Eq. (7.1). -/
noncomputable def explicitCCMLimitH (x : ℝ) : ℂ :=
  (((Real.pi / 2) * x ^ 2 * (2 * Real.pi * x ^ 2 - 3) : ℝ) : ℂ) *
    Complex.exp (-Real.pi * (x : ℂ) ^ 2)

private noncomputable def gaussianPi (x : ℝ) : ℂ :=
  Complex.exp (-Real.pi * (x : ℂ) ^ 2)

private lemma integrable_moment_gaussianPi (n : ℕ) :
    Integrable (fun x : ℝ => x ^ n • gaussianPi x) := by
  have hreal :
      Integrable (fun x : ℝ => x ^ n * Real.exp (-Real.pi * x ^ 2)) := by
    have h := integrable_rpow_mul_exp_neg_mul_sq Real.pi_pos
      (show (-1 : ℝ) < (n : ℝ) by
        exact lt_of_lt_of_le (by norm_num) (Nat.cast_nonneg n))
    simpa only [Real.rpow_natCast] using h
  have hc :
      Integrable (fun x : ℝ =>
        ((x ^ n * Real.exp (-Real.pi * x ^ 2) : ℝ) : ℂ)) :=
    hreal.ofReal
  convert hc using 1
  funext x
  unfold gaussianPi
  rw [Complex.real_smul]
  rw [show -Real.pi * (x : ℂ) ^ 2 =
      ((-Real.pi * x ^ 2 : ℝ) : ℂ) by norm_cast]
  rw [← Complex.ofReal_exp]
  exact (Complex.ofReal_mul _ _).symm

private lemma hasDerivAt_gaussianPi (x : ℝ) :
    HasDerivAt gaussianPi ((-2 * Real.pi * x : ℂ) * gaussianPi x) x := by
  unfold gaussianPi
  have h :=
    (((hasDerivAt_pow 2 (x : ℂ)).const_mul (-(Real.pi : ℂ))).cexp).comp_ofReal
  convert h using 1 <;> ring

private lemma deriv_gaussianPi :
    deriv gaussianPi = fun x : ℝ => (-2 * Real.pi * x : ℂ) * gaussianPi x := by
  funext x
  exact (hasDerivAt_gaussianPi x).deriv

private noncomputable def gaussianP2 (x : ℝ) : ℂ :=
  ((4 * Real.pi ^ 2 * x ^ 2 - 2 * Real.pi : ℝ) : ℂ)

private noncomputable def gaussianP3 (x : ℝ) : ℂ :=
  ((-8 * Real.pi ^ 3 * x ^ 3 + 12 * Real.pi ^ 2 * x : ℝ) : ℂ)

private noncomputable def gaussianP4 (x : ℝ) : ℂ :=
  ((16 * Real.pi ^ 4 * x ^ 4 - 48 * Real.pi ^ 3 * x ^ 2 +
    12 * Real.pi ^ 2 : ℝ) : ℂ)

private lemma hasDerivAt_gaussianP2 (x : ℝ) :
    HasDerivAt gaussianP2 (8 * (Real.pi : ℂ) ^ 2 * x) x := by
  unfold gaussianP2
  have h :
      HasDerivAt (fun y : ℝ => 4 * Real.pi ^ 2 * y ^ 2 - 2 * Real.pi)
        (8 * Real.pi ^ 2 * x) x := by
    convert (((hasDerivAt_pow 2 x).const_mul (4 * Real.pi ^ 2)).sub_const
      (2 * Real.pi)) using 1 <;> ring
  convert h.ofReal_comp using 1 <;> norm_cast

private lemma hasDerivAt_gaussianP3 (x : ℝ) :
    HasDerivAt gaussianP3
      (-24 * (Real.pi : ℂ) ^ 3 * (x : ℂ) ^ 2 + 12 * Real.pi ^ 2) x := by
  unfold gaussianP3
  have h :
      HasDerivAt
        (fun y : ℝ => -8 * Real.pi ^ 3 * y ^ 3 + 12 * Real.pi ^ 2 * y)
        (-24 * Real.pi ^ 3 * x ^ 2 + 12 * Real.pi ^ 2) x := by
    convert (((hasDerivAt_pow 3 x).const_mul (-8 * Real.pi ^ 3)).add
      ((hasDerivAt_id x).const_mul (12 * Real.pi ^ 2))) using 1 <;> ring
  convert h.ofReal_comp using 1 <;> norm_cast

private lemma deriv_gaussianP2_mul_gaussianPi :
    deriv (fun x => gaussianP2 x * gaussianPi x) =
      fun x => gaussianP3 x * gaussianPi x := by
  funext x
  have h := (hasDerivAt_gaussianP2 x).mul (hasDerivAt_gaussianPi x)
  change deriv (gaussianP2 * gaussianPi) x = _
  rw [h.deriv]
  unfold gaussianP2 gaussianP3
  push_cast
  ring

private lemma deriv_gaussianP3_mul_gaussianPi :
    deriv (fun x => gaussianP3 x * gaussianPi x) =
      fun x => gaussianP4 x * gaussianPi x := by
  funext x
  have h := (hasDerivAt_gaussianP3 x).mul (hasDerivAt_gaussianPi x)
  change deriv (gaussianP3 * gaussianPi) x = _
  rw [h.deriv]
  unfold gaussianP3 gaussianP4
  push_cast
  ring

private lemma iteratedDeriv_two_gaussianPi :
    iteratedDeriv 2 gaussianPi = fun x => gaussianP2 x * gaussianPi x := by
  rw [show (2 : ℕ) = 1 + 1 by norm_num, iteratedDeriv_succ, iteratedDeriv_one]
  rw [deriv_gaussianPi]
  funext x
  have ha :
      HasDerivAt (fun y : ℝ => (-2 * Real.pi * y : ℂ)) (-2 * Real.pi) x := by
    have hr : HasDerivAt (fun y : ℝ => -2 * Real.pi * y) (-2 * Real.pi) x := by
      convert (hasDerivAt_id x).const_mul (-2 * Real.pi) using 1 <;> ring
    convert hr.ofReal_comp using 1 <;> push_cast <;> ring
  have h := ha.mul (hasDerivAt_gaussianPi x)
  change deriv ((fun y : ℝ => (-2 * Real.pi * y : ℂ)) * gaussianPi) x = _
  rw [h.deriv]
  unfold gaussianP2
  push_cast
  ring

private lemma iteratedDeriv_four_gaussianPi :
    iteratedDeriv 4 gaussianPi = fun x => gaussianP4 x * gaussianPi x := by
  rw [show (4 : ℕ) = 3 + 1 by norm_num, iteratedDeriv_succ]
  rw [show (3 : ℕ) = 2 + 1 by norm_num, iteratedDeriv_succ]
  rw [iteratedDeriv_two_gaussianPi, deriv_gaussianP2_mul_gaussianPi,
    deriv_gaussianP3_mul_gaussianPi]

private noncomputable def fourierMoment2 (x : ℝ) : ℂ :=
  (-2 * (Real.pi : ℂ) * I * (x : ℂ)) ^ 2 • gaussianPi x

private noncomputable def fourierMoment4 (x : ℝ) : ℂ :=
  (-2 * (Real.pi : ℂ) * I * (x : ℂ)) ^ 4 • gaussianPi x

private lemma integrable_fourierMoment2 : Integrable fourierMoment2 := by
  have h :=
    (integrable_moment_gaussianPi 2).const_mul ((-2 * (Real.pi : ℂ) * I) ^ 2)
  convert h using 1
  funext x
  unfold fourierMoment2
  rw [Complex.real_smul]
  simp only [smul_eq_mul]
  push_cast
  ring

private lemma integrable_fourierMoment4 : Integrable fourierMoment4 := by
  have h :=
    (integrable_moment_gaussianPi 4).const_mul ((-2 * (Real.pi : ℂ) * I) ^ 4)
  convert h using 1
  funext x
  unfold fourierMoment4
  rw [Complex.real_smul]
  simp only [smul_eq_mul]
  push_cast
  ring

private lemma fourier_add_integrable {f k : ℝ → ℂ}
    (hf : Integrable f) (hk : Integrable k) :
    𝓕 (f + k) = 𝓕 f + 𝓕 k := by
  exact VectorFourier.fourierIntegral_add Real.continuous_fourierChar
    continuous_inner hf hk

private lemma fourier_const_smul (c : ℂ) (f : ℝ → ℂ) :
    𝓕 (c • f) = c • 𝓕 f := by
  exact VectorFourier.fourierIntegral_const_smul _ _ _ _ _

private lemma fourier_gaussianPi : 𝓕 gaussianPi = gaussianPi := by
  unfold gaussianPi
  simpa using (fourier_gaussian_pi (b := (1 : ℂ)) (by norm_num))

private lemma fourier_fourierMoment2 :
    𝓕 fourierMoment2 = fun x => gaussianP2 x * gaussianPi x := by
  have h := Real.iteratedDeriv_fourier (f := gaussianPi) (N := (4 : ℕ∞))
    (fun n _ => integrable_moment_gaussianPi n) (n := 2) (by norm_num)
  rw [fourier_gaussianPi, iteratedDeriv_two_gaussianPi] at h
  exact h.symm

private lemma fourier_fourierMoment4 :
    𝓕 fourierMoment4 = fun x => gaussianP4 x * gaussianPi x := by
  have h := Real.iteratedDeriv_fourier (f := gaussianPi) (N := (4 : ℕ∞))
    (fun n _ => integrable_moment_gaussianPi n) (n := 4) (by norm_num)
  rw [fourier_gaussianPi, iteratedDeriv_four_gaussianPi] at h
  exact h.symm

private noncomputable def spectralCCMLimitH : ℝ → ℂ :=
  (1 / (16 * (Real.pi : ℂ) ^ 2)) • fourierMoment4 +
    (3 / (8 * (Real.pi : ℂ))) • fourierMoment2

private lemma spectralCCMLimitH_eq_explicitCCMLimitH :
    spectralCCMLimitH = explicitCCMLimitH := by
  funext x
  unfold spectralCCMLimitH fourierMoment4 fourierMoment2 explicitCCMLimitH gaussianPi
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have hI2 : I ^ 2 = (-1 : ℂ) := by norm_num
  have hI4 : I ^ 4 = (1 : ℂ) := by norm_num
  push_cast
  field_simp [Real.pi_ne_zero]
  ring_nf
  rw [hI2, hI4]
  ring

private lemma fourier_spectralCCMLimitH :
    𝓕 spectralCCMLimitH = spectralCCMLimitH := by
  unfold spectralCCMLimitH
  calc
    𝓕 ((1 / (16 * (Real.pi : ℂ) ^ 2)) • fourierMoment4 +
        (3 / (8 * (Real.pi : ℂ))) • fourierMoment2) =
        (1 / (16 * (Real.pi : ℂ) ^ 2)) • 𝓕 fourierMoment4 +
          (3 / (8 * (Real.pi : ℂ))) • 𝓕 fourierMoment2 := by
      rw [fourier_add_integrable]
      · rw [fourier_const_smul, fourier_const_smul]
      · exact integrable_fourierMoment4.const_mul _
      · exact integrable_fourierMoment2.const_mul _
    _ = (1 / (16 * (Real.pi : ℂ) ^ 2)) •
          (fun x => gaussianP4 x * gaussianPi x) +
        (3 / (8 * (Real.pi : ℂ))) •
          (fun x => gaussianP2 x * gaussianPi x) := by
      rw [fourier_fourierMoment4, fourier_fourierMoment2]
    _ = (1 / (16 * (Real.pi : ℂ) ^ 2)) • fourierMoment4 +
        (3 / (8 * (Real.pi : ℂ))) • fourierMoment2 := by
      funext x
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      unfold gaussianP4 gaussianP2 fourierMoment4 fourierMoment2
      have hI2 : I ^ 2 = (-1 : ℂ) := by norm_num
      have hI4 : I ^ 4 = (1 : ℂ) := by norm_num
      push_cast
      field_simp [Real.pi_ne_zero]
      ring_nf
      rw [hI2, hI4]
      simp only [smul_eq_mul]
      ring

/-- The literal CCM Eq. (7.1) packet is fixed by Mathlib's plus-phase Fourier
transform.  No Fourier eigenrelation is assumed. -/
theorem fourier_explicitCCMLimitH :
    𝓕 explicitCCMLimitH = explicitCCMLimitH := by
  rw [← spectralCCMLimitH_eq_explicitCCMLimitH]
  exact fourier_spectralCCMLimitH

private lemma explicitCCMLimitH_apply (x : ℝ) :
    explicitCCMLimitH x =
      ((Real.pi ^ 2 * x ^ 4 - (3 * Real.pi / 2) * x ^ 2 : ℝ) : ℂ) *
        gaussianPi x := by
  unfold explicitCCMLimitH gaussianPi
  push_cast
  ring

private lemma fourier_scale_pos (f : ℝ → ℂ) {u : ℝ} (hu : 0 < u) (y : ℝ) :
    𝓕 (fun x => f (u * x)) y = (u⁻¹ : ℝ) • 𝓕 f (y / u) := by
  rw [Real.fourier_real_eq_integral_exp_smul,
    Real.fourier_real_eq_integral_exp_smul]
  let q : ℝ → ℂ := fun z =>
    Complex.exp (((-2 * Real.pi * (z / u) * y : ℝ) : ℂ) * I) • f z
  have hscale := Measure.integral_comp_mul_left q u
  rw [abs_of_pos (inv_pos.mpr hu)] at hscale
  calc
    _ = ∫ x : ℝ, q (u * x) := by
      apply integral_congr_ae
      filter_upwards with x
      unfold q
      congr 2
      congr 2
      push_cast
      field_simp [hu.ne']
    _ = (u⁻¹ : ℝ) • ∫ z : ℝ, q z := hscale
    _ = _ := by
      congr 1
      apply integral_congr_ae
      filter_upwards with z
      unfold q
      congr 2
      congr 2
      push_cast
      field_simp [hu.ne']

open Filter Asymptotics in
private lemma explicitCCMLimitH_decay :
    explicitCCMLimitH =O[cocompact ℝ]
      (fun x : ℝ => |x| ^ (-2 : ℝ)) := by
  have hpoly :
      (fun x : ℝ =>
        (((Real.pi ^ 2 * x ^ 4 - (3 * Real.pi / 2) * x ^ 2 : ℝ) : ℂ)))
        =O[cocompact ℝ] (fun x : ℝ => |x| ^ 4) := by
    rw [isBigO_iff]
    refine ⟨1 + Real.pi ^ 2 + 3 * Real.pi / 2, ?_⟩
    filter_upwards [tendsto_norm_cocompact_atTop.eventually
      (eventually_ge_atTop (1 : ℝ))] with x hx
    rw [Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs]
    have hx1 : 1 ≤ |x| := by simpa using hx
    have hxpow : |x| ^ 2 ≤ |x| ^ 4 := by
      nlinarith [sq_nonneg (|x| ^ 2 - 1)]
    calc
      |Real.pi ^ 2 * x ^ 4 - (3 * Real.pi / 2) * x ^ 2| ≤
          Real.pi ^ 2 * |x| ^ 4 + (3 * Real.pi / 2) * |x| ^ 2 := by
        calc
          _ ≤ |Real.pi ^ 2 * x ^ 4| + |(3 * Real.pi / 2) * x ^ 2| :=
            abs_sub _ _
          _ = _ := by
            rw [abs_mul, abs_mul, abs_pow, abs_pow, abs_sq]
            rw [abs_of_pos Real.pi_pos]
            rw [abs_of_nonneg (div_nonneg
              (mul_nonneg (by positivity) Real.pi_pos.le) (by norm_num))]
            rw [sq_abs]
      _ ≤ (1 + Real.pi ^ 2 + 3 * Real.pi / 2) * |x| ^ 4 := by
        have hp : 0 ≤ Real.pi := Real.pi_pos.le
        nlinarith [pow_nonneg (abs_nonneg x) 4]
      _ = (1 + Real.pi ^ 2 + 3 * Real.pi / 2) * |(|x| ^ 4)| := by
        rw [abs_of_nonneg (pow_nonneg (abs_nonneg x) 4)]
  have hgauss :=
    (isLittleO_exp_neg_mul_sq_cocompact (a := (Real.pi : ℂ))
      (by simpa using Real.pi_pos) (-6 : ℝ)).isBigO
  have hmul :
      (fun x : ℝ =>
        ((((Real.pi ^ 2 * x ^ 4 - (3 * Real.pi / 2) * x ^ 2 : ℝ) : ℂ))) *
          Complex.exp (-(Real.pi : ℂ) * (x : ℂ) ^ 2))
        =O[cocompact ℝ]
          (fun x : ℝ => |x| ^ 4 * |x| ^ (-6 : ℝ)) := by
    exact hpoly.mul hgauss
  have htarget :
      (fun x : ℝ => |x| ^ 4 * |x| ^ (-6 : ℝ))
        =O[cocompact ℝ] (fun x : ℝ => |x| ^ (-2 : ℝ)) := by
    rw [isBigO_iff]
    refine ⟨1, ?_⟩
    filter_upwards [tendsto_norm_cocompact_atTop.eventually
      (eventually_gt_atTop (0 : ℝ))] with x hx
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, one_mul]
    rw [abs_of_nonneg (pow_nonneg (abs_nonneg x) _),
      abs_of_nonneg (Real.rpow_nonneg (abs_nonneg x) _),
      abs_of_nonneg (Real.rpow_nonneg (abs_nonneg x) _)]
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_add (by simpa using hx)]
    norm_num
  refine (hmul.trans htarget).congr' ?_ EventuallyEq.rfl
  filter_upwards with x
  rw [explicitCCMLimitH_apply]
  rfl

open Filter Asymptotics in
private lemma rpow_decay_comp_mul_pos {f : ℝ → ℂ} {u : ℝ} (hu : 0 < u)
    (hf : f =O[cocompact ℝ] (fun x : ℝ => |x| ^ (-2 : ℝ))) :
    (fun x => f (u * x)) =O[cocompact ℝ]
      (fun x : ℝ => |x| ^ (-2 : ℝ)) := by
  have hcomp := hf.comp_tendsto (Filter.tendsto_cocompact_mul_left₀ hu.ne')
  refine hcomp.trans ?_
  rw [isBigO_iff]
  refine ⟨|u| ^ (-2 : ℝ), ?_⟩
  filter_upwards [tendsto_norm_cocompact_atTop.eventually
    (eventually_gt_atTop (0 : ℝ))] with x hx
  simp only [Function.comp_apply]
  rw [Real.norm_eq_abs, Real.norm_eq_abs]
  rw [abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _),
    abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
  rw [abs_mul, Real.mul_rpow (abs_nonneg u) (abs_nonneg x)]

open Filter Asymptotics in
private lemma poisson_scaled_sum (u : ℝ) (hu : 0 < u) :
    (∑' n : ℤ, explicitCCMLimitH (u * n)) =
      ∑' n : ℤ, (u⁻¹ : ℝ) • explicitCCMLimitH ((n : ℝ) / u) := by
  let fu : ℝ → ℂ := fun x => explicitCCMLimitH (u * x)
  have hcont : Continuous fu := by
    unfold fu
    simp_rw [explicitCCMLimitH_apply]
    unfold gaussianPi
    apply Continuous.mul
    · fun_prop
    · apply Complex.continuous_exp.comp
      fun_prop
  have hfu : fu =O[cocompact ℝ] (fun x : ℝ => |x| ^ (-2 : ℝ)) :=
    rpow_decay_comp_mul_pos hu explicitCCMLimitH_decay
  have hFfu :
      𝓕 fu =O[cocompact ℝ] (fun x : ℝ => |x| ^ (-2 : ℝ)) := by
    have hscaled :
        (fun y : ℝ => (u⁻¹ : ℝ) • explicitCCMLimitH (u⁻¹ * y))
          =O[cocompact ℝ] (fun x : ℝ => |x| ^ (-2 : ℝ)) := by
      simpa only [Pi.smul_apply] using
        (rpow_decay_comp_mul_pos (inv_pos.mpr hu)
          explicitCCMLimitH_decay).const_smul_left (u⁻¹ : ℝ)
    refine hscaled.congr' ?_ EventuallyEq.rfl
    filter_upwards with y
    rw [fourier_scale_pos explicitCCMLimitH hu y,
      fourier_explicitCCMLimitH]
    congr 2
    field_simp [hu.ne']
  have hp := Real.tsum_eq_tsum_fourier_of_rpow_decay
    hcont one_lt_two hfu hFfu 0
  calc
    _ = ∑' n : ℤ, fu (0 + n) := by simp [fu]
    _ = ∑' n : ℤ, 𝓕 fu n * fourier n (0 : UnitAddCircle) := hp
    _ = ∑' n : ℤ, 𝓕 fu n := by
      congr 1
      funext n
      simp
    _ = _ := by
      apply tsum_congr
      intro n
      rw [fourier_scale_pos explicitCCMLimitH hu n,
        fourier_explicitCCMLimitH]

private lemma explicitCCMLimitH_even (x : ℝ) :
    explicitCCMLimitH (-x) = explicitCCMLimitH x := by
  rw [explicitCCMLimitH_apply, explicitCCMLimitH_apply]
  unfold gaussianPi
  push_cast
  ring_nf

private lemma explicitCCMLimitH_zero : explicitCCMLimitH 0 = 0 := by
  rw [explicitCCMLimitH_apply]
  norm_num

open Filter Asymptotics in
private lemma summable_explicitCCMLimitH_int_mul (u : ℝ) (hu : 0 < u) :
    Summable (fun n : ℤ => explicitCCMLimitH (u * n)) := by
  have hcof := (rpow_decay_comp_mul_pos hu
    explicitCCMLimitH_decay).comp_tendsto Int.tendsto_coe_cofinite
  exact summable_of_isBigO (Real.summable_abs_int_rpow one_lt_two) hcof

private lemma int_sum_eq_two_pnat_sum (u : ℝ) (hu : 0 < u) :
    (∑' n : ℤ, explicitCCMLimitH (u * n)) =
      2 * ∑' n : ℕ+, explicitCCMLimitH ((n : ℕ) * u) := by
  let fz : ℤ → ℂ := fun n => explicitCCMLimitH (u * (n : ℝ))
  have heven : ∀ n : ℤ, fz (-n) = fz n := by
    intro n
    unfold fz
    push_cast
    rw [show u * (-(n : ℝ)) = -(u * (n : ℝ)) by ring]
    exact explicitCCMLimitH_even _
  have h := tsum_int_eq_zero_add_two_mul_tsum_pnat heven
    (summable_explicitCCMLimitH_int_mul u hu)
  have hfz0 : fz 0 = 0 := by
    unfold fz
    norm_num [explicitCCMLimitH_zero]
  have hpn :
      (∑' n : ℕ+, fz (n : ℕ)) =
        ∑' n : ℕ+, explicitCCMLimitH ((n : ℕ) * u) := by
    apply tsum_congr
    intro n
    unfold fz
    congr 1
    push_cast
    ring
  rw [hfz0, zero_add, hpn, nsmul_eq_mul] at h
  exact h

private lemma positive_sum_scaling (u : ℝ) (hu : 0 < u) :
    (∑' n : ℕ+, explicitCCMLimitH ((n : ℕ) * u)) =
      (u⁻¹ : ℝ) • ∑' n : ℕ+, explicitCCMLimitH ((n : ℕ) * u⁻¹) := by
  have hp := poisson_scaled_sum u hu
  rw [int_sum_eq_two_pnat_sum u hu] at hp
  have hinv : 0 < u⁻¹ := inv_pos.mpr hu
  rw [tsum_const_smul'' (u⁻¹ : ℝ)] at hp
  have harg :
      (fun n : ℤ => explicitCCMLimitH ((n : ℝ) / u)) =
        fun n : ℤ => explicitCCMLimitH (u⁻¹ * (n : ℝ)) := by
    funext n
    congr 1
    field_simp [hu.ne']
  rw [harg, int_sum_eq_two_pnat_sum u⁻¹ hinv] at hp
  apply mul_left_cancel₀ (show (2 : ℂ) ≠ 0 by norm_num)
  calc
    (2 : ℂ) * ∑' n : ℕ+, explicitCCMLimitH ((n : ℕ) * u) = _ := hp
    _ = 2 * ((u⁻¹ : ℝ) •
        ∑' n : ℕ+, explicitCCMLimitH ((n : ℕ) * u⁻¹)) := by
      rw [mul_comm (2 : ℂ), mul_comm (2 : ℂ)]
      exact (smul_mul_assoc (u⁻¹ : ℝ)
        (∑' n : ℕ+, explicitCCMLimitH ((n : ℕ) * u⁻¹)) (2 : ℂ)).symm

/-- Poisson summation transports the exact Fourier invariance of the literal
CCM Eq. (7.1) packet to multiplicative inversion symmetry of `E_star` on the
positive half-line. -/
theorem E_star_explicitCCMLimitH_inv (u : ℝ) (hu : 0 < u) :
    E_star explicitCCMLimitH u⁻¹ = E_star explicitCCMLimitH u := by
  unfold E_star
  rw [Real.sqrt_inv, positive_sum_scaling u hu]
  have hs : Real.sqrt u ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hu)
  have hsq : Real.sqrt u * Real.sqrt u = u := Real.mul_self_sqrt hu.le
  simp only [Complex.real_smul]
  rw [show (u⁻¹ : ℝ) = (Real.sqrt u)⁻¹ * (Real.sqrt u)⁻¹ by
    rw [← mul_inv, hsq]]
  push_cast
  field_simp

end Q3.RouteB.D0Pstar
```

### q3.lean.aristotle/Q3/Proofs/RouteB/D0PstarInversionCoefficientCrosswalk.lean
```text
import Q3.Proofs.RouteB.D0LogWindowMeasureTransport
import Q3.Proofs.RouteB.D0PstarSourceCCMOddMassReflectionDefect
import Q3.Proofs.RouteB.D0AnchorFloor

set_option linter.mathlibStandardSet false

open Complex MeasureTheory Set
open scoped ENNReal NNReal

noncomputable section

namespace Q3.RouteB.D0Pstar

/-!
# Inversion symmetry to production coefficient reflection

This file transports multiplicative inversion symmetry of an actual pointwise
comparison packet to exact reflection symmetry of the production logarithmic
Fourier coefficients.  The proof uses the existing source-locked
`du/u -> dx` transport and the exact phase identity `exp (2*pi*I*n) = 1`.

It does not assert that the finite prolate source trial is inversion even.
Instead, its final theorem supplies the non-circular comparison packet needed
by the exact odd-mass receiver.
-/

private theorem lambda_m_pos_local (i : PairIndex) :
    0 < lambda_m i := by
  rw [lambda_m]
  exact Real.sqrt_pos.2 (by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 2) i.hm))

private theorem lambda_m_sq_local (i : PairIndex) :
    lambda_m i * lambda_m i = (i.m : ℝ) := by
  rw [lambda_m, Real.mul_self_sqrt]
  exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 2) i.hm).le

private theorem exp_logWindow_reflection_div_lambda
    (i : PairIndex) (x : ℝ) :
    Real.exp (L_m i - x) / lambda_m i =
      (Real.exp x / lambda_m i)⁻¹ := by
  have hlam : 0 < lambda_m i := lambda_m_pos_local i
  have hlog : Real.exp (L_m i) = (i.m : ℝ) := by
    rw [L_m, logLength, Real.exp_log]
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 2) i.hm)
  rw [Real.exp_sub, hlog, ← lambda_m_sq_local i]
  field_simp

private theorem reflected_mode_inner
    (i : PairIndex) (n : ℤ) (g : ℝ → ℂ) (x : ℝ)
    (heven : g ((Real.exp x / lambda_m i)⁻¹) =
      g (Real.exp x / lambda_m i)) :
    inner ℂ
        (((Real.sqrt (L_m i))⁻¹ : ℂ) *
          Complex.exp
            (2 * Real.pi * Complex.I * (-n) *
              ((L_m i - x) / L_m i)))
        (g (Real.exp (L_m i - x) / lambda_m i)) =
      inner ℂ
        (((Real.sqrt (L_m i))⁻¹ : ℂ) *
          Complex.exp
            (2 * Real.pi * Complex.I * n * (x / L_m i)))
        (g (Real.exp x / lambda_m i)) := by
  rw [exp_logWindow_reflection_div_lambda i x, heven]
  rw [RCLike.inner_apply', RCLike.inner_apply']
  congr 1
  rw [map_mul, map_mul, ← Complex.exp_conj, ← Complex.exp_conj]
  congr 1
  simp only [Complex.conj_ofReal, map_mul, map_ofNat,
    Complex.conj_I, map_neg, map_intCast, map_div₀, map_sub]
  rw [show
      Complex.exp
          (2 * Real.pi * -Complex.I * (-n : ℂ) *
            (((L_m i : ℂ) - x) / L_m i)) =
        Complex.exp (2 * Real.pi * Complex.I * (n : ℂ)) *
          Complex.exp
            (2 * Real.pi * -Complex.I * (n : ℂ) *
              ((x : ℂ) / L_m i)) by
    rw [← Complex.exp_add]
    congr 1
    field_simp [(show (L_m i : ℂ) ≠ 0 by
      exact_mod_cast (logLength_pos i).ne')]
    ring]
  have hphase :
      Complex.exp (2 * Real.pi * Complex.I * (n : ℂ)) = 1 := by
    rw [show 2 * Real.pi * Complex.I * (n : ℂ) =
      (n : ℂ) * (2 * Real.pi * Complex.I) by ring]
    exact Complex.exp_int_mul_two_pi_mul_I n
  rw [hphase, one_mul]

/-- Multiplicative inversion symmetry on the literal source window implies
exact reflection symmetry of every production logarithmic Fourier
coefficient.  The hypothesis is on the physical function, not on its
coefficients. -/
theorem inner_V_neg_eq_inner_V_of_inversion_even
    (i : PairIndex) (n : ℤ) (g : ℝ → ℂ)
    (hg : MemLp g 2 (dStar.restrict (I_m i)))
    (heven : ∀ u ∈ I_m i, g u⁻¹ = g u) :
    inner ℂ (V_n_m i (-n)) (MemLp.toLp g hg) =
      inner ℂ (V_n_m i n) (MemLp.toLp g hg) := by
  have hlam : 0 < lambda_m i := lambda_m_pos_local i
  have hv (r : ℤ) :
      (V_n_m i r : ℝ → ℂ) =ᵐ[dStar.restrict (I_m i)]
        (fun u : ℝ =>
          ((Real.sqrt (L_m i))⁻¹ : ℂ) *
            Complex.exp
              (2 * Real.pi * Complex.I * r *
                (Real.log (lambda_m i * u) / L_m i))) := by
    unfold V_n_m
    apply MemLp.coeFn_toLp
  have hvneg := hv (-n)
  have hvpos := hv n
  have hgcoe :
      (MemLp.toLp g hg : ℝ → ℂ) =ᵐ[dStar.restrict (I_m i)] g := by
    apply MemLp.coeFn_toLp
  rw [MeasureTheory.L2.inner_def, MeasureTheory.L2.inner_def]
  calc
    _ = ∫ u : ℝ,
          inner ℂ
            (((Real.sqrt (L_m i))⁻¹ : ℂ) *
              Complex.exp
                (2 * Real.pi * Complex.I * (-n) *
                  (Real.log (lambda_m i * u) / L_m i)))
            (g u) ∂(dStar.restrict (I_m i)) := by
      apply integral_congr_ae
      filter_upwards [hvneg, hgcoe] with u hvu hgu
      rw [hvu, hgu]
      simp only [Int.cast_neg]
    _ = ∫ x : ℝ in Set.Icc 0 (L_m i),
          inner ℂ
            (((Real.sqrt (L_m i))⁻¹ : ℂ) *
              Complex.exp
                (2 * Real.pi * Complex.I * (-n) * (x / L_m i)))
            (g (Real.exp x / lambda_m i)) := by
      rw [← integral_comp_logWindow_dStar i]
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem
        (measurableSet_Icc : MeasurableSet (I_m i))] with u hu
      have hu_pos : 0 < u := (inv_pos.mpr hlam).trans_le hu.1
      rw [Real.exp_log (mul_pos hlam hu_pos)]
      field_simp
    _ = ∫ x : ℝ in Set.Icc 0 (L_m i),
          inner ℂ
            (((Real.sqrt (L_m i))⁻¹ : ℂ) *
              Complex.exp
                (2 * Real.pi * Complex.I * n * (x / L_m i)))
            (g (Real.exp x / lambda_m i)) := by
      rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
        MeasureTheory.integral_Icc_eq_integral_Ioc]
      rw [← intervalIntegral.integral_of_le (logLength_pos i).le,
        ← intervalIntegral.integral_of_le (logLength_pos i).le]
      let f : ℝ → ℂ := fun x =>
        inner ℂ
          (((Real.sqrt (L_m i))⁻¹ : ℂ) *
            Complex.exp
              (2 * Real.pi * Complex.I * (-n) * (x / L_m i)))
          (g (Real.exp x / lambda_m i))
      have hreflect :
          (∫ x : ℝ in (0 : ℝ)..L_m i, f (L_m i - x)) =
            ∫ x : ℝ in (0 : ℝ)..L_m i, f x := by
        simpa only [sub_self, sub_zero] using
          (intervalIntegral.integral_comp_sub_left
            (a := (0 : ℝ)) (b := L_m i) f (L_m i))
      change (∫ x : ℝ in (0 : ℝ)..L_m i, f x) = _
      rw [← hreflect]
      apply intervalIntegral.integral_congr
      intro x hx
      have hx' : x ∈ Set.Icc (0 : ℝ) (L_m i) := by
        simpa [uIcc_of_le (logLength_pos i).le] using hx
      have hu_mem : Real.exp x / lambda_m i ∈ I_m i := by
        rw [I_m]
        constructor
        · rw [inv_eq_one_div]
          exact (div_le_div_iff_of_pos_right hlam).2 (by
            rw [← Real.exp_zero]
            exact Real.exp_le_exp.mpr hx'.1)
        · exact (div_le_iff₀ hlam).2 (by
            calc
              Real.exp x ≤ Real.exp (L_m i) :=
                Real.exp_le_exp.mpr hx'.2
              _ = (i.m : ℝ) := by
                rw [L_m, logLength, Real.exp_log]
                exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 2) i.hm)
              _ = lambda_m i * lambda_m i :=
                (lambda_m_sq_local i).symm)
      simpa only [f, Complex.ofReal_sub] using
        reflected_mode_inner i n g x (heven _ hu_mem)
    _ = ∫ u : ℝ,
          inner ℂ
            (((Real.sqrt (L_m i))⁻¹ : ℂ) *
              Complex.exp
                (2 * Real.pi * Complex.I * n *
                  (Real.log (lambda_m i * u) / L_m i)))
            (g u) ∂(dStar.restrict (I_m i)) := by
      rw [← integral_comp_logWindow_dStar i]
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem
        (measurableSet_Icc : MeasurableSet (I_m i))] with u hu
      have hu_pos : 0 < u := (inv_pos.mpr hlam).trans_le hu.1
      rw [Real.exp_log (mul_pos hlam hu_pos)]
      field_simp
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [hvpos, hgcoe] with u hvu hgu
      rw [hvu, hgu]

/-- Direct production corollary: an actual inversion-even ambient packet
controls the exact literal source-row odd mass by its squared approximation
error.  No coefficient symmetry is assumed. -/
theorem sourceCCMComplexOddMass_le_norm_sub_sq_of_inversion_even
    (S : ProlateCanonicalSourceData)
    (i : PairIndex)
    (g : ℝ → ℂ)
    (hg : MemLp g 2 (dStar.restrict (I_m i)))
    (heven : ∀ u ∈ I_m i, g u⁻¹ = g u) :
    sourceCCMComplexOddMass S i ≤
      ‖(kTrial_m_N
          i
          (prolateCombination (S.source.pair i))
          (S.source.eStar_memLp i)
          (S.source.trialNonzero i) : H_m i) - MemLp.toLp g hg‖ ^ 2 := by
  apply sourceCCMComplexOddMass_le_norm_sub_sq_of_even_coefficients
  intro j
  rw [ccmModeFinite_neg]
  exact inner_V_neg_eq_inner_V_of_inversion_even
    i (ccmModeFinite i.N j) g hg heven

/-- The zero production mode turns approximation to a concrete ambient packet
into a quantitative lower bound for the unnormalized projected source trial.
The right side is the denominator used by `kTrial_m_N`; no denominator floor
is assumed. -/
theorem norm_inner_V0_sub_approximation_error_le_projected_trial_norm
    (i : PairIndex)
    (hTrial_m : ℝ → ℂ)
    (hE_star :
      MemLp (E_star hTrial_m) 2 (dStar.restrict (I_m i)))
    (f : H_m i) :
    ‖inner ℂ (V_n_m i 0) f‖ -
        ‖gTrial_m i hTrial_m hE_star - f‖ ≤
      ‖gTrial_m_N i hTrial_m hE_star‖ := by
  have hv0 : ‖V_n_m i 0‖ = 1 :=
    (V_n_m_orthonormal i).norm_eq_one 0
  have hsplit :
      inner ℂ (V_n_m i 0) f =
        inner ℂ (V_n_m i 0) (gTrial_m i hTrial_m hE_star) +
          inner ℂ (V_n_m i 0)
            (f - gTrial_m i hTrial_m hE_star) := by
    rw [inner_sub_right]
    ring
  have herror :
      ‖inner ℂ (V_n_m i 0)
          (f - gTrial_m i hTrial_m hE_star)‖ ≤
        ‖gTrial_m i hTrial_m hE_star - f‖ := by
    calc
      _ ≤ ‖V_n_m i 0‖ *
          ‖f - gTrial_m i hTrial_m hE_star‖ :=
        norm_inner_le_norm _ _
      _ = ‖gTrial_m i hTrial_m hE_star - f‖ := by
        rw [hv0, one_mul, norm_sub_rev]
  have hprojected :
      ‖inner ℂ (V_n_m i 0)
          (gTrial_m i hTrial_m hE_star)‖ ≤
        ‖gTrial_m_N i hTrial_m hE_star‖ := by
    rw [← inner_V0_gTrial_m_N_eq i hTrial_m hE_star]
    calc
      _ ≤ ‖V_n_m i 0‖ *
          ‖(gTrial_m_N i hTrial_m hE_star : H_m i)‖ :=
        norm_inner_le_norm _ _
      _ = ‖gTrial_m_N i hTrial_m hE_star‖ := by
        rw [hv0, one_mul, Submodule.coe_norm]
  rw [hsplit]
  calc
    ‖inner ℂ (V_n_m i 0)
          (gTrial_m i hTrial_m hE_star) +
        inner ℂ (V_n_m i 0)
          (f - gTrial_m i hTrial_m hE_star)‖ -
          ‖gTrial_m i hTrial_m hE_star - f‖ ≤
        ‖inner ℂ (V_n_m i 0)
          (gTrial_m i hTrial_m hE_star)‖ := by
      linarith [norm_add_le
        (inner ℂ (V_n_m i 0) (gTrial_m i hTrial_m hE_star))
        (inner ℂ (V_n_m i 0)
          (f - gTrial_m i hTrial_m hE_star))]
    _ ≤ _ := hprojected

#print axioms inner_V_neg_eq_inner_V_of_inversion_even
#print axioms sourceCCMComplexOddMass_le_norm_sub_sq_of_inversion_even
#print axioms norm_inner_V0_sub_approximation_error_le_projected_trial_norm

end Q3.RouteB.D0Pstar
```
