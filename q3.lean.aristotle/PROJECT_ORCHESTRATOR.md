# PROJECT ORCHESTRATOR - Q3

Updated: 2026-03-07

## Role

This file is the single source of truth for:

- gate-state,
- current frontier,
- active milestone,
- hard blockers,
- decision ledger.

It is **not** a session log and **not** a microtask queue.

## Mainline Chain

`T0-pd -> corrected cone -> A1-pd -> packet-Rayleigh-pd -> A3-pd -> A2 closure -> LF-pd -> G6 -> RH`

- `T0-pd`: Guinand--Weil crosswalk with the corrected positive-definite target cone.
- `corrected cone`: local/global positive-definite Weil cone
  `\mathcal W_K^{pd} / \mathcal W^{pd}`.
- `A1-pd`: density of the centered autocorrelation family
  `\mathcal G_K^{pd}` in `\mathcal W_K^{pd}`.
- `packet-Rayleigh-pd`: exact Toeplitz quadratic-form identity on the same
  autocorrelation packet family `\Psi * \widetilde\Psi`; this is now part of the
  public theorem package.
- `A3-pd`: packet-symbol positivity on that same exact family.
- `A2 closure`: continuity transfer on the corrected local cone.
- `LF-pd`: inductive-limit lift from all `\mathcal W_K^{pd}` to `\mathcal W^{pd}`.
- `G6`: Weil linkage from positivity on `\mathcal W^{pd}` to RH.

Broad-cone route status:

- old `W_K / \mathcal W` route is now **background only**;
- it may still produce reusable local lemmas,
- but it is no longer the public RH contract.

## Precedence Rule

If files disagree, resolve conflicts in this order:

1. `PROJECT_ORCHESTRATOR.md`
2. `docs/PAPER_MAINLINE_TRACKER.md`
3. `IMPLEMENTATION_PLAN.md`
4. `docs/INSIGHTS.md`

Interpretation:

- `PROJECT_ORCHESTRATOR.md` decides gate-state and frontier.
- `docs/PAPER_MAINLINE_TRACKER.md` decides manuscript typing and dependency map.
- `IMPLEMENTATION_PLAN.md` decides only the current execution queue.
- `docs/INSIGHTS.md` is non-normative and never overrides the other three.

## Current Compiled Route

Compiled Lean route still exported today:

`Q3.Main -> Q3.RH_of_shifted_atom_route -> PaperMainlineAtomRoute -> CompatibilityReduction -> Q_nonneg_t_critical`

Current `#print axioms Q3.Main.RH_of_Weil_and_Q3`:

- standard: `propext`, `Classical.choice`, `Quot.sound`
- project/classical: `Q3.Weil_criterion`
- project/scalar placeholder: `Q3.prime_term_le_at_t_critical_axiom`

Interpretation after `T0.1`:

- this route is structurally useful,
- it remains compiled to preserve local theorem payloads,
- but it is a **background broad-cone export**, not the public mainline contract.

## Gate Table

| Gate | Meaning | Status | Exit criterion |
| --- | --- | --- | --- |
| `T0` | Guinand--Weil crosswalk | `done` | normalization remains locked |
| `T0.1` | target-cone audit | `done` | one binary verdict written: `pivot required` |
| `T0-pd` | corrected public target cone | `done` | control docs + manuscript use the positive-definite cone as the public RH target |
| `A1-pd` | density of `\mathcal G_K^{pd}` in `\mathcal W_K^{pd}` | `frozen theorem block` | pre-square density route + autocorrelation continuity prove `\overline{\mathcal G_K^{pd}}=\mathcal W_K^{pd}` |
| `packet-Rayleigh-naive` | naive quadratic-form bridge on `\mathcal G_{K,\mathrm{Ray}}^{pd}=\operatorname{cone}\{\Phi_{B,t}|p|^2\}` | `background candidate` | keep only as an auxiliary identity; do not reuse it as the public closure family |
| `SF-pd` | same-family bridge through `\mathcal G_{K,\mathrm{Ray}}^{pd}` | `rejected as mainline route` | rejected because the naive Rayleigh family is too large and would force false broad local positivity |
| `packet-Rayleigh-pd` | exact Toeplitz form on autocorrelation packets `\Psi_c * \widetilde{\Psi_c}` | `frozen theorem block` | identify `Q^\star(t;\Psi_c * \widetilde{\Psi_c})` with `\langle T_M[S_{g,\Delta}]c,c\rangle` |
| `A3-pd` | positivity of packet symbols `S_{g,\Delta}` on the same dense packet family | `active` | prove `S_{g,\Delta}(\theta)\ge c_K>0` on the exact packet family used by `A1-pd` |
| `centered A3/RKHS` | positivity engine on centered packets | `done as analytic input` | supplies the model estimates that must be upgraded to packet-symbol positivity |
| `A2-pd` | continuity on the corrected local cone | `done as inherited input` | continuity explicitly restricted to `\mathcal W_K^{pd}` in the paper contract |
| `LF-pd` | LF lift on `\mathcal W^{pd}` | `blocked` | local positivity on every `\mathcal W_K^{pd}` is available |
| `G6` | Weil linkage to RH | `frozen` | available once positivity on `\mathcal W^{pd}` is honest |

## Current Frontier

- `T0.1` is closed with verdict `pivot required`.
- The broad target cone `W_K / \mathcal W` is too wide for the honest Weil interface.
- Current `G1.6` Aristotle work stays background only. It may still land local support lemmas,
  but it no longer determines the architectural frontier.
- New live frontier:
  1. keep `A1-pd` as the dense corrected-cone input on `\mathcal G_K^{pd}`;
  2. keep the naive Rayleigh family
     `\mathcal G_{K,\mathrm{Ray}}^{pd}=\operatorname{cone}\{\Phi_{B,t}|p|^2\}`
     background-only after the local-bump obstruction;
  3. freeze exact packet-Rayleigh on autocorrelation packets
     `\Psi_c * \widetilde{\Psi_c}`;
  4. make `A3-pd` the single live knife-edge: positivity of the packet symbol
     `S_{g,\Delta}` on the same exact packet family.

## Active Milestone

Turn the frozen corrected theorem package into a proof-ready `A3-pd` stack:

1. keep `\mathcal W_K^{pd}` and `\mathcal W^{pd}` fixed in control docs and manuscript,
2. keep `A1-pd` frozen on the dense autocorrelation packet family `\mathcal G_K^{pd}`,
3. keep exact packet-Rayleigh frozen on `\Psi_c * \widetilde{\Psi_c}`,
4. keep the naive centered Rayleigh family
   `\mathcal G_{K,\mathrm{Ray}}^{pd}` background-only after the obstruction,
5. decompose the packet symbol as
   `S_{g,\Delta}=A_{g,\Delta}-P_{g,\Delta}`,
6. make `A3-pd` explicit as one estimate package for a uniform symbol floor,
7. keep Aristotle `G1.6` as background lemma-mining only.

## Hard Blockers

- `A1'` is a density theorem on the broad restriction cone `R_K`; it does not feed
  the corrected positive-definite mainline directly.
- No proof yet closes the pre-square density route that would prove `A1-pd`.
- The naive Rayleigh family `\mathcal G_{K,\mathrm{Ray}}^{pd}` is too large to serve
  as the mainline closure family: on compacts `K<\pi` it would combine with the full
  quadratic-form meaning of Lemma 8.8 and A3 positivity to force false broad local
  positivity on even nonnegative bumps.
- Exact packet-Rayleigh on autocorrelation packets is now the honest theorem shape,
  but no proof yet establishes positivity of the associated packet symbol
  `S_{g,\Delta}` on the same dense family.
- The broad-cone compiled route in Lean still exists and may generate useful local
  lemmas, but it cannot be used as public evidence for RH after `T0.1`.
- The compiled Lean route still inherits `Q3.prime_term_le_at_t_critical_axiom`.

## Read-Only Support Docs

These files may be updated as snapshots, but they are no longer part of the active control plane:

- `docs/CHAIN_STATUS.md`
- `ACTIVE/MAIN_CHAIN_DEPS.md`

Legacy narrative surfaces are reference-only:

- centered/T5 route,
- Acceptance Gate material,
- `τ = 0` / PrimeCert / PathB status narratives,
- archived D3/IND/AB branches.

## Decision Ledger

- 2026-03-06: active compiled route reset from legacy `τ = 0` narrative to shifted-atom route.
- 2026-03-07: same-repo reset chosen; no new physical repo.
- 2026-03-07: control plane fixed to 4 canonical files:
  `PROJECT_ORCHESTRATOR.md`,
  `IMPLEMENTATION_PLAN.md`,
  `docs/PAPER_MAINLINE_TRACKER.md`,
  `docs/INSIGHTS.md`.
- 2026-03-07: gate chain fixed as
  `T0 -> G0 -> G1 -> G2 -> G3 -> G4 -> G5 -> G6 -> RH`.
- 2026-03-07: `G2` and `G3` split cleanly:
  `G2` chooses and freezes `G_K`,
  `G3` proves positivity on that exact `G_K`.
- 2026-03-07: `G0` closed and verified across control docs, manuscript, Lean narrative, and builds.
- 2026-03-07: `G1.1-G1.6` prepared the broad-cone support-upgrade branch and moved the
  Aristotle `W_K` packet into background-only status.
- 2026-03-07: a reviewed target-cone reset note raised a stronger blocker:
  current `W_K / \mathcal W` may be too broad for honest Weil positivity.
- 2026-03-07: `T0.1` audit closed with verdict `pivot required`.
  Public mainline now pivots to the positive-definite / convolution-square cone
  `\mathcal W_K^{pd} / \mathcal W^{pd}`.
- 2026-03-07: the corrected-cone theorem blocks `A1-pd` and `packet-Rayleigh`
  were refined further: they currently target two different centered families,
  so the live knife-edge is now the same-family bridge `SF-pd`.
- 2026-03-07: pushing the naive same-family route one step further exposed a
  contradiction: the family `\Phi_{B,t}|p|^2` is too large to serve as the
  closure family, because on `K<\pi` it overgenerates broad local positivity.
- 2026-03-07: the honest corrected theorem package is now:
  `A1-pd` on dense autocorrelation packets,
  exact packet-Rayleigh on `\Psi_c * \widetilde{\Psi_c}`,
  and the new hard theorem `A3-pd` asserting positivity of the packet symbol
  `S_{g,\Delta}` on that same exact family.
