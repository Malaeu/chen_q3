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

`T0-pd -> corrected cone -> A1-pd -> packet-Rayleigh -> centered A3/RKHS -> SF-pd -> A2 closure -> LF-pd -> G6 -> RH`

- `T0-pd`: Guinand--Weil crosswalk with the corrected positive-definite target cone.
- `corrected cone`: local/global positive-definite Weil cone
  `\mathcal W_K^{pd} / \mathcal W^{pd}`.
- `A1-pd`: density of the centered autocorrelation family
  `\mathcal G_{K,\mathrm{dens}}^{pd}` in `\mathcal W_K^{pd}`.
- `packet-Rayleigh`: exact identification of `Q^\star(t;\Phi_{B,t,p})` with the
  Toeplitz/RKHS quadratic form on the centered Rayleigh family
  `\mathcal G_{K,\mathrm{Ray}}^{pd}`.
- `SF-pd`: same-family bridge between the dense family and the positive family,
  or an enlarged operator model acting directly on the dense family.
- `centered A3/RKHS`: positivity engine on centered packets.
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
| `A1-pd` | density of `\mathcal G_{K,\mathrm{dens}}^{pd}` in `\mathcal W_K^{pd}` | `active input` | pre-square density route + autocorrelation continuity prove `\overline{\mathcal G_{K,\mathrm{dens}}^{pd}}=\mathcal W_K^{pd}` |
| `packet-Rayleigh` | quadratic-form bridge on `\mathcal G_{K,\mathrm{Ray}}^{pd}` | `active input` | exact theorem statement on `\Phi_{B,t,p}` is frozen and later proved |
| `SF-pd` | same-family bridge on the corrected cone | `active` | either `\overline{\operatorname{cone}(\mathcal G_{K,\mathrm{Ray}}^{pd})}=\mathcal W_K^{pd}` or an enlarged operator model acts directly on `\mathcal G_{K,\mathrm{dens}}^{pd}` |
| `centered A3/RKHS` | positivity engine on centered packets | `done as analytic input` | reused on the exact packet family chosen by `A1-pd` |
| `A2-pd` | continuity on the corrected local cone | `done as inherited input` | continuity explicitly restricted to `\mathcal W_K^{pd}` in the paper contract |
| `LF-pd` | LF lift on `\mathcal W^{pd}` | `blocked` | local positivity on every `\mathcal W_K^{pd}` is available |
| `G6` | Weil linkage to RH | `frozen` | available once positivity on `\mathcal W^{pd}` is honest |

## Current Frontier

- `T0.1` is closed with verdict `pivot required`.
- The broad target cone `W_K / \mathcal W` is too wide for the honest Weil interface.
- Current `G1.6` Aristotle work stays background only. It may still land local support lemmas,
  but it no longer determines the architectural frontier.
- New live frontier:
  1. freeze the density family `\mathcal G_{K,\mathrm{dens}}^{pd}` and the
     Rayleigh family `\mathcal G_{K,\mathrm{Ray}}^{pd}`;
  2. record the exact same-family blocker between them;
  3. choose the first honest closure route:
     same-family density on the Rayleigh family, or enlarged operator model on
     the dense family.

## Active Milestone

Turn the corrected target-cone audit into the honest post-pivot contract:

1. freeze `\mathcal W_K^{pd}` and `\mathcal W^{pd}` in control docs and manuscript,
2. freeze the density family `\mathcal G_{K,\mathrm{dens}}^{pd}` and the
   Rayleigh family `\mathcal G_{K,\mathrm{Ray}}^{pd}`,
3. replace the old missing-theorem framing
   (`same shifted family dense and positive`)
   by the corrected same-family bridge `SF-pd`,
4. keep Aristotle `G1.6` as background lemma-mining only.

## Hard Blockers

- `A1'` is a density theorem on the broad restriction cone `R_K`; it does not feed
  the corrected positive-definite mainline directly.
- No proof yet closes the pre-square density route that would prove `A1-pd`.
- No proof yet closes packet-Rayleigh on the centered Rayleigh family in live Q3.
- No proof yet identifies the dense family with the positive family, nor supplies
  an enlarged operator model that acts directly on the dense family.
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
