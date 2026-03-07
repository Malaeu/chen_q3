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

`T0 -> G0 -> G1 -> G2 -> G3 -> G4 -> G5 -> G6 -> RH`

- `T0`: Guinand--Weil crosswalk locked.
- `G0`: domain/type repair (`R_K` vs `W_K`) and narrative alignment.
- `G1`: support upgrade inside admissible `W_K`.
- `G2`: choose one exact admissible generator family `G_K`.
- `G3`: prove positivity on that same `G_K`.
- `G4`: compact closure on each `W_K`.
- `G5`: LF lift from all `W_K` to `W`.
- `G6`: Weil linkage from positivity on `W` to RH.

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

Active compiled route:

`Q3.Main -> Q3.RH_of_shifted_atom_route -> PaperMainlineAtomRoute -> CompatibilityReduction -> Q_nonneg_t_critical`

Current `#print axioms Q3.Main.RH_of_Weil_and_Q3`:

- standard: `propext`, `Classical.choice`, `Quot.sound`
- project/classical: `Q3.Weil_criterion`
- project/scalar placeholder: `Q3.prime_term_le_at_t_critical_axiom`

This route is structurally useful, but it is **not** yet an honest closed proof of RH.

## Gate Table

| Gate | Meaning | Status | Exit criterion |
| --- | --- | --- | --- |
| `T0` | Guinand--Weil crosswalk | `done` | `Q3.Weil_criterion` and manuscript normalization stay locked |
| `G0` | domain/type repair and narrative alignment | `done` | `R_K`, `W_K`, `G_K` fixed across control docs, manuscript, and Lean-facing narrative |
| `G1` | support upgrade on admissible `W_K` | `active` | density inside admissible `W_K` or restriction-to-support replacement with explicit `Q^*` error control |
| `G2` | choose one exact admissible family `G_K` | `blocked` | one exact `G_K` fixed and tied to the `G1` route |
| `G3` | positivity on that exact `G_K` | `blocked` | positivity stated and proved on that same `G_K` |
| `G4` | compact closure on each `W_K` | `frozen` | should become routine once `G1-G3` are honest |
| `G5` | LF lift to `W` | `frozen` | available once `G4` is honest on every `W_K` |
| `G6` | Weil linkage to RH | `frozen` | available once positivity on `W` is honest |

## Current Frontier

- `G0` is closed and verified across control docs, manuscript, Lean narrative, and builds.
- `G1.1` is frozen: the first honest support-upgrade target is now a replacement theorem for restriction-level shifted approximants.
- `G1.2` is now closed: the finite reuse list and exact file pointers for the frozen `G1` statement have been extracted.
- Current active task: `G1.3` in `IMPLEMENTATION_PLAN.md`
- Current frontier: turn that finite reuse packet into one small Aristotle-ready packet or one manual proof packet without reviving the old `A1_density_WK` overclaim

## Active Milestone

Turn the finite `G1.2` reuse map into a concrete proof-search packet:

1. split the route into a support-preserving replacement packet and an A2-facing error-budget packet,
2. keep all legacy strong density claims read-only,
3. leave `G2/G3` blocked behind the resulting honest `G1` packet.

## Hard Blockers

- `A1'` is naturally a theorem on the restriction cone `R_K`, not yet on admissible `W_K`.
- The exact shape of `G1` is now frozen, but the reusable proof packet is not yet isolated cleanly from the old overstrong `A1_density_WK` route.
- The finite reuse list is now isolated, but it still needs to be turned into a single proof packet with no legacy overclaiming.
- No exact common admissible family `G_K` is fixed yet.
- No positivity theorem is proved yet on a final admissible `G_K`.
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
- 2026-03-07: first real sprint is `G0`, not a new scalar inequality.
- 2026-03-07: `G0` closed and verified by:
  `cd full && latexmk -pdf RH_Q3.tex`,
  `cd q3.lean.aristotle && lake env lean Q3/Main.lean`,
  `printf 'import Q3.Main\n#print axioms Q3.Main.RH_of_Weil_and_Q3\n' | lake env lean --stdin`.
- 2026-03-07: next active frontier is `G1.1`, i.e. freeze the first honest support-upgrade theorem on admissible `W_K`.
- 2026-03-07: `G1.1` frozen as a replacement theorem for restriction-level shifted approximants; `G1.2` is now the active reuse-mapping step.
- 2026-03-07: `G1.2` closed; reusable lemmas, structure-only templates, and do-not-reuse legacy claims have been separated cleanly.
