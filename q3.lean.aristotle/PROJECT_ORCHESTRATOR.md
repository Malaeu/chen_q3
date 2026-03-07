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

- A new architectural challenger has appeared at the `T0/G6` boundary:
  the current target cone `W_K` may be too broad for honest Weil positivity.
- This challenger does not yet replace the mainline, but it is strong enough to
  require an explicit target-cone audit before more narrative capital is spent on
  the current `W_K`-closure story.
- `G0` is closed and verified across control docs, manuscript, Lean narrative, and builds.
- `G1.1` is frozen: the first honest support-upgrade target is now a replacement theorem for restriction-level shifted approximants.
- `G1.2` is now closed: the finite reuse list and exact file pointers for the frozen `G1` statement have been extracted.
- `G1.3` is now closed: one small Aristotle-ready packet exists for the local support-replacement brick.
- `G1.4` is now closed: the prepared packet was user-approved and submitted to Aristotle as project `c315e2a4-5923-44fa-a18c-4ed90cb08375`.
- `G1.5` is now closed: `q3_docs` was rebuilt as a curated live KB and the first honest fallback theorem shape was frozen from the real `hg_mem` block.
- `G1.6` is now in flight: the updated exact?-tolerant `W_K` packet was approved and submitted to Aristotle as project `ad4c74f1-764f-4cfb-a229-2bc0b2905b67`.
- Current active task is no longer “push G1 blindly”.
  A target-cone audit now takes priority, while Aristotle project
  `ad4c74f1-764f-4cfb-a229-2bc0b2905b67` remains background work.
- Current frontier:
  1. audit whether current `W_K` / `\mathcal W` is mathematically too broad for the
     Weil criterion interface;
  2. only if the current target survives, return to the exact `W_K`-membership brick
     and then reopen the stronger `AtomCone_K_fixed` wrapper.

## Active Milestone

Turn the refreshed blocker extraction into one honest landed theorem packet:

1. keep `q3_docs` fresh as the live blocker-search base,
2. packetize the fallback theorem `atom_sum_mem_W_K_of_margin`,
3. triage project `ad4c74f1-764f-4cfb-a229-2bc0b2905b67` under the new
   `sorry`/`admit` hard-hole policy with `exact?` advisory only,
4. keep the stronger `AtomCone_K_fixed` statement as a downstream wrapper, not as the next ask.

## Hard Blockers

- Current `W_K` may be too broad: the project contract presently asks for
  positivity on all even, nonnegative, compactly supported tests, while the
  classical Weil criterion may require a narrower positive-definite /
  convolution-square cone.
- The project Archimedean density `a(ξ)` is already negative for moderate `|ξ|`,
  so broad positivity on all of current `W_K` is mathematically suspect and must
  be audited before further closure spending.
- `A1'` is naturally a theorem on the restriction cone `R_K`, not yet on admissible `W_K`.
- The completed Aristotle draft for `G1.4` is unusable: it does not integrate in the
  real project context and introduces sandbox-local fake definitions, so no theorem landed.
- There is still no integrated local theorem for the support-replacement brick.
- The exact fallback theorem `atom_sum_mem_W_K_of_margin` is now frozen, but it still exists only as an inline proof shape inside `hg_mem`, not as a standalone mainline lemma.
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
- 2026-03-07: `G1.3` closed; a small Aristotle-ready prompt now targets only the local support-replacement brick `atom_sum_mem_atomcone_fixed_of_margin` with an honest fallback.
- 2026-03-07: `G1.4` closed; `subagent_g1_support_replacement_2026_03_07.md` was approved and submitted to Aristotle as project `c315e2a4-5923-44fa-a18c-4ed90cb08375`.
- 2026-03-07: the completed `G1.4` Aristotle draft was rejected: it redefined dummy local objects and did not integrate in the real Q3 project context.
- 2026-03-07: Aristotle on this machine is already at `aristotlelib 0.7.0`, which matches the latest available release checked via `pip index versions`.
- 2026-03-07: `exact?` is no longer treated as an automatic rejection signal in the Aristotle workflow; only `sorry`/`admit` are hard holes. `exact?` is allowed if the result compiles in the real Q3 context.
- 2026-03-07: `q3_docs` refresh became a required blocker-workflow step; the collection must track live control docs, active TeX, and selected live Lean files rather than stale markdown-only snapshots.
- 2026-03-07: refreshed `q3_docs` now uses a curated live corpus after excluding stale legacy snapshots, transcript dumps, and queue artifacts.
- 2026-03-07: the next exact local theorem target is frozen as `atom_sum_mem_W_K_of_margin`; the stronger `atom_sum_mem_atomcone_fixed_of_margin` is downstream.
- 2026-03-07: `G1.6` submitted the updated exact?-tolerant packet `subagent_g1_wk_membership_2026_03_07.md` to Aristotle as project `ad4c74f1-764f-4cfb-a229-2bc0b2905b67`.
- 2026-03-07: a reviewed target-cone reset note raised a stronger blocker:
  current `W_K` / `\mathcal W` may be too broad for honest Weil positivity.
  The project now requires an explicit target-cone audit before spending more
  narrative capital on the current `W_K`-based closure route.
