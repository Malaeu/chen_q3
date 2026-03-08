# Reviewed Note: H1 theorem skeleton

## Source

- raw files:
  - `q3.lean.aristotle/docs/incoming_notes/H1f_final_block_2026_03_08.tex`
  - `q3.lean.aristotle/docs/incoming_notes/Main_closure_H1_readyinsert_2026_03_08.tex`
  - `q3.lean.aristotle/docs/incoming_notes/Main_closure_H1_readyinsert_2026_03_08.diff`
- date: `2026-03-08`
- author / tool: `Proshka`

## Status

- review status: `reviewed`
- scope: `theorem-map`
- safe for embeddings: `yes`

## Core claim

The incoming H1 package does not propose a new route. It gives the right
drop-in theorem and proof skeleton for the already-frozen two-sided filtered
Suzuki bridge: `H1^f` should explicitly assume the two raw bulk identities
`w_{mn}(a)=\kappa(a)q_{mn}` and `w_{m,-n}(a)=\kappa(a)q_{m,-n}`, and then derive
the filtered operator equality by the common four-term stencil plus Hermitian
symmetry.

## Checked against repo

- Lean files: none
- TeX files:
  - `full/sections/Main_closure.tex`
  - `full/sections/A3/rayleigh_bridge.tex`
  - `full/sections/A3/calibration.tex`
- control docs:
  - `SESSION_ENTRY.md`
  - `q3.lean.aristotle/PROJECT_ORCHESTRATOR.md`
  - `IMPLEMENTATION_PLAN.md`
  - `q3.lean.aristotle/docs/INSIGHTS.md`

## What survived review

- `H1^f` should no longer be stated as an unexplained operator equality; the
  exact remaining burden is the raw bulk match on `(+,+)` and `(+,-)`.
- The filtered four-block identities are consequence-level statements, not the
  narrowest primary theorem target.
- The exact `J_a` pullback belongs in the theorem package as a separate metric
  input, not inside the remaining bulk proof burden.

## What was rejected or weakened

- The incoming text still used old transitional local-`L` wording for the raw
  entries and had to be adapted to the raw-compressed notation already frozen
  in the live bridge.

## Reusable theorem / lemma pointers

- `full/sections/Main_closure.tex` — `prop:H1-raw-q-formula`
- `full/sections/Main_closure.tex` — `prop:H1-raw-entry-reduction`
- `full/sections/Main_closure.tex` — `prop:H1-filtered-q-blocks`
- `full/sections/Main_closure.tex` — `cor:H1-bulk-symmetry-reduction`

## Next action

- already promoted to `docs/INSIGHTS.md`
- keep the active blocker as the raw bulk identity on `(+,+)` and `(+,-)`
- after that, attack only the finite-dimensional Suzuki cap

## Notes

This incoming package is worth keeping because it sharpens the theorem shape,
but it does not by itself prove the raw identities. The active bridge remains:
raw bulk match first, filtered consequence second, finite cap last.
