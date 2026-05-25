# Step32F analytic Q boundary rows report

## Status

Closed.

## Request

Expose the active analytic `Q` boundary-row matrices as concrete exponential
rows, so the next generated Q-row hbox proof has a simple finite target.

## Declarations added

In `Q3/Proofs/PSD_CenteredCoeffDictionaryImport.lean`:

- `primaryK11AnalyticQ_zero`
- `primaryK11AnalyticQ_one`
- `controlK9AnalyticQ_zero`
- `controlK9AnalyticQ_one`

These prove that row `0` is `Real.exp (center i / 2)` and row `1` is
`Real.exp (-(center i) / 2)` for the active primary/control coefficient
dictionaries.

## Files touched

- `Q3/Proofs/PSD_CenteredCoeffDictionaryImport.lean`
- `docs/INSIGHTS.md`
- `ACTIVE/requests/step32f_analytic_q_boundary_rows/report.md`

## Commands run

- `lake env lean Q3/Proofs/PSD_CenteredCoeffDictionaryImport.lean`
- `rg -n "sorr[y]|admi[t]" Q3/Proofs/PSD_CenteredCoeffDictionaryImport.lean ACTIVE/requests/step32f_analytic_q_boundary_rows/report.md`
- `git diff --check`
- `lake build Q3.Main`
- `./scripts/check_axioms.sh`

## Compile status

Closed and verified.

- The edited dictionary import file compiles with `lake env lean`.
- `lake build Q3.Main` passes.
- Focused hole scan found no `sorry`/`admit`.
- `git diff --check` passes.
- `./scripts/check_axioms.sh` passes with the expected profile:
  `3` standard Lean axioms plus `2` documented project axioms.

## Remaining blocker

The next actual payload lock is still the generated/numeric Q-row hbox:

- `matrixEntrywiseAbsLe primaryK11AnalyticQ primaryK11Q primaryK11QRadius`
- `matrixEntrywiseAbsLe controlK9AnalyticQ controlK9Q controlK9QRadius`

After these, the existing imported-QRadius wrappers can consume the hboxes.

## Next smallest theorem

Generate or prove the finite exponential interval enclosures for the active
Q rows against the imported rational midpoint/radius payload.
