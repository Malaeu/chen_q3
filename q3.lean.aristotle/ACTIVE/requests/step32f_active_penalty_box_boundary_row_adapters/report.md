# Step32F active penalty-box boundary-row adapters report

## Status

Closed.

## Request

Compose the active boundary-Gram adapters with the existing D/R penalty-box
adapters so future generated boundary-row hboxes can feed active penalty-box
hypotheses directly.

## Declarations added

In `Q3/Proofs/PSD_CenteredCoeffCertifiedBlockImport.lean`:

- `primaryK11DPenaltyBox_of_matrix_and_boundaryRows`
- `primaryK11RPenaltyBox_of_matrix_and_boundaryRows`
- `controlK9DPenaltyBox_of_matrix_and_boundaryRows`
- `controlK9RPenaltyBox_of_matrix_and_boundaryRows`

Each theorem proves:

```text
base matrix hbox
+ boundary-row hbox
+ Gram-radius dominance
+ penalty-radius dominance
=> active D/R penalty-box hbox
```

## Files touched

- `Q3/Proofs/PSD_CenteredCoeffCertifiedBlockImport.lean`
- `docs/INSIGHTS.md`
- `ACTIVE/requests/step32f_active_penalty_box_boundary_row_adapters/report.md`

## Commands run

- `lake env lean Q3/Proofs/PSD_CenteredCoeffCertifiedBlockImport.lean`
- `lake build Q3.Proofs.PSD_CenteredCoeffCertifiedBlockImport`
- `rg -n "sorr[y]|admi[t]" Q3/Proofs/PSD_CenteredCoeffCertifiedBlockImport.lean ACTIVE/requests/step32f_active_penalty_box_boundary_row_adapters/report.md`
- `git diff --check`
- `lake build Q3.Main`
- `./scripts/check_axioms.sh`

## Compile status

Closed and verified. `Q3.Proofs.PSD_CenteredCoeffCertifiedBlockImport` and
`Q3.Main` build, the focused hole scan is clean, `git diff --check` passes, and
the axiom profile remains the expected `3` standard Lean axioms plus `2`
documented project axioms.

## Remaining blocker

Concrete generated enclosure facts are still open: Q-row hboxes, Gram-radius
dominance, and base D/R matrix hboxes.

## Next smallest theorem

Add the generated Q-row hbox import facts for `primaryK11QRadius` and
`controlK9QRadius`, or add a concrete wrapper that consumes those facts when
the generator payload is available.
