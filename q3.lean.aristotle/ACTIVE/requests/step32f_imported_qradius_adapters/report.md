# Step32F imported Q-radius adapters report

## Status

Closed.

## Request

Specialize the active boundary-row and penalty-box adapters to the concrete
imported Q-row radius matrices:

- `primaryK11QRadius`
- `controlK9QRadius`

This keeps the remaining numeric enclosure facts explicit while removing
unnecessary generic `QR` plumbing from downstream active-block calls.

## Declarations added

In `Q3/Proofs/PSD_CenteredCoeffCertifiedBlockImport.lean`:

- `primaryK11BoundaryGramBox_of_importedQRadius`
- `primaryK11DPenaltyBox_of_matrix_and_importedQRadius`
- `primaryK11RPenaltyBox_of_matrix_and_importedQRadius`
- `controlK9BoundaryGramBox_of_importedQRadius`
- `controlK9DPenaltyBox_of_matrix_and_importedQRadius`
- `controlK9RPenaltyBox_of_matrix_and_importedQRadius`

## Files touched

- `Q3/Proofs/PSD_CenteredCoeffCertifiedBlockImport.lean`
- `docs/INSIGHTS.md`
- `ACTIVE/requests/step32f_imported_qradius_adapters/report.md`

## Commands run

- `rg -n "primaryK11QRadius|controlK9QRadius|matrixEntrywiseAbsLe .*Q|AnalyticQ.*QRadius|QRadius.*AbsLe|BoundaryRow|boundary row|Q-row|Qrow" Q3/Proofs`
- `lake env lean Q3/Proofs/PSD_CenteredCoeffCertifiedBlockImport.lean`
- `lake build Q3.Proofs.PSD_CenteredCoeffCertifiedBlockImport`
- `rg -n "sorr[y]|admi[t]" Q3/Proofs/PSD_CenteredCoeffCertifiedBlockImport.lean ACTIVE/requests/step32f_imported_qradius_adapters/report.md`
- `git diff --check`
- `lake build Q3.Main`
- `./scripts/check_axioms.sh`

## Compile status

Closed and verified. `Q3.Proofs.PSD_CenteredCoeffCertifiedBlockImport` and
`Q3.Main` build, the focused hole scan is clean, `git diff --check` passes, and
the axiom profile remains the expected `3` standard Lean axioms plus `2`
documented project axioms.

## Remaining blocker

The concrete analytic hboxes are still open:

- `matrixEntrywiseAbsLe primaryK11AnalyticQ primaryK11Q primaryK11QRadius`
- `matrixEntrywiseAbsLe controlK9AnalyticQ controlK9Q controlK9QRadius`

The generated Gram-radius and final penalty-radius dominance facts are also
still open.

## Next smallest theorem

Add generated Q-row hbox import facts for the active `QRadius` payloads, or add
the generated Gram-radius dominance matrix if that payload already exists.
