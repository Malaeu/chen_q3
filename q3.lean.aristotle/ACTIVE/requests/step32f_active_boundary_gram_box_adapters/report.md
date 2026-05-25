# Step32F active boundary-Gram box adapters report

## Status

Closed.

## Request

Close the active adapter layer that turns future boundary-row hboxes for the
primary/control coefficient payloads into the boundary-Gram hboxes consumed by
the existing D/R penalty-box adapters.

## Declarations added

In `Q3/Proofs/PSD_CenteredCoeffCertifiedBlockImport.lean`:

- `primaryK11BoundaryGramBox_of_boundaryRows`
- `controlK9BoundaryGramBox_of_boundaryRows`

Each theorem proves:

```text
matrixEntrywiseAbsLe analyticQ importedQ QR
+ product-split Gram-radius dominance into GR
=> matrixEntrywiseAbsLe
     (boundaryGramMatrix analyticQ)
     (boundaryGramMatrix importedQ)
     GR
```

## Files touched

- `Q3/Proofs/PSD_CenteredCoeffCertifiedBlockImport.lean`
- `docs/INSIGHTS.md`
- `ACTIVE/requests/step32f_active_boundary_gram_box_adapters/report.md`

## Commands run

- `./scripts/research_oracle.py query "boundaryGramMatrix active primaryK11 controlK9 penalty box adapter" -c q3_docs`
- `./scripts/research_oracle.py query "matrixEntrywiseAbsLe boundary rows boundary Gram imported coefficient block" -c q3_docs`
- `lake env lean Q3/Proofs/PSD_CenteredCoeffCertifiedBlockImport.lean`
- `lake build Q3.Proofs.PSD_CenteredCoeffCertifiedBlockImport`
- `rg -n "sorr[y]|admi[t]" Q3/Proofs/PSD_CenteredCoeffCertifiedBlockImport.lean ACTIVE/requests/step32f_active_boundary_gram_box_adapters/report.md`
- `git diff --check`
- `lake build Q3.Main`
- `./scripts/check_axioms.sh`

## Compile status

Closed and verified. `Q3.Proofs.PSD_CenteredCoeffCertifiedBlockImport` and
`Q3.Main` build, the focused hole scan is clean, `git diff --check` passes, and
the axiom profile remains the expected `3` standard Lean axioms plus `2`
documented project axioms.

## Remaining blocker

The concrete generated boundary-row hboxes and numeric Gram-radius dominance
facts are still open. These adapters close the API handoff once those generated
facts are supplied.

## Next smallest theorem

Compose the active boundary-Gram adapters with the existing D/R penalty-box
adapters, or add generated Q-row enclosure imports for `primaryK11QRadius` and
`controlK9QRadius` if the payload data is already available.
