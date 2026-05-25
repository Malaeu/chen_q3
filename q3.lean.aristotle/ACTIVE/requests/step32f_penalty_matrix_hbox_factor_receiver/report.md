# Step32F penalty-matrix hbox factor receiver report

## Status

Closed.

## Commit

Recorded in the session final summary after commit creation.

## Request

Continue the active hbox bridge by reducing a direct `penaltyMatrix` hbox to
separate hboxes for the base matrix and the boundary Gram matrix.

## Declarations added

In `Q3/Proofs/PSD_PenaltyCertificate.lean`:

- `boundaryGramMatrix`
- `penaltyMatrix_entrywiseAbsLe_of_matrix_and_boundaryGram`

The receiver proves:

```text
matrix hbox for M
+ boundary Gram hbox for Q^T Q
=> penaltyMatrix hbox for M + tau Q^T Q
```

with entry radius `MR_ij + |tau| * GR_ij`.

## Files touched

- `Q3/Proofs/PSD_PenaltyCertificate.lean`
- `docs/INSIGHTS.md`
- `ACTIVE/requests/step32f_penalty_matrix_hbox_factor_receiver/report.md`

## Commands run

- `lake env lean Q3/Proofs/PSD_PenaltyCertificate.lean`
- `lake build Q3.Proofs.PSD_PenaltyCertificate`
- focused hole scan on the edited Lean file and report
- `git diff --check`
- `lake build Q3.Main`
- `./scripts/check_axioms.sh`

## Compile status

Closed. The edited receiver file compiles, `Q3.Main` builds, and the axiom
gate passes with the expected profile: 3 standard Lean axioms and 2 documented
project axioms.

## Remaining blocker

The active primary/control analytic hbox statements are still open. This
receiver only factors their proof obligations.

## Next smallest theorem

Specialize this factor receiver to the primary `k=11` D penalized matrix, so
future analytic D-entry and boundary-Gram enclosures feed the exact hbox
expected by `primaryK11CertifiedCoeffBlock_of_penalty_boxes`.
