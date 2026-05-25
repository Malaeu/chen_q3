# Step32F boundary-Gram hbox receiver report

## Status

Closed.

## Request

Close the generic algebraic receiver that turns an entrywise boundary-row hbox
into an entrywise hbox for the boundary Gram matrix `Q^T Q`.

## Declarations added

In `Q3/Proofs/PSD_PenaltyCertificate.lean`:

- `boundaryGramMatrix_entrywiseAbsLe_of_matrix`

The theorem proves:

```text
matrixEntrywiseAbsLe Q Q0 QR
=> matrixEntrywiseAbsLe (Q^T Q) (Q0^T Q0) GR
```

with

```text
GR_ij = sum_r QR_ri * (abs Q0_rj + QR_rj) + abs Q0_ri * QR_rj
```

## Files touched

- `Q3/Proofs/PSD_PenaltyCertificate.lean`
- `docs/INSIGHTS.md`
- `ACTIVE/requests/step32f_boundary_gram_hbox_receiver/report.md`

## Commands run

- `lake env lean Q3/Proofs/PSD_PenaltyCertificate.lean`
- `lake build Q3.Proofs.PSD_PenaltyCertificate`
- `rg -n "sorr[y]|admi[t]" Q3/Proofs/PSD_PenaltyCertificate.lean ACTIVE/requests/step32f_boundary_gram_hbox_receiver/report.md`
- `git diff --check`
- `lake build Q3.Main`
- `./scripts/check_axioms.sh`

## Compile status

Closed and verified.  `Q3.Proofs.PSD_PenaltyCertificate` and `Q3.Main`
build, the focused hole scan is clean, `git diff --check` passes, and the axiom
profile remains the expected `3` standard Lean axioms plus `2` documented
project axioms.

## Remaining blocker

Concrete active boundary-row hboxes and numeric radius-dominance lemmas are
still open. This receiver only closes the generic `Q -> Q^T Q` algebra.

## Next smallest theorem

Add active boundary-Gram adapters for primary `k=11` and control `k=9` that
feed generated boundary-row hboxes and radius dominance into the D/R penalty
box adapters.
