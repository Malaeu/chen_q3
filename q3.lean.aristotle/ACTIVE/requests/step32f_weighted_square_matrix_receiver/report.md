# Step32F weighted-square matrix receiver report

## Request

Prepare the lower-bound receiver for generated 23-by-23 rational LDL/SOS
certificates by accepting a matrix-level weighted-Gram identity.

## Theorems / definitions added

- `Q3.Proofs.weightedSquareMatrix`
- `Q3.Proofs.boundaryEnergy_eq_quadForm_gram`
- `Q3.Proofs.weightedSquareSum_eq_quadForm_weightedSquareMatrix`
- `Q3.Proofs.quadForm_pointwise_smul`
- `Q3.Proofs.quadForm_pointwise_add`
- `Q3.Proofs.quadForm_diagonal_floor`
- `Q3.Proofs.quadForm_pointwise_congr`
- `Q3.Proofs.penalty_lower_bound_of_weightedSquareMatrix_identity`
- `primaryK11DLowerBound_of_weightedSquareMatrix`
- `primaryK11RLowerBound_of_weightedSquareMatrix`
- `controlK9DLowerBound_of_weightedSquareMatrix`
- `controlK9RLowerBound_of_weightedSquareMatrix`

## Files touched

- `Q3/Proofs/PSD_PenaltyCertificate.lean`
- `Q3/Proofs/PSD_CenteredCoeffPenaltyImport.lean`
- `scripts/q3_psdpd_step32f_penalty_lower_bound_lean_params.py`
- `docs/INSIGHTS.md`
- `ACTIVE/requests/step32f_weighted_square_matrix_receiver/report.md`

## Commands run

```bash
./scripts/research_oracle.py query "weighted square lower bound receiver primaryK11 DLowerBound SOS LDL exact identity" -c q3_docs
./scripts/research_oracle.py query "FinitePenaltyLowerBoundCert weightedSquareSum penaltyForm euclideanEnergy primaryK11" -c q3_docs
./scripts/research_oracle.py query "Step32F PenaltyLowerBoundParamsImport next lower-bound generator LDL SOS" -c q3_docs
python3 scripts/q3_psdpd_step32f_penalty_lower_bound_lean_params.py
lake env lean Q3/Proofs/PSD_PenaltyCertificate.lean
lake build Q3.Proofs.PSD_PenaltyCertificate
lake env lean Q3/Proofs/PSD_CenteredCoeffPenaltyImport.lean
lake build Q3.Proofs.PSD_CenteredCoeffPenaltyImport
lake build Q3.Main
rg -n "sorry|admit|exact\?" Q3/Proofs/PSD_PenaltyCertificate.lean Q3/Proofs/PSD_CenteredCoeffPenaltyImport.lean scripts/q3_psdpd_step32f_penalty_lower_bound_lean_params.py || true
git diff --check
./scripts/check_axioms.sh
```

## Status

Closed and verified.

- `Q3.Proofs.PSD_PenaltyCertificate` builds.
- `Q3.Proofs.PSD_CenteredCoeffPenaltyImport` builds.
- `Q3.Main` builds.
- Hole scan is clean for the touched Lean/generator files.
- `git diff --check` is clean.
- `check_axioms.sh` passes with the expected profile: 5 total axioms, consisting
  of 3 standard Lean axioms and 2 documented project axioms.

## Remaining blocker

This node still does not prove `primaryK11DLowerBound`,
`primaryK11RLowerBound`, `controlK9DLowerBound`, or
`controlK9RLowerBound`.

## Next smallest theorem

Generate the primary `k=11` D/R rational LDL data and prove the pointwise
matrix identities:

```lean
primaryK11D i j + primaryK11TauD * (∑ r : BoundaryIndex2, primaryK11Q r i * primaryK11Q r j)
  =
primaryK11DFloor * (if i = j then (1 : Real) else 0)
  + Q3.Proofs.weightedSquareMatrix wD LD i j
```

and the analogous `primaryK11R` identity, with nonnegative weights.
