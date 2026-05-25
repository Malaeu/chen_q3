# Step32F weighted-square lower-bound receiver report

## Request

Add a Lean-checked algebraic receiver for future LDL/SOS lower-bound
certificates, so the active Step32F penalty lower-bound propositions can be
closed from exact weighted-square identities.

## Theorems / definitions added

- `Q3.Proofs.weightedSquareSum`
- `Q3.Proofs.weightedSquareSum_nonneg`
- `Q3.Proofs.penalty_lower_bound_of_weightedSquareSum_identity`
- `Q3.PSDpd.CenteredCoeffPenaltyImport.primaryK11DLowerBound_of_weightedSquareSum`
- `Q3.PSDpd.CenteredCoeffPenaltyImport.primaryK11RLowerBound_of_weightedSquareSum`
- `Q3.PSDpd.CenteredCoeffPenaltyImport.controlK9DLowerBound_of_weightedSquareSum`
- `Q3.PSDpd.CenteredCoeffPenaltyImport.controlK9RLowerBound_of_weightedSquareSum`

## Files touched

- `Q3/Proofs/PSD_PenaltyCertificate.lean`
- `Q3/Proofs/PSD_CenteredCoeffPenaltyImport.lean`
- `scripts/q3_psdpd_step32f_penalty_lower_bound_lean_params.py`
- `docs/INSIGHTS.md`
- `ACTIVE/requests/step32f_weighted_square_lower_bound_receiver/report.md`

## Commands run

```bash
lake env lean --stdin
python3 scripts/q3_psdpd_step32f_penalty_lower_bound_lean_params.py
lake env lean Q3/Proofs/PSD_PenaltyCertificate.lean
lake build Q3.Proofs.PSD_PenaltyCertificate
lake env lean Q3/Proofs/PSD_CenteredCoeffPenaltyImport.lean
lake build Q3.Proofs.PSD_CenteredCoeffPenaltyImport
lake build Q3.Main
rg -n "sorry|admit|exact\?" Q3/Proofs/PSD_PenaltyCertificate.lean Q3/Proofs/PSD_CenteredCoeffPenaltyImport.lean scripts/q3_psdpd_step32f_penalty_lower_bound_lean_params.py
./scripts/check_axioms.sh
git diff --check
```

## Status

Closed and verified.

- `lake build Q3.Proofs.PSD_CenteredCoeffPenaltyImport`: passed.
- `lake build Q3.Main`: passed.
- Hole scan on touched Lean/generator files: clean.
- `./scripts/check_axioms.sh`: passed with expected 5 axioms
  (3 standard Lean, 2 documented project axioms).
- `git diff --check`: clean.

## Remaining blocker

This node does not prove `primaryK11DLowerBound`,
`primaryK11RLowerBound`, `controlK9DLowerBound`, or
`controlK9RLowerBound`.

## Next smallest theorem

Generate and Lean-check the exact weighted-square identity for the primary
`k=11` D/R penalty forms:

```lean
Q3.Proofs.penaltyForm primaryK11D primaryK11Q primaryK11TauD v =
  primaryK11DFloor * Q3.Proofs.euclideanEnergy v +
    Q3.Proofs.weightedSquareSum wD LD v
```

and the analogous `primaryK11R` identity, with nonnegative weights.
