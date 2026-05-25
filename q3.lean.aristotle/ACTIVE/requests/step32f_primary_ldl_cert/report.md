# Step32F primary k=11 LDL certificate report

## Request

Close the primary `k=11` rational LDL penalty lower-bound certificate for the
Step32F centered coefficient payload.

## Files touched

- `Q3/Proofs/PSD_PenaltyCertificate.lean`
- `Q3/Proofs/PSD_CenteredCoeffPayloadImport.lean`
- `Q3/Proofs/PSD_CenteredCoeffPenaltyImport.lean`
- `Q3/Proofs/PSD_CenteredCoeffPenaltyLDLImport.lean`
- `scripts/q3_psdpd_step32f_coeff_payload_lean_data.py`
- `scripts/q3_psdpd_step32f_penalty_lower_bound_lean_params.py`
- `scripts/q3_psdpd_step32f_primary_ldl_cert.py`
- `docs/INSIGHTS.md`

## Theorems and definitions added

- `Q3.Proofs.ratWeightedSquareMatrix`
- `Q3.Proofs.ratWeightedSquareMatrix_cast`
- `Q3.Proofs.penalty_lower_bound_of_ratWeightedSquareMatrix_identity`
- `Q3.Proofs.penalty_lower_bound_of_ratMatrixWeightedSquare_identity`
- `primaryK11DLDLWeight_nonneg`
- `primaryK11DLDL_identity`
- `primaryK11DLowerBound_ldl`
- `primaryK11RLDLWeight_nonneg`
- `primaryK11RLDL_identity`
- `primaryK11RLowerBound_ldl`
- `primaryK11PenaltyLowerBoundCert_ldl`
- `primaryK11FinitePenaltyCert_ldl`

## Commands run

```bash
python3 scripts/q3_psdpd_step32f_coeff_payload_lean_data.py
python3 scripts/q3_psdpd_step32f_penalty_lower_bound_lean_params.py
python3 scripts/q3_psdpd_step32f_primary_ldl_cert.py
python3 -m py_compile scripts/q3_psdpd_step32f_primary_ldl_cert.py
lake env lean Q3/Proofs/PSD_PenaltyCertificate.lean
lake env lean Q3/Proofs/PSD_CenteredCoeffPayloadImport.lean
lake env lean Q3/Proofs/PSD_CenteredCoeffPenaltyImport.lean
lake env lean Q3/Proofs/PSD_CenteredCoeffPenaltyLDLImport.lean
lake build Q3.Proofs.PSD_CenteredCoeffPenaltyImport
lake build Q3.Proofs.PSD_CenteredCoeffPenaltyLDLImport
lake build Q3.Main
rg -n "sorry|admit|exact\\?" Q3/Proofs/PSD_PenaltyCertificate.lean Q3/Proofs/PSD_CenteredCoeffPayloadImport.lean Q3/Proofs/PSD_CenteredCoeffPenaltyImport.lean Q3/Proofs/PSD_CenteredCoeffPenaltyLDLImport.lean scripts/q3_psdpd_step32f_coeff_payload_lean_data.py scripts/q3_psdpd_step32f_penalty_lower_bound_lean_params.py scripts/q3_psdpd_step32f_primary_ldl_cert.py
git diff --check
./scripts/check_axioms.sh
```

## Compile status

`lake env lean` passed for the touched proof files.

`lake build Q3.Proofs.PSD_CenteredCoeffPenaltyLDLImport` passed.

`lake build Q3.Main` passed.

The focused hole scan found no `sorry`, `admit`, or `exact?` in the touched
Lean/script files.

`git diff --check` passed.

`./scripts/check_axioms.sh` passed with the expected profile: 3 standard Lean
axioms and 2 documented project axioms.

## Result

Closed the primary `k=11` D/R lower bounds by exact rational LDL certificates.
The generated Lean file checks nonnegative rational LDL weights, 529 entrywise
matrix identities per D/R block, and feeds them through the matrix receiver into
the existing `FinitePenaltyLowerBoundCert` and `FinitePenaltyCert` API.

## Remaining blocker

The control `k=9` D/R lower-bound certificate is still open.

## Next smallest theorem

Generate and Lean-check the control `k=9` exact rational LDL certificate, then
add the active block wrapper consuming both primary and control
`FinitePenaltyCert` values.
