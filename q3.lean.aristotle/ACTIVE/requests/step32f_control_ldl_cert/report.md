# Step32F control k=9 LDL certificate report

## Request

Close the control `k=9` rational LDL penalty lower-bound certificate for the
Step32F centered coefficient payload.

## Files touched

- `Q3/Proofs/PSD_CenteredCoeffPenaltyLDLImport.lean`
- `scripts/q3_psdpd_step32f_primary_ldl_cert.py`
- `docs/INSIGHTS.md`
- `ACTIVE/requests/step32f_control_ldl_cert/report.md`

## Theorems and definitions added

- `controlK9DLDLWeight_nonneg`
- `controlK9DLDL_identity`
- `controlK9DLowerBound_ldl`
- `controlK9RLDLWeight_nonneg`
- `controlK9RLDL_identity`
- `controlK9RLowerBound_ldl`
- `controlK9PenaltyLowerBoundCert_ldl`
- `controlK9FinitePenaltyCert_ldl`

## Commands run

```bash
./scripts/research_oracle.py query "primary k11 LDL control k9 finite penalty certificate" -c q3_docs
./scripts/research_oracle.py query "Step32F weighted square matrix receiver controlK9DLowerBound" -c q3_docs
./scripts/research_oracle.py query "FinitePenaltyCert primary control active block wrapper" -c q3_docs
python3 scripts/q3_psdpd_step32f_primary_ldl_cert.py
python3 -m py_compile scripts/q3_psdpd_step32f_primary_ldl_cert.py
lake env lean Q3/Proofs/PSD_CenteredCoeffPenaltyLDLImport.lean
lake build Q3.Proofs.PSD_CenteredCoeffPenaltyLDLImport
python3 scripts/q3_psdpd_step32f_coeff_payload_lean_data.py
python3 scripts/q3_psdpd_step32f_penalty_lower_bound_lean_params.py
python3 scripts/q3_psdpd_step32f_primary_ldl_cert.py
python3 -m py_compile scripts/q3_psdpd_step32f_coeff_payload_lean_data.py scripts/q3_psdpd_step32f_penalty_lower_bound_lean_params.py scripts/q3_psdpd_step32f_primary_ldl_cert.py
lake build Q3.Main
rg -n "sorry|admit|exact\\?" Q3/Proofs/PSD_PenaltyCertificate.lean Q3/Proofs/PSD_CenteredCoeffPayloadImport.lean Q3/Proofs/PSD_CenteredCoeffPenaltyImport.lean Q3/Proofs/PSD_CenteredCoeffPenaltyLDLImport.lean scripts/q3_psdpd_step32f_coeff_payload_lean_data.py scripts/q3_psdpd_step32f_penalty_lower_bound_lean_params.py scripts/q3_psdpd_step32f_primary_ldl_cert.py
git diff --check
./scripts/check_axioms.sh
```

## Compile status

`lake env lean Q3/Proofs/PSD_CenteredCoeffPenaltyLDLImport.lean` passed.

`lake build Q3.Proofs.PSD_CenteredCoeffPenaltyLDLImport` passed.

`lake build Q3.Main` passed.

The focused hole scan found no `sorry`, `admit`, or `exact?` in the touched
Lean/script files.

`git diff --check` passed.

`./scripts/check_axioms.sh` passed with the expected profile: 3 standard Lean
axioms and 2 documented project axioms.

## Result

Closed the control `k=9` D/R lower bounds by exact rational LDL certificates.
The LDL generator now reads both accepted active PASS blocks from the payload
plan/manifest and emits primary plus control rational weighted-square matrix
certificates into the same Lean import module.

## Remaining blocker

The active certified-block wrapper is still open. The current payload import
contains the matrices and penalty certificates, but the concrete
`center/weight/shift` data required by `CertifiedCenteredBSplineCoeffBlock`
still needs a small generator/import bridge.

## Next smallest theorem

Add the concrete coefficient dictionary data for the active primary/control
rows, then instantiate:

```lean
CertifiedCenteredBSplineCoeffBlock
```

for both active payloads using `primaryK11FinitePenaltyCert_ldl` and
`controlK9FinitePenaltyCert_ldl`.
