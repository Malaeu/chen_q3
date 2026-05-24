# Step32F coefficient payload import plan report

## Status

Closed.

## Artifacts added

- `scripts/q3_psdpd_step32f_coeff_payload_plan.py`
- `docs/insights/q3_psdpd_step32f_coeff_payload_import_plan.json`
- `docs/insights/q3_psdpd_step32f_coeff_payload_import_plan_2026_05_24.md`

## Files touched

- `scripts/q3_psdpd_step32f_coeff_payload_plan.py`
- `docs/INSIGHTS.md`
- `docs/insights/q3_psdpd_step32f_coeff_payload_import_plan.json`
- `docs/insights/q3_psdpd_step32f_coeff_payload_import_plan_2026_05_24.md`
- `ACTIVE/requests/step32f_coeff_payload_import_plan/report.md`

## What changed

Added a machine-checkable import-plan generator for the accepted Step27 seed
rows.  It validates the Step22 midpoint/radius artifact hashes, CSV schemas,
matrix dimensions, duplicate entries, and missing entries.

This is not a proof generator.  It records the exact Lean payload that the next
generator/import node must produce.

## Validated blocks

- `psdpd_L3_k11_ell030_delta025_theta1e4`
  - role: primary
  - coefficient index: `Fin 23`
  - boundary row index: `Fin 2`
  - label:
    `CenteredBSplineCoeffManifestLabel.primaryK11L3Ell030Delta025Theta1e4`

- `psdpd_L3_k9_ell030_delta025_theta1e5`
  - role: control
  - coefficient index: `Fin 23`
  - boundary row index: `Fin 2`
  - label:
    `CenteredBSplineCoeffManifestLabel.controlK9L3Ell030Delta025Theta1e5`

## Required Lean payload for the next node

```text
D      = Dtheta = (1 - theta) * A - P + theta * kappa * P0
R      = Rkappa = A - kappa * P0
Q      = boundary rows matching the analytic coefficient contract
theta  = active manifest theta
cert   = FinitePenaltyCert D R Q
split  = quadForm C v = quadForm D v + theta * quadForm R v
block  = CertifiedCenteredBSplineCoeffBlock
```

## Commands run

```bash
./scripts/research_oracle.py query "Step22 interval artifacts Lean matrix import generator CertifiedCenteredBSplineCoeffBlock" -c q3_docs
./scripts/research_oracle.py query "Step32F coefficient active manifest labels generator import D R Q theta split" -c q3_docs
./scripts/research_oracle.py query "FinitePenaltyCert Dtheta Rkappa Q CSV Lean payload matrix" -c q3_docs
python3 scripts/q3_psdpd_step32f_coeff_payload_plan.py
python3 -m py_compile scripts/q3_psdpd_step32f_coeff_payload_plan.py
lake env lean Q3/Proofs/PSD_CenteredCardinalBSpline.lean
lake env lean Q3/Proofs/PSD_CertificateFamily.lean
lake build Q3.Main
rg -n "sorry|admit|exact\?" Q3/Proofs/PSD_CenteredCardinalBSpline.lean Q3/Proofs/PSD_CertificateFamily.lean Q3/Proofs/PSD_BSplineTranslationIdentities.lean
./scripts/check_axioms.sh
git diff --check
```

## Verification status

Closed.  The generator validates both accepted blocks and writes the
JSON/Markdown plan.  `python3 -m py_compile` passed.  The Lean checks for the
touched proof-adjacent files and `lake build Q3.Main` passed.  The hole scan is
clean.  `./scripts/check_axioms.sh` passed with the expected profile:
5 total axioms, consisting of 3 standard Lean axioms and 2 documented project
axioms.  `git diff --check` passed.

## Remaining blocker

The next step must generate or import actual Lean matrix terms and the
certificate fields needed to construct `CertifiedCenteredBSplineCoeffBlock`:

- `D`;
- `R`;
- `Q`;
- `theta_nonneg`;
- `FinitePenaltyCert D R Q`;
- split proof `C = D + theta R` as quadratic forms.

## Next smallest theorem/node

Build the checked Lean generator/import layer that consumes this import plan and
produces active primary/control `CertifiedCenteredBSplineCoeffBlock` values.
