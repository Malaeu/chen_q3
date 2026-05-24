# Step32F coefficient active manifest labels report

## Status

Closed.

## Definition names added

- `CenteredBSplineCoeffManifestLabel.primaryK11L3Ell030Delta025Theta1e4`
- `CenteredBSplineCoeffManifestLabel.controlK9L3Ell030Delta025Theta1e5`
- `CertifiedCenteredBSplineCoeffBlock.toPrimaryK11FiniteBlock`
- `CertifiedCenteredBSplineCoeffBlock.toControlK9FiniteBlock`
- `CertifiedCenteredBSplineCoeffBlock.toPrimaryK11SingletonDirectedCertFamily`
- `CertifiedCenteredBSplineCoeffBlock.toControlK9SingletonDirectedCertFamily`

## Files touched

- `Q3/Proofs/PSD_CenteredCardinalBSpline.lean`
- `docs/INSIGHTS.md`
- `ACTIVE/requests/step32f_coeff_active_manifest_labels/report.md`

## What changed

Added theorem-facing Lean labels for the two currently accepted Step27 seed
rows:

- primary: `psdpd_L3_k11_ell030_delta025_theta1e4`
- control: `psdpd_L3_k9_ell030_delta025_theta1e5`

The labels can now be used directly by future interval-backed
`CertifiedCenteredBSplineCoeffBlock` values to produce the corresponding
`CertifiedFiniteBlock` ledger row or singleton `DirectedCertFamily`.

## Evidence checked

The generated Step27 seed records both accepted rows, with `L = 3.0`,
`ell = 0.30`, `delta = 0.25`, and spline degrees `11` and `9`.

The Step22 CSV artifacts contain matrix midpoint/radius rows for `A`, `P`,
`P0`, and `Q`; they do not yet provide Lean matrix terms or the split proof
needed to construct a `CertifiedCenteredBSplineCoeffBlock`.

## Commands run

```bash
./scripts/research_oracle.py query "CertifiedFiniteBlock singleton DirectedCertFamily constructor" -c q3_docs
./scripts/research_oracle.py query "Step27 DirectedCertFamily single block refinement skeleton" -c q3_docs
./scripts/research_oracle.py query "certificate family manifest rows CertifiedFiniteBlock DirectedCertFamily" -c q3_docs
lake env lean Q3/Proofs/PSD_CenteredCardinalBSpline.lean
lake env lean Q3/Proofs/PSD_CertificateFamily.lean
lake env lean Q3/Proofs/PSD_BSplineTranslationIdentities.lean
lake build Q3.Proofs.PSD_CenteredCardinalBSpline Q3.Main
rg -n "sorry|admit|exact\?" Q3/Proofs/PSD_CenteredCardinalBSpline.lean Q3/Proofs/PSD_CertificateFamily.lean Q3/Proofs/PSD_BSplineTranslationIdentities.lean
./scripts/check_axioms.sh
git diff --check
```

## Compile status

Passed.

- `Q3/Proofs/PSD_CenteredCardinalBSpline.lean` checks.
- `Q3/Proofs/PSD_CertificateFamily.lean` checks.
- `Q3/Proofs/PSD_BSplineTranslationIdentities.lean` checks.
- `Q3.Proofs.PSD_CenteredCardinalBSpline` and `Q3.Main` build.
- Hole scan on the touched/adjacent Lean files is clean.
- `git diff --check` is clean.
- `./scripts/check_axioms.sh` passes with the expected profile: 5 total axioms,
  consisting of 3 standard Lean axioms and 2 documented project axioms.

## Downstream status

The active labels are now wired. The remaining blocker is not a label problem:
it is the generator/import layer that must produce actual Lean
`CertifiedCenteredBSplineCoeffBlock` values from interval-backed matrix data.

## Next smallest theorem/node

Build a checked generator/import layer for the active coefficient blocks:

```text
Step22 interval artifacts
→ Lean D/R/Q/theta/split data
→ CertifiedCenteredBSplineCoeffBlock
→ active manifest label adapter
```
