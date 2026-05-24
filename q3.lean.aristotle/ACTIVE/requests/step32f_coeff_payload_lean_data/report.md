# Step32F coefficient payload Lean data report

## Status

Closed as a checked data-import layer.

This node does not close `FinitePenaltyCert` and does not construct
`CertifiedCenteredBSplineCoeffBlock`.  It deliberately stops at Lean-checked
exact matrix data plus the algebraic split needed by that future block.

## Artifacts added

- `scripts/q3_psdpd_step32f_coeff_payload_lean_data.py`
- `Q3/Proofs/PSD_CenteredCoeffPayloadImport.lean`

## Files touched

- `scripts/q3_psdpd_step32f_coeff_payload_lean_data.py`
- `Q3/Proofs/PSD_CenteredCoeffPayloadImport.lean`
- `docs/INSIGHTS.md`
- `ACTIVE/requests/step32f_coeff_payload_lean_data/report.md`

## What changed

Added a generator that consumes:

- `docs/insights/q3_psdpd_step32f_coeff_payload_import_plan.json`
- Step22 midpoint CSVs for the active primary/control blocks
- Step22 radius CSVs for the active primary/control blocks

and emits a Lean module with exact rational matrix entries.

The generated Lean module defines, for both accepted active blocks:

- midpoint `A`, `P`, `P0`, and `Q`;
- radius `A`, `P`, `P0`, and `Q` data;
- derived midpoint `C = A - P`;
- derived midpoint `R = A - kappa * P0`;
- derived midpoint `D = C - theta * R`;
- `theta_nonneg`;
- quadratic-form split:

```text
quadForm C v = quadForm D v + theta * quadForm R v
```

The split is proved structurally in Lean by
`quadForm_scaled_sub_split`, not trusted from Python arithmetic.

## Lean payload names added

- `CenteredCoeffPayloadImport.CenteredCoeffPayloadData`
- `CenteredCoeffPayloadImport.primaryK11PayloadData`
- `CenteredCoeffPayloadImport.controlK9PayloadData`
- `CenteredCoeffPayloadImport.primaryK11Split`
- `CenteredCoeffPayloadImport.controlK9Split`
- `CenteredCoeffPayloadImport.primaryK11Theta_nonneg`
- `CenteredCoeffPayloadImport.controlK9Theta_nonneg`

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

## Commands run

```bash
python3 scripts/q3_psdpd_step32f_coeff_payload_lean_data.py
python3 -m py_compile scripts/q3_psdpd_step32f_coeff_payload_lean_data.py
lake env lean Q3/Proofs/PSD_CenteredCoeffPayloadImport.lean
lake build Q3.Proofs.PSD_CenteredCoeffPayloadImport
lake build Q3.Main
rg -n "sorry|admit|exact\?" Q3/Proofs/PSD_CenteredCoeffPayloadImport.lean scripts/q3_psdpd_step32f_coeff_payload_lean_data.py Q3/Proofs/PSD_CenteredCardinalBSpline.lean Q3/Proofs/PSD_CertificateFamily.lean Q3/Proofs/PSD_BSplineTranslationIdentities.lean
./scripts/check_axioms.sh
git diff --check
```

## Verification status

Closed.

- Python generator compile: passed.
- Generated Lean module: passed.
- `lake build Q3.Proofs.PSD_CenteredCoeffPayloadImport`: passed.
- `lake build Q3.Main`: passed.
- Hole scan: clean.
- `./scripts/check_axioms.sh`: passed with expected profile:
  5 total axioms, consisting of 3 standard Lean axioms and 2 documented project
  axioms.
- `git diff --check`: passed.

## Remaining blocker

The next proof node is not another CSV/data import.  The remaining bridge is a
Lean-checked interval/SPD positivity checker that turns the midpoint/radius
payload into:

```lean
Q3.Proofs.FinitePenaltyCert D R Q
```

Only after that can the active payloads be promoted to:

```lean
CertifiedCenteredBSplineCoeffBlock
```

and then through the existing primary/control manifest adapters.

## Next smallest theorem/node

Build the finite interval penalty certificate bridge:

```text
midpoint/radius penalty guard
→ verified lower bound for penaltyForm D Q tauD
→ verified lower bound for penaltyForm R Q tauR
→ FinitePenaltyCert D R Q
→ CertifiedCenteredBSplineCoeffBlock
```
