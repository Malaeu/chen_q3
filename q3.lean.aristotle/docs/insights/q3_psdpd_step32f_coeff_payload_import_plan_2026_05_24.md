# Step32F coefficient payload import plan

## Status

validated_import_plan_not_proof

## Meaning

This is a machine-checkable import plan, not a proof generator.
It validates the Step22/Step27 artifacts and records the exact Lean
payload that must be generated next.

## Blocks

| block | role | iota | rho | label |
|---|---:|---:|---:|---|
| `psdpd_L3_k11_ell030_delta025_theta1e4` | primary | `Fin 23` | `Fin 2` | `CenteredBSplineCoeffManifestLabel.primaryK11L3Ell030Delta025Theta1e4` |
| `psdpd_L3_k9_ell030_delta025_theta1e5` | control | `Fin 23` | `Fin 2` | `CenteredBSplineCoeffManifestLabel.controlK9L3Ell030Delta025Theta1e5` |

## Required Lean payload

For each block, the next generator must emit:

```text
D      = Dtheta = (1 - theta) * A - P + theta * kappa * P0
R      = Rkappa = A - kappa * P0
Q      = boundary rows matching the analytic coefficient contract
theta  = active manifest theta
cert   = FinitePenaltyCert D R Q
split  = quadForm C v = quadForm D v + theta * quadForm R v
block  = CertifiedCenteredBSplineCoeffBlock
```

## Validation

### `psdpd_L3_k11_ell030_delta025_theta1e4`

- midpoint sha256: `29d9c06befcc68ee13dbe2fe7cbad898df968ea9632f0d31c9a7d6c983411ac3`
- radius sha256: `e6112bc2202d2560f1aab4f4e4bffdcc60586652a902859e19dd122e6d491ed2`
- matrix dimensions: `{'A': [23, 23], 'P': [23, 23], 'P0': [23, 23], 'Q': [2, 23]}`
- row counts: midpoint `1633`, radius `1633`

### `psdpd_L3_k9_ell030_delta025_theta1e5`

- midpoint sha256: `cc88eb915f7dc7fd499c2ae3dcfe8f5bac9615750c92ba1c1c98559c9b711a0f`
- radius sha256: `0b3c5a067323b278a3c4fc75d8af86df4ea69dfa20c5a8472343a263e78ebea9`
- matrix dimensions: `{'A': [23, 23], 'P': [23, 23], 'P0': [23, 23], 'Q': [2, 23]}`
- row counts: midpoint `1633`, radius `1633`

## Next node

Build the checked Lean generator/import layer that turns this payload plan
into actual `CertifiedCenteredBSplineCoeffBlock` values for the active
primary/control manifest labels.
