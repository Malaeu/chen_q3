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
- radius sha256: `15a1a7b988c52b46dcfa728922ad70ca9a7fb5cb497d7b90fbbb9a4d737198fe`
- matrix dimensions: `{'A': [23, 23], 'P': [23, 23], 'P0': [23, 23], 'Q': [2, 23]}`
- row counts: midpoint `1633`, radius `1633`

### `psdpd_L3_k9_ell030_delta025_theta1e5`

- midpoint sha256: `cc88eb915f7dc7fd499c2ae3dcfe8f5bac9615750c92ba1c1c98559c9b711a0f`
- radius sha256: `4f94d7a8508d081223961bd1f0c2a210f2624aedbbaeddd62b8d517aaeb10f37`
- matrix dimensions: `{'A': [23, 23], 'P': [23, 23], 'P0': [23, 23], 'Q': [2, 23]}`
- row counts: midpoint `1633`, radius `1633`

## Next node

Build the checked Lean generator/import layer that turns this payload plan
into actual `CertifiedCenteredBSplineCoeffBlock` values for the active
primary/control manifest labels.
