# Goal 058 — W5 quantitative shifted-energy extraction

```yaml
schema: q3_codex_task.v1
task_id: GOAL058_W5_QUANTITATIVE_SHIFTED_ENERGY_EXTRACTION
status: ACTIVE
owner_instruction: close Goal 058 nodes in physical DAG order
route: CHALLENGER_NOT_RH
parent_goal: 058_realzero_ground_diagonal_to_xi
phase_key_hash: 1c0914e2e93a49defedf2c8a8497fbdc22de993b7404e0426e4b2d6c131f9aae
scope: ONE_KERNEL_GREEN_NODE
```

## Exact node

W4 proved fixed-`k` membership in the literal shifted Archimedean form domain,
but hid the decay witness behind an existential.  Extract the actual W4
budget

```text
C_k = 2 * (L1 packet mass + (derivative budget + repaired jump budget)/(2*pi))
```

and prove both:

1. the pointwise ordinary-Fourier bound `norm <= C_k / (1 + |t|)`;
2. the literal production shifted sesquilinear energy is bounded by a single
   index-independent integrable envelope times `C_k^2`.

The theorem must consume the production selected-Ferrers Abel limit, the W1
a.e. ordinary/synthesized Fourier crosswalk, the repaired W4 jump ledger, and
the literal shifted Archimedean symbol.  It may not introduce a surrogate
energy or a fitted constant.

## Exit and next gap

```text
CLOSES: W5_QUANTITATIVE_SHIFTED_ENERGY_EXTRACTION
OPENS: W5_COFINAL_PACKET_BUDGET_RATE
```

This task does not prove a cofinal rate for `C_k`, a Gamma source rate, the
polarized near-radical rate, G3, G1, Route promotion, or RH.

## Gates

```text
lake env lean Q3/Proofs/RouteB/G6N1SelectedFerrersQuantitativeShiftedRootEnergy.lean
lake build Q3.Proofs.RouteB.G6N1SelectedFerrersQuantitativeShiftedRootEnergy
scripts/q3_check.sh Q3/Proofs/RouteB/G6N1SelectedFerrersQuantitativeShiftedRootEnergy.lean
```

Every public declaration must print exactly
`[propext, Classical.choice, Quot.sound]`.
