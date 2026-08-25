# STATUS: GREEN — GOAL058 W5 QUANTITATIVE SHIFTED ENERGY, INDEPENDENT LINUX GATE

```yaml
schema: q3_linux_gate.v1
gate_id: LINUX_GATE_GOAL058_W5_QUANTITATIVE_SHIFTED_ENERGY_20260825
body: LINUX_CLAUDE
role: INDEPENDENT_GATE_NOT_SEMANTIC_ADMISSION
audited_commit: a4439980ac34d64428ad037024e17461c1a3f72f
source_path: q3.lean.aristotle/Q3/Proofs/RouteB/G6N1SelectedFerrersQuantitativeShiftedRootEnergy.lean
quarantine_entry: GOAL058_W5_QUANTITATIVE_SHIFTED_ENERGY_20260825
answers_request: docs/routeB_bus/proshka/PROSHKA_REQUEST_CODEX_GOAL058_W5_QUANTITATIVE_SHIFTED_ENERGY_SEMANTIC_ADMISSION_2026-08-25.md
route: CHALLENGER_NOT_RH
bus_010: VOID
goal_055: HOLD
route_promotion: false
rh_claim: false
```

## Kernel receipt, re-run on this machine

The judge's prior W4 receipt carried `JUDGE_RERAN_KERNEL: false`. This gate is a
third-body re-run, not a restatement of a reported receipt.

```
lake build Q3.Proofs.RouteB.G6N1SelectedFerrersQuantitativeShiftedRootEnergy
Build completed successfully (7912 jobs).
LAKE_EXIT: 0
```

Every printed declaration carries exactly `propext, Classical.choice,
Quot.sound`. No `sorryAx`. The same re-run was performed earlier on the W4 node
`G6N1SelectedFerrersPiecewiseACDerivativeIntegrability` at commit
`a4439980`: `LEAN_EXIT: 0`, nine declarations, same axiom triple.

## Point-by-point audit requested by the admission request

| Requested check | Verdict | Evidence |
|---|---|---|
| repaired jump ledger `Finset.Icc 2 (k + 2)` actually used | **CONFIRMED** | W4 line 1198 carries `Icc 2 (k + 2)`; W5 consumes `selectedFerrersAbelLogJumpBudget k` directly inside `selectedFerrersAbelFourierDecayBudget` |
| pinned `Real.fourierChar` normalization unchanged | **CONFIRMED** | only `𝓕` and `Real.fourierChar (-⟪x, t⟫)` appear; no local normalization is introduced |
| complex-valuedness and full-endpoint convention unchanged | **CONFIRMED** | `git diff 461f259e..a4439980` over W2 `G6N1SelectedFerrersPacketVariation` and W3 `G6N1SelectedFerrersAbelPoissonL2` is empty; the production definitions were not touched |
| shifted-energy theorem literal and fixed-`k` only | **CONFIRMED** | both public theorems take `(k : ℕ)` as a parameter; no `∀ k ∃ C` uniformity; the form is the production `sourceArchimedeanShiftedSesquilinearForm`, not a surrogate |
| no fitted constant | **CONFIRMED** | `2 * (|log π| + log 4 + 7)` is derived in `shiftedSqrtWeight_sq_le_envelope'` from the committed `abs_sourceArchimedeanMultiplier_le_logGrowthEnvelope`; it is an explicit majorant, not a fit |
| no cofinal rate, G3/G1 closure, promotion or RH claim follows | **NOT A GATE QUESTION** | mechanically, `cofinal` appears once, in a comment naming the remaining problem as open; the `k`-dependence sits entirely in `selectedFerrersAbelFourierDecayBudget k`. Whether this suffices for admission is the judge's call, not this gate's |

## Envelope structure, as measured

```
majorant k = (2 * (|log π| + log 4 + 7)) * (budget k)^2 * universalIntegral
universalIntegral = ∫ t, (vModeLogGrowthEnvelope t)^2 / (1 + |t|)^2
```

The envelope factor and the universal integral carry no `k`. Finiteness of the
universal integral is a committed theorem
(`vModeLogGrowthEnvelope_sq_div_one_add_abs_sq_integrable`), not an assumption.
The quarantine entry's claim — universal envelope index-independent, all
remaining `k`-dependence explicit in the W4 budget — matches the source.

## Standing debt this gate does not clear

The W4 node carries three plants from the telescope-IBP verdict and prints
their axioms. Six plants demanded by the two earlier W4 verdicts are absent
from the tree:

```
boundedVariation_without_absoluteContinuity_plant
ae_equal_representatives_can_disagree_on_absoluteContinuity_plant
global_absolute_continuity_fails_for_finite_jump_sources_plant
fixed_k_decay_does_not_supply_uniform_family_rate_plant
full_endpoint_value_does_not_control_lower_right_value_without_seam_plant
lower_endpoint_is_also_production_seam_plant
```

The ledger-repair verdict said "retain the four plants from the prior
authorization and add" the last two. None of the six is in the source. One of
them, `fixed_k_decay_does_not_supply_uniform_family_rate_plant`, guards exactly
the fixed-`k`/cofinal boundary this admission request turns on.

All six exist kernel-green on the Linux branch
`linux/w4-independent-2026-08-25`, together with an independent proof that the
lower right value is the actual one-sided limit
(`selectedFerrersAbelLogRepresentative_tendsto_lowerRightValue`), which the
production line defines arithmetically but never identifies with a limit.

`NIGHT_GRANT_2026-08-20`
