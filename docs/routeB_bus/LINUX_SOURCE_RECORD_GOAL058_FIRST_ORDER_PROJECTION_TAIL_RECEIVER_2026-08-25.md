# SOURCE RECORD — generic first-order projection-tail receiver

```yaml
schema: q3_codex_source_record.v1
record_for: G6_S2_D0_SELECTED_PROJECTION_TAIL_DECAY_VIA_W5_FIRST_ORDER_BUDGET_GENERIC_RECEIVER
body: LINUX_CLAUDE
node_path: q3.lean.aristotle/Q3/Proofs/RouteB/D0PstarFirstOrderProjectionTailReceiver.lean
node_git_blob: 6273fd4b11822b6a81e3aa68c57da36bc857f86f
parent_commit_at_record: aea49e0ffe666a694919b14d943ca9227ea91049
authorizing_verdict: docs/routeB_bus/proshka/PROSHKA_VERDICT_GOAL058_W5_FIRST_ORDER_PROJECTION_TAIL_SUPPLIER_2026-08-25.md
public_surface:
  - selectedProjectionTailDecay_of_firstOrderCoefficientBudgetAndBandwidth
private_reconstructions:
  - w5rTailWeight (+ nonneg / le_base / summable)
  - w5rNatTail (+ nonneg / summable / tsum_le via sum_Ioo_inv_sq_le)
  - w5rTailWeight_nat_eq, w5rTailWeight_neg_eq (cast crosswalks)
  - w5rTailWeight_tsum_le (two-sided integer tail <= 4/(N+1))
conclusion: >-
  From a first-order coefficient envelope norm(c_n)^2 <= C^2 * L_m / n^2 on
  the omitted modes (eventually in k) and SelectedPhysicalBandwidthCofinal,
  the literal SelectedProjectionTailDecay follows.  Chain: unweighted
  Parseval complement identity, two-sided integer tail 4/(N+1), and the exact
  bandwidth conversion L/(N+1) = 2*pi/bandwidth, giving residual_sq <=
  8*pi*C^2/bandwidth -> 0.  SelectedPhysicalFourierEnergyControl is not
  required and its weights are untouched (retained as alternative supplier).
key_intermediate: >-
  w5rTailWeight_tsum_le: tsum over ZZ of the sector-removed inverse-square
  weight is at most 4/((N:R)+1), via Mathlib sum_Ioo_inv_sq_le on both signs.
conditionality:
  - FIRST_ORDER_COEFFICIENT_ENVELOPE (hypothesis hCoeff, open supplier)
  - SELECTED_PHYSICAL_BANDWIDTH_COFINAL (existing contract, open supplier)
closes:
  - CONSUMER_SELECTION_FOR_SELECTED_PROJECTION_TAIL_DECAY (generic receiver half)
opens: []
carries_open:
  - W5_FIRST_ORDER_COEFFICIENT_BOUND_ON_EXACT_SELECTED_SOURCE_PATH
  - EXACT_FIRST_ORDER_COEFFICIENT_CROSSWALK_TO_V_N_M
kernel_run:
  command: lake build (full)
  result: Build completed successfully, LAKE_EXIT 0
  axioms: [propext, Classical.choice, Quot.sound]
  sorry: none
route: CHALLENGER_NOT_RH
rh_claim: false
```

Forbidden list of the verdict respected: no SelectedPhysicalFourierEnergyControl
requirement, no weight change, no seam-vanishing assumption, no second-order ODE
pairing, no index identification between selectedFerrersPreAnchorIndex and
selectedPairIndex (the crosswalk is the named open gap).
