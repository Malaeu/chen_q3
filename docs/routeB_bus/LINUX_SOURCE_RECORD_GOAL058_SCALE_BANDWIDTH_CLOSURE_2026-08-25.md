# SOURCE RECORD — scale and bandwidth closed as theorems on the b1 path

```yaml
schema: q3_codex_source_record.v1
record_for: G6_S2_D0_SELECTED_FERRERS_FIRST_ORDER_BUDGET_WITH_DERIVED_SCALE_AND_BANDWIDTH
body: LINUX_CLAUDE
node_path: q3.lean.aristotle/Q3/Proofs/RouteB/G6N1SelectedFerrersScaleBandwidthClosure.lean
node_git_blob: 811fa5f04ad716bc76138f2e7f677f03c76726bc
parent_commit_at_record: d52dcc773597b89d228e8e38746effbb14c4e52a
authorizing_verdict: docs/routeB_bus/proshka/PROSHKA_VERDICT_GOAL058_POST_B1_SCALE_BANDWIDTH_ORDER_2026-08-25.md
public_surface:
  - selectedFerrersSourceScale_inverse_bounded (norm(scale^{-1}) <= 8, eventual)
  - selectedPhysicalBandwidthCofinal_of_familyCrosswalk
  - selectedProjectionTailDecay_of_selectedFerrersFirstOrderBudget_closedScaleBandwidth
private_reconstructions:
  - w5s_D0_eq (D_0(t) = exp(-t^2/4), hermite_zero)
  - w5s_error_small, w5s_paperLambda_sq/one_le
  - w5s_a0_lower (the preferred-route L2 mass argument on J=[-1/4,1/4]:
    pointwise norm(a0*h0) >= 1/2 from D_0 >= 3/4 and error < 1/4; integrate:
    1/8 <= norm(a0)^2 * int_J norm(h0)^2 <= norm(a0)^2 via unit L2 mass)
  - w5s_chi2_lower (chi2 > 3/4 eventually)
conclusion: >-
  hScale is a theorem, not owner data: norm(scale^{-1}) <= 8 eventually,
  via the exact mode-four center cancellation a4*h4(0)=3, the denominator
  bound normalizingDenominator >= |I4| = |chi2|*norm(h4(0)), and the
  mode-zero L2 mass lower bound.  Bandwidth cofinality is pure arithmetic
  on the b1-transported schedule m=N=k+2: bandwidth >= pi*sqrt(k+2) via
  log(k+2) <= 2*sqrt(k+2).  The public target theorem consumes only
  (S, hFamily, F72.6 rates, hD) and yields SelectedProjectionTailDecay S.
key_intermediate: >-
  norm(scale) >= (3/4)*norm(a0)*|chi2| >= (3/4)*(1/3)*(1/2) = 1/8.
conditionality:
  - SELECTED_FERRERS_PREANCHOR_PRODUCTION_FAMILY_CROSSWALK (hFamily, owner)
  - F72_6_MODE_AND_CHI_RATE_INPUTS
  - W5_LOG_DERIVATIVE_BUDGET_BOUNDED (hD)
closes:
  - SOURCE_SCALE_INVERSE_BOUNDED_AS_SEPARATE_INPUT (now a theorem)
  - SELECTED_PHYSICAL_BANDWIDTH_COFINAL_AS_SEPARATE_INPUT_ON_B1_PATH (now a theorem)
opens: []
carries_open:
  - SELECTED_FERRERS_PREANCHOR_PRODUCTION_FAMILY_CROSSWALK
  - F72_6_MODE_AND_CHI_RATE_INPUTS
  - W5_LOG_DERIVATIVE_BUDGET_BOUNDED (next load-bearing gap)
kernel_run:
  command: lake build (targeted + full)
  result: Build completed successfully, LAKE_EXIT 0
  axioms: [propext, Classical.choice, Quot.sound]
  sorry: none
route: CHALLENGER_NOT_RH
rh_claim: false
```
