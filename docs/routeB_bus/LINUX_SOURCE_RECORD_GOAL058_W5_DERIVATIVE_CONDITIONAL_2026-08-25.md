# SOURCE RECORD — W5 derivative reduction and conditional closure

```yaml
schema: q3_codex_source_record.v1
record_for: W5_DERIVATIVE_CONDITIONAL_CLOSURE
body: LINUX_CLAUDE
node_path: q3.lean.aristotle/Q3/Proofs/RouteB/G6N1SelectedFerrersW5DerivativeBudgetRate.lean
node_git_blob: 7b39ee0efffae6edcbfbbda29d131d1563bff998
parent_commit_at_record: bceb7d06c7ae658ae1a9792070162673f5edfee6
authorizing_verdict: docs/routeB_bus/proshka/PROSHKA_VERDICT_GOAL058_W5_DERIVATIVE_AFTER_D2_2026-08-25.md
public_surface:
  - selectedFerrersAbelFourierDecayBudget_bounded_of_modeAndChiRates
private_reconstructions:
  - w5d_packet_differentiableAt_of_pos_ne (and its window/outside halves)
  - w5d_packet_windowFiniteSupport
  - w5d_rep_eq_finite
  - w5d_Q
  - w5d_hasDerivAt_of_no_seam
  - w5d_seamSet, w5d_seamSet_measure_zero
  - w5d_budget_reduction
conclusion: >-
  Given the F72.6 mode and chi rate inputs and the open supplier
  W5_LOG_DERIVATIVE_BUDGET_BOUNDED as the hypothesis hD, the full Fourier
  budget C_k is eventually bounded by an explicit constant assembled from the
  L1, endpoint and seam nodes.  Consumer strength exactly: BOUNDED_CK_SUFFICES.
key_intermediate: >-
  Exact signed derivative decomposition at every seam-free interior point
  (D2, no C1 input), and the authorized a.e. reduction of the budget to
  (1/2) L1 + the weighted signed Q-comb integral (D3a).
conditionality:
  - F72_6_MODE_AND_CHI_RATE_INPUTS
  - W5_LOG_DERIVATIVE_BUDGET_BOUNDED (open supplier, carried as hypothesis)
closes:
  - W5_DERIVATIVE_BUDGET_REDUCTION
  - W5_CONDITIONAL_CK_BOUNDED_ASSEMBLY
opens: []
carries_open:
  - W5_LOG_DERIVATIVE_BUDGET_BOUNDED
  - DISCRETE_CONTINUUM_ENERGY_BRIDGE (small node, per the consumer caveat)
route: CHALLENGER_NOT_RH
rh_claim: false
```
