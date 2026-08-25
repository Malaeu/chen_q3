# SOURCE RECORD — cylinder transport L1 node (Sturm chain, node 2)

```yaml
schema: q3_codex_source_record.v1
record_for: W_TRANSPORT_L1_NODE (verdict 4c0e13ba, node 2)
body: LINUX_CLAUDE
node_path: q3.lean.aristotle/Q3/Proofs/RouteB/G6N1CylinderTransportL1Budget.lean
node_git_blob: e537ce605cff6679b8634c36da8a0ff5a31f9af0
parent_commit_at_record: 4c0e13ba3f30f6e67f0849bd18c5799f8c5a0487
authorizing_verdict: docs/routeB_bus/proshka/PROSHKA_VERDICT_GOAL058_STURM_WEIGHTED_ENERGY_AND_EDGE_CONSUMER_2026-08-25.md
public_surface:
  - ctW0, ctW4 (fixed physical cylinder profiles), ctT0, ctT4 (transport derivatives)
  - ctW0_eq_cylinder (link to committed parabolicCylinderD 0 . projectCylinderArgument)
  - cylinderTransport_L1_bounded (one absolute constant bounds both L1 masses)
conclusion: >-
  The transport derivatives (x^2 W_n')' for both fixed cylinder targets are
  explicit polynomial-times-Gaussian functions with absolute L1 mass; the
  profiles are k-independent so the constant is uniform over the selected
  family by construction.  Inputs: none.
conditionality: []
closes:
  - W_TRANSPORT_L1_NODE
opens: []
carries_open:
  - STURM_ENERGY_NODE (node 1, next)
  - WEIGHTED_CONSUMER_NODE (node 3)
  - W5_DEFECT_EDGE_TOP_LATTICE_BUDGET_BOUNDED
kernel_run:
  command: lake build (targeted + full)
  result: Build completed successfully, LAKE_EXIT 0
  axioms: [propext, Classical.choice, Quot.sound]
  sorry: none
route: CHALLENGER_NOT_RH
rh_claim: false
```
