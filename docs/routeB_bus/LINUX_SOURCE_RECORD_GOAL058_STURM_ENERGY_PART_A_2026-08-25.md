# SOURCE RECORD — Sturm energy node, part A (abstract identity + cylinder ODEs)

```yaml
schema: q3_codex_source_record.v1
record_for: STURM_ENERGY_NODE (verdict 4c0e13ba, node 1, part A)
body: LINUX_CLAUDE
node_path: q3.lean.aristotle/Q3/Proofs/RouteB/G6N1SturmWeightedEnergyIdentity.lean
node_git_blob: c5e83a93978148e0a28e7c1adb43377eab31014c
parent_commit_at_record: 2b630d145079d0a66b323fda59d484c58b699a0f
authorizing_verdict: docs/routeB_bus/proshka/PROSHKA_VERDICT_GOAL058_STURM_WEIGHTED_ENERGY_AND_EDGE_CONSUMER_2026-08-25.md
public_surface:
  - sturm_weighted_energy_identity: for any g differentiable on the open
    window with weighted-flux derivative r and ZERO FLUX LIMITS at both
    singular endpoints, INT (lam^2-x^2) gd^2 = - INT r*g.  The boundary
    enters only through the flux limits — no trace, no endpoint value.
  - ctW0d/ctW0dd/ctW4d/ctW4dd + hasDerivAt chains
  - ctW0_cylinder_eigenrelation (-W0'' + 4pi^2x^2 W0 = 2pi W0)
  - ctW4_cylinder_eigenrelation (-W4'' + 4pi^2x^2 W4 = 18pi W4)
conclusion: >-
  The energy identity is proved by FTC on a monotone exhaustion
  Ioc(a_n,b_n) -> Ioo(-lam,lam) (tendsto_setIntegral_of_monotone) with the
  flux limits killing the boundary; the two fixed cylinder profiles carry
  their exact eigenvalues 2pi and 18pi = 4pi(n+1/2), n = 0, 4.
conditionality: []
closes:
  - STURM_ENERGY_NODE part A (abstract identity + cylinder eigenrelations)
opens: []
carries_open:
  - STURM_ENERGY_NODE part B (instantiation on the Ferrers defect + F72.6/F72.3B ledger)
  - WEIGHTED_CONSUMER_NODE
  - W5_DEFECT_EDGE_TOP_LATTICE_BUDGET_BOUNDED
kernel_run:
  command: lake build (targeted + full)
  result: Build completed successfully, LAKE_EXIT 0
  axioms: [propext, Classical.choice, Quot.sound]
  sorry: none
route: CHALLENGER_NOT_RH
rh_claim: false
```
