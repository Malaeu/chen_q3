# SOURCE RECORD — first-order coefficient crosswalk and W4-fed envelope

```yaml
schema: q3_codex_source_record.v1
record_for: W5_FIRST_ORDER_COEFFICIENT_BOUND_ON_EXACT_SELECTED_SOURCE_PATH (V_n_m crosswalk half)
body: LINUX_CLAUDE
node_path: q3.lean.aristotle/Q3/Proofs/RouteB/G6N1SelectedFerrersFirstOrderCoefficientEnvelope.lean
node_git_blob: 058f2a78892ce9faef46b89659d1fe934d261038
parent_commit_at_record: 1d9caa755fe47585566627e992e4c4b4f4268f96
authorizing_verdict: docs/routeB_bus/proshka/PROSHKA_VERDICT_GOAL058_W5_FIRST_ORDER_PROJECTION_TAIL_SUPPLIER_2026-08-25.md
public_surface:
  - physicalFourierCoefficient_eq_fourier_sourceLogWindowZeroExtension
  - selectedFerrersAbelLimitHm_physicalCoefficient_sq_le
private_reconstructions:
  - w5c_additiveMode_memLp, w5c_additiveModeLp (upstream privates)
  - w5c_logWindowL2Equiv_additiveModeLp, w5c_symm_V_n_m
  - w5c_fourier_congr_ae
conclusion: >-
  Exact crosswalk: for every H_m vector x and integer n,
  physicalFourierCoefficient i x n = (sqrt L_m)^{-1} * Fourier(zeroExt x)(n/L_m).
  Instantiated on the W3 Abel-limit vector via the committed ae-identity and
  the W4 quantitative decay: norm(c_n)^2 <= Budget_k^2 * L_m / n^2 for all
  nonzero n.  This is exactly the receiver envelope shape with C = Budget_k.
key_intermediate: >-
  logWindowL2Equiv unitarity moves the inner product to the additive window;
  the additive mode maps to V_n_m; the restricted integral equals the
  whole-line Fourier integral of the zero extension at t = n/L_m.
conditionality: []
closes:
  - EXACT_FIRST_ORDER_COEFFICIENT_CROSSWALK_TO_V_N_M (V_n_m half)
opens: []
carries_open:
  - ABEL_LIMIT_TO_GTRIAL_MIDPOINT_DELTA (vector correction (1/2)*pkt(0)*sqrt(u))
  - PREANCHOR_TO_PRODUCTION_SOURCE_FAMILY_CROSSWALK (judge's STRONGEST ATTACK)
  - W5_LOG_DERIVATIVE_BUDGET_BOUNDED (upstream, unchanged)
kernel_run:
  command: lake build (targeted + full)
  result: Build completed successfully, LAKE_EXIT 0
  axioms: [propext, Classical.choice, Quot.sound]
  sorry: none
route: CHALLENGER_NOT_RH
rh_claim: false
```

Note per verdict FORBIDDEN list: no index identification is made anywhere;
the envelope is stated on selectedFerrersPreAnchorIndex only.  The eventual
boundedness of Budget_k stays conditional on W5_LOG_DERIVATIVE_BUDGET_BOUNDED
exactly as in the W5 conditional assembly.
