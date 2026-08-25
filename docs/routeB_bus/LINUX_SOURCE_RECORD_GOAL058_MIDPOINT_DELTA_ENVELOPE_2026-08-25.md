# SOURCE RECORD — midpoint-delta envelope for the pure E_star vector

```yaml
schema: q3_codex_source_record.v1
record_for: ABEL_LIMIT_TO_GTRIAL_MIDPOINT_DELTA
body: LINUX_CLAUDE
node_path: q3.lean.aristotle/Q3/Proofs/RouteB/G6N1SelectedFerrersMidpointDeltaEnvelope.lean
node_git_blob: f6c810859979f101c366e3a613c67e4353545fdb
parent_commit_at_record: c082e0702475485f28118e61f6f3f65871218af1
authorizing_verdict: docs/routeB_bus/proshka/PROSHKA_VERDICT_GOAL058_W5_FIRST_ORDER_PROJECTION_TAIL_SUPPLIER_2026-08-25.md
public_surface:
  - selectedFerrersSqrtUHm, selectedFerrersEStarHm (defs)
  - selectedFerrersEStarHm_physicalCoefficient_le
  - selectedFerrersEStarHm_physicalCoefficient_sq_le
private_reconstructions:
  - w5m_one_lt_lambda, w5m_exp_half_L, w5m_finiteWindow
  - w5m_sqrtU_memLp, w5m_eStar_eq_fun, w5m_eStar_memLp, w5m_eStarHm_eq
  - w5m_sqrtU_zeroExtension_ae (transport clone)
  - w5m_fourier_congr_ae (upstream private clone)
  - w5m_sqrtU_fourier_norm_le (closed-form exponential integral,
    exp(cL)=lambda via L=log m and exp_int_mul_two_pi_mul_I)
  - w5m_sqrtU_coefficient_le
conclusion: >-
  The pure E_star vector of the selected Ferrers packet obeys the receiver
  envelope with the explicit combined constant
  Budget_k + norm(packet 0) * sqrt(lambda_k)/(4*pi):
  norm(c_n)^2 <= C_comb^2 * L_m / n^2 for all nonzero n.  The midpoint
  delta (1/2)*packet(0)*sqrt(u) is paid exactly through the closed-form
  Fourier value ((lambda-1)/c)/sqrt(lambda*L) with norm(c) >= 2*pi*|n|/L.
key_intermediate: >-
  Vector identity EStarHm = AbelLimitHm - (1/2)packet(0) * sqrtUHm in H_m,
  plus the exact exponential integral over the additive window.
conditionality: []
closes:
  - ABEL_LIMIT_TO_GTRIAL_MIDPOINT_DELTA (per-k envelope with explicit constant)
opens: []
carries_open:
  - CENTER_VALUE_RATE (eventual boundedness of norm(packet 0)*sqrt(lambda_k);
    expected from modeAndChiRates C0-rates at 0 since the target 4H(0)=0)
  - PREANCHOR_TO_PRODUCTION_SOURCE_FAMILY_CROSSWALK (awaiting judge b1/b2)
  - W5_LOG_DERIVATIVE_BUDGET_BOUNDED (upstream, unchanged)
kernel_run:
  command: lake build (targeted + full)
  result: Build completed successfully, LAKE_EXIT 0
  axioms: [propext, Classical.choice, Quot.sound]
  sorry: none
route: CHALLENGER_NOT_RH
rh_claim: false
```
