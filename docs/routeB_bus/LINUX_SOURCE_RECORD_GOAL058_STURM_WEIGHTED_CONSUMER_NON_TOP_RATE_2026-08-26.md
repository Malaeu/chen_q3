# SOURCE RECORD — Sturm weighted consumer, nodes 3A/3B (Linux-тело, ночная петля)

```yaml
PRIMARY: GOAL058_STURM_WEIGHTED_CONSUMER_NON_TOP_RATE
DATE: 2026-08-26
BODY: Linux (Claude), LINUX_STANDING_GRANT_2026-08-25
TASK: verdict c47b75a8 (REQ-2026-08-26-B) CODEX/LINUX DIRECTIVE
MODE: ONE_GOAL_ONE_COMMIT
PREFLIGHT: docs/routeB_bus/LINUX_WEIGHTED_CONSUMER_PREFLIGHT_GOAL058_COMPANION_LEDGER_2026-08-26.md (1dec336a)

LEAN_PATH: q3.lean.aristotle/Q3/Proofs/RouteB/G6N1SturmWeightedConsumerNonTopRate.lean
LEAN_SHA256: 2433f597f4b70d2df865135db60af16f8aa400b821f7439eecc849fdac079957
LEAN_LINES: 786

PUBLIC_SURFACE:
  - Q3.RouteB.D0Pstar.wc_sum_inv_sqrt_le                            # sum n^{-1/2} <= 2 sqrt(m)
  - Q3.RouteB.D0Pstar.wc_companion_integral_le                      # exact antiderivative -(1/2)log(lam^2-y^2)
  - Q3.RouteB.D0Pstar.wc_pointwise_amgm                             # sqrt(y)|g| <= companion/(2t) + t*energy/2
  - Q3.RouteB.D0Pstar.wc_core_bound                                 # abstract threshold beta, bound 2*lam*sqrt(Ccap)*sqrt(E0)
  - Q3.RouteB.D0Pstar.sturm_weighted_consumer_interior_bound        # node 3A: filter 2n*u <= lam, Ccap = (1/2)log(4/3) ABSOLUTE
  - Q3.RouteB.D0Pstar.sturm_weighted_consumer_nonTop_sqrtLog_bound  # node 3B: filter (n+1)*u <= lam, Ccap = (1/2)log(m+1)
  - Q3.RouteB.D0Pstar.sturm_weighted_consumer_interior_rate         # <= 2*sqrt((1/2)log(4/3))*CE uniform
  - Q3.RouteB.D0Pstar.sturm_weighted_consumer_nonTop_rate           # <= 2*sqrt((1/2)log(m+1))*CE = sqrt(2)*CE*sqrt(log(m+1))

EXPECTED_AXIOM_PROFILES:
  ALL_EIGHT:
    - propext
    - Classical.choice
    - Quot.sound

VERIFICATION:
  lake_env_lean_exit: 0
  lake_build_target_exit: 0
  full_lake_build_exit: 0
  q3_check_exit: 0
  sorry_count: 0

LEDGER:
  CLOSES:
    - WEIGHTED_CONSUMER_INTERIOR
    - WEIGHTED_CONSUMER_NON_TOP_SQRT_LOG_RATE
  OPENS: []
  CARRIES_OPEN:
    - W5_DEFECT_EDGE_TOP_LATTICE_BUDGET_BANDWIDTH_NEGLIGIBLE

PROOF_ROUTE_AS_MANDATED:
  - finite triangle inequality over n (Finset.sum_filter + abs_sum_le_sum_abs);
  - per-n condition is the interval x <= log(m/beta n) (le_log_iff_exp_le);
  - piecewise split at c_n with pointwise-zero beyond (no a.e. needed on Ioc);
  - exact change of variables y = n*exp(x)/lam (integral_comp_mul_deriv',
    phi' = phi), turning sqrt(u)*y_n into n^{-1/2}*sqrt(y);
  - pointwise AM-GM against the energy weight with the global optimal
    t = sqrt(Ccap)/sqrt(E0);
  - exact companion antiderivative -(1/2)log(lam^2-y^2) and the cap
    lam^2/(lam^2-(n*lam/beta)^2) = beta^2/(beta^2-n^2);
  - interior cap (1/2)log(4/3), non-top cap (1/2)log(m+1);
  - sum n^{-1/2} <= 2*sqrt(m) by telescoping AM-GM induction.

EXCLUSIONS_HONORED:
  top_point_excluded_by_filter: true      # (n+1)*u <= lam excludes the uppermost point per spacing
  no_uniform_edge_band_claim: true
  no_unweighted_L2_norm: true
  no_derivative_sup_norm: true
  no_delta_second_derivative: true
  uniform_D_theorems_untouched: true
```
