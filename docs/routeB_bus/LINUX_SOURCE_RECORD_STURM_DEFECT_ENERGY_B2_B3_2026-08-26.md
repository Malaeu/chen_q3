# SOURCE RECORD — Sturm defect energy, parts B2+B3 (Linux-тело, ночная петля)

```yaml
PRIMARY: STURM_ENERGY_NODE_B2_B3_DEFECT_ENERGY_INTEGRABLE
DATE: 2026-08-26
BODY: Linux (Claude), LINUX_STANDING_GRANT_2026-08-25
TASK: verdict 4c0e13ba (Sturm chain node 1), preflight LINUX_STURM_PREFLIGHT_GOAL058_DEFECT_ENERGY_IDENTITY_2026-08-25
MODE: NIGHT_LOOP, per-node commits
BASE_HEAD: 3de5e54ddd169297d471571134aeb27fad08c630

COMMITS:
  - 3de5e54d  # B2: sturm_defect_truncated_energy_bound
  - c20be54b  # B3: flux limits + energy integrable on open window

LEAN_PATH: q3.lean.aristotle/Q3/Proofs/RouteB/G6N1SturmDefectTruncatedEnergy.lean
LEAN_GIT_BLOB: e30e9a823db10f0defe3c2dff52271cfda73314e
LEAN_SHA256: 711154c03e875e63a93831ac8ba6b49d6878d9fa27831605937c7b83a751c1df
LEAN_LINES: 607

PUBLIC_SURFACE:
  - Q3.RouteB.D0Pstar.sturm_physSeries_continuousOn_closed
  - Q3.RouteB.D0Pstar.sturm_defect_truncated_energy_bound
  - Q3.RouteB.D0Pstar.sturm_defect_flux_tendsto_zero_top
  - Q3.RouteB.D0Pstar.sturm_defect_flux_tendsto_zero_bot
  - Q3.RouteB.D0Pstar.sturm_defect_energy_integrable_and_bound

EXPECTED_AXIOM_PROFILES:
  ALL_FIVE:
    - propext
    - Classical.choice
    - Quot.sound

VERIFICATION:
  lake_env_lean_exit: 0
  full_lake_build_exit: 0
  sorry_count: 0

LEDGER:
  CLOSES:
    - STURM_NODE1_DEFECT_ENERGY_INTEGRABILITY  # энергия дефекта интегрируема на открытом окне, БЕЗ краевых гипотез
    - STURM_NODE1_FLUX_REMAINDER               # флюкс-члены сняты пределом: INT (lam^2-x^2)|delta'|^2 <= INT |r*delta|
  OPENS:
    - STURM_NODE1_RATE_LEDGER  # алгебра r*delta + F72.6/F72.3B-гипотезы -> C^2/lam^2 (последний шаг узла 1)

PROOF_ROUTE:
  B2: instantiate part-A truncated bound on delta = c*physSeries - W;
      exact source r from committed physical prolate ODE + product rule;
      series continuity on the CLOSED window pays integrability of r*delta.
  B3a: defect flux -> 0 at both endpoints (committed zero-flux transport
      kills the physical part; vanishing weight kills the cylinder part).
  B3b: exhaustion Icc(-lam+lam/(n+2), lam-lam/(n+2)); AECover machinery
      (aecover_Ioo_of_Icc, integrable_of_integral_bounded_of_nonneg_ae,
      integral_tendsto_of_countably_generated); flux terms vanish along
      the exhaustion => clean bound with no flux remainder.
```
