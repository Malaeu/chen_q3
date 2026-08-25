# SOURCE RECORD — Sturm defect energy, parts B2+B3 (Linux-тело, ночная петля)

```yaml
PRIMARY: STURM_ENERGY_NODE_B2_B5_DEFECT_ENERGY_RATE_LEDGER
DATE: 2026-08-26
BODY: Linux (Claude), LINUX_STANDING_GRANT_2026-08-25
TASK: verdict 4c0e13ba (Sturm chain node 1), preflight LINUX_STURM_PREFLIGHT_GOAL058_DEFECT_ENERGY_IDENTITY_2026-08-25
MODE: NIGHT_LOOP, per-node commits
BASE_HEAD: 3de5e54ddd169297d471571134aeb27fad08c630

COMMITS:
  - 3de5e54d  # B2: sturm_defect_truncated_energy_bound
  - c20be54b  # B3: flux limits + energy integrable on open window
  - a3c84e45  # B4+B5: signed identity + rate ledger

LEAN_PATH: q3.lean.aristotle/Q3/Proofs/RouteB/G6N1SturmDefectTruncatedEnergy.lean
LEAN_GIT_BLOB: 0ce87ceab417e5eea9b376917168187057f1fd6e
LEAN_SHA256: 2edfc57575d1a3d97b01c46072b47296c72e38ba47473e58aae6534a4701b370
LEAN_LINES: 1045

PUBLIC_SURFACE:
  - Q3.RouteB.D0Pstar.sturm_physSeries_continuousOn_closed
  - Q3.RouteB.D0Pstar.sturm_defect_truncated_energy_bound
  - Q3.RouteB.D0Pstar.sturm_defect_flux_tendsto_zero_top
  - Q3.RouteB.D0Pstar.sturm_defect_flux_tendsto_zero_bot
  - Q3.RouteB.D0Pstar.sturm_defect_energy_integrable_and_bound
  - Q3.RouteB.D0Pstar.sturm_defect_energy_identity
  - Q3.RouteB.D0Pstar.sturm_defect_energy_rate_ledger

EXPECTED_AXIOM_PROFILES:
  ALL_SEVEN:
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
  CLOSES_ADDITIONALLY:
    - STURM_NODE1_SIGNED_IDENTITY   # B4: energy = -INT r*delta (знак доступен леджеру)
    - STURM_NODE1_RATE_LEDGER       # B5: <= m*mu*Cd^2*sqrt(mu)/pi + Ce*Cphi*Cd + D*Cd
  OPENS:
    - STURM_NODE1_INSTANTIATION  # подстановка selected-семьи: Cd (F72.6 C0), Ce (F72.3B), Cphi (L1 моды), D (узел 2 в форме u^2W''+2uW')

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
  B4: part-A signed identity applies verbatim (all four inputs now theorems).
  B5: pointwise ledger (sympy-verified) -r*delta = m(mu-4pi^2u^2)delta^2
      + (theta-m*mu)(cS)delta - (u^2W''+2uW')delta; cylinder potential sign
      pays the bulk via an indicator majorant on the core |u|<=sqrt(mu)/2pi.
```
