# SOURCE RECORD — selected Ferrers anchored outer polynomial decay (Linux-тело, ночная петля)

```yaml
PRIMARY: GOAL058_SELECTED_FERRERS_ANCHORED_OUTER_POLYNOMIAL_DECAY
DATE: 2026-08-26
BODY: Linux (Claude), LINUX_STANDING_GRANT_2026-08-25
TASK: verdict fce7669c (REQ-2026-08-26-D) CODEX/LINUX DIRECTIVE
MODE: ONE_GOAL_ONE_COMMIT

LEAN_PATH: q3.lean.aristotle/Q3/Proofs/RouteB/G6N1SelectedFerrersOuterPolynomialDecay.lean
LEAN_SHA256: 0644e33487e20cbba0b95aa06015feb172c3101031d7295506b571a3eb4e0078
LEAN_LINES: 1026

PUBLIC_SURFACE:
  - Q3.RouteB.D0Pstar.sturm_outer_polynomial_decay
    # core: raw committed series, |phi| <= 65536*sqrt(B)/lam^6 on [lam/2, lam]
    # from eigenvalue window Lambda+G <= lam^4 and half-window L2 mass B
  - Q3.RouteB.D0Pstar.selectedFerrersAnchoredOuterPolynomialDecay_of_modeAndThetaRates
    # both literal anchored selected modes <= 65536*sqrt(2032129)/lam^6
    # on [lam/2, lam] eventually, from hmode (F72.6 family) + theta-rate

EXPECTED_AXIOM_PROFILES:
  BOTH:
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
    - SELECTED_ANCHORED_OUTER_POLYNOMIAL_DECAY_LEAN
  OPENS: []
  CARRIES_OPEN:
    - W5_DEFECT_EDGE_TOP_LATTICE_BUDGET_BANDWIDTH_NEGLIGIBLE  # consumer assembly next, after semantic admission

PROOF_ROUTE (verdict-repaired, route delta declared honestly):
  core_mechanism: >-
    The energy function E = ((lam^2-y^2)*phi')*phi has, by the committed
    physical prolate ODE, E' = q*phi^2 + (lam^2-y^2)*phi'^2 with
    q >= lam^4 on y >= lam/4 (eigenvalue window); committed zero-flux
    transport gives E(lam-) = 0, hence E <= 0 on the outer region and
    phi^2 is NONINCREASING there (the verdict's monotonicity, obtained
    directly - no zero-freeness case analysis needed).
  quantitative_recursion: >-
    lam^4*M(y) <= -E(y) <= lam^2*(-phi*phi') pointwise; integrating over
    a lam/32-block and using the antitone conversion g(a)*w <= M(a-w)
    yields M(a+w) <= 512*lam^-4*M(a-w). Three precommitted steps
    8/32 -> 10/32 -> 12/32 -> 14/32 give outer mass 512^3*lam^-12*B -
    the same lam^-12 as the verdict's three Caccioppoli shells, with the
    E-function replacing the cutoff tests (DELTA vs the mandated
    IMPLEMENTATION_ORDER: no cutoff eta needed; all FORBIDDEN moves
    honored - no endpoint weighted-FTC, no sup norm, no delta'').
  pointwise_recovery: >-
    g antitone + block mean on [14/32, 15/32] gives
    g(lam/2) <= 32*512^3*lam^-13*B, i.e. sup <= 2^16*sqrt(B)*lam^-13/2,
    weakened to 65536*sqrt(B)/lam^6 (lam >= 1) - the verdict's
    lam^-13/2 -> lam^-6 exactly.
  anchored_assembly: >-
    hnormEq: anchored norm = (norm(a)/N)*|phi| on the window (C04: literal
    anchored modes). L2: pointwise triangle vs the cylinder target +
    Gaussian envelope |D_j(sqrt(4pi)y)| <= 1008*e^{-pi y^2/2} (elementary,
    pow_div_factorial) + gaussian integral <= 1 => anchored half-window
    mass <= 2*1008^2 + 1 = 2032129 uniformly (the verdict's anchored-L2
    repair; no individual anchor bound used - scale cancels exactly).
  eigenvalue_window: theta = Lambda + G <= Ctheta*(k+2) <= (k+2)^2 = lam^4 eventually.
```
