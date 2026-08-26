# SOURCE RECORD — selected Ferrers edge-top flux consumer (Linux-тело, ночная петля)

```yaml
PRIMARY: GOAL058_EDGE_TOP_FLUX_CONSUMER_ASSEMBLY
DATE: 2026-08-26
BODY: Linux (Claude), LINUX_STANDING_GRANT_2026-08-25
TASK: verdict ed7c8f7d (REQ-2026-08-26-E) CODEX/LINUX DIRECTIVE
MODE: ONE_GOAL_ONE_COMMIT
SUCCESS_CODE: W5_DEFECT_EDGE_TOP_LATTICE_BUDGET_BANDWIDTH_NEGLIGIBLE_LEAN

LEAN_PATH: q3.lean.aristotle/Q3/Proofs/RouteB/G6N1SelectedFerrersEdgeTopFluxConsumer.lean
LEAN_SHA256: 4c459466ad3f8041ca99c47e1336a99e8d8a3e51f9bb7d9d03552ea9317b50df
LEAN_LINES: 1583

PUBLIC_SURFACE:
  - selectedFerrersLemma73SourcePacket_eq_anchored_combination
    # EXACT packet identity: sourcePacket = (1/4)(chi0*(a4 h4) - 3 chi2*(a0 h0));
    # via the structure fields I0 = chi0*h0(0), I4 = chi2*h4(0) and the two
    # committed center-anchor locks; normalizingDenominator cancels exactly
  - four_mul_explicitCCMLimitH_eq_cylinder      # 4H = (1/4)(D4 - 3 D0)
  - edgeTop_boundary_trichotomy                 # non-top / strict-top / seam, exact and disjoint
  - edgeTop_strictTop_unique                    # at most one strict-top index per spacing
  - edgeTop_strictTop_outer                     # y_top > lambda/2 (pure arithmetic)
  - sturm_outer_flux_derivative_bound           # |phi'| <= 41 A/lambda^3 from outer decay A/lambda^6
                                                # ((lambda - y) cancels exactly between flux and weight)
  - selectedFerrersDefectEdgeTopBudget          # THE literal strict-top budget (public def)
  - selectedFerrersDefectEdgeTopBudget_bound_of_modeChiThetaRates
    # eventual budget <= 2*(5373952*sqrt(2032129)+1)/(lambda*sqrt(lambda))
    # (the lambda^{-3/2} rate with the EXACT constant of the complete algebra)
  - selectedFerrersDefectEdgeTopBudget_bandwidthNegligible_of_modeChiThetaRates
    # budget^2 * physicalFourierBandwidth^{-1} -> 0 at O(lambda^{-4})

EXPECTED_AXIOM_PROFILES:
  ALL_PUBLIC:
    - propext
    - Classical.choice
    - Quot.sound

VERIFICATION:
  lake_env_lean_exit: 0
  lake_build_target_exit: 0
  full_lake_build_exit: 0
  q3_check_exit: 0
  sorry_count: 0

INPUTS_CONSUMED (no new analytic supplier):
  - hmode (F72.6 mode-rate input family, literal anchored modes)
  - hchi (F72.3B chi-defect rate: |1-chi0|, |1-chi2| <= Cchi/lambda^2)
  - htheta (two-sided differential eigenvalue rate |Lambda_j + G| <= Ctheta*(k+2))
  - selectedFerrersAnchoredOuterPolynomialDecay_of_modeAndThetaRates (128a27f0)
  - committed B-chain: sturm_mode_flux_hasDerivAt, zero-flux transport,
    physSeries continuity (node 1 machinery)

MANDATES_HONORED:
  two_mode_split: >-
    flux applied per mode with its OWN eigenvalue (Solution0/Solution4 have
    distinct classical eigenvalues); recombined by the exact packet identity;
    no common theta ever applied to prolateCombination
  three_way_partition: >-
    strict top nu < lambda < (n+1)u only; non-top stays with nodes 3A/3B;
    seam nu = lambda excluded from the filter (belongs to the W4 jump ledger);
    trichotomy + uniqueness + outer-half membership proved as public lemmas
  no_deriv_at_seam: strict inequalities keep every evaluated point interior
  no_endpoint_weighted_FTC: the (lambda-y) factor cancels BEFORE division
  no_sup_norm_no_delta2: only value-level decay + flux representation
  exact_constant_exported: >-
    the third-attack guard honored: the exported constant
    2*(5373952*sqrt(2032129)+1) = 2*(2*41*65536*sqrt(2032129)+1) is the one
    the algebra produces (two-mode combination (2+6)/4 = 2 of the per-mode
    41*65536*sqrt(2032129), plus the Gaussian H-part paid to 1/lambda^3 by
    1536*lambda^8 <= e^{pi lambda^2/4} eventually)

LEDGER:
  CLOSES:
    - W5_DEFECT_EDGE_TOP_LATTICE_BUDGET_BANDWIDTH_NEGLIGIBLE  # kernel gate passed; semantic admission judge's
  OPENS: []
  CARRIES_OPEN:
    - SELECTED_FERRERS_PREANCHOR_PRODUCTION_FAMILY_CROSSWALK
    - F72_6_MODE_AND_CHI_RATE_INPUTS
```
