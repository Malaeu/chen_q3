# SOURCE RECORD — the explicit H derivative comb budget (unconditional)

```yaml
schema: q3_codex_source_record.v1
record_for: W5_EXPLICIT_H_QCOMB_BOUNDED
body: LINUX_CLAUDE
node_path: q3.lean.aristotle/Q3/Proofs/RouteB/G6N1ExplicitHDerivativeCombBudget.lean
node_git_blob: 933538b766a32fbc1c10dcaed36c290914e03b9d
parent_commit_at_record: dee1ec4df27bc55dce9ae65342c644870616dccc
authorizing_verdict: docs/routeB_bus/proshka/PROSHKA_VERDICT_GOAL058_W5_DERIVATIVE_H_SPLIT_AND_L2_STURM_PRIMARY_2026-08-25.md
public_surface:
  - hbG (the comb kernel, closed polynomial form), hbG_eq_four_mul_deriv
  - explicitCCMLimitH_eq_hbHRe (profile identity to the committed complex H)
  - hbMaj (explicit window majorant), hbBudget, hbBudget_nonneg
  - hbComb_le_hbMaj (pointwise, every window u in [lam^-1, lam])
  - hbMaj_integral_le (uniform weighted window integral <= hbBudget)
  - explicitH_derivative_comb_budget (packaged existential)
private_reconstructions:
  - hbV := (4 pi^2 y^5 - 4 pi y^3) e^{-pi y^2}: EXACT elementary antiderivative
    of hbG — the load-bearing find; no Poisson, no zero-mass import needed
  - hb_cell (order-2 midpoint cell estimate, error u^2/2 * cell L1 of hbG2)
  - hb_comb (comb vs exact FTC value, error u/2 * hbKG)
  - head/tail Gaussian bounds via pow_div_factorial_le_exp
conclusion: >-
  For every lam >= sqrt 2 and every u in [lam^{-1}, lam], the explicit target
  derivative comb |sum_{n<=floor(lam/u)} g_H(n u)| is dominated by the
  explicit majorant hbMaj, and int (sqrt u)^{-1} * hbMaj du <= hbBudget,
  one absolute constant.  Uniform over the whole selected family; inputs: [].
  This converts W5_LOG_DERIVATIVE_BUDGET_BOUNDED into a pure defect
  statement, as ratified.
key_intermediate: >-
  V' = g_H exactly (algebraic); midpoint-cell second-order comparison pays
  the u-decay of the Euler-Maclaurin remainder; Gaussian tails pay u >= 1.
conditionality: []
closes:
  - W5_EXPLICIT_H_QCOMB_BOUNDED
opens: []
carries_open:
  - W5_PACKET_DEFECT_DERIVATIVE_L2_RATE (Sturm preflight next)
kernel_run:
  command: lake build (targeted + full)
  result: Build completed successfully, LAKE_EXIT 0
  axioms: [propext, Classical.choice, Quot.sound]
  sorry: none
route: CHALLENGER_NOT_RH
rh_claim: false
```
