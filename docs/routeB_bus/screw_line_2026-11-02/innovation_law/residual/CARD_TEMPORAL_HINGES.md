# HYPOTHESIS — prime thresholds have one favorable kick sign

DIAGNOSTIC_NEVER_A_PROOF. The registered prediction was instead that both derivative-jump signs occur (prior 0.9). Confirmed on the tested fixed-history extensions; a uniform favorable temporal-kick sign is killed.

**Object.** A discrete sampled innovation sequence has no literal value at log n unless a target-time extension is chosen. Here all old grid points strictly below log n are fixed, and only the new target moves. Sigma is continuous at the threshold. Its first derivative has a kink. The coefficient derivative `d sigma²/d c_n = -Q(log n)` is a different operation.

**Evidence.** Mesh32 uses all 98 prime powers with log n<6 in each world; mesh64 uses nine declared controls. On zeta mesh32, the formula predicts 88 positive and 10 negative derivative jumps. Examples:

- n=2: predicted +0.0802140085207392, measured +0.0802140085779754.
- n=16: predicted -0.00505185080690822, measured -0.00505185083110383.

The source coefficient is positive in both examples. History determines the sign through `2 c_n beta_first`, equivalently `-2c_n+2c_n sum(a_i)`. DH mesh32 has 72 positive, 23 negative and three zero predictions; planted has 88 positive and 10 negative. These counts do not distinguish zeta from the planted world.

**Accuracy and retained failure.** Source values and centered differences use mpmath80; Toeplitz predictor coefficients use float64. Nine independent MP80 solves agree with the predicted jump within 2.97e-13; maximal predictor coefficient difference is 4.73e-11. The initial Richardson difference had a 1.25642e-4 error at log163 because the threshold is extremely close to an old mesh point. `hinges_initial.csv` preserves it. Deterministic repair of 15 rows shrank epsilon relative to that distance and the distance to other arithmetic hinges. The final maximum absolute jump discrepancy over 321 rows is 3.375e-9. All nonzero predicted signs agree with the measured signs; four zero predictions remain numerically unresolved as zero, as expected. The printed long decimal strings do not confer 80-digit predictor accuracy.

**What kills a stronger claim.** The mixed signs occur already with positive zeta histories, so neither dropping indefinite controls nor replacing DH coefficients repairs a universal sign law. The same jump-sign counts in zeta and plant also kill these counts as the requested two-world discriminator. The finite table does not establish an asymptotic rate or a continuum sign theorem.

**What to hand Proshka.** Keep temporal hinge response and arithmetic coefficient sensitivity separate. Both depend on the complete optimizer. The residual source envelope remains the jointly compensated expression; neither positive arithmetic coefficients nor a local favorable-kick interpretation supplies its missing bound.

Reproduce using `hinges.py`, then `hinges.py --repair-near-grid`, then `finish_hinges.py`. Rows with nonzero past negative index are stationary signed pivots, not variational minima. No route state changes.
