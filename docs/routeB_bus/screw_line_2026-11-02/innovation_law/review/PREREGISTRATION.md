# Independent review and finite planted-risk control

DIAGNOSTIC_NEVER_A_PROOF. No route-state change, no RH claim.

Recorded before the following new runs.

1. Probability 0.99: point-kernel Schur and stationary-increment Toeplitz innovation agree on the same regular grid. DISCRIMINATOR: independently assemble both matrices and directly solve at 80 digits for small prefixes, including a planted indefinite prefix. An unchanged value is algebraic after positivity fails, not a variational minimum.
2. Probability 0.99: the full sampled quartet is rank at most four, with at most two negative directions. Adding its two positive squares to the zeta baseline produces C; the two-column negative load U yields a monotone matrix Theta_n=U_n^T C_n^{-1} U_n. Its largest eigenvalue first exceeds 1 at the first planted negative prefix. DISCRIMINATOR: independent dense Cholesky of C, direct signed kernel eigenvalue near crossover, and arbitrary-precision small-cell check. Do not reduce the full non-even history to the rank-one even formula (29).
3. Probability 0.95: double-precision hazard agrees with the main arbitrary-precision signed recursion away from determinant ratios below 1e-9. DISCRIMINATOR: cross-check all four meshes and first crossing; discrepancies trigger arbitrary-precision reevaluation rather than rounding a sign.

Budget: one full pass on the four requested meshes using shared source-g samples, plus small 80-digit controls. If C is not numerically positive or a crossing is unresolved, mark that case unresolved and stop rather than invent a PSD inverse. No claim that this finite factorization provides the missing zeta arithmetic inequality.
