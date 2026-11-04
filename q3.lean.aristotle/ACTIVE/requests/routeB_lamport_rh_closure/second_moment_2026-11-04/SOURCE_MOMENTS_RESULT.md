# Literal-source second moments

DIAGNOSTIC_NEVER_A_PROOF. All285 integer m=16,…,300 completed for zeta, DH and plant:855 unique source rows and9405 decomposition rows. Dense C/B/A/G/P/W arrays remain local. No eigensystems or spectral scans were computed.

The unchanged source uses400-bit MPFR, GL192 and eight panels. Frobenius and atom decomposition arithmetic is binary64. Maximum relative decomposition conservation residual is8.02e−15; maximum source-split entry residual4.11e−15; atom-to-source B entry residual1.27e−12. These are numerical checks, not interval bounds.

At m=16,40,300 unchanged-source GL256 paired-order pilots agree at binary64. Genuine400-bit MPFR comparisons at m300 give maximum A-entry difference1.15e−115 and Frobenius-square difference at most1.22e−112 across worlds. Binary64 Frobenius values differ from MPFR by at most2.96e−12 in these pilots. These three checks do not supply a uniform quadrature error theorem.

At m300 the arithmetic off-diagonal net and sum of absolute pairwise cross terms differ substantially. For zeta, |net|/||A||²=.0121192493 while sum_{n≠k}|〈B_n,B_k〉|/||A||²=.0871713712; for DH the respective values are.00644103007 and.1231498593; for plant,.0116960027 and.0841270415. Ordered pairs include both(n,k) and(k,n). The direct Gram net agrees with the existing decomposition to2.4e−11 absolute. Both interpretations are retained; no score interpretation is silently selected.

`SOURCE_MOMENTS.csv/json` contain trace, Frobenius square, scope/counters, residuals, source hashes and local array hashes. `DECOMPOSITION.csv` contains signed shares, absolute contributions divided by Frobenius square, and the separately named share of the sum of absolute terms. Plant innovation W and its three mixed terms remain explicit. `SOURCE_MOMENTS_validation.json`, `SOURCE_MOMENTS_paired_orders.csv`, `SOURCE_MOMENTS_mp_m*.json` and `ARITHMETIC_PAIR_MASS_m300.csv/json` give the validation receipts.

Reproduce the pair-mass receipt without rebuilding the source using `PYTHONPATH=<dependencies>:<output> python -c 'import source_moments as s; s.arithmetic_pair_mass(300)'` after the source cache exists. `source_moments_mp_pilots.py` runs the unchanged400-bit GL192/256 paired MPFR moment comparison.
