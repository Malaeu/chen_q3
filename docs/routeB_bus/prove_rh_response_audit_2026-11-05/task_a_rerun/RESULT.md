# Task A instrument-fix rerun: PASS

DIAG only. RH_PROVED: false. No RH claim and no claim of (7.4). Source formulas and previous audit artifacts are unchanged.

Both worlds, all five t, both precisions: **20/20 baselines PASS; 20/20 c_*+1e−10 plants FAIL** the absolute1e−15 gate. The independently bounded omitted prime-power tail is below1e−18 in every row. The revised instrument meets all requested checks.

Base rh_clean@2cd805e0abf59d21ab103410548e9b011e5ee7a5. PREDICTIONS.md was committed before numerical runs at `c64e6038675138381df066e711aed895e22b550f`. `preregistration.bundle` preserves that commit against the base; it is retained when the local commit is amended for one final delivered commit. The numerical start time and input fingerprints are in results.json.

## Gate table

Prime cutoff is floor(exp(t+12)); all prime powers are retained. Columns show absolute residuals. Each precision uses a fresh zero computation, Gamma quadrature, prime sum and quartet-moment quadrature. The perturbation changes arithmetic by exactly −1e−10 C(t).

| world | t | baseline error50 | baseline error70 | planted error70 | baseline50/70 | plant50/70 |
|:---|---:|---:|---:|---:|:---|:---|
| zeta | 0 | 5.517562138e-22 | 5.517562138e-22 | 4.495580822e-9 | PASS / PASS | FAIL / FAIL |
| zeta | 0.5 | 3.552995015e-22 | 3.552995015e-22 | 5.324988067e-10 | PASS / PASS | FAIL / FAIL |
| zeta | 1 | 4.570916807e-22 | 4.570916807e-22 | 3.390614777e-9 | PASS / PASS | FAIL / FAIL |
| zeta | 1.5 | 5.872432961e-22 | 5.872432961e-22 | 1.053949435e-9 | PASS / PASS | FAIL / FAIL |
| zeta | 2 | 7.521884236e-22 | 7.521884236e-22 | 1.37238288e-9 | PASS / PASS | FAIL / FAIL |
| zeta_plus_quartet | 0 | 5.517562138e-22 | 5.517562138e-22 | 4.495580822e-9 | PASS / PASS | FAIL / FAIL |
| zeta_plus_quartet | 0.5 | 3.552995015e-22 | 3.552995015e-22 | 5.324988067e-10 | PASS / PASS | FAIL / FAIL |
| zeta_plus_quartet | 1 | 4.570916807e-22 | 4.570916807e-22 | 3.390614777e-9 | PASS / PASS | FAIL / FAIL |
| zeta_plus_quartet | 1.5 | 5.872432961e-22 | 5.872432961e-22 | 1.053949435e-9 | PASS / PASS | FAIL / FAIL |
| zeta_plus_quartet | 2 | 7.521884236e-22 | 7.521884236e-22 | 1.37238288e-9 | PASS / PASS | FAIL / FAIL |

Maximum baseline error: **7.521884236e-22**. Minimum planted error: **5.324988067e-10**. Maximum arithmetic change between50 and70 dps: 9.523191983e-49. Full H, S, both arithmetic/zero sides, quartet terms, C(t), shift and decisions for every row are in results.json.

## Omitted arithmetic tail: independent analytic bound

Write N=floor(exp(t+12)), b=log N−t, D=b−1/2−9/b. Here b>11.99 and D>0 for every requested t. The explicit polynomial is

    C(v) = [v^8−28.5v^6+217.5625v^4−442.875v²+112.6875]
           × exp(−v²/2)/sqrt(2π).

For v≥b, the sum of absolute polynomial coefficients after division by v^8 is less than2, so |C(v)|≤2v^8exp(−v²/2)/sqrt(2π). Bound Lambda(n) by log n and sum over every integer n>N. Each of the two resulting functions of n decreases on [N,infinity): its logarithmic derivative in lambda=log n is 1/lambda−1/2+8/(lambda±t)−(lambda±t)<0. Therefore the sum is at most the integral starting at N.

After v=log x−t or v=log x+t, both integrals are bounded by the same expression. This gives

    tail ≤ 4 exp(t/2)/sqrt(2π)
              × integral_b^infinity (v+t)v^8 exp(v/2−v²/2) dv
         ≤ 4 exp(t/2)(b+t)b^8 exp(b/2−b²/2)/(sqrt(2π)D).

The second inequality follows because the logarithmic derivative of the integrand is 1/(v+t)+8/v+1/2−v≤−D for all v≥b. This bounds the entire omitted prime-power tail, including both shifts, without using a zero identity or any cancellation. The quartet is exact and adds no omitted arithmetic tail.

For reporting, the driver multiplies the analytic majorant by1.001, then rounds upward to eight significant digits. The formula is an analytic bound; its evaluation uses mpmath, not an interval library.

| t | N | reported omitted-tail upper bound (max50/70) | below1e−18 |
|---:|---:|---:|:---|
| 0 | 162754 | 1.6642325e-20 | YES |
| 0.5 | 268337 | 2.2258634e-20 | YES |
| 1 | 442413 | 2.9723819e-20 | YES |
| 1.5 | 729416 | 3.9633905e-20 | YES |
| 2 | 1202604 | 5.2775635e-20 | YES |

Maximum reported omitted arithmetic tail: **5.2775635e-20 < 1e−18**. The finite-cutoff residual still exceeds the true zeta response around1e−34. Passing the absolute gate checks normalization at the tested points; it does not resolve h relatively or establish a sign.

## Zero sum and quartet

As before, mpmath zetazero supplies every positive ordinate through60, with conjugates included explicitly. The inherited analytic zero-tail envelope uses Nζ(T)≤T² for T≥60, a loose classical explicit zero-count bound; it does not assume RH. In each integer shell k≥60, use 2(k+1)²(k²+1/4)²(k²+1/2)²exp(1/8−k²/2+t/2). The polynomial times Gaussian decreases there. Shells60 through100 and the geometric remainder allowance give maximum 7.171243688e-764 over this grid. This zero tail is negligible compared with the arithmetic truncation.

Quartet u=1/3+7i is evaluated as 2Re(G_u²(e^{ut}+e^{−ut})) on the arithmetic side, where G_u is computed by full-line quadrature of g(x)e^{ux}. The zero side uses F(u) instead. These are the same four-root polarization as the unchanged builder, using complex squares rather than modulus squares.

## Reproduce and verification

From repository root run `python docs/routeB_bus/prove_rh_response_audit_2026-11-05/task_a_rerun/run_task_a.py`, then the report.py in the same directory. The driver imports C,F,g,atoms directly from the original ../scripts/task_a.py; its original main is not invoked. Dependencies are Python, mpmath and NumPy. No Tasks B/C are rerun. SHA256SUMS covers all delivered rerun files except itself.

All20 gate decisions and20 intentional failures, tail limits, precision repeats, source fingerprints and syntax were checked. Independent read-only review is in REVIEW.md. Numerical quadrature is diagnostic, not interval certified. The earlier failed-cutoff audit remains intact.
