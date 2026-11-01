# Limiting-ladder identification canary

DIAGNOSTIC_NEVER_A_PROOF

Source: rh_clean d6e76475b98dcfe58fe649bcb22d3c126951279c. Physical, normalized, zero-extended even eigenvectors from m=20 and m=24. The ninth profile is the least-ladder-aligned direction in the first six levels, defined by the parent shape.py SVD; it is nearly, not exactly, orthogonal to the six-profile ladder.

## Finding

All 90 normalized zero residuals decrease from m=20 to m=24, by factors between 2.76e-10 and 2.31e-6. This supports a radical-like limiting trend. It does not identify a limiting function or prove convergence. Every tested finite profile has resolved nonzero Fourier values at the tested zeros, hence finite-profile Phi/H has simple poles there.

Higher-degree even polynomial models approximate the ratios away from zeros. The data do not identify the first eight levels with the span of h,h'',...,h^(14): a degree-14 multiplier gives large errors for the upper levels. Nor does a finite-interval polynomial approximation establish an exact polynomial quotient.

## Radical test

Fourier convention: Phi(t)=integral phi(x) exp(-itx) dx. In the orthonormal even basis, phi(x)=sum c_n d_n (-1)^n cos(2 pi n x/L)/sqrt(L) inside the window, with d_0=1, d_n=sqrt(2). Transforms use the exact finite sinc sum (with removable modal values handled directly).

The tables give |Phi(gamma_k)| / max_t |Phi(t)|. Accurate zeros were computed with mpmath.zetazero at 140 dps, not the rounded ordinates in the request. All ten precise ordinates and H derivatives are in zeta_zeros.csv. Maxima were searched on [0,80], step .05, with local stationary-point refinement. An explicit 1/(|t|-omega_max) tail upper bound is below the selected maximum in every case. Interior maximization is numerical, not interval-certified.

### m=20

| Profile |gamma1|gamma2|gamma3|gamma4|gamma5|gamma6|gamma7|gamma8|gamma9|gamma10|
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
|phi0|1.654e-44|2.091e-42|5.319e-41|9.913e-39|1.340e-37|2.595e-35|4.949e-33|7.349e-31|3.565e-27|1.189e-26|
|phi1|2.259e-39|1.053e-37|1.784e-36|2.096e-34|2.340e-33|3.259e-31|4.971e-29|6.305e-27|2.255e-23|6.690e-23|
|phi2|1.308e-34|1.947e-33|2.132e-32|1.549e-30|1.420e-29|1.411e-27|1.714e-25|1.850e-23|4.845e-20|1.275e-19|
|phi3|1.640e-30|1.402e-29|8.623e-29|3.578e-27|2.623e-26|1.772e-24|1.650e-22|1.471e-20|2.615e-17|5.876e-17|
|phi4|4.252e-26|1.475e-25|4.330e-25|9.348e-24|5.351e-23|2.381e-21|1.664e-19|1.202e-17|1.362e-14|2.496e-14|
|phi5|5.856e-22|1.047e-21|1.923e-21|2.191e-20|9.856e-20|2.983e-18|1.623e-16|9.838e-15|7.923e-12|1.266e-11|
|phi6|1.808e-18|8.615e-20|2.122e-18|1.688e-17|5.045e-17|8.911e-16|3.478e-14|1.671e-12|8.449e-10|1.112e-09|
|phi7|5.815e-16|2.781e-15|1.516e-15|1.155e-14|2.046e-14|1.878e-13|4.857e-12|1.725e-10|4.242e-08|3.690e-08|
|least_ladder|5.071e-22|9.069e-22|1.665e-21|1.897e-20|8.533e-20|2.582e-18|1.404e-16|8.513e-15|6.854e-12|1.095e-11|

### m=24

| Profile |gamma1|gamma2|gamma3|gamma4|gamma5|gamma6|gamma7|gamma8|gamma9|gamma10|
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
|phi0|1.708e-52|2.084e-50|5.026e-49|7.984e-47|9.395e-46|1.100e-43|8.790e-42|2.026e-40|1.122e-36|1.726e-34|
|phi1|2.609e-47|1.174e-45|1.886e-44|1.890e-42|1.839e-41|1.551e-39|9.927e-38|1.957e-36|8.027e-33|1.101e-30|
|phi2|1.353e-42|1.948e-41|2.025e-40|1.257e-38|1.005e-37|6.063e-36|3.097e-34|5.210e-33|1.574e-29|1.920e-27|
|phi3|2.946e-38|2.475e-37|1.449e-36|5.181e-35|3.327e-34|1.380e-32|5.462e-31|7.656e-30|1.610e-26|1.698e-24|
|phi4|5.990e-34|2.034e-33|5.725e-33|1.076e-31|5.436e-31|1.514e-29|4.599e-28|5.344e-27|7.741e-24|7.025e-22|
|phi5|1.312e-29|2.286e-29|4.058e-29|4.035e-28|1.596e-27|3.011e-26|7.088e-25|6.893e-24|7.059e-21|5.586e-19|
|phi6|1.565e-25|6.874e-27|1.757e-25|1.307e-24|3.494e-24|4.025e-23|7.102e-22|5.699e-21|4.092e-18|2.835e-16|
|phi7|1.250e-22|7.980e-22|3.979e-22|3.112e-21|5.148e-21|3.386e-20|4.353e-19|2.844e-18|1.408e-15|8.507e-14|
|least_ladder|1.125e-29|1.960e-29|3.479e-29|3.458e-28|1.368e-27|2.580e-26|6.074e-25|5.906e-24|6.047e-21|4.785e-19|

Independent physical Gauss-Legendre integration (192 and 224 nodes, 140 dps) checks phi0 and phi7 at gamma1 and gamma10 against both source precisions. The quadrature change is at most 1.98e-116. For example, m24 phi0(gamma1)=1.54755612297981e-52; source100-to140 relative change is 3.43e-48. phi7(gamma10)=-6.54202510277052e-14; relative change is 5.72e-81. These are resolved finite-source residuals, not rounding-level zeros. See check.json.

## Ratio test on [0,40]

H(t)=4 xi(1/2-it). ratios_grid.csv records Phi/H on the .05 grid. Six zeta zeros lie in this interval. ratio_pole_checks.csv probes both sides at distances 1e-2 through 1e-80 and compares delta*Phi(gamma+delta)/H(gamma+delta) with Phi(gamma)/H'(gamma). At 1e-80, the worst relative residue discrepancy is 8.59e-32. The poles have tiny but nonzero residues, and ordinary grids can conceal them.

Polynomial models fit Phi=H P(t^2) on the .1 grid and validate on the interleaved .05-offset grid. The quotient metric excludes points within .05 of any zero and divides its maximum absolute error by the maximum absolute quotient on the retained grid; it is not a pointwise relative error. Fits use 140 dps; degree-30 normal-matrix condition is 3.04e21. No fit is evaluated as a removable extension through a pole.

m24 holdout errors:

| Profile | degree14 transform error/max Phi | degree30 transform error/max Phi | degree30 quotient relative sup error |
|---|---:|---:|---:|
|phi0|2.561e-12|1.322e-22|2.868e-12|
|phi1|6.410e-10|2.646e-19|5.367e-10|
|phi2|2.338e-07|4.094e-17|5.267e-09|
|phi3|2.605e-05|6.275e-16|4.333e-09|
|phi4|6.845e-04|3.675e-13|2.837e-07|
|phi5|1.763e-02|2.781e-11|1.430e-06|
|phi6|1.340e-01|7.179e-11|3.795e-07|
|phi7|3.958e-01|2.581e-08|2.449e-05|
|least_ladder|1.552e-02|2.405e-11|1.503e-06|

Full degree sweep and coefficients are in polynomial_fits.csv and polynomial_coefficients.csv. The least-ladder direction has degree20 transform error 8.55e-7 and quotient relative sup error .00671. This is evidence for approximation by higher theta derivatives on the tested interval, not an exact ladder identification.

## Two-peak location

| m | positive numerical peak x* | 2x* - log 7 |
|---:|---:|---:|
|20|0.98374606852059885380|+0.02158198798588440249|
|24|0.98359736480703454287|+0.02128458055875578064|

Among log n, n=2,...,12, log 7 is nearest to 2x*, but it is not equal. The peak moves by -0.00014870371356431 between these two m. Full arithmetic differences are in peak_log_comparison.csv.

For the full theta profile with transform 4 xi:
h(x)=sum_{n>=1}(16 pi^2 n^4 exp(9x/2)-24 pi n^2 exp(5x/2)) exp(-pi n^2 exp(2x)), continued evenly.
D=-x partial_x-1/2.

Nonnegative roots located: h': 0; Dh: 0.16080817201898867512; h'': 0.26136077609528135962. Neither peak matches these. Scaled theta sums avoid underflow zeros; termwise signs exclude further positive roots for x>=.5. The root count below .5 is numerical. Peak extrema were cross-checked using the derivative Chebyshev polynomial roots and include endpoints. These are refined numerical positions, not symbolic exact values. See peak_report.md and peak_theta_comparison.csv.

## Reproduction and scope

Run from this directory:
- uv run --with mpmath python3 identify.py
- uv run --with mpmath python3 check.py
- uv run --with mpmath python3 peaks.py

Inputs are the existing parent core JSONs and ladder_limit/shape_results.json. repair_condition_metadata.py reproduces a metadata-only correction using the saved H grid: mpmath matrix indexing must use len(ev)-1, not -1. The corrected main script already uses this indexing. No eigenvector, polynomial coefficient, or fit error depended on that metadata.

No RH conclusion, NOESCAPE estimate, or limiting-radical theorem is claimed. The named limiting ladder remains unidentified beyond the measured radical-like trend and finite-interval polynomial approximability.
