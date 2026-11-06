# Part A — coefficient space and J1/J2

The preregistered free index range is `n=2..N`, with `N=500, 1000, 2000, 5000`.
The coefficient and reference tables were loaded directly from Git commit
`ba5654b46adf84159702748b006699bafa0ed89b` and their blobs were checked by
`part_a.py`. The archived CSV stores `x=G^{-1}b`; for the frozen residual
`1 + sum c_n r_n`, the aligned full-Gram optimum is `c_opt=-x`. The Möbius
taper is `a_n=mu(n)*log(N/n)/log(N)`, and `delta=c_opt-a`.

## J1 and J2

The full 4999×4999 Gram matrix was rebuilt from the pinned Vasyunin formula.
Both comparisons use `E(v)=1+2 b^T v+v^T G v`, with `b_n=log(n)/n`.
J1 compares `E(c_opt)` with archived `e_N`; J2 compares `E(a)` with archived
`E_V_centered`. Each passes the preregistered `1e-10` tolerance.

| N | J1 `E(c_opt)` | J1 abs diff | J2 `E(a)` | J2 abs diff | wrong-sign `E(+x)` | normal residual, infinity norm |
|---:|---:|---:|---:|---:|---:|---:|
| 500 | 0.007426788071839940 | 4.44e-16 | 0.04090652137838324 | 1.11e-15 | 3.9777196357844775 | 5.74e-15 |
| 1000 | 0.006561374298162503 | 2.55e-15 | 0.03408267538909171 | 6.66e-16 | 3.9803158771054994 | 8.92e-15 |
| 2000 | 0.006118802780197052 | 1.07e-14 | 0.02853848542120252 | 5.77e-15 | 3.981643591659367 | 1.53e-14 |
| 5000 | 0.005307020683004815 | 2.31e-13 | 0.02333637999226790 | 2.99e-14 | 3.9840789379519057 | 5.58e-14 |

The small normal residual and the large opposite-sign error independently
confirm the sign alignment. The source is not an interval computation: Apple
clang reports `LDBL_MANT_DIG=53`, and the stored Gram and linear algebra are
float64. The Gram binary was temporary and is not an output artifact.

## Coefficient comparison

| N | cosine `(c_opt,a)` | delta/optimal energy ratio | delta energy `n>sqrt(N)` | delta energy `n>N/2` | nonsquarefree share of optimal coefficient energy |
|---:|---:|---:|---:|---:|---:|
| 500 | 0.903768 | 0.274713 | 0.980279 | 0.565530 | 0.025825 |
| 1000 | 0.892144 | 0.303795 | 0.987569 | 0.534658 | 0.048298 |
| 2000 | 0.883946 | 0.316960 | 0.992261 | 0.547349 | 0.048660 |
| 5000 | 0.875310 | 0.347973 | 0.995013 | 0.509611 | 0.048743 |

The remaining disjoint delta-energy partitions (squarefree/non-squarefree,
prime/proper prime power/other) are in `part_a_energy_splits.csv`. At N=5000,
the preregistered profile correlation against N=2000 is only `0.082609`.
All six raw Pearson correlations on the preregistered 4096-point common
`n/N` grids are in `part_a_profile_correlations.csv`; interpolated data are in
`part_a_allpairprofiles.csv`.

OLS with an intercept and the six frozen features has R² values
`0.8161879, 0.7351334, 0.7209355, 0.7126824` at the four increasing N values.
The coefficients and feature definitions are in `part_a_regression.csv` and
`part_a_features.csv`.

## Part A prediction scores

- Q1: **HIT**, cosine at N=5000 is `0.875310` (threshold `0.8`; p=0.55).
- Q2: **MISS**, N=2000 vs 5000 profile correlation is `0.082609` (threshold `0.7`; p=0.60).
- Q3: **HIT**, `n>sqrt(N)` holds `0.995013` of delta energy at N=5000 (strict threshold `0.5`; p=0.50).
- Q4: **MISS**, nonsquarefree coefficients hold `0.048743` of optimal coefficient energy at N=5000 (threshold `0.1`; p=0.50).

The partial Brier score over Q1–Q4 is `0.265625`; it is not the full Q1–Q6
score. The R8 `certificate_witness_N*.json` files are upper-envelope optimizer
candidates, not the NB full-Gram optimum, and were not used in this calculation.
The separate input audit records their differences where witnesses were
available.

`part_a.py` and `gram_native.cpp` contain the reproducible run. The runner uses
the pinned source blobs, emits ASCII progress/ETA, checks both judges, and
writes the coefficient, feature, split, regression, profile, and plot outputs.
Part B, J3's continuous-integral/tail comparison, and J4's permutation nulls
were not part of this run; these results make no causal or RH claim.
