# Low-cluster canary

**DIAGNOSTIC_NEVER_A_PROOF — K7.** Literal even CCM, N=m, L=log m. No cofinal or RH claim.

Source: `PROSHKA_VERDICT_NOESCAPE_F_ONLY_2026-11-02.md`, inbox commit `777c504c07512487b758e41aab120edd686f27d3`, Git blob `c2633b50199981b80da01610c64e2239c0494e82`; definitions: NOESCAPE (4.7)–(4.14), SHA256 `fdfd384345b69d7565100b93ef57348eb6944bdbaf014a01c001df007129aded`.

## Full even-sector sums

Every even level i=0..m is in levels.csv. The sums below exclude i=0 and include every computed nonzero excited eigenvalue, without a small-eigenvalue cutoff. All computed eigenvalues are positive and resolved relative to the eigensolver residual. No numerical zero modes were observed, so z=0 in this diagnostic; this is not an interval-certified kernel classification.

| m | 1−a0² | S from independent F+X | S_F | max excited X/F magnitude | level | max relative closure |
|---|---|---|---|---|---|---|
| 12 | 0.00123802531809 | 0.00123802531809 | 0.00124664423102 | 0.00347309326537 | 1 | 3.43609e-72 |
| 16 | 0.00156248945241 | 0.00156248945241 | 0.00156278477549 | 9.47536213032e-5 | 1 | 3.95998e-63 |
| 20 | 0.00171437775938 | 0.00171437775938 | 0.00171438389542 | 1.79432479372e-6 | 1 | 8.0044e-55 |
| 24 | 0.00170874790034 | 0.00170874790034 | 0.00170874800419 | 3.04605106099e-8 | 1 | 1.38151e-46 |

## Polynomial bands

Low means 0<|lambda_i|<m^(-B), excited levels only; high is its complement among nonzero excited levels. Each pair of rows sums to S (z=0).

| m | B | low count | low sum | high count | high sum |
|---|---|---|---|---|---|
| 12 | 2 | 7 | 0.00123802531809 | 5 | 1.8007899e-18 |
| 12 | 4 | 6 | 0.00123802531809 | 6 | 1.9290725e-16 |
| 12 | 8 | 4 | 0.001238025317267 | 8 | 8.2316589e-13 |
| 16 | 2 | 9 | 0.001562489452409 | 7 | 6.1116956e-20 |
| 16 | 4 | 8 | 0.001562489452409 | 8 | 3.6618409e-19 |
| 16 | 8 | 6 | 0.001562489452409 | 10 | 2.84206e-16 |
| 20 | 2 | 11 | 0.001714377759384 | 9 | 2.0118518e-23 |
| 20 | 4 | 10 | 0.001714377759384 | 10 | 2.4558283e-22 |
| 20 | 8 | 8 | 0.001714377759384 | 12 | 7.6312947e-20 |
| 24 | 2 | 13 | 0.001708747900339 | 11 | 1.314224e-26 |
| 24 | 4 | 12 | 0.001708747900339 | 12 | 1.7300675e-25 |
| 24 | 8 | 9 | 0.001708747900339 | 15 | 1.3513837e-21 |

## Ladder principal angles (degrees)

Profiles: h,h_second,h_fourth,h_sixth,Dh,Dh_second with D=−x d/dx−1/2, projected from the full theta profiles, H=hat h=4xi. Column-scaled SVD gives ladder rank six in all cells.

| m | k | canonical angles, degrees |
|---|---|---|
| 12 | 3 | 7.8453713e-8, 9.5125603e-6, 0.026333544, 6.9501594 |
| 12 | 5 | 6.1524218e-11, 1.8941245e-7, 0.00036572546, 0.26643804, 31.659967, 88.558243 |
| 12 | 7 | 0*, 4.6326743e-9, 4.216532e-7, 0.0053601103, 29.20674, 67.065552 |
| 16 | 3 | 5.0612691e-9, 2.5078258e-5, 0.035975908, 8.998107 |
| 16 | 5 | 4.3950877e-11, 2.0810696e-7, 0.0004997126, 0.37049163, 30.9672, 88.871904 |
| 16 | 7 | 2.2448379e-13, 2.6081672e-9, 1.1937695e-5, 0.016175545, 28.740417, 66.162777 |
| 20 | 3 | 5.1256651e-9, 2.8677798e-5, 0.040131822, 9.5337392 |
| 20 | 5 | 4.6071701e-11, 2.344797e-7, 0.00054708023, 0.39327662, 30.879272, 87.944603 |
| 20 | 7 | 4.4202757e-13, 3.7087719e-9, 1.0407982e-5, 0.015628116, 28.580524, 67.100376 |
| 24 | 3 | 4.8216769e-9, 2.7402329e-5, 0.039356898, 9.5105596 |
| 24 | 5 | 2.7815875e-11, 1.6854228e-7, 0.00043797514, 0.34921735, 30.954829, 87.83396 |
| 24 | 7 | 3.5542627e-13, 2.9689321e-9, 8.1501444e-6, 0.013927356, 28.540567, 67.662556 |

For k=3, two ladder dimensions are unmatched. For k=7, two cluster dimensions are unmatched. At m12,k7, the first zero angle (*) is forced by 6+8>13; its tiny raw numerical value is rounding, not extra evidence of alignment. Full cosines/sines and dimension accounting are in angles.csv.

## Independent computation and controls

F is the signed whole-line Xi tail from the source row formula, with cutoffs 128,160,192. The high modes enter only F, never the active matrix. Archimedean sine moments are evaluated by a digamma identity plus an exponentially convergent correction, independently checked against all off-diagonal active entries. The matrix includes all prime powers through m, including 19 and 23 when applicable.

X is evaluated independently as k(h_out,e_j)−k(W,e_j)+sum_l A_jl<W,e_l>, then paired with every eigenvector. Physical archimedean integrals, both even tails, all supported prime powers (including n>m for h_out), the pole, and finite projection correction are retained. No X=T−F reconstruction is used. Equation F+X=−Z lambda a is a posteriori validation only. The exterior JSON records each component and omitted-tail indicators.

Production: mpmath100dps, composite Gauss-Legendre128. Validation: complete m24 cell at140dps/GL160, including independent X and ladder. Additional X convergence checks: m12GL64 and m16GL96. No interval quadrature enclosure is claimed.

| m24 validation quantity | maximum relative discrepancy |
|---|---|
| lambda_i_max_relative | 1.359476e-46 |
| a_i_max_relative | 8.712828e-52 |
| F_i_max_relative | 2.203515e-48 |
| X_i_independent_max_relative | 6.986704e-48 |
| full_inverse_weighted_term_max_relative | 2.763023e-46 |
| X_over_F_max_relative | 4.783189e-48 |

Maximum absolute angle discrepancy (degrees): 1.4366466e-66.

Explicit F-vector tail bounds beyond192 (also bounding each coordinate) are approximately 1.14e−157,1.93e−140,2.57e−129,2.08e−121 for m12,16,20,24. See tail_bound.py/results and its elementary Gamma/zeta derivation. They bound only the truncation tail, not floating roundoff or quadrature. Exterior tail indicators similarly do not certify numerical quadrature.

## Interpretation

These finite cells retain most theta mass in the chosen bottom; the excited inverse-weighted mass is concentrated in the polynomial low cluster. The maximum coordinatewise exterior ratio is measured across all excited levels, not only i1. None of these finite measurements supplies an unbounded subsequence, a uniform strict margin, or eta_m→0. The six-profile ladder has several small principal angles but a large worst angle for the six-level cluster; unmatched dimensions are not suppressed.

## Reproduction

Install mpmath and run from this directory:

```bash
uv run --with mpmath python3 core.py 100 128 12 16 20 24
uv run --with mpmath python3 core.py 140 160 24
for m in 12 16 20 24; do uv run --with mpmath python3 exterior.py "$m" 100 128; done
uv run --with mpmath python3 exterior.py 24 140 160
uv run --with mpmath python3 finalize.py
```

exterior.py uses the repository full_center_probe.py to form its projection matrix when none is passed; core.py includes the same literal formula in matrix_core.py. No route-status files are changed.
