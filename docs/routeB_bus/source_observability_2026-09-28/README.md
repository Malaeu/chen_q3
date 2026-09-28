# Literal full-K even-sector source observability diagnostic

**Status:** numerical diagnostic only; not a proof or interval certificate.
The computation uses the literal `full_center_probe.matrix_K(m)` and the
reflection-even sector. Results and detailed residuals are in `results.json`.

## Reproduction

From the repository root, using the existing environment:

```sh
.venv/bin/python docs/routeB_bus/source_observability_2026-09-28/probe.py --m-list 8 12 16 --dps 70
```

This recomputes the three samples. To refresh source hashes, provenance, and
the direct theta-series endpoint checks in the saved result without rerunning
the eigensolver or Fourier quadratures:

```sh
.venv/bin/python docs/routeB_bus/source_observability_2026-09-28/probe.py --refresh-metadata
```

## Method and observed values

The script imports `full_center_probe.matrix_K` unchanged and forms
`B = Q.T * K * Q`, where `Q` has columns `e_0` and
`(e_n + e_-n)/sqrt(2)` for `1 <= n <= m`. It computes the five lowest
eigenvalues of `B` and Rayleigh quotients of the even projections of
`D^(2k)G`, `k=0,...,4`. The finite theta-G series and its cutoff match
`full_center_probe.gaussian_plane`; derivatives use the polynomial
recurrence in `probe.py`. Each sample uses 70 decimal digits. Cutoffs are
26, 32, and 36 for m=8, 12, and 16, respectively.

| m | lambda_1 | lambda_2 - lambda_1 | lambda_3 - lambda_1 | elapsed sample time |
|---:|---:|---:|---:|---:|
| 8 | 1.0239258710e-19 | 6.3726260399e-15 | 1.0872106804e-10 | 54.85 s |
| 12 | 6.7904267000e-29 | 1.6299412278e-23 | 9.6446924386e-19 | 97.33 s |
| 16 | 5.4561380117e-38 | 4.7334130203e-32 | 7.3464888017e-27 | 145.68 s |

The five derivative Rayleigh quotients for every m, all five eigenvalues,
eigenpair residuals, Fourier projection residuals, and exploratory three-point
log-log fits are recorded in `results.json`. The fits have no asymptotic
interpretation. Direct comparisons of the same truncated theta series at
`t = +/-log(m)/2` give maximum absolute discrepancies across `G` and `G''`
of about `1.2e-69`, `7.1e-70`, and `1.3e-69` for the three samples.

As a separate numerical cross-check, the m=8 even-sector `lambda_1` agrees
with `actual_lowest_full_K_eigenpair.lambda0` in
`fokas_k_sign_2026-09-25/schur_probe_m8_dps140.json`; its `lambda_2` agrees
with the third entry of `full_K_eigenvalues_below_a`. This is a comparison of
two numerical diagnostics, not an Arb certificate.

## Limits

Only m=8, 12, and 16 were computed; m >= 24 was not run. The mpmath quadrature
and eigensolver values are not interval enclosures. Small eigensolver residuals
do not bound matrix quadrature or theta-tail error. No selected Ferrers
reference row was built, so `Z_m` and `alpha_m` are not computed; `E_m` and
`E_m/Z_m` need the selected full-row interval/sup error and tail bound. The
multirow `S_m` required for `gamma_mr` is not defined by the cited
`SOURCE_TRANSFER.md` input, so neither it nor `gamma_mr` is computed. Thus
this run does not evaluate the selected-source observability criterion or
decide whether Route B succeeds or fails.
