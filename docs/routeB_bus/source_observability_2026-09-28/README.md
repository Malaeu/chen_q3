# Literal full-K even-sector source observability diagnostic

**Status:** numerical diagnostic only; not a proof or interval certificate.
The computation uses the literal `full_center_probe.matrix_K(m)` and the
reflection-even sector. Results and detailed residuals are in `results.json`.

## Reproduction

From the repository root, using the existing environment:

```sh
.venv/bin/python docs/routeB_bus/source_observability_2026-09-28/probe.py --m-list 8 12 16 --dps 70
```

This recomputes the three full even-sector samples.

To augment the saved samples with the reference midpoint row from
`SOURCE_TRANSFER.md` (without overwriting the eigenvalue/Rayleigh samples):

```sh
.venv/bin/python docs/routeB_bus/source_observability_2026-09-28/probe.py --augment-reference-rows --m-list 8 12 16 24 --dps 140
```

To refresh source hashes, provenance, and the direct theta-series endpoint
checks in the saved result without rerunning
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

## Reference source row and the observability test

The optional pass constructs precisely the finite midpoint row used in
`schur_probe.py`: `zhat_m = F_m*((-1)^k(P_k(c0)-P_k(c4)))`, with Robin midpoint
energies from `rectangle_probe.bracket(m)`. It uses the **same literal full**
`K_m` to compute `Z_m=||zhat_m||` and
`alpha_m=||(I-u_m u_m*) zhat_m/Z_m||`, where `u_m` is the lowest full-`K_m`
eigenvector. These are reference-center diagnostics, not values for a selected
exact-energy row or a proof that the lowest eigenvalue is simple for all `m`.

| m | reference Z_m | reference alpha_m |
|---:|---:|---:|
| 8 | 4.341846776998 | 0.055342160605 |
| 12 | 5.283815971540 | 0.059589624762 |
| 16 | 6.082827707407 | 0.057575447710 |
| 24 | 7.428231110414 | 0.053206801408 |

The m=8 norm and angle agree with the separate 140-dps `schur_probe_m8_dps140.json`
diagnostic. The four-point log-log slope of `alpha_m` is about `-0.0412`;
four subthreshold cells cannot establish an eventual rate. `m=24` has only
this reference-row pass; its five even eigenvalues and derivative Rayleigh
quotients have not been computed.

An independent 180-dps repeat of `run_reference_row(24,180)` changed the
140-dps `Z_m` by relative `5.65e-50`, `alpha_m` by `2.26e-47`, and the lowest
full-`K_m` eigenvalue by `1.92e-87`. The tiny source reflection difference
changed from `1.14e-42` to `7.30e-63`, showing that this *difference* was
roundoff-limited at 140 dps; the reported `Z_m` and `alpha_m` were stable.
Reproduction without rewriting `results.json`:

```sh
.venv/bin/python -c 'import sys; sys.path.insert(0,"docs/routeB_bus/source_observability_2026-09-28"); import probe; x=probe.run_reference_row(24,180); print(x["Z_m_reference"],x["alpha_m_reference"])'
```

`SOURCE_TRANSFER.md` (T1)--(T4) uses one reference vector `zhat_m` and one
selected vector `b_m`, but defines no multirow observation map `S_m` on the
low eigenspace. If one takes the only source functional
`v -> <zhat_m,v>`, its restriction to any `r`-dimensional space with `r>=2`
has a nonzero kernel by rank-nullity. Thus its lower frame bound is exactly
zero for structural reasons, not evidence that Route B dies. The convention
for `sigma_min` of a wide rectangular matrix must also be specified: a
software-reported smallest *listed* singular value need not include its
nullspace. Even treating `zhat_m` and `b_m` as two observation rows leaves a
kernel for `r>=3`. Adding `F_m*` or arbitrary derivative rows would define a new
test; it does not follow from the transfer statement. The `gamma_mr` death
criterion therefore remains undefined as written.

For `E_m`, (T4) requires a uniform Robin-rectangle row error plus the
selected infinite-tail bound. The existing separate m=8 Arb calculation has
`E_energy<1.900e-31` and **conditional** `E_tail<4.186e-21`, giving a
conditional `E/Z` of about `9.64e-22` at that finite reference center. Since
m=8 is below the selected threshold, this is not a selected-family bound.
Under the accepted hypotheses and eventual thresholds of (T5), direct
division by its positive lower bound on Z gives

```
E/Z <= (2400 C_A/c_G) m^(11/4) (8/25)^m
     + (16 C_P/c_G) m sqrt(log m) 210^(-m)
     + (320 C_A/c_G) m^(5/4) sqrt(log m) (2/225)^m -> 0.
```

This excludes the `E/Z -> 1` death condition **under those matched
hypotheses**; it does not settle the `alpha_m` rate or the undefined
multirow-observability condition.

## Limits

Only m=8, 12, and 16 have the full even-sector tower calculation; m>=24
does not. The mpmath quadrature and eigensolver values are not interval
enclosures. Small eigensolver residuals do not bound matrix quadrature or
theta-tail error. The reference-row values above are not cofinal
selected-family values. `E_m` and
`E_m/Z_m` at m=12,16,24 still need selected full-row interval/sup error and
tail bounds. No source-defined multirow `S_m` or `gamma_mr` has been computed.
Thus this run does not decide whether Route B succeeds or fails.
