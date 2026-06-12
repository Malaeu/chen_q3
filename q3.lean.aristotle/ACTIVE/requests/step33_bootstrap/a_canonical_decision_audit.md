# A_CANONICAL_DECISION_AUDIT

This is a non-mutating audit for `Step33A.1-A`.
It does not edit A CSV, `ARadius`, radius-floor data, LDL data, or Lean proof payloads.

## Source map

- analytic receiver A: `CenteredCoeffBaseHboxImport.primary/control AnalyticA, identified with centeredBSplineArchKernelProfile and the transformed Step22-Omega Arch-sign profile`
- imported table A: `raw Step22 positive-axis Omega payload in q3_psdpd_step22_midpoints_k11/k9.csv`
- finite PSD cert A: `the same raw imported A midpoint payload used to assemble D/R`
- C convention: `C = A - P`
- D/R convention: `R = A - kappa*P0; D = (1 - theta)*A - P + theta*kappa*P0 = C - theta*R`
- Arch sign location: `in the analytic receiver/profile bridge theorem, not in the imported table, not in C/D/R assembly, and not in penaltyForm`

## Family summary

| family | raw sanity | transformed sanity | -transformed probe | rank(DeltaA) 1e-9 | Delta zero on Qv=0 | Delta spectral | Q-null spectral | chosen signal |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | --- |
| primary | True | False | True | 23 | False | 1.0183779500551256e+02 | 1.0183705466870832e+02 | no hidden sign-location or boundary/gauge absorption was found; current finite PSD cert is for raw Step22 A |
| control | True | False | True | 23 | False | 1.0036032838644537e+02 | 1.0035951788619748e+02 | no hidden sign-location or boundary/gauge absorption was found; current finite PSD cert is for raw Step22 A |

## DeltaA structure

### primary

- `DeltaA = A_transformed - A_raw` Frobenius norm: `4.0078932429952738e+02`
- spectral norm: `1.0183779500551256e+02`
- max entry abs: `7.9021105875595637e+01`
- offdiag max abs: `1.6162911132755699e+01`
- rank at `1e-9`: `23`
- top singular values: `1.0183779500551255e+02, 1.0159230445962747e+02, 1.0118126412889264e+02, 1.0060337611115756e+02, 9.9853291734502321e+01`
- Q-null spectral norm: `1.0183705466870832e+02`
- best QtQ relative residual: `9.9923521385725522e-01`
- best P0 relative residual: `9.9839516399909456e-01`
- combined span relative residual: `9.8956186834478696e-03`

### control

- `DeltaA = A_transformed - A_raw` Frobenius norm: `3.8832996376692563e+02`
- spectral norm: `1.0036032838644537e+02`
- max entry abs: `7.5231379074650604e+01`
- offdiag max abs: `1.7808695263616606e+01`
- rank at `1e-9`: `23`
- top singular values: `1.0036032838644537e+02, 1.0009157462658801e+02, 9.9641425592099964e+01, 9.9008227684523007e+01, 9.8185814261147655e+01`
- Q-null spectral norm: `1.0035951788619748e+02`
- best QtQ relative residual: `9.9999230858918953e-01`
- best P0 relative residual: `9.9746068688499123e-01`
- combined span relative residual: `1.0259860770379031e-02`

## Decision

- raw sanity all pass: `True`
- transformed sanity all pass: `False`
- negative transformed probe all pass: `True`
- `DeltaA` zero on `Qv = 0`: `False`
- `DeltaA` rank <= 2: `False`
- `DeltaA` absorbable by `Q^T Q`: `False`
- `DeltaA` P0-like: `False`
- chosen path: `C. one-time recert with transformed A, unless receiver is changed to raw Step22 by a semantic theorem`

Interpretation:

The finite PSD contour uses the raw Step22 positive-axis A.  The transformed
Arch-sign receiver is not being recovered by a later sign flip in `C`, `D`,
`R`, or the penalty layer.  The observed `DeltaA` is not a boundary-null
or small low-rank correction under the current checks.
