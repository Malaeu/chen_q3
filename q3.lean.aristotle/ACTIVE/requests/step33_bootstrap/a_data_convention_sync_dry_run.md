# Step33A A data-convention sync dry-run

This is a non-mutating diagnostic for `Step33A.1-A-data-convention-sync`.
It uses the convention proved by
`centeredBSplineArchKernelProfile_eq_step22OmegaEtaTransformedProfileWithArchSign`.

It does not edit A CSV files, `ARadius`, radius-floor data, LDL data, or Lean proof payloads.

## Summary

### primary

- candidate: `A_transformed_from_rawStep22`
- convention: `Step22 Omega eta source with Arch sign, eta=2*pi*xi, cosine and packet argument transformed`
- max current raw-vs-transformed center error: `7.902110587559564195130000000000e+1`
- worst distance index: `0`
- worst distance: `0.00`
- current raw Step22 D pass: `True`
- transformed candidate D pass: `False`
- transformed candidate D min eig: `-1.0165250980604694e+02`
- transformed candidate D floor: `1.2228594783222341e-04`
- transformed candidate R pass: `False`
- negative transformed sign probe D pass: `True`
- current raw radius reuse passes: `False`
- transformed radius policy exists: `False`

Direct eta samples:

| index | distance | eta 260 transformed | eta 2pi*260 transformed | bridge receiver | direct-bridge abs |
| ---: | ---: | ---: | ---: | ---: | ---: |
| 0 | 0.00 | -7.849353299351628000000000000000e+1 | -7.889774143023172000000000000000e+1 | -7.889774143023172000000000000000e+1 | 0.000000e-23 |
| 1 | 0.25 | 1.576840478066379700000000000000e+1 | 1.572542934926196200000000000000e+1 | 1.572542934926196200000000000000e+1 | 0.000000e-23 |
| 2 | 0.50 | 7.289426184764776600000000000000e+0 | 7.469675830471349000000000000000e+0 | 7.469675830471349000000000000000e+0 | 0.000000e-24 |

### control

- candidate: `A_transformed_from_rawStep22`
- convention: `Step22 Omega eta source with Arch sign, eta=2*pi*xi, cosine and packet argument transformed`
- max current raw-vs-transformed center error: `7.523137907465061484422000000000e+1`
- worst distance index: `0`
- worst distance: `0.00`
- current raw Step22 D pass: `True`
- transformed candidate D pass: `False`
- transformed candidate D min eig: `-1.0027132888586563e+02`
- transformed candidate D floor: `1.2636922821866160e-05`
- transformed candidate R pass: `False`
- negative transformed sign probe D pass: `True`
- current raw radius reuse passes: `False`
- transformed radius policy exists: `False`

Direct eta samples:

| index | distance | eta 260 transformed | eta 2pi*260 transformed | bridge receiver | direct-bridge abs |
| ---: | ---: | ---: | ---: | ---: | ---: |
| 0 | 0.00 | -7.507130231772885000000000000000e+1 | -7.520513017099184000000000000000e+1 | -7.520513017099184000000000000000e+1 | 0.000000e-23 |
| 1 | 0.25 | 1.732476495235339400000000000000e+1 | 1.732138601963182000000000000000e+1 | 1.732138601963182000000000000000e+1 | 0.000000e-23 |
| 2 | 0.50 | 8.159387431694918000000000000000e+0 | 8.228638331900756000000000000000e+0 | 8.228638331900756000000000000000e+0 | 0.000000e-24 |

## Decision

The transformed Step22-Omega candidate does not pass midpoint penalty sanity.
Do not migrate A data yet.  Keep the source bridge, but escalate the finite PSD
sign/convention contour before any CSV/radius-floor/LDL rebuild.
