# Independent verification of the native signed ledgers

DIAGNOSTIC_NEVER_A_PROOF. Read-only evaluation of the six existing native kappa=1.1 trial vectors at `rh_clean@8acecc1574740c5163c2a4e8ef75049f6df84313`; no new source eigensystem or changed source matrix. Original source pin is `d26831357b6cb3b2b7d4a569d2031e454952b246`.

All six remote source blobs are pinned in `remote_provenance.json`. Each vector is independently normalized and evaluated using a separately prepared implementation: real cosine/sine correlation coefficients and analytic atom-tail exponential moments. The published ledger uses physical complex exponential products and per-integer segmented moments. This checks the same source identities using different arithmetic organizations. Independent archimedean GL128/120dps components are compared with the remote GL160/140dps ledger.

| world | m | selected Rayleigh | max component difference | independent direct sum minus Rayleigh | reference Abel closure |
|---|---:|---:|---:|---:|---:|
| DH | 55 | -0.6639206461 | 3.407880885e-119 | -1.452221968e-120 | -3.836891458e-119 |
| zeta | 55 | 0.0001070512462 | 1.471584928e-119 | 2.129405552e-120 | -8.870655855e-120 |
| DH | 80 | -1.240687012 | 4.337302945e-119 | 6.931939528e-119 | 1.030022467e-118 |
| zeta | 80 | 3.817633164e-7 | 1.413496049e-119 | -1.133022718e-119 | -1.518782142e-120 |
| DH | 120 | -1.588253688 | 1.169522758e-118 | 4.99564357e-119 | 1.702136511e-118 |
| zeta | 120 | 6.134500659e-10 | 2.052473715e-119 | -2.235840963e-119 | -1.698040791e-120 |

Every arithmetic p/p2/pk>=3/non-prime-power bin, separated by sign of b(n), agrees. The endpoint atom n=m is exactly zero. The raw operator sum H_original+c+pole−P agrees with the selected same-vector Rayleigh. The sum of separate component minima is never substituted.

## Boundary and interior: naming and no double counting

The pinned `c31645a` file labels the actual boundary as (3.3) and the interior derivative as (3.4); it has no displayed (12). In the published package `reference_derivative_bulk` is exactly the requested source interior derivative. The package also uses a two-column `I_ref=reference_T+reference_derivative_bulk`; retaining `reference_T` is necessary. Thus the separate source identity is

    halfQ + Bulk + Boundary = P − continuum.

These are not additional terms in the raw H+c+pole−P ledger. For zeta the transformed identity H_plus+(4−cstar)−halfQ−Bulk−Boundary gives the same Rayleigh; both the H shift and pole/continuum identity independently close.

For DH, the canonical raw Abel identity uses psi_D without reference subtraction. It closes as halfQ_raw+Bulk_raw+Boundary_raw=P_D. The optional common x−1 reference must separately retain the continuum, since DH has no pole. Both versions are independently verified; no DH pole or artificial arithmetic main term is inferred.

| world | m | Boundary with common reference | source interior derivative Bulk | halfQ |
|---|---:|---:|---:|---:|
| DH | 55 | 0.19326929672 | 4.66761853269 | -0.00399677709336 |
| zeta | 55 | 0.00121285803567 | 2.42470157805 | -0.000599934586627 |
| DH | 80 | -0.0499643963253 | 5.51370239201 | -0.00351877126512 |
| zeta | 80 | 3.8625109774e-5 | 2.79782139309 | 0.00150833632234 |
| DH | 120 | 0.05559519615 | 5.75342123692 | -0.00280971517626 |
| zeta | 120 | 1.39298731028e-6 | 3.09607785609 | -0.000669368721799 |

Maximum absolute verification discrepancies:

- `H_plus_difference`: 1.51031084679e-119.
- `canonical_Abel_identity`: 5.88633971057e-119.
- `independent_direct_sum_minus_rayleigh`: 6.93193952758e-119.
- `max_component_difference`: 1.16952275828e-118.
- `pole_continuum_identity`: 9.36002440357e-123.
- `reference_Abel_identity`: 1.70213651056e-118.
- `remote_same_vector_Rayleigh_difference`: 2.90444393614e-120.
- `transformed_rayleigh_difference`: 2.00348544849e-119.

## Full R and quiet residual delta readback

`verify_saved_linear_algebra.py` separately checks the published native A,Q,U,f,y. It computes the norm of AQ from its existing small Gram, rather than solving any new full source eigenproblem. Full R is read from the complete source spectrum, not the compressed complement bottom.

| m | full R | delta | delta recomputation difference |
|---:|---:|---:|---:|
| 55 | 0.66392064608105 | 3.44079009708846e-8 | 2.509422e-121 |
| 80 | 1.24068701234966 | 1.07855923001335e-11 | -2.7343007e-121 |
| 120 | 1.5882536880355 | 6.85316657399964e-14 | 7.7284067e-121 |

The same readback records E Q, U Q, both basis orthogonality residuals, the lifted-vector residual, and the compressed eigen-equation residual. These are numerical agreement checks, not outward-rounded enclosures of the exact zero-defined J.

Reproduce from this directory after restoring the parent matched archive:

```sh
python verify_remote.py dh_m55_q50_native.json
python verify_remote.py dh_m80_q73_native.json
python verify_remote.py dh_m120_q108_native.json
python verify_remote.py zeta_m55_q27.json
python verify_remote.py zeta_m80_q41.json
python verify_remote.py zeta_m120_q64.json
python verify_saved_linear_algebra.py
```

`DH_INPUTS` selects the unchanged parent fake-world input directory; `REMOTE_LEDGER` and `MATCHED_ROOT` can override the parent ledger_cells/ and matched_cells/ locations. The scripts default to the repository-relative parent layout.

No cofinal bound, source-paper result, route status, RH claim, or interval certificate is produced by this verification.
