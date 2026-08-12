# Exact projective ground-to-trial residual on one control cell

Date: 2026-08-12

Scope: `[FINITE_CELL][CONDITIONAL]`

Outcome: `MEASURED_FINITE_CELL_CONDITIONAL_NOT_PROMOTING`

## Knowledge preflight

Before producing the measurement, the required query was run from the repository
root:

```text
./orchestrator/kb.py ask "exact projective ground to trial residual one control cell lambda_sq 13 N 120 ground_xi1 portable_k_coeffs NO_PERSISTED_MFIN_MATVEC"
```

It exited `0` and returned:

```text
no hits for 'exact projective ground to trial residual one control cell lambda_sq 13 N 120 ground_xi1 portable_k_coeffs NO_PERSISTED_MFIN_MATVEC' in any layer
```

The same receipt is embedded in the JSON result.

## Source lock

The sole control cell is `(lambda_sq, N) = (13, 120)`.  Both complete
241-coordinate vectors use indices `-120,...,120`.

| Role | Persisted source and selector | SHA-256 |
|---|---|---|
| trial | `q3.lean.aristotle/ACTIVE/requests/routeB_twolevel_spectral_ladder/out/portable_k_coeffs_lambda_sq_13_N_120.json`; `coefficients`, `logical_vector=k1` | `0e5239355c54103859b22d7f753d8cd6765c2c41bcd3ec7f86b20beccc907a88` |
| actual finite ground | `q3.lean.aristotle/ACTIVE/requests/routeB_twolevel_spectral_ladder/out/nconv_anchor_lambda_sq_13_N_120.json`; `xi_m_y_cache[0].xi_vector`, `name=xi1` | `cbc556ef7c73c9aefa9f177bb59aeca5867ed6628e3f1cca6edb270bfc13e7f0` |

The generator fails closed if either hash, cell metadata, selector, or coordinate
support changes.

## Convention and measurement

For

```text
<u,v> = sum_n conj(u_n) v_n,
```

both persisted vectors are renormalized from their full decimal-string
coordinates.  If `g` is `ground_xi1` and `t` is the trial, the nonzero minimizer
is

```text
c_star = <t,g> / ||t||^2.
```

Thus the recorded relative distance and defect are

```text
inf_{c != 0} ||g-c*t|| / ||g||
  = 6.8497317830183172756379642033197217218514289634008501626034303056304663711159675e-5

1 - |<g/||g||,t/||t||>|^2
  = 4.6918825499291295939231005532377541134674161985269713758969716899447143804110465e-9
```

The normalized absolute overlap is

```text
0.99999999765405872228371496379189172608655005485968185846480854523753181266941100.
```

No acceptance threshold is asserted.  These values are a calibration/falsifier
readout for exactly one finite cell, not a convergence result.

## Guards and independent replay

The generator uses 140-decimal-digit arithmetic and checks the direct
coordinate projection residual against `1-|overlap|^2`; their absolute mismatch
was `7.6793408e-141`, below the declared `1e-110` arithmetic guard.

The separate validator reads both locked sources and the result afresh, uses a
170-digit context, recomputes the Gram-determinant expression independently,
and checks the recorded quantities to `1e-75` relative/absolute tolerance.

```text
q3.lean.aristotle/ACTIVE/requests/routeB_lamport_rh_closure/exact_projective_ground_to_trial_residual_one_control_cell.py
q3.lean.aristotle/ACTIVE/requests/routeB_lamport_rh_closure/validate_exact_projective_ground_to_trial_residual_one_control_cell.py
```

Observed validator result:

```text
VALIDATE_EXACT_PROJECTIVE_ONE_CONTROL_CELL: PASS
spectral_residual_and_gap=NO_PERSISTED_MFIN_MATVEC
scope=[FINITE_CELL][CONDITIONAL]
```

## Evidence boundary

The two source-locked packets do not persist a canonical `Mfin` matvec.
Consequently the matrix residual and spectral gap are deliberately recorded as
`NOT_MEASURED` under `NO_PERSISTED_MFIN_MATVEC`; eigenpair-cache metadata is not
used as a replacement.

This object is not a theorem, not a cofinal estimate, not Route B closure, and
not an RH claim.
