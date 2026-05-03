# Step 20 -- Midpoint/radius contract

## Goal

Fix the mismatch discovered in Step 19:

- `k_spline=9` passed radius-mode.
- `k_spline=11` failed because Arb evaluation of `P` differed from the
  internal float midpoint produced by the high-degree power-basis B-spline
  evaluator.

The fix is to let Step 18 read both:

```text
midpoint CSV: matrix,i,j,mid
radius CSV:   matrix,i,j,rad
```

This lets `P` and `Q` use Arb midpoint plus Arb radius, instead of forcing a
radius around an unstable float midpoint.

## Code Changes

Updated:

```text
scripts/q3_psdpd_step18_interval_guard.py
```

New argument:

```text
--midpoint-csv
```

The midpoint CSV overrides internal float midpoint matrices for `A`, `P`,
`P0`, and `Q`, and recomputes `Q^T Q` if `Q` is overridden.

Added:

```text
scripts/q3_psdpd_step20_midpoint_contract.py
```

The generator writes both midpoint and radius CSV files.

Current contract:

| Matrix | Midpoint | Radius |
|---|---|---|
| `P` | Arb | Arb |
| `Q` | Arb | Arb |
| `A` | float quadrature | drift radius |
| `P0` | float quadrature | drift radius |

Thus `A` and `P0` are still Step 21/22 proof-grade targets.

## `k_spline=11` Result

Parameters:

```text
L = 3.0
ell = 0.30
delta = 0.25
k_spline = 11
kappa = 3.25
theta = 1e-4
arb_prec = 256
```

Generated:

```text
docs/insights/q3_psdpd_step20_midpoints_k11.csv
docs/insights/q3_psdpd_step20_radii_k11.csv
```

Contract summary:

```text
||P_float-P_arb_mid||_2 = 2.0221155393806238e-04
max rad(A)              = 1.6431300764452317e-14  [drift]
max rad(P)              = 2.1399664282886390e-16  [Arb]
max rad(P0)             = 1.2179468440010055e-05  [drift]
max rad(Q)              = 3.3619987347001753e-16  [Arb]
```

Step 18 radius-mode result with midpoint CSV:

```text
||rad(P)||_2      = 6.5268739490277510e-16
||rad(Dtheta)||_2 = 2.4898059291564031e-08

Dtheta safe_lower = 1.2226127113676471e-04
Rkappa safe_lower = 1.3543578198995190e-01
PASS              = True
```

This confirms the Step 19 diagnosis:

```text
k=11 failed because of midpoint instability, not because of the finite form.
```

## `k_spline=9` Control

Parameters:

```text
L = 3.0
ell = 0.30
delta = 0.25
k_spline = 9
kappa = 3.075
theta = 1e-5
arb_prec = 256
```

Generated:

```text
docs/insights/q3_psdpd_step20_midpoints_k9.csv
docs/insights/q3_psdpd_step20_radii_k9.csv
```

Contract summary:

```text
||P_float-P_arb_mid||_2 = 1.5796107294751509e-06
max rad(A)              = 1.8651746813702630e-14  [drift]
max rad(P)              = 2.6057745144044991e-16  [Arb]
max rad(P0)             = 1.4818841709285380e-07  [drift]
max rad(Q)              = 3.3619987347001753e-16  [Arb]
```

Step 18 radius-mode result with midpoint CSV:

```text
||rad(P)||_2      = 7.9787190368612646e-16
||rad(Dtheta)||_2 = 2.0856225786302011e-11

Dtheta safe_lower = 1.2636902053577041e-05
Rkappa safe_lower = 1.9569374457049731e-03
PASS              = True
```

The control branch remains healthy.

## Verdict

Step 20 restores `k_spline=11` as the stronger finite proof-candidate.  The
key change is the interval contract:

```text
certify around Arb midpoint, not around the old float midpoint.
```

The next hardening target is no longer `P` or `Q`; those now have Arb
midpoints and Arb radii.  The remaining non-proof-grade parts are:

- `P0`: float midpoint plus drift radius;
- `A`: float midpoint plus drift radius.

## Next Move

Step 21 should replace `P0` drift radii with proof-grade piecewise
B-spline/exponential-polynomial interval integrals.

Step 22 should replace `A` drift radii with interval quadrature plus a
sinc-power analytic tail bound.
