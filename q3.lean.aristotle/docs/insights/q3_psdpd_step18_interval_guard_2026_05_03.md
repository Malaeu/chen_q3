# Step 18 -- Interval/drift guard for the finite kappa certificate

## Goal

Harden the Step 17 finite candidate without relying on a numerical nullspace
basis `N`.

We want the strengthened finite inequality

```text
C^circ >= theta R_kappa^circ,
R_kappa^circ > 0,
```

where

```text
C = A - P,
R_kappa = A - kappa P0,
D_theta = C - theta R_kappa.
```

## Candidate

- `L = 3.0`
- `k_spline = 11`
- `ell = 0.30`
- `delta = 0.25`
- `kappa = 3.25`
- `theta = 1e-4`

This is the same-profile high-margin candidate selected in Steps 16--17.

## Penalty Method

Instead of certifying the numerical boundary-null basis `N`, use full-space
penalty matrices:

```text
M_D,tau = D_theta + tau Q^T Q,
M_R,tau = R_kappa + tau Q^T Q.
```

If both are strictly positive definite on the full coordinate space, then on
`ker Q` we get

```text
D_theta >= 0,
R_kappa > 0.
```

This proves

```text
C^circ >= theta R_kappa^circ > 0
```

on the finite boundary-null space, without separately certifying `N`.

## Drift Guard Run

Command:

```bash
uv run python q3.lean.aristotle/scripts/q3_psdpd_step18_interval_guard.py \
  --L 3.0 \
  --k-spline 11 \
  --ell 0.30 \
  --delta 0.25 \
  --kappa 3.25 \
  --theta 1e-4 \
  --arch-tmax 260 \
  --arch-nt 48001 \
  --p0-na 24001 \
  --mode drift \
  --tau-grid log:-8:8:161
```

The drift radius was estimated from the tested quadrature variants:

```text
220:36001:18001
260:48001:24001
320:64001:32001
```

This is not proof-grade interval arithmetic, but it checks whether the
penalty certificate has enough room for the observed quadrature drift.

## Results

Midpoint tau scan:

```text
Dtheta best tau midpoint = 7.9432823472428218e+07
Rkappa best tau midpoint = 3.9810717055349857e+07
```

Radius diagnostics:

```text
||rad(A)||_2      = 4.0613878140729339e-14
||rad(P)||_2      = 0.0000000000000000e+00
||rad(P0)||_2     = 3.8304595415531493e-05
||rad(QTQ)||_2    = 0.0000000000000000e+00
||rad(Dtheta)||_2 = 1.2449029323788542e-08
||rad(Rkappa)||_2 = 1.2448993513629463e-04
```

Dtheta penalty certificate:

```text
best_tau   = 7.9432823472428218e+07
lambda_mid = 1.1537351069866537e-04
err_norm   = 1.2449029323788542e-08
safe_lower = 1.1536106166934159e-04
PASS       = True
```

Rkappa penalty certificate:

```text
best_tau   = 3.9810717055349857e+07
lambda_mid = 1.3568479327718430e-01
err_norm   = 1.2448993513629463e-04
safe_lower = 1.3556030334204799e-01
PASS       = True
```

## Verdict

The drift-mode penalty guard passes:

```text
D_theta + tau Q^T Q > 0,
R_kappa + tau Q^T Q > 0
```

under the tested quadrature drift model.  This confirms that the Step 17
candidate is robust enough to justify building proof-grade entry intervals.

This is still not the final proof-grade certificate.  The next step must
replace empirical drift radii by rigorous Arb/FLINT or interval enclosures for
the entries of `A`, `P`, `P0`, and `Q`.

## Entry Interval Plan

- `P`: finite prime-power sum; evaluate B-spline pieces, logs, and weights
  with interval arithmetic.
- `P0`: compact-support exponential-polynomial integral; evaluate by
  piecewise exact recurrence or interval quadrature.
- `A`: interval quadrature on `[0,T]` plus analytic sinc-power tail bound.
- `Q`: interval evaluation of `exp(+/- u_j/2)`.

The guard script already supports a future `radius` mode through a CSV of
entry radii:

```text
matrix,i,j,rad
A,0,0,1e-40
P,0,0,1e-60
P0,0,0,1e-55
Q,0,0,1e-60
```

Once those radii are generated, the same penalty/Weyl guard can provide the
first proof-grade finite certificate.
