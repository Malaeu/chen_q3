# Step 21 -- Proof-grade P0 interval patch

## Goal

Replace drift-based `P0` radii by Arb midpoint/radius computed from
piecewise B-spline exponential integrals.

After this step:

| Matrix | Contract |
|---|---|
| `P` | Arb midpoint + Arb radius |
| `Q` | Arb midpoint + Arb radius |
| `P0` | Arb midpoint + Arb radius |
| `A` | float midpoint + drift radius |

Thus the only remaining non-proof-grade matrix in the finite certificate is
the Arch matrix `A`.

## Formula

The continuous prime-main matrix is

```text
(P0)_ij =
  int_0^{2L} e^{a/2}
  [ r_k((d_ij-a)/ell) + r_k((d_ij+a)/ell) ] da.
```

With the substitution used by Step 21:

```text
P0^+(d) = ell e^{d/2}
          int_{(d-2L)/ell}^{d/ell} e^{-ell x/2} r_k(x) dx,

P0^-(d) = ell e^{-d/2}
          int_{d/ell}^{(d+2L)/ell} e^{ell x/2} r_k(x) dx.
```

For B-splines,

```text
r_k(x) = b_{2k+1}(s_k x) / c_k
```

is a polynomial on each spline segment.  Step 21 splits the integral at all
spline breakpoints and evaluates each piece as an Arb ball using

```text
int exp(lambda x) polynomial(x) dx.
```

## Script

Added:

```text
scripts/q3_psdpd_step21_p0_interval.py
```

The script reads Step 20 midpoint/radius CSVs, replaces only `P0`, and writes
patched CSVs.

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
docs/insights/q3_psdpd_step21_midpoints_k11.csv
docs/insights/q3_psdpd_step21_radii_k11.csv
```

P0 patch summary:

```text
||P0_old_mid - P0_arb_mid||_2 = 2.7970066670295662e-05
||P0_old_rad - P0_arb_rad||_2 = 7.6609190830408588e-05
max old rad(P0)               = 1.2179468440010055e-05
max new rad(P0)               = 1.4346310462727313e-16
```

Step 18 radius-mode result:

```text
||rad(P)||_2      = 6.5268739490277510e-16
||rad(P0)||_2     = 6.5970311032570478e-16
||rad(Dtheta)||_2 = 8.1709133786136165e-14

Dtheta safe_lower = 1.2228594834390210e-04
Rkappa safe_lower = 1.3569220780294897e-01
PASS              = True
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
docs/insights/q3_psdpd_step21_midpoints_k9.csv
docs/insights/q3_psdpd_step21_radii_k9.csv
```

P0 patch summary:

```text
||P0_old_mid - P0_arb_mid||_2 = 5.0207272109570589e-08
||P0_old_rad - P0_arb_rad||_2 = 6.7531766438222302e-07
max old rad(P0)               = 1.4818841709285380e-07
max new rad(P0)               = 2.0592753938766065e-16
```

Step 18 radius-mode result:

```text
||rad(P0)||_2     = 7.7626345855150444e-16
||rad(Dtheta)||_2 = 1.1468555030175416e-13

Dtheta safe_lower = 1.2636922668453045e-05
Rkappa safe_lower = 1.9590641959251385e-03
PASS              = True
```

## Verdict

Step 21 removes the second temporary part of the finite certificate.  The
finite pipeline now has Arb midpoint/radius contracts for `P`, `Q`, and `P0`.

The remaining proof-grade target is `A`.

The `k_spline=11` branch remains the primary finite proof-candidate:

```text
Dtheta safe_lower ~= 1.22e-4
Rkappa safe_lower ~= 1.36e-1
```

with only the Arch matrix still using drift radii.

## Next Move

Step 22 should replace the Arch matrix `A` drift radius with interval
quadrature plus an analytic sinc-power tail bound.
