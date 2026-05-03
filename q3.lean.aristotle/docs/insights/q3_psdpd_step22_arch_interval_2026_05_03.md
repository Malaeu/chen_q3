# Step 22 -- Arch interval patch

## Goal

Replace the last drift-backed matrix in the finite PSD-pd certificate:

| Matrix | Contract after Step 22 |
|---|---|
| `P` | Arb midpoint + Arb radius |
| `Q` | Arb midpoint + Arb radius |
| `P0` | Arb midpoint + Arb radius |
| `A` | acb/Arb midpoint + radius, with tail guard |

The target remains the strengthened finite inequality

```text
Dtheta = C - theta R_kappa >= 0 on ker(Q),
R_kappa > 0 on ker(Q).
```

The penalty guard checks this without certifying the numerical nullspace basis
`N`.

## Formula

The Arch matrix is

```text
A_ij =
  ell/pi * int_0^infty
    Omega(t) |E_{ell,k}(it)|^2 cos(t d_ij) dt.
```

For the B-spline basis,

```text
|E_{ell,k}(it)|^2 =
  1/(s_k c_k) *
  sinc(ell t/(2s_k))^(2k+2).
```

Step 22 splits

```text
int_0^infty = int_0^T + int_T^infty.
```

The finite part is evaluated by `acb.integral`.  The tail is bounded using the
sinc-power decay

```text
|sinc(ell t/(2s_k))| <= 2s_k/(ell t)
```

and a conservative Arch-tail envelope

```text
|Omega(t)| <= 10 log(2+t),  t >= T.
```

For `k_spline=11`, the sinc power is `24`, so the tail is tiny at `T=260`.

## Script

Added:

```text
scripts/q3_psdpd_step22_arch_interval.py
```

The script reads Step 21 midpoint/radius CSVs, replaces only `A`, and writes
patched Step 22 CSVs.  It uses the Toeplitz structure and computes only the
unique distances `|u_j-u_i|`.

## `k_spline=11` Primary Result

Parameters:

```text
L = 3.0
ell = 0.30
delta = 0.25
k_spline = 11
kappa = 3.25
theta = 1e-4
T = 260
arb_prec = 256
```

Generated:

```text
docs/insights/q3_psdpd_step22_midpoints_k11.csv
docs/insights/q3_psdpd_step22_radii_k11.csv
```

Arch patch summary:

```text
unique distances              = 23
||A_old_mid - A_acb_mid||_2   = 9.9568088963520556e-13
||A_pilot_T - A_acb_mid||_2   = 9.9568088963520556e-13
max old rad(A)                = 1.6431300764452317e-14
max new rad(A)                = 1.2977061614918555e-17
tail radius                   = 1.3296454597994329e-18
```

Step 18 radius-mode result:

```text
||rad(A)||_2      = 1.2530477049315057e-16
||rad(P)||_2      = 6.5268739490277510e-16
||rad(P0)||_2     = 6.5970311032570478e-16
||rad(Dtheta)||_2 = 7.6233808704405884e-16

Dtheta safe_lower = 1.2228594850139608e-04
Rkappa safe_lower = 1.3569220780301769e-01
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
T = 260
arb_prec = 256
```

Generated:

```text
docs/insights/q3_psdpd_step22_midpoints_k9.csv
docs/insights/q3_psdpd_step22_radii_k9.csv
```

Arch patch summary:

```text
unique distances              = 23
||A_old_mid - A_acb_mid||_2   = 3.0132195213074030e-13
max old rad(A)                = 1.8651746813702630e-14
max new rad(A)                = 1.1903552467810403e-16
tail radius                   = 8.2313712644170306e-17
```

Step 18 radius-mode result:

```text
||rad(A)||_2      = 2.0455060480410520e-15
||rad(Dtheta)||_2 = 2.7571875130377107e-15

Dtheta safe_lower = 1.2636922932217566e-05
Rkappa safe_lower = 1.9590641960201293e-03
PASS              = True
```

## Verdict

Step 22 removes the last drift-backed entry source from the finite certificate
pipeline.  The primary `k_spline=11` finite block now has interval-backed
contracts for all four matrix sources:

```text
A, P, P0, Q.
```

The Step 18 penalty guard passes with a strong positive lower bound:

```text
Dtheta safe_lower ~= 1.22e-4
Rkappa safe_lower ~= 1.36e-1
```

This is a finite interval-backed certificate candidate, not a global RH proof.
The next mathematical layer is a family/exhaustion theorem: explain how these
finite interval certificates scale to a dense class of admissible tests with
uniform parameter control.

## Next Move

Step 23 should stop adding numerical sweeps and formulate the certificate
family contract:

```text
finite interval certificates + uniform stability + exhaustion
  -> PSD-pd on the target test class.
```

The analytic tail envelope for `Omega` should also be isolated as a reusable
lemma for later formalization.
