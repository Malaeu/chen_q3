# Q3 PSD-pd Step 17 Finite Certificate Extraction (2026-05-03)

Status: in progress / drift-guard numerical certificate

Placement:

- This continues the fallback `PSD-pd` finite certificate route.
- It does not claim RH.
- It extracts a finite proof-candidate inequality suitable for Step 18
  interval certification.

Script:

```text
scripts/q3_psdpd_step17_extract_certificate.py
```

Output:

```text
docs/insights/q3_psdpd_step17_k11_kappa_scan.csv
docs/insights/q3_psdpd_step17_k9_kappa_scan.csv
```

## Goal

Certify a strengthened finite inequality:

```math
C^\circ \succeq \theta R_\kappa^\circ,
\qquad
R_\kappa^\circ \succ 0,
```

where:

```math
C=A-P,\qquad
R_\kappa=A-\kappa P_0,\qquad
S_\kappa=P-\kappa P_0.
```

Equivalently:

```math
D_\theta^\circ=C^\circ-\theta R_\kappa^\circ\succeq0.
```

This is stronger than finite PSD of `C^circ` and gives an explicit drift
budget for the final interval proof.

## Primary candidate

Chosen from the stable same-profile Step 16 branch:

```text
k_spline=11
ell=0.30
delta=0.25
kappa=3.25
theta=1e-4
arch_tmax=260
arch_nt=48001
p0_na=24001
```

Base quadrature:

```text
eig_min(C,G)       = 1.8338037892862786e-04
eig_min(R_k,G)     = 1.3535348018636173e-01
eig_min(D_theta,G) = 1.1537873311854264e-04
rel_max(S_k,R_k)   = 9.9973042467725000e-01
rel_margin         = 2.6957532274995977e-04
||Q N||_F          = 5.592e-15
||C-(R-S)||_F      = 3.661e-16
```

This proves numerically, on this finite level:

```math
C^\circ \succeq 10^{-4} R_\kappa^\circ
```

with remaining generalized lower bound:

```text
eig_min(D_theta,G)≈1.15e-4.
```

## Kappa scan

For the primary candidate with `theta=1e-4`, every tested kappa from `2.50` to
`4.25` passes both:

```text
R_kappa^circ > 0
D_theta^circ > 0
```

Summary:

| kappa | eig_min(R,G) | eig_min(Dtheta,G) | rel_margin | pass |
| ---: | ---: | ---: | ---: | :--- |
| 2.50 | `3.5226087809e-02` | `1.1616221982e-04` | `2.7266610939e-04` | true |
| 3.25 | `1.3535348019e-01` | `1.1537873312e-04` | `2.6957532275e-04` | true |
| 4.25 | `2.2907039170e-01` | `1.1433109319e-04` | `2.6553356737e-04` | true |

The scan CSV has 71 rows and 71 passing rows.

## Quadrature drift guard

Primary drift test:

| arch_tmax | arch_nt | p0_na | eig_min(Dtheta,G) | eig_min(R,G) | rel_margin | dD | dR | dC |
| ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| 220 | 36001 | 18001 | `1.1537891122e-04` | `1.3537516083e-01` | `2.6957603130e-04` | `3.886e-09` | `3.886e-05` | `2.448e-14` |
| 260 | 48001 | 24001 | `1.1537873312e-04` | `1.3535348019e-01` | `2.6957532275e-04` | `0.000e+00` | `0.000e+00` | `0.000e+00` |
| 320 | 64001 | 32001 | `1.1537831072e-04` | `1.3535988246e-01` | `2.6957364801e-04` | `2.895e-09` | `2.895e-05` | `1.598e-14` |

Safe lower bounds after subtracting tested drift:

```text
safe_R_lower      = 1.3531462169491143e-01
safe_Dtheta_lower = 1.1537484728942835e-04
safe_C_lower      = 1.8338037890414558e-04
```

Verdict:

```text
PASS drift-guard: R_k and D_theta remain positive under tested quadrature variants.
```

## Control candidate

The original Step 16 baseline also passes with a smaller theta:

```text
k_spline=9
ell=0.30
delta=0.25
kappa=3.075
theta=1e-5
```

Base quadrature:

```text
eig_min(C,G)       = 1.9647793435239931e-05
eig_min(R_k,G)     = 1.9438124191560983e-03
eig_min(D_theta,G) = 1.3164546746145258e-05
rel_margin         = 3.0305236804029080e-05
```

Drift-guard safe bounds:

```text
safe_R_lower      = 1.9435549694985165e-03
safe_Dtheta_lower = 1.3164544175238416e-05
safe_C_lower      = 1.9647793411946166e-05
```

The control kappa scan has 71 rows and 48 passing rows; it becomes viable at
`kappa=3.075` and remains viable through `4.25`.

## Interpretation

Step 17 upgrades the Step 16 plateau into an explicit finite certificate target:

```math
\boxed{
C^\circ \succeq 10^{-4} R_\kappa^\circ
}
```

for the primary `k_spline=11`, `ell=0.30`, `delta=0.25`, `kappa=3.25`
candidate.

This is the right object for Step 18 because it supplies a concrete error
budget.  The tested quadrature drift is far below the remaining lower bound:

```text
max_Dtheta_drift≈3.89e-9
eig_min(Dtheta,G)≈1.15e-4
```

so the numerical margin is about four orders of magnitude larger than the
tested drift.

## Verdict

Primary proof-candidate:

```text
k_spline=11
ell=0.30
delta=0.25
kappa=3.25
theta=1e-4
```

Control proof-candidate:

```text
k_spline=9
ell=0.30
delta=0.25
kappa=3.075
theta=1e-5
```

Recommended next target:

```math
\boxed{
\text{Step 18: interval-certified entries for }A,\ P_0,\ P.
}
```

The priority is now to replace the drift guard with rigorous interval bounds
on the matrix entries and then prove
`D_theta^circ >= 0` by interval/LDL or interval-Cholesky certification.
