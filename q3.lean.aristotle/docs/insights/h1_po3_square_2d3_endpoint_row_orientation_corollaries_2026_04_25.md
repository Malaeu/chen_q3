# `PO3-square.2d3` endpoint-row orientation corollaries (2026-04-25)

## Status

This note specializes the orientation-safe endpoint-row product asymptotic to
the two concrete endpoint orientations.

## Verdict

Left-edge upper extension works with integer rows:

```tex
I_{k,p}=[L_k,U_k+s_{k,p}],
\qquad
\alpha_p=p,
\qquad
m\text{-ratio}\to e^{-pt}.
```

Right-edge later-base lower truncation works only with bounded fractions:

```tex
I_{k,\beta}=[L_k+s_{k,\beta},U_k],
\qquad
\alpha_\beta=-\beta,
\qquad
m\text{-ratio}\to e^{+\beta t},
\qquad
0\le\beta\le1.
```

The false theorem shape is `alpha=-p` for arbitrary integer
`p=0,1,2,...` on the right edge.  Later-base lower truncation cannot remove
more than one full long-side logarithmic slope.

The fix is to use distinct fractions

```tex
0=\beta_0<\beta_1<\cdots<\beta_{n-2}\le1.
```

The limiting matrix `e^{\beta_j t_i}` is still a generalized Vandermonde
matrix on separated nodes.

## Common geometry

Let

```tex
I_k=[L_k,U_k]\cap\mathbb Z,
\qquad
K_k:=U_k-L_k\to\infty,
```

and

```tex
\Lambda_k=\sum_{j=L_k}^{U_k}\frac1{\xi_k-j}.
```

The generic product asymptotic consumes:

```tex
\Theta_{k,\rho}/\Lambda_k\to\alpha_\rho,
\qquad
S_{k,\rho}/|\Lambda_k|^2\to0,
```

plus the local tube condition, and returns

```tex
\frac{m_{k,\rho}(\xi_k+t/\Lambda_k)}
     {m_{k,\rho}(\xi_k)}
\to e^{-\alpha_\rho t}.
```

## Left-edge upper extension

Assume

```tex
\xi_k=L_k+\theta_k,
\qquad
\theta_k\in[\tau,1-\tau],
\qquad
0<\tau<1/2.
```

Then

```tex
\Lambda_k=-\log K_k+O_\tau(1),
\qquad
|\Lambda_k|\asymp\log K_k.
```

For fixed integer `p>=0`, use

```tex
I_{k,p}^{L,+}=[L_k,U_k+s_{k,p}].
```

Define

```tex
H_k^+(s):=\sum_{r=1}^{s}\frac1{\xi_k-(U_k+r)}.
```

Choose

```tex
s_{k,p}:=\min\{s\ge0:H_k^+(s)\le p\Lambda_k\}.
```

The crossing error is at most the first step:

```tex
|H_k^+(s_{k,p})-p\Lambda_k|
\ll 1/K_k.
```

Therefore

```tex
H_k^+(s_{k,p})/\Lambda_k\to p.
```

For this row, `Theta_{k,p}=H_k^+(s_{k,p})`, so `alpha_p=p`.

The second-order term satisfies

```tex
S_{k,p}\ll1/K_k,
\qquad
S_{k,p}/|\Lambda_k|^2\to0,
```

and the local tube holds because moved poles are at distance `asymp K_k`.

Thus

```tex
\frac{m_{k,p}^{L,+}(\xi_k+t/\Lambda_k)}
     {m_{k,p}^{L,+}(\xi_k)}
\to e^{-pt}
```

uniformly for fixed bounded `p` and compact `t`.

Lean-facing names:

```text
po3_left_edge_upper_extension_theta_slope
po3_left_edge_upper_extension_endpoint_row_asymptotic
```

## Right-edge later-base lower truncation

Assume

```tex
\xi_k=U_k-\theta_k,
\qquad
\theta_k\in[\tau,1-\tau],
\qquad
0<\tau<1/2.
```

Then

```tex
\Lambda_k=\log K_k+O_\tau(1),
\qquad
|\Lambda_k|\asymp\log K_k.
```

Later-base lower truncation uses

```tex
I_{k,\beta}^{R,tr}=[L_k+s_{k,\beta},U_k].
```

Use fractions `beta in [0,1]`, not arbitrary integers.

Define

```tex
H_k^-(s):=\sum_{r=0}^{s-1}\frac1{\xi_k-(L_k+r)}.
```

For `0<=beta<1`, choose

```tex
s_{k,\beta}:=\min\{s\ge0:H_k^-(s)\ge\beta\Lambda_k\}.
```

For `beta=1`, remove the whole long lower side up to the bounded right-edge
gap.

Then

```tex
H_k^-(s_{k,\beta})/\Lambda_k\to\beta.
```

Since lower truncation removes poles,

```tex
\Theta_{k,\beta}=-H_k^-(s_{k,\beta}),
```

so

```tex
\Theta_{k,\beta}/\Lambda_k\to-\beta.
```

Thus

```tex
\frac{m_{k,\beta}^{R,tr}(\xi_k+t/\Lambda_k)}
     {m_{k,\beta}^{R,tr}(\xi_k)}
\to e^{+\beta t}.
```

For `0<=beta<1`, crossing occurs with

```tex
K_k-s_{k,\beta}\asymp K_k^{1-\beta},
```

and

```tex
S_{k,\beta}\ll K_k^{\beta-1},
\qquad
S_{k,\beta}/|\Lambda_k|^2\to0.
```

For `beta=1`, the pole-near gap is excluded by `theta_k in [tau,1-tau]`, so

```tex
S_{k,1}=O_\tau(1),
\qquad
S_{k,1}/|\Lambda_k|^2\to0.
```

The local tube condition holds uniformly for any fixed finite beta-family.

Lean-facing names:

```text
po3_right_edge_lower_truncation_theta_slope
po3_right_edge_lower_truncation_endpoint_row_asymptotic
```

## Right-edge obstruction

Later-base lower truncation can only realize

```tex
\alpha=-\beta,\qquad 0\le\beta\le1.
```

It cannot realize `alpha=-p` for integer `p>1`, because the full removable
long-side harmonic sum is only

```tex
H_k^-(s)\le \Lambda_k+O(1).
```

Thus

```tex
\limsup |\Theta_{k,\rho}/\Lambda_k|\le1.
```

Lean-facing name:

```text
po3_right_edge_lower_truncation_ratio_le_one_asymptotically
```

This does not kill the right-edge branch.  It only kills the false
integer-`p` formulation.  Distinct fractional exponents are enough for the
bounded-separated Vandermonde/stable-projection wrapper.

## Lean status

The PO3Cert file now contains marker consumers:

```text
PO3LeftEdgeUpperExtensionAsymptoticCertificate
po3_left_edge_upper_extension_endpoint_row_asymptotic

PO3RightEdgeLowerTruncationAsymptoticCertificate
po3_right_edge_lower_truncation_endpoint_row_asymptotic

PO3RightEdgeLowerTruncationRatioLeOneCertificate
po3_right_edge_lower_truncation_ratio_le_one_asymptotically
```

The next real proof is to replace these markers by concrete product estimates
or feed them from a focused Aristotle/Lean lemma packet.
