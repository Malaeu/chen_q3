# `PO3-square.2d3` endpoint-row product asymptotic (2026-04-25)

## Status

This note records the orientation-safe row-limit theorem needed by the
bounded-separated stable-projection branch.

The important correction is that the endpoint-row limit is not always
`e^{-pt}`.  The correct general form is

```tex
\frac{m_{k,p}(\xi_k+t/\Lambda_k)}
     {m_{k,p}(\xi_k)}
\to
e^{-\alpha_p t}.
```

For left-edge upper extensions one expects `alpha_p=p`.  For right-edge
later-base lower truncations one often gets `alpha_p=-p`, hence the row limit
is `e^{+pt}`.  This is not a route-kill: it just changes the Vandermonde nodes
from `e^{-t_i}` to `e^{t_i}`.

## Product model

Use integer intervals

```tex
I[L,U]=\{j\in\mathbb Z:L\le j\le U\}.
```

For a row interval `I`, define

```tex
A_I(x):=\prod_{j\in I}(x-j)^{-1}.
```

Let the base interval be

```tex
I_k=I[L_k,U_k]
```

and the endpoint row be

```tex
I_{k,p}=I_{k,\rho_p}.
```

The multiplier is

```tex
m_{k,p}(x):=\frac{A_{I_{k,p}}(x)}{A_{I_k}(x)}.
```

Set

```tex
P^+_{k,p}:=I_{k,p}\setminus I_k,
\qquad
P^-_{k,p}:=I_k\setminus I_{k,p}.
```

Then

```tex
m_{k,p}(x)=
\prod_{j\in P^+_{k,p}}(x-j)^{-1}
\prod_{j\in P^-_{k,p}}(x-j).
```

Relative to `xi_k`,

```tex
\frac{m_{k,p}(\xi_k+h)}{m_{k,p}(\xi_k)}
=
\prod_{j\in P^+_{k,p}}
\left(1+\frac{h}{\xi_k-j}\right)^{-1}
\prod_{j\in P^-_{k,p}}
\left(1+\frac{h}{\xi_k-j}\right).
```

This is the exact product identity.

## Theta and second-order control

Define the base slope

```tex
\Lambda_k(\xi_k):=
\Lambda_{I_k}(\xi_k):=
\sum_{j\in I_k}\frac1{\xi_k-j}.
```

Define the endpoint multiplier slope

```tex
\Theta_{k,p}(\xi_k):=
\Lambda_{I_{k,p}}(\xi_k)-\Lambda_{I_k}(\xi_k)
=
\sum_{j\in P^+_{k,p}}\frac1{\xi_k-j}
-
\sum_{j\in P^-_{k,p}}\frac1{\xi_k-j}.
```

Define

```tex
S_{k,p}(\xi_k):=
\sum_{j\in P^+_{k,p}\cup P^-_{k,p}}
\frac1{|\xi_k-j|^2}.
```

For `p=0`, take `I_{k,0}=I_k`, so `m_{k,0}=1`,
`Theta_{k,0}=0`, and `S_{k,0}=0`.

## General theorem target

```text
po3_endpoint_row_multiplier_uniform_asymptotic_of_theta_slope
```

Fix `T>0`.  Let `|t|<=T`, and let `p` range over a bounded finite set
`0<=p<=n0-2`.  Assume uniformly in `p`:

1. edge-log scale:

```tex
|\Lambda_k(\xi_k)|\to\infty,
\qquad
\Lambda_k(\xi_k)\ne0;
```

2. local tube/no moved pole collision:

```tex
\sup_{j\in P^+_{k,p}\cup P^-_{k,p}}
\frac{T}{|\Lambda_k(\xi_k)|\,|\xi_k-j|}
\to0;
```

3. adaptive theta-slope:

```tex
\Theta_{k,p}(\xi_k)/\Lambda_k(\xi_k)\to\alpha_p;
```

4. second-order smallness:

```tex
S_{k,p}(\xi_k)/|\Lambda_k(\xi_k)|^2\to0.
```

Then

```tex
\sup_{0\le p\le n0-2}\sup_{|t|\le T}
\left|
\frac{m_{k,p}(\xi_k+t/\Lambda_k)}
     {m_{k,p}(\xi_k)}
-
e^{-\alpha_p t}
\right|
\to0.
```

## Proof sketch

Put

```tex
h:=t/\Lambda_k.
```

For all moved poles, the local tube assumption gives

```tex
|h/(\xi_k-j)|\le1/2
```

eventually.  Therefore

```tex
\log(1+z)=z+O(|z|^2),
\qquad
\log(1+z)^{-1}=-z+O(|z|^2).
```

Using the exact product identity,

```tex
\log
\frac{m_{k,p}(\xi_k+h)}
     {m_{k,p}(\xi_k)}
=
-h\left(
\sum_{j\in P^+_{k,p}}\frac1{\xi_k-j}
-
\sum_{j\in P^-_{k,p}}\frac1{\xi_k-j}
\right)
+
O\left(
|h|^2
\sum_{j\in P^+_{k,p}\cup P^-_{k,p}}
\frac1{|\xi_k-j|^2}
\right).
```

Thus

```tex
\log
\frac{m_{k,p}(\xi_k+t/\Lambda_k)}
     {m_{k,p}(\xi_k)}
=
-\frac{t}{\Lambda_k}\Theta_{k,p}(\xi_k)
+
O_T\left(
\frac{S_{k,p}(\xi_k)}{|\Lambda_k|^2}
\right).
```

The theta-slope assumption gives the main term `-alpha_p t`, and the
second-order assumption gives `o(1)`, uniformly for bounded `p` and compact
`t`.  Exponentiation gives the claimed multiplier limit.

## Orientation cases

### Left-edge upper extension

If the packet is near the left edge and the long side is to the right, use

```tex
I_{k,p}^{L,+}=I[L_k,U_k+s_{k,p}].
```

Then

```tex
P^+_{k,p}=\{U_k+1,\dots,U_k+s_{k,p}\},
\qquad
P^-_{k,p}=\varnothing.
```

The slope is

```tex
\Theta_{k,p}(\xi_k)=
\sum_{j=U_k+1}^{U_k+s_{k,p}}\frac1{\xi_k-j}.
```

Choose `s_{k,p}` so that `Theta/Lambda -> p`.  The row limit is `e^{-pt}`.

### Right-edge later-base lower truncation

For a right-edge packet, the available later-base row is

```tex
I_{k,p}^{R,tr}=I[L_k+s_{k,p},U_k].
```

Then

```tex
P^-_{k,p}=\{L_k,\dots,L_k+s_{k,p}-1\},
```

and

```tex
\Theta_{k,p}(\xi_k)=
-
\sum_{j=L_k}^{L_k+s_{k,p}-1}\frac1{\xi_k-j}.
```

If the removed lower-side sum divided by `Lambda_k` tends to `p`, then

```tex
\Theta_{k,p}/\Lambda_k\to -p
```

and the row limit is `e^{+pt}`.

This is acceptable for Vandermonde capture: use nodes `e^{t_i}` rather than
`e^{-t_i}`.

### Right-edge lower extension obstruction

The sign-correct row for literal `e^{-pt}` at the right edge would extend the
lower endpoint:

```tex
I[L_k-s_{k,p},U_k].
```

That needs an earlier base, not the later-base monotonicity currently frozen.
Do not assume it unless the wall identity is actually available for earlier
bases.

## Lean status

The orientation-safe certificate is frozen in
`Q3/Proofs/PO3Cert/PO3SquareSignedDominanceCertificate_2026_04_21.lean`:

```text
PO3EndpointRowProductAsymptoticCertificate
po3_endpoint_row_multiplier_uniform_asymptotic_of_theta_slope
```

This is currently a certificate consumer.  The analytic proof still has to
show the theta-slope and second-order hypotheses for the real endpoint rows.

## Next target

The next proof should specialize the product asymptotic to the two concrete
orientation cases:

```text
left_edge_upper_extension_gives_exp_neg_rows
right_edge_lower_truncation_gives_exp_pos_rows
```

Those two corollaries then feed the bounded-separated stable projection
certificate.
