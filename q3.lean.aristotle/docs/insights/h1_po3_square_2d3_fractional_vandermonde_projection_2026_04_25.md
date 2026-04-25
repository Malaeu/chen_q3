# `PO3-square.2d3` fractional Vandermonde projection (2026-04-25)

## Status

This note closes the matrix-shape question created by the right-edge
orientation correction.

Right-edge later-base lower truncation only gives fractional rows

```tex
e^{\beta t},\qquad 0\le\beta\le1.
```

Use the concrete choice

```tex
\beta_j=\frac{j}{n-1},
\qquad j=0,\dots,n-2.
```

Then the limiting matrix is ordinary Vandermonde:

```tex
W_{j,i}=e^{\beta_j t_i}
=
\left(e^{t_i/(n-1)}\right)^j.
```

Set

```tex
y_i:=e^{t_i/(n-1)}.
```

## Static matrix theorem

Let

```tex
W(y)_{j,i}=y_i^j,
\qquad j=0,\dots,n-2,\quad i=1,\dots,n.
```

If the `y_i` are pairwise distinct, then `W` has rank `n-1` and
`dim ker W = 1`.

Indeed, deleting any column gives an ordinary square Vandermonde matrix with
determinant

```tex
\prod_{a<b}(y_b-y_a)\ne0.
```

A kernel generator is

```tex
h_i=
\frac{1}{\prod_{\ell\ne i}(y_i-y_\ell)}.
```

Then

```tex
\sum_i h_i y_i^j=0,\qquad j=0,\dots,n-2.
```

## Uniform singular gap

For bounded `n<=n0`, assume

```tex
R_-\le |y_i|\le R_+,
\qquad
|y_i-y_\ell|\ge\Delta>0.
```

The class of such nodes is compact.  The smallest nonzero singular value of
the rectangular Vandermonde matrix is continuous and positive on this compact
set.  Therefore there is a uniform gap

```tex
\sigma_*=\sigma_*(n0,R_-,R_+,\Delta)>0.
```

For the orthogonal projection `Pi_y` onto `ker W(y)`,

```tex
\|u-\Pi_yu\|_2\le\sigma_*^{-1}\|W(y)u\|_2.
```

## Perturbed endpoint-row theorem

The real endpoint-row matrix is

```tex
V_{k,j,i}
=
\frac{m_{\rho_{k,\beta_j}}(x_{k,i})}
     {m_{\rho_{k,\beta_j}}(\xi_k)}.
```

The product asymptotic gives

```tex
V_{k,j,i}=e^{\beta_j t_{k,i}}+o(1)=y_{k,i}^j+o(1),
\qquad
y_{k,i}=e^{t_{k,i}/(n_k-1)}.
```

Assume

```tex
2\le n_k\le n0,
\qquad
R_-\le |y_{k,i}|\le R_+,
\qquad
|y_{k,i}-y_{k,\ell}|\ge\Delta.
```

If `||V_k-W_k||_op -> 0`, then singular-value continuity gives

```tex
\sigma^+(V_k)\ge\sigma_*/2
```

for large `k`.  Hence

```tex
\|u-\Pi_ku\|_2\le(2/\sigma_*)\|V_ku\|_2.
```

For the row equation `V_k q_k = epsilon_k`,

```tex
\|q_k-\Pi_kq_k\|_2
\le
(2/\sigma_*)\|\epsilon_k\|_2.
```

Since `n_k<=n0`, componentwise row error `max_j |epsilon_{k,j}| -> 0` is
enough.

## Correct separation condition

For the right-edge fractional rows, the correct nodes are

```tex
y_{k,i}=e^{t_{k,i}/(n_k-1)}.
```

Do not certify the right-edge branch using only separation of `e^{-t_i}`.
On compact sets such separation may imply the needed condition, but the
certificate should check the actual fractional nodes.

Route-kill the bounded-separated right-edge branch if

```tex
\min_{i\ne\ell}
|e^{t_{k,i}/(n_k-1)}-e^{t_{k,\ell}/(n_k-1)}|
\to0
```

and no confluent/Hermite stable-projection replacement is supplied.

## Lean status

The PO3Cert file now contains the right-edge fractional certificate:

```text
PO3FractionalVandermondeStableProjectionCertificate
po3_endpoint_rows_stable_projection_of_fractional_right_edge_vandermonde
```

and the route-kill marker:

```text
PO3FractionalRightEdgeNodeCollapseRouteKillCertificate
po3_fractional_right_edge_capture_route_kill_of_node_collapse
```

The next proof task is to connect the concrete right-edge endpoint-row product
asymptotic to this fractional Vandermonde certificate, or record node collapse.
