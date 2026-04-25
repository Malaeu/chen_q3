# `PO3-square.2d3` log-loss mirror control (2026-04-25)

## Status

Mainline correction of the `AbsoluteRowMassControl` target.

The previous endpoint-row audit correctly identified that `MirrorRowSmall`
needs absolute row-mass input.  The sharper review shows that the unconditional
inputs currently allowed on the mainline,

```tex
Y_a=\{x_\gamma,x_\gamma-1\},\qquad x_\gamma=a\gamma/\pi,
\qquad |c_\gamma|\lesssim \gamma^{-3},
```

do not imply the stronger `o(D_{k,\rho})` exterior `A`-mass estimate for a
fixed finite packet.  They imply only a log-loss absolute row-mass bound.

## Verdict

`AbsoluteRowMassControl` is not viable as stated.

The correct split is:

1. prove `MirrorRowSmall` by a log-loss absolute row-mass estimate plus strong
   enough pointwise mirror suppression;
2. keep `RowClusterExhaustion` as the separate hard blocker for the signed
   main-side `A`-remainder.

## Why zero counting gives only log loss

Classical zero counting gives local bounds of the form

```tex
N(T+1)-N(T-1)\ll \log(2+T).
```

This is consistent with explicit Riemann--von Mangoldt error bounds such as

```tex
\left|N(T)-\frac{T}{2\pi}\log\frac{T}{2\pi e}\right|
\le 0.1038\log T+0.2573\log\log T+9.3675,
```

where `N(T)` counts nontrivial zeta zeros with `0 < Im rho <= T`.  See
Hasanalizade--Shen--Wong, arXiv:2107.06506, and DLMF 25.10 for the standard
zero-counting/Riemann--Siegel context.

With `|c_y|\ll |y|^{-3}` this gives

```tex
\sum_{y\in Y_a\cap[T,T+1]} |c_y|
\ll \frac{\log(2+T)}{T^3}.
```

It does not give spacing.  In particular, it does not rule out several support
points inside an endpoint-row window of size `1/|\Lambda_k(\xi_k)|`.

For a row interval `I`,

```tex
\frac{A_I(\xi+\delta)}{A_I(\xi)}
=
\exp\left(
-\delta\sum_{j\in I}\frac1{\xi-j}
+O\left(\delta^2\sum_{j\in I}\frac1{|\xi-j|^2}\right)
\right).
```

Thus support points with

```tex
|y-\xi_k|=o(1/|\Lambda_k(\xi_k)|)
```

are almost indistinguishable by the endpoint-row products.  Polynomial
coefficient decay does not make their coefficients smaller on this local
scale.

## Theorem target 1: log-loss row mass

```text
endpoint_row_log_mass_bound_of_zero_counting
```

Let `W_{k,\rho}\subset Y_a` be a row-local window contained in
`[\xi_k-1,\xi_k+1]`.  Assume:

1. `Y_a={x_gamma,x_gamma-1}`, `x_gamma=a gamma/pi`, with multiplicity counted.
2. Local zero counting:

```tex
\#\{\gamma: |a\gamma/\pi-\xi_k|\le 2\}
\ll \log(2+\xi_k).
```

3. Coefficient decay:

```tex
|c_y|\ll (1+|y|)^{-3}.
```

4. Row distortion on the local window:

```tex
\sup_{y\in W_{k,\rho}}
\left|\frac{A_{I_k}(y)}{A_{I_k}(\xi_k)}\right|\le C_A,
\qquad
\sup_{y\in W_{k,\rho}}
\left|\frac{m_\rho(y)}{m_\rho(\xi_k)}\right|\le C_m.
```

5. Packet-scale comparability:

```tex
\sup_{y\in W_{k,\rho}} |c_yA_{I_k}(y)|\le C_M M_k.
```

Then

```tex
\sum_{y\in W_{k,\rho}} |c_yA_{I_\rho}(y)|
\ll
\log(2+\xi_k)\,M_k|m_\rho(\xi_k)|.
```

Proof sketch:

```tex
|c_yA_{I_\rho}(y)|
= |c_yA_{I_k}(y)|\,|m_\rho(y)|
\le C\,M_k|m_\rho(\xi_k)|
```

for each `y in W_{k,\rho}`.  The number of such points is
`O(log(2+\xi_k))`.

## Theorem target 2: log-loss mirror smallness

```text
EndpointRowLogMassMirrorControl
```

Assume the log-loss row-mass bound above and define

```tex
\eta_{k,\rho}:=
\sup_{y\in X^{near}_{k,\rho}}
\frac{|B_{I_\rho}(y)|}{|A_{I_\rho}(y)|}.
```

If

```tex
\eta_{k,\rho}\log(2+\xi_k)\to0
```

and the far mirror tail satisfies

```tex
\sum_{y\in X^{far}_{k,\rho}} |c_yB_{I_\rho}(y)|
=o(M_k|m_\rho(\xi_k)|),
```

then

```tex
\sum_{y\in X} c_yB_{I_\rho}(y)
=o(M_km_\rho(\xi_k)).
```

This proves `MirrorRowSmall` without pretending that the stronger exterior
`A`-mass estimate follows from zero counting.

## Theorem target 3: row-cluster exhaustion

```text
RowClusterExhaustion
```

The main-side remainder still needs the separate estimate

```tex
\sum_{y\in X^{near}_{k,\rho}\setminus P_k}
|c_yA_{I_\rho}(y)|
=o(M_k|m_\rho(\xi_k)|).
```

This is not implied by the allowed inputs.  It is the next real hard blocker:
the selected packet `P_k` must contain all row-scale support points with
comparable normalized contribution, or the finite Vandermonde packet route is
not legitimate.

## Route-kill criterion

Kill the fixed finite-packet adaptive Vandermonde route if there are selected
rows `rho_k`, centers `xi_k`, and omitted exterior points `y_k\notin P_k`
such that

```tex
\Lambda_k(\xi_k)(y_k-\xi_k)=O(1)
```

and

```tex
|c_{y_k}A_{I_{\rho_k}}(y_k)|
\asymp
M_k|m_{\rho_k}(\xi_k)|.
```

Also kill the fixed finite-packet version if, for some `delta>0`, the number
of comparable row-scale support points is unbounded:

```tex
\#\left\{
y\in Y_a:
|c_yA_{I_k}(y)|\,|m_\rho(y)|
\ge \delta M_k|m_\rho(\xi_k)|
\right\}\to\infty.
```

Counting allows such clusters up to logarithmic size.  Only an additional
spacing/no-resonance/cluster-exhaustion input can rule them out.

## Mainline consequence

The immediate next step is not Hermite residue incompatibility.  It is:

```text
prove log-loss mirror control now;
isolate RowClusterExhaustion as the hard blocker.
```

Once `MirrorRowSmall` is closed under the log-loss condition, the remaining
route-critical input is exactly `RowClusterExhaustion`, or the route-kill
obstruction above.
