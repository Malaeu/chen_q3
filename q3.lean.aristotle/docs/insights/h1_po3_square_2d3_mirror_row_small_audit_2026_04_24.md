# `PO3-square.2d3` mirror-row smallness audit (2026-04-24)

## Status

Mainline audit for the first row-error estimate in
`PO3-square.2d3.row-error-estimates`.

The result is not a new branch.  It clarifies exactly what is needed to prove
`MirrorRowSmall` for the endpoint-adaptive Vandermonde rows.

## Setup

Use the interval-product notation from the shifted-error note:

```tex
A_I(x):=\prod_{j\in I}(x-j)^{-1}.
```

For the mirror row use the symmetric product avatar

```tex
B_I(x):=\prod_{j\in I}(x+j)^{-1}.
```

For a selected endpoint row `rho`, write

```tex
m_\rho(x):=\frac{A_{I_\rho}(x)}{A_{I_k}(x)}.
```

The required mirror estimate is

```tex
\sum_{x\in X} c_x B_{I_\rho}(x)
=
o\!\left(M_k\,m_\rho(\xi_k)\right),
```

where

```tex
M_k:=\max_{i\in P_k}|c_i A_{I_k}(x_i)|.
```

This is stronger than the old shell-level `mirror_decay`, because the
denominator is moving and may be much smaller than an absolute constant.

## Pointwise mirror/main ratio

For real `x>0` away from the poles,

```tex
\frac{|B_I(x)|}{|A_I(x)|}
=
\prod_{j\in I}\frac{|x-j|}{|x+j|}.
```

Every factor is `<1` when `j>0`, but this is not enough uniformly on an
unbounded support.  If `x` is far to the right of the interval, then

```tex
\frac{|x-j|}{|x+j|}=1-\frac{2j}{x+j}\approx 1,
```

and the full product need not be small without an additional tail split or
coefficient decay input.

## Clean sufficient criterion

For each selected row `rho`, split the support into a row-effective region
`X_k^{near}` and a far mirror tail `X_k^{far}`.

`MirrorRowSmall` follows if the following three estimates hold:

### 1. Pointwise suppression on the row-effective region

```tex
\eta_{k,\rho}
:=
\sup_{x\in X_k^{near}}
\frac{|B_{I_\rho}(x)|}{|A_{I_\rho}(x)|}
\to 0.
```

### 2. Absolute shifted `A`-mass control on the row-effective region

```tex
\sum_{x\in X_k^{near}} |c_x A_{I_\rho}(x)|
=
O\!\left(M_k |m_\rho(\xi_k)|\right).
```

This is stronger than signed `RemainderRowSmall`.  Signed cancellation in the
exterior remainder does not control the mirror side after absolute values are
inserted.

### 3. Far mirror tail is already small

```tex
\sum_{x\in X_k^{far}} |c_x B_{I_\rho}(x)|
=
o\!\left(M_k |m_\rho(\xi_k)|\right).
```

Then

```tex
\left|\sum_{x\in X}c_xB_{I_\rho}(x)\right|
\le
\eta_{k,\rho}
\sum_{x\in X_k^{near}} |c_xA_{I_\rho}(x)|
+
\sum_{x\in X_k^{far}} |c_xB_{I_\rho}(x)|
=
o(M_k|m_\rho(\xi_k)|).
```

This proves `MirrorRowSmall`.

## Consequence for the mainline

`MirrorRowSmall` is cheap only after an absolute row-mass statement is
available.

The old plan

```tex
signed RemainderRowSmall + mirror suppression
```

is too weak.  The mirror estimate needs the stronger input

```tex
AbsoluteRowMassControl:
\qquad
\sum_{x\notin P_k}^{near}|c_xA_{I_\rho}(x)|
=o(M_k|m_\rho(\xi_k)|)
```

plus a far-tail mirror estimate.

So the next theorem target should be:

```tex
PO3-square.2d3.absolute-row-mass-control
```

for endpoint-adaptive rows.  Once that is proved, it simultaneously gives:

- the absolute part needed by `MirrorRowSmall`;
- the signed `RemainderRowSmall`;
- stability of the same top packet under the selected endpoint rows.

## What would invalidate this route

If the real support/coefficients admit a far-right mirror tail satisfying

```tex
\sum_{x\in X_k^{far}} |c_xB_{I_\rho}(x)|
\not=
o(M_k|m_\rho(\xi_k)|),
```

or if the exterior shifted `A`-mass is large but cancels only after signs, then
the adaptive Vandermonde route is blocked at the row-error level.

That would be a real obstruction, not a shell issue.  It should be recorded in
`ACTIVE/graphs/ROUTE_KILL_REGISTRY.md` before any Hermite/residue-incompatibility
claim is made.
