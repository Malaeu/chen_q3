# `PO3-square.2d3`: shift-orientation audit after adaptive constraints

Date: 2026-04-24

Status: mainline correction.  This note self-checks the adaptive-shift
constraint idea and prevents a false theorem-shape from becoming canonical.

## Problem

The adaptive-shift note correctly identifies the desired matrix mechanism:
shifted wall equations should produce rows converging to a Vandermonde block.
But the first version only used future upper-end shifts `k -> k+s`.  That is
not symmetric enough for the full edge-log regime.

Use the interval-product notation

```text
A_{L,U}(x) := prod_{j=L}^{U} (x-j)^(-1),
Lambda_{L,U}(x) := sum_{j=L}^{U} 1/(x-j).
```

For the current `PO3` tower, `L=N+1` and `U=N+k+1`.

The edge-log slope comes from the long side of the pole interval:

- if `x` is near the left endpoint `L`, the long side is to the right;
- if `x` is near the right endpoint `U`, the long side is to the left.

Therefore a shifted constraint must move the endpoint on the long side.

## Left-edge case

If `x` is near `L`, upper-end shifts can see the long side.  However, future
shifts `U -> U+s` may need very large `s` to accumulate a logarithmic amount
from newly added distant poles, which can destabilize the top packet.

A cleaner test uses backward upper truncations:

```text
U_p < U,       A_{L,U_p}(x) = A_{L,U}(x) * prod_{j=U_p+1}^{U} (x-j).
```

Choose `U_p` so that

```text
sum_{j=U_p+1}^{U} 1/(xi_k-j) / Lambda_{L,U}(xi_k) -> alpha_p,
```

with distinct `alpha_p` in `(0,1)`.  For example, if the center is left-edge,
`U_p-L` can be a power of `U-L`.  This keeps the sampled endpoint large while
extracting a nontrivial fraction of the logarithmic slope.

## Right-edge case

If `x` is near `U`, the logarithmic slope comes from the left side.  Moving only
the upper endpoint `U` does not naturally see that long side:

- adding future poles to the right accumulates the wrong orientation and may
  require huge shifts;
- deleting a few upper poles only sees the short side near `U`, not the long
  left side.

The correct dual operation is to move the lower endpoint:

```text
L_p > L,       A_{L_p,U}(x) = A_{L,U}(x) * prod_{j=L}^{L_p-1} (x-j).
```

Choose `L_p` so that

```text
sum_{j=L}^{L_p-1} 1/(xi_k-j) / Lambda_{L,U}(xi_k) -> alpha_p.
```

Then the normalized rows again converge to

```text
exp(-alpha_p t_i)
```

up to the chosen orientation convention, and the finite constraint matrix is a
Vandermonde block for distinct local coordinates.

## New exact blocker

The adaptive-shift route is valid only if the wall identity is available as a
two-endpoint family, not just as a one-parameter `k` family with fixed `N`.

The next theorem target must therefore be:

```text
PO3-square.2d3b5-orient:
  either prove that the transform-side wall can be sampled with both endpoint
  shifts L and U, or prove that real near-maximizers never occur in the
  endpoint orientation not visible to the available shifts.
```

If neither is true, then the current finite-packet capture route is incomplete:
it can extract constraints only from one edge-log orientation and cannot close
`PO3-square.2d3` globally.

## Practical next step

Check the closed lower-shell feeder and the `H_a(alpha_r)=0` to square/gamma
reduction for the exact quantifiers in `N`:

- if the tail-zero/gamma wall is available for every sufficiently large base
  `N`, then lower-end shifts are legitimate and the two-endpoint adaptive
  Vandermonde route survives;
- if `N` is frozen once and for all, then right-edge edge-log is the new hard
  blocker and must be killed by a separate argument before Hermite capture can
  finish the wall.

This is the next mainline check.  Do not proceed to residue-incompatibility
until the endpoint-orientation issue is resolved.
