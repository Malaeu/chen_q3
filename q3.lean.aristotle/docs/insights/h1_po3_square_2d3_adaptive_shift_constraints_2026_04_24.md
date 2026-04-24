# `PO3-square.2d3`: adaptive shift constraints for the edge-log branch

Date: 2026-04-24

Status: mainline working note.  This note does not close the analytic wall.
It freezes the next exact theorem-shape after the reciprocal-product slope
trichotomy.

## Position

The lower `PO3` feeder is frozen.  The live wall is still the transform-side
Gamma tower

```text
sum_x c_x A_k(x) = sum_x c_x B_k(x)
```

with the reciprocal-product avatar for the main side.  The slope trichotomy
shows that the naive `1/log k` packet model is legitimate only in the
`edge-log` regime.  The current task is therefore not another abstract
dominant-packet statement; it is to extract enough independent constraints
from the identities at shifted indices `k+s`.

## Exact shifted equations

For the Gamma profile already named in Lean as `po3_gamma_profile`, the
product avatar gives the exact shift factor

```text
A_{k+s}(x) = A_k(x) * Shift_k,s(x),

Shift_k,s(x) = prod_{j=k+1}^{k+s} (x - (N+j))^{-1}.
```

The wall at the shifted index `k+s` gives, after isolating a finite top packet
`P_k={x_{k,1},...,x_{k,L}}`,

```text
sum_{i=1}^L c_{k,i} A_k(x_{k,i}) Shift_k,s(x_{k,i})
  = shifted remainder + shifted mirror.
```

After normalizing by a packet scale, this becomes a finite linear system.  The
key point is that fixed shifts `s=0,1,...,L-2` are usually too weak in the
edge-log window: they see almost constant rows and the constraint matrix can
degenerate.

## Adaptive shifts

Let the edge-log top center be `xi_k`, and write

```text
lambda_k := Lambda_k(xi_k),
L_k      := |lambda_k| ~= log k.
```

For a future shift define

```text
mu_k(s; xi_k) := sum_{j=k+1}^{k+s} (xi_k - (N+j))^{-1}
              = - d/dx log Shift_k,s(x) |_{x=xi_k}.
```

Choose shifts `s_{k,p}` for `p=0,...,L-2` by

```text
s_{k,0}=0,
mu_k(s_{k,p}; xi_k) / lambda_k -> p       for p>=1.
```

This is the useful normalization: the shifted test rows now change at exactly
the local edge-log packet scale.

## Vandermonde limit

If local packet points satisfy

```text
x_{k,i} = xi_k + t_i / lambda_k + o(1/L_k)
```

with `t_i` in a compact separated class, then

```text
Shift_k,s_{k,p}(x_{k,i}) / Shift_k,s_{k,p}(xi_k)
  -> exp(-p t_i).
```

Thus the normalized constraint matrix tends to

```text
V_{p,i} = exp(-p t_i),       p=0,...,L-2.
```

This is a rectangular Vandermonde matrix with nodes `z_i=exp(-t_i)`.  If the
`t_i` are distinct and uniformly separated, then `rank V = L-1` and the
smallest nonzero singular value is uniformly bounded below on compact
separated families.

## Consequence

If the shifted remainder plus shifted mirror is `o(1)` after the same
normalization for `p=0,...,L-2`, then the normalized coefficient vector is
forced into the one-dimensional kernel of this Vandermonde block.  Equivalently
it is captured by the exponential finite-difference line

```text
w_i(t) = 1 / prod_{j != i} (exp(-t_i) - exp(-t_j)).
```

So the edge-log branch is no longer a vague packet statement.  It reduces to
one precise next theorem:

```text
PO3-square.2d3b5:
  prove normalized shifted-error control for the adaptive shifts s_{k,p}.
```

If that error control fails, the route obstruction is also precise: the actual
Gamma tower has a shifted tail/mirror contribution of the same size as the top
packet after adaptive testing, so the current signed-dominance route cannot be
closed by finite-packet capture alone.

## External sanity checks

The formulas used here are standard consequences of:

- the Gamma ratio/product recurrence already formalized as
  `po3_gamma_profile_succ` and `po3_gamma_profile_eq_prod`;
- the digamma recurrence/reflection and asymptotics used for the previous
  slope trichotomy;
- the Vandermonde determinant/rank fact for distinct nodes.

Useful references:

- DLMF Gamma asymptotics: https://dlmf.nist.gov/5.11
- DLMF polygamma identities: https://dlmf.nist.gov/5.15
- DLMF Vandermonde determinant section: https://dlmf.nist.gov/1.3
