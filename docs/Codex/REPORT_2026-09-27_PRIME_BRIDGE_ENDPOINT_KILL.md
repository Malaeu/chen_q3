# A prime-edge bridge is unbounded on independent edge fields

2026-09-27 · PAPER-only diagnostic · global signed Weil form, not the selected
Goal058 fixed-128 transport · `PX_RH_CLAIM: NOT_MADE`.

## Source and proposed certificate

Use the exact `f_0` of `paper_weil/sections/canonical.tex` and the signed
energy identity in `paper_weil/sections/groundstate.tex`. For a compact smooth
profile `s`, let `F_s` contain its increments at all positive edges: short
continuous lags `0<u<t_0` and prime-power atoms `u=log n`. Let `G_s` contain
its increments at negative continuous lags `t>t_0`. With the exact edge
weights, `||F_s||^2=P_s` and `||G_s||^2=N_s`.

A candidate geometric certificate chooses a nearest prime log `ell=log p`
on a region where `|t-ell|<t_0`, and writes the exact
increment as a prime edge plus or minus a short bridge. On a left-hand
prime band `B_p` (`t<ell`), for example,

```
s(x+t)-s(x) = [s(x+ell)-s(x)]
              - [s(x+ell)-s(x+t)].
```

Thus a proposed linear routing `T` on the *independent* positive-edge
Hilbert space would obey `(TF)(x,t)=F_p(x)-F_c(x+t,ell-t)` there. If such
`T` were a contraction, `N_s<=P_s` would follow for every profile. The
identity alone provides no norm estimate.

## Exact obstruction to this ambient-space route

**Proposition (PAPER).** Any nearest-prime routing with the direct coefficient
`1` on `F_p(x)` throughout a nonempty interval left of `ell=log p` is
unbounded from the independent positive-edge Hilbert space to the negative
edge Hilbert space. In particular it cannot be a contraction certificate.

**Proof.** Choose a prime `p` in the bridge region and a compact interval
`I` in its nearest-prime band with `t_0<inf I<sup I<ell`. Such an interval
exists since consecutive prime logs are distinct, so the Voronoi band of
`ell` extends a positive distance to its left. Set every positive-edge
component to zero except `F_p(x)`. The input and a part of the output norms
satisfy

```
||F||_+^2 = w_p ∫ f_0(x) f_0(x+ell) |F_p(x)|² dx,
||TF||_-^2 >= ∫_I |b(t)| ∫ f_0(x) f_0(x+t) |F_p(x)|² dx dt,
w_p = log(p)/sqrt(p)>0.
```

The exact theta series gives constants `0<c<C<infty` such that, for every
`z>=0`,

```
c exp(9z/2 - pi exp(2z)) <= f_0(z)
                            <= C exp(9z/2 - pi exp(2z)).
```

For the lower bound, keep the `n=1` term of
`Phi(z)=4 exp(z/2) sum_{n>=1} h(n exp z)` and use
`h(u)=pi u²(pi u²-3/2) exp(-pi u²)>0` for `u>=1`. For the upper bound,
use `h(nu)<=pi² n⁴u⁴ exp(-pi n²u²)` and sum
`sum_{n>=1}n⁴ exp[-pi(n²-1)]<infty` for `u>=1`; divide by the fixed
normalization `A`.

Put `d=ell-sup I>0`. Uniformly for `t in I` and `x` sufficiently large,

```
f_0(x+t)/f_0(x+ell)
 >= (c/C) exp[9(t-ell)/2]
             exp{pi exp(2x)[exp(2ell)-exp(2t)]}
 >= c_I exp(c'_I exp(2x)) -> infinity.
```

Here `c'_I=pi[exp(2ell)-exp(2 sup I)]>0`. The continuous `|b|` is
strictly positive on `I`. Choose `F_p` supported in `[X,X+1]` and normalize
its input norm to one. The displayed ratio makes `||TF||_-^2` tend to
infinity as `X->infinity`. Therefore `T` is not bounded. QED.

This uses one actual prime atom and the full endpoint weights. Prime-gap
asymptotics and a sum over all atoms are unnecessary for the obstruction.
The test field with `F_c=0`, `F_p!=0` is deliberately **not** a gradient
field `F_s`: gradient components are linked by the same profile `s`.
Therefore the proposition does not imply any sign for `P_s-N_s` and does
not refute a different, nonlocal factorization or a source-aware routing
that preserves gradient compatibility.

## Logical boundary and next exact test

On the gradient range alone, the formal map `F_s -> G_s` has squared
operator norm `sup_{s!=0} N_s/P_s`. Calling it a contraction merely
restates the unproved all-profile inequality; it is not a certificate.
The companion critical-ratio report proves this supremum is at least `1`
unconditionally, so any valid sharp route must allow saturation.

`REJECTED`: this nearest-prime direct bridge as a contraction on independent
edge fields. `INCOMPLETE`: the sharp sign `N_s<=P_s` on the gradient range,
and the separate selected Goal058 C128/floor obligations. A useful next
candidate must give an explicit source-derived operator or identity that
enforces the gradient relations **before** its norm is estimated, retaining
the prime jumps, endpoint weights, and mixed terms.

The calculation was independently checked in a read-only mathematical
subtask. No Lean run or RH claim.
