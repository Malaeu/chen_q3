# The exact prime-bridge mixed term has both signs

2026-09-27 · PAPER-only diagnostic · global signed Weil form ·
`PX_RH_CLAIM: NOT_MADE`.

## Exact coupled band

Use the source `f_0>0`, `b(t)` and `t_0` from
`paper_weil/sections/canonical.tex` and `groundstate.tex`. Fix a prime
`p`, put `ell=log p>t_0`, and choose a compact interval `I` of positive
length inside

```
(max(t_0, 2ell/3), ell).
```

It may also be chosen inside the left nearest-prime band of `ell`, because
that band contains a nonempty left neighborhood of `ell`. For
`s in C_c^infty(R;C)` set

```
A_s(x)   = s(x+ell)-s(x),
B_s(x,t) = s(x+ell)-s(x+t),
W(x,t)   = |b(t)| f_0(x) f_0(x+t)>0.
```

The actual long increment is `A_s-B_s`, so the exact negative-band
energy is

```
N_I(s) = ∫_I∫ W |A_s-B_s|² dxdt
       = ∫_I∫ W (|A_s|²+|B_s|²) dxdt - M_I(s),
M_I(s) = 2 Re ∫_I∫ W A_s conjugate(B_s) dxdt.
```

The `A` and `B` terms and their mixed pairing have the **same original
endpoint weight**. No prime atom has been converted to a density, and
`M_I` is not assumed favorable.

## A source-valid sign test

**Proposition (PAPER).** On this same interval `I`, there are compact
smooth complex profiles `s_+` and `s_-` with `M_I(s_+)>0` and
`M_I(s_-)<0`. Thus the mixed term has no universal sign even on the
gradient-compatible test class.

**Proof.** First use the bounded plane wave `s(x)=exp(i xi x)` as a
limit of compact tests. Write `h=ell-t>0`, `L=xi ell`, `H=xi h`.
The common phase `exp(i xi x)` cancels, and direct multiplication gives

```
Re(A_s conjugate(B_s))
  = Re[(exp(iL)-1)(exp(-iL)-exp(-i xi t))]
  = 1-cos(H)-cos(L)+cos(L-H).
```

For `xi_+=pi/(2ell)`, `L=pi/2` and this equals
`1-cos(H)+sin(H)>0`. For `xi_-=3pi/(2ell)`, `L=3pi/2` and it equals
`1-cos(H)-sin(H)<0`, because `0<h<ell/3` gives
`0<H=3pi h/(2ell)<pi/2` and `cos(H)+sin(H)>1` there.
The weight has strictly positive total mass on `R×I`, so the two
integrated mixed terms have these strict opposite signs.

To return to the authorized test class, choose a real smooth compact
cutoff `chi` with `0<=chi<=1` and `chi=1` near zero, and put
`s_{xi,R}(x)=chi(x/R) exp(i xi x)`. Each is in
`C_c^infty(R;C)`. For fixed `x,t`, its two increments converge to the
plane-wave increments. Their product is bounded uniformly in `R` by
`4`, while `∫_I |b(t)| C_0(t)dt<infty`, where
`C_0(t)=∫f_0(x)f_0(x+t)dx`. Dominated convergence therefore gives
`M_I(s_{xi,R}) -> M_I(exp(i xi ·))`. Choose one sufficiently large
finite `R` for each frequency. QED.

This is an exact all-source sign test, not a numerical zero check. It
uses only the positivity and integrability already proved for `f_0`.

## Consequence and boundary

When `M_I<0`, dropping the mixed term **underestimates** the long-edge
cost; when `M_I>0`, it overestimates it. Thus `M_I>=0` is false, and
replacing `M_I` by `|M_I|` in `N_I=S_I-M_I` is not a valid upper bound.
The always-valid bound `N_I<=S_I+2∫_I∫W|A_s conjugate(B_s)|` would need
its own positive-energy budget; the sign test does not exclude it. The result
does **not** determine the sign of the complete `P_s-N_s`: the rest of
the negative continuum, short positive continuum, and all prime-power
atoms have not been compared.

The 2026-09-05 coupled-square verdict already rejects equal-path
capacity and a positive local second-difference extraction with a
nonnegative remainder. The present test is narrower: it checks the
specific nearest-prime bridge's mixed pairing on actual profiles.
The next comparison can keep the entire signed sum or pay an explicit
upper bound for its cross terms; either way it must retain the actual
arithmetic atoms and endpoint weights. The existing source-exact
Chebyshev-discrepancy representation is another route. A favorable sign
for one band cannot be supplied as an input.

No Lean run, selected Goal058 floor, or RH claim follows.
