# Long-lag comparison is critical, not uniformly strict

2026-09-27 · PAPER-only note · global signed Weil form, not selected Goal058
matrix closure · `PX_RH_CLAIM: NOT_MADE`.

## Exact target

For every `s ∈ C_c^∞(R; C)`, use `paper_weil/sections/groundstate.tex`,
Theorem `GS` and Lemma `plastic`. Put `t0=log(plastic number)` and

```
E_s(t) = ∫_R f0(x) f0(x+t) |s(x+t)-s(x)|² dx,
P_s    = ∫_0^t0 b(t) E_s(t) dt
         + Σ_{n≥2} [Λ(n)/√n] E_s(log n),
N_s    = ∫_t0^∞ |b(t)| E_s(t) dt.
```

All three quantities are finite for compact smooth `s`: `E_s(t)=O(t²)`
at zero and `E_s(t)≤4||s||∞² C0(t)`, `C0(t)≤Ce^{-t}` at infinity
(`groundstate.tex`, proof of Theorem `GS`). The identity is
`Q(f0 s)=P_s-N_s`. The required all-profile sign is exactly
`N_s≤P_s` for every such `s`; by Corollary `DOM` of that paper it is
equivalent to RH. No sign is established in this note.

`P_s>0` for each nonzero compact smooth `s`: if its short-lag integral
vanished, positivity of `b(t)` for `0<t<t0` and of `f0` would give
`s(x+t)=s(x)` on all short pairs by continuity, making `s` constant,
then zero by compact support. Consequently the ratio `N_s/P_s` is
well-defined for nonzero tests.

## Exact obstruction to a fixed percentage surplus

**Proposition (PAPER).** There is no `ε>0` such that
`N_s≤(1-ε)P_s` for all compact smooth complex profiles `s`.

**Proof.** The prime-power atom at `n=2` has
`w2=Λ(2)/√2=log(2)/√2>0`, so `P_s≥w2 E_s(log 2)`. The proposed
inequality would give

```
Q(f0 s)=P_s-N_s ≥ ε P_s ≥ ε w2 E_s(log 2)
        = ∫_R W(x)|s(x+log 2)-s(x)|² dx,
W(x)=ε w2 f0(x)f0(x+log 2)>0.
```

This is a nonzero nonnegative two-point finite-stencil minorant on the
full compact profile class. It contradicts `paper_weil/sections/
obstruction.tex`, Corollary `nominorantWeil` (from Theorem
`nominorant`). Therefore no such `ε` exists. This implication uses
only the already stated theorem and the positive `n=2` atom; it does
not require comparing any scalar masses or assuming the target sign.

There is also a geometric check using the same paper's radical. For
`q≠0`, let `r_q(x)=f0(x-q)/f0(x)` and
`s_{q,R}(x)=χ_R(x)r_q(x)`. Lemma `budget` in `obstruction.tex` proves
`Q(f0 s_{q,R})→0`. The ratio `r_q` is not constant: a constant ratio
would make the strictly positive integrable `f0` periodic up to a
constant multiplier; integration makes that multiplier one, then
positive periodicity contradicts integrability. Hence some compact
rectangle `(x,t)∈I×J`, `J⊂(0,t0)`, has
`f0(x)f0(x+t)b(t)|r_q(x+t)-r_q(x)|²>0`. Once `R` covers the two
endpoints, this rectangle gives `P_{s_{q,R}}≥η_q>0` independently of
`R`. Thus `N_{s_{q,R}}/P_{s_{q,R}}→1`. This argument does **not**
insert the noncompact `r_q` in the form or assume `P_{r_q}` finite.

Define `ρ*=sup_{s≠0} N_s/P_s` on the stated test class. The
proposition proves `ρ*≥1` unconditionally. If the full sign holds,
then `ρ*=1`; if the full sign fails, `ρ*>1`. This is a criticality
statement, not a proof of which case occurs. Pointwise strict
`N_s<P_s` with an `s`-dependent margin remains possible.

## What the obvious short-path argument actually gives

For `t>t0`, choose an integer `m≥2` and `h=t/m<t0`. The exact
telescoping identity is

```
s(x+t)-s(x)
  = Σ_{j=0}^{m-1} [s(x+(j+1)h)-s(x+jh)].
```

Minkowski in the **same endpoint-weighted** `L²(dx)` gives

```
E_s(t)^(1/2) ≤ Σ_{j=0}^{m-1} I_j(t,h;s)^(1/2),
I_j = ∫_R f0(y-jh) f0(y+(m-j)h)
            |s(y+h)-s(y)|² dy,
```

and Cauchy gives `E_s(t)≤m Σ_j I_j`. There is no omitted boundary
term in this finite identity; the cross-term information is lost at
Minkowski/Cauchy. The short positive energy `E_s(h)` has instead
the weight `f0(y)f0(y+h)`. Their pointwise ratio is

```
R_j(y;t,h) = f0(y-jh)f0(y+(m-j)h)
             / [f0(y)f0(y+h)].
```

For `j=m-1` this is `f0(y-(m-1)h)/f0(y)`, whose supremum over
`y` is infinite for the actual `f0`. Indeed, if for some `d>0`
`f0(y-d)/f0(y)≤C` eventually, iteration along `y=y0+nd`
would imply `f0(y0+nd)≥C^{-n}f0(y0)>0`, contradicting the
super-exponential upper envelope of `f0` in
`paper_weil/sections/canonical.tex`, Theorem `FPhi`.

Thus this naive **pointwise** transfer of each long edge to a fixed
short path has no finite uniform weight constant. It does not exclude
an integrated, source-aware routing that shares short edges and prime
atoms, or a nonlocal factorization. Even such a routing must reach the
sharp constant `1`, not `1-ε` globally. A finite selected matrix may
have a positive cellwise floor that shrinks with the cell; the global
proposition does not decide that separate Goal058 obligation.

## Verdict and stopping point

`REJECTED`: a global fixed-percentage domination of negative energy by
the full positive energy, and a pointwise fixed-short-path argument
based on a uniform ratio of the actual `f0` endpoint weights.

`INCOMPLETE`: the sharp all-profile inequality `N_s≤P_s`, any
source-aware integrated routing with constant `1`, and selected-cofinal
Goal058 ground tracking. The first unpaid input for the proposed
geometry is a joint long-to-short/prime transport that retains the
full `f0(x)f0(x+t)` weight and all cross terms while allowing the
translated radical to saturate the bound.

The global strict-margin proof and its scope were independently checked
by a read-only explorer; the telescoping calculation was independently
derived by a read-only researcher. A separate read-only reviewer found
no material defect in these deductions from the cited PAPER statements;
that is not an independent audit of the entire paper or Goal058. No
Lean run or new RH claim.
