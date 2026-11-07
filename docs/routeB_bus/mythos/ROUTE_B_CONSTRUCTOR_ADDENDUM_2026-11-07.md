# Route B — constructor shelf, addendum 2026-11-07

Two-scale divisor kernel, Proshka rounds L/M/N/O. Branch `proshka_inbox_2026-10-31`, repo github.com/Malaeu/chen_q3.
Base document (unchanged): `docs/routeB_bus/mythos/ROUTE_B_CONSTRUCTOR_PROVEN_2026-11-06.md` on rh_clean.
Status: Route B CHALLENGER / NOT_RH. Nothing here claims RH.

| Round | Commit | Blob | Result |
|---|---|---|---|
| L (plan) | c3f80b9871ca022d307b27331a2753dbc386e97a | 7e8920ceac98f25b2da19a968c026baf37c76b7f | plan only, no tests |
| M freeze | 7c82bc24e15a0620be9ff7c9ad715cadb45e0644 | 8725658c527cde25b4465ecc0cd9eca84a50f532 | frozen predictions |
| M | 45afff3806bd7671919f5330830b246b1229c75c | 27168a1a764b5254b53d87e5772673017b7f5d37 | NO_DERIVATION; KILL of entrywise payment |
| N freeze | 5393c758e76d78a1668d3a0b787aede3cf66f0d9 | 256a47d2d08064771712c62718e98072b41e3395 | frozen predictions |
| N | 3e04a47b3b3470104a6775c98dd05ad7718f13a3 | 8a7c61590fe2de2736d560af05b104860bde2389 | PROOF_PROGRESS; KILL of source-blind compression |
| O | 9104b014155bdd0dca507facb810da7a4bc1726a | f08bcf4f2302b7122a788c524472412ceaf382bb | equivalence with 3/4; exact d<->2d fold |

## Receiver A11 (O, PAPER)

For all eta>0: C_long(X) << X^{1/2+eta} on all late dyadic X  <=>  zeta(s) != 0 for Re s > 3/4 (quasi-RH).
Beyond 3/4 a repeatable exponent-lowering step is required; one fixed step may not be iterated.

## Paid (PAPER)

- Main term x^2/(4de) cancels exactly at coefficient 1/8 (M).
- |M_X(d,e)| <= (5X/12)(d/e+e/d) + 5X/16 (M).
- Block d,e <= sqrt X: <= 2X^2(1+log U)^3 (M).
- Boundary with lcm(d,e) <= X: <= (3/4)X^2(1+log X)^4 (M).
- Periodic main term: (3/2)X^2(1+log 4X)^2 (M).
- Tail d,e > 2X: equals -(1/8) int_{2X}^{4X} (sum_{2X<d<=x} a_d)^2 dx <= 0, useful sign (M).
- All high additive frequencies of the common source: energy O(log X); nonzero low modes of short divisors: polylog (N).
- Exact fold d<->2d (O14): all powers of two contribute exactly log 2 (O).

## Killed

- Entrywise positive payment after scale subtraction: for X<d,e<=4X/3, M=(2X+3min-2max)/8 >= 7X/24 and sum (a_d a_e M)_+ >= (7/27648) X^3 log^2 X on the actual mu (M).
- Source-blind low-mode contraction from PNT plus diagonal size: witness u(n)=n^{beta-1}, beta=3/4, flux ~X^{1/4} (N). Use as a standard judge for future attempts.

## Address of the wall (Mythos check, exact identity verified at X=48, 96, 192)

Block X<d,e<=4X/3:

    sum a_d a_e M = (1/8)[2X*T^2 + T*W - 5*sum_y S(y)(T-S(y))],
    S(y) = sum_{X<d<=y} -mu(d) log d,  T = S(4X/3),  W = sum a_d * d.

The tail is also a square of the same kind of sum. The open remainder is a contest between Mertens-type squares on different intervals.
Open line (O20): c_{4X} J_{4X}(X) + B_>(X) <= K_eta X^{5/2+eta}.

## Rule E+I

Against the 3/4 wall an argument must use, in the same place, the Euler product (E) and the integer lattice floor(x/d) (I).

- E alone is refuted by DMV (Diamond-Montgomery-Vorhauer Beurling primes: Euler product present, zeros approach Re s = 1). Source: PROSHKA_VERDICT_FAKE_WORLD_EFZ_DH_BEURLING_2026-11-02, blob a3912756efbfac0825d96f29f35c0e834d38f560, table line "Chebyshev via binomial/Legendre = E + I, not E of abstract Beurling primes".
- Functional equation / lattice without Euler product is refuted by Davenport-Heilbronn.
- Source-blind arguments are refuted by n^{beta-1} (N).
- O14 is E+I: mu(2d) = -mu(d) is E; "exactly one power of two in (y/2, y]" is I. [hypothesis] It is free only because the window (x/2, x] is dyadic; p=3 would need (y/3, y].
- Not killed: growing S (the case {inf,2,3} was never computed), blocks of growing width, signed inter-block estimates.

## K6 (registered before each round, scored after)

- L/M: L1 0.70 HIT; L2 0.45 MISS; L3 0.10 correct.
- N: N1 0.55 MISS; N2 0.30 HIT; N3 0.25 MISS; N4 0.03 correct.
- O: T1 0.75 HIT (landing on quasi-RH predicted before sending); T2 0.30 MISS; T3 0.20 partial; T4 0.02 correct.

## Appendix: reproducible check of the slab identity

```python
from fractions import Fraction as F
import math
def mu(n):
    r,p=1,2
    while p*p<=n:
        if n%p==0:
            n//=p
            if n%p==0: return 0
            r=-r
        p+=1
    return -r if n>1 else r
def N(d,x): return x//d - x//(2*d)
def M(d,e,X):
    I1=sum(N(d,k)*N(e,k) for k in range(X,2*X))
    I2=sum(N(d,k)*N(e,k) for k in range(2*X,4*X))
    return F(I1)-F(I2,8)
for X in (48,96,192):
    D=list(range(X+1,4*X//3+1))
    ok=all(M(d,e,X)==F(2*X+3*min(d,e)-2*max(d,e),8) for d in D[::7] for e in D[::5])
    a={d:-mu(d)*math.log(d) for d in D}
    direct=sum(a[d]*a[e]*float(M(d,e,X)) for d in D for e in D)
    T=sum(a.values()); W=sum(a[d]*d for d in D)
    S=0; s=0
    for y in range(X+1,4*X//3):
        S+=a[y]; s+=2*S*(T-S)
    pred=(2*X*T*T + W*T - 2.5*s)/8
    print(X, ok, round(direct,3), round(pred,3))
# output: 48 True 1192.497 1192.497 / 96 True 14378.258 14378.258 / 192 True 43382.782 43382.782
```
