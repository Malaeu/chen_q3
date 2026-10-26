# Post-Q39: finite many-prime incidence variance return

2026-10-26. Own bounded attempt, independent read-only qualified PAPER check PASS. Original sparse P,
N=m,L=log m,M=R=floor(m^epsilon). No new exponent; no Q40 sent.
Source: Q39 §§2 and 7, D_n=1_(n>R)B_n and ||D_n||<=b/sqrt(n),
b=40+16Omega. Every D_n is the full Hermitian source matrix, including all
k, both times, complex mode cross terms and original hyperbolic edges.

## Distinction from earlier attempts

CCM_Q02_DIRECT_ABEL_TEST is the close Abel predecessor: it treated the
continuous C part of B=C+E and the full weighted sawtooth identity, leaving
discrete E variation unpaid. It did not establish full B differentiation.
Do not repeat that conditional Abel-Mertens route as a new supplier.
Q05_LOG_CORRELATION_PREFLIGHT rejects automatic qualitative shifted-correlation
transfer. Here the tested certificate is an elementary finite variance of
many prime divisibility indicators, with its full signed incidence residual.
No external Turan/Kubilius or Katai theorem is assumed.

## Exact source extraction

Let S be all primes <=Y, 2<=Y<=m, K=|S|, H=sum_(p in S)1/p,
omega(n)=sum_(p in S)1_(p|n). Extend D_n by zero outside R<n<=m.

 J=sum_k mu(k) sum_(p in S,p not dividing k) D_(pk),
 Eomega=sum_n mu(n)(omega(n)-H)D_n,
 H T=-J-Eomega.

This is the Q39 identity with a finite set, not a new arithmetic gain.
All intersections and p-power exceptions stay in the coprimality mask.
The residual is not zero and must not be discarded.

## Fully paid finite variance bound

For real x>=1, expand V(x)=sum_(n<=x)(omega(n)-H)^2 using floors.
The main term is x[H-sum_p 1/p²]. Each of the K² ordered indicator pairs
has floor error at most one. The negative linear term contributes at most
2HK; the constant term H² floor(x) contributes no positive error.
Thus V(x)<=xH+K²+2HK<=xH+3K², since H<=K.

Weighted partial summation, retaining the lower boundary before dropping
its NONPOSITIVE contribution, gives

 sum_(R<n<=m)(omega(n)-H)^2/sqrt(n)
 =V(m)/sqrt(m)-V(R)/sqrt(R)+(1/2)integral_R^m V(t)t^(-3/2)dt
 <=2H sqrt(m)+3K²/sqrt(R).

For every unit complex c=Pc, beta(n)=c*D_n c, |beta(n)|<=b/sqrt(n).
Cauchy with weight n^(-1/2), |mu|<=1, and sum_(n<=m)n^(-1/2)<=2sqrt(m)
yields uniformly on original P

 ||Eomega||/H <= 2b sqrt(m/H)+sqrt(6)b K (m/R)^(1/4)/H =: r_var.

This bound contains the entire incidence residual, not just its scalar mean.
The use of absolute values loses its joint sign with J at this precise step.

## Remaining channel and full consumer budget

Put j=sum_(p in S)p^(-1/2), N=floor(m/2), H_N=sum_(k<=N)1/k.
Keeping all p,q products inside the channel square, then using triangle only
as an explicit fallback, gives

 E=sum_k mu(k)^2 |sum_(p in S,p not dividing k) beta(pk)|² <=b² j² H_N,
 |J[c]|/H <= b*j*sqrt(N H_N)/H =: r_J.

Therefore T<=(r_J+r_var)P and, with the standalone Q39 short bound,
 P K_m P >= -(r_J+r_var+2b sqrt(R)+50L+8)P.
No intermediate compressed-operator product, omitted prime power, or extra
Q32 near-return fee is introduced. Preserve the stronger inherited fallback
s_keep<=6sqrt(m)+6m^(1/4) for A rather than replacing it with this trial.

Even granting J zero at no cost, THIS explicit residual upper-budget formula
has first term 2b sqrt(m/H). Since H<=sum_(n<=m)1/n<=1+L, its numerical
allowance is >=2b sqrt(m/(1+L)). Hence optimizing Y in this bound cannot
produce eta(epsilon)->0. This is a lower bound on the displayed allowance,
NOT a lower bound on Eomega, J+Eomega, T or a CCM eigenvalue.
The variance estimate may be loose; signed joint cancellation remains open.

## Evidence and stopping point

Root exact Fraction arithmetic checked V(x)<=xH+3K² for all integer
1<=x<=1024, Y in {2,3,5,11,31,65}:6144 checks PASS. These are finite
controls of the elementary algebra, not source evaluations or a proof of RH.
The proof is the floor expansion and weighted summation above.

One own no-gain certificate tested after Q39. Do not manufacture three
attempts from Q02/Q05 duplicates. Roll back before separately bounding
Eomega and J. A next supplier must control their signed joint value or give
a source-specific residual estimate, not just unweighted divisibility variance.

Reproducible finite control (standard Python, no package installation):
```python
from fractions import Fraction as F
from math import isqrt
ps = [n for n in range(2,66) if all(n%d for d in range(2,isqrt(n)+1))]
for Y in (2,3,5,11,31,65):
    S = [p for p in ps if p<=Y]
    H = sum((F(1,p) for p in S), F()); V = F()
    for x in range(1,1025):
        V += (sum(x%p==0 for p in S)-H)**2
        assert V <= x*H+3*len(S)**2
```

Independent q39_joint_supplier checked the floor variance, weighted Abel
boundaries, both Cauchy constants and the full short/arch return. Its bounded
shelf search found no prior many-prime variance trial in inspected CCM notes;
this is not a global absence claim. A=T+T_short; C0=A+Hd, so Hd is not
an extra charge in the direct K floor. Mathematical target remains OPEN.
