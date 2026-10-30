# Direct physical m16 X: interval audit

Status: ACCEPTED BOUNDED PAPER + ARB, one m16 eigenvector only. Independent
direct-source |X|/B<0.000336<1/4 is established under the inherited certified
eigenpair/B and trusted Arb enclosure semantics. No cofinal, NOESCAPE or RH
conclusion follows. The sign of X remains unresolved.
The independent physical route is

    X=k(h_out,v)-k(W,v)+lambda <W,v>,
    W(x)=sum_{ell!=0} h(x+ell L), x in I=[-b,b],
    L=log16, b=L/2.

The certified retained second even eigenpair and denominator B are inherited
from M16_ARB_SOURCE_MAP and noescape_m16_eigenpair.json. The new script
noescape_m16_direct_x_arb.py checks the input hash against the earlier physical
denominator file and interval-normalizes the same real Fourier coordinates.
It never solves the F+X+lambda<h,v>=0 identity for X.

## Exact finite expressions and interval integration

Let h1 retain only theta index n=1, and W1(x)=h1(L-x)+h1(L+x).
All arguments of h1 below are at least b on the real integration paths.
Write J(a,z;k)=integral_a^z h1(y) exp(ky)dy. The incomplete-gamma formula
in M16_DIRECT_X_CERTIFICATE_GAP evaluates this exactly with Arb; an infinite
upper limit is the upper-gamma primitive at the lower limit.

With omega_r=2pi r/L and the full Fourier coefficients c_r, the correlations are

    qW(s)=2/sqrt(L) sum_r c_r exp(i omega_r(s+b))
          [J(b+s,3b;-i omega_r)+J(b,3b-s;i omega_r)], 0<=s<=L,
    qH(s)=2/sqrt(L) sum_r c_r exp(i omega_r(b-s))
          J(max(b,s-b),s+b;i omega_r), s>=0.

These follow by substitutions in the actual window overlaps. In particular
qW(0)=2<W1,v>, qW(L)=0; the n=16 prime power is retained and contributes zero
only to qW, not qH. qH is integrated with separate analytic formulas below
and above L. Odd pole pairings vanish by actual evenness.

The archimedean integrals use delta=1e-24 and S=L+0.4. On bounded subintervals
Arb integrates j(s)(qW(0)-qW(s)) and j(s)qH(s). Returned radii, rather than
requested tolerances, enter the final enclosure. The complex callback only
accepts balls with |Im s|<0.12 and -0.01<Re s<S+0.01. The gamma arguments
pi exp(2y) stay in the right half-plane there; no principal-branch cut is
crossed. The meromorphic j factor returns nonfinite at its poles.

All pole integrals are exact J combinations, including the infinite h1 tails:

    <h1_out,p>=sqrt2 [J(b,infinity;1/2)+J(b,infinity;-1/2)],
    <W1,p>=sqrt2 [exp(L/2)J(b,3b;-1/2)+exp(-L/2)J(b,3b;1/2)],
    <p,v>=sum_r c_r sqrt2 sinh(b/2)/[sqrt(L)(1/4+omega_r²)].

Prime powers through 64 are evaluated explicitly for qH and through 16 for
qW. The infinite remaining qH prime tail is bounded below. The script retains
the diagonal -c*<W1,v>, arch tail qW(0) integral_L^infinity j and correction
lambda<W1,v> with their signs.

## Bounds near zero and beyond the arch/prime cutoffs

Unit normalization and Cauchy-Schwarz give

    ||v||infinity <=sqrt(33/L)<4,
    ||v'||infinity <=sqrt(4pi²*2992/L³)<80, ||v||1<=sqrt(L)<2.

h1 decreases for y>=b: its derivative divided by h1 is negative there,
as is also immediate from its explicit polynomial times exp(-pi exp(2y)).
Thus ||W1||infinity<=2h1(b)<3e-17. Differentiating the finite overlap yields
|qW'|<=2||W1||infinity(4+80L)<2e-14. Also |qH(s)|<=8s h1(b) near zero.
Since s j(s)<1 for 0<s<=delta, the omitted W integral is <2e-38 and the
omitted H integral is <1e-39. Their sum is paid by 2.1e-38.

For s>=S, |qH(s)|<=2sqrt(L)*1000 exp(4.5(s-b)-pi exp(2(s-b))).
The exponential envelope is decreasing, so its integral against j is at most

    2sqrt(L)*1000 exp(4.5(S-b)-pi exp(2(S-b))) J_S,
    J_S=atanh(exp(-S/2))+atan(exp(-S/2)).

For n>=65, bound Lambda(n)<=log n and use the same envelope. The positive
majorant is 2sqrt(L)*1000*16^(-9/4) log(n)n^4 exp(-pi n²/16).
Its ratio from n to n+1 is at most

    ((66/65)^5) exp(-(pi/16)*131)=:q<1,

because log(n+1)/log n<=(n+1)/n and both ratio factors decrease. The geometric
tail first/(1-q), computed outward by Arb, pays all omitted prime powers.

## Full theta and periodization replacement, not a first-term diagnostic

For y>=b let R(y)=h(y)-h1(y). A geometric theta estimate gives

    |R(y)|<=F(y)=10000 exp(4.5y-4pi exp(2y)),
    Btail=F(b)<1e-77,
    F(y)<=Btail exp(-397(y-b)).

For completeness, bound a theta summand by
(16pi²+24pi)n^4 exp(4.5y-pi n² exp(2y)). After extracting exp(-4pi exp(2y)),
the n=2 term contributes 16. For n>=3 use n²-4>=n and n^4<=16^n; the remaining
geometric sum with ratio 16 exp(-16pi) is <1. The coefficient is <4000<10000.
The exponential slope is at most 4.5-128pi<-397. No RH premise is used.

For deltaH=R(|x|) outside I, the overlap formula gives |Q(s)|<=8s Btail for
0<s<=L and <=8L Btail exp(-397(s-L)) for s>=L. Using integral s j(s)<5
and J_L<1 pays the arch term by 64Btail. The primes n<=16 cost <1100Btail.
For n>=17, comparison with the decreasing integral gives

    sum log(n)/sqrt(n)*(16/n)^397
    <=4[L/396.5+1/396.5²]<1,

so their cost is <24Btail. The diagonal is zero by disjoint supports.
The weighted tail integral integral_b^infinity exp(y/2)F(y)dy is at most
2Btail/396.5<Btail/100; both pole products together are <24 times this
integral (in fact the odd one is zero). Thus |k(deltaH,v)|<1200Btail.

For deltaW=W-W1, the two nearest images contribute R(L-x)+R(L+x).
Remote images have arguments >=3b. The full theta envelope
10000 exp(4.5y-pi exp(2y)) and a successive-image ratio <1/2 show that their
total is <40000 exp(13.5b-pi exp(6b))<1e-4000<Btail.
Therefore ||deltaW||infinity<3Btail and ||deltaW||1<9Btail.

For 0<s<L, evenness and the boundary-strip split give

    |2<deltaW,v>-Q_deltaW,v(s)|
       <=2s(80||deltaW||1+4||deltaW||infinity).

The arch term is consequently <810||deltaW||1+40||deltaW||infinity;
the supported primes cost <360||deltaW||1. On I, p<=5sqrt2/4<2 and
|q|<=3sqrt2/4<2, so both pole products together cost <16||deltaW||1.
The diagonal costs <32||deltaW||1 because c*<8. The script checks |lambda|<1,
so the correction costs <4||deltaW||1. Summing these and the deltaH budget
gives <15000Btail<1e-72, well below the reserved replacement budget 1e-60.

Root outward-Arb checks at60dps gave V0<3.45, V1<74.45, 2h1(b)<2.321e-17,
Btail<2.451e-81, and the remote-image envelope <1.756e-5576.
Independent escaping_radical_trials review derived the same complete-tail
mechanism; root corrected/relaxed intermediate constants as explicitly above.

## Verification boundary

Independent direct_x_interval_review checked the gamma formulas, signs,
analytic domain, near-zero budgets, pole factors, n=16 treatment and input
scope. The terminal output and complete replacement proof passed its final
bounded review (proof-before-verdict SHA256
b4214eee7ccbf4364c093727cbff249a35c0a040174dc2985c242b1b42a6997b). The exploratory /tmp run with an asynchronous signal inside
an Arb callback was discarded: a callback exception was swallowed and its
finite-looking output is not evidence. The durable script has no signal
handler and must complete cleanly. No omitted-tail budget may be inferred
from the difference of two quadrature orders.

## Completed outcome

The durable run completed cleanly: 42 Arb integration pieces in224.004s.
All input, denominator and script hashes in its JSON matched during review.
The serialized conservative bound is |X|<1.42e-36 with
B>4.22699e-33, hence |X|/B<0.000336. The unsymmetrized internal interval
was approximately [-6.09661e-37,1.41079e-36]; zero remains inside.
Near-zero budget2.1e-38, far arch budget<1.102e-42, prime tail<2.540e-352,
and full replacement budget1e-60 are all included, in addition to returned
quadrature radii and interval input propagation.

A separate root Arb check combines the earlier independently reviewed F96
and analytic Fourier tail with this independently evaluated X. The interval
F+X+lambda<h,v> contains zero (conservative radius2.25e-36). This is a
consistency check of the known identity, not a proof from a numerical zero.
The earlier identity-derived |X|/B<0.0002 is sharper but logically separate.
The missing independent direct-X part of the finite m16 discriminator is
now paid; this does not establish anything on an unbounded sequence.
