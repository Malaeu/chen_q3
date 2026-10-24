# Post-Q14: finite Vaughan split and the complete original-P budget

2026-10-24. Own bounded calculation; independent q15_vaughan_audit PAPER PASS.
Original N=m, L=log m, M=R=floor(m^epsilon), fixed 0<epsilon<1/32.
A(n)=P Q_M(log n)P, all matrix entries retained, ||A(n)||<=2, A(m)=0.
No source spectrum computed; no new arithmetic exponent or RH claim.

## Mechanism tested: short convolutions plus one joint Type-II source

For integer U,V>=1 write mu_U(n)=mu(n)1_(n<=U),
Lambda_V(n)=Lambda(n)1_(n<=V), with * denoting Dirichlet convolution.
The EXACT finite coefficient identity is

 Lambda = mu_U * log + Lambda_V - mu_U * 1 * Lambda_V
          + mu_>U * 1 * Lambda_>V.                         (1)

Indeed log=1*Lambda and mu*1=delta_1. Split mu and then Lambda;
mu_>U*1*Lambda_V=Lambda_V-mu_U*1*Lambda_V. No asymptotic term.
Here mu_U notation is a restriction, not Dirichlet convolution with an indicator.
Set b_V(v)=sum_(k|v,k>V) Lambda(k), so 0<=b_V(v)<=log v.
This includes every proper prime power and composite v, not just primes.
For the actual full S=sum_(n<=m)Lambda(n)A(n)/sqrt(n), (1) gives

 S=I+J-K+II,
 I=sum_(d<=U)mu(d)sum_(dk<=m) log(k) A(dk)/sqrt(dk),
 J=sum_(k<=min(V,m))Lambda(k) A(k)/sqrt(k),
 K=sum_(d<=U,k<=V,dkj<=m)mu(d)Lambda(k) A(dkj)/sqrt(dkj),
 II=sum_(d>U,v>V,dv<=m)mu(d)b_V(v) A(dv)/sqrt(dv).   (2)

All cutoffs are literal. No rectangular replacement of dv<=m, no missing
upper strip, no local renormalization of P. (2) is an operator identity, so
all mixed Fourier coordinates and both time directions remain together.
There are no products between I,J,K,II in this LINEAR operator identity.
Squaring it would create mixed sector products, which we do not discard or
use here. For W=PWP>=0 every trace in (2) uses the SAME W.

The SAME II also equals sum_(a>U,b>V,ab<=m) nu_U(a)Lambda(b)
A(ab)/sqrt(ab), where nu_U(a)=sum_(d|a,d>U)mu(d). This is regrouping
the same three factors, not two independent energies. For a>U,
nu_U(a)=-sum_(d|a,d<=U)mu(d). These exact coefficient relations are
possible inputs to a joint argument, not supplied cancellation estimates.

## Cheap log-free full-k input and all three short prices

Let C_a=sum_(j<=m/a) A(aj)/sqrt(aj), integer 1<=a<=m.
The original b constraint makes the zero extension of every synthesized
vector in ran P an H1 function with ||f'||<=Omega||f||,
Omega=2pi M/L. Translation differentiation gives ||A'(s)||<=2Omega
on this fixed projected space. Thus H(x)=A(x)/sqrt(x) has
||H'(x)||<=(1+2Omega)x^(-3/2).

The original exponential contacts give exactly
int_1^m H(x)dx=-P H_decay P, ||H_decay||<=4.
Consequently ||a^-1 int_a^m H(x)dx||<=4/sqrt(a): subtract the entire
lower interval, bounded by 4(sqrt(a)-1), before dividing by a.
For g(t)=H(at), sum-versus-integral on [1,m/a] costs at most
||g(1)||+int_1^(m/a)||g'(t)||dt <=(4+4Omega)/sqrt(a).
The noninteger terminal interval is included; g(m/a)=0. Therefore safely

 ||C_a|| <= c_m/sqrt(a), c_m=12+4Omega.              (3)

For a>m define C_a=0. This is a new log-free bridge calculation, not an
arithmetic cancellation theorem. Its continuous identity is inherited from
CCM_CONTINUOUS_RANK_TWO_TEST.md, valid on the same sparse synthesis.

Using Q01's already checked full-log bound b_m=40+16Omega and
W(x)=sum_(k<=x)Lambda(k)/sqrt(k)<=6sqrt(x), we get

 ||I||<=2b_m sqrt(U), ||J||<=12sqrt(V),
 ||K||<=12c_m sqrt(UV).                             (4)

The last bound keeps ALL d,k,j and cutoff endpoints, applying (3) before
norms in d,k. Coefficients mu(d)Lambda(k) have not been declared positive.
Thus S <= II + B_short P with
B_short=2b_m sqrt(U)+12sqrt(V)+12c_m sqrt(UV).
For U=V=R this has power 2epsilon up to logarithms. No intermediate
projector has been inserted in a translation product.

## The remaining joint source and its honest full return

The concrete intended saving is cancellation of actual mu(d) against the
whole b_V(v) weighted matrix A(dv), BEFORE absolute values. The available
bound b_V(v)<=log v gives only

 ||II||<=4sqrt(m)L(1+L),                             (5)

since sum_(v<=m/d)1/sqrt(v)<=2sqrt(m/d) and sum_(d<=m)1/d<=1+L.
Restrictions d>U,v>V can be retained but do not improve this exponent for
U=V=m^epsilon. This is the first step that loses the intended cancellation.
No phase mixing is supplied by (dv)^it=d^it v^it; original cutoff/weight
coupling is still present and has NOT been proved incapable of cancellation.

Full original K_m restricted to P has lower floor

 -[4sqrt(m)L(1+L)+B_short+50L+8] P.                 (6)

Direct S-to-K pays arch once, no additional short-divisor charge. If the
result is instead reported for T_>R=S-T_<=R, add exactly once
(56+32Omega)sqrt(R)+12(1+log R)^2. This has power3epsilon/2.
Thus the displayed complete bound has exponent1/2, not eta->0, and does
not beat the inherited CONDITIONAL3/8. The old direct12sqrt(m) is stronger.
These are prices of available upper bounds, not lower bounds for II or CCM.

A genuinely useful input is the weaker ONE-SIDED estimate
Tr(W II)<=C_epsilon m^theta(epsilon) TrW for every W=PWP>=0,
with theta(epsilon)>=0, actual b_V, original hyperbola and all modes. The complete resulting
power is max(theta(epsilon),2epsilon) with a strict logarithmic margin;
eta->0 needs theta(epsilon)->0. Beating3/8 needs theta<3/8 and2epsilon<3/8.
No such estimate has been derived. An absolute scalar primitive or an
independent positive sieve remainder is not substituted for it.

## Decision and next question

This is a fully priced candidate mechanism, not a fresh arithmetic result.
The prior fixed-prime pairing, primorial sieve, absolute primitive, and
positive divisibility-energy routes were already audited and are not repeated.
Concrete impasse: the new cheap three-sector return leaves an actual signed
Type-II upper estimate unpaid; changing U,V alone cannot improve (5).
Rollback before absolute values in (5), or to original S if (1) adds no
usable structure. Ask Pro for ONE source-specific joint mechanism with a
proved complete exponent; if none, require an explicit return to an earlier
branch rather than another equivalent identity. Q14 contour is retained as
a checking tool, not an arithmetic supplier. No automatic no-go for II.

## Reproduction and bounded shelf search

q15_vaughan_checks/check.py passes8192 exact formal-prime-log coefficient
checks, n<=128,U,V=1..8. Omitting K or II is detected. This proves neither
a cofinal bound nor a CCM spectrum; the all-n identity is proved above.
Read-only q15_mobius_shelf found this finite Vaughan source split not present
in the inspected local Q01-Q10 shelf; this is a bounded novelty check only.
The earlier additive Type-II preflight explicitly left Vaughan/arithmetic
Type-II open. It supplies no estimate for this actual hyperbolic block.

Independent q15_vaughan_audit: PASS for exact identities, H1 projected
derivative, noninteger endpoint return (3), constants (4)-(6), same P and
all mixed coordinates. Inherited full-k, rank-two and arch inputs were
checked as inputs, not all upstream results re-proved. Direct12sqrt(m)
is still sharper. Root supplied the exact finite coefficient reproduction.
