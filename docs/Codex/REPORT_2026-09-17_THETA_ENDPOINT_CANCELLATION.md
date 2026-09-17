# Full theta endpoint cancellation in the forced quotient

Status: ACCEPTED_LIMITED_PAPER; independent review and parent check complete.
Base: 6de89d8894e358f6c9469edae75eae9d2040f178.
This is an actual-source approximation/domain audit. It does not prove VAR,
global Pick, positivity of original V, or RH. Canonical production is HOLD.
No numerical source test or external theorem is used.

## 1. Return to a paid source identity

Use exactly q=Phi/Z, Z=xi(1/2)>0, and the full source

  q(x)=sum_(n>=1) q_n(x),
  q_n(x)=Z^(-1) exp(x/2)(4y_n^2-6y_n)exp(-y_n),
  y_n=pi n^2 exp(2x).

On x>=0 these modes are positive. The complete theta identity makes q
even, hence q'(0)=0. This parity and the derivative-polynomial recurrence
are already present in REPORT_2026-09-12_ODD2_ORIGIN_CORNER.md, equations
(3)--(5); the identity q'(0)=0 is NOT a new discovery. Here we determine
its exact effect on the new fixed Mellin quotient and a proposed common
compensation. The existing full-series tails justify the differentiations.

Put a_n=pi n^2 and P(y)=8y^2-30y+15. Then

  p_n(x):=-q'_n(x)
    =Z^(-1) a_n exp(5x/2)P(a_n exp(2x))exp[-a_n exp(2x)],
  b_n=p_n(0)=Z^(-1)a_n P(a_n)exp(-a_n).                (C1)

The sums of b_n and their absolute values converge. Normal convergence of
the differentiated series near zero and parity give

  sum_(n>=1) b_n=0.                                     (C2)

The signs in this equality are strict. P increases on [3,infinity), and
3<pi<22/7 gives P(pi)<P(22/7)=-13/49<0. Thus b_1<0.
For n>=2, a_n>12 and P(a_n)>P(12)=807>0, so b_n>0. Hence

  -b_1=sum_(n>=2)b_n>0.                                 (C3)

This is a full-series balance with fixed square rates and fixed weights.
It is not an independently adjustable constant or a prime positivity law.

## 2. Every raw finite theta cutoff produces a spurious pole

Use an integer m>=1 and define only for this diagnostic

  q^[m](x)=sum_(n=1)^m q_n(x), x>=0,
  rho^[m](s)=q^[m](sqrt(s)),
  D^[m](u)=2 integral_0^infinity x^(2u)q^[m](x)dx,
  N^[m](u)=integral_0^infinity x^(2u-1)(-q^[m]'(x))dx.

D^[m] converges for Re u>-1/2; N^[m] initially for Re u>0.
These are RAW THETA-MODE cutoffs. They are not the finite gamma-law Mellin
M_N of the earlier MELLINEDGE request. No assertion about that M_N is made.
The fixed factor 1/Z need not normalize the cutoff; it cancels in N/D.

By (C2)--(C3),

  a_m^*=q^[m]'(0)=sum_(n>m)b_n>0                       (C4)

for every finite m. In particular the positive finite source has positive
slope near zero even though the complete q has zero slope and decreases
for x>0. There is no contradiction: q^[m]'(0) tends to zero as m grows.

Taylor expansion at zero and the finite-mode tails imply, as u decreases
to zero through positive reals,

  N^[m](u)=-a_m^*/(2u)+O_m(1),
  D^[m](u)=D^[m](0)+O_m(u),  D^[m](0)>0,
  phi^[m](u):=4N^[m](u)/D^[m](u)
       =-2a_m^*/[D^[m](0)u]+O_m(1).                    (C5)

Indeed subtract q^[m]'(0) on 0<x<1. The residual is O_m(x), whose
log-weighted integral stays bounded for u near zero. The integral from
1 to infinity is analytic there. D^[m] is analytic and positive at zero.
Thus every raw finite cutoff has phi^[m](u)<0 for all sufficiently small
positive u and fails even nonnegative real-axis Bernstein membership.

For the FULL source q'(x)=q''(0)x+O(x^3) near zero, and its full derivative
tails give

  N(0)=integral_0^infinity [-q'(x)]/x dx in (0,infinity),
  D(0)=1,
  phi(0)=4N(0)>0.                                      (C6)

Strict positivity uses the already proved strict decrease of actual q.
Hence (C5) is an approximation artifact, not an actual-source obstruction.
The convergence of N^[m] to N holds on compact subsets of Re u>0 by the
normally convergent full derivative series and a common endpoint/tail
majorant. It cannot be uniform down to u=0, where each approximation has
a pole and the limit is finite. Compact subsets with Re u>0 stay a positive
distance from this endpoint; no contradiction with local convergence arises.

There is also a precise downstream domain loss. Local Taylor subtraction
continues D^[m] near u=-1, where its residue is q^[m]'(0)=a_m^*>0:
the term 2a_m^* integral_0^1 x^(2u+1)dx equals a_m^*/(u+1).
Gamma(u+1/2) is finite and nonzero at u=-1. Consequently

  H^[m](u)=D^[m](u)/Gamma(u+1/2)

has a genuine pole at -1, unlike the already proved entire FULL H.
Every odd Taylor coefficient of q would similarly produce an integer
Mellin pole; full evenness removes these coefficients. Only the first
one needs to be nonzero to establish the cutoff defect above.

## 3. One common boundary compensation cannot make every mode positive

The obvious null correction using (C2) would choose a finite real function
R(x), independent of n, and write

  -q'(x)=sum_(n>=1) J_n(x),
  J_n(x)=p_n(x)-b_n R(x).                              (C7)

For each fixed x the series is absolutely convergent, and its sum is
unchanged because sum b_n=0. A condition R(0)=1 would make each J_n vanish
at the endpoint; the following obstruction does not even require it.

Let beta=(15+sqrt(105))/8 be the larger root of P and
x_0=(1/2)log(beta/pi)>0. Fix 0<x<x_0. Then p_1(x)<0.
For n>=2, b_n>0, and putting t=exp(2x)>1 gives

  p_n(x)/b_n
    =t^(5/4) [P(a_n t)/P(a_n)] exp[-a_n(t-1)]
       ->0 as n tends to infinity.                     (C8)

The polynomial ratio tends to t^2 and the exponential tends to zero.
If J_n(x)>=0 for all n>=2, then R(x)<=p_n(x)/b_n for every such n,
hence R(x)<=0. But b_1<0 and p_1(x)<0 imply

  J_1(x)=p_1(x)+|b_1|R(x)<0.                            (C9)

Thus no common R, even signed and without endpoint restrictions, can
turn all compensated individual modes nonnegative on (0,x_0). This
excludes ONLY the common-profile ansatz (C7). Grouped/nonlocal corrections
or the positivity of the complete sum are not excluded; the complete
-q' already has a positive sign. In particular it is not a V witness.

## 4. What this supplies, and what it does not

The known source reciprocity performs a concrete cancellation: it removes
an artificial numerator pole and the corresponding failure of entire H
created by every raw finite theta cutoff. This is a source-domain fact.
It supplies no sign of the logarithmic variance comparison

  0<=Var_D,u(log s)-Var_N,u(log s)<=1/u^2, u>0,          (VAR)

where the two laws have densities proportional to s^(u-1/2)rho(s) and
s^(u-1/2)(-rho'(s)). The recently reviewed rho_e=exp(-s-epsilon s^3)
control proves strict log concavity alone cannot supply VAR.

A bounded actual-source VAR attempt must retain the paired full laws and
(C2), and cannot use phi^[m] as an admissible Pick approximation or claim
a modewise positive correction from (C7). The full additive PF property
of r remains available, but no implication from it to VAR is proved here.
A VAR proof would remain only a necessary filter for the sufficient Pick
entrance. A strict actual-source VAR failure would reject that entrance,
not RH or V positivity. The original all-finite complex V remains OPEN.

## Independent acceptance

Verdict: `ACCEPT_THETA_ENDPOINT_CANCELLATION_AND_RAW_CUTOFF_DOMAIN_OBSTRUCTION_ONLY`.
Candidate SHA256: `b2bfcc8047944efc949cb2295ce87f3d8d418464523c0964d1fbf6157f49878d`.
Full review SHA256: `f9d14772c0080a1fb84b49d75c0330b75f6e2a9531308c07f09d83787e7f0919`.
The paired certificate retains complete independent and parent checks.
Acceptance covers only C1--C9 and their stated domains. No actual VAR,
Pick, original V sign, RH, canonical admission or counter reset follows.
