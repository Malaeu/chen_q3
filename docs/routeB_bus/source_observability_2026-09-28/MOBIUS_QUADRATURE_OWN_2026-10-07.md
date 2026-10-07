# Exact lattice remainder: bounded own scalar attempt

Previous turn: PROGRESS, ordered-energy/approximate-Selberg tests checked and pushed. Source remains the full Suzuki F=B-Psi and all-event scalar reserve; Q10 not sent. This tests arithmetic information lost by the approximate O(x) Selberg equation. No change of terminal consumer.

## Exact finite identity and root quadrature bound

Using actual Lambda=mu*log, for x=e^t,
F(t)=sum_(d<=x) mu(d)/sqrt d H(log(x/d)),
H(s)=sum_(k<=e^s) log(k)/sqrt k (s-log k).
All endpoints have zero ramp, and every ordered divisor pair is included. Define
H0(s)=integral_1^(e^s) log(u)/sqrt u (s-log u)du
     =4e^(s/2)(s-4)+4s+16,
K(s)=H0(s)-H(s).

For f_s(u)=log(u)u^-1/2(s-log u), elementary finite integration by parts on each unit interval gives
H(s)-H0(s)=integral_1^(e^s) ({u}-1/2) f_s'(u)du.
The endpoints vanish, including a noninteger upper cutoff. With v=log u, the derivative has the sign of
s-(s/2+2)v+v²/2.
For s>0 this upward quadratic is positive at v=0, negative at v=s, hence has exactly one zero in (0,s). Thus f_s is nonnegative and unimodal. Its total variation is twice its maximum. Since v exp(-v/2)<=2/e,
|H-H0| <= max f_s <=2s/e.
At s=0 the formula holds trivially.

Consequently the entire correction obeys
|sum_(d<=x) mu(d)/sqrt d K(log(x/d))|
 <=(2/e)sum_(d<=x) d^-1/2 log(x/d) <=8sqrt x/e.
The last step uses decreasing g(u)=u^-1/2 log(x/u): sum g(d)<=g(1)+integral_1^x g(u)du=4sqrt x-log x-4<=4sqrt x.
This is an explicit whole-sum bound, but it is at the half-power scale and gives no signed reserve. The smooth main term is retained, not silently equated to B.

## Independent exploration of the remaining signed moments

The bounded growth_symbol_attempt derivation retained the full cutoff error for h_j(u)=log^j(u)/sqrt u:
E_j(x)=sum_(k<=x)h_j(k)-integral_1^x h_j(u)du
      =integral_1^floor(x) {u}h_j'(u)du-integral_floor(x)^x h_j(u)du.
Since h_j' is integrable, C_j=integral_1^infinity {u}h_j'(u)du exists. For s>=log56, its bound is
H(s)-H0(s)=C_1 s-C_2+epsilon(s), |epsilon(s)|<=4sqrt2 s² exp(-s/2).
This expansion is recorded as exploration, not separately admitted or needed for the root bound. After convolution its remainder is O(sqrt x) and its main terms are weighted Mobius moments. It supplies no independent sign estimate.

## Exact finite control of the correction sign

A float diagnostic suggested opposite signs at x=10 and 100. The accompanying `mobius_kernel_interval_check_2026-10-07.py` replaces it with rational interval arithmetic only:
- log via range reduction to [1,2) and 32 terms of 2 atanh(z), with geometric upper tail;
- sqrt via integer square root and rational outward endpoints, scale 10^20;
- exact integer Mobius values and exact floor(x/d), no floating cutoffs;
- interval operations using Fraction throughout.

Its asserted enclosures for T_K(x)=sum mu(d)K(log(x/d))/sqrt d are
T_K(10) in (2/125,9/500),
T_K(100) in (-17/200,-83/1000).
Each computed interval has width less than 10^-12. These are finite arithmetic certificates, not Lean proofs. Even if K itself were nonnegative, convolution by mu cannot be assigned a fixed favorable sign by that fact. These two events rule out a sign valid for ALL x for this isolated correction; they say nothing about its eventual sign. T_K is NOT Psi, E_q or a terminal witness. The smooth main term and all Mobius moments must remain jointly in any source estimate.

## Source correspondence and decision

Dictionaries: exact divisor convolution; quadrature defect / periodic Bernoulli integral; signed renewal inverse. Local scalar/Mobius files did not contain this particular kernel estimate; no global absence claim. DLMF https://dlmf.nist.gov/2.10#i was read for the Euler-Maclaurin convention (2.10.1); the first-order fractional-part identity above is proved directly, so no external unverified remainder is imported. A high-precision Hurwitz-zeta algorithm search lead was not consumed.

Independent causal_algebra_audit PASS: ran the rational certificate, checked mu/cutoffs/log tails/square-root brackets, and verified unimodality, endpoint identity and 8sqrt(x)/e bound. No Q10 is justified by this change of representation alone: the finite kernel-sign test already prevents generic positive-quadrature transfer. Exact signed cancellation of the complete Mobius moments remains OPEN; scalar reserve, SP and RH remain OPEN.
