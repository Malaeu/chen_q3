# UI.25: rational clipping with a paid exact error

2026-10-09. Independent read-only q05_moment_audit R1–R4 PASS. RH/SP/UI25 OPEN.
Same Q4 full Q_b(u), exact w(b), rho, common profiles and scales.
This tests whether replacing subtraction and the sharp selector by a
denominator creates a useful analytic input. It does not claim a gain.

## R1. Exact scalar comparison

For x>=0,V>0 define R_V(x)=x²/(x+V). Exactly

 0<=R_V(x)-(x-V)+<=V/2.                           R1

For x<=V the difference is x²/(x+V), increasing from0 toV/2.
For x>=V it is V²/(x+V), decreasing fromV/2. Thus V/2 is sharp.
At V=V0/24 define E_rat=sum_b w(b)sum_u rho R_V(Q_b(u)),
where every original sixthfree row and mask is retained. Then

 T_Q(V)<=E_rat<=T_Q(V)+(V/2) sum_b w(b)sum_u rho.    R2

The final mass is O(PU), and PU V0=H U^-3/500 exactly.
Thus the error is O(H U^-3/500), below targetHU^-1/200 with
margin1/1000 before losses. At that target budget the rational
functional and original excess are equivalent. V has not been set
rowwise; it is fixed in L and across the common profile family.

## R2. Actual fractional selector and principal return

Put g_b(u)=Q_b(u)/(Q_b(u)+V), in[0,1]. It is unit-invariant,
but not asserted radial or smooth as a function of the row u.
Then E_rat=sum w rho g_b Q_b. Replace f_b of UI19 by
f_b^rat=1_(u!=0,u6free)rho g_b, with its EXACT Fourier spectrum.
All finite identities UI20–23 hold for this actual nonnegative weight.
The principal same-sixth-core block is bounded by UI17:

 0<=P_rat=sum w rho g_b Pi_b<=PU*loss.
 E_rat=P_rat+F_np^rat.                             R3

F_np^rat retains both long divisor sums, same-unit-character restriction,
unequal sixth cores, all redundant zeros and exact w(b). There is no
separate level credit here: it is built into the denominator defining g.
The sufficient unproved input is F_np^rat<=H U^-1/200*loss.
By Q3 and R2 the full return is

 T_M(V0)<=24(P_rat+F_np^rat)+2E_KB+8E_I+8E_delta.   R4

No selector derivative is used. A future bound must hold for every
common profile first; only after restoring full M energy may the
old positive-energy Sobolev and finite inversion be applied.

## R3. Cheapest attempted bounds do not close it

R_V(x)<=min(x,x²/V). The first gives precisely the old energy bound.
The second requires E2=sum w rho Q_b²<=H V U^-1/200*loss.
Since Q_b is a six-unit mean of |J|², this is a fourth-type input,
not supplied by the plain S fourth moment. Jensen only gives
sum rho Q_b²<=sum rho |J_b|^4 after full unit summation.
The old pointwise Q_b<=L*loss and second moment give E2<=L E1*loss.
Dividing by V costs exponent ell-(5p-3/500)>0 throughout the
upper band; this strictly worsens the available old bound.
This is a failed upper-bound calculation, not an actual lower bound.

Exactly R_V(Q)=Q-V+V²/(Q+V). Discarding the positive reciprocal
term has the WRONG direction for the required upper bound. Also
R_V(Q)=integral_(t>=0) e^(-Vt) Q² e^(-Qt) dt. The row sum is
finite, so this identity can be summed without a limiting exchange
problem. No estimate of that Laplace functional has been obtained.

## Decision boundary

The sharp threshold can be removed at a paid error, so discontinuity
itself is not an established obstruction. The missing input is still
quantitative control of the actual coupled arithmetic functional.
Generic second-moment or pointwise-to-fourth replacements are STALLED
as suppliers. Do not infer spatial regularity from smoothness in Q,
or use a resolvent identity as though it were the missing bound.

## Bounded alias return

Shelf queries: nonlinear large sieve level sets character polynomials;
soft threshold positive part moment majorant; entropy variational large
values arithmetic Fourier restriction. All three returned INCOMPLETE
(q3_docs freshness), not absence. No consumer-mapped supplier returned.
Reused Montgomery source and verified hash/locator from
HV27_THRESHOLD_FRONTIER.md. Theorem3 (translation p125) concerns counts
for primitive Dirichlet characters and sampled s-values, not the actual
Hecke ideal family, masks and weighted rational excess. No new bridge
from its count to our coefficient-coupled functional was obtained.
The existing source-mapping exclusion remains; no external theorem is
consumed. R1–R4 are direct scalar/finite-sum arguments, not literature claims.
