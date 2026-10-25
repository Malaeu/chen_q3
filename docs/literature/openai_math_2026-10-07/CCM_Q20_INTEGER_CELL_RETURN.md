# After Q19: exact integer-cell centering on the actual source pair

2026-10-25. Bounded own test; original sparse P and actual C of Q19.
No new arithmetic exponent. No Q20 sent. Generic heat/high-order smoothing
already tested (CCM_COMPOSITE_HEAT_RETURN, CCM_HIGH_ORDER_Q10_CONCLUSION);
not counted again. The existing CCM_TRANSPORT_QUADRATURE_CONTROL already isolates cheap weight-one
quadrature and the Lambda-1 remainder. This source-pair specialization is a
transfer/discriminator, NOT an additional new arithmetic mechanism. It isolates
the integer-lattice quadrature from
prime irregularity, after the accepted Q19 continuous subtraction.

For integer m, y=2a>=0, set
 f_y(x)=x^(-1/2)[C(y-log x)+C(y+log x)], x>=1.
Keep its complex value and both temporal directions. Exactly
 J(a;m)-J0(a;m)=sum_(n=2)^m (Lambda(n)-1)f_y(n)+E_y,
 E_y=sum_(n=2)^m integral_(n-1)^n [f_y(n)-f_y(x)]dx.
No upper atom, lower cell or prime power is dropped. Finite sums justify
all exchanges. E_y is ordinary right-cell quadrature, not prime discrepancy.

Let g(u)=|C(u)|/2+|C'(u)|, K_w=integral_R exp(u/2)g(u)du<infinity,
using inherited double-exponential source tails. Direct differentiation:
 f'_y(x)=x^(-3/2)[-C(y-logx)/2-C'(y-logx)
                         -C(y+logx)/2+C'(y+logx)].
Hence |E_y|<=integral_1^m |f'_y(x)|dx. Substitute u=y-logx in
first orientation, u=y+logx in second. With L=logm this is at most
 exp(-y/2)integral_(y-L)^y exp(u/2)g(u)du
 +exp(y/2)integral_y^(y+L) exp(-u/2)g(u)du.
Since u>=y in the second integral, exp((y-u)/2)<=exp((u-y)/2).
The two integration intervals are disjoint except their endpoint, giving
 |E_y|<=K_w exp(-y/2)=K_w exp(-a).
This is a bound for the COMPLEX error, so it remains valid after the actual
phase exp(2i gamma a), real part, and positive averaging on [h-T,h].
The full averaged error obeys
 |Ebar|<=K_w exp(-(h-T))(1-exp(-T))/T=o(1).

Thus define the full signed arithmetic target
 Abar=T^(-1)integral_(h-T)^h Re[exp(2i gamma a)
                   sum_(n=2)^m (Lambda(n)-1)f_(2a)(n)]da.
Exactly B_T=Abar+B0_T+Ebar. Q19 already paid B0_T=e_m^0=o(1).
This preserves the phase and all mixed source contributions. Apply the same
inherited P return to the WHOLE source pair, never per cell. Since K=Arch-S on the original P and S=self-2B_T, a lower bound
Abar>=-H_m implies the complete floor
 average z*K_m z>=-2H_m-2e_m^0-2|Ebar|-D_w(50L+8)
                                  -C_self,w-rho_S.
No extra short-divisor fee is added to this direct K receiver.

## What completion actually supplies

|Lambda(n)-1|<=Lambda(n)+1. The existing unit logarithmic-shell mass
bound used in Q17 gives sum |Lambda(n)-1| |f_(2a)(n)|<=C_w exp(a)
(the added unit integer weights obey the same mass bound).
Therefore H_m=C_w exp(h)(1-exp(-T))/T is sufficient, still
sqrt(m)/(L*T). At T=alpha L the inherited total budget remains
sqrt(m)/L²+L. Desired signal m^delta/L^(2delta+1) is not beaten.
No unknown estimate for accumulated Lambda-1 is assumed.

Conclusion: integer-lattice geometry is cheap on this source pair; the
remaining difficulty is the signed weighted arithmetic sequence Lambda-1.
Replacing its partial sums by a generic PNT bound is the already documented
Abel/PNT impasse, not a further experiment. This representation alone supplies
no mechanism reducing that main sum. Not a no-go for signed cancellation.
No numerical data/Lean/Arb or new Pro question. Bounded read-only q20_centered_shelf check: PASS after correcting parentheses
in the displayed exponential inequality. Reviewer initially questioned the K
sign, then withdrew the objection upon using K=Arch-S; lower bound is correct.
Shelf match: CCM_TRANSPORT_QUADRATURE_CONTROL §2,(7), Q04 centered primitive
and Q17 shell budget. Do not count this specialization as a new mechanism
or as one of three independent no-gain attempts.
