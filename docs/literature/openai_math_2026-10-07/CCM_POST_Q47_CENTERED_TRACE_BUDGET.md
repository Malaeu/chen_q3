# Post-Q47 original-P centered two-copy attempt

Status: BOUNDED_PAPER_PASS; no new arithmetic exponent.
Original N=m,L=log(m),M=R=floor(m^epsilon),fixed0<epsilon<1/32.
All operators below act on H_P=ran P with its original norm; d=rank P.
The d=0 case is vacuous. For sufficiently large m, d=2M-2>=2.
No original-P hypothesis or sparse receiver is changed.

## Exact full source before moduli

Let H(s)=P Q_M(s)P restricted to H_P, 0<=s<=L, including H(L)=0.
Let dnu(s)=sum_(2<=n<=m) Lambda(n)/sqrt(n) delta_log(n)-exp(s/2)ds.
Define C=integral H(s)dnu(s)=A+H_d, with A the full original compressed
prime operator and 0<=H_d<=4 I. Both temporal directions occur in Q_M.
There is no projection inside a single H except its original compression.

Put a=Tr(C)/d and V=Tr((C-a I)^2). Then exactly
 a=(1/d) integral Tr H(s)dnu(s),
 V=double integral [Tr(H(s)H(t))-TrH(s)TrH(t)/d]dnu(s)dnu(t).
The real symmetric two-copy kernel is a Hilbert-Schmidt Gram kernel, but
its individual off-diagonal values need not be nonnegative. Its integral V
is nonnegative, not a supplied small quantity. Expanding nu times nu retains
all prime-power pairs, both atom-continuous terms, and continuous-continuous
term. Actual Lambda coefficients, finite limits and the upper atom are kept.
The intermediate P between H(s) and H(t) follows from squaring the already
compressed C; it does not redefine the original first form. If dnu=0,
both a and V vanish exactly, before any inequality.

## One-sided finite-dimensional bound

For eigenvalues lambda_j of C, write z_j=lambda_j-a, so sum z_j=0.
For the largest z, Cauchy on the other d-1 terms gives
 z^2 <= (d-1)(V-z^2), hence
 lambda_max(C) <= a+sqrt((d-1)V/d) =: U_2.
Equality is possible for one upper eigenvalue and d-1 equal lower ones.
The formula is sharp given only the first two spectral moments. It is not
necessary for a small one-sided top: for spectrum(-K,0,...,0),K>0,d>=3,
U_2=K(d-2)/d although lambda_max=0. This is a generic matrix diagnostic,
NOT an actual-source obstruction or proof that V must be large here.

## Complete available budget and limitation

Use the elementary absolute estimate ||A||<=2W_<(m)<=12sqrt(m)=:S_m,
from Q47(7.1)-(7.4) and ||Q(s)||<=2. The sharper inherited one-sided
s_keep is NOT silently promoted into an absolute norm estimate.
Then ||C||<=S_m+4=:S, |a|<=S, V<=Tr C^2<=d S^2.
Therefore U_2 <= S(1+sqrt(d-1))=O(m^(1/2+epsilon/2)).
This is a valid but worse completion than retaining the original fallback.
A negative mean could offset the square-root term, but no such joint
source-specific inequality is supplied by these separate bounds.

If a sharper actual U_2 were proved, C<=U_2 I and A=C-H_d<=U_2 I give
 T_>R <= (U_2+b_div)P,
 PKP >= -(U_2+50L+8)P.
There is no extra H_d fee. b_div=(56+32Omega_M)sqrt(R)+12(1+log R)^2,
Omega_M=2pi M/L; it is charged only for T_>R, not again in the direct K return.
All mixed terms survive in V until the displayed crude norm completion.
Keep the better inherited bound; the required eta(epsilon)->0 is not obtained.

## Shelf discriminator and rollback

Readonly shelf inspection found no identical centered sparse-P formula in
its bounded set. Actual-Mobius Q01 has a different Fejer/long-divisor Gram
trace with an unpaid actual signed off-diagonal. Full-Pi Q06/Q07 atomic
lower bounds do not transfer to this signed sparse-P C. Thus neither small
V nor large V is established here. Do not polish this identity into a claim.
The next useful input would be a proved estimate for the complete signed
two-copy pairing coupled to its actual mean, or a weaker one-sided method
that avoids paying the negative spectrum. No generic prime independence,
RH/strong variance or surrogate phase law is admitted. Concrete impasse:
source-specific two-copy compensation has not been derived. Goal OPEN.

Independent q44_bounded_audit: bounded PAPER PASS, no material findings in signed
double integral, centered bound, generic control, absolute envelope and full return.
Inherited source/receiver assumed; shelf absence not independently checked.
Root verified four exact Fraction negative-spectrum controls (d=3,4,8,16);
these are generic algebra diagnostics, not CCM spectra.
