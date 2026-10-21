# Post-Q09 own attempt1: retain the exact second-frequency moment

2026-10-21. Same original full CCM S=P A_prime P, N=m,L=log m,
M=R=floor(m^epsilon),fixed0<epsilon<1/32. Q09 original and conclusion
are the source pins; all three constraints, mixed coefficients and prime
powers remain. No Q10 request. This is a quantitative test, not a new bound.

## Stronger admissible comparison

Use Q09 omega_j=2pi j/L,nu_k=2pi(k+1/2)/L,u=Uc,
r(x)=1/(x^2+1/4),beta=a-g-r. Besides the shared r moment, the exact
endpoint contact f(0)=f(L)=0 gives

 sum_k nu_k^2|u_k|^2=||f'||^2=sum_j omega_j^2|c_j|^2.

Proof: integration by parts expresses the half-shifted Fourier coefficients
of f' as i nu_k u_k; the boundary term vanishes. Parseval in either basis
proves the equality. H1 suffices. No H2 zero-extension or higher endpoint
vanishing is assumed. All mixed terms are inside the actual u=Uc.

For t real and v>0 set

 A(t,v)=max_(|j|<=M)[beta(omega_j)-t r(omega_j)+v omega_j^2],
 B(t,v)=sup_(k in Z)[beta(nu_k)+t r(nu_k)-v nu_k^2].

The scalar comparison yields S<=(A+B)P/2 because BOTH moment differences
cancel exactly. For fixed m,t,v, B is finite and its summands tend to minus
infinity: |beta|<=18sqrt(m), r<=4, and v>0. Thus the supremum is a finite
maximum, although no useful uniform maximizer bound is claimed here.

This differs from Q09's excluded v=0 family. Its distant recurrence peaks
cannot give B>=2W_m-10L after subtracting v nu_k^2. Reusing the Q09 lower
certificate here would be invalid. The strengthened certificate still
relaxes the full u=Uc relation: agreement of moments does not restore it.

## Test the available source input before any numerical optimization

The already audited centered PNT input is

 |b(x)|<=D_m(1+|x|), D_m=C sqrt(m) exp(-c sqrt(L)),

with fixed positive constants after enlargement on the finite initial range.
Hence |beta(x)|<=D_m(1+|x|)+4. Take t=0. Writing Omega=2pi M/L,

 A(0,v)<=D_m(1+Omega)+4+v Omega^2,
 B(0,v)<=D_m+4+D_m^2/(4v).

The latter is the exact maximum of D_m x-v x^2 on x>=0.
Choosing v=D_m/(2Omega) minimizes this available upper budget and gives

 S <= [D_m(1+Omega)+4]P.

The full power is still1/2+epsilon-o(1). Taking the minimum with the
already known2W_m<=12sqrt(m) restores the elementary1/2, not a new gain.
Direct integration of the SAME conservative beta bound also costs
D_m(1+Omega)+4; the two-cap optimization reproduces it. Retaining
beta=b-r<=b removes the harmless4 in either calculation. Thus no optimizer
run is justified solely by this input. This is not a lower bound for the
new certificate and does not exclude a better actual arithmetic estimate.

For an eventual source cap s_m, full returns remain
T_>R<=s_m P-T_<=R and PKP>=-(s_m+50L+8)P.
Short fee only for scalar T; Q02 F2 only for separate V. eta(epsilon)->0
has not been obtained. Ordinary PNT is inherited from the audited Q09
preflight, not assumed with RH-size error or a growing free exponent.

## Decision and scope

One substantive post-Q09 no-gain attempt: the second moment repairs the
specific far-peak obstruction but the available arithmetic input still
fails after full return. Do not label this entire stronger family killed.
Do not repeat optimization of the old PNT envelope as an arithmetic advance.
Before external review, seek a genuinely different source estimate using
actual coefficient coupling; moment bookkeeping alone is insufficient here.
No new code, full prime sums, spectra, Lean or Arb. Root derivation complete;
independent q10_second_moment_review bounded PAPER PASS on corrected draft.
Reviewer caught an intermediate coefficient3/2 error; corrected coefficient1
reproduces direct integration. No exponent change. Native goal ACTIVE; RH OPEN.
AUTOPSY: dropped=NO_DERIVATION; note=Second-frequency moment suppresses distant scalar peaks but inherited PNT still returns half-power or worse.
