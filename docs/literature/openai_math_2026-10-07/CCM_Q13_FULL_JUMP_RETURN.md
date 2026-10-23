# Full original-P jump and complete seam return — 2026-10-23
Status: finite Arb certificate and bounded PAPER budget; no asymptotic CCM gain.
Root derivation and independent bounded q13_full_jump audit; root reproduced attached Arb script.

Keep Q12 definitions, unitary Fourier transform, original P, N=m,L=log m,
M=R=floor(m^epsilon), both exponential contacts and both time signs.
T=L/2, Omega=2 pi M/L. B is Q12's full signed Volterra operator.

## Exact jump
j(psi)=Bpsi(0+)-Bpsi(0-)=-int_0^T g'(s)[psi'(s)-psi'(-s)]ds.
The pole contribution vanishes by the original exponential contacts.
With a(s)=exp(-s/2)/(1-exp(-2s)) and psi zero extended:
j_ar=c_A psi(0)+int_0^infty a(s)[psi(s)+psi(-s)-2psi(0)]ds,
j_pr=sum_{n<=sqrt(m)} Lambda(n)/sqrt(n)[psi(log n)+psi(-log n)],
j=j_ar+j_pr. The arch tail beyond T is included.

For m=16,M=2,w=2pi/log16 take the unnormalized original-P vector
f(t)=-3/4+(1+4w^2)cos(wt)-(1/4+4w^2)cos(2wt), psi(r)=f(r+T).
Both endpoints and both exponential moments vanish exactly.
The full finite prime sum includes n=2,3,4 (the n=4 endpoint is zero).
j_pr approximately 33.461310029485, j_ar approximately -33.229055925697.
Arb 80 dps, attached script and output rigorously give 0.23225<j<0.23226.
Integration excludes [0,1/10000], whose absolute contribution is bounded
by the explicit positive Taylor bound in the script; no singular numerical
quadrature is used. Thus full cancellation is false on this exact cell.
This is not an eventual sparse-band obstruction or a lower bound on CCM.

## Exact seam removal and all mixed terms
V=sqrt((2M+1)/L), W(y)=sum_{n<=y}Lambda(n)/sqrt(n),
J0=V[2W(sqrt(m))+c_A+14+2log(1+Omega)]. Q12 bounds give
|j(psi)|<=J0 ||psi||. They use ||psi||infty<=V||psi|| and
||psi'||infty<=Omega V||psi||. Exact j is retained before this bound.
For 0<h<=T let H_h(r)=sgn(r)(1-|r|/h)_+/2.
Its jump is 1, ||H_h||^2=h/6; its classical derivative norm^2=1/(2h).
B_reg psi=Bpsi-j(psi)H_h removes the jump exactly.
U=alpha Fpsi-i beta FBpsi, U_reg=alpha Fpsi-i beta FB_reg psi,
E=-i beta j(psi)FH_h, U=U_reg+E.
N=2||U_reg||^2+4 Re<U_reg,E>+2||E||^2.
Also |j|^2=|j_ar|^2+|j_pr|^2+2Re(j_ar conjugate(j_pr)).
No cross term or time quadrant is set to zero.

C_Omega=9+c_A/2+log(1+Omega), b_m=W(sqrt(m))+C_Omega,
A_m=sqrt(1+b_m^2), d=J0 sqrt(h/6).
Q12 row contraction gives ||U||<=A_m||psi||, ||E||<=d||psi||,
hence ||U_reg||<=(A_m+d)||psi|| and the complete correction satisfies
|N-N_reg|<=(4A_m d+6d^2)||psi||^2, N_reg=2||U_reg||^2.
With h=min(T,L/(2M+1)), d<= (J0/V)/sqrt(6).
Using W(y)<=6sqrt(y), the supplied return fee is O_epsilon(sqrt(m)).
This is an upper bound, not a lower bound or proof that sharper return is impossible.
It pays the seam correction only: a useful bound on N_reg-Q remains open.
Reducing h decreases this L2 fee but raises the derivative return |j|/sqrt(2h).
Any Fourier-cutoff argument must pay both, plus the low-frequency comparison.

The already checked full Q12 defect estimate remains
Delta=N-Q <= e_m||psi||^2-D_arch,
e_m=2(1+b_m^2)+2W(m)+c_A=O_epsilon(sqrt(m)).
The linear prime term runs to m, not sqrt(m). No extra arch fee is added
to this full Q bound. Separate conversion to the prime receiver and T_{>R}
must return arch and short-divisor budgets exactly once.

## Concrete impasse for Q13
The full jump survives; removing it preserves all signs but the supplied
mixed return still has exponent 1/2. The regularized joint comparison with
actual xi multipliers is unpaid. Neither derivative regularity alone nor
boundary unitarity licenses Poisson reconstruction or RH innerness.
Three own post-Q12 tests: anchor budget; isolated-prime regularity; full
jump with complete seam return. None yields a full exponent gain.
