# Q09 — exact coupled grids; optimized scalar caps retain half power

2026-10-21. Full original PROSHKA_CCM_CONSTRAINED_DENSITY_Q09_VERDICT_2026-10-21.md:
81006 bytes,1196 LF,SHA256
b8062fec47e464d2fc12f60c35a990a0a6c6a749d1ecaabdf09d5afd1362dc96.
Natural completion observed14:19UTC after one send13:19UTC; download completed
through native Save dialog. Repository copy byte-identical to Downloads.
Entire original read. All14 embedded request-slice hashes verified.
Native goal ACTIVE; full arithmetic exponent unchanged; RH OPEN, no PX claim.

## Exact full source and the first loss

Original integer m,N=m,L=log m,M=R=floor(m^epsilon),fixed0<epsilon<1/32,
all three original contacts/P, actual Mobius convolution and all prime powers.
For omega_j=2pi j/L,nu_k=2pi(k+1/2)/L,

 u_k=fhat(nu_k)/sqrt(L)=(i/pi) sum_j c_j/(j-k-1/2),  ||u||=||c||.

Zero extension to the circle of length2L is only an isometric calculation;
physical source/window remains unchanged. For0<=s<=L the wrapped overlap
vanishes, giving exact two-grid quadrature. At s=L the two masses cancel
exactly; a single original grid fails this mandatory endpoint control.
All mixed terms remain inside |Uc|^2.

With r(x)=1/(x^2+1/4), the original exponential contacts imply

 sum_j r(omega_j)|c_j|^2=sum_k r(nu_k)|u_k|^2=<f,Hf>.

For b=a-g and beta=b-r, full source S=P A_prime P is exactly

 <c,Sc>=(1/2)sum_j beta(omega_j)|c_j|^2
       +(1/2)sum_k beta(nu_k)|u_k|^2.

The root waiting note CCM_Q09_HALFGRID_AUDIT_DISCRIMINATOR.md uses a
combined grid and coefficients divided by sqrt(2L); Q09 uses the odd
subgrid divided by sqrt(L). After that factor2 conversion they agree.
The exact linear quadrature does not automatically extend to b^2 or b_+.

## What is genuinely excluded

A(t)=max_j[beta(omega_j)-t r(omega_j)],
B(t)=sup_k[beta(nu_k)+t r(nu_k)], C*=inf_t(A(t)+B(t))/2.
This is a valid upper certificate for S. It retains mass and one common
moment, but loses the full relation u=Uc. It is not the optimal source bound.

For fixed integer m, 1 and log(p)/log(m), p not dividing m, are rationally
independent by unique factorization. Geometric sums and torus approximation
therefore give arbitrarily distant half-grid samples with all these prime
phases near1. All powers of one prime remain linked. The total exceptional
weight for primes dividing m is <=(sqrt2+1)log m; hence

 B(t)>=2W_m-10log m, W_m=sum_(n<=m)Lambda(n)/sqrt(n),

for every finite t, including an m-dependent choice. The vanishing r term
is taken at fixed m,t, not uniformly in a growing t before the k limit.

Ordinary PNT implies W_m~2sqrt(m) and beta(x)=o(sqrt(m)) uniformly on each
FIXED compact frequency interval. Fix xi0>0; take x_m=omega_ceiling(xi0 L/2pi)
and y_m=pi/L, q_m=r(x_m)/r(y_m). Eventually j_m is within the original band.
The exact dual lower certificate, valid for EVERY t, is

 C(t)>=[beta(x_m)+(1-q_m)(2W_m-10L)+q_m beta(y_m)]/2.

The t terms cancel. First take m to infinity with epsilon,xi0 fixed,
then supremum over fixed xi0. This gives liminf C*/sqrt(m)>=2.
Choosing t=-sqrt(m) gives C*<=2W_m and limsup<=4.
Thus this entire globally capped family cannot yield a power below1/2,
even on a cofinal original subsequence. This is a lower bound on the
CERTIFICATE PRICE, not on any actual CCM eigenvalue or attainable density.

## Tail and full return

For integer K>=2M, original sum c_j=0 gives

 sum_(k outside [-K,K-1])|u_k|^2
 <=8(2M+1)M^2/(3pi^2 K^3)||c||^2.

The full signed beta-quadrature tail is bounded by
24(2M+1)M^2 sqrt(m)/(pi^2 K^3)||c||^2.
K>=L m^(1/6+epsilon+kappa) pays O(m^(-3kappa)/L^3).
The recurrence supplies NO effective peak location. Far peaks can lie in
this small-mass exterior; the theorem does not exclude a coupled finite
window estimate. No new estimate for its interior has been obtained.

Completed return remains S<=2W_m P<=12sqrt(m)P,
T_>R<=2W_m P-T_<=R, PKP>=-(2W_m+50L+8)P.
Short fee is paid once only for scalar T; direct K cancels it algebraically.
Q02 F2 is paid only for separate V. Conditional Q03 power3/8 still needs
unchanged ZF78. No eta(epsilon)->0 or new cofinal source bound.

## Verification and next action

ccm_constrained_density_q09_checks/ preserves extracted registration, both
scripts, expected JSON and reproduced JSON. python3 check_q09.py:334 exact
controls PASS, entire JSON identical including script/registration hashes.
Existing .venv Python diagnostic_q09.py:3 kernel and3 transform cases at
55 digits plus norm/Green tail checks PASS, entire JSON identical.
These are noninterval diagnostics, not asymptotic or full spectral proofs.
No dependency installation, Lean, Arb or full CCM spectral computation.
Root PAPER audit checked §§2–8 including quantifier order and all returns.
Primary DLMF27.12#E5 and27.5#E5 rechecked: ordinary PNT and Mobius-log
identity only; fixed-frequency weighted PNT consequences derived in Q09.
Independent q09_verdict_audit bounded PAPER PASS, bound to the original
SHA256 above: no material defect in quadrature, shared moment, arithmetic
recurrence, optimized dual bound, tail or return. Inherited short/arch/F2
constants checked for propagation, not independently rederived. No new Lean
admission; script JSON retains its original author NOT_RUN review field.

Stop this global-cap family. Roll back before losing u=Uc; do not send Q10
merely requesting the same unpaid joint estimate under a new name. A new
attempt must identify a quantitative source-specific mechanism and its
full price before dispatch. The current exact representation is available,
not itself a successful mechanism. Native research goal remains ACTIVE.
AUTOPSY: dropped=NO_DERIVATION; note=Separate global caps forget attainable coupling; their optimized price is half power, while actual full CCM bound remains open.
