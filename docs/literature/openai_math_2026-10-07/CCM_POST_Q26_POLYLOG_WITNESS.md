# Actual-source polylogarithmic witness inside the original CCM band

2026-10-25. STATUS: BOUNDED_PAPER_PASS_CONDITIONAL_ON_INHERITED_RECEIVER.
Read-only independent polylog_contact_check audited the full payload,
including (3)--(9), actual-profile normalization and the final Q10 budget.
No material flaw found; upstream source/Weil identities remain inherited,
not independently recertified. No Lean or interval computation was run.
Source baseline: 44fc95ed. This is a conditional witness refinement, not an
upper bound on the prime operator, T_{>R}, or a claim of RH. The original
all-vector sparse-band goal remains open and is not replaced by this lemma.

## Contract and inherited inputs

Keep the literal K_m, N=m, L=log m, original frequencies 2 pi j/L and the
three original contacts b*c=v_+*c=v_-*c=0. Fix a hypothetical actual zero
w=delta+i gamma, 0<delta<1/2, multiplicity r. Use the separately normalized
actual g,k in Q26 verdict (1.1)--(1.3), and the whole complex pair
f_a=exp(-i gamma a) tau_a g-exp(i gamma a) tau_{-a} k.
The inherited receiver supplies its full Weil value -2r exp(2delta a), bounded
L2 norm, vanishing moments at +/-1/2, and double-exponential physical tails
for every FIXED derivative. These upstream results are assumed as in
CCM_RESTRICTED_PRIME_RECEIVER.md; they are not recertified here.
Precisely the inherited physical bound needed is
|g^(q)(t)|+|k^(q)(t)|<=C_(w,q) exp(-c_(w,q) exp(2|t|)).
A weaker exp(-c exp(|t|)) bound would NOT justify the following L^2
cutoff exponent. The source normalization agrees: if d_w is the unfiltered
zero normalization, c_w=(w^2-1/4)d_w, so applying (partial^2-1/4)/(w^2-1/4)
to its separator gives exactly Q26's g (and likewise the partner).

Let h=L/2-log L. The argument is uniform for h-T<=a<=h, 0<=T<=h/2.
Put M0=ceil(8L^2). Eventually M0<m and M0<=floor(m^epsilon) for every fixed
epsilon>0. Define H0 as the original coefficient vectors supported on
|j|<=M0 satisfying all three original contacts. Correction is performed
INSIDE this band, not by projecting onto the larger band afterwards.
Thus H0 is a subspace of ran P_(m,epsilon), without altering K_m or P.

## Source-specific Fourier estimate

Q26 gives M_g(z)=A(z)/(c_w(w-z)^r), M_k(z)=A(z)/(c_v(v-z)^r),
A(z)=-4(z^2-1/4)xi(1/2+z). On the imaginary axis the xi gamma factor gives
exp(-pi |tau|/4) times a polynomial. A polynomial zeta bound suffices:
the elementary continuation formula
zeta(s)=s/(s-1)-s integral_1^infinity {x}x^(-s-1) dx for Re s>0
gives |zeta(1/2+i tau)|<=C(1+|tau|). The fixed denominators are bounded
away from zero on this axis and have polynomial behaviour at infinity.
Absorb all polynomial factors into the weaker exponential to obtain

    |M_g(i tau)|+|M_k(i tau)| <= C_w exp(-|tau|/8).       (1)

Translation and the complex prefactors have modulus one on this line.
Primary gamma inputs: DLMF 25.4.E4 and 5.11.E9 (fixed real part).
https://dlmf.nist.gov/25.4.E4 ; https://dlmf.nist.gov/5.11.E9
No assumption on absence of other zeros is used for this bound.

Use the inherited fixed-width smooth cutoff chi on [-L/2,L/2]. Let
F=chi f_a and d=F-f_a on the whole line. The transition is at distance
at least log L-O(1) from either center. For q=0,1,2,

    ||d^(q)||_1 <= C_w rho,  rho=exp(-c_w L^2).          (2)

This follows by integrating the inherited double-exponential tails, with
only fixed derivative orders. It does NOT assert that chi is analytic.
After translation to [0,L], Fourier coefficients satisfy for |omega_j|>=1

 |c_j| <= C_w L^(-1/2)[exp(-|omega_j|/8)+rho |omega_j|^(-2)]. (3)

The translation adds only a unit phase. Set Omega=2pi M0/L, t0=exp(-Omega/8).
Geometric sums with spacing 2pi/L and the elementary power tails give for
e=F-F_M0, on its interval (including endpoint values),

 a0=||e||_2 <= C_w[t0+rho Omega^(-3/2)],
 a1=||e'||_2 <= C_w[(1+Omega)t0+rho Omega^(-1/2)],
 ainf=||e||_infinity <= C_w[t0+rho Omega^(-1)].          (4)

All constants are independent of m,a,T. In particular Omega>=16pi L,
t0<=m^(-2pi). The rho contribution is summed using its power tail; a
uniform small bound on individual coefficients alone would not suffice.

## Full form and contacts, including cross terms

Use precisely the inherited zero-extension form estimate
||e||_E^2<=(m+16)a0^2+2a1^2+8ainf^2. It includes the endpoint jump strips.
Since Omega=O(L), ||e||_E<=C_w sqrt(m)(t0+rho) eventually. Together with
||F||_E<=C_w sqrt(m), the full quadratic-form continuity bound gives

 |W(F_M0)-W(F)| <= C_w m[(t0+rho)+(t0+rho)^2].          (5)

This bounds the whole pair, not its lobes separately. All mixed terms are
retained via the full cross-error term. The inherited cutoff fee is
C_w m exp(-c_w L^2), absorbable after reducing c_w.

Restrict the original v_+,v_- to M0 and normalize them, and set
b0=ones/sqrt(2M0+1). The receiver's explicit coefficient calculation gives
||v_+,M0||^2=m(1+O(L/M0)), ||v_-,M0||^2=1+O(L/M0),
normalized mutual overlap O(L/sqrt(m)+L/M0), and overlaps with b0
O(sqrt(L/M0)). Hence their three-column Gram matrix is >=I/2 eventually.
These calculations require M0/L->infinity, not a power bandwidth.

The full cutoff Fourier series has zero endpoint value and is absolutely
convergent. Thus

 |b0*c_M0| <= sqrt(L/(2M0+1)) ainf <= C_w(t0+rho).       (6)

Both cutoff Laplace moments are at most m^C rho after translation. For each
normalized exponential contact, subtract the omitted Fourier tail. Cauchy-
Schwarz bounds it by a0 times the full/truncated exponential norm ratio,
which is bounded. Thus each normalized residual is <=C_w t0+m^C rho.
The Gram bound, with all three constraints corrected simultaneously, gives

 z=projection_H0(c_M0),  ||z-c_M0||<=C_w t0+m^C rho.    (7)

Padding z with zeros gives all original equations exactly; no high modes
are added. Using the inherited FULL ||K_m||<=40 sqrt(m)L and bounded
||c_M0||, both linear mixed correction and quadratic correction cost

 C_w sqrt(m)L [t0+t0^2]+m^C rho.                       (8)

Combining (5), (8), and the cutoff fee proves the full return bound

 |z*K_m*z +2r exp(2delta a)|
       <= C_w m^(1-2pi)+m^C exp(-c_w L^2)=o(1).        (9)

Constants/exponents C may increase finitely between lines. No arithmetic
term is dropped or replaced: Lambda and every prime power remain in K_m.
The norm of z is bounded independently of m. At a=h the negative signal
diverges, so z is nonzero and normalization gives the same conditional
negative Rayleigh bound -c_w m^delta/L^(2delta), now already on H0.

## What this changes and what it does not

This supplies a smaller sufficient test space if (9) survives independent
review. It does not prove a prime upper bound on H0 or on original P.
The exact continuous cancellation and archimedean price 50L+8 still apply.
An INDEPENDENT subpolynomial upper floor for the full prime form on H0
would suffice against the same witness; it is currently OPEN.
The original requested T_{>R} estimate on all ran P remains OPEN.
No inference from smaller dimension alone to a smaller spectral bound is
valid. Next test must estimate actual signed prime entries jointly on H0,
or return to the original all-P supplier; no repetition of the adverse
zero identity as a favorable estimate is allowed. No Q27 has been sent.

## Immediate budget test against the existing supplier

Keep ORIGINAL R=floor(m^epsilon); do not change the target divisor split.
The already paid short-divisor bound from CCM_MOMENT_Q10_CONCLUSION.md is
(56+32Omega)sqrt(R)+12(1+log R)^2. On H0, Omega=O(L), so its cost is
O_epsilon(m^(epsilon/2)L+L^2), rather than the old power-band cost with
exponent 3epsilon/2. This is a smaller short-sector fee only.
The SAME Q10 long-sector supplier still costs
4 Ccl m^(3/8)L^2 log(3L), conditionally on ZF78. Its bound is uniform in
frequency but does not decrease with the bandwidth. Consequently the full
known conditional exponent remains 3/8. The unconditional 12sqrt(m) prime
upper fallback is also unchanged. Reduced dimension does not yet yield
eta(epsilon)->0: the joint long-sector estimate remains the precise debt.
