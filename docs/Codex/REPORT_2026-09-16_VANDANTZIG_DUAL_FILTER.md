# Reciprocal-transform filter: a positive infinitely divisible dual does not pay V

STATUS: INDEPENDENTLY_ACCEPTED_PAPER; ACCEPT_SCOPED_DUAL_FILTER_AND_STIELTJES_STRENGTH_DIAGNOSTIC_ONLY.
Base 4a786c7b74b3efa7ccf8e227963f7f4c6c060d7c. No RH or actual-theta sign result.

## D1. Fix the correct transformed object
For the actual normalized source density q=Phi/integral Phi,
F(z)=integral exp(izx)q(x)dx=xi(1/2+iz)/xi(1/2).
Its entire extension exists by the full theta tail.
The proposed dual on the real axis is H(t)=1/F(it)=xi(1/2)/xi(1/2+t).
Evenness removes the sign of t. F(it)>0 for real t by its moment integral.
That pointwise fact does not prove that H is a characteristic function,
or infinitely divisible, or a Polya-frequency transform.

## D2. Exact control at the same reciprocal-transform operation
Use the already accepted non-theta source
 g0(x)=exp(-x^2)-(1/4)exp(-2x^2)>0.
Its full kernel V_g0 has a negative finite four-node row; see
REPORT_2026-09-14_FULL_V_RANK_TWO_INTAKE.md, R10-R12,
SHA256 51168fb802d7facfb74291d0a3fc0009b121f540711df2fe10ae01cd84c1d14f.
Positive normalization does not change that sign.

Put a=1/(4 sqrt(2)) in (0,1). Gaussian integration gives
 Z0=sqrt(pi)(1-a),
 F0(z)=[exp(-z^2/4)-a exp(-z^2/8)]/(1-a).
For real t the exact dual is
 H0(t)=1/F0(it)
      =(1-a)exp(-t^2/4)/(1-a exp(-t^2/8))
      =(1-a)sum_(n>=0) a^n exp(-(n+2)t^2/8).
The nonnegative mixture weights sum to one. Each summand is the
characteristic function of a centered Gaussian of variance (n+2)/4.
Thus H0 is a characteristic function and (F0,H0) is a van-Dantzig-type pair
under precisely the convention H0(t)=1/F0(it).

More strongly, on real t the absolutely convergent log series gives
 log H0(t)=-t^2/4+sum_(n>=1) (a^n/n)[exp(-n t^2/8)-1].
The sum of the intensities is sum a^n/n=-log(1-a)<infinity.
For every integer m>=1, H0(t)^(1/m) is the characteristic function of
an independent Gaussian of variance 1/(2m), together with a compound
Poisson law of total intensity -log(1-a)/m and jump distribution the
mixture of centered Gaussians of variance n/4, with weights proportional
to a^n/n. This constructs every convolution root explicitly.
Hence H0 is infinitely divisible, while its original full V_g0 has a
negative row. Positive dual energy or infinite divisibility alone cannot
supply the desired implication on this source class.

This control does not have the true source's additive TN-infinity property.
It therefore does not refute a theorem using that additional hypothesis
and reciprocity together. Its Fourier order also need not match every
stronger proposed source class. Only the stated weak criteria are excluded.

## D3. An even stronger weak property still holds for this control
Define E0(u)=F0(i sqrt(u)), using its even entire power series; explicitly
 E0(u)=[exp(u/4)-a exp(u/8)]/(1-a).
For u>=0 put psi0(u)=log E0(u). Then
 psi0'(u)=1/4+(1/8)sum_(n>=1) a^n exp(-nu/8).
Every derivative has the required alternating sign. Thus psi0' is
completely monotone and psi0(0)=0. In particular the reciprocal function
exp(-psi0(u)) is a Laplace transform (already the geometric mixture in D2).

But psi0' is not a Stieltjes function. E0 has simple zeros
 u_k=8 log(a)+16*pi*i*k, k in Z.
For k!=0 they are off the negative real axis and produce simple poles of
E0'/E0. A Stieltjes representation b+alpha/u+integral (u+s)^(-1)dmu(s),
with b,alpha>=0 and mu positive satisfying integral(1+s)^(-1)dmu<infinity,
is holomorphic on C minus (-infinity,0]. If it agreed with E0'/E0 for u>0,
analytic continuation (or the ODE E0'=S E0) would forbid these poles.
Thus complete monotonicity is strictly weaker than the needed Stieltjes
condition even in this explicit reciprocal-transform example.

## D4. Exact strength of the corresponding actual-xi condition
Let E(u)=xi(1/2+sqrt(u))/xi(1/2), defined by the even Taylor series of xi
about 1/2. E is entire, E(0)=1, and E(u)>0 for u>=0. Suppose independently
that E'(u)/E(u) admits the positive Stieltjes representation just stated
for every u>0. The representing function S is holomorphic on the slit plane
Omega=C minus (-infinity,0]. The entire function E solves E'=S E there,
initially by equality on the positive axis and then by the identity theorem.
A nonzero analytic solution of this first-order equation has no zeros in
Omega. Equivalently a zero would force E and all derivatives to vanish by
the equation. All zeros of E therefore lie on the negative real axis.

For each xi zero rho, E((rho-1/2)^2)=0. If (rho-1/2)^2 is negative real,
then rho-1/2 is purely imaginary. Thus the Stieltjes condition implies RH.
This is a sufficient analytic criterion, not a proof that it holds.

Conversely, using the standard entire order-one Hadamard factorization
of xi and its symmetry, RH gives
 E(u)=product_(gamma>0)(1+u/gamma^2),
with zero multiplicities retained and sum gamma^(-2)<infinity. Hence
 E'/E=sum_(gamma>0)1/(u+gamma^2)
is a positive Stieltjes transform of the discrete measure on gamma^2.
The standard factorization is an explicit additional input for this
converse; it is not derived from our source's TN property here.

Consequently asking for the actual Stieltjes measure is already an
RH-strength requirement. Writing it as a Thorin measure or an auxiliary
positive law does not lower that requirement. The known source Thorin
atoms at pi*n^2 describe L_r, not this E'/E, and cannot be substituted for
unknown xi-zero squares.

## D5. Scope / next test
For a proposed published transfer theorem, check whether it proves only
H positive definite / infinitely divisible / psi Bernstein, or actually
E'/E Stieltjes with a positive source-built measure. D2-D3 rule out treating
the former as an automatic full-V sign supplier. D4 identifies the exact
strength and the circularity trap of the latter. A direct implication to
original V still requires its separately pinned consumer theorem.
No actual-theta H property, full V sign, or RH result is proved here.

## Independent acceptance

Candidate SHA256: `61f5cc05daa010f7d467caf6e5b4b79d0f96c764d8e0743578439e2145698020`.
Reviewer `/root/sibling5_check`; review SHA256: `e52aa28316965313dea405b9478a997e64b628e36cc03a74ba7604616c64f1c5`.
Verdict: ACCEPT_SCOPED_DUAL_FILTER_AND_STIELTJES_STRENGTH_DIAGNOSTIC_ONLY.
The parent read the complete review and checked the algebra, source identities,
analytic domains and result scope. Only status and this receipt were added
after review. No canonical or Lean admission is claimed.
