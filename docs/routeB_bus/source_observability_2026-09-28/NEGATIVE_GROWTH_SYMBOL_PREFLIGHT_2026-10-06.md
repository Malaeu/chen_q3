# Negative-growth preflight while Pro question1 runs

Same full K_m, m=N, L=log m, original eventual family. No lower bound is
proved here. Root derivation and one bounded independent read-only check
by growth_symbol_attempt agree on the following conditional consumers.
This note does not change the phase or close SP, G1, G3, or RH.

## Quantifiers: all late cells are unnecessary

Let x_j=(-lambda_min(K_mj))_+ and m_j tend to infinity. The checked
off-critical-zero alternative gives x_j>=c m_j^delta/(log m_j)^(2delta)
on EVERY sufficiently late cell. Consequently it suffices to establish

 liminf_j log(1+x_j)/log(m_j)=0.                         (LI)

Equivalently, for every eta>0 and every J there is j>=J with x_j<=m_j^eta.
Forward: choose a late log-ratio below eta. Reverse: for each eta use the
asserted unbounded subsequence and log(1+m^eta)/log m -> eta, then eta->0.
The adverse alternative forces the same liminf to be at least delta>0.
Constants C_eta in a subsequence bound can be absorbed by enlarging eta.
No existence of a good subsequence has been supplied. This relaxes the
requested bound's quantifiers, not its RH-level mathematical difficulty.

## Exact scalar multiplier and the carrier's actual Fourier tail

Use fhat(omega)=integral f(t)exp(-i omega t)dt. For support in I,
Q_f(s)=(1/pi)integral |fhat(omega)|^2 cos(omega s)domega. Hence

 W(f)=(1/(2pi))integral sigma_m(omega)|fhat(omega)|^2 domega,
 sigma_m(omega)=2 integral_0^infinity J(s)(1-cos(omega s))ds-cA
   +2 integral_0^L 2cosh(s/2)cos(omega s)ds
   -2 sum_(n<=m) Lambda(n)/sqrt(n) cos(omega log n).

Here J(s)=exp(-s/2)/(1-exp(-2s)), cA=EulerGamma+log(8pi)+pi/2.
Endpoint n=m is harmless because Q_f(L)=0. The first term is
Re digamma(1/4+i omega/2)-digamma(1/4), obtained by expanding J into
its positive exponential series and integrating each cosine difference.
It grows logarithmically; the finite pole/prime remainder is bounded
for fixed m. Thus sigma_m tends to positive infinity as |omega| grows.

For the actual phased basis, omega_n=2pi n/L and sinc(x)=sin(x)/x,

 fhat_(psi_n)(omega)=(-1)^n sqrt(L) sinc(L(omega-omega_n)/2).

The sharp zero extension creates infinite 1/|omega| amplitude tails.
The logarithmic archimedean multiplier is integrable against their squares.
The identity is over ALL real frequencies; checking only the carrier
frequencies, or pretending fhat is supported below 2pi m/L, is invalid.

A pointwise lower bound on sigma_m implies the same lower bound on K_m,
but is stronger than the required compressed-form estimate. No unconditional
sharp-cutoff counterexample to a subpolynomial lower symbol bound was found
in this bounded pass. The off-critical-zero alternative conditionally forces
min sigma_m<=lambda_min(K_m)<=-c m^delta/(log m)^(2delta), not an actual
negative example. The first unsupplied assertion is still a uniform lower
estimate of the JOINT multiplier or its carrier-weighted integral.

## Paid finite-frequency reduction (root, independently checked)

The preceding warning does not require an infinite-frequency estimate.
For f=sum_(|n|<=m) v_n psi_n, d=2m+1 and Omega=2pi m/L, direct integration
with the ACTUAL endpoint phase gives

 fhat(omega)=2 sin(omega L/2)/sqrt(L)
              * sum_n v_n/(omega-omega_n).

The apparent poles are removable. For B>Omega they are outside the tail
region. Cauchy-Schwarz and integration over both tails imply

 T_B=(1/(2pi)) integral_(|omega|>B) |fhat(omega)|^2 domega
     <=4d/[pi L(B-Omega)] ||v||2^2.

Indeed each denominator has modulus at least |omega|-Omega; use sin^2<=1
and integral_B^infinity (omega-Omega)^-2 domega=(B-Omega)^-1.
The symbol's globally valid crude floor is sigma_m>=-V_m, where

 V_m=cA+8sinh(L/2)+2 sum_(n<=m) Lambda(n)/sqrt(n)
     <=cA+(4+4L)sqrt(m).

This follows from nonnegative D_arch, absolute value of the finite pole
integral, Lambda(n)<=L and sum_(n<=m)n^-1/2<=2sqrt(m). If a_m>=0 and
sigma_m>=-a_m on |omega|<=B, splitting the Plancherel integral gives

 lambda_min(K_m)>=-a_m-V_m*4d/[pi L(B-Omega)].           (FB)

Choose B=m^(3/2+epsilon) for any fixed epsilon>0. Eventually B>=2Omega,
d<=3m, V_m=O(L sqrt(m)), so the omitted-tail penalty is O(m^-epsilon).
Thus a subpolynomial lower symbol bound on this polynomial frequency
range is sufficient; no uncontrolled frequency truncation is involved.
The required lower symbol bound INSIDE that range remains OPEN. Formula
(FB) does not supply it and does not claim the pointwise bound is necessary.
One bounded independent pass by growth_symbol_attempt checked the phase,
constants, signs and the original-carrier tail; no second proof route opened.

Source checks: CCMFiniteWeilSourceMatrixN1.lean:39-60,89-100 and the full
source prime pairing definitions; KERNEL_INDEPENDENT_CHECK_2026-09-08.md:24-25.
No fresh Lean build. No claim that pointwise-symbol positivity is necessary.
Averaging sigma_m does not control its infimum; averaged matrices need not
have a positive member. Varying original carriers are not nested.

Question1 remains pending in Proof of CCM Growth; no duplicate/addendum sent.
At 19:00 UTC Oct6 the browser showed ongoing new reasoning, Pro and Stoppen,
although read_thread returned idle with only the saved user message. Keep
the existing handle; that observational mismatch does not justify restart.
