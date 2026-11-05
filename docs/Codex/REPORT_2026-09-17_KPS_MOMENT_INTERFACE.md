# KPS moment interface: what the full theta source actually supplies

STATUS: ACCEPTED_LIMITED_PAPER; independently reviewed K1--K4.
Date: 2026-09-17. Isolated analytic research, base 76df4f76795069453bf6a12bddef48f4bcad0d8d.
Canonical production remains HOLD. FULL_V_SIGN and RH remain OPEN.
No positive mechanism has been selected for a new Proshka proof request.

## 1. Exact source and consumer

Keep the full density and the same logarithmic source:

    r(t)=sum_(k>=1)(4 pi^2 k^4 t-6 pi k^2) exp(-pi k^2 t), t>0,
    r(1/t)=t^(5/2)r(t),  M_r(s)=2xi(2s-2),
    Phi(x)=exp(5x/2)r(exp(2x)),
    q(x)=Phi(x)/Z,  Z=integral_R Phi(x)dx=xi(1/2)>0.

The change t=exp(2x) gives, for every complex z,

    F(z)=integral_R exp(izx)q(x)dx=xi(1/2+iz)/xi(1/2).       (1)

Evenness follows from the exact reciprocity. The full source bounds justify
all complex Fourier moments and differentiation. The target is still the
original V formed with f=Phi/||Phi||_2:

    V(x,y)=integral_0^infinity (2X+x+y)f(X+x)f(X+y)dX,
    sum_ij conjugate(c_i)V(x_i,x_j)c_j >=0

for every finite admissible family and all complex coefficients. Normalizing
q by its L1 integral in (1) does not redefine V. The previously accepted
full-sign transfer, not the paper below, identifies the full V question with RH.

## 2. Published input and its boundary

Primary: Konstantopoulos--Patie--Sarkar, *A new class of solutions to the van
Dantzig problem, the Lee--Yang property, and the Riemann hypothesis*, AIF
74(1) (2024), 377--421, https://doi.org/10.5802/aif.3600 .
PDF: https://aif.centre-mersenne.org/item/10.5802/aif.3600.pdf ; SHA256
05f75d661af5d94d64c5c66b6a9c1ee22a73d53e13c5afd8ceb7a76a5cf14a19.
Relevant pp396--397,416--417 were read; p397 was also visually inspected.

Theorem 4.4, using definition (4.14), supplies real zeros for

    J_Psi(z)=sum_(n>=0) (-1)^n z^(2n)/product_(k=1)^n Psi(k), (2)
    Psi(u)=u phi(u),  phi in B_P1.

Here B_P1 requires Bernstein--Pick structure and 1-separation: successive
entire-function zeros satisfy z_(k+1)<z_k-1; meromorphic zeros/poles satisfy
rho_k=z_k-1>z_(k+1). Ordinary real-axis positivity is insufficient.
This published theorem is an external input; its proof cites working
paper [25]. Section 4.1 leaves xi membership unresolved: "Since this question
does not seem straightforward". Theorem 4.1's weaker van Dantzig conclusion
and Proposition 4.7's growth comparison are not substitutes. We derive
coefficients from (1), without importing equations (4.15)--(4.18).

## 3. K1: the exact, fully fixed coefficient interface

Let mu_(2n)=integral_R x^(2n)q(x)dx, so mu_0=1 and every mu_(2n)>0.
Absolute convergence and evenness give

    F(z)=sum_(n>=0) (-1)^n a_n z^(2n),
    a_n=mu_(2n)/(2n)! >0.

If F=J_Psi, comparing neighboring coefficients NECESSARILY gives

    Psi(n)=a_(n-1)/a_n
          =(2n)(2n-1)mu_(2n-2)/mu_(2n), n>=1.             (3)

Conversely these values telescope in (2), giving precisely F, since its
power series is entire. For the sufficient subclass Psi(u)=u phi(u), the
required data are therefore

    phi(n)=b_n:=2(2n-1)mu_(2n-2)/mu_(2n), n>=1.           (4)

There is no free correction constant or independently adjustable sequence.
An independently constructed phi in B_P1 taking ALL values (4), together
with Theorem 4.4, would establish real zeros of F and hence RH. This is a
closed conditional implication. Existence of such a phi for actual q is
not established. No claim that this stronger sufficient condition is
necessary for RH is made.

## 4. K2: a genuine source property pays the first required inequality

The pinned Csordas--Varga input proves strict concavity of
ell(s)=log Phi(sqrt(s)) for s>0. Strict concavity, not an unproved assertion
ell''<0 everywhere, is used here. Write

    rho(s)=Phi(sqrt(s)),
    M(p)=integral_0^infinity s^(p-1)rho(s)ds, p>0,
    h(s)=-rho'(s)/rho(s).

Evenness, smoothness and positivity of Phi imply rho(0)>0 and bounded
rho' near zero. The full theta bounds control rho and rho' at infinity.
Since ell is differentiable and strictly concave, h is strictly increasing.
Also mu_(2n)=M(n+1/2)/Z, where Z=M(1/2). For u>1/2 set

    b(u)=4(u-1/2)M(u-1/2)/M(u+1/2).                     (5)

This agrees with b_n at u=n. Integration by parts, with both endpoints
zero, gives for p=u-1/2>0

    p M(p)=-integral s^p rho'(s)ds,
    b(u)=4 E_u h(S),
    dP_u(s)=s^(u-1/2)rho(s)ds/M(u+1/2).                  (6)

There is no discarded boundary: s^p rho(s) tends to zero at both endpoints.
Differentiation of this probability tilt is justified locally uniformly in
u>1/2 by the same bounds, including the additional |log s| factors. Thus

    b'(u)=4 Cov_u(h(S),log S)>0.                         (7)

For strictness use an independent copy S': twice the covariance equals
E[(h(S)-h(S'))(log S-log S')]. The integrand is strictly positive when
S!=S'; P_u has a positive density on (0,infinity). Consequently

    0<b_1<b_2<... .                                     (8)

Equivalently, for every n>=1,

    mu_(2n)^2 > [(2n-1)/(2n+1)]mu_(2n-2)mu_(2n+2).        (9)

This is a moment/Turan consequence of the already proved source concavity;
no novelty claim is made. It demonstrates exactly where that known property
works in this interface. It does NOT establish concavity of b, all higher
Bernstein signs, a Pick continuation, or 1-separation. The additive PF
property of r has not supplied any of those missing facts in this audit.
The probability integral (6) is an expectation of an increasing function;
it is not automatically a positive Levy measure for a Bernstein function.

## 5. K3: even a full Bernstein interpolation can fail the desired zero claim

Use the existing explicit non-theta control

    g0(x)=exp(-x^2)-(1/4)exp(-2x^2),
    a=1/(4 sqrt(2))=2^(-5/2),  Z0=sqrt(pi)(1-a).

The pinned two-shift intake already proves a negative four-node row of
its original full V. It is positive, even, rapidly decreasing, and strictly
log-concave after x=sqrt(s). Gaussian integration gives its normalized
moments and the exact values required by (4):

    mu^0_(2n)=(2n)!/[4^n n!] * (1-a 2^(-n))/(1-a),
    b^0_n=4(1-a 2^(1-n))/(1-a 2^(-n)).                   (10)

These interpolate by the explicit Bernstein function, for real u>=0,

    phi0(u)=4(1-2a 2^(-u))/(1-a 2^(-u))
           =phi0(0)+4 sum_(k>=1) a^k(1-exp(-k log(2)u)),
    phi0(0)=4(1-2a)/(1-a)>0.                             (11)

The total mass 4sum a^k is finite. Hence (11) is a genuine positive
Levy--Khintchine representation, with positive atoms at k log2, and all
Bernstein derivative signs hold. Nevertheless phi0 is NOT Pick: its
meromorphic continuation has genuine simple poles at

    u=-5/2+2pi i j/log2, j in Z,                         (12)

including poles in the upper half-plane. The numerator equals -1 at every
zero of the denominator, so none is removable. A Pick extension agreeing
on the positive axis would, by uniqueness of analytic continuation from a
neighborhood of that axis, encounter these nonreal poles.

The actual control Fourier function is

    F0(z)=[exp(-z^2/4)-a exp(-z^2/8)]/(1-a).

Its zeros satisfy z^2=-8log(a)-16pi i j. For j!=0 these are nonreal.
Thus replacing B_P1 by ordinary Bernstein interpolation in K1 is false,
even while K2 and every Bernstein derivative sign hold. This control does
not possess all theta hypotheses; it does not refute a theorem which
additionally uses the actual PF source and weighted reciprocity.

There is also no hidden application of Theorem 4.1 here. For
Psi0(u)=u phi0(u), direct twice differentiation yields

    Psi0''(u)=4 sum_(k>=1)a^k exp(-k log2 u)
                       [2k log2-u(k log2)^2]<0

whenever u>2/log2. A spectrally negative Levy exponent must be convex;
hence Psi0 is not in N_D. Passing an ordinary Bernstein test is weaker
than either of the relevant published hypotheses.

## 6. K4: one cannot fix this control merely by choosing another BF interpolant

If two Bernstein functions take the same values at every positive integer,
they coincide on (0,infinity). Here is a proof sufficient for this use.
Write phi(u)=A+B u+integral(1-exp(-ur))nu(dr), with the usual positive
Levy measure. For integer n>=1,

    phi(n+1)-phi(n)=B+integral exp(-nr)(1-exp(-r))nu(dr).

On t=exp(-r) in (0,1), let sigma be the finite measure obtained by pushing
forward exp(-r)(1-exp(-r))nu(dr), and put B mass at t=1. The above increments
are precisely its moments of orders n-1. Equality of every increment makes
the two finite measures equal: polynomials are dense in C([0,1]), so a
finite measure on [0,1] is determined by all its moments. Neither measure
has mass at t=0. Its atom at 1 determines B, and division by the strictly
positive weight t(1-t) on (0,1) recovers nu. Finally phi(1) determines A.
Thus the unique Bernstein interpolation of (10) is phi0. Since phi0 is not
Pick, that control admits no different Bernstein--Pick interpolation of
these SAME values. This argument is not a uniqueness claim for arbitrary
analytic interpolations.

## 7. Search receipt, diagnostic limit, and stopping condition

Three registered shelf queries preceded this external pass:
"van Dantzig self reciprocal Polya frequency";
"inversion invariant gamma convolution Mellin zeros";
"self reciprocal totally positive density characterization".
All returned INCOMPLETE because semantic-index freshness validation failed;
this does not assert no shelf hits. Existing joint-PF, dual, convolution,
reflection and sibling reports were read before selecting this primary.
Consensus was discovery only; journal formulas and the above own derivations
are the evidence. No new shared paper registration or index repair was run.

A finite diagnostic used 10 theta modes, x in [0,4], 65-digit arithmetic,
and the first 20 required b_n. It showed no violation of the tested finite
Bernstein difference signs. It has no certified tail/integration error and
is NOT a universal Bernstein theorem, a source-sign result, or evidence for
Pick membership. It is excluded from K1--K4 proofs.

Outcome: a closed conditional bridge (K1), an actual-source first property
(K2), and an exact obstruction to weakening the bridge (K3--K4).
The unpaid requirement remains a source-built B_P1 interpolation of (4),
or a different independently proved sufficient mechanism. The published
paper does not construct it for xi. Do not send Proshka a generic request
to prove 'the interpolation is positive' or treat Proposition 4.7's growth
match as payment. Before choosing this route, identify a concrete source
identity that can control the missing higher/complex conditions. No such
identity is supplied here; no new proof dispatch is justified by this audit.
CONSUMPTION: INCOMPLETE_NO_CONSUMABLE_TARGET.
No canonical admission, Lean proof, RH claim, or source-sign counter reset.

## Independent acceptance

Candidate SHA256: `5ece10af57e06d233cb501ae2ea6aff4ba4dacf4409ea0a76b1a75a49b1b4231`.
Review SHA256: `eab2271902100f359b5abe419c48e1d8a9380088e7a077ff2c9d7142b4477a0b`.
Verdict: `ACCEPT_LIMITED_KPS_INTERFACE_AND_BF_CONTROL`.
Reviewer `/root/pairzero_geometry_review` read the exact source pins and
audited K1--K4. Parent checks independently verified normalization,
endpoint control, covariance strictness, the explicit Bernstein control
and uniqueness of BF interpolation. Full checks are embedded in the paired
certificate. This accepts only the conditional interface, the stated source
moment inequality and the scoped obstruction to weakening the hypothesis.
It does not prove actual Bernstein--Pick membership, full V positivity or RH.
No canonical or Lean admission is claimed.
