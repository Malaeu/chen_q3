# Global Pick mechanism hunt: exact phase and string controls

Status: ACCEPTED_LIMITED_PAPER; independent review and parent check complete. Isolated analytic research only.
Source base: da556b66de0b840bcd5131fe32b74b35ad1652ec.
Exploratory intake: INCOMPLETE_NO_CONSUMABLE_TARGET; no canonical exact
Lean theorem/consumer edge is bound. No admission or RH/V sign claim.

## Return point and result

The exact full-source quotient is phi(u)=4N(u)/D(u)=4H(u-1)/H(u),
with the normalization and source pins in
BRIEF_2026-09-17_GLOBAL_PICK_MECHANISM_HUNT.md. Its global Pick property
would suffice for the already published conditional RH bridge. It is OPEN.

This bounded hunt found two concrete mechanisms and one false transfer.
Neither mechanism has yet been constructed from the actual theta source.
The new calculations below realize BOTH mechanisms exactly for the same
positive control, including its boundary energy. This is a mechanism check,
not progress on the sign of the theta quotient or of V.

## Search reconciliation and primary evidence

The four registered ask-shelf queries and receipts PICK_HUNT_ASK_1--4 are
retained in private staging. All report INCOMPLETE due to semantic-index
freshness; no absence theorem or index repair follows. Earlier PF/inversion
queries used different inputs. The existing hyperbolic-source and Gaussian
latent-source reports were reread; their scalar/latent positivity does not
identify this Mellin quotient. Three bounded external dictionaries led to:

1. Deng--Schilling, arXiv:1606.04610v2, printed p.2, Theorem and Remark 2;
   proofs pp.3--4. https://arxiv.org/pdf/1606.04610
   PDF SHA256 75ab07ee2f2dd43226cf7fab3deae0451d6ad951d78d534974cc1c4946b7b651.
   Quote, Remark 2: "all complete Bernstein functions have a representation
   of the form (1)". For measurable 0<=alpha<=1 on [0,1],
   P_alpha(u)=exp integral_0^1 (u-1)alpha(x)/(1+(u-1)x) dx
   is complete Bernstein; conversely phi(u)/phi(1) has this form if phi is
   complete Bernstein. Map u to the actual Mellin parameter, without shift;
   phi(1)>0 is proved. Existence of the exact source alpha is OPEN.
   Strength: verified mechanism, conditional application. The negative
   Gaussian control has upper-half-plane poles and cannot admit this alpha.
   We do not use the p.3 assertion of a zero limit for every step function:
   alpha=0 gives the constant 1. The representation theorem and direct
   phase argument below do not require that assertion.

2. Kwasnicki--Mucha, arXiv:1707.02475v1, Theorem 3.1 p.6 and (3.3) p.7.
   https://arxiv.org/pdf/1707.02475
   PDF SHA256 7456075b35759379459ddf4319b0ac8fe21a07d1f11846218246824389ed17a6.
   Quote, Theorem 3.1: "can be obtained in the above manner in a unique way."
   A fixed nonnegative string measure A, its equation v''=u v A and the
   prescribed terminal condition produce psi(u)=-v'(0). The response is
   complete Bernstein; the real-parameter solution minimizes the energy.
   Map the spectral parameter to our u and require psi(u)=4N(u)/D(u)
   identically. Both an independently constructed A and exact matching
   are OPEN for theta. The converse cannot construct a positive source
   device before its complete-Bernstein hypothesis is paid. The Gaussian
   control fails this response class. Strength: verified conditional mechanism.

3. Patie--Vaidyanathan, arXiv:1806.02644v2, (1.2) p.2 and Definition 2.1 p.3.
   https://arxiv.org/pdf/1806.02644
   PDF SHA256 4eb40f415abb402d0585916b2eaef5390fb67f10a96fe02e9c475e8453217355.
   Quote, p.2: "We call these the Berg-Urbanik semigroups". The explicit
   hypothesis in Definition 2.1 is ordinary Bernstein membership. It
   supplies a multiplicative semigroup with time-one moments
   product_(k=1)^n phi(k). Our old Abel law instead has moments
   n!/product_(k=1)^n phi(k); it is the complementary exponential-functional
   law, not automatically this semigroup. Neither positive old Abel mass nor
   its moment determinacy supplies the missing BF premise; even that premise
   would not supply Pick. The Gaussian control IS ordinary BF and so is not
   excluded. Strength: verified source, INAPPLICABLE as the needed upgrade.

The quoted source statements were checked against rendered PDF pages. This
is bounded source verification, not a claim to have surveyed all literature.

## M1. Why the upper bound on phase density matters

Write z=a+ib, b>0. The integrand in log P_alpha has imaginary part

  b alpha(x)/|1+(z-1)x|^2.

The integral with alpha=1 is log z, with the branch real at z=1.
Consequently 0<=Im log P_alpha(z)<=arg z<pi. Exponentiation stays in the
closed upper half-plane. Bounded alpha also gives local uniform analyticity
on the slit plane. This controls the whole phase before exponentiation.
Positivity of alpha alone is insufficient: alpha=2 gives P_alpha(z)=z^2,
whose imaginary part is negative at z=-1+i.

For the already pinned positive control

  H_c(u) proportional to (u+2)(u+3),
  phi_c(u)=4(u+1)/(u+3), phi_c(1)=2,

take alpha_c=1_(1/4,1/2). Direct integration gives

  integral_(1/4)^(1/2) (u-1)/(1+(u-1)x) dx
    = log[2(u+1)/(u+3)].

Thus the exact control has the required bounded density. Equivalently the
half-line phase density eta(t)=alpha(1/(1+t)) is 1_(1,3). No unit-gap
assumption on the surviving zero -1 and pole -3 was inserted.

## M2. An explicit positive string with the SAME control response

This is a new elementary calculation for the control, not an assertion
about the actual theta source. Put R=3/4, a=1/4, A=2 delta_a.
Let v_z be continuous and linear on [0,a] and [a,R], with v_z(0)=1,
v_z(R)=0, and derivative jump

  v'_z(a+)-v'_z(a-)=2z v_z(a).

Writing w=v_z(a), the left and right slopes are 4(w-1) and -2w.
The jump equation is 4-6w=2zw, hence w=2/(z+3). The input response is

  -v'_z(0)=4(1-w)=4(z+1)/(z+3)=phi_c(z).

For real u>=0 and any absolutely continuous complex v with the same two
boundary values, define

  E_u[v]=integral_0^R |v'|^2 ds+2u|v(a)|^2.

Set g=v-v_u. Piecewise integration by parts and the derivative jump give

  integral v'_u conjugate(g') ds = -2u v_u(a)conjugate(g(a)),

since g vanishes at both endpoints. The ENTIRE mixed term cancels and

  E_u[v]=E_u[v_u]+E_u[g],    E_u[v_u]=phi_c(u).

The endpoint at R and jump at a are essential parts of this identity.
For complex z off the pole, the same integration by parts with v_z gives

  phi_c(z)=integral_0^R |v'_z|^2 ds+2z|v_z(a)|^2,
  Im phi_c(z)=2 Im z |v_z(a)|^2=8 Im z/|z+3|^2.

This exhibits exactly how one fixed positive device controls every upper
half-plane parameter. It does not identify its energy with our physical V.
For theta, matching the quotient would feed the separately accepted Pick
consumer; direct equality E=V is not asserted.

## M3. A source-level diagnostic that does not assume unknown zeros

Let L(u)=log(phi(u)/phi(1)), real u>0. Under the M1 representation,
differentiation on compact positive u intervals yields, for every n>=1,

  (-1)^(n-1) L^(n)(u)/n!
    = integral_0^1 x^(n-1)alpha(x)/(1+(u-1)x)^(n+1) dx,
  0 <= (-1)^(n-1) L^(n)(u)/n! <= 1/(n u^n).

The upper bound follows by alpha<=1 and differentiating log u. These are
necessary conditions only; a finite list cannot prove the representation.
Use the ACTUAL full source and the two normalized positive densities

  dP_D,u(s)=s^(u-1/2)rho(s) ds/D(u),
  dP_N,u(s)=s^(u-1/2)(-rho'(s)) ds/N(u).

Full-source endpoint and tail bounds justify two logarithmic derivatives
for every real u>0. Therefore

  L'(u)=E_N,u log s-E_D,u log s,
  L''(u)=Var_N,u(log s)-Var_D,u(log s).

In particular the n=2 condition becomes the concrete source comparison

  0 <= Var_D,u(log s)-Var_N,u(log s) <= 1/u^2.             (VAR)

The published strict increase pays L'>0; it does NOT pay either bound in
(VAR). No variance ordering for the actual theta source is proved here.
This is not the previous unsigned formula for phi''; it is an exact
necessary condition on log phi, with a stated source-level failure test.

## Hypotheses, decision and bounded next action

PROVED: exact source/quotient, normalization, old Abel law, H continuation
and growth, direct conditional Pick consumer. PROVED FOR CONTROL ONLY:
alpha_c, A=2 delta_(1/4), exact response, full boundary compensation.
OPEN FOR THETA: bounded phase density; positive string with exact response;
global Pick; (VAR). FALSE AS A GENERAL RULE: positive phase weights alone
or ordinary BF/positive radial law force Pick. INAPPLICABLE: reversing the
Berg--Urbanik construction without its premises.

No proof request should merely ask Proshka to construct the guaranteed
string or choose alpha: those existence assertions encode the unpaid sign.
The next bounded mathematical test is (VAR) on the full theta source,
using the two explicit measures together. A strict violation excludes this
sufficient Pick route, not RH or V positivity. A proof is only a necessary
filter. If the source identities give neither ordering nor a violation,
stop this diagnostic and preserve the exact comparison; do not automatically
generate an infinite queue of higher derivative tests or split its terms.

This hunt changes the description and supplies worked mechanisms. It does
not change the mathematical sign frontier or reset any no-delta counter.
Canonical production, goal status, phase/chat and previous verdicts remain
unchanged. No new Proshka proof job was sent during the hunt.

## M4. Completed bounded variance-transfer test: strict log concavity does not suffice

Status: ACCEPTED_LIMITED_PAPER. Companion to the fixed-hash
GLOBAL_PICK_MECHANISM_CANDIDATE.md, M3. This is NOT the full theta source.

For epsilon>0 take

  rho_e(s)=exp(-s-epsilon*s^3), s>=0,
  q_e(x)=C_e exp(-x^2-epsilon*x^6), x real, C_e>0 normalized.

The constant cancels from the quotient. These profiles are positive, even
in x, strictly decreasing for x>0, smooth, rapidly decreasing, and
(log rho_e)''(s)=-6 epsilon s<0 for s>0. We make no claim that this source
has the actual theta additive-PF and reciprocal structure jointly.

Put p=u+1/2 and

  D_e(u)=integral_0^infinity s^(p-1)rho_e(s) ds,
  N_e(u)=integral_0^infinity s^(p-1)(1+3 epsilon s^2)rho_e(s) ds,
  phi_e=4N_e/D_e,    L_e(u)=log(phi_e(u)/phi_e(1)).

On a fixed compact interval around u=1, the two u derivatives and two
one-sided epsilon derivatives at epsilon>=0 are dominated by finite sums
of s^(p-1+j)|log s|^k exp(-s), j<=8, k<=2. Use a compact interval p bounded
strictly above zero and the larger/smaller endpoint powers for s>=1/s<=1.
Consequently the following first-order expansions have O(epsilon^2)
remainders in C^2 as functions of u on a smaller fixed interval:

  D_e(u)=Gamma(p)-epsilon Gamma(p+3)+O_C2(epsilon^2),
  N_e(u)=Gamma(p)+epsilon[3Gamma(p+2)-Gamma(p+3)]
           +O_C2(epsilon^2).

Denominators stay uniformly away from zero there for sufficiently small
epsilon. Division and the smooth logarithm preserve the C^2 expansions:

  phi_e(u)=4[1+3 epsilon p(p+1)+O_C2(epsilon^2)],
  L_e''(1)=6 epsilon+O(epsilon^2)>0

for every sufficiently small positive epsilon. The variance identity from
M3 therefore gives

  Var_D,e,1(log s)-Var_N,e,1(log s)
       =-6 epsilon+O(epsilon^2)<0.

This violates (VAR), hence excludes global Pick / complete Bernstein for
these controls. Also phi_e''(1)=24 epsilon+O(epsilon^2)>0, independently
excluding ordinary Bernstein. No finite numerical sample is used.

The test invalidates the generic transfer from squared-coordinate strict
log concavity to the necessary variance ordering. It does not decide (VAR)
for theta, does not give a negative theta V, and does not refute RH. The
remaining source-specific input must use additional structure; neither
the exact string for the rational control nor the phase theorem supplies it.
Do not proceed automatically to an infinite hierarchy of derivative tests.

## Independent acceptance

Verdict: `ACCEPT_GLOBAL_PICK_MECHANISM_CONTROLS_AND_VARIANCE_OBSTRUCTION_ONLY`.
Review SHA256: `fa0dabcffe4bbab4135856f083fc7b0a3a592992eeb4be6c337550df981a0525`. Main and companion candidate hashes,
full independent review and parent check are embedded in the paired
certificate. M4 executes the generic concavity-to-variance test and rejects
that transfer analytically. The actual theta variance comparison remains
OPEN. These are mechanism and control results only; no actual-source Pick,
full-V sign, RH conclusion, Lean admission or counter reset follows.
