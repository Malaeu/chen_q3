# A source-preservation obstruction for Gaussian positive-product reconstruction

Status: ACCEPTED_LIMITED_PAPER; independent review and parent check complete.
Base: e4cac72033652ff8685cae3195a68124285205ed.
Scope: bounded continuation of the accepted source-preservation hunt;
original full V, actual global Pick, and RH remain OPEN.

## Exact question

The previous plus sibling has only real Fourier zeros, with a proof by
positive quadratic factors times a Gaussian followed by a locally uniform
Fourier limit. But that sibling is not the fixed theta source q. Can tuning
all positive factors, all their rates, and the Gaussian weight recover q
as a positive pointwise limit? This note tests that reconstruction mechanism,
not the missing VAR comparison and not an abstract existence theorem.

The answer is no for the class below, even if a quartic exponential factor
is added. The obstruction concerns convergence of the source densities.
It does not rule out Fourier-only approximations without such convergence,
arbitrary changes of variable, positive sums, or other constructions.

## Source and exact inputs

Keep the complete source from the accepted reports:

  q(x)=Phi(x)/Z, Z=xi(1/2)>0, rho(s)=q(sqrt(s)), s>0,
  Phi(x)=exp(5x/2)r(exp(2x)),
  L_r(v)=product_(n>=1)(1+v/(pi*n^2))^(-2).

The physical f=Phi/||Phi||_2 and the original full V are unchanged;
q is only the probability normalization used to describe the source.
For x>=0 the full theta factorization is

  q(x)=(4pi^2/Z) exp(9x/2-pi exp(2x)) Hcal(exp(2x)),
  Hcal(t)=sum_(n>=1)(n^4-3n^2/(2pi t))exp(-pi(n^2-1)t).

Accepted full-source estimates give Hcal bounded above and bounded away
from zero on t>=1 and |Hcal(t)-1|<=C_H/t. Thus, with ell=log rho,

  ell(s)=-pi exp(2sqrt(s))+(9/2)sqrt(s)+O(1), s->infinity.       (R1)

No theta term is omitted in this identity and its bound. The O(1) is never
differentiated. This follows directly from PV5 and the accepted PICKVAR
intake, rather than a new first-mode replacement.

## R2. A closed invariant of the proposed reconstruction class

Let C2 consist of positive functions on s>0 of the form

  rho_j(s)=A_j exp(-a_j s^2-b_j s)
                 product_(k=1)^m_j (s+lambda_jk)^(alpha_jk),   (R2)

where A_j>0, lambda_jk>=0, alpha_jk>=0, m_j is finite, and a_j,b_j
are real. Real powers here have their positive real meaning on s>0.
No bound is imposed on parameters, exponents, or m_j. This is deliberately
an enlarged comparison class; no real-Fourier-zero theorem is claimed for
all its members. Integrability is not needed for its invariant.

For h>0 define Delta_h L(s)=L(s+h)-L(s). Polynomial terms of degree at most
two vanish in Delta_h^3, and

  (log rho_j)'''(s)=2 sum_k alpha_jk/(s+lambda_jk)^3 >=0.

By three applications of the fundamental theorem of calculus,

  Delta_h^3 log rho_j(s)
   =integral_[0,h]^3 (log rho_j)'''(s+t1+t2+t3)dt1 dt2 dt3 >=0. (R3)

Suppose rho_j(s)->rho_*(s)>0 at every point of (0,infinity). Fix any s,h>0.
The four logarithms in R3 converge, so

  Delta_h^3 log rho_*(s)>=0.                                  (R4)

No derivative convergence, uniform tail estimate, or uniform parameter
bound is required. Local uniform convergence of positive densities is a
special case. The same conclusion holds for any positive limit of an
infinite-product member approximated by its finite products: every such
member already satisfies R4, so a further pointwise limit does too.

The previous sibling

  w_b^+(x)=exp(-b x^2) product_(n>=1)(1+x^2/(pi*n^2))^2

belongs to this closure after s=x^2, a=0, alpha=2. Its product converges on
bounded positive s because sum 1/n^2<infinity. Normalizing mass changes only
log A. Linear exponential canonical-factor compensators are absorbed in b.

## R3. The complete theta source violates the invariant

In R4 take s=R and h=R. R1 gives

  exp(-4sqrt(R)) [ell(4R)-3ell(3R)+3ell(2R)-ell(R)] -> -pi.     (R5)

Indeed the ell(4R) leading term is -pi exp(4sqrt(R)). Every other leading
exponential is exp(2sqrt(k)*sqrt(R)), k=1,2,3, and becomes negligible after
multiplication by exp(-4sqrt(R)). The remaining four square-root terms are
O(sqrt(R)) and the four full-source logarithmic errors are O(1). All vanish
under the same scaling. This uses four values of a controlled full-source
asymptotic, not its derivatives and not an interchange of infinite limits.

Consequently there exists a finite R0 such that for every R>=R0,

  Delta_R^3 ell(R)<0.                                        (R6)

Fix one such R before taking any approximation limit. Equations R4 and R6
contradict each other. Therefore the fixed actual rho cannot be a positive
pointwise limit of C2, and in particular cannot be a locally uniform limit
of that class. Failure occurs already on those four fixed positive nodes.
This is an analytic exclusion of a reconstruction class, not merely failure
to tune one Gaussian parameter or one finite product.

## R4. Why the obstruction is not a test for real Fourier zeros

For a concrete control take the OTHER source w6(x)=exp(-x^6), with
rho6(s)=exp(-s^3). It is positive, even, and integrable with an entire Fourier
transform, but

  Delta_h^3 log rho6(s)=-6h^3<0.

Thus it too lies outside the pointwise closure of C2. Nevertheless its
Fourier transform has only real zeros, as the following named-theorem
argument verifies. This establishes that R4 is a property of our proposed
construction, not a necessary property of every successful source.

In the initial domain Re u>-1/2, substitution y=s^3 gives

  D6(u)=integral_0^infinity s^(u-1/2)exp(-s^3)ds
       =(1/3)Gamma((u+1/2)/3).

Set H6(u)=D6(u)/Gamma(u+1/2). Gauss triplication, DLMF 5.5.6,
https://dlmf.nist.gov/5.5.E6, yields its entire continuation

  H6(u)=2pi*3^(-u-1)
           /[Gamma(u/3+1/2) Gamma(u/3+5/6)].                 (R7)

The reciprocal Gamma products show H6 is real entire of order at most one,
positive at real u>=0, and has exactly the simple negative zeros

  u=-3n-3/2 and u=-3n-5/2, n=0,1,2,... .

Use the same classical Laguerre coefficient-transform theorem as the
accepted DIRECT_PICK_BRIDGE R2: a real entire function of order less than
two having only negative real zeros has exponential coefficient transform
with only negative real zeros. Primary statement: Baricz--Singh, *Zeros of
some special entire functions*, arXiv:1702.00626v2, Lemma 1, printed p.2,
https://arxiv.org/pdf/1702.00626v2. No new general preservation theorem is
assumed beyond that already named project input.

For clarity, let mu_(2n)=integral_R x^(2n)w6(x)dx=D6(n). Since
Gamma(n+1/2)=(2n)!sqrt(pi)/(4^n n!),

  G6(w)=sum_(n>=0) H6(n)w^n/n!,
  F6(z)=integral_R exp(izx)w6(x)dx=sqrt(pi)*G6(-z^2/4).       (R8)

The entire series and integration are justified on every compact z-set
by exp(R|x|-x^6). The named theorem applied to H6 implies every G6 zero
is negative real, and G6(0)>0. Hence every F6 zero is real. Normalizing
w6 by its positive mass changes none of the conclusions. This control is
not the original theta source, not an original negative V witness, and not
a proof that arbitrary mixtures of such seeds preserve real zeros.

## Decision and the role of the arithmetic source

The plus-sibling proof cannot be converted to a proof for q just by tuning
its positive quadratic factors, allowing any number of them, changing their
rates, adding a quartic exponential factor, or taking positive pointwise
source limits. The proposed operation fails a closed invariant of its own
outputs. Stop that operation here; do not delegate its impossible source
matching to Proshka.

The exclusion uses the exact theta tail with full errors controlled. It does
not use additive PF-infinity jointly with reciprocity and does not extract
a new property of primes or a new lower bound for the original energy.
The successful w6 control emphasizes that changing the construction is
possible in principle, while no source-preserving map to q is supplied here.
It is not permission to promote another model source to an RH proof.

Next source mechanism must specify an exact operation on the fixed q (or an
exactly equivalent transform) and a preservation theorem whose hypotheses
are paid. Merely choosing another positive seed or an unknown multiplier
would leave the same missing preservation proof.

ORIGINAL_FULL_V: OPEN. ACTUAL_PICK: OPEN. RH: OPEN.
ORIGINAL_NEGATIVE_V_WITNESS: NONE. NEW_PROOF_REQUEST: false.
CANONICAL_ADMISSION: false. SOURCE_SIGN_COUNTER_RESET: false.
CONSUMPTION: INCOMPLETE_NO_CONSUMABLE_TARGET. LEAN_RUNS: 0.

## Independent acceptance

Verdict: ACCEPT_C2_RECONSTRUCTION_OBSTRUCTION_AND_W6_CONTROL_ONLY.
Candidate SHA256: 9bc6eca8ddc0b5686921364eed293032d7ec5d819823c40a75c795bd951cbb9b.
Complete review SHA256: 01e0f5469ba8a6e02274b63ed2efa1d0992842f39261706e46dc9a75b3d40a9a.
Complete parent check SHA256: 79438f477fc8ff9a9c193b9ea5815e9fd104a4ed1ef86cf0439891f342a73c30.
The certificate binds full inputs and embeds both checks. No formula correction
was required. The parent read the entire independent review before publication.
This accepts only the stated reconstruction-class obstruction and the separate
control. It proves no sign for original V and no assertion of RH.
