# Closing the Fourier-only loophole for the positive-product reconstruction

Status: ACCEPTED_LIMITED_PAPER; independent review and parent check complete.
Base: b8d18da4d323e9be3f50b75078308310e6ca1f12.
Scope: a bounded completion of the source-reconstruction preflight.
Actual global Pick, original full V and RH remain OPEN.

## Question and accepted source input

The previous reconstruction report excludes positive pointwise convergence
of the Gaussian/quartic positive-product sources to the actual theta q.
Its proof alone left Fourier-only convergence unexamined. A real-zero proof
by locally uniform entire Fourier limits would need precisely such convergence.
We now test this remaining possibility for normalized nonnegative sources.

The actual q=Phi/xi(1/2) is the same positive even probability density,
rho(s)=q(sqrt(s)), s>0. The previous independently accepted report proves

  exp(-4sqrt(R))*Delta_R^3 log rho(R) -> -pi, R->infinity,     (F1)

where Delta_h^3 L(s)=L(s+3h)-3L(s+2h)+3L(s+h)-L(s).
Its full-source theta errors and finite-node proof are reused unchanged.
The physical f=Phi/||Phi||_2 and original V are not modified here.

## F2. Approximation class and its two invariants

Consider any sequence of nonnegative even probability densities q_j on R,
with rho_j(s)=q_j(sqrt(s)) positive and continuous for s>0, satisfying

  log rho_j is concave on (0,infinity),
  Delta_h^3 log rho_j(s)>=0 for every s,h>0.                  (F2)

This class includes every mass-normalized integrable finite product

  q_j(x)=A_j exp(-a_j x^4-b_j x^2)
                product_k (x^2+lambda_jk)^(alpha_jk),        (F3)

where A_j>0, lambda_jk>=0, alpha_jk>=0. Positivity is required only away
from x=0; its value at that one point is immaterial to the probability law.
Integrability forces a_j>=0: a_j<0 makes the tail grow like exp(|a_j|x^4)
times a nonnegative power. If a_j=0, integrability also forces b_j>0.
For all integrable cases

  (log rho_j)''(s)=-2a_j-sum_k alpha_jk/(s+lambda_jk)^2<=0,
  (log rho_j)'''(s)=2sum_k alpha_jk/(s+lambda_jk)^3>=0.

Thus F2 follows exactly. The number of factors and their parameters may all
vary without a common bound. Positive continuous pointwise limits of these
profiles also inherit both finite-value invariants, whenever the resulting
q_j is integrable and is normalized by its positive mass. This includes the
previous convergent Gaussian*sinh-product sibling. We do not claim every
positive pointwise limit of the enlarged NONintegrable C2 comparison class
has these two properties; F2 is the exact entrance used in this note.

## F3. Real-axis Fourier convergence forces local measure convergence

Let F_j(t)=integral_R exp(itx)q_j(x)dx and let F be the Fourier transform of
the original q. Suppose, for contradiction, that

  F_j(t)->F(t) for every real t.                             (F4)

All |F_j(t)|<=1. For any real or complex test psi in C_c^infinity(R), Fourier
inversion with hat psi(t)=integral exp(-itx)psi(x)dx gives

  integral psi(x)q_j(x)dx=(1/(2pi))integral hat psi(t)F_j(t)dt.

The test transform is integrable, so Fubini and dominated convergence give
convergence to the same expression for q. No exponential-moment or derivative
convergence is needed, and no assertion of source convergence is assumed.

Now choose phi in C_c^infinity((0,infinity)), and set
psi(x)=|x|phi(x^2). It is smooth with compact support on R: it vanishes on
a neighborhood of zero, where the absolute value would otherwise matter.
Evenness and s=x^2 give exactly, without a missing factor of two,

  integral_R psi(x)q_j(x)dx=integral_0^infinity phi(s)rho_j(s)ds.

Hence the measures rho_j(s)ds converge against all such smooth compact tests
to rho(s)ds. These measures need not have uniformly bounded total mass on
the whole half-line; only local bounds will be used.

## F4. Elementary local stability lemma for log-concave densities

Lemma. Let p_j>0 be continuous on an open interval I, with log p_j concave.
If p_j(s)ds converges against smooth compact tests on I to p(s)ds, where
p>0 is continuous, then p_j->p locally uniformly on I.

Proof. Fix a compact interval K strictly inside I. Choose two disjoint
closed intervals L and R strictly to the left and right of K, both inside I.
Choose nonnegative smooth test functions of nonzero p-integral supported
inside L and R. Test convergence shows that for all sufficiently large j
there are u_j in L and v_j in R with p_j(u_j),p_j(v_j)>=c>0, uniformly in j.
Otherwise the corresponding test integral could not have its positive lower
bound. Concavity of log p_j gives p_j>=c between u_j and v_j, in particular
on a fixed larger interval [a,b] whose interior contains K and which lies
strictly between L and R.

A nonnegative smooth compact test which is >=1 on [a,b] gives a uniform
local mass bound integral_a^b p_j<=C. For x in [a,b] put M=p_j(x)>=c, and
choose the farther endpoint y in {a,b}; |x-y|>=d=(b-a)/2 and p_j(y)>=c.
Along that segment log concavity implies the geometric interpolation bound,
so for M>c

  C>=integral_[x,y] p_j(s)ds
    >=d*integral_0^1 M^t c^(1-t)dt
     =d*(M-c)/log(M/c).                                    (F5)

For M=c the continuous limiting value is d*c. Since the right side tends
to infinity with M, this bounds M uniformly. Therefore log p_j is uniformly
bounded above and below on [a,b]. Secant-slope inequalities for concave
functions now give a uniform Lipschitz bound on K (or on a slightly larger
compact interval still inside (a,b)).

Arzela--Ascoli gives, from every subsequence, a further subsequence converging
uniformly on K in logarithm. Testing inside K identifies its continuous
positive exponential with p, hence also at endpoints by continuity. Thus
every subsequential limit is log p, and the whole sequence converges uniformly
on K. For a one-point compact set use a containing nondegenerate interval.
The choice of K was arbitrary. This proves the lemma. There is no use of
uniform global moments, a common derivative bound supplied by a model,
or normalization of p_j on the entire interval.                         QED.

## F5. Contradiction and complete scope of the exclusion

Apply F4 with p_j=rho_j and p=rho on I=(0,infinity), using the local measure
convergence proved in F3. Then rho_j->rho locally uniformly. Since rho>0,
the logarithms converge at every fixed four-node configuration. The second
invariant in F2 passes to the limit and forces

  Delta_h^3 log rho(s)>=0 for every s,h>0.

This contradicts F1 at any one sufficiently large fixed R, s=h=R.
Consequently no sequence in F2 has Fourier transforms converging to the
actual F even pointwise on the whole real axis. In particular it cannot
converge locally uniformly as entire functions, as required by the proposed
Laguerre--Polya Fourier closure mechanism. No real-zero assumption on the
approximating F_j was used, so adding that assumption cannot avoid this
obstruction.

This strengthens the PREVIOUS report's scope: its R1--R8 alone did not
settle Fourier-only limits; F3--F5 here supply the missing local-stability
argument for normalized nonnegative sources satisfying both F2 invariants.
It does not exclude signed approximating sources, positive sums that lose
log concavity, other seed classes, other maps, or unrelated Fourier
approximations. None of those is asserted to preserve real zeros here.

The earlier exp(-x^6) control still separates this construction obstruction
from real Fourier zeros in general: its squared profile has negative third
log differences and hence does not satisfy F2, while the named Laguerre
argument proves its Fourier zeros real. This is not the original q.

The result closes the remaining Fourier-closure escape for the stated
positive-product mechanism. Stop tuning this class, on either the source
or Fourier side. It supplies no new arithmetic positivity mechanism and
uses no new property of primes; actual Pick, full V and RH remain OPEN.
NEW_PROOF_REQUEST: false. ORIGINAL_NEGATIVE_V_WITNESS: NONE.
CANONICAL_ADMISSION: false. SOURCE_SIGN_COUNTER_RESET: false.
CONSUMPTION: INCOMPLETE_NO_CONSUMABLE_TARGET. LEAN_RUNS: 0.

## Independent acceptance

Verdict: ACCEPT_NORMALIZED_FOURIER_CLOSURE_OBSTRUCTION_ONLY.
Candidate SHA256: e0357a55d5f32805bcc87f673f5a20889a71ff77bd74f436443058490d7e7e94.
Complete review SHA256: 0976f476e6c493ff2de6dda5988be2e08d7e265272eab31cb4ddbd9c1171fc4d.
Complete parent check SHA256: 8ab47d0cc6ef9c835469b42cce6ad883c298cca7122fc65a86a38129d12cd774.
The certificate binds full inputs and embeds both checks. No formula correction
was required. The parent read the entire independent review before publication.
This accepts only the stated positive-source Fourier closure obstruction. It proves no sign for original V and no assertion of RH.
