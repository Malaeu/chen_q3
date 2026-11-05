# What the positive scattering phase actually represents

Status: ACCEPTED_LIMITED_PAPER; independent review and parent check complete.
Base: 54f753cbd9e01902c3fc9f4b86f22c7053ba0e8f.
Scope: complete the one source-functional interface left by the accepted
scalar-centering audit. Original full V, the RH goal, canonical HOLD,
phase and source-sign counters remain unchanged.

The previous goal turn completed publication and native terminal Proshka
acknowledgement of the constructive scalar transport. It was PROGRESS for
the route audit, not a proof of the original sign. No proof job is pending.
This candidate settles the pinned private Poisson-damping conjecture and
checks whether its energy gives a lower bound for the original form.

**Claim for review.** The pole-corrected scattering phase gives exactly the
complete Weil functional after damping each correlation by exp(-|u|/2).
This holds for every complex compact smooth signal, with the cusp, all
prime powers, both completed-function poles and the archimedean constant
retained. The undamped-minus-damped correction has BOTH signs on actual
smooth tests. Thus the damped positive energy cannot be identified with
the original Q, and the correction cannot simply be declared nonnegative.
No sign or negative witness for original Q or V is claimed.

## P0. Exact source, conventions and named inputs

Use the meromorphic completed function Lambda(s)=pi^(-s/2)Gamma(s/2)zeta(s)
and the entire xi(s)=s(s-1)Lambda(s)/2. The actual response is

    m(v)=Lambda(v)/Lambda(1+v)
        =((v+1)/(v-1)) xi(v)/xi(1+v).

Set L(v)=xi(1/2+v), l=L'/L. L is even and real on R. All zeros below are
the actual nontrivial zeta zeros rho=beta+i gamma, repeated by multiplicity.
The unconditional fact 0<beta<1, not beta=1/2, is used.

For psi in C_c^infinity(R;C), set

    k(u)=integral psi(y+u)conjugate(psi(y))dy,
    hat psi(t)=integral psi(u)exp(i t u)du,
    Z(h)=sum_rho integral h(u)exp((rho-1/2)u)du.

Then hat k(t)=|hat psi(t)|^2 and k(-u)=conjugate(k(u)). The earlier accepted
full-sign transfer fixes Q(psi)=Z(k) and its all-test equivalence with the
full original V sign; this does not identify numerical values of E below
with a finite V family. Its SHA256 is
1e296a504631b58beb7863f4c7f36174bd08876cfc7093febfe00cc8306a5282.

The accepted scalar-centering report SHA256
aa9075413850f4062dc9fec86257188abdbd7e93ef189be4e6ea4e47793a9653
establishes the full complex Mellin square transport. It remains paid here.
The modular source/cutoff report SHA256
59376eb8b2c4129d9747e679ca2d94d06be4390837175c99afedea93224103c5
fixes the source m and the four-term Maass-Selberg formula.

Primary named inputs:
- [DLMF 25.4](https://dlmf.nist.gov/25.4), (25.4.3)-(25.4.4), fixes xi
  and its functional equation.
- [DLMF 25.10(i)](https://dlmf.nist.gov/25.10#i), the known open critical
  strip and both zero symmetries, without RH.
- [Suzuki, arXiv:2301.00421v3](https://arxiv.org/html/2301.00421v3),
  equation (3.3) and the all-test Weil criterion in the introduction.
  Downloaded HTML SHA256 a1ae9e997fcd21d712bd90c73280831addec246f647b4c1b35f9b20d57326c4c.
  Only the explicit formula is imported; no conditional Hilbert-space
  isometry is used.
- [Goldfeld, Exploring.pdf](https://www.math.columbia.edu/~goldfeld/Exploring.pdf),
  Theorem 4.1 and Lemma 4.2, pp.8-9. PDF SHA256
  da2ce5e958da27fb20f17b1cc0cbff4f17c24e28efa76590f47aba7d5d4f0209.
  Only the previously normalized full norm formula is used.

Classical analytic background: Jensen's formula, Hadamard factorization
for finite-order entire functions, Fourier inversion for the elementary
Poisson kernel, smooth mollification, and Lebesgue convergence theorems.
The order/growth and cusp hypotheses are checked below. No full printed
Wong arithmetic RHS is imported.

## P1. Exact phase and elementary pole term

The response, with the entire rather than meromorphic L, is

    m(v)=((v+1)/(v-1)) L(v-1/2)/L(v+1/2).

Oddness and real symmetry of l give
l(-1/2+it)=-conjugate(l(1/2+it)). Logarithmic differentiation, without any
choice of logarithm branch, yields

    m'(it)/m(it)=2/(1+t^2)-2 Re l(1/2+it).

Consequently define the REAL pole-corrected phase density

    P(t):=2/(1+t^2)-m'(it)/m(it)
         =2 Re xi'(1+it)/xi(1+it).                         (P1)

The removable value m(0)=-1 is used. xi(1) is nonzero, so (P1) holds
continuously at t=0 as well. The rational term comes from the actual
elementary zero/pole at v=-1,1; dropping it changes the energy.

## P2. The positive density uses only the known zero strip

For completeness, the accepted full-source bound
|Phi(x)|<=C exp(-c exp(2|x|)) gives

    L(v)=integral Phi(x)exp(vx)dx,
    log max_(|v|<=R)|L(v)| <= C1 R log(R+2)+C2.

The integral identity follows from the previously proved Mellin identity
and analytic continuation. The bound follows by the substitution y=e^(2x)
in the positive half-line majorant; Gamma(R/2)c^(-R/2) is an upper bound
up to constants for R>=2. L(0)>0 by positivity of Phi. Jensen's formula
now bounds the zero count in |v|<=T by O(T log(T+2)); in particular the
sum of |lambda|^-2 over zeros lambda=rho-1/2 converges.

Hadamard factorization, paired using lambda -> -lambda, gives

    L(v)=L(0) product_{one representative of each +/- pair}
                         (1-v^2/lambda^2).

Indeed the genus-one exponential factors cancel inside each pair, and
the possible exponential exp(bv) has b=L'(0)/L(0)=0 by evenness.
There is no zero at 0. Multiplicities are retained. The product and its
logarithmic derivative converge locally off zeros; paired derivative
terms are 1/(v-lambda)+1/(v+lambda)=O_v(|lambda|^-2).
On Re v=1/2 the real parts of EVERY unpaired summand are positive, so
taking real parts permits an absolutely convergent unpaired sum:

    P(t)=2 sum_rho (1-beta)/((1-beta)^2+(t-gamma)^2)>0.      (P2)

Local uniform convergence follows from the same paired bounds, or directly
from |gamma|^-2 real-part bounds on each fixed compact t-interval. Finitely
many remaining terms have strictly positive widths 1-beta. This covers
t=0 and proves that no constant has been lost.

Crucially, each width is positive for EVERY 0<beta<1. Nothing in (P2)
forces beta=1/2. This is precisely the source property paying this energy.

## P3. Fourier inversion with finite total energy

Put a_rho=1-beta, so 0<a_rho<1. Direct integration gives

    integral exp(-a|u|)exp(i(t-gamma)u)du
                     =2a/(a^2+(t-gamma)^2).

For any Schwartz F on R, uniformly in 0<a<1 and |gamma|>=2,

    integral [2a/(a^2+(t-gamma)^2)] |F(t)|dt
                     <= C_F/(1+gamma^2).                 (P3.1)

To see this split |t-gamma|<=|gamma|/2 and its complement. In the first
region use Schwartz decay at |t|>=|gamma|/2 and the full kernel mass 2pi.
In the second use denominator >=gamma^2/4, a<=1 and ||F||_1.
The finitely many small gamma contribute finite terms with the same
kernel mass. Jensen's count in P2 makes these bounds summable.

Thus for F=hat k=|hat psi|^2, Tonelli and Fourier inversion give a finite
strictly positive value for nonzero psi:

    E(psi):=(1/(2pi)) integral P(t)|hat psi(t)|^2 dt
      =sum_rho integral k(u)exp(-(1-beta)|u|)exp(i gamma u)du
      >=0.                                                (P3.2)

Each summand is nonnegative by its Poisson-kernel representation, although
its oscillating u-integrand need not be nonnegative. Absolute convergence
was proved before exchanging the entire sum and the spectral integral.
The assertion also holds for arbitrary compact smooth k in place of an
autocorrelation as a linear identity, using (P3.1) with F=hat k.

## P4. The whole centered functional, including its cusp

Let d(u)=exp(-|u|/2). We claim

    E(psi)=Z(d k).                                         (P4)

This notation DOES NOT assume multiplication of an arbitrary distribution
by a nonsmooth function. Define Z(dk) by the sum of its zero evaluations.

For every |delta|<=1/2, the function
q_delta(u)=exp(delta u)d(u)k(u) is continuous and compactly supported,
smooth on each side of 0. Its distributional second derivative is a finite
measure of uniformly bounded total variation: the ordinary second
derivatives have uniformly bounded L1 norms and the first derivative jump
at 0 is exactly -k(0). There is no value jump. Two distributional integrations
by parts therefore prove

    |integral exp(delta u)d(u)k(u)exp(i gamma u)du|
                  <= C_k/(1+gamma^2).                     (P4.1)

The bound for small gamma is supplied by ||q_delta||_1. Thus Z(dk) is
absolutely convergent. This explicitly retains the cusp; it is not smoothed
away without a limit.

To establish (P4), first sum over the finite multiset |gamma|<=T, invariant
under rho -> 1-conjugate(rho). For u>=0,

    d(u)exp((beta-1/2)u)=exp(-(1-beta)u).

For u<0 it equals exp(-beta|u|). Relabel beta -> 1-beta on that negative
half ONLY, which preserves gamma and multiplicity in the finite multiset.
This gives equality with the finite zero sum in (P3.2). Pass to the limit
using the absolute convergence of the WHOLE zero evaluations on both
sides. No separately absolutely convergent half-line zero sum is asserted:
the half-line integrals alone can have a 1/gamma boundary term.

## P5. Exact full arithmetic identity and extension to dk

Write alpha(u)=exp(-u/2)/(1-exp(-2u)),
c_A=EulerGamma+log(8pi)+pi/2 and w_n=Lambda(n)/sqrt(n). For a compact smooth
test h, the accepted version of Suzuki's full explicit formula is

    Z(h)=integral_0^infinity alpha(u)[2h(0)-h(u)-h(-u)]du
          -c_A h(0)
          +integral_R 2cosh(u/2)h(u)du
          -sum_(n>=2) w_n[h(log n)+h(-log n)].             (P5.1)

This is the same original full Q when h=k. No prime power is omitted.
The different archimedean constant in Suzuki (3.3) converts using the
already checked integral
2 integral (1-exp(-u/2))alpha(u)du=log 2+pi/2.

To extend (P5.1) to h=dk, use real nonnegative even compact smooth unit-mass
mollifiers eta_epsilon and h_epsilon=eta_epsilon*h. Supports lie in a fixed
compact interval; h_epsilon converges uniformly to h and has a uniform
Lipschitz bound. The second derivatives have uniformly bounded L1 norms
because h'' is a finite measure. For |delta|<=1/2, the second derivatives
of exp(delta u)h_epsilon have uniformly bounded L1 norms too. The bound
(P4.1) is therefore uniform in epsilon. Dominated convergence of the zero
evaluations yields Z(h_epsilon)->Z(h). On the arithmetic side the prime
sum has only finitely many possible terms in the common compact support,
the pole integrals converge uniformly on that support, and near zero

    |2h_epsilon(0)-h_epsilon(u)-h_epsilon(-u)| <= C|u|.

This cancels the alpha(u)=O(1/u) singularity and gives dominated convergence
of the grouped archimedean integral. Away from zero alpha is integrable.
Hence (P5.1) applies to dk without any unaccounted contact term.

Substitution of h=dk now gives the promised COMPLETE arithmetic energy:

    E(psi)=integral_0^infinity alpha(u)
                 [2k(0)-exp(-u/2)(k(u)+k(-u))]du
            -c_A k(0)
            +integral_R (1+exp(-|u|))k(u)du
            -sum_(n>=2) [Lambda(n)/n][k(log n)+k(-log n)]. (P5.2)

The original prime coefficients Lambda(n)/sqrt(n) have become Lambda(n)/n.
Both original pole terms combine to 1+exp(-|u|), rather than disappear.
The archimedean constant is unchanged because d(0)=1; its integral kernel
has changed exactly as displayed. There is no series truncation error.

## P6. Relation to the full cutoff field, with the boundary terms visible

Let T>=1, s=(1+it)/2, and let N_T(t) be the squared L2 norm of the truncated
Eisenstein series at s in the accepted modular normalization. The full
four-term Maass-Selberg identity on the unitary line gives

    N_T(t)=2 log T-2m'(it)/m(it)+O_T(t),
    O_T(t)=[conjugate(m(it))T^(it)-m(it)T^(-it)]/(it).      (P6.1)

For t=0 these are interpreted by the removable limit. One way to verify
the factor 2 is to approach with s=(1+epsilon+it)/2. The sum of the two
diagonal terms is
[T^epsilon-|m(epsilon+it)|^2 T^(-epsilon)]/epsilon;
|m(it)|=1 and m'/m(it) is real, so its limit is
2 log T-2m'/m(it). The other two terms give O_T.

Combining (P1) and (P6.1) yields

    N_T(t)=2 log T+2P(t)-4/(1+t^2)+O_T(t).                 (P6.2)

Consequently the corresponding integrated field norm satisfies exactly

    (1/(2pi)) integral N_T(t)|hat psi(t)|^2 dt
      =2 log T ||psi||_2^2 + 2E(psi)
        -(1/(2pi)) integral [4/(1+t^2)]|hat psi(t)|^2 dt
        +(1/(2pi)) integral O_T(t)|hat psi(t)|^2 dt.        (P6.3)

All terms converge. P3 pays the P term; O_T is continuous at 0 and at most
2/|t| for |t|>=1. There is no limit T->infinity and no discarded oscillating
term. In fact the removable formula gives N_T(0)=0, consistently with
m(0)=-1 and the functional equation for E(s) at s=1/2.

Thus E is a precisely identified pole-corrected phase energy, NOT the bare
cutoff norm. Its positivity was established independently in P2-P3; positivity
of N_T alone was not used to justify subtraction of its other terms.

## P7. The exact undamped correction has both signs on actual smooth tests

Set K(u)=k(u)+k(-u). Subtract (P5.2) from the ORIGINAL (P5.1):

    Q(psi)=E(psi)+R(psi),

    R(psi)=integral_0^infinity H(u)K(u)du
            -sum_(n>=2) w_n(1-n^(-1/2))K(log n),          (P7.1)

    H(u)=(1-exp(-u/2))[2cosh(u/2)-alpha(u)].

H is continuous for u>0 and has finite limit H(0+)=-1/4. There is no
diagonal constant discrepancy. The following are source-exact controls
for R, not for V or Q.

**Negative R.** Choose any nonzero real nonnegative
psi in C_c^infinity((0,1/8)). Then K>=0, is positive close to 0, and is
supported in |u|<1/8; every prime term vanishes because log 2>1/8.
For 0<u<=1/8,

    alpha(u) >= (15/16)/(2u) >= 15/4,
    2cosh(u/2) <= 2exp(1/16) <= 32/15 <15/4.

Thus H(u)<0 on the relevant positive interval, proving R(psi)<0.
The energy E therefore OVERestimates Q on these exact admissible tests.
This is not a proof that Q itself is negative.

**Positive R.** Fix nonzero real b in C_c^infinity((-1,1)) with ||b||_2=1,
and let b_epsilon(x)=epsilon^(-1/2)b(x/epsilon). Write
r_epsilon(u)=integral b_epsilon(y+u)b_epsilon(y)dy, so r_epsilon(0)=1,
|r_epsilon|<=1 and its support is |u|<2epsilon. Set L0=log 2 and

    psi_epsilon(x)=b_epsilon(x)-b_epsilon(x-L0).

For small epsilon the two bumps are disjoint, and

    k_epsilon(u)=2r_epsilon(u)
                       -r_epsilon(u-L0)-r_epsilon(u+L0).

Choose 2epsilon smaller than min(L0/2,(log 3-log 2)/2). The only prime
power encountered by k_epsilon on u>0 is n=2, and k_epsilon(log 2)=-1.
The prime part of R is exactly

    2 [log 2/sqrt(2)](1-1/sqrt(2)) >0.                    (P7.2)

On the positive half-line, k_epsilon is bounded uniformly and supported
in shrinking intervals about 0 and L0. Since H is bounded on a fixed
neighborhood of those points, its integral contribution is O(epsilon).
It follows that R(psi_epsilon) tends to the positive constant (P7.2);
hence R>0 on actual smooth tests for all sufficiently small epsilon.

This proves indefiniteness of the correction for the ORIGINAL arithmetic
functional. We have not introduced a different source to obtain it.

There is also a generic explanation for why one cannot undo damping by
a positive multiplier: exp(+|u|/2) has the two-node matrix
[[1,exp(d/2)],[exp(d/2),1]] with a negative eigenvalue for every d>0.
This generic fact is secondary to the source-exact R controls above.
Neither is an original negative V witness.

## P8. Decision for the full goal

The exact question "what full functional does this positive phase energy
represent?" is answered by P4-P6. The full complex test class, zero
multiplicities, cusp, pole terms, prime-power weights, archimedean part
and finite-T field boundary terms are all retained.

However the answer is Z(exp(-|u|/2)k), not Z(k)=Q. P7 excludes both a literal
energy equality and the shortcut Q>=E by a universally nonnegative
correction. A bound on the NEGATIVE part of R by E would still require a
new source-specific theorem; the exact identity itself provides none.

We therefore do not continue splitting R into further unnamed remainders
or send a renamed RH inequality to Proshka. This route's proposed free sign
transfer has been tested at its first missing joint and fails there.
The algebraic/source data are preserved for a later genuinely new mechanism.

No original V/Q negative witness, original sign improvement, global VAR/Pick
proof, RH proof/refutation, Lean run, canonical admission or counter reset.


## Independent acceptance

Verdict: ACCEPT_SCATTERING_POISSON_FULL_FUNCTIONAL_IDENTITY_AND_SIGNED_CORRECTION_ONLY.
Final candidate SHA256: 7b5e49d3847be742a7fb017132bd09cf16c14b81045353148589b3cb40411750.
Complete review SHA256: 4ea860215074b10b5899840d728fb8f8b2f8272b8a15e887eb2eeab2e50f26e4.
Complete parent check SHA256: d61b2ca989254c2c094845646bdd67f8487503b8dca0f1d0e4830ef12c625daa.
The parent read the complete independent review and checked the primary formula,
normalizations, cusp extension and both actual-source correction controls.
The full damped-functional identity is accepted; the original undamped sign
is not established. The certificate embeds both reviews and source pins.
