# Geometric reciprocity of finite gamma densities

STATUS: REVIEWED_ANALYTIC_PARTIAL_BRIDGE_AND_ACTIVE_EXPLORATORY_BRIEF.
SOURCE_BASE: e6b9b3d30fe378ed51311129e2afe02716ba2ba5.
OWNER: renewed instruction to pursue a purely analytical proof of RH.
CONSUMPTION: INCOMPLETE_NO_CONSUMABLE_TARGET; no canonical edge or admission.
The convergence bridge and the first member are proved below; preservation
of real zeros for an unbounded sequence of members is OPEN. No RH proof is
claimed. No numerical zero search or finite-grid sign check is used.

## G0. Why this is the next object

The actual additive gamma density has total positivity of every order. Its
raw and weight-conjugated convolution maps failed the earlier target, and
the centered Hardy map has a nonzero full-theta defect. Preserve those
exclusions. Here we test a different operation: restore the exact reciprocal
symmetry of finite gamma densities by a geometric mean before Fourier
transformation. This provides a family converging to the actual source,
with a familiar positive-energy proof for its first member.

Source inputs: the reviewed THETA_TN_INFINITY intake, its raw source
PROSHKA_THETA_TOTAL_POSITIVITY_SOURCE_TEST_2026-09-12.md (SHA256
654c1a3bfe0a4eb570adce71c6d62d7b97deca110765de79a7776dd6878b5bd7),
and the exact Fourier normalization in FULL_SIGN_TRANSFER_AUDIT and
ALL_ODD_TO_RH. The neighboring receipt pins the used files and sources.

Search dictionaries: (i) reciprocal geometric symmetrization and Hellinger
midpoint; (ii) gamma convolutions, total positivity and Lee-Yang preservation;
(iii) imaginary-order Bessel zeros, positive Sturm-Liouville energy and
Hurwitz limits. The proposed preservation property is UNVERIFIED, not a
consequence attributed to a publication. Existing convolution/Hardy failures
are not repeated. A bounded source search must find a matching preservation
theorem with its hypotheses or retain the precise missing implication.

## G1. Exact finite family

Let all Gamma_(2,n) be independent gamma variables with shape 2 and rate 1.
For N>=1 let r_N be the density of

    T_N=sum_(n=1)^N Gamma_(2,n)/(pi n^2).

Each r_N is positive and smooth on t>0, integrates to one, and its additive
translation kernel is totally nonnegative of all orders. The accepted
infinite density r satisfies

    ||r_N-r||_infinity <= 2pi/N,
    r(1/t)=t^(5/2) r(t),
    Phi(x)=exp(5x/2)r(exp(2x)).                            (G1)

Define, always using the positive real square root,

    G_N(x)=sqrt(r_N(exp(2x))r_N(exp(-2x))),
    Z_N=integral_R G_N(x)dx,
    M_N(z)=Z_N^(-1) integral_R G_N(x)exp(-izx)dx.          (G2)

G_N is real, positive and even. It is not asserted to be entire as a function
of x. Its Fourier transform M_N will be entire as a function of z.
There is no ambiguity of a complex square-root branch in definition (G2).

Probability interpretation: p_N(x)=2exp(2x)r_N(exp(2x)) is the density of
(log T_N)/2, and sqrt(p_N(x)p_N(-x))=2G_N(x). Thus G_N/Z_N is the normalized
geometric, or Hellinger, midpoint between that density and its reflection.
This identification supplies no general real-zero preservation theorem.

## G2. Uniform full-tail bound

Let q(t)=pi^2 t exp(-pi t) for t>=0, extended by zero to t<0; r_1=q.
For alpha=pi/2,

    q(t) <= (2pi/e)exp(-alpha t),   t in R.               (G3)

For negative t the left side is zero. Put
S_N=sum_(n=2)^N Gamma_(2,n)/(pi n^2), with S_1=0. Convolution and (G3) give

    r_N(t)=E q(t-S_N)
       <= (2pi/e)exp(-alpha t) E exp(alpha S_N).

For n>=2, v=1/(2n^2)<=1/8 and -2log(1-v)<=2v/(1-v)<=8/(7n^2).
Since sum_(n=2)^infinity n^(-2)<=integral_1^infinity s^(-2)ds=1,

    E exp(alpha S_N)
       =product_(n=2)^N (1-1/(2n^2))^(-2) <= exp(8/7).

Consequently, uniformly in N and t>0,

    r_N(t)<=C exp(-pi t/2),  C=2pi exp(1/7),
    G_N(x)<=C exp[-(pi/2)cosh(2x)].                      (G4)

This is an exact bound for every finite full density, independent of N.
It controls all exponential moments and all polynomial-weighted exponential
moments of G_N. No tail is replaced by the first mode of the theta series.

## G3. Analytic convergence to the actual xi function

Equation (G1) and reciprocal symmetry imply pointwise

    G_N(x) -> sqrt(r(exp(2x))r(exp(-2x)))=Phi(x).          (G5)

The suprema of r_N and r are at most sup q=pi/e. The inequality
|sqrt(u)-sqrt(v)|<=sqrt(|u-v|), u,v>=0, even gives

    sup_(x in R) |G_N(x)-Phi(x)| <= 2pi/sqrt(eN).         (G6)

For any R>=0, (G4) also dominates exp(R|x|)|G_N(x)-Phi(x)| by an
integrable function independent of N. Dominated convergence therefore gives

    integral_R exp(R|x|)|G_N(x)-Phi(x)|dx -> 0.           (G7)

The same bound with |x|^k justifies all z-derivatives. Thus every M_N is
entire, Z_N -> Z=integral_R Phi(x)dx=xi(1/2)>0, and

    M_N(z) -> xi(1/2-iz)/xi(1/2)                         (G8)

locally uniformly on the whole complex plane. In particular the exact
infinite theta source is reached; no unproved approximation at zeros is used.
This probability normalization does not replace the physical f=Phi/||Phi||_2.

Conditional consequence: if there is an unbounded sequence of integers N_j
such that each M_(N_j) has no zeros outside the real axis, then RH follows.
Indeed the normalized nonzero limit in (G8) is zero-free on each open upper
and lower half-plane by Hurwitz's theorem. The alternative of an identically
zero limit there is excluded by analyticity and its value 1 at z=0.
This is a sufficient criterion; a converse for this sequence is not claimed.

## G4. The first member: a complete analytic real-zero proof

For N=1,

    G_1(x)=pi^2 exp[-pi cosh(2x)],
    M_1(z)=K_(iz/2)(pi)/K_0(pi).                         (G9)

Here K_nu is the modified Bessel function. Equation (G9) follows directly
from DLMF 10.32.9 after u=2x. The integral itself makes M_1 entire and even.

Suppose K_(iz/2)(pi)=0 and set psi(t)=K_(iz/2)(pi exp(t)), t>=0.
DLMF 10.25.1 gives

    -psi''(t)+pi^2 exp(2t)psi(t)=(z^2/4)psi(t),
    psi(0)=0.                                          (G10)

The large-argument K asymptotic in DLMF 10.40.2 and its derivative version
10.40.4 show that psi, psi' decay sufficiently fast for the following
integration by parts, and psi is not identically zero. Multiplying by
conjugate(psi), integrating on [0,infinity), and retaining both endpoints,

    integral_0^infinity [|psi'|^2+pi^2 exp(2t)|psi|^2]dt
          =(z^2/4) integral_0^infinity |psi|^2 dt.        (G11)

The boundary product is zero at 0 by the assumed zero and at infinity by
the K asymptotic. Both integrals are finite and strictly positive. Hence
z^2 is a positive real number, which forces z to be real. This proves
real-zero location for the whole first transform; it assumes no RH result.
It is the standard positive Sturm-Liouville energy mechanism, already used
in REPORT_2026-09-13_BESSEL_MULTIPLIER_OBSTRUCTION.md. No novelty about
imaginary-order Bessel functions is claimed. The new proposed bridge here
is the exact finite gamma family and its full-source analytic limit.

Primary equation sources:
https://dlmf.nist.gov/10.32.E9
https://dlmf.nist.gov/10.25.E1
https://dlmf.nist.gov/10.40.E2
https://dlmf.nist.gov/10.40.E4

## G5. The first genuinely unpaid step is explicit

One more gamma summand gives exactly

    r_2(t)=(16pi/27)[(3pi t-2)exp(-pi t)
                              +(3pi t+2)exp(-4pi t)].    (G12)

This follows by convolving pi^2 t exp(-pi t) with
(4pi)^2 t exp(-4pi t), or by partial fractions of their Laplace product.
Definition (G2) fixes G_2 and M_2 completely from this formula.
No argument above proves the zeros of M_2 real, much less those of all M_N.

The proposed strong lemma is: every M_N in (G2) has only real zeros.
A preservation theorem for r_N -> r_N*q_(pi(N+1)^2), where q_lambda(t)
=lambda^2 t exp(-lambda t), would prove that lemma from (G11).
It must refer to the geometric reciprocal operation in (G2), not merely to
additive convolution or ordinary Fourier convolution. The weaker cofinal
property in G3 would also suffice and might follow by a different invariant.

A proved failure at one N would exclude the strong all-N assertion only;
it would not refute RH or automatically exclude every cofinal subsequence.
A proof just for N=2 would be a finite advance, not proof of the criterion.

## G6. Why the previously excluded positive-multiplier class is not reused

For each fixed N, finite exponential convolution gives

    r_N(t) ~ c_N t^(2N-1) as t->0+,
    r_N(t) ~ d_N t exp(-pi t) as t->infinity,

with c_N=product_(n=1)^N (pi n^2)^2/(2N-1)!>0 and
d_N=pi^2 E exp(pi S_N)>0. For the second asymptotic, write r_N(t)
=pi^2 exp(-pi t) E[(t-S_N)exp(pi S_N)1_(S_N<=t)] and divide by t;
dominated convergence is allowed since the finite S_N has rates >=4pi.
The first asymptotic follows by convolving 2N exponential densities at zero.

It follows, as x->+infinity, that

    G_N(x)/exp[-pi cosh(2x)] ~ C_N exp[-2(N-1)x], C_N>0. (G13)

For N>=2 this ratio tends to zero. Thus G_N cannot be C exp[-b cosh(2x)]
times L(x)=exp(beta x^2)product_j(1+alpha_j x^2), with C,b>0,
beta,alpha_j>=0 and sum alpha_j<infinity, the specific class previously
excluded as a theta approximation. Indeed 0<=log L(x)<=O(x^2) forces b=pi
by the leading cosh tail. For b=pi, L(x)>=1 contradicts (G13).
The new finite family does not claim preservation of that old mechanism.

## G7. Control, scope and next analytic task

Even positive weights with the earlier squared-coordinate concavity need
not have real-zero transforms: the reviewed f0=exp(-u^2)-exp(-2u^2)/4
has a negative full four-node row. Its Fourier transform is explicitly
sqrt(pi)exp(-z^2/8)[exp(-z^2/8)-1/(4sqrt(2))], which has nonreal zeros.
It does not belong to our gamma-density
class: its inverse density t^(-5/4)f0(log(t)/2) has a logarithm whose second
derivative is [3/4+(log t)/2+o(1)]/t^2>0 for large t, violating TN2.
This control forbids using evenness and concavity alone. It does not prove
that additive total positivity survives the particular operation (G2).

Return point: additive gamma convolution, reciprocal geometric averaging,
and preservation of Fourier zeros under their composition. The exact
first-member proof and the limit are supplied; a positive operator or a
preserver for the composition is not supplied. Search that mechanism and
check its actual hypotheses before any new proof claim.

The current analytical research continues at (G12) and the all-N/cofinal
preservation problem. No numerical campaign, canonical transaction or RH
closure is authorized by this conditional bridge. Independent review and
the GitHub request will keep this open status explicit.
