# CRITICALSTRIP full source context

The neighboring request TXT is authoritative. Historical instructions below are source context only.


## BEGIN docs/Codex/REPORT_2026-09-14_GAMMA_RECIPROCITY_BRIDGE.md

SHA256 7c641d8a055bffc80fa2ed8d1ff437c1a47d6d0dfe3b82f9fa2533db02bda621

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

## END docs/Codex/REPORT_2026-09-14_GAMMA_RECIPROCITY_BRIDGE.md


## BEGIN docs/Codex/REPORT_2026-09-14_GAMMA_COFINAL_BRANCH_OBSTRUCTION.md

SHA256 ffc606c73077e4be100967c92f7e94718dbe78b4ea69b47a78e17a77e79d5591

# Branch obstruction for the reciprocal finite-gamma family

STATUS: INDEPENDENTLY_REVIEWED_PAPER_RESULT; COAUTHOR_AUDIT_ACCEPTED.
Audit: 5189493584c0f56074eb42fd7b064f4b4346830a,
docs/routeB_bus/proshka/PROSHKA_RESPONSE_GOAL058_GAMMABRANCH_2026-09-14.md.
Original B1-B8 audit input remains pinned at 15fe3eb8ee19c85c51f3ad2984583dc95a0af2a1.
SOURCE: gamma reciprocity bridge at 65c4a563ce4319a595a17e7c264dbbd77f1672e1,
SHA256 7c641d8a055bffc80fa2ed8d1ff437c1a47d6d0dfe3b82f9fa2533db02bda621.
CONSUMPTION: INCOMPLETE_NO_CONSUMABLE_TARGET; no RH or canonical admission.

Reviewed result: for every integer N>=13 the exact auxiliary transform M_N
has infinitely many nonreal zeros. The cofinal real-zero criterion for this
particular family is therefore unavailable, even
though its analytic convergence to the actual xi function remains correct.
This is not a negative witness for the actual theta form and does not refute
RH. No numerical zero search, quadrature, or finite-grid sign test is used.

The semantic return from the scalar-lift failure is to the geometric square
root itself: it preserves the real source limit, but may create algebraic
branch points in the complex source variable. The worked mechanism is a
contour shift to the nearest branch points, Watson endpoint asymptotics,
Jensen's formula to count real zeros, and Hadamard factorization to compare
that count with growth on the imaginary axis. All four maps are spelled out.

## B1. The relevant finite exponential polynomial

Fix N>=13 and lambda_n=pi n^2. The Laplace transform of r_N is
product_(n=1)^N [lambda_n/(z+lambda_n)]^2. Partial fractions at its distinct
double poles give the entire continuation

    r_N(t)=sum_(n=1)^N (d_n t+e_n) exp(-pi n^2 t),
    d_n=lambda_n^2 product_(m!=n)[lambda_m/(lambda_m-lambda_n)]^2
       =4pi^2 n^4 (N!)^4/[(N-n)!(N+n)!]^2 >0.          (B1)

The constants e_n are real; their values will not be needed. Write

    D_N(w)=sum d_n w^(n^2)=w P_N(w),
    P_N(w)=sum d_n w^(n^2-1),
    E_N(w)=sum e_n w^(n^2).

Then r_N(t)=t D_N(exp(-pi t))+E_N(exp(-pi t)).
The coefficient ratios satisfy

    d_2/d_1=16[(N-1)/(N+2)]^2 >=256/25,
    d_n/d_2 <= n^4/16,  n>=3.                          (B2)

The second inequality follows by writing the extra factorial ratios as
product_(j=2)^(n-1)[(N-j)/(N+j+1)]^2 <=1.

## B2. A simple negative root of P_N inside the unit disk

Put r=1/2. In P_N(-r), even n give negative terms and odd n positive ones.
Using (B2), dropping the negative terms n>=4, and bounding the odd tail by
all n>=5,

    P_N(-1/2)/d_2
      <=25/256-1/8+81/4096
                         +sum_(n>=5) (n^4/16)2^(-(n^2-1))
      <=-31/4096 +(256/255)625/2^28 <0.                 (B3)

For the last bound the ratio of consecutive positive tail terms is at most
(6/5)^4 2^(-11)=81/80000 <1/256.
As P_N(0)=d_1>0, a negative root w_0=-r_0 exists with 0<r_0<1/2.
It is simple: for every 0<r<=1/2,

    (d/dr)P_N(-r)/(3d_2 r^2)
       <=-1+(27/2)r^5
          +sum_(n>=5) [(n^2-1)n^4/48] r^(n^2-4)
       <=-1+27/64+(256/255)625/2^22 <0.                (B4)

The ratio of consecutive terms in the latter tail is at most
(35/24)(6/5)^4 2^(-11)=189/128000 <1/256. Thus the real root is simple.
For transparency the positive rational margins in (B3) and (B4) are,
respectively, 404611/53477376 and 482947/835584. These are exact rational
inequalities, not a numerical approximation to a zero or integral.

## B3. Simple zeros of r_N in Re(t)>0, and nonremovable square roots

Let sigma=-log(r_0)/pi>0, t_j=sigma+i(2j+1). Then exp(-pi t_j)=w_0.
For t=t_j+zeta in a fixed small disk about t_j,

    r_N(t)/t = D_N(w_0 exp(-pi zeta))
                         + E_N(w_0 exp(-pi zeta))/(t_j+zeta).

The first term has a simple zero at zeta=0; the second converges uniformly
to zero as j->infinity. Rouche's theorem on a sufficiently small fixed
circle, followed by the local simple-root estimate, gives exactly one
simple zero t_j^*=t_j+O(1/j). In particular Re(t_j^*)>0 for large j.
At zero, r_N(t)=c_N t^(2N-1)(1+O(t)) with c_N>0, so r_N has no nonzero
zeros in a fixed punctured disk. Thus r_N(1/t_j^*)!=0 for large j.

Let x_j=(1/2)Log(t_j^*) using the principal logarithm. Then
0<Im(x_j)<pi/4 and the entire function

    F_N(x)=r_N(exp(2x))r_N(exp(-2x))

has a simple zero at x_j. Its square root G_N, continued from the positive
real axis, therefore has a genuine algebraic branch point there. Conjugation
provides such a point below the real axis as well. This step specifically
checks that reciprocal pairing does not cancel the branch.

## B4. Only finitely many singularities in every strictly smaller strip

For any fixed b<pi/4, the finite exponential polynomial (B1), uniformly in
|Im(x)|<=b as Re(x)->infinity, gives

    r_N(exp(2x))=(d_1 exp(2x)+e_1)exp(-pi exp(2x))(1+o(1)),
    r_N(exp(-2x))=c_N exp(-2(2N-1)x)(1+o(1)).          (B5)

Indeed Re(exp(2x))>=cos(2b)exp(2Re(x)), so all higher rates are uniformly
suppressed. Both factors are nonzero outside a sufficiently large compact
rectangle. By reflection the same holds at Re(x)->-infinity. Hence F_N has
only finitely many zeros in that closed strip. It has none on the real axis.

By B3 there is an odd-order zero at distance less than pi/4 from the axis.
Consequently the smallest such distance a is positive and attained by a
finite nonempty set of lower-half-plane zeros

    x_l=b_l-i a,  l=1,...,L, with distinct real b_l.

Choose epsilon>0 so a+epsilon<pi/4 and no other odd-order zero lies between
those zeros and Im(x)=-(a+epsilon). Even-order zeros are removable for the
analytic square root and need no cut. Continue G_N into this lower strip
with vertical cuts from each x_l down to its lower boundary. On this slit
strip it is holomorphic and has the uniform double-exponential tail bound

    |G_N(x+iy)|<=C exp(C|x|-c exp(2|x|)),               (B6)

away from the finite cuts; the corresponding boundary values obey the same
bound. This follows directly by taking the modulus of the square root of
(B5). All constants here may depend on the fixed N, a and epsilon.

## B5. Contour asymptotics in every fixed spectral horizontal band

Let an odd zero at x_l have multiplicity 2m_l+1. In a local branch,

    G_N(x)=c_l(x-x_l)^alpha_l(1+O(x-x_l)),
    alpha_l=m_l+1/2,  c_l!=0.

Move the Fourier contour down to Im(x)=-(a+epsilon), retaining the two
banks of each vertical cut. The vertical sides at Re(x)=+/-R tend to zero
by (B6). Each cut contribution has the form

    exp(-iz x_l) integral_0^epsilon exp(-z t) J_l(t)dt,
    J_l(t)=k_l t^alpha_l(1+O(t)),  k_l!=0.              (B7)

Orientation and the square-root jump are absorbed into k_l; its nonzero
value follows from odd monodromy. Local cuts can be shortened and their
remaining segments included in exponentially smaller errors. Watson's
lemma, or direct scaling t=u/z with a Taylor remainder estimate, now gives
k_l Gamma(alpha_l+1) z^(-alpha_l-1) times exp(-iz x_l).
The lower horizontal integral is exponentially smaller. These estimates
are uniform as Re(z)->infinity with |Im(z)|<=B, for each fixed finite B:
(B6) controls the horizontal integral and exp(B|Re(x_l)|) is a constant.

With alpha=min_l alpha_l, after division by the positive constant Z_N,

    exp(a z) z^(alpha+1) M_N(z)=P(z)+O(1/Re(z)),        (B8)
    P(z)=sum_(alpha_l=alpha) C_l exp(-i b_l z),
    C_l!=0.

The principal power of z is holomorphic and nonzero in Re(z)>0. Higher
alpha_l differ from alpha by positive integers; this gives the stated
O(1/Re(z)) remainder. Distinct b_l ensure P is not identically zero.
This is an explicit application, not an inference from a picture of zeros.
For the endpoint method see NIST DLMF 2.4(i), equation 2.4.1, and 2.3(ii).
The contour construction and all input hypotheses needed here are above.

## B6. There are only O(T) real zeros

Write U(z)=exp(a z)z^(alpha+1)M_N(z), holomorphic for Re(z)>0.
There are constants L_0,c>0 such that every real interval [A,A+L_0]
contains a point s with |P(s)|>=c. To prove this, integrate |P|^2: the
diagonal part is L_0 sum|C_l|^2, while the cross terms are bounded by
sum_(l!=j)2|C_l C_j|/|b_l-b_j| independently of A. Choose L_0 large enough
that the diagonal exceeds twice that bound.

For large A, (B8) gives a point s in that interval with |U(s)|>=c/2.
On the disk of radius 2(L_0+2) about s, U is bounded above by a constant
independent of A: use (B8) uniformly in that fixed horizontal band and the
boundedness of the finite exponential sum there. Jensen's formula bounds
the number of zeros in the concentric disk of radius L_0+2 by a fixed
constant, independent of A. That disk includes [A,A+1]. Thus the number of
positive real zeros up to T, counted with multiplicity, is O(T).
Evenness gives the same conclusion for all real zeros. The bounded initial
segment contains finitely many zeros because M_N is entire and M_N(0)=1.

## B7. Growth forbids all but finitely many zeros being real

The real-tail bound in G4 implies

    log max_(|z|<=R)|M_N(z)|=O(R log(R+2)),              (B9)

so M_N has order at most one. Conversely the fixed-N tail in G6 gives
G_N(x)>=c exp(-A exp(2x)-B x) for all sufficiently large positive x.
Integrate exp(Tx)G_N(x) over
[(log T)/2, (log T)/2+1] to get

    log M_N(iT)>=(T/2)log T-C T-C log T.               (B10)

Suppose only finitely many zeros of M_N were nonreal. Hadamard factorization
for an even entire function of order at most one, grouping opposite roots,
then gives

    M_N(z)=P_0(z) product_(rho_j>0)(1-z^2/rho_j^2),    (B11)

up to a nonzero constant absorbed into the even polynomial P_0. All
nonreal roots are in P_0, with multiplicities. There is no linear exponential
factor, by evenness. There is no root at zero. The paired product converges
since the real zero count is O(T). For its logarithmic growth on iT,

    sum_j log(1+T^2/rho_j^2)=O(T),                     (B12)

as follows by Stieltjes integration with n(t)<=C(1+t), using separately a
fixed interval below the first positive root. The finite polynomial adds
only O(log T), contradicting (B10). Thus M_N has infinitely many nonreal
zeros for every N>=13, provided B1--B6 withstand independent review.

This conclusion excludes every unbounded real-zero subsequence of this
specific geometric finite-gamma family. It leaves M_2 through M_12 undecided
and does not alter the proven N=1 Bessel case. The convergence to xi remains
true: nonreal zeros can move with N, and no zero of the limit off the real
axis has been supplied. Full V, IC, ODD2 and RH remain OPEN.

## B8. Fixed Gaussian multipliers do not repair the obstruction

For every fixed real h, replace G_N(x) by exp(h x^2)G_N(x), with its positive
integral as normalization. For N>=13 its Fourier transform again has
infinitely many nonreal zeros. The multiplier is entire and nowhere zero,
so all branch points and their orders in B3--B5 are unchanged. On each
horizontal source strip it adds at most exp(|h|x^2+C), still dominated by
the double-exponential tail. Thus the fixed spectral-band asymptotic in equation (B8) and
B6's real-zero count apply without change, with different nonzero constants.
The imaginary-axis lower bound loses at most O_h((log T)^2), which is o(T),
and the maximum-modulus upper bound is still O_h(R log(R+2)). The Hadamard
contradiction therefore repeats for this fixed h.

No finite choice h=h_N for each N can provide a cofinal all-real-zero family
by this multiplication. This excludes only the stated Gaussian multiplication
of this auxiliary family, not arbitrary source deformations or a conclusion
about the de Bruijn--Newman constant of the actual xi function.

## END docs/Codex/REPORT_2026-09-14_GAMMA_COFINAL_BRANCH_OBSTRUCTION.md


## BEGIN docs/Codex/REPORT_2026-09-15_GAMMA_CRITICAL_STRIP_INTERFACE.md

SHA256 97213adb97f5a5b8224ce1f4268e4afc186e15a125dd1f7b95cc57a4e0f8c5e0

# Finite-gamma approximants: the critical-strip interface

Status: PAPER analytic candidate; exact independent review required before
delivery. Source base: 5aba82c8108c19006c03d0fe207c38234ac0bbae.
No canonical admission, change to the paused native goal, or RH claim.

## 1. Return to the actual target

The user renewed the request to prove RH using the existing results.
Neither a self-adjoint realization nor real zeros of every auxiliary function
throughout the whole plane is necessary as a general requirement for RH.
The existing finite-gamma family already has a proved analytic limit. Its
full-plane real-zero preserver was disproved; a weaker local condition was
not settled by that result. This report states the weaker condition exactly
and proves what the branch obstruction does say about horizontal bands.

Source documents at the pinned base, read in full:
`docs/Codex/REPORT_2026-09-14_GAMMA_RECIPROCITY_BRIDGE.md`, G1-G3, G6;
`docs/Codex/REPORT_2026-09-14_GAMMA_COFINAL_BRANCH_OBSTRUCTION.md`, B1-B8.
Their previous independent PAPER reviews remain scoped to their actual claims.

For independent Gamma(2,1) variables define

    T_N=sum_(n=1)^N Gamma_(2,n)/(pi*n^2), density r_N,
    G_N(x)=sqrt(r_N(exp(2x))*r_N(exp(-2x))) >0 on R,
    Z_N=integral_R G_N(x)dx,
    M_N(z)=integral_R G_N(x)exp(-izx)dx/Z_N.

All square roots here are positive real roots. Let r be the full density.
Already proved: r_N(u-v) is TN infinity,
||r_N-r||_infinity<=2pi/N, r(1/t)=t^(5/2)r(t), and

    G_N(x)<=2pi exp(1/7) exp[-(pi/2)cosh(2x)]

uniformly in N. With Phi(x)=exp(5x/2)r(exp(2x)), the resulting entire
functions satisfy, locally uniformly in the whole complex plane,

    M_N(z) -> F_*(z)=xi(1/2-iz)/xi(1/2),  F_*(0)=1.     (C1)

Raw r_N loses exact inversion B. G_N restores real reflection symmetry;
it is not thereby proved to retain additive TN infinity or the exact
holomorphic divisor structure of the full source. These are distinct claims.

## 2. What the old obstruction proves in every fixed band

Fix N>=13. B5 gives a>0, alpha>=1/2 and a nonzero finite exponential sum

    P(z)=sum_l C_l exp(-i b_l z),  b_l distinct real,
    U(z)=exp(a*z)z^(alpha+1)M_N(z)=P(z)+O(1/Re z)       (C2)

as Re z tends to infinity in each fixed horizontal band. Constants may
depend on N and on the band. U is holomorphic on Re z>0; its prefactor has
no zeros there. Distinct frequencies give constants L,c>0 such that every
real interval [A,A+L] contains s with |P(s)|>=c. Indeed, the integral of
|P|^2 over that interval is L sum|C_l|^2 plus bounded cross terms, uniformly
in A; choose L so the diagonal dominates those terms. Then |U(s)|>=c/2
for all sufficiently large A.

Fix B>0 and choose d>L+B+2. The disk of radius d about s covers
[A,A+1]+i[-B,B]. On the disk of radius 2d, (C2) bounds |U| above by a
constant independent of large A. Jensen's formula therefore bounds the
number of zeros in the inner disk by a constant independent of A.
Evenness covers negative real parts; the remaining compact rectangle has
finitely many zeros, since M_N is entire and M_N(0)=1. Thus, with
multiplicities,

    #{z: M_N(z)=0, |Re z|<=R, |Im z|<=B}
        = O_(N,B)(1+R).                                (C3)

In addition B7 proves

    log max_(|z|<=R)|M_N(z)|=O_N(R log(R+2)),
    log M_N(iT)>=(T/2)log T-O_N(T+log(T+2)).           (C4)

Suppose only finitely many zeros lay outside some fixed horizontal band.
Then (C3), together with those finite exceptions, gives total radial zero
count n(R)=O(1+R). The even entire function M_N has order at most one and
has no zero at zero. Pairing opposite zeros in Hadamard's product removes
the linear exponential factor by evenness. Consequently

    log|M_N(iT)| <= C + sum_j log(1+T^2/|z_j|^2)=O(T).

Here z_j is one root from each opposite pair, with multiplicities. The final
estimate follows by Stieltjes integration from n(R)=O(1+R), starting below
the first positive root modulus. Finite polynomial factors add O(log T).
This contradicts (C4). Therefore

    for every fixed N>=13 and every B>0,
    infinitely many zeros of M_N satisfy |Im z|>B.     (C5)

This is a fixed-N statement about arbitrarily high zeros. It does NOT prove
that all nonreal zeros escape as N tends to infinity; the two limits must
not be exchanged. It also neither excludes nor exhibits a nonreal zero in
the critical band |Im z|<=1/2.

## 3. The exact weaker condition and its complete sufficiency

For R>0 and 0<epsilon<1/2 set

    K_(R,epsilon)={z: |Re z|<=R,
                       epsilon<=|Im z|<=1/2}.

The following condition on the fixed sequence M_N is equivalent to RH:

    for every R>0 and 0<epsilon<1/2 there is N0
    such that for every N>=N0, M_N has no zero in K_(R,epsilon).   (C6)

Proof of sufficiency: if F_* had a nonreal zero z0 in |Im z|<1/2,
choose R,epsilon so z0 lies inside K_(R,epsilon), and a closed disk around
z0 inside K whose boundary has no zeros of F_*. By (C1), Rouche's theorem
gives a zero of every sufficiently large M_N inside the disk, contradicting
(C6). The classical location of xi zeros and zero-freeness on Re s=0,1
exclude the boundary and exterior. Thus all zeros of F_* are real and RH
follows. No simplicity assumption is used.

Proof of necessity: under RH, F_* is nonzero on K_(R,epsilon). Its modulus
there has positive minimum. Uniform convergence (C1) then excludes zeros
of M_N on K for all sufficiently large N.

The necessity argument is NOT a source proof of (C6): using that unknown
positive minimum before proving RH would be circular. (C6) is an exact
consumer interface, not new source-sign progress or a new solved theorem
about the zeros of xi.

All-real auxiliary functions were stronger than needed. For a transparent
logical example, (1+z^2/N^2)cos z converges locally uniformly to cos z,
although every member has nonreal roots at +iN and -iN. This is not claimed
to be a gamma-family example. It only separates the quantifiers.

## 4. One specific next proof task

An explicit error budget is available, without assuming anything about zeros.
Let C=2pi exp(1/7), c=pi/4, delta_N=2pi/sqrt(eN), and, for N>=3,

    L_N=(1/2)log(4 log(N)/pi),
    D_N(R)=integral_R exp(R|x|)|G_N(x)-Phi(x)|dx.

The uniform sup bound and the common double-exponential envelope give

    D_N(R) <= E_N(R)
      :=2 delta_N L_N exp(R L_N)
           +2 C c^(-R/2) Gamma(R/2,log N),              (C7)

for every R>=0, where Gamma(a,b)=integral_b^infinity t^(a-1)exp(-t)dt.
Indeed the central interval contributes at most the first term. On its
complement use |G_N-Phi|<=2C exp[-c exp(2|x|)], add the two tails and set
t=c exp(2x). This yields exactly the second term. Both terms tend to zero
for fixed R. The same envelope also yields the finite upper bound

    integral_R exp(R|x|)Phi(x)dx
       <= B_R:=C c^(-R/2)Gamma(R/2,c).

Writing Z=integral_R Phi>0, whenever E_N(0)<=Z/2 the normalization is paid:

    sup_(|Im z|<=R)|M_N(z)-F_*(z)|
      <= 2 E_N(R)/Z + 2 B_R E_N(0)/Z^2.               (C8)

The estimate is uniform even in Re z, but it is an absolute approximation
bound. It is not a lower bound on either transform away from the real axis.
In particular it does not prove C6 where transforms can be very small.

Try to prove (C6) directly from the full fixed rate product and the coupled
reciprocal construction. A useful result would supply, for each R,epsilon,
an N0 from source estimates that exclude zeros of M_N on K. A zero-location
bound on compact critical rectangles with distance to the real axis tending
to zero is another way to supply the same interface.

Do not replace the target by full-plane real zeros, simplicity, another
Gaussian multiplier, or positivity of V. Do not infer it from (C3)-(C5):
their constants depend on N and their large-Re limit is a different limit.
Do not infer zero exclusion from an approximation error alone without a
proved nonzero comparison function and its required lower bound.

A fixed-N nonreal zero only refutes an all-N strengthening. To disprove C6
for this actual convergent family one needs zeros in one fixed off-axis
critical compact for an unbounded sequence of N; that would itself refute
RH by (C1). No such witness is known here. Failure of a proposed estimate
must be reported in its narrower scope.

## 5. Bounded semantic return already performed

Three new shelf dictionaries (Meixner-Pollaczek expansion; continuous Hahn
Mellin reciprocity; orthogonal polynomial hyperbolicity preservers) returned
INCOMPLETE because of index freshness, not no hits. Their exact outputs are
retained in the source-polynomial-preserver-20260915 evidence directory.
The old source-query receipts were reused rather than repeated.

Romik's primary paper was inspected as a possible alternative. Theorem 3.1,
printed p.27, gives an expansion of the full Xi with local uniform convergence;
it does not supply the all-order zero-preserving estimate sought here. The
source's literal phrase is "converges uniformly on compacts". Source:
https://www.math.ucdavis.edu/~romik/data/uploads/papers/riemannxi-acta-online-first.pdf
PDF SHA256 a28edcf341776bf801e9d0c2de4631639b2c46c579a67a38cc2788d255e2ae87,
721444 bytes. Only introduction and relevant expansion statements were read;
no full-paper or proof-of-RH claim. This alternative was not selected. The
present continuation uses the already proved gamma limit (C1).

Decision: retain the old global obstruction, reopen only the weaker compact
critical-strip proof question under the user's renewed instruction. This is
one interface correction and an analytic attempt to supply it, not a reset
of source-sign counters or another claim that a renamed unknown is progress.

## END docs/Codex/REPORT_2026-09-15_GAMMA_CRITICAL_STRIP_INTERFACE.md
