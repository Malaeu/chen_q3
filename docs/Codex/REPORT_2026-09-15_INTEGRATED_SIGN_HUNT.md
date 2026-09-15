# Integral compensation: verified mechanisms and exact theta preflights

STATUS: ANALYTIC_PAPER_AND_SOURCE_HUNT; review is recorded in the adjacent certificate.
SOURCE_BASE: 12db0efd95e911bd558bfd4a80558e9a199eb8fa.
CONSUMPTION: INCOMPLETE_NO_CONSUMABLE_TARGET; isolated exploration, not canonical admission.
FULL_THETA_V / IC / ODD2 / RH: OPEN. ACTUAL_NEGATIVE_V_WITNESS: NONE.
PX_RH_CLAIM: NOT_MADE.

## 1. Question, exact object and bounded search

The owner asks how known proofs compensate signed integral contributions,
which partial signs can actually be proved, and whether theta structure was
overlooked. Preserve f=Phi/||Phi||_2, the COMPLETE positive even theta source,
I=(-log(2)/2,0), arbitrary finite node lists in I and arbitrary complex c.

    V(x,y)=integral_0^infinity (2t+x+y)f(t+x)f(t+y) dt
          =integral_0^infinity K_s(x,y) ds,
    K_s(x,y)=f(sqrt(s+m^2)+d)f(sqrt(s+m^2)-d),
    m=(x+y)/2, d=(x-y)/2.                                  (H1)

Write h_c(s)=sum_ij conjugate(c_i)K_s(x_i,x_j)c_j. This is real and
absolutely integrable: every individual positive entry has finite integral.
The target is integral h_c>=0 for ALL such families, not entrywise positivity.

Pinned inputs under docs/Codex:

| Report | SHA256 | Use |
| --- | --- | --- |
| REPORT_2026-09-15_LAYER_GRAM_TEST.md | a402aa67f81824945d3324881e2a822a8e897a07316b3dc780e671228715e1eb | L1, L10-L13; actual negative small-s layers, not negative V |
| REPORT_2026-09-14_FULL_V_RANK_TWO_INTAKE.md | 51168fb802d7facfb74291d0a3fc0009b121f540711df2fe10ae01cd84c1d14f | R2-R5 pointwise comparison; R9-R12 negative control |
| REPORT_2026-09-13_NULL_AND_GROUND_STATE_TEST.md | See certificate source pin | Existing local ground-state mismatch; not repeated as a new route |

The source-pinned brief in this commit preceded discovery. Three registered
ask.sh shelf queries covered cumulative integrals/Abel-Steffensen, nonlocal
ground-state/Picone, and Plancherel/spectral factorization. All returned exit
2 with INCOMPLETE freshness, so none establishes absence. Exact queries, raw
hashes and source artifacts are in the certificate. Primary-source web
verification followed. This is a bounded three-mechanism hunt, not an
exhaustive literature review or a repaired semantic-index attestation.

Reconciled prior work: local ground-state and first-order storage failures;
covariance/Poisson identities; KYP initial-boundary requirements; anchored
Hardy transfer; reflection/Hankel mismatch; the explicit quartic sibling.
None is promoted to a new theta proof by changing its name.

## 2. Partial positivity that really does hold

Every scalar K_s(x,y) is positive. More strongly, RAW2 supplies, with
rho(z)=f(sqrt(z)), the POINTWISE comparison

    0<K_s(x,y)<=rho(s+x^2)rho(s+y^2)
               =sqrt(K_s(x,x)K_s(y,y)).                    (H2)

It follows from concavity of log rho and the equal-sum argument in R3-R4;
the comparison precedes integration. Hence every TWO-node matrix K_s is
positive semidefinite for every s>=0. In particular h_c(s)>=0 for every
two-node family and every complex coefficient pair. Repeated nodes combine.

There is another genuine restricted class, of arbitrary size: if
Re(conjugate(c_i)c_j)>=0 for all pairs, then

    h_c(s)=sum_i |c_i|^2 K_s(x_i,x_i)
            +2 sum_(i<j) Re(conjugate(c_i)c_j)K_s(x_i,x_j)>=0. (H3)

For example, the phases of all nonzero coefficients may lie in one closed
arc of width pi/2. Same-phase nonnegative amplitudes are a special case.
These restrictions do not cover all complex coefficients.

L13 nevertheless proves the existence of a fixed finite allowed family with

    h_c(s)=A s+o(s), A<0, as s decreases to 0.              (H4)

No explicit nodes, rank bound or threshold are supplied by L13. H2 shows
that after repeated nodes are combined, such a row has at least THREE
distinct nodes. The four-node witness known elsewhere belongs to the
DIFFERENT control source f0, not to this actual-theta layer result.

The original t-integrand in H1 is a different decomposition: even a single
negative shift gives a negative t-contribution near t=0. H2 concerns the
new s-layers AFTER exact odd cancellation. Those two decompositions must
not be conflated. H4 rules out making all these fixed s-layers positive;
it leaves other regroupings of the WHOLE integral possible.

## 3. Abel-Steffensen: control accumulated signed mass

Primary source: C. P. Niculescu, *The Abel-Steffensen inequality in higher
dimensions*, arXiv:1707.03236v1, [PDF](https://arxiv.org/pdf/1707.03236).
Read introduction p.1 (Abel partial summation) and section 3, Theorem 2,
pp.5-6 (cumulative rectangle integrals and Young's identity).
Short quote, section 3 p.5: "restricted to suitable subcones".
Fetched PDF SHA256: 1e7d66eecede5738f6476fcafc71a8f3372bbf89fa23b195880130ddbfc444c4.

The useful mechanism is accumulated balance rather than the sign of each
increment. The following one-dimensional version is proved directly here.
For real h in L1([0,R]), F(t)=integral_0^t h, and a C1 weight w>=0 with
w'<=0, integration by parts gives

    integral_0^R w h = w(R)F(R)+integral_0^R (-w')F.        (H5)

Thus F>=0 on the whole interval suffices for a nonnegative weighted integral,
even if h is sometimes negative. This explicitly includes the endpoint term.

EXACT THETA PREFLIGHT: use h=h_c from H4. Then

    F_c(R)=integral_0^R h_c(s) ds=A R^2/2+o(R^2)<0         (H6)

for every sufficiently small R>0. Therefore the unmodified sufficient
premise "every initial partial integral is nonnegative for every row" is
FALSE for theta. With w=1 and R=infinity, asking only F_c(infinity)>=0
is just the original target. Likewise assuming all tail integrals positive
already includes V[c]>=0 at tail endpoint zero. A weighted or regrouped
version would need an exact new identity and its endpoint comparison.

CONTROL: if all initial-integral matrices were PSD for the negative control
f0, their entrywise convergent limit would make V0 PSD, contradicting its
known negative row. Positive individual matrix entries cannot replace the
all-row cumulative premise. Verdict: source-verified mechanism; this direct
prefix-positive fit is excluded, not Abel integration in general.

## 4. Nonlocal ground-state identity: compensate across pairs of points

Primary source: R. L. Frank and R. Seiringer, *Non-linear ground state
representations and sharp Hardy inequalities*, arXiv:0803.0503v2,
[HTML](https://arxiv.org/html/0803.0503v2), section 2.1, Assumption 2.1,
Proposition 2.3 (2.5), proof (2.17)-(2.19).
Short quote: "If p = 2, then (2.5) is an equality".
Fetched HTML SHA256: 7bb71219df750fc62cccc14fa784ae0e5ea736799de1b85807a8f25c9af8d9d1.

Here is the p=2 mechanism with exact normalization, first in the absolutely
integrable regime on the source's Euclidean domain. Let k(r,s)=k(s,r)>=0,
omega>0, and define the potential by the source equation

    U(r)omega(r)=2 integral (omega(r)-omega(s))k(r,s) ds.

For complex u=omega v, symmetrization and expansion give

    integral integral |u(r)-u(s)|^2 k(r,s) dr ds
      -integral U(r)|u(r)|^2 dr
    =integral integral omega(r)omega(s)|v(r)-v(s)|^2
                        k(r,s) dr ds >=0.                 (H7)

There is NO factor 1/2 in the double integrals; the source equation has
factor 2. The algebra is exactly

    |a v-b w|^2-(a|v|^2-b|w|^2)(a-b)=ab|v-w|^2

for a,b>0 and complex v,w. Signed terms meet their partners before the
nonnegative square appears. Singular kernels require the paper's symmetric
truncations and potential convergence plus its energy/domain hypotheses;
those limits cannot be assumed for a proposed theta model.

The HTML display defining E_omega appears to repeat omega(x) in both slots.
We do not silently rely on that display: the two different weights in H7
follow from the explicit algebra above and proof (2.17)-(2.19).

THETA MAP STILL UNPAID: construct k, omega, U and a linear map c -> u_c
from the full source, verify the source equation, and identify the WHOLE
V[c] with H7 (or H7 plus independently nonnegative terms), with all domain,
integrability, half-line/exterior and boundary terms. Taking omega=f alone
does not supply this. The previously tested local energy
integral |P'-(f'/f)P|^2 is not V: at x=0 it vanishes for P=f, whereas
V(0,0)>0. That endpoint is a diagnostic limit, not an allowed isolated node.

CONTROL: the positive even f0(u)=exp(-u^2)-exp(-2u^2)/4 has strict concavity
of log f0(sqrt(s)) but negative four-node V0. The conjunction of exact
identification, positive k, source equation and valid domains cannot hold
for it. Without a concrete k there is no basis to claim WHICH premise
fails. Verdict: verified compensation template; actual theta fit UNVERIFIED.

## 5. Fourier energy: keep the cutoff before testing the sign

Primary source: T. Tao, *245C, Notes 2: The Fourier transform* (2009),
[lecture notes](https://terrytao.wordpress.com/2009/04/06/the-fourier-transform/).
Locators: Exercise 14, equation (5) (convolution); Exercise 29 (multiplication
and differentiation); Theorem 43 and preceding Parseval identity (L2).
Short quote, Theorem 43: "can be uniquely extended to a unitary transformation".
Fetched HTML SHA256: 1ee4827784ca788bfe5bd43925abb3994466f594a54811e8f9a3b19904bfb5cd.

Use angular frequency omega: hat g(omega)=integral g(t)exp(-i omega t)dt;
Tao's variable is xi=omega/(2pi). A real even integrable convolution kernel
k with hat k>=0 gives, for Schwartz g,

    integral conjugate(g)(k*g)
      =(1/(2pi))integral hat k |hat g|^2 >=0.              (H8)

The time-domain kernel need not be positive. For example, direct integration
for k(t)=exp(-|t|)cos(b t), b nonzero, gives

    hat k(omega)=1/(1+(omega-b)^2)+1/(1+(omega+b)^2)>0.

Thus H8 is a concrete integral compensation example with a sign-changing
kernel. Its operative hypothesis is the spectral sign, not Plancherel alone.

For the actual target define zero-extended half-line profiles

    P_c(t)=1_(t>=0) sum_i c_i f(t+x_i),
    Q_c(t)=1_(t>=0) sum_i c_i (t+x_i)f(t+x_i).

Both are in L1 intersect L2, with the needed moments, by the full-source tail.
Parseval yields exactly

    V[c]=(1/pi) Re integral conjugate(hat P_c)hat Q_c.      (H9)

This is a cross product, not yet a positive square. For each node put

    A_x(omega)=exp(i omega x) integral_x^infinity f(u)exp(-i omega u)du
      =exp(i omega x)[F_+(omega)-integral_0^x f(u)exp(-i omega u)du],
    F_+(omega)=integral_0^infinity f(u)exp(-i omega u)du,
    B_x(omega)=exp(i omega x) integral_x^infinity u f(u)exp(-i omega u)du
             =i partial_omega A_x(omega)+x A_x(omega).     (H10)

For x<0 the integral from 0 to x is oriented. Omitting it changes the form.

BOUNDED PREFLIGHT: no single scalar Fourier multiplier m(omega) can obey
B_x=m A_x almost everywhere for every x in any open node interval. This
holds even for Gaussian f, so it excludes this unnecessarily rigid map,
not the general Fourier route. Proof: at omega=0 define

    T0(x)=integral_x^infinity f(u)du>0,
    T1(x)=integral_x^infinity u f(u)du, mu(x)=T1(x)/T0(x).

Positivity of f and its finite moments give

    mu'(x)=f(x) integral_x^infinity (u-x)f(u)du / T0(x)^2>0. (H11)

For any two distinct nodes A_x and B_x are continuous, and A_x is nonzero
near omega=0. A common multiplier would make their continuous ratios B_x/A_x
agree almost everywhere on that neighborhood, hence everywhere there. At
zero this contradicts H11. This uses continuity, not a claim based only on
one measure-zero frequency. In the Gaussian case f=C exp(-b u^2), b>0,

    B_x=(f(x)-i omega A_x)/(2b),

so an explicit endpoint term explains the failure of the multiplier ansatz
despite known positivity of the full Gaussian form. A valid theta spectral
construction must retain the cutoff terms, or justify a different domain
or augmented transform. No positive multiplier for H9 has been constructed.

## 6. What theta structure was checked, and the remaining useful question

Evenness from theta reciprocity has already paid the exact odd cancellation
in H1. Squared-coordinate log-concavity pays H2, including every two-node
layer. Full differentiated theta tails, with controlled higher modes, enter
L13: its obstruction is not a first-mode numerical surrogate. The Fourier
cutoff is explicit in H10. No omitted theta mode or dropped boundary was
found that reverses these conclusions. This is not a claim that every
possible theta identity has been exhausted.

Joint additive total positivity of the underlying density and its reciprocal
identity remain candidate extra structure; their transfer to this shifted,
cutoff form has not been supplied. They cannot make the fixed K_s PSD in
conflict with L13. They might instead help construct a different full-form
identity, but that is a hypothesis to test, not a consequence of their names.

The hunt therefore identifies a concrete target for the next CONSTRUCTION:
an exact two-point energy or augmented transform that pays the cutoff and
weight terms for every finite row. Before an all-rank sign claim, exhibit
its source-defined kernel/map and the full boundary identity. Then test its
hypotheses against f0. The map cannot be defined as the positive square root
of V or selected separately after seeing the sign of each coefficient row.

Completed here: three primary-source mechanism cards; H2-H3 legitimate
partial signs; H6 exclusion of direct prefix positivity; H9-H11 exact
Fourier cutoff and common-multiplier obstruction. These clarify the missing
transfer but give no new lower bound for the full theta V. No numerical
quadrature, finite-rank sweep, Lean closure or new Proshka request was used.
