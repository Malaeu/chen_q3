# Hardy cancellation: an exact sibling and the theta mismatch

STATUS: ANALYTIC_PAPER; independent review recorded in the adjacent receipt.
DISCOVERY: one SOURCE_VERIFIED_PARTIAL_MECHANISM; application derived below.
CONSUMPTION: INCOMPLETE_NO_CONSUMABLE_TARGET; canonical theorem/consumer edge unbound.
SOURCE_BASE: fe1044cb45356fff684fc99c042a2354bfad17fd.
SCOPE: one explicit common map, Gaussian fit and actual full-theta mismatch.
No numerical sign search, Lean verification, canonical admission or RH claim.

## H0. The question in plain language

Linux has already expressed the remaining energy as the energy of centered
A signals minus the energy of B signals. We need a single rule that sends
every centered A to its corresponding B without increasing energy, including
every mixture of signals. Rules separately chosen for each mixture do not
prove this. A familiar rule from Hardy averaging supplies the right energy
identity; the issue is whether it produces the right B.

    centered A -- one energy-preserving Hardy map --> output
                                                       |
    Gaussian: output = B                    theta: B = output + e

The Gaussian identity is exact. For theta the error e is exact and demonstrably
nonzero. Its joint energy contribution remains unpaid. This is a worked
transfer and a scoped exclusion, not progress in the sign of full theta V.

Inputs and source hashes are in the accompanying search receipt. The Linux
anchored note's original DRAFT header is retained in its immutable bytes; its
separate V2 review is the evidence for reading its conclusions as reviewed
paper mathematics. Neither file supplies canonical admission.

## H1. Freeze the actual object

Use f=Phi/||Phi||_2, the full positive even theta source. Simultaneous reflection
allows nodes x in J=(0,log(2)/2). Fix a in J, put u=t+a>=a and delta=x-a. Set

    V(x,y)=integral_0^infinity (2t+x+y)f(t+x)f(t+y)dt,
    D(u)=V(u,u)=2 integral_u^infinity v f(v)^2 dv,
    dmu(u)=2u f(u)^2 du / D(a),
    r_x(u)=f(u+delta)/f(u),
    A_x(u)=(1+delta/(2u))r_x(u),
    B_x(u)=delta r_x(u)/(2u),  U_x=A_x-E_mu A_x.

All profiles are in L2(mu): u>=a>0 and the denominator f(u)^2 cancels
against the measure, leaving a finite weighted tail of f(u+delta)^2.
Let U_c=sum c_i U_(x_i), B_c=sum c_i B_(x_i), with arbitrary finite complex c.
The already established anchored identity is

    S_a(x,y)=V(x,y)-V(x,a)V(a,y)/D(a),
    S_a[c]/D(a)=||U_c||_mu^2-||B_c||_mu^2.                 (H1)

The exact target is nonnegativity for all finite families and all complex c.
The strict positive definiteness of the centered A Gram matrix on distinct
non-anchor nodes does not compare it with the B Gram matrix.

## H2. Source-verified mechanism card: Hardy cancellation

Primary source: Jean-Francois Burnol, *A lower bound in an approximation
problem involving the zeros of the Riemann zeta function*, arXiv:math/0103058v2,
Section 3, printed page 7, first paragraph. Published in Adv. Math. 170 (2002).
URL: https://arxiv.org/pdf/math/0103058v2 .

Local source: docs/routeB_bus/litreview/pdfs/survey_2026-09-03_sources/burnol_2002.pdf.
PDF SHA256: 999f05d5045fd909c3fb985677c4e40459f2a8b1e8b7d932f34b35bdc52d6e7d.
Text SHA256: 8769bb3889126610ba2cdd5bd1ee7f56fe245a673dafde6e816c5c41f11aafed.
Text locator: lines 349--353. Verbatim conclusion about 1-M: "is thus unitary."
PDF line wraps are normalized to spaces in this short quotation.

Here M h(z)=z^(-1) integral_0^z h(s)ds on L2((0,infinity),dz).
Burnol identifies the Mellin multiplier of I-M as s/(s-1), of modulus one on
Re(s)=1/2. This particular operator fact uses no assumption about zeta zeros.
It is the only newly applied external operator fact; the probability transport,
finite-interval boundary accounting and source fits are our derivations.

For any h in L2(0,1), extend h by zero to the full positive line, calling
the extension h0. For z>1,

    (I-M)h0(z)=-(integral_0^1 h(s)ds)/z.

The unitary identity and integral_1^infinity z^(-2)dz=1 give

    ||(I-M)h||_(0,1)^2
        =||h||_(0,1)^2-|integral_0^1 h|^2.                (H2)

This proof applies to every complex L2 function, not just smooth functions.
In particular it retains the removed mean as an exact exterior tail energy.
There is no unproved integration-by-parts boundary at infinity.

Transport to any strictly positive continuous probability density m on
[a,infinity) using its survival function H(u)=integral_u^infinity m(v)dv.
The substitution z=H(u) carries m(u)du to dz on (0,1). Under this isometry,

    (R g)(u)=H(u)^(-1) integral_u^infinity g(v)m(v)dv

is precisely M, and W=I-R obeys

    ||Wg||_mu^2=||g||_mu^2-|E_mu g|^2,
    W1=0,  ||WU||_mu=||U||_mu whenever E_mu U=0.         (H3)

Thus W is one explicit linear contraction on L2(mu), and an isometry on its
centered subspace. Its output need not have zero mean. Boundedness of R also
follows, with ||R||<=2. None of these statements assumes positivity of V.

Hypothesis map:

| Requirement | Actual theta | Gaussian | Non-theta control f0 |
|---|---|---|---|
| Positive continuous probability density on u>=a>0 | PROVED | PROVED | PROVED |
| Each A and B lies in the same L2(mu) | PROVED | PROVED | PROVED |
| Centered input U and all finite complex mixtures | PROVED | PROVED | PROVED |
| WU_x equals prescribed B_x | FALSE for x!=a by equation (H8) in section H6 | PROVED in section H5 | Cannot supply the all-row target |
| Some independently constructed contraction sends every U_x to B_x | OPEN | W suffices | FALSE for the whole required class |

Strength: a source-verified general mechanism with an exact Gaussian fit and
an explicitly failed direct theta fit. VERIFIED discovery does not mean that
the target inequality has been proved.

## H3. Exact map into the anchored theta formulas

For our measure, H(u)=D(u)/D(a). Define

    N_delta(u)=integral_u^infinity
                     (2v+delta)f(v)f(v+delta)dv
              =V(u,u+delta).

Direct substitution into R, with no differentiation, gives

    R A_x(u)=N_delta(u)/D(u).

As W kills constants, WU_x=A_x-R A_x. Since B_x=A_x-r_x,

    e_x(u)=N_delta(u)/D(u)-r_x(u),
    B_x=WU_x+e_x.                                        (H4)

All terms in H4 belong to L2(mu): A_x and r_x do, and R is bounded by H3.
The formula holds on the whole original half-line and for the full source.
No error is dropped at u=a. The anchor x=a gives U_a=B_a=e_a=0.

## H4. The entire error budget, with its sign still open

Use the complex inner product <g,h>=integral conjugate(g)h dmu and
e_c=sum c_i e_(x_i). Equations H1, H3 and H4 give exactly

    S_a[c]/D(a)
        =-2 Re <WU_c,e_c>-||e_c||_mu^2.                  (H5)

All arbitrary mixtures and their cross terms remain in this identity.
The needed inequality is

    2 Re <WU_c,e_c>+||e_c||_mu^2 <= 0 for every finite c. (H6)

H6 is equivalent to the original anchored target in these coordinates. It
is not a new estimate, and assigning a name to the error does not prove it.
The benefit of H4 is a concrete source-defined map and a computable formula
for its failure, against which an additional mechanism can be tested.

## H5. Worked positive sibling: Gaussian, every finite family

Take f(u)=C exp(-k u^2), C>0 and k>0, as a separate model. Then

    D(u)=f(u)^2/(2k),
    N_delta(u)=f(u)f(u+delta)/(2k),

because the derivative of f(v)f(v+delta) is
-2k(2v+delta)f(v)f(v+delta), and its tail vanishes.
Consequently e_x=0 and B_x=WU_x for every x, with the SAME operator W for
all nodes and all finite complex combinations. Therefore S_a[c]=0 exactly.
Independently, V(x,y)=f(x)f(y)/(2k), so its full Gram matrix has rank one.
These two calculations agree. This is not a fitted Gaussian correction to
theta and makes no claim that the two sources can be interchanged.

## H6. Actual full theta: the direct fit fails for every non-anchor node

The full-source tail estimate in section 5 of the Linux input is

    f(u)=C exp(9u/2) exp(-pi exp(2u))(1+o(1)), C>0.       (H7)

It includes a uniformly bounded full n>=2 series remainder, not a replacement
of f by its first summand. A fixed translate u+delta has the same estimate.
We use H7 to derive an asymptotic of exact full integrals.

For fixed lambda>0 and fixed delta, substitution z=exp(2v), followed by an
elementary exponential tail estimate, gives

    integral_u^infinity (2v+delta)exp(9v-lambda exp(2v))dv
       ~ (2u+delta)exp(9u-lambda exp(2u))/(2lambda exp(2u)).

For completeness, the transformed integral is
(1/2) integral_(exp(2u))^infinity (log z+delta)z^(7/2)exp(-lambda z)dz.
Its ratio to (log z+delta)z^(7/2)exp(-lambda z)/(2lambda) tends to one:
l'Hopital's rule applies because the logarithmic derivative of the
polynomial-logarithmic factor tends to zero. All integrands are positive
eventually. The relative o(1) in H7 is uniformly small on v>=u as u grows,
so it can be bounded above and below before integration. No limit is
exchanged with an unbounded integral without this domination argument.

Apply this with lambda=2pi to D and lambda=pi(1+exp(2delta)) to N_delta:

    D(u) ~ u f(u)^2/(2pi exp(2u)),
    N_delta(u) ~
      (2u+delta)f(u)f(u+delta)
        /[2pi(1+exp(2delta))exp(2u)].

Therefore the actual source satisfies

    (R A_x)(u)/r_x(u) -> 2/(1+exp(2delta)),
    e_x(u)/r_x(u) -> -tanh(delta),                       (H8)
    (WU_x)(u)/r_x(u) -> tanh(delta).

For x!=a the middle limit is nonzero. Since r_x>0, e_x is nonzero on an
entire far tail, hence is not the zero L2(mu) vector. This rigorously excludes
the direct identification B_x=WU_x for every non-anchor actual theta node.
The source-normalization constant cancels. This says nothing by itself about
the sign of H5: an error can either decrease or increase the total norm.

## H7. Other dictionaries: exact preflights, not additional verified candidates

1. A mean-preserving probability channel cannot be this literal map.
For any x!=a,

    E_mu U_x=0,
    E_mu B_x=delta/D(a) integral_a^infinity f(v)f(v+delta)dv != 0.

A stationary Markov operator on this same probability space, or a
conditional expectation preserving the integral, therefore cannot send
U_x to B_x. This excludes only the mean-preserving proposal. General Hilbert
contractions, including W, are not required to preserve means.

2. A plain reflecting Poisson-gradient map has an endpoint mismatch.
Write L psi=m^(-1)(m psi')' for m=dmu/du. In the proposal -L psi_x=U_x
with a C1 solution up to the endpoint and reflecting condition psi_x'(a)=0,
an output gamma(u)psi_x'(u), with gamma continuous and finite at a, vanishes
there. But B_x(a)=delta f(x)/(2a f(a))!=0. Continuous equality almost
everywhere would imply equality at the endpoint, so this precise proposal
fails. Singular prefactors, a different boundary condition, or a boundary
lift are different constructions whose energy terms would have to be paid.
This preflight does not reject the full Brascamp-Lieb or Poisson method.
Here Poisson means an equation for a potential, not theta Poisson summation.
The prior COMPENSATION_COUPLING_HUNT report, section P, remains the source
card for that method; no new result is attributed to it here.

3. Factorization/contractive interpolation is a search dictionary, not an
independent proof in this report. The Linux linear independence already
makes T0(sum c_i U_(x_i))=sum c_i B_(x_i) a well-defined algebraic assignment
on the finite span. Its norm is at most one if and only if H1 is nonnegative
on that span. Its continuous extension cannot be asserted without this
bound. No unverified Douglas citation is promoted to a candidate.

## H8. Negative control and semantic return

For f0(u)=exp(-u^2)-exp(-2u^2)/4, the probability measure and the entire Hardy
identity H3 still hold. Yet the reviewed RAW2 input supplies a negative finite
four-node V0 row, with reflected nodes in J. For any anchor in J append the
anchor to this row. Completing its positive diagonal square shows that some
Schur row is negative. Thus H6 must fail for at least one row of this control.
The universal Hardy energy identity cannot supply the missing source sign.

Keep the return point: a common tail average N_delta/D, the exact ratio
r_x, their difference e_x, and the simultaneous cross-energy with WU_x.
The plain direct fit is now FALSE for theta. A new attempt must bring an
independently justified mechanism for this joint contribution, not rename H6
or rely on separate one-node bounds. Pairwise positivity, the presence of a
positive measure, centering, and rapid tails already survive the control.

One bounded next question is to derive a source-specific identity for the
polarized error kernel

    Q_a(x,y)=<WU_x,e_y>+<e_x,WU_y>+<e_x,e_y>,

using the exact N_delta and D, and check any proposed conservation or
factorization against H8 and the non-theta control BEFORE attempting a sign
claim. This kernel is just -S_a(x,y)/D(a); it is not a new easier criterion.
Stop a next test at its first unproved source hypothesis or exact mismatch.
No further sign experiment is started by this report.

## H9. Search receipt and decision

Reused local covariance/Poisson and compensation reports before looking for
a new mechanism. The one new registered ask.sh query returned INCOMPLETE
because semantic-index freshness validation failed. This is a workflow defect,
not a no-hit or mathematical conclusion. Its full stdout and empty stderr,
hashes, query and the preserved structured receipt are in the adjacent JSON.
A scoped local text search found the Hardy paragraph in an existing primary
PDF. The arXiv abstract and exact v2 PDF were opened to verify attribution.
The web screenshot timed out; page 7 was also extracted directly from the
local PDF with pdftotext and the quoted operator statement was verified there.
No new source download, shelf mutation, index refresh, broad search, paid API,
new Proshka dispatch or runtime-policy change was performed.

RETAIN equations (H2)--(H4) as a proved source-visible transfer, equation (H5)
as exact accounting, the Gaussian fit in section H5 and the actual-theta
tail mismatch in equation (H8).
DO NOT promote these to the original all-family sign. All-rank V, full IC,
full ODD2 and RH remain open; no actual-theta negative witness is supplied.
The mathematical part of this bounded test is complete. Exact review and
publication receipts are tracked separately from the unpaid sign statement.
