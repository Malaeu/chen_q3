# Full V: independent intake of the two-shift sign proof

STATUS: ACCEPTED_PAPER_FULL_V_RAW_TWO_SHIFT_POSITIVITY_AND_CONTROL.
SOURCE_BASE: 7214ab0ae955ad7b84e0fb1760a525b3e538ac77.
CONSUMPTION: ISOLATED_PAPER_ONLY; canonical theorem/consumer remains unbound.
CLAIM: all actual full-theta two-node V matrices are positive definite for
distinct real nodes, positive semidefinite when nodes coincide.
FULL_ARBITRARY_RANK_V / GLOBAL_IC / GLOBAL_ODD2 / RH: OPEN.
ACTUAL_THETA_NEGATIVE_WITNESS: NONE. PX_RH_CLAIM: NOT_MADE.

## 1. Provenance and source verification

Input: the owner's pasted Proshka argument, sections 1--7, in this conversation.
The linked sandbox artifact PROSHKA_FULL_V_RANK_TWO_EXCLUSION_2026-09-14.md
was not accessed. No byte-exact intake of that unseen file is claimed.
The authorized GitHub branch was checked at SOURCE_BASE and had no newer
commit at intake. This is our independent derivation and audit of the visible
argument, not a claim that Proshka published the unseen artifact to GitHub.

Full source and V definitions were rechecked against:

- docs/routeB_bus/proshka/PROSHKA_RESPONSE_GOAL058_NULLVAR_2026-09-13.md,
  equation (1), SHA256 4fa7909725d2fa10ccc52d3413580289692d3a1489ecae7bed88956f80980730;
- docs/Codex/REPORT_2026-09-13_NULL_AND_GROUND_STATE_TEST.md, T1 and G1,
  SHA256 19ce3481523bfb3f3f9ba8be24f2c86dc2f1916d80f9535a451d010bceef0d95.
The existing local CSORDAS_PLANAT_LOGCONCAVITY_USAGE_CARDS.md was read; it
already documented the relevant 2015 restatement and the variable scaling.

Original published input verified directly:
G. Csordas and R. S. Varga, "Moment Inequalities and the Riemann Hypothesis",
Constructive Approximation 4 (1988), 175--198, Theorem 2.1, printed p178;
source definition (1.2), printed p175.
DOI: https://doi.org/10.1007/BF02075457
Author-hosted PDF: https://www.math.kent.edu/~varga/pub/paper_161.pdf
PDF: 2132541 bytes, 24 pages, SHA256
fd43597072010242ef5b8a75480e263a1538df0aba47755c47e137b140cf01ce.

Printed pp175--178 were rendered and visually read. This scanned PDF yielded
no useful pdftotext text. The theorem statement and source formula were
checked on the rendered pages; no full independent reproving of section 3
of that article is claimed. We use an explicitly named published theorem.

Short quote, Theorem 2.1: "is strictly concave".
The interval in the statement is (0,infinity).

The article defines

    Phi_C(r)=sum_(n>=1) [2pi^2 n^4 exp(9r)-3pi n^2 exp(5r)]
                              exp(-pi n^2 exp(4r)).

Termwise substitution gives EXACTLY

    Phi_ours(u)=2 Phi_C(u/2), f=Phi_ours/A, A=||Phi_ours||_2,
    ell(s)=log f(sqrt(s))=log(2/A)+log Phi_C(sqrt(s/4)).      (R1)

Theorem 2.1 proves strict concavity of the last source function for s>0.
Only strict concavity, not a generic inference that every strictly concave
C2 function has a strictly negative second derivative everywhere, is needed
in the proof below. Positivity and even smoothness of the actual f extend
ell continuously to s=0.

Registered shelf query:
"Csordas Varga squared coordinate log concavity full V two shifts".
It returned exit 2, INCOMPLETE / q3_docs semantic-index freshness failure.
The retained exact receipt is in the accompanying JSON. No absence verdict,
index repair or canonical admission is inferred.

## 2. Exact integration change and the two-node theorem

For the positive even full source, retain

    V(x,y)=int_0^infinity (2t+x+y) f(t+x) f(t+y) dt,
    D(x)=V(x,x).

These integrals are absolutely convergent by the full-source derivative/tail
bounds in the pinned reports. Fix any real x,y, and put m=(x+y)/2, d=(x-y)/2.
The function u f(u+d)f(u-d) is odd and integrable on R. Therefore

    V(x,y)=2 int_m^infinity u f(u+d)f(u-d) du
          =2 int_|m|^infinity u f(u+d)f(u-d) du > 0.        (R2)

There is no discarded boundary term: the interval [m,-m] cancels when m<0.
Let s=u^2-m^2 in the final positive half-line integral. Then

    V(x,y)=int_0^infinity f(sqrt(s+m^2)+d)
                           f(sqrt(s+m^2)-d) ds,
    D(x)=int_0^infinity f(sqrt(s+x^2))^2 ds > 0.             (R3)

Write rho(s)=f(sqrt(s)). The two squared arguments in the first integrand
have sum 2(s+m^2+d^2) and half-separation 2|d|sqrt(s+m^2).
The comparison pair s+x^2, s+y^2 has the same sum and half-separation
2|d||m|. Thus the first pair is more separated.

For a concave function ell, ell(z+r)+ell(z-r) is nonincreasing in r>=0
when both arguments are in its domain. This follows directly by expressing
the less separated pair as strict convex combinations of the more separated
pair. Strict concavity makes the inequality strict when the separations
differ and the arguments are positive. Continuity covers zero endpoints.

Apply this with ell=log rho. By evenness of f,

    f(sqrt(s+m^2)+d) f(sqrt(s+m^2)-d)
      <= rho(s+x^2) rho(s+y^2).                            (R4)

If x!=y, then d!=0, and for s>0 the separations differ strictly. In particular,
on any positive-length interval with s>max(0,d^2-m^2), all four squared
arguments are positive, so R4 is strict there. Integration followed by
Cauchy--Schwarz gives

    0 < V(x,y) < G(x,y) <= sqrt(D(x)D(y)),                  (R5)
    G(x,y)=int_0^infinity rho(s+x^2)rho(s+y^2) ds.

No equality analysis for Cauchy--Schwarz is needed: the first strict inequality
already provides the strict determinant. Hence

    D(x)D(y)-V(x,y)^2>0  whenever x!=y.                     (R6)

All-real-node theorem: for x!=y and (c1,c2)!=(0,0),

    V[c1,c2]
      =D(x)|c1+V(x,y)c2/D(x)|^2
        +[D(y)-V(x,y)^2/D(x)]|c2|^2 > 0.                  (R7)

This includes every complex phase. At x=y the form is
D(x)|c1+c2|^2>=0. Repeated nodes in any family can be combined first.
Therefore any actual negative finite V row must involve at least THREE
distinct nodes with nonzero combined coefficients.

This is an actual-source sign-family result. It is not a new proof of the
published input R1, and no priority/novelty claim about R2--R7 is made.

## 3. Exactly why the Gram comparison stops at this point

G is a genuine Gram kernel in L2([0,infinity),ds), via x -> rho(s+x^2).
But E=G-V has E(x,x)=0 and E(x,y)>0 for x!=y. On any two distinct nodes its
matrix is [[0,e],[e,0]], with eigenvalues e,-e. Thus E is indefinite.

Consequently entrywise V<=G does not give a Loewner-order comparison of
the full forms. Neither E>=0 nor V>=G nor a positive-residual transfer is
established. One must retain

    V[c]=||sum_i c_i rho(s+x_i^2)||_2^2 - E[c].              (R8)

This does not conflict with R7: R7 bounds one mixed coefficient relative to
its two diagonal coefficients. The signs of all mixed coefficients in an
arbitrary row need a joint bound.

## 4. Exact audit of the non-theta counterexample

Let f0(u)=exp(-u^2)-(1/4)exp(-2u^2). It is positive, even, entire and rapidly
decreasing; f0'(u)=-2u exp(-u^2)[1-(1/2)exp(-u^2)]<0 for u>0.

For s>=0,

    log f0(sqrt(s))=-s+log(1-(1/4)exp(-s)),
    its second derivative
      =-[(1/4)exp(-s)]/[1-(1/4)exp(-s)]^2<0.               (R9)

The general argument R2--R7 therefore proves all its two-node matrices
positive definite for distinct nodes. It is explicitly NOT the theta source.

For its kernel V0 define J_mn=partial_x^m partial_y^n V0(0,0).
Differentiation under the integral is valid locally with Gaussian polynomial
domination, and the product rule gives

    J_mn=int_0^infinity [
       2t f0^(m)(t) f0^(n)(t)
       +m f0^(m-1)(t) f0^(n)(t)
       +n f0^(m)(t) f0^(n-1)(t)] dt.                       (R10)

Every term reduces to odd powers times exp(-a t^2). The companion script
RANK_TWO_CONTROL_JETS_20260914.py uses ONLY exact Fraction arithmetic,
the polynomial derivative rule (p exp(-a t^2))'=(p'-2atp)exp(-a t^2), and

    int_0^infinity t^(2k+1)exp(-a t^2)dt=k!/(2a^(k+1)).

Its executed exact result, independently matching the pasted values, is

    [J11 J13; J31 J33]=[1/18 -25/54; -25/54 100/27],
    det J=-25/2916,
    (25/3,1) J (25/3,1)^T=-25/162<0.                      (R11)

No numerical quadrature, theta samples or floating point is involved.

To convert jets to allowed finite rows, define on smooth functions

    L_h g=(g(-h)-3g(-2h)+3g(-3h)-g(-4h))/h^3
                +(25/3)(g(-h)-g(-2h))/h.

Taylor expansion gives L_h -> partial^3+(25/3)partial as h->0+.
The script verifies the exact zeroth through third cancellation moments.
The locally analytic kernel V0 has continuous mixed derivatives of sufficient
order, so applying the finite-difference limit in both arguments is legitimate:

    L_h^(x) L_h^(y) V0(x,y) -> -25/162.                     (R12)

These are exactly the four nodes and coefficients in the pasted argument.
For sufficiently small h>0 this is a negative FINITE row; moreover
h<(log 2)/8 places all four nodes in I=(-(log 2)/2,0).
No explicit certified numeric h is claimed. The witness is an analytic
existence result for f0, never a negative witness for theta.

## 5. Independent check of the added double-exponential-tail claim

The unseen producer file is not a premise for this section. An explicit
construction of our own verifies the claim stated in the pasted summary:

    f_delta(u)=f0(u) exp[-delta cosh(2u)], delta>0.           (R13)

It is positive, even, entire, decreasing for u>0, and has double-exponential
decay on the real axis. Since

    cosh(2sqrt(s))=sum_(k>=0) 4^k s^k/(2k)!,

its second s derivative is positive on s>=0. Thus R9 minus
delta cosh(2sqrt(s)) is still strictly concave.

For derivative orders j<=3 and 0<delta<=1, differentiating the extra factor
produces finite sums bounded by C_j exp(2j|u|), since
exp[-delta cosh(2u)]<=1 and delta<=1. With f0 and its Gaussian derivatives,
all terms in R10 have an integrable common bound
C(1+t)^M exp(12t-2t^2) on t>=0.
Dominated convergence gives J_delta -> J0 as delta->0+.
The fixed vector in R11 therefore still has negative jet energy for all
sufficiently small positive delta. Fix such a delta and apply R12 to its
smooth kernel to obtain a negative four-node finite row inside I.

Thus strict squared-coordinate log-concavity, positivity, evenness and
double-exponential decay together STILL do not imply all-rank V positivity.
This is a control on hypotheses, not a deformation theorem about actual theta.

## 6. Updated mathematical frontier and connection to the prior test

Raw two shifts here must not be confused with ODD2. The latter uses TWO odd
profiles, each a difference of +x and -x translates: normally FOUR raw nodes.
This distinction is verified in REPORT_2026-09-12_ODD2_COMPACT_LOCALIZATION.md,
especially the four-node interpretation following (9). Full ODD2 remains open.

The earlier FIRST_ORDER_COMPENSATION_PREFLIGHT report excludes a particular
POINTWISE local storage using (P,P'). R2--R7 perform a full integrated
comparison instead. They do not contradict that scoped obstruction.

The next unknown raw size is three. Its normalized determinant is precisely

    1+2 r12 r13 r23-r12^2-r13^2-r23^2,                      (R14)
    rij=V(xi,xj)/sqrt(D(xi)D(xj)) in (0,1).

R14 is not proved here for theta. Even all triples would not prove all ranks.

For a fixed pivot a, completing one square leaves the kernel

    S_a(x,y)=V(x,y)-V(x,a)V(a,y)/D(a).                      (R15)

R6 pays S_a(x,x)>0 for x!=a. All-rank closure would require the full S_a
to be positive semidefinite, not merely its diagonal. R2--R7 do not show
that S_a retains the source representation or concavity comparison needed
to repeat this argument. That preservation, or an independent whole-kernel
bound, is the exact missing interface. It is not asserted to exist.

## 7. Verification, evidence and decision

Parent: original published theorem and source normalization checked visually;
all transformations, strictness, complex coefficients, Gram-order obstruction,
exact rational jets, finite-difference limit and R13 domain proof checked.

Artifacts:

- this intake;
- docs/Codex/certificates/RANK_TWO_CONTROL_JETS_20260914.py, SHA256
  a7a45f81c969ac8e0e786c71dc73d53f2cd9849a631f7adb18997b92ba91b95f;
- same prefix .json, SHA256
  fed9520a4b0c5e155a99937572f1de9e5c858991db786e7dc59f0e9f924d020e.
The JSON retains exact output, named-source evidence and the incomplete shelf
receipt. Raw PDF/renders/shelf output are retained in the owned external
rank-two-intake evidence directory, not added to the source repository.

The independent read-only checker /root/sibling5_check returned CLEAN on
the exact full draft SHA256
ccefc3df9652a95085ceb9d89fe3976358f0eed2cbfa964023cabe2caa7c625d.
The checker confirmed source normalization, strictness and all complex rows,
the Gram-order boundary, executed exact jets, finite differences, R13 dominated
convergence, and RAW2 versus ODD2. Only acceptance metadata and formatting
were added afterward; all mathematical formulas and proofs are unchanged.
No Lean certification or canonical node close is claimed.
The actual two-shift negative-witness search is excluded by R7.
This is new accepted family progress relative to the preceding local
obstruction, not an all-rank sign theorem. Historical failed attempts are not
deleted and no progress percentage for RH is inferred.
