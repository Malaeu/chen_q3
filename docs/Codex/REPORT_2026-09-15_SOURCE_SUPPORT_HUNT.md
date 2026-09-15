# Exact xi multiplier and the remaining unweighted stability problem

STATUS: ANALYTIC_CANDIDATE_PENDING_INDEPENDENT_REVIEW.
FULL_V / IC / ODD2 / RH: OPEN. PX_RH_CLAIM: NOT_MADE.
CONSUMPTION: INCOMPLETE_NO_CONSUMABLE_TARGET; owner-authorized isolated research.
BASE: d375efb4a755d5bcf3f65ae4392bdc6e40768310.

## 1. Locked input and discovery boundary

The accepted FULLVPOS raw response is
`docs/routeB_bus/proshka/PROSHKA_RESPONSE_GOAL058_FULLVPOS_2026-09-15.md`,
commit 66c0da89b5d5da291df694e7cfa1d319df1d2691, SHA256
3e51c432683640422e2052680e4c592fd39a8078f213b70ee5f1bb4c72d4a508.
Its parent intake has SHA256
8f9abe3e60ce3188709ad5b6e91022980a78bc33f70635fcb4f3fe6abb77aad6.
Keep its full theta f=Phi/A, A=||Phi||_2, I=(-log(2)/2,0), Fourier sign
exp(-izt), and all finite complex rows. In particular,

    E=F+iF', S=(F-iF')/(F+iF'), U=Fourier_inverse M_S Fourier,
    a(t)=(1+t)f(t)/sqrt(2), b(t)=(1-t)f(t)/sqrt(2), a_x(t)=a(t+x),
    U a_x=b_x, closure span{a_x:x in I}=L2(R),
    all-row V>=0 iff P+ U P-=0.                         (SUPPORT)

All real common zeros in S are removed as in the accepted response.
Unitarity on the full line is established; SUPPORT is not.

The pinned discovery brief is `BRIEF_2026-09-15_SOURCE_SUPPORT_HUNT.md`.
Three registered shelf queries (operator/support, entire-function, systems)
each returned exit 2 / ASK_STATUS INCOMPLETE because index freshness failed.
Their output SHA256 values, in brief order, are
d7be4c79a095f49cc3ff2d5de1d67a0f1fd759f6a3df86587078960eabfd3faa,
d0c2b3fc0caec54aa56a987ded38a440c8b0c5eeaad46615b84986160473e469,
eda12714ace49df9db8f75c2e2621c58699b551d0b447bca086aff37d42ab57c.
These are not absence results. No index repair or canonical admission occurred.
The local references led to Suzuki; primary sources were then read directly.

## 2. This is literally Suzuki's xi multiplier

Write theta_0(t)=sum_(n>=1) exp(-pi n^2 t). With t=exp(2u),
Phi(u)=t^(5/4)[4t theta_0''(t)+6 theta_0'(t)]. Put s=1/2-iz.
For Re s>1, change variables in the full Fourier integral and integrate
twice by parts:

    integral_R Phi(u) exp(-izu)du
      = integral_0^infinity [2t^(s/2+1)theta_0''+3t^(s/2)theta_0']dt
      = [2(s/2)(s/2+1)-3s/2] Gamma(s/2) pi^(-s/2) zeta(s)
      = xi(s).

Here xi(s)=s(s-1)Gamma(s/2)pi^(-s/2)zeta(s)/2.
The endpoint terms vanish in Re s>1: theta_0(t)=O(t^(-1/2)) and
theta_0'(t)=O(t^(-3/2)) near zero, and both decay exponentially at infinity.
The Mellin integral follows by absolute summation in this same half-plane.
The full theta Fourier transform and xi are entire, so the identity extends.
Consequently, with no unrecorded factor of two,

    F(z)=xi(1/2-iz)/A,
    E(z)=[xi(s)+xi'(s)]/A,
    S(z)=[xi(s)-xi'(s)]/[xi(s)+xi'(s)].                 (S1)

This agrees exactly with Suzuki's E_xi#/E_xi, using xi(s)=xi(1-s).
In [S], p.2, equations (1.3)-(1.4) give the same functions. Theorem 1.1
begins: "Assume that the RH holds." Its Hilbert-space isomorphism and the
preceding Hermite-Biehler assertion therefore cannot supply unconditional
SUPPORT. This is a verified exact object match, not a proof of its positivity.

## 3. An unconditional weighted realization of our source transfer

Let R(s)=xi'(s)/xi(s). Lagarias [L], introduction (1.4), gives

    Re R(s)>0 for Re s>1.

The same page (1.5) identifies extension to Re s>1/2 with RH. Its short
description is: "the Riemann hypothesis is equivalent to the positivity condition".
Only these introductory facts are imported, not the paper's later bounds.
They also follow in the first half-plane by logarithmically differentiating
the conjugate-paired xi product: every zero has Re rho<1, each
Re(1/(s-rho)) is positive, and the paired series converges locally.

Since S=(1-R)/(1+R), (1.4) implies S is holomorphic and |S|<1 on
Im z>1/2. Fix any v>1/2. Then S_v(z)=S(z+iv) is Schur on Im z>0.
The Hardy multiplier theorem, in the Fourier convention of the accepted
intake, gives a contraction C_v on H=L2(R):

    C_v=Fourier_inverse M_(S(omega+iv)) Fourier,
    C_v(H-) subset H-.

This last orientation matters: exp(-izt) identifies H- with upper-half-plane
Hardy boundary values. The full theta tails make e^(vt)a and e^(vt)b
Schwartz. Their Fourier transforms are E(z+iv)/sqrt(2) and
E#(z+iv)/sqrt(2), hence

    C_v(e^(vt)a)=e^(vt)b.

Define H_v=L2(R,e^(2vt)dt), J_v h=e^(vt)h, and

    T_v=J_v^(-1) C_v J_v : H_v -> H_v.                 (W1)

It is a contraction in H_v, preserves negative support, and T_v a_x=b_x
for every real x. Indeed, J_v a_x=e^(-vx)(J_v a)(t+x), and C_v commutes
with real translations. This is an unconditional realization using the
actual full source. It controls the weighted norm, not the required L2 norm.
It supplies no lower bound or positive budget for V.

## 4. The exact bridge to the original norm

A sufficient next lemma, for one fixed v>1/2, is a finite constant M with

    T_v h belongs to L2(R),
    ||T_v h||_2 <= M ||h||_2 for every h in C_c^infinity(R).    (W2)

W2 is UNPROVED. Its conclusion would be decisive, as follows.
It extends T_v uniquely from these tests to a bounded W on unweighted H.
Approximate each a_x by smooth cutoffs in both H and H_v. Their outputs
converge in H to W a_x and in H_v to b_x. Both convergences imply local
L2 convergence, so W a_x=b_x. By the accepted density, W=U on H.
Negative-support compact smooth tests have negative-support outputs by W1;
their density in H- and boundedness imply W(H-) subset H-. Thus W2 implies
SUPPORT and the exact original all-row V>=0.

This is boundedness of a specific transfer in the original norm. It is not
the excluded strengthening V>=C E_NULLFIELD. No positive coercivity or
simple-zero assumption is added. Nevertheless, W2 must be proved from the
source, not renamed "stability" and assumed. A bound merely on the finite
span of a_x is already automatic from Ua_x=b_x and does not prove W2 on
compact supported tests: the two topologies are the missing issue.
Nor does the H_v bound let v tend to zero; the known range is v>1/2.

The old negative source f0=exp(-t^2)-(1/4)exp(-2t^2) has B0!=0 by FULLVPOS.
It rules out a matching bounded, support-preserving unweighted extension.
We do NOT assert that this f0 satisfies the shifted Schur premise used in W1.
For the positive Gaussian, the accepted explicit one-sided convolution
already supplies the unweighted operator. These controls separate support,
norm and source hypotheses without changing the target.

## 5. A second classical mechanism: independent passive realization

Ball et al. [B], Theorem 1.1, pp.1-2, give the one-variable equivalence between
a Schur function and a contractive connecting operator. The source wording is
"There exists a Hilbert space H and a coisometric (or even unitary or contractive) connecting operator".
For our problem set q(w)=S(i(1+w)/(1-w)), |w|<1. An independently constructed
contraction K=[[A_c,B_c],[C_c,D_c]] with

    q(w)=D_c+w C_c(1-w A_c)^(-1)B_c

would suffice. For x=(1-w A_c)^(-1)B_c u and y=q(w)u,
K[wx;u]=[x;y], so contractivity gives
(1-|w|^2)||x||^2+||y||^2<=||u||^2. Hence q is Schur and SUPPORT follows.
The input/output spaces here are scalar complex spaces; the state space
and its positive inner product must be supplied independently from theta.
The already unitary full-line U does not automatically supply such a K
with this exact transfer. Constructing K from assumed Pick-kernel positivity
would put the desired sign back into the premise. Exact theta fit: UNVERIFIED.
The negative f0 cannot have such a matching contractive realization.

The shelf also contains Suzuki's different shifted quotient family [S2].
It was inspected as a nearby lead, not identified with S1. No Hamiltonian,
parameter limit, or theorem for that different family is imported here.

## 6. Source ledger and decision

- [S] Masatoshi Suzuki, *On the Hilbert space derived from the Weil distribution*,
  https://arxiv.org/abs/2301.00421, local PDF v3; pp.1-3, especially p.2
  (1.3)-(1.4), Theorem 1.1. PDF SHA256
  e4100e529d74cdc4dfa855aa24bcf34a88562d9facebefd70de6e529f9a1ce2e.
  Existing shelf: docs/routeB_bus/litreview/pdfs/2301.00421.pdf.
- [L] Jeffrey C. Lagarias, *On a Positivity Property of the Riemann xi-Function*,
  https://websites.umich.edu/~lagarias/doc/positivity.pdf, introduction,
  PDF page 2, equations (1.1)-(1.5). PDF SHA256
  b497dd6cdad46a31e8d6b2a199906e9020d96666715b0bcb24e780a36b2a3f42.
  Text extraction has broken font encoding; the rendered page was read visually.
- [B] Ball, Biswas, Fang, ter Horst, *Multivariable generalizations of the Schur
  class: positive kernel characterization and transfer function realization*,
  https://arxiv.org/abs/0705.2042, Theorem 1.1, pp.1-2 (classical one variable).
  PDF SHA256 34b63b910628595af152f354d448c3da4837a18d2043174735b674f172e3eebc.
- [S2] Suzuki, *A canonical system of differential equations arising from the
  Riemann zeta-function*, https://arxiv.org/abs/1204.1827; distinct-family lead.
  Existing shelf PDF SHA256
  2c4cf2aa7a5bca731e0f1ac356deaa082eb6137a07c465fdfe09198acc82ef38.

New downloaded sources, rendered pages and query receipts are outside the
repository in this task's source-support-hunt-20260915 evidence directory.
No claim to have read the entire papers. The imported equations and theorem
statements, including the Suzuki and Ball formula pages, were checked directly.

Decision: use W1 as the explicit known starting point; ask the coauthor for
a source-based proof of W2 or its first precise analytic obstruction. Do not
retry the RH-conditional Suzuki theorem as if it were an unconditional input.
The passive realization is a mapped alternative, not another launched model.
This hunt completed a normalization and weighted-source transfer; the full
sign remains open. No source-sign counter reset, historical counter rebuild,
Lean substitution, numerical sweep, or claim of RH closure.
