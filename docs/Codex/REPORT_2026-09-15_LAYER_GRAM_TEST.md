# Exact cancellation layers: a working quartic Gram map and the theta obstruction

STATUS: ANALYTIC_PAPER; exact-payload independent review belongs to the adjacent certificate.
SOURCE_BASE: 9579d415dc05cbc54b0300b2eb8de6238da2bee4.
CONSUMPTION: INCOMPLETE_NO_CONSUMABLE_TARGET; isolated research, not canonical admission.
FULL_THETA_V / IC / ODD2 / RH: OPEN. ACTUAL_NEGATIVE_V_WITNESS: NONE.
PX_RH_CLAIM: NOT_MADE.

AUTOPSY: dropped=OBJECT_IDENTITY; note=An independent Gram representation of each fixed cancellation layer cannot exist for all sufficiently small positive layers of the full theta source; positivity after integrating the layers remains open.

## 1. Exact question and reconciled inputs

The owner asked to continue the search for a source-built common Gram map.
Test ONE proposed construction: first use the exact cancellation change of
variables already proved in RAW2, then make EACH resulting integrand a Gram
kernel. If that works, a direct integral supplies the whole common space.
The mechanism is stronger than positivity of the integrated kernel.

Keep f=Phi/||Phi||_2, the complete theta source, and I=(-log(2)/2,0).
The unchanged consumer requires every finite node family and every complex
coefficient row. Set m=(x+y)/2, d=(x-y)/2. RAW2 gives exactly

    V(x,y)=integral_0^infinity K_s(x,y) ds,
    K_s(x,y)=f(sqrt(s+m^2)+d) f(sqrt(s+m^2)-d).             (L1)

There is no discarded boundary: the odd integral on [m,-m] cancels when
m<0 before s=u^2-m^2 is substituted. Every K_s is positive-valued; that
alone says nothing about its arbitrary finite quadratic forms.

Pinned local inputs under docs/Codex:

| File | SHA256 | Used part |
| --- | --- | --- |
| REPORT_2026-09-14_FULL_V_RANK_TWO_INTAKE.md | 51168fb802d7facfb74291d0a3fc0009b121f540711df2fe10ae01cd84c1d14f | R2-R5, exact L1 and all two-node comparisons |
| REPORT_2026-09-13_ANALYTIC_POSITIVITY_PROPAGATION.md | fb83c216aef4687425074732904f9d2f52aac77527a926e7556fb0067335e2bd | A1, all-rank analytic propagation |
| REPORT_2026-09-14_FIRST_ORDER_COMPENSATION_PREFLIGHT.md | 758eb21c80cb405fa242bc5e6a6ce38053cbe9edc997752ac01480aa5c6c55e7 | F8-F10, differentiated complete-source tail |
| REPORT_2026-09-14_SCHUR_REPEATABILITY.md | fe737941236b24c67bee7803a38014660698e852b2e61bc54f58672efb494190 | S6, exponential/tensor Gram identity |

The prior passivity/finite local-state tests and the quartic Lee-Yang sibling
were reconciled first. This is not a new discovery of that sibling and does
not repeat its spin-limit construction. The new test concerns the explicit
K_s in L1; the derivations below are self-contained except for the pinned
full-source bounds and the re-explained propagation lemma. No new external
theorem, semantic-shelf absence, numerical scan, or canonical supplier is
claimed. Existing incomplete semantic-index receipts remain incomplete.

## 2. A sibling for which this exact construction succeeds at every rank

Take, separately from theta,

    f_(a,b)(u)=C exp(-a u^4-b u^2), C>0, a>0, b real.

This is positive, even and integrable with every required polynomial weight.
The same identities also cover a=0,b>0 as the Gaussian limit. Direct expansion
of the TWO shifted arguments in L1 gives

    (sqrt(s+m^2)+d)^2+(sqrt(s+m^2)-d)^2=2s+x^2+y^2,
    (sqrt(s+m^2)+d)^4+(sqrt(s+m^2)-d)^4
      =2s^2+4s(x^2-xy+y^2)+x^4+y^4.                       (L2)

Define the real positive weight

    w_s(x)=C exp[-a s^2-b s-(4as+b)x^2-a x^4].

Then the full integrand, including every mixed term, is

    K_s(x,y)=w_s(x) w_s(y) exp(4as xy).                    (L3)

An explicit common feature map, indexed by s>=0 and integer n>=0, is

    psi_x(s,n)=w_s(x) (4as)^(n/2) x^n / sqrt(n!).          (L4)

The n=0 factor is 1, including when as=0; higher factors vanish when as=0.
Use H=L2([0,infinity),ds; ell2(N_0)). The exponential series proves

    sum_n conjugate(psi_x(s,n)) psi_y(s,n)=K_s(x,y).

Each psi_x belongs to H: its squared norm is
integral_0^infinity K_s(x,x) ds=V_(a,b)(x,x)<infinity.
Cauchy--Schwarz therefore justifies the inner product over s and n; for a
finite complex row all mixed terms are absolutely integrable. Consequently

    V_(a,b)[c]=integral_0^infinity sum_(n>=0)
                  |sum_i c_i psi_(x_i)(s,n)|^2 ds >=0.    (L5)

This is an independent construction from the source, not a square root of
an unknown-sign matrix. It covers all real nodes, arbitrary N and complex c.
For a>0 and distinct nodes it is strictly positive for nonzero c: at each
s>0, the first N monomial coordinates give an invertible Vandermonde matrix
after nonzero column scalings. For a=0,b>0 only n=0 remains, recovering the
known rank-one Gaussian identity V(x,y)=f(x)f(y)/(2b).

## 3. A necessary condition for transferring the same construction to theta

Simultaneous reflection preserves K_s because f is even. Work on any open
positive interval J; reflection will return to I. At s=0 and x,y>0,

    K_0(x,y)=f(x)f(y).

Normalize by this known positive rank-one factor, not by an unknown matrix:

    W_s(x,y)=K_s(x,y)/(f(x)f(y)), W_0=1,
    q(u)=f'(u)/f(u).

For fixed positive x,y, differentiation of the square root in L1 at s=0
is legitimate (m>0), and gives the EXACT tangent kernel

    J_q(x,y)=partial_s W_s(x,y)|_(s=0)
            =(q(x)+q(y))/(x+y).                          (L6)

Suppose K_s were PSD on J for every sufficiently small s>0. Then W_s is
PSD by diagonal congruence. For any finite row z with sum z_i=0,

    0 <= z^*W_s z=s z^*J_q z+o(s),
    hence z^*J_q z>=0.                                   (L7)

This is conditional PSD of J_q, on zero-sum rows. Apply first finite
differences in BOTH arguments. Each difference is a zero-sum functional;
arbitrary linear combinations still have total coefficient zero. Taking
their finite-dimensional limit in L7 proves that the kernel

    C_q(x,y)=partial_x partial_y J_q(x,y)
      =[2(q(x)+q(y))-(x+y)(q'(x)+q'(y))]/(x+y)^3          (L8)

must be PSD on J for all finite rows. On its diagonal,

    C_q(x,x)=[q(x)-x q'(x)]/(2x^3).                       (L9)

Notice the distinctions: C_q is NOT the earlier C_V=partial_x partial_y
log V, and PSD of K_s is NOT inferred from positivity of K_s(x,y).

## 4. Full theta violates this necessary condition on every positive interval

The complete-source estimates F8-F10 give, as x->infinity,

    q(x)=-2pi exp(2x)+9/2+O(exp(-2x)),
    q'(x)=-4pi exp(2x)+O(exp(-2x)).                       (L10)

These estimates include controlled derivatives of all n>=2 theta modes;
the source has not been replaced by its first mode. Fix any y0>0. Inserting
L10 in the exact formulas L8-L9 gives

    C_q(x,x) ~ 2pi exp(2x)/x^2,
    C_q(x,y0) ~ 4pi exp(2x)/x^2,
    C_q(y0,y0) is finite.                                (L11)

Therefore the actual two-node determinant of C_q obeys

    C_q(x,x) C_q(y0,y0)-C_q(x,y0)^2
       ~ -16pi^2 exp(4x)/x^4 < 0.                        (L12)

This proves C_q is not PSD on the positive half-line. To bring that failure
into the prescribed small interval, ALL-RANK analytic propagation is needed;
moving these two nodes into J without it would be invalid.

Here its hypotheses are satisfied. The full f is holomorphic on
|Im z|<pi/4 and is nonzero on the positive real axis. Choose a connected
complex open neighborhood Omega of that axis, contained in Re z>0 and in
the strip, thin enough to avoid zeros of f. Such a neighborhood is the
union of sufficiently small zero-free disks centered at positive real
points. Then q=f'/f is holomorphic on Omega, and z+w never vanishes on
Omega x Omega. Formula L8 is jointly holomorphic on that PRODUCT domain.

For completeness, the propagation fact used here is: a Hermitian kernel
holomorphic on Omega x Omega and PSD for every finite row on an open real
subinterval is PSD on the whole connected real interval in Omega. At an
interior point, limits of finite differences give PSD of every finite
derivative/evaluation block. Finite Taylor sums then extend the evaluation
set to a complex-disk-sized real neighborhood while retaining its mixed
entries with all old nodes. First take the difference limit at each fixed
Taylor degree, then the Taylor limit. Along a compact segment a uniform
positive disk radius and a finite chain of overlapping neighborhoods carry
any desired finite family. This is pinned A1; a mere pairwise hypothesis
would not suffice for its derivative blocks.

If C_q were PSD on ANY open J contained in (0,infinity), propagation would
contradict L12. Thus C_q is not PSD on any such J. In particular L7 cannot
hold on any J: otherwise first differences would make C_q PSD there.

Negating L7 yields a FIXED finite row z and nodes x_i in J with

    sum_i z_i=0,  z^*J_q z<0.

Set c_i=z_i/f(x_i). Taylor expansion in s for this fixed finite family gives

    sum_(i,j) conjugate(c_i) K_s(x_i,x_j)c_j
       =s z^*J_q z+o(s)<0                                (L13)

for EVERY sufficiently small s>0. Reflection puts all the nodes in I when
J=(0,log(2)/2). This is an analytic existence result: no explicit numeric
node set, rank bound, or value of the small-s threshold is claimed.

THEOREM: on the required interval there is a fixed finite complex family
whose full-theta K_s form is negative for all sufficiently small s>0.
Consequently there cannot be independent positive Gram realizations of
each K_s for almost every s in any full neighborhood of zero.

## 5. What was learned, and the precise next requirement

The quartic sibling has an explicit all-rank representation L4-L5 using
the same exact cancellation coordinates. For actual theta, the necessary
tangent condition L7 fails; L13 excludes this layer-by-layer transfer.
The tail test is a discriminator for this CONSTRUCTION. It also applies
to many other rapidly decaying sources and does not distinguish RH truth
from falsity. Additive TN-infinity or reciprocity cannot repair the specific
claim that these fixed K_s are PSD: L13 already uses the actual theta source.

L13 is NOT an actual negative witness for V. For that same row the identity
remains V[c]=integral_0^infinity K_s[c] ds; the rest of the integral can
compensate the negative contribution near zero. We prove neither sign of
that total. This does not alter the all-two-node V theorem, and does not
exclude a different common Gram representation of the whole integral.

The next allowed mechanism must therefore account for cancellation between
integration levels, or use another exact representation of the full form.
A change to the positive state must explicitly pay the terms generated by
mixing levels, weights and boundaries. Reasserting K_s>=0 as matrices,
changing it to another positive comparison kernel without proving equality,
or relabelling abstract Gram existence would repeat the failed step.

No all-rank theta sign delta, Lean proof, canonical CLOSES/OPENS, new Proshka
request or RH claim results from this bounded test.
