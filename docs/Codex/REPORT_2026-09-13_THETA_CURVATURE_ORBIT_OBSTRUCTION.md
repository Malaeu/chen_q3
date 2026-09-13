# The full squared-coordinate log-curvature does not distinguish negative heat deformations

STATUS: ACCEPTED_CURVATURE_ONLY_TRANSFER_OBSTRUCTION_PAPER.
SCOPE: ISOLATED_PAPER_OBSTRUCTION_TO_CURVATURE_ONLY_TRANSFER.
ORIGINAL_RF: OPEN. GLOBAL_IC: OPEN. GLOBAL_ODD2: OPEN. RH: OPEN.
PX_RH_CLAIM: NOT_MADE. No Lean or canonical admission.

This tests one proposed kind of source property, rather than supplying a
new positive carrier or another polynomial control. All deformations below
use the full original theta source.

## C1. Exact preservation of the known source curvature

Use f=Phi/||Phi||_2 and g_a(x)=exp(a x^2)f(x), with the complete Phi fixed
in REPORT_2026-09-13_DEFORMED_SOURCE_ZERO_WITNESS.md at
fc3a000f2b54f32a9f606f8c2145f305d9af201f, 7259 bytes / 146 LF, SHA256
70163ec5703ea516b8a191f705a26034cc9914d875f8e74cee7544a0b496bb4c.
That independently accepted report proves: for every a<0 and every
nonempty open real interval I, a finite complex row in I has V_(g_a)[c]<0.
It uses the published Rodgers--Tao theorem and proves the exact transfer;
it provides no numerical row or original a=0 witness.

For t>0 let s(t)=f(sqrt(t)) and s_a(t)=g_a(sqrt(t)). Then

    s_a(t)=exp(a t)s(t),
    d^2/dt^2 log s_a(t)=d^2/dt^2 log s(t).                 (C1)

The source theorem of Csordas, Theorem4.2(b) and Remark4.3(a),
https://arxiv.org/html/1309.0055v1, gives the strict negativity of the
right side, with Phi_ours(x)=2Phi_C(x/2). The rescaling is t->t/4 and a
positive constant; it preserves the strict sign. The stated curvature
theorem is a named published dependency, not reproved here.
The source definition (4.2), theorem and remark were read directly.
Fetched HTML: 439021 bytes, SHA256
15d9c07069448784d19489c64fecccb5155631e3c99069fca2fd1a1665a1fb47.

Equivalently, for J_g(x)=x(g'^2-gg'')+gg', direct differentiation gives

    J_(g_a)(x)=exp(2a x^2)J_f(x)>0, x>0.                (C2)

Indeed J_g/g^2=(log g)'-x(log g)'', so the 2ax terms cancel. Positive
scalar L2 renormalization changes log s_a only by a constant and multiplies
J_(g_a) by a positive constant. It does not repair this inability to detect a.

For every a<0 these kernels are positive, even, smooth, rapidly decaying,
and strictly log-concave in the squared coordinate. They nevertheless fail
the full matrix sign, as recalled above. Thus these properties, even the
exact whole function (log s)'', cannot by themselves imply V_g>=0 on a
class containing this full Gaussian-deformation family. Such a theorem
would apply to a negative-a member and contradict its finite negative row.
The conclusion concerns a universal transfer from the named properties;
it does not rule out additional hypotheses specific to the original source.

## C2. The familiar symmetric-pair positive budget survives as well

For each fixed a<0, concavity of log s_a and evenness of g_a give, for
u,x>=0,

    g_a(u+x)g_a(u-x)<=g_a(sqrt(u^2+x^2))^2.              (C3)

This is Jensen's inequality at the two squared arguments (u+x)^2 and
(u-x)^2, whose average is u^2+x^2. At an argument zero use continuity.
Integrating with weight 2u and changing v=sqrt(u^2+x^2) proves

    0<V_(g_a)(x,-x)<=2 int_x^infinity v g_a(v)^2 dv
                    =V_(g_a)(x,x)=V_(g_a)(-x,-x).       (C4)

Consequently every matrix on the symmetric pair {x,-x} is PSD, while
some other finite matrix inside any prescribed open interval is negative.
This does not assert positivity of every arbitrary two-node matrix or
identify the minimum possible rank of a negative matrix.

## C3. Iterating this particular curvature operation does not remove the ambiguity

For smooth h(t), define T(h)=h'^2-hh'', and C_0(h)=h,
C_(k+1)(h)=T(C_k(h)). For every integer k>=0, lambda>0 and real a,

    C_k(lambda exp(a t)h)
       =lambda^(2^k) exp(2^k a t) C_k(h).                (C5)

The base case is immediate; induction uses
T(exp(beta t)q)=exp(2beta t)T(q) and T(lambda q)=lambda^2 T(q).
Thus signs of all these expressions are preserved; wherever C_k is
positive, its logarithmic second derivative is also unchanged. This is
a pointwise exact covariance, not a positivity proof for higher C_k(s).

In particular, if a proposed property P of s is preserved by multiplication
by exp(a t), and P(s) is established, then P alone cannot imply positivity
of V_g throughout a class containing all g_a with a<0. The source proof
plus that proposed universal implication would contradict C1's negative
members. Higher C_k(s) are not asserted positive here. Nor are these
iterated source expressions identified with the generalized Laguerre
inequalities of the Fourier transform or the associated kernels K_n in
Csordas Theorem4.6; those are different objects and quantifiers.

## Consequence for the pending source-property task

The missing ingredient must distinguish the actual source from its
negative Gaussian deformations. Repeating only the invariant curvature
data cannot do so. This leaves source-specific structural hypotheses open;
none is proved sufficient here. The result narrows an attempted transfer,
not the full RF question, and supplies no original-source negative witness.
The existing THETARF request is unchanged; no message is sent into its live
chat and no new source-sign construction is counted.

## Independent acceptance receipt

The sole checker read the entire 5227-byte / 104-LF draft, SHA256
c9425408a32cf9c2c82f3cba34027af7411b4af99dcbefd1f5c0bf6ebb1e57b7,
and returned CLEAN_CURVATURE_ONLY_TRANSFER_OBSTRUCTION. The review checks
the exact covariance, Jensen bound and conditional higher-level statement,
including the distinction from Fourier generalized Laguerre inequalities.
Review receipt SHA256:
51ec6e5b40627c0b55d8f1d5eb0b3a79841513446179441aa76acaea753e9952.
Only the status and this receipt were appended after that exact review.
