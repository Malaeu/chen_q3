# Exact radial-carrier obstruction for closed linear energy transforms

STATUS: ACCEPTED_LIMITED_PAPER; independently reviewed C1--C7.
SOURCE_BASE: 07cf0e5892ec9b0bf53a70701dffc0d85100df53.
Date: 2026-09-17. Original V positivity and RH remain open.

## C1. The same carrier and the exact question

Let f be the complete normalized theta source, with all conventions of
FULL_V_RANK_TWO and RADIAL_GRAM_DIVISOR_PREFLIGHT unchanged. Keep

    V(x,y)=int_0^infinity (2t+x+y) f(t+x)f(t+y) dt,
    I=(-log(2)/2,0), S={z: |Im z|<pi/4},
    H=L2([0,infinity),ds), g_z(s)=f(sqrt(s+z^2)).

The accepted radial preflight Q2 proves that g:S->H is a single-valued
holomorphic Hilbert map, with the full source and full half-line retained.
Evenness of f removes all square-root branch points. In particular

    g_z=g_(-z) for every z in S.                         (C1)

The previous result excluded multiplicative PSD repairs of its Gram.
This report tests a different enlargement: any single closed linear
operator T from a linear domain in H to an arbitrary complex Hilbert
space K, possibly unbounded and not necessarily densely defined.
Can its domain contain every g_x, x in I, with the exact identity

    V(x,y)=<Tg_x,Tg_y>_K for all x,y in I?               (C2)

Inner products are conjugate-linear in their first argument. Equality
on all finite complex quadratic forms is equivalent to C2 by polarization.
We prove C2 impossible for this carrier and this closed-operator class.
We do not assume that the full V is PSD independently of C2.

## C2. What is known about V and what is only conditional

The accepted full-source strip bounds make V jointly holomorphic on S x S,
with real symmetry and Hermitian polarization. FULL_V_RANK_TWO R3--R7
also gives for every nonzero real a

    V(-a,-a)=V(a,a)>0,
    0<V(a,-a)<V(a,a).                                  (C3)

This is an unconditional two-node statement, not all-family positivity.
Its strictness comes from the named published strict concavity of
log f(sqrt(s)), applied with the exact original integrals.

Suppose, for contradiction, C2 holds. It implies all-finite PSD of V
on I. Apply the accepted continuation lemma Q3 of the radial preflight
with N=V and D identically 1. The strip is conjugation-stable and simply
connected; D has nonzero positive Hermitian diagonal everywhere. There
is a Hilbert space E and one global holomorphic map F:S->E such that

    <F(z),F(w)>_E=V(conj(z),w) for z,w in S.             (C4)

This use of Q3 is conditional on the hypothesized energy representation.
It is not a construction of a Gram representation of the actual unknown V.
No new complex pair-zero premise is needed in this report.

## C3. Identification with the actual operator outputs

Put E0=closure(span{F(x):x in I}) inside E. Every F(z), z in S, lies in E0:
if e is perpendicular to E0, the scalar holomorphic function <e,F(z)>
vanishes on I, so it vanishes on the connected strip by the identity
theorem. Thus F(z) is perpendicular to E0's orthogonal complement.

On finite linear combinations define

    U(sum_i c_i F(x_i))=sum_i c_i T g_(x_i), x_i in I.

C2 and C4 give equality of squared norms on both sides for every finite
complex coefficient row. A zero left combination therefore has zero
right combination. U is well-defined and isometric; it extends to an
isometry E0 -> K onto the closed span of the actual Tg_x. Define

    F_tilde(z)=U F(z).

This is globally holomorphic in the FIXED actual codomain K, preserves
C4, and F_tilde(x)=Tg_x for every real x in I. No arbitrary unitary
transition between different local feature spaces is used.

## C4. Closed graph forces extension of the actual operator relation

Because T is closed, Graph(T) is a closed complex linear subspace of
H direct-sum K. The map

    Psi(z)=(g_z,F_tilde(z))

is holomorphic on S and belongs to Graph(T) for every real x in I.
For any vector b perpendicular to Graph(T), the scalar function
<b,Psi(z)> is holomorphic and zero on I. The identity theorem makes it
zero on all S. Since a closed subspace equals the orthogonal complement
of its orthogonal complement, Psi(z) belongs to Graph(T) for every z in S.
Therefore

    g_z is in Dom(T),  Tg_z=F_tilde(z) for all z in S.   (C5)

This is where closedness is used. We did NOT assume that Dom(T) already
contains the positive real or complex profiles; C5 follows from closed
graph, holomorphy and the exact identity on the original negative I.

Now C1 and the single-valuedness of T give F_tilde(z)=F_tilde(-z).
For nonzero real a, C4 then gives

    V(a,-a)=<F_tilde(a),F_tilde(-a)>
            =||F_tilde(a)||^2=V(a,a),                 (C6)

contradicting the strict inequality C3. C2 is impossible.
The same argument starts from any nonempty real open interval, but
in particular covers the original I without inserting positive nodes
as additional assumptions on the proposed operator domain.

## C5. Closable operators and closed nonnegative energy forms

The exclusion extends to a closable linear T: its closure is a
single-valued closed linear operator agreeing with T on the original
domain and would still satisfy C2.

It also excludes a nonnegative closed sesquilinear form q on H with a
complex linear domain D containing all g_x, x in I, if

    q(g_x,g_y)=V(x,y) for every x,y in I.               (C7)

Here closed means D is complete for the norm
(||u||_H^2+q(u,u))^(1/2); no density assumption is required for the following
argument. Let K be the completion of D/null(q) in the energy norm, and
T:D->K the class map. Positivity of q makes this quotient an inner-product
space (Cauchy--Schwarz ensures null vectors pair to zero), and
<Tu,Tv>=q(u,v).

T has closed graph: if u_n->u in H and Tu_n->v in K, then u_n is Cauchy
in the stated graph norm. Closedness of q gives u_* in D with u_n->u_*
in that norm. The H limit forces u_*=u; the K limit forces Tu=v.
Hence C7 would yield a forbidden closed T. This proof constructs the
energy Hilbert space directly; it does not import a self-adjoint
square-root theorem or presume positivity of V. A closable nonnegative
form is likewise excluded by its closed extension, which agrees with
q on its original domain.

In particular no positive bounded operator or bounded integral
transform on this fixed radial H can give the exact original V energy.
Unbounded CLOSED transforms are also excluded, not just bounded ones.

## C6. Scope and an exact sanity check

This result concerns a single fixed linear transform of these exact
radial profiles, or a closed nonnegative form on their fixed ambient H.
It does not exclude source features that retain shift orientation,
an enlarged carrier with additional information, shift-dependent maps,
nonlinear constructions, nonclosable algebraic maps, or positivity of V.
A nonclosable map is outside the theorem, not an accepted proof route.
There is no negative finite row of original V here and no better lower
bound for it.

The source-specific strictness in C3 is essential. For the distinct
control source f_a(u)=exp(-a u^2), a>0, direct differentiation in t gives

    V_a(x,y)=exp(-a(x^2+y^2))/(2a)=G_a(x,y).

For this control, T=identity DOES work. Its log f_a(sqrt(s)) is linear,
not strictly concave. Thus the argument is not the false assertion that
all even radial profiles forbid positive energy; it compares their
retained symmetry with the actual target's proven interaction.

## C7. Decision and exact source pins

A general closed linear change of energy on the old radial profiles
cannot repair their loss of x versus -x. Therefore the same radial G
must not be kept as a candidate exact energy carrier merely by replacing
its metric or adding a fixed bounded/unbounded closed linear operator.
Its valid two-node comparison remains a useful estimate. This excludes
a specified carrier, not all positive representations of original V.
No replacement carrier or new positive mechanism is selected by this
exclusion. Full V positivity and RH remain open.

Direct named inputs:
- REPORT_2026-09-17_RADIAL_GRAM_DIVISOR_PREFLIGHT.md Q2--Q3,
  SHA256 8fffcd6f46c4228fec6703864920e3e6121cee3c51a2d2025ec6b7b0a78652ad.
- REPORT_2026-09-14_FULL_V_RANK_TWO_INTAKE.md R3--R7,
  SHA256 51168fb802d7facfb74291d0a3fc0009b121f540711df2fe10ae01cd84c1d14f.
- REPORT_2026-09-16_LOGVCURV_INTAKE.md I1 (full-strip source bounds),
  SHA256 074a6ee11edf58ed502f8a41454515c06b5d286605b53ff0fe9e889981a3b929.

The two actual mathematical steps added here are the isometry into the
original output Hilbert space and the closed-graph analytic identity.
No new external theorem, source truncation, finite numerical test or
claim of literature novelty is used. Registered search coverage remains
incomplete after the provider authentication failure. No Lean run,
canonical admission, RH claim or Pro proof dispatch is made here.

## Independent acceptance

Candidate SHA256: `e3881205c3c14814cee060b86e1773dc1701e6ea839213fef4bbb22bd5e65faf`.
Review SHA256: `e17fdc02e380b31e78f745e9fbcbbe076888e1e23c3e5f1e1f4cd4d26660b78c`.
Verdict: `ACCEPT_EXACT_RADIAL_CLOSED_OPERATOR_OBSTRUCTION_ONLY`.
The parent checked the conditional N=V,D=1 feature continuation,
the isometry into the actual operator codomain, closed-graph identity
on the connected strip, strict actual-source two-node contradiction,
and the direct energy-space construction for closed forms. The complete
review is retained in the paired certificate. There is no numerical
source test, Lean certificate, canonical admission or original-V
negative witness. Original V positivity and RH remain open.
