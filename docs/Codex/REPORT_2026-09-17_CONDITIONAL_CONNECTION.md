# A common conditional-space transport, with its exact limitation

STATUS: ACCEPTED_LIMITED_PAPER; independently reviewed C1--C18 analytic result.
Original all-finite complex V positivity and RH remain open.
SOURCE_BASE: 434f6c2b194243aa15a00a4125984fa41da67223.
CONSUMPTION: INCOMPLETE_NO_CONSUMABLE_TARGET; isolated analytic research.

## 1. Fixed inputs and the exact question

This returns to the original covariance before introducing another reserve.
Under docs/Codex, the directly read inputs are:

- REPORT_2026-09-13_BROWNIAN_DILATION_CONDITIONAL.md, sections 1--5,
  SHA256 8ea7ed0b70f57d271b09cb44f53156cd50b71aa6511bd1fd4077111ba5bef5ef;
- REPORT_2026-09-13_DEFORMED_SOURCE_ZERO_WITNESS.md, Z1--Z4,
  SHA256 70163ec5703ea516b8a191f705a26034cc9914d875f8e74cee7544a0b496bb4c;
- REPORT_2026-09-16_PAIRZERO_GEOMETRY.md, P3--P13,
  SHA256 c53ae234d3ad87728203b9e64439eb718a79e0b13c09d2f18d9e9a481f31bccd.

Also read the exact definitions and domains in
docs/routeB_bus/proshka/PROSHKA_RESPONSE_GOAL058_NULLVAR_2026-09-13.md,
sections 2--5, equations (3)--(22), SHA256
4fa7909725d2fa10ccc52d3413580289692d3a1489ecae7bed88956f80980730.
No new external theorem is used below; the transport is proved directly.
The named search for moving conditional projections/Fisher information and
nonadiabatic energy returned mgrep exit 1, HTTP 403 credits depleted.
This is incomplete discovery, not a no-hit result. No alternative search,
shared index repair, source registration or new Pro request is performed.

Let h be the full density of sum_n Exp(1)/(pi n^2), r=h*h,
f(X)=exp(5X/2)r(exp(2X))/||Phi||_2, t=exp(2X), and

    p_X(s)=t h(ts)h(t(1-s))/r(t), 0<s<1,
    rho_X(s)=partial_X log p_X(s),
    I_X=integral_0^1 rho_X(s)^2 p_X(s) ds.                 (C1)

All modes and physical X>=0 cutoff are retained. The pinned source bounds
give p_X>0 inside the interval, smooth dependence in X, normalized mass,
and, with c0=3/(2pi)<1 and a fixed finite full-source constant M_chi,

    I_X <= 16 M_chi/(exp(2X)-c0), X>=0.                  (C2)

The small-argument exponential h(u)~(pi/2)u^(-5/2)exp(-pi/(4u)), with
the controlled derivatives of NULLVAR (9)--(10), provides common endpoint
majorants on every compact X-interval. In particular all differentiations
of the following Hilbert vectors on such compacts are legitimate.

The question is whether straightening this moving conditional projection
creates a positive compensation for the original V. We first construct
the common transport exactly, then test that inference.

## 2. One Hilbert space and a finite total operator rotation

Set H=L2((0,1),ds), inner product conjugate-linear in the first slot, and

    e_X=sqrt(p_X),  ||e_X||=1,
    e'_X=(rho_X/2)e_X,
    <e_X,e'_X>=0,  ||e'_X||^2=I_X/4.                    (C3)

Let P_X=|e_X><e_X| and define the bounded rank-at-most-two operator

    A_X=|e'_X><e_X|-|e_X><e'_X|.                        (C4)

Here |v><w| maps u to v<w,u>. Thus A_X^*=-A_X,
A_X e_X=e'_X, P'_X=[A_X,P_X], and ||A_X||=sqrt(I_X)/2
(with the same formula when e'_X=0). These assertions follow by writing
the two by two matrix on span(e_X,e'_X).

The norm-continuous bounded-operator ODE

    W'_X=A_X W_X, W_0=Id                               (C5)

has a solution on every finite X-interval by its norm-convergent iterated
integral series. The skew-adjoint identity shows W_X^*W_X=Id; solving
the reverse ODE gives surjectivity. Uniqueness, C3 and C4 imply

    W_X e_0=e_X, P_X=W_X P_0 W_X^*.                    (C6)

C2 now pays a global bound, without a rank or signal-dependent constant:

    integral_X^infinity ||A_u||du
      <= (2 sqrt(M_chi)/sqrt(c0))
                      arcsin(sqrt(c0) exp(-X))=:R(X).   (C7)

Indeed substitute v=exp(-u) in the integral of
2 sqrt(M_chi)/sqrt(exp(2u)-c0). In particular the total integral is
finite, R(X)=O(exp(-X)), and W_X converges in operator norm to a unitary
W_infinity with ||W_infinity-W_X||<=R(X).

The complete conditional law tends to uniform: write
h(u)=2pi exp(-pi u)chi(u), 0<chi<=1, chi(u)->1. Then
p_X(s)=chi(ts)chi(t(1-s))/(J(t)/t), J(t)/t->1.
Dominated convergence gives p_X->1 in L1(0,1), hence e_X->1 in H.
Consequently W_infinity e_0=1. This is a common positive Hilbert carrier
and an operator-norm bound for its transport; it is not an energy bound
for V or its mixed covariance.

## 3. Transport of every original column, with no changed cross term

For x in I=(-log(2)/2,0), a=exp(2x), the original likelihood is

    g_x(X,s)=a^(9/4) h(ats)h(at(1-s))/(h(ts)h(t(1-s))).

The exact ratio identity is

    g_x(X,s)=[f(X+x)/f(X)] [p_(X+x)(s)/p_X(s)].           (C8)

Both factors are retained. Define the H-valued source column

    F_x(X)=f(X)e_X g_x(X)
          =f(X+x) p_(X+x)/sqrt(p_X),
    Y_x(X)=W_X^* F_x(X).                               (C9)

The original likelihood domain proves F_x and X F_x lie in
L2([0,infinity);H). Locally, F_x, its first derivatives and multiplication
by rho_X belong to H: their endpoint bounds have exponential factor
exp[-pi(2/a-1)/(8t s)] at s=0, and its counterpart at 1, times powers.
Here a in (1/2,1); the positive exponent easily absorbs the score poles.
Only this common source-column domain is used below; multiplication by
rho_X is NOT claimed bounded on all H.

For a finite complex row let

    F_c=sum c_i F_(x_i), D_c=sum c_i(X+x_i)F_(x_i),
    Y_c=W_X^*F_c, Z_c=W_X^*D_c,
    u_c=<e_0,Y_c>=sum c_i f(X+x_i),
    v_c=<e_0,Z_c>=sum c_i(X+x_i)f(X+x_i).

The original three exact accounts become

    E_micro[c]=2 Re integral_0^infinity <Y_c,Z_c>dX,
    E_loss[c] =2 Re integral_0^infinity
                         <(1-P_0)Y_c,(1-P_0)Z_c>dX,
    V[c]      =2 Re integral_0^infinity conjugate(u_c)v_c dX. (C10)

Thus the projection is now constant, and the full loss cancels as the
same orthogonal-component cross product. Unitarity changes NEITHER account
and supplies no sign for the remaining scalar cross product. X=0 is
unchanged because W_0=Id. No integration by parts, deleted boundary term,
or limit of boundary traces is used in C10.

## 4. The exact triangular equation, including the coupling

Let Sigma_X be multiplication by rho_X/2 on its maximal domain.
Direct differentiation of C9 gives, on the stated source columns,

    partial_x F_x=(partial_X+Sigma_X)F_x.

Consequently, for B_X=W_X^*(A_X+Sigma_X)W_X,

    partial_x Y_x=partial_X Y_x+B_X Y_x.                (C11)

It is essential that the sign in A_X+Sigma_X is plus. Since
Sigma_X e_X=e'_X, the top row of this operator vanishes after flattening:

    P_0 B_X=0,
    (1-P_0)B_X e_0=2 W_X^*e'_X.                        (C12)

To see the first equality on its domain, for arbitrary v there,
<e_X,Sigma_X v>=<e'_X,v> and
<e_X,A_X v>=-<e'_X,v>. Their contributions cancel exactly.
For Y_x=u_x e_0+z_x, z_x orthogonal to e_0, C11 is therefore

    partial_x u_x=partial_X u_x,
    partial_x z_x=partial_X z_x+2 b_X u_x+D_X z_x,
    b_X=W_X^*e'_X,
    D_X=(1-P_0)W_X^*Sigma_X W_X(1-P_0).                 (C13)

The last operator is only used on the transformed source-column domain;
no self-adjoint compression theorem or boundedness is asserted.
At x=0, Y_0(X)=f(X)e_0. The formula u_x=f(X+x) is already proved by the
exact conditional mean in C8--C10, not inferred from the PDE alone.
For x<0 and X+x<0 the characteristic meets the physical X=0 boundary;
the PDE and x=0 data alone do not supply that boundary value. The actual
source columns retain it. The complementary field is driven by this
scalar profile; its mere norm positivity adds no sign restriction to C10.

The familiar positive geometric term is real but belongs to another
functional. For a compactly supported scalar C1 profile u,

    integral ||partial_X(e_X u)||^2 dX
       = integral (|u'|^2+(I_X/4)|u|^2)dX.               (C14)

This is immediate from <e,e'>=0. It is a positive kinetic energy.
No equality between C14 and the first-order mixed form C10 has been
established. Inserting C14 as a reserve for V would require a new exact
identity and an independent comparison, including complementary terms.

## 5. An actual-source deformation preserves ALL this conditional geometry

For epsilon<0 replace f by a positive scalar normalization of
f_epsilon(X)=exp(epsilon X^2) f(X). The pinned deformation theorem proves
that its full V has a negative finite complex row in every nonempty real
open interval, including I. This is a known analytic existence theorem,
not a computed original-theta witness.

Under the natural joint tilt exp(epsilon X^2)dmu, the conditional law
p_X is EXACTLY unchanged because the tilt is measurable in X. Hence
e_X, I_X, A_X, W_X, B_X, D_X and the global bound C7 are unchanged.
The new columns have the exact form

    F_(x,epsilon)(X)=f_epsilon(X+x) p_(X+x)/sqrt(p_X).

C10--C13 remain true with scalar initial data f_epsilon instead of f.
Evenness of the scalar profile also survives. Therefore no sign argument
using ONLY this conditional projection geometry, its Fisher metric,
the unitary transport bound, the triangular equation and scalar evenness
can distinguish the positive-sign target from these negative controls.
The scalar initial profile and its compatibility with the joint law must
be used in an additional way.

This is not a refutation of the full product-source approach. The negative
tilt changes the dilation likelihood by
exp(epsilon x^2)T^(epsilon x), which is not a product of a function of u
and a function of v for x!=0. The original un-tilted source retains the
two-factor likelihood in C8's original formula. That radial/conditional
compatibility is precisely a source property that this generic geometric
transport does NOT spend. No theorem combining it with reciprocity into
the required sign is supplied here.

## 6. What the product condition and reciprocity force jointly

There is a precise rigidity statement within the radial reweighting class
just used. Let w:(0,infinity)->(0,infinity) be C2, keep the SAME conditional
law p_X, and replace the scalar source by a positive normalization of

    f_w(X)=w(exp(2X)) f(X).

The new dilation likelihood is g_x times w(aT)/w(T). Suppose it retains
two-factor separability in u,v for EVERY a in (1/2,1). Since original g_x
is positive and separable, this is equivalent to

    w(a(u+v))/w(u+v)=A_a(u)B_a(v), u,v>0.                (C15)

No smoothness of these positive factors is needed. Writing q=log w,
the four-point identity for the right side and taking mixed differences
of the smooth left side imply

    a^2 q''(aT)-q''(T)=0, T>0, a in (1/2,1).            (C16)

Therefore T^2 q''(T) is unchanged under multiplication by any a in that
interval. Repeated such scalings and their inverses connect any two
positive T, so this continuous function is constant. Integration gives

    w(T)=C T^beta exp(gamma T), C>0, beta,gamma real.     (C17)

Conversely all these w satisfy C15, since the ratio is
a^beta exp(gamma(a-1)(u+v)). Thus this is the entire smooth positive
radial class retaining the two-factor likelihood, not only a check of
Gaussian examples. This classifies the ratio identity before imposing
any additional normalization or integrability requirements on the tilted
measure or source; C17 does not assert that all beta,gamma are admissible
probability parameters.

If the new scalar source also retains the exact reciprocal/even symmetry,
then w(T)=w(1/T). In C17 this says

    2 beta log T + gamma(T-1/T)=0 for all T>0.           (C18)

Dividing by T and letting T->infinity gives gamma=0, then beta=0.
Consequently w is constant. Normalization removes that last constant.
The fixed conditional law, full two-factor dilation likelihood and exact
reciprocity jointly leave no nontrivial radial reweighting of f.

This is a classification inside the specified reweighting class, not a
classification of all sources or all lifts. In particular, the Gaussian
negative controls have q(T)=epsilon(log T)^2/4 up to a constant and violate
C16 when epsilon!=0. The theorem locates precisely what extra condition
the geometry-only negative control loses. It does not infer positivity
from uniqueness: a unique admissible profile still needs a sign proof.

## 7. Decision

C5--C7 construct one common source-based unitary transport, with a finite
whole-half-line operator budget, for every finite row at once. C10--C13
show exactly what it preserves and where the unpaid scalar flux stays.
C14 and the Gaussian deformation control prevent replacing that flux by
a positive kinetic term or conditional-information budget without proof.
C15--C18 then classify the surviving radial reweightings and show that
two-factor dilation plus reciprocity select the original profile within
this class; neither property can be dropped when using that rigidity.

This is representation and compatibility evidence, not an improved lower
bound for original V. Do not launch a generic request to prove positivity
from conditional Fisher geometry alone, and do not re-open the old W2
response-energy criterion under this name. A further candidate must use
the linked radial amplitude and two-factor likelihood, retaining the
full square-rate law, physical weight and boundary. No new proof request,
canonical admission, source-sign counter reset, or RH claim follows.

## Independent acceptance

Candidate SHA256: `7af6ee175d0d746465cc1e15777ecc91fc305a5428bdcc6a5569b7a8f2e338ab`.
Review SHA256: `cf3192ad89e98d1fa832089a2e4de27b04536193be6cb4656e2d33c90fbcac88`.
Verdict: `ACCEPT_CONDITIONAL_UNITARY_TRANSPORT_AND_SCOPE_ONLY`.
The parent independently checked the finite-rank generator, exact tail integral,
column-domain exponent, triangular coupling sign, and radial four-point
rigidity. The final review includes the physical-boundary and normalization
clarifications. The complete review is embedded in the paired certificate.
This supplies no improved lower bound for original V, no original negative
witness, no canonical theorem admission and no RH claim.
