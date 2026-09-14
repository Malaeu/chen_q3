# Two source ends: a coupled Laplace carrier and the unpaid full-form bound

STATUS: ACCEPTED_PARTIAL_PAPER_CARRIER_AND_END_ASYMPTOTICS.
GLOBAL_IC: OPEN. GLOBAL_ODD2: OPEN. ALL_ORDER_SOURCE_SIGN: OPEN.
RH: OPEN. PX_RH_CLAIM: NOT_MADE. No Lean or canonical admission.

## Source pins and the question

Work from 4f1d9f75e31955960d56111942b3f1c5efbb78d0. Keep f=Phi/A,
A=||Phi||_2, p=Phi/Z, Z=integral Phi=xi(1/2), with no identification of A,Z.

    V(x,y)=integral_0^infinity (x+y+2t) f(x+t)f(y+t)dt,
    D(x)=V(x,x)>0,  rho(x,y)=V(x,y)/sqrt(D(x)D(y)).             (T0)

The fixed-source Brownian response at 1953179544258aa3adb3cc6dcb483419ffe49bc3,
SHA2567649d7600e9ddac8407aa24a93ebf624466d1a3410e44270de70c3476595dfa9,
equations (2)--(7),(25)--(27), supplies the exact complete factorization

    f(z)=K exp(9z/2-a_z) h(a_z), a_z=pi exp(2z), K=4pi^2/A,
    0<h(a)<=1, h(a)>=1-3/(2a), a>0.                           (T1)

It holds for every real z, including z<0; h retains the entire convolution
law, not a truncated theta series. Evenness gives D(-r)=D(r) and
V(-x,-y)=V(x,y). These identities and the same-end limit

    rho(r,r+d)->sech(d) as r->infinity, fixed real d,            (T2)

are accepted in B6--B8 of REPORT_2026-09-13_BROWNIAN_PRIMITIVE_FORM.md
at 6556d34e863955e68bde80b03323bd95adb2a531, SHA256
00b5e80a573bd3a31c28f21ffa4fcf11695746c7df56274d12c0a94370e225fa.
The question here is how a positive carrier can also preserve the coupling
between the two different ends. The previous conditional Brownian map is
already excluded and is not reused.

## T1. The full-source opposite-end correlation

For fixed d>0 put a=pi exp(2r), b=a exp(2d). Evenness and (T0) give

    V(-r,r+d)=integral_0^infinity (d+2t) f(r-t)f(r+d+t)dt.

The ratio of the density product to f(r)f(r+d), using (T1), is

    exp(a(1-exp(-2t))-b(exp(2t)-1))
      *h(a exp(-2t))h(b exp(2t))/(h(a)h(b)).                   (T3)

Set z=2(b-a)t. For each fixed z>=0 the ratio tends to exp(-z).
The exponential in (T3) is at most exp(-2(b-a)t), using
1-exp(-2t)<=2t<=exp(2t)-1. The h quotient is at most
[(1-3/(2a))(1-3/(2b))]^-1, eventually bounded by 4.
After division by d the linear factor is 1+z/[d(b-a)], bounded by
1+z for large r. Dominated convergence therefore proves

    V(-r,r+d)/(f(r)f(r+d)) ~ d/[2(b-a)].                       (T4)

For d=0 the scale changes. Put w=2sqrt(a)t. The exact expression is

    a V(-r,r)/f(r)^2
      =(1/2) integral_0^infinity w exp(-2a(cosh(w/sqrt(a))-1))
        *h(a exp(-w/sqrt(a)))h(a exp(w/sqrt(a)))/h(a)^2 dw.

The integrand tends to w exp(-w^2); it is bounded by 4w exp(-w^2)
for large a because cosh z>=1+z^2/2. Hence

    V(-r,r)/f(r)^2 ~ 1/(4a).                                  (T5)

The full diagonal asymptotic from B8 is D(r)/f(r)^2~r/(2a).
Combining it with (T4)--(T5), symmetry and reflection yields, for every
FIXED pair of real offsets u,v,

    R rho(-R-u,R+v) -> T(v-u)/2,
    T(d)=d/sinh(d) for d!=0, T(0)=1.                           (T6)

For v<u reflect and exchange the nodes to reduce to d=|v-u|>0;
r=R+min(u,v), and R/sqrt(r(r+d))->1. In particular
rho(-r,r)~1/(2r), much slower than sech(2r).
This proof is pointwise in the offsets (and consequently entrywise on
each fixed finite matrix). No uniform rank or operator estimate is claimed.

## T2. One stationary orbit cannot be the exact normalized source

In L2((0,infinity),ds), j_x(s)=sqrt(2 exp(2x)) exp(-exp(2x)s) is a unit
vector and <j_x,j_y>=C(x-y), C(d)=sech(d), by elementary integration.
These are a unitary dilation orbit: D_a g(s)=sqrt(a)g(as).
They pass (T2), but their opposite-end correlation sech(2r) fails (T5).

More generally, suppose rho(x,y)=<U_x v,U_y v> for all real x,y, where
U is any unitary one-parameter group and ||v||=1. It is stationary in x-y.
Taking the same-end limit (T2) forces that stationary function to be C(d)
for every fixed d. Equation (T5) then contradicts it at (-r,r).
Scalar weights that restore D cancel in normalized correlations; node
phases cannot repair the discrepancy in magnitudes. This excludes only
one stationary orbit in the original x coordinate, not general Hilbert maps.

## T3. A positive coupled carrier with the correct two-end limits

The elementary convolution identity is

    (C*C)(d)=integral_R sech(t)sech(d-t)dt=2d/sinh(d)=2T(d).     (T7)

For d!=0 use z=tanh(t): the integral becomes
integral_(-1)^1 dz/(cosh(d)-sinh(d)z)=2d/sinh(d).
Continuity gives the value 2 at d=0. Let S be convolution by C on L2(R).
The preceding Laplace Gram identity implies S>=0; first integrate compact
test functions, then extend by Young's inequality. Also ||S||<=||C||_1=pi.
Thus the block operator with diagonal S and off-diagonal S^2/(4q)
is positive whenever q>=pi/4: symmetric/antisymmetric channels give
S^(1/2)[I +/- S/(4q)]S^(1/2)>=0. Approximating point masses by smooth
mollifiers and using continuity gives positivity for every finite complex
matrix of the corresponding two-channel kernel

    K_q((sigma,r),(tau,s)) = C(r-s) if sigma=tau,
                            T(r-s)/(2q) if sigma!=tau.        (T8)

Here sigma,tau are labels in {-,+}; r,s are arbitrary real numbers.
This is a proved carrier, not a source identity.

A radius-dependent version avoids freezing the coupling at an arbitrary q.
For r>=1 put a(r)=1/sqrt(r), b(r)=sqrt(1-1/r). Take the sum of the
positive kernel a(r)a(s)K_1 and the block-diagonal positive kernel
1_(sigma=tau) b(r)b(s)C(r-s). It has unit diagonal and equals

    G((sigma,r),(tau,s))
      =[a(r)a(s)+b(r)b(s)] C(r-s)                  if sigma=tau,
      =T(r-s)/(2sqrt(rs))                         if sigma!=tau. (T9)

Since 1>pi/4, this proves G>=0 for all finite complex coefficient families
on {-,+} x [1,infinity). For fixed u,v and R->infinity,

    G((sigma,R+u),(sigma,R+v))->C(u-v),
    R G((-,R+u),(+,R+v))->T(u-v)/2.                            (T10)

Both (T2) and the leading opposite-end coefficient (T6) are preserved.
The explicit positive candidate for the original normalization on |x|>=1 is

    V_G(x,y)=sqrt(D(x)D(y)) G((sgn(x),|x|),(sgn(y),|y|)).       (T11)

Its diagonal is exactly D. Let E=V-V_G, an exact definition retaining all
source terms. No positivity of E is asserted. Because E has zero diagonal,
a claim E>=0 would force E identically zero. The useful open question is
a RELATIVE quadratic-form bound E>=-theta V_G with theta<1, uniformly over
all finite node families and complex coefficients in the claimed domain,
or a different exact source-defined correction with its sign proved.
Entrywise error bounds do not imply this relative bound when Gram matrices
can have arbitrarily small eigenvalues. Fixed-rank tail limits are not RH.

## T4. An explicit single map on the whole real line

The two labelled rays in (T9) are useful end coordinates, but a full-source
map must also pass through x=0 as one family. Define for every real x

    r_x=sqrt(x^2+4),
    c_x=exp(x/2)/sqrt(2cosh(x)), d_x=exp(-x/2)/sqrt(2cosh(x)),
    A_x=1/sqrt(r_x), B_x=sqrt(1-1/r_x).

Here c_x^2+d_x^2=1, A_x^2+B_x^2=1, and r_x>=2. Let v_(sigma,r)
be Gram vectors of the independently proved K_1 in (T8). Let w_(sigma,r)
be two independent copies of the explicit Laplace Gram vectors j_r, so
<w_(sigma,r),w_(tau,s)>=1_(sigma=tau)C(r-s). The two Hilbert spaces are
orthogonal. Define, without using V positivity or its unknown zeros,

    L_x=A_x(c_x v_(+,r_x)+d_x v_(-,r_x))
          direct_sum B_x(c_x w_(+,r_x)+d_x w_(-,r_x)),
    N_x^2=||L_x||^2=1+A_x^2 c_x d_x,
    J_x=L_x/N_x.                                               (T12)

The vectors v exist from the proved explicit kernel (T8), not from the
unproved target V; alternatively the positive block-operator construction
above realizes their Gram space. The complete real mixed kernel is

    P_xy=c_x c_y+d_x d_y, Q_xy=c_x d_y+d_x c_y,
    Ghat(x,y)={ (A_x A_y+B_x B_y)P_xy C(r_x-r_y)
                 +A_x A_y Q_xy T(r_x-r_y)/2 }/(N_x N_y).       (T13)

It is positive for every finite complex family on ALL real nodes and has
unit diagonal. Reflection x->-x swaps c,d, hence Ghat(-x,-y)=Ghat(x,y).
All coefficients and the kernel are real analytic on R and R^2: the square
roots have strictly positive real arguments, and T has a removable value
at zero. This is one family through the centre, not independent values at
two copies of zero.

For x=R+u with u fixed, r_x=x+O(1/x), c_x->1, d_x=O(exp(-x)),
A_x~x^-1/2 and B_x->1. For negative x the c,d limits interchange.
Consequently, for every fixed u,v,

    Ghat(R+u,R+v)->C(u-v),
    R Ghat(-R-u,R+v)->T(u-v)/2.                                (T14)

This passes the same two necessary end tests as (T10). The named full-line
candidate is W(x,y)=sqrt(D(x)D(y))Ghat(x,y), with exact residual Ehat=V-W.
All diagonal, mixed and central terms are explicit. W is not claimed equal
to V. A uniform relative form lower bound Ehat>=-theta W, theta<1, would
prove V>=0 in its full stated domain. No such bound is proved here.
One may also study a proved positive source-defined correction, retaining
every term. The abstract availability of Gram vectors for K_1 pays only
the carrier; it supplies none of this missing source comparison.

## Literature dictionary and negative control

Galé, Matache, Miana, Sánchez--Lajusticia, Hilbertian Hardy-Sobolev spaces
on a half-plane, arXiv:2401.16091v1, https://arxiv.org/pdf/2401.16091.
Fetched PDF:301840bytes, SHA256
7aa803af7e43e3607ad21a83647de44506cb8b8750a656d2191e58b401cb28be.
Read scope: printed/PDF p2, definition (1.1) and following kernel formula;
p9, start of section3, classical Paley--Wiener statement. P2 also inspected
as a rendered page to verify the complex conjugate in K_w(z)=1/(z+bar(w)).
The source states that the Laplace transform "is an isometric isomorphism"
from L2(R+) to H2 of Re z>0 with norm squared (1/(2pi)) times the boundary
L2 integral. Our j_x maps to sqrt(2 exp(2x))/(z+exp(2x)), the normalized
Hardy kernel at positive w=exp(2x). This is an exact Laplace/Hardy dictionary;
the paper supplies no theta, Weil, two-end or RH theorem. T1--T3 are root
derivations, not claims attributed to that source or claims of novelty.

The fixed negative control f_c=exp(-x^2)(1+3x^2/10+x^4/25) has normalized
M_c(h)=exp(h^2/4)(h^4+42h^2+472)/472 and off-axis zeros. The carrier G is
available independently of f, so its positive sign alone cannot distinguish
the control. The unpaid hypothesis is the actual full-source transfer or
relative bound, not mere positive density or availability of a Hardy space.

All three new registered shelf queries returned INCOMPLETE due semantic-index
freshness; no absence or index repair is claimed. The inspected local cards
did not supply this map. One primary source was fetched for the dictionary.
Discovery remains INCOMPLETE_NO_CONSUMABLE_TARGET under the foreign canonical
writer and unbound production edge. Historical source-sign count5 is retained;
this carrier/preflight is not a completed third source-transfer attempt.

## Exact independent review and retrieval receipts

The T1--T3 draft SHA256
3fcafe0be4d1f976099a7b850d5ab5255363eedebf35784b41e5c41637f44c48
was independently CLEAN, including the quoted primary PDF scope; review
SHA256 e60cdc9e42288cc7837f761612e4699ae4c6938c3ed46b0c670e99679747ef76.
The complete T1--T4 draft SHA256
abf799bb9f74f703139170cbc125c141c2bec279cdbc4da39b856db5bfcd136b
was then independently CLEAN at the global carrier scope; review SHA256
2c59493bc26d7116cad81195781524ba99357cb5a1f666796b126eb6582e7f62.
Only the acceptance status and this receipt were subsequently added.
No numerical source evaluation, quadrature, finite-rank scan or Lean run.

New shelf receipt hashes, all INCOMPLETE:
Paley Wiener Laplace Hardy kernel:
8197ff458b51e41720a7e279d9bcb06cd8279e82f8434172393ac0e0d7bbee18;
unitary dilation coherent states:
60b4b69279e090fcb70a620dfce40ee733cd45b5eb7130c7be0367fe7381a536;
two channel positive convolution Schur contraction:
6e6a3728532005a5d4b4ca5aec2a8fcbd0b53d862c61093a62735604f73cac3e.
