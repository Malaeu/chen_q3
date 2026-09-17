# Exact whole-integral compensation for the sextic brother

STATUS: ACCEPTED_LIMITED_PAPER; ACCEPT_SEXTIC_SPECTRAL_TAIL_COMPENSATION_CONTROL_ONLY.
Base: f0237d451168eb59a01fe19ec018462ed1bf460b.
ORIGINAL_THETA_V and RH: OPEN. No original negative witness.

## T0. Return point and decision

The fixed positive raw-response norm floor is excluded for the theta source.
The quartic source already has a direct Gram map, but its separate cancellation
layers are positive. This worked comparison addresses the harder geometry:
can a source have negative cancellation layers, no positive raw point-response
floor, and nevertheless an EXACT positive representation of the WHOLE V?

Yes, for the separately identified source f6(t)=exp(-t^6). Its Fourier
real-zero theorem was already proved in RECONSTRUCTION_CLASS_OBSTRUCTION R4;
it is not a new discovery. Here an explicit square-sum of Fourier TAILS
accounts for the entire integral and its boundary. It is derived without
taking a positive square root of V6. This is a worked compensation control,
not a new source identity for theta or a new RH criterion. In particular it
does not supply the unproved real-zero input for the actual theta transform.

Reconciled inputs: LAYER_GRAM_TEST L1--L9; RECONSTRUCTION_CLASS_OBSTRUCTION
R4 (the already positive sextic Fourier sibling); RAW_RESPONSE_FLOOR F3--F5;
SOURCE_GENERATOR_SUPPORT_AUDIT A2--A13; DIRECT_PICK_BRIDGE's already unpaid
real-negative-zero input on the actual normalized Mellin function H. This
uses a partial-fraction decomposition of the old Fourier multiplier iF'/F
WHEN its real-zero input is independently known, followed by a separate
tail-field realization. No unitary equivalence between the old full-line
generator and the discrete diagonal field operator is claimed or needed.
This is not a replacement for the old SUPPORT question.

## T1. The independent input for this OTHER source

For this note only, define

 f(t)=exp(-t^6), F(z)=int_R exp(-izt)f(t)dt,
 V6(x,y)=int_0^infinity (2t+x+y)f(t+x)f(t+y)dt.

This f is not Phi, not a truncation of Phi, and has no claimed prime-product
or modular source identity. Positive normalization rescales V6 harmlessly.
All real nodes and all finite complex coefficient rows are considered.

For rho(s)=exp(-s^3), direct Gamma integration and triplication give

 D6(u)=(1/3)Gamma((u+1/2)/3),
 H6(u)=D6(u)/Gamma(u+1/2)
      =2pi*3^(-u-1)/[Gamma(u/3+1/2)Gamma(u/3+5/6)].       (T1)

The last expression is entire of order at most one, positive on u>=0,
and has only negative real zeros. The classical Laguerre coefficient
theorem, already checked in the pinned primary Baricz--Singh, Lemma 1,
printed p.2, applies: an entire real function of order less than two with
only negative real zeros has an exponential coefficient transform with
only negative real zeros. The exact moment identity is

 F(z)=sqrt(pi) sum_(n>=0) H6(n)(-z^2/4)^n/n!.            (T2)

Thus F has only real zeros, with multiplicities allowed. Dominating by
exp(R|t|-t^6) pays every compact z-set. Young's inequality also gives
|F(z)|<=C exp(C'|z|^(6/5)), hence order at most 6/5<2.
F is even, real on the real axis, and F(0)>0. Its real zeros can therefore
be listed as pairs +/-gamma, gamma>0, each counted with its multiplicity,
and Hadamard factorization gives

 F(z)=F(0) product_(gamma>0)(1-z^2/gamma^2),
 sum_(gamma>0) gamma^(-2)<infinity,
 F'(z)/F(z)=sum_(gamma>0)[1/(z-gamma)+1/(z+gamma)].       (T3)

Evenness removes a linear exponential factor and order less than two
excludes a quadratic one. All products and logarithmic derivatives in T3
converge locally uniformly away from the zeros. No assertion of simple
zeros, explicit zero positions, or positive matrices is used here.

## T2. A field constructed by tails, with estimates at BOTH ends

For each signed zero gamma define the scalar tail

 T_gamma(t)=int_0^infinity exp(i gamma s) f(t+s)ds.       (T4)

Because F(-gamma)=0, this is ALSO

 T_gamma(t)=-int_(-infinity)^0 exp(i gamma s)f(t+s)ds.   (T5)

The equality is what pays the negative-t endpoint; discarding it would
give an incorrect integrability assertion for a generic frequency.
Differentiating, or integrating once by parts, yields exactly

 T_gamma'(t)=-f(t)-i gamma T_gamma(t).                  (T6)

Put

 A1(t)=|f(t)|+min(int_(-infinity)^t |f'(v)|dv,
                 int_t^infinity |f'(v)|dv),
 A2(t)=|f'(t)|+min(int_(-infinity)^t |f''(v)|dv,
                  int_t^infinity |f''(v)|dv).

Both are integrable with every polynomial weight, and decay rapidly at
both ends. One integration by parts in either T4 or T5, then choosing
the smaller tail, proves

 |T_gamma(t)|<=A1(t)/|gamma|.                           (T7)

Two integrations by parts cancel the leading terms in opposite frequencies:

 |T_gamma(t)+T_(-gamma)(t)|<=2 A2(t)/gamma^2.            (T8)

All derivatives of f have the required rapid decay. These estimates use
actual zero frequencies and hold with constants independent of gamma.
In particular each tail is in L1 and L2, and the paired series of T8
converges in weighted L1 for every polynomial weight.

## T3. Exact reconstruction of t f(t), not an assumed energy law

Use the Fourier convention of T1. Equation T6 gives

 hat(T_gamma)(omega)=i F(omega)/(omega+gamma),           (T9)

with its removable value at omega=-gamma. Fourier transforms of the paired
series can be taken termwise by T8 and summability in T3. At real omega
away from the zeros, T3 identifies their sum with i F'(omega). Fourier
uniqueness in L1 then proves, everywhere by continuity,

 t f(t)=sum_(gamma>0)[T_gamma(t)+T_(-gamma)(t)].         (T10)

The summation is paired. We never assert absolute summability of the
UNPAIRED scalar T_gamma series. Equation T10 reconstructs the same flux
factor t f(t), not a surrogate with a chosen normalization.

## T4. The whole original-form integral is a sum of squares

For real x,y, T6 and real gamma give

 -d/dt[conj(T_gamma(t+x)) T_gamma(t+y)]
   =f(t+x)T_gamma(t+y)+conj(T_gamma(t+x))f(t+y).         (T11)

Integrate over the FULL physical half-line. The boundary at infinity is
zero by T7; the boundary at t=0 is retained. Sum finite symmetric sets
of zero pairs, then take their limit using T8 for the integrated flux.
The resulting boundary series is absolutely convergent by T7 and T3.
With T10, the exact identity is

 V6(x,y)=sum_(gamma signed) conj(T_gamma(x))T_gamma(y).
                                                               (T12)
Thus Psi_x=(T_gamma(x)) belongs to ell2 of the zero multiset, and

 V6[c]=sum_(gamma signed)|sum_i c_i T_gamma(x_i)|^2>=0  (T13)

for EVERY finite complex row, with arbitrary real shifts. Cauchy--Schwarz
or T7 pays mixed sums; no rank restriction or discarded cutoff term occurs.
Repeated zeros mean repeated equal coordinates, i.e. their correct positive
multiplicity. T11 proves that the sign arises from the COMPLETE flux and
its boundary, not from positivity of its separate integral pieces.

## T5. This SAME positive example has negative cancellation layers

Apply the old exact cancellation variable, now to f6:

 m=(x+y)/2, d=(x-y)/2,
 K_s(x,y)=f(sqrt(s+m^2)+d)f(sqrt(s+m^2)-d),
 V6(x,y)=int_0^infinity K_s(x,y)ds.                    (T14)

For x,y>0, K_0=f(x)f(y). Normalize W_s=K_s/(f(x)f(y)).
The old exact tangent calculation, with q=f'/f=-6x^5, gives

 J(x,y)=partial_s W_s|_0=(q(x)+q(y))/(x+y)
       =-6(x^4-x^3y+x^2y^2-xy^3+y^4),
 C(x,y)=partial_x partial_y J=18x^2-24xy+18y^2.         (T15)

For any distinct positive a,b, C(a,a)=12a^2, C(b,b)=12b^2,
C(a,b)=12ab+18(a-b)^2, and

 det C_{a,b}=-108(a-b)^2(3a^2-2ab+3b^2)<0.            (T16)

Choose v=(-C(a,b)/C(a,a),1), so v^T C v<0. Replace each derivative
evaluation at a,b by a sufficiently small forward difference. The combined
four-node functional z_epsilon has coefficient sum zero, and
z_epsilon^T J z_epsilon tends to v^T C v<0. Fix a small epsilon BEFORE
taking s down to zero. Then

 z_epsilon^T W_s z_epsilon
    =s z_epsilon^T J z_epsilon+o(s)<0                  (T17)

for every sufficiently small s>0. Congruence by 1/f at these four nodes
returns an actual negative K_s row. The a,b and forward differences can
lie inside any prescribed open positive interval; simultaneous reflection
places them inside the original negative I. This uses a fixed finite row
for all sufficiently small s, not a different row at each layer.

Nevertheless T13 says its INTEGRATED V6 is nonnegative. Thus the exact
square-sum T12 actually reconciles the type of negative-layer obstruction
found for theta. It does not rely on a sibling whose layers were positive.

## T6. No raw point-response floor, yet a positive full energy

For this same f6, -f'/f=6t^5 on t>0. If R>0 and L_R=6R^5,
f(R+s)<=f(R)exp(-L_R s). Exact evenness gives

 0<V6(-R,-R)/f(-R)^2
   <=R/L_R+1/(2L_R^2) ->0.                            (T18)

Both V6 and f(x)f(y) extend holomorphically to C x C (sextic decay is
uniform for bounded complex shifts). The already accepted all-rank analytic
propagation lemma therefore excludes V6>=kappa f(x)f(y) on all finite
rows of any open interval, for every kappa>0. This is only the point
measure delta_0 comparison, not the entire theta F1 weight class.

Consequently Psi_x in T12 cannot have a bounded linear scalar readout
returning f(x). This is fully compatible with T6: taking a derivative
of a selected tail coordinate is not a bounded scalar observation of the
pointwise ell2 vector Psi_x. No closability or domain claim for such a
derivative is needed. The explicit energy exists despite the excluded floor.

## T6a. An explicit space in which the singular input is well defined

There are infinitely many signed zeros: otherwise T3 would make F a
polynomial, contradicting its real-axis decay and F(0)>0. Define

 H=ell2(gamma),
 H_-1={v:sum_gamma |v_gamma|^2/(1+gamma^2)<infinity},
 b=(1)_gamma, A:H->H_-1, (Az)_gamma=-i gamma z_gamma.

Then b belongs to H_-1 by T3, and A is bounded between the stated spaces.
The Fourier transform of f' also vanishes at every signed zero. Applying
the same two-end estimate to f' gives

 |T_gamma'(x)|<=A2(x)/|gamma|.

This bound is uniform on compact real x-intervals. Finite truncations and
their derivatives converge uniformly there in H, so x->Psi_x is C1 into H.
The coordinate equations T6 therefore give an actual vector identity

 Psi'_x=A Psi_x-b f(x) in H_-1.                        (T19)

Two integrations by parts also show gamma T_gamma(x)->i f(x)!=0 as
|gamma|->infinity. Thus Psi_x is NOT in the H-domain of diag(gamma),
which requires sum gamma^2|T_gamma(x)|^2<infinity. The two terms on
the right of T19 separately fail to lie in H, but their difference does
lie in H and equals Psi'_x. This is explicit cancellation in a larger
space, with the positive energy still measured in H. It does not assert
an ordinary H-domain generator equation, a bounded input in H, a closable
scalar readout, or a source-preserving construction for theta.

## T7. Mapping back to theta and exact stopping condition

For theta, the same candidate tails at known real zeros exist and obey
their first-order equations. The sum over ONLY known real zeros, however,
cannot be declared to reconstruct t f(t): T3 would require accounting
for ALL zeros of the actual F, and excluding nonreal zeros is RH. Assuming
T3 for actual F would insert the desired conclusion into the construction.

For f6 the entrance was instead paid by the explicit Gamma quotient T1
and the classical coefficient preserver T2. For theta the actual H is a
different entire function; the old DIRECT_PICK_BRIDGE leaves its negative
real-zero property open. Neither the Gamma triplication identity for H6,
source-tail bounds, negative-layer compensation nor the existence of a
skew-adjoint generator pays that property for actual H.

This is a worked all-rank compensation model, not a new unproved request
to build a reservoir or repeat SUPPORT/Pick. A source-specific entrance
remains necessary before applying this mechanism to original V. No new
Pro proof job, original sign result, negative theta row, canonical admission,
Lean certification, or source-sign counter reset follows.

AUTOPSY: dropped=OBJECT_IDENTITY; note=The exact spectral-tail square sum is proved for the independently real-zero sextic source; its real-zero entrance is unproved for the theta source and cannot be assumed in the transfer.

## Independent acceptance

Final candidate SHA256: c218cb435f809049fabb41e026202d3249cfaaf1b6c4484762e71e3435fbecf0.
Complete review SHA256: 99fed03389ce6997ea84d3965f9af0d3ce4a97bbf1be19c5e311c48e711f575a.
Parent check SHA256: 2162b7909b67dc960b706998e5dd520703b962e7397baad740a2efd8c61f2582.
Reviewer: /root/pairzero_geometry_review. The full review was read and its distinction between multiplier partial fractions and distinct field generators was incorporated before final acceptance. T1--T19 establish only the exact sextic compensation control, its negative layers, absence of a point floor, and the larger-space input equation. They do not establish a real-zero entrance, full V sign, or RH for theta. No Lean or canonical admission is claimed.
