# The existing Abel lift forces a single KPS quotient

STATUS: ACCEPTED_LIMITED_PAPER; independently reviewed Q1--Q5.
Base: 3178cd4b617031ff14246c6a29249ed6f0b27720. Isolated analytic research.
FULL_V_SIGN: OPEN. RH: OPEN. Canonical production remains HOLD.

## Source, old construction, and exact question

Use the unchanged complete source r, Phi, q=Phi/Z and original V from
REPORT_2026-09-17_KPS_MOMENT_INTERFACE.md. In particular

    r(1/t)=t^(5/2)r(t), Phi(x)=exp(5x/2)r(exp(2x)),
    Z=xi(1/2), F(z)=int exp(izx)q(x)dx=xi(1/2+iz)/xi(1/2),
    mu_(2n)=int x^(2n)q(x)dx,
    b_n=2(2n-1)mu_(2n-2)/mu_(2n), n>=1.                  (1)

The published KPS sufficient class is B_P1: Bernstein--Pick with the
specified 1-separation of zeros/poles. Membership for an interpolant of
ALL values b_n would imply real zeros of F by KPS Theorem 4.4. It is not
known for theta. The previous report proved only b_(n+1)>b_n, and supplied
an explicit ordinary-Bernstein control with nonreal poles and nonreal zeros.

An older accepted construction is available in
REPORT_2026-09-13_VILLAIN_RADIAL_BRIDGE.md: q is the coordinate marginal of
a positive rotational law. The question now is whether its exact radius
removes the apparent freedom to choose a different Bernstein interpolant.
It does. This does not prove that any Bernstein interpolant exists.

## Q1. Reuse the actual positive Abel lift

The source is positive, even, strictly decreasing for x>0 and has
super-Gaussian decay with its fixed derivatives. Let

    g(a)=-(1/pi)int_a^infinity q'(x)/sqrt(x^2-a^2)dx,
    P(R in da)=2pi a g(a)da, a>=0,
    U uniform on [0,2pi), independent of R.

The pinned Abel report proves g>=0, total planar mass 1, and R cos U has
exactly density q. We reuse this construction, not the unproved finite
Villain realization. Put

    I_*=R^2/4,  w_*(v)=4pi g(2sqrt(v)), v>0.              (2)

It is a positive probability law. For each n>=0, the elementary angular
integral E cos(U)^(2n)=(2n)!/[4^n(n!)^2] gives

    m_*(n):=E I_*^n = (n!)^2 mu_(2n)/(2n)!.              (3)

This identity keeps all source modes. In particular the KPS values are

    b_n=n m_*(n-1)/m_*(n).                              (4)

All exponential moments of I_* exist. Indeed Tonelli and q'<0 give, for
c>0,

    E exp(c I_*)
     =-2 int_0^infinity q'(x)
          int_0^x a exp(ca^2/4)/sqrt(x^2-a^2) da dx
     <=-2 int_0^infinity x q'(x)exp(cx^2/4)dx<infinity.  (5)

The last inequality is paid by the full differentiated theta tail. Thus
I_* is moment determinate; alternatively its moment generating function
is entire by dominated convergence on bounded complex sets.
At the origin, g is continuous and finite. To see this, set
x=sqrt(a^2+y^2) in its defining integral:

    g(a)=-(1/pi)int_0^infinity q'(sqrt(a^2+y^2))
                                   /sqrt(a^2+y^2) dy.

The quotient extends continuously at zero, and full derivative decay pays
a common majorant for bounded a. Hence w_* is bounded near zero. As a
consequence, m_*(u) exists for every real u>-1, including the negative
fractional moments used below.

## Q2. Every hypothetical BF interpolant must produce this same radial law

Let phi be any Bernstein function with phi(n)=b_n for all n>=1. Its
standard Levy--Khintchine representation constructs a possibly killed
subordinator S_t with

    E[exp(-u S_t); t<zeta]=exp(-t phi(u)), u>0.

Define J_phi=int_0^zeta exp(-S_t)dt. The nonzero data b_1>0 imply
phi(u)>0 for every u>0. Its standard integer moment formula is

    E J_phi^n=n!/product_(k=1)^n phi(k).                 (6)

For completeness, the more general identity is derived in Q3, so the
moment formula is not used as an unexplained sign-transfer theorem.
Equations (4),(6) telescope to E J_phi^n=m_*(n) for every integer n>=0.
Moreover phi(k)>=phi(1)>0, so these moments are at most
n!/phi(1)^n. By Tonelli J_phi has a finite exponential moment for any
0<c<phi(1). The identical moments give the same moment generating function
near zero as I_*. Uniqueness of the Laplace transform therefore proves

    J_phi has exactly the law of I_*.                  (7)

This is conditional on existence of phi, not an assertion that the old
positive Abel law automatically is a subordinator exponential functional.

Published orientation: KPS, AIF74(1)(2024), equations (5.17)--(5.18),
pp409--410, state this exponential-functional construction and its integer
moments. DOI https://doi.org/10.5802/aif.3600 ; PDF
https://aif.centre-mersenne.org/item/10.5802/aif.3600.pdf , SHA256
05f75d661af5d94d64c5c66b6a9c1ee22a73d53e13c5afd8ceb7a76a5cf14a19.
The standard existence of a killed subordinator for a Bernstein exponent
is the only stochastic construction imported here. No assertion about
xi in that article is imported as a proved source property.

## Q3. The real-parameter identity fixes the entire positive axis

First Tonelli gives E J_phi=int_0^infinity exp(-t phi(1))dt
=1/phi(1)<infinity, so J_phi is finite almost surely. It is strictly
positive almost surely by right continuity at time zero and positive
lifetime. Write A_t=int_t^zeta exp(-S_s)ds, zero after killing. Before
killing it decreases absolutely continuously, and for any real u>0,

    J_phi^u=u int_0^zeta exp(-S_t) A_t^(u-1)dt.          (8)

Integrate first up to a time where A_t>0 and then take a monotone limit;
this handles u<1. At a deterministic t on survival, independent stationary
increments and the memoryless killing law give A_t=exp(-S_t)J_phi', with
J_phi' independent and distributed like J_phi. Tonelli gives

    E J_phi^u=[u/phi(u)] E J_phi^(u-1).                 (9)

Finiteness follows recursively for integer u starting at E J^0=1.
For general u>0, positive moments follow by interpolation between integer
moments.
Tonelli in (9), whose other factor is finite and positive, then also
establishes the required negative fractional moment when 0<u<1.
Thus no unproved inverse-moment assumption is used in (9).

Together with (7), this forces, for every real u>0,

    phi(u)=u m_*(u-1)/m_*(u).                          (10)

Now set rho(s)=q(sqrt(s)), and define

    D(u)=int_0^infinity s^(u-1/2)rho(s)ds,
    N(u)=int_0^infinity s^(u-1/2)[-rho'(s)]ds,
    phi_*(u)=4N(u)/D(u).                               (11)

For real u>0 these are finite and strictly positive. A direct Abel
calculation identifies (10) with (11). Specifically, from (2),

    w_*(v)=-4 int_(4v)^infinity rho'(s)/sqrt(s-4v)ds,
    m_*(u)=-4^(-u)B(u+1,1/2)
                          int_0^infinity s^(u+1/2)rho'(s)ds, u>-1.

Tonelli licenses this because -rho'>0. Dividing the formulas for u-1
and u, and using B(u,1/2)/B(u+1,1/2)=(u+1/2)/u, gives (10)=(11) after

    int s^(u+1/2)[-rho'(s)]ds=(u+1/2)D(u).

Both boundary terms vanish for u>0. Hence any BF interpolation of the
integer data MUST be this explicit function phi_* on all of (0,infinity).
Conversely, if phi_* is Bernstein it interpolates those data by (3),(4).
In particular,

    exists phi in B_P1 with phi(n)=b_n for all n>=1
                 iff phi_* belongs to B_P1.             (12)

This removes interpolation freedom, not the unproved class membership.
The route's remaining sufficient hypothesis is now a specified quotient
of full-source integrals. If (12)'s right side were proved independently,
KPS Theorem 4.4 and the pinned coefficient identity would give real zeros
of F, hence RH and the pinned full-V conclusion. No extra unnamed property
is added after that hypothesis. It is a stronger sufficient route, not
asserted to be necessary for RH.

## Q4. Known domain and a precise analytic failure test

D and N are holomorphic on Re(u)>-1/2: near zero rho and rho' are bounded,
and at infinity their full-source tails dominate fixed powers and logs.
Thus their quotient is meromorphic on that half-plane, with positive
finite real values for u>0. The earlier covariance argument now gives

    phi_*'(u)=4 Cov_u(-rho'/rho, log s)>0, u>0,
    dP_u=s^(u-1/2)rho(s)ds/D(u).

The source's strict squared-coordinate log-concavity supplies this sign;
it supplies neither higher BF derivative signs nor Pick membership.
Any independently certified nonreal u0 with Re(u0)>-1/2, Im(u0)>0,
D(u0)=0 and N(u0)!=0 would produce a nonremovable upper-half-plane pole
and exclude B_P1 for this source and every alternative BF interpolant.
Zeros shared by numerator and denominator require their orders to be
checked; they cannot be declared poles automatically. Absence of such a
pole in a finite region would not establish the global class property.
No u0, pole, BF failure or Pick failure of actual theta is claimed here.

## Q5. Reciprocity alone has already become evenness at this interface

Let q0 be ANY positive even probability density with the necessary
exponential moments. Define

    C=[2 int_R exp(-x/2)q0(x)dx]^(-1),
    r0(t)=C t^(-5/4)q0((log t)/2), t>0.

Substitution t=exp(2x) proves int r0=1, and evenness proves EXACTLY

    r0(1/t)=t^(5/2)r0(t),
    exp(5x/2)r0(exp(2x))=C q0(x).                       (13)

Thus a weighted reciprocal identity of this exponent, by itself, adds no
restriction beyond evenness to this class of normalized logarithmic sources.
It cannot be spent a second time as an independent moment-sign theorem.
This does not address its joint action with additive PF or fixed square rates.

For q0 proportional to exp(-x^2)-exp(-2x^2)/4, (13) gives a positive
probability density with the exact exponent 5/2 reciprocity, while the
logarithmic source retains the known negative full-V row and the unique
non-Pick BF interpolation. It fails even additive PF2: as t->infinity,

    (log r0)''(t)=[(log t)/2+3/4+o(1)]/t^2>0.

The omitted correction is O((log t)^2 exp(-(log t)^2/4))/t^2, from
differentiating log[1-(1/4)exp(-(log t)^2/4)]. For sufficiently large t
and small h>0, r0(t)^2<r0(t-h)r0(t+h), which is a negative 2-by-2
translation minor. Hence this control does not refute a joint PF plus
reciprocity theorem. It identifies precisely the input still absent.

## Scope and next bounded test

The old Abel law and the KPS moment data are the same object after the
explicit radius change I_*=R^2/4. Every possible BF interpolant is forced
to (11); no choice of another field or another continuation on the positive
axis avoids that quotient. The fixed candidate can now be tested
analytically for the first genuinely missing BF/Pick/1-separation property,
using the COMPLETE source and all corrections. An actual-source failure
rejects this strengthened entrance only, not original V positivity or RH.
A successful proof of all B_P1 requirements has a closed conditional
consumer. Real-axis monotonicity, positive Abel mass, finite checks and
mere reciprocity are not that proof. No numerical campaign was run.
CONSUMPTION: INCOMPLETE_NO_CONSUMABLE_TARGET; isolated PAPER only.

## Independent acceptance

Candidate SHA256: `adce6cff13c9d1954c9499d95f7bc4748d144dd58d61ac3f365d4b4ce5562efb`.
Review SHA256: `2c1c6aa80117a4077e35a64ad19fb52343624ca5ab15b6909fb1e92389fc2c7a`.
Verdict: `ACCEPT_FORCED_KPS_QUOTIENT_AND_RECIPROCITY_SCOPE`.
Reviewer `/root/pairzero_geometry_review` checked all Q1--Q5, the pinned
source files, and the full radial/subordinator/Abel normalization. The full
review and independent parent check are embedded in the paired certificate.
Acceptance covers only the fixed-quotient reduction and the precisely scoped
reciprocity control. Actual Bernstein/Pick/1-separation membership, full V
positivity and RH remain open. No canonical or Lean admission is made.
