# Structured zero: null integrals, weighted compensation and score information

STATUS: ANALYTIC_PAPER_AND_SOURCE_HUNT; exact review belongs to the certificate.
SOURCE_BASE: 1c792b3e2474ee642362c8826e3dcb2eec80c988.
CONSUMPTION: INCOMPLETE_NO_CONSUMABLE_TARGET; isolated owner-requested research.
FULL_THETA_V / IC / ODD2 / RH: OPEN. ACTUAL_NEGATIVE_V_WITNESS: NONE.
PX_RH_CLAIM: NOT_MADE.

## 1. Unchanged target and the precise meaning of zero

Keep f=Phi/||Phi||_2, the COMPLETE positive even theta source, and
I=(-log(2)/2,0). For arbitrary finite x_i in I and complex c_i,

    P(X)=sum_i c_i f(X+x_i), Q(X)=sum_i c_i(X+x_i)f(X+x_i),
    V[c]=2 Re integral_0^infinity conjugate(P)Q dX.          (Z1)

Source pins under docs/Codex:

| Report | SHA256 | Used scope |
| --- | --- | --- |
| REPORT_2026-09-13_NULL_AND_GROUND_STATE_TEST.md | 19ce3481523bfb3f3f9ba8be24f2c86dc2f1916d80f9535a451d010bceef0d95 | T1-T2, N and its actual nonzero boundary |
| REPORT_2026-09-13_RESIDUAL_COMPENSATION_HUNT.md | 7aaf8e43faa5bfd37954d6076db3acb1801325777bd9d989b25d75c9a9466c14 | R1-R3 full endpoint bounds, R6-R9 score and correction accounting |
| REPORT_2026-09-15_INTEGRATED_SIGN_HUNT.md | 8560b8c70e35fd76dbb2820471440aa802cefe21f9928e957c9f2e0be7dbe8eb | Existing partial signs and cutoff obstruction |
| REPORT_2026-09-14_FIRST_ORDER_COMPENSATION_PREFLIGHT.md | 758eb21c80cb405fa242bc5e6a6ce38053cbe9edc997752ac01480aa5c6c55e7 | Existing local (P,P') storage obstruction; not reopened |

The three relevant zeros are different:

* A quantity identically zero has no hidden additive value.
* A signed integrand can be nonzero although its FULL integral is zero.
* A random variable can have mean zero although its mean square is positive.

The second case can redistribute the integrand before completing squares.
The third exposes a quadratic quantity, but does not authorize adding it to
V without the term which balances it. For a fixed finite family, a Hermitian
matrix Z with c*Zc=0 for EVERY complex c is itself zero, by polarization.
Nontrivial compensation therefore uses the representation, domain or
differential constraints, not a new nonzero quadratic form that vanishes on
all unconstrained coefficient vectors.

The saved brief preceded three new shelf queries: null Lagrangian/differential
constraint; carre du champ/quadratic variation; score/Fisher normalization.
All returned INCOMPLETE freshness, exit 2. Raw hashes and primary-source
artifacts are in the certificate; no absence or semantic admission is claimed.
Prior null-boundary, Stein/covariance and integral-sign results were reconciled.

## 2. Verified sibling: a nonzero null integrand pays the entire sign

Primary source: J. M. Ball, J. C. Currie and P. J. Olver, *Null Lagrangians,
weak continuity, and variational problems of arbitrary order*, JFA 41 (1981),
135-174, DOI 10.1016/0022-1236(81)90085-9,
[author PDF](https://people.maths.ox.ac.uk/~ball/Papers/Ball%2C%20Currie%20%26%20Olver%201981.pdf).
Locators: definition (3.1) p.139, Theorem 3.1 p.140, Theorem 3.4(ii) p.143,
and divergence identity (4.2) p.150. Quote at p.150:
"each Jacobian determinant is a divergence".
PDF SHA256: 0a9af1c9c082c9baf98af0bf5e90fa20c72a8aae303716f6540faa89ac08f3e7.

The source characterizes null Lagrangians; it does not identify our V with
one of its variational forms. The following concrete example is derived
directly here. Let u=(u1,u2) be smooth and compactly supported in a planar
domain Omega, with coordinates X,Y. First take real u and set

    a=partial_X u1, b=partial_Y u1,
    c=partial_X u2, d=partial_Y u2,
    J=ad-bc,
    Q0=a^2+d^2+2bc.

Commuting mixed derivatives proves

    J=partial_X(u1 partial_Y u2)-partial_Y(u1 partial_X u2),
    integral_Omega J=0.                                    (Z2)

The boundary vanishes because the field is compactly supported. Pointwise,

    Q0+2J=(a+d)^2,
    integral_Omega Q0=integral_Omega (div u)^2>=0.           (Z3)

Yet Q0 can be strictly negative on an open region: choose u=(Y,-X) there
and smoothly cut it off outside a larger interior region. There a=d=0,
b=1,c=-1, so Q0=-2 and J=1. The cutoff region supplies the required
compensation. This is a complete example of positive FULL integral despite
negative local density; J itself is not zero pointwise.

For complex u, use

    J=Re(a conjugate(d)-b conjugate(c)),
    Q0=|a|^2+|d|^2+2 Re(b conjugate(c)).

The same divergence identity with real parts gives integral J=0 and
integral Q0=integral |a+d|^2. Equivalently apply the real result to the
real and imaginary parts. Thus the mechanism itself respects complex rows.

Exact theta fit: UNVERIFIED. We must construct a linear source-defined
c -> u_c and prove that its full energy, including boundary terms, equals
Z1. The differential condition that a,b,c,d come from the SAME field and
the boundary condition are indispensable; arbitrary four functions do not
satisfy Z2.

## 3. Bounded preflight: the physical weight changes the null identity

Set w(X)=f(X)^2 and q=f'/f. For compactly supported u in
Omega=(0,infinity) x R, the ordinary J in Z2 satisfies exactly

    integral w J=-integral w' Re(u1 conjugate(partial_Y u2)). (Z4)

Therefore its unweighted zero cannot simply be carried into a weighted
formula. The right side has no automatic sign for arbitrary fields.

There is an EXACT way to keep a null identity with this weight. Define

    D_X u=partial_X u+q u=f^(-1) partial_X(f u),
    J_f=Re(D_X u1 conjugate(partial_Y u2)
              -partial_Y u1 conjugate(D_X u2)),
    Q_f=|D_X u1|^2+|partial_Y u2|^2
              +2 Re(partial_Y u1 conjugate(D_X u2)).

Put v=f u. Since f depends only on X,

    w J_f=J(v),
    Q_f+2J_f=|D_X u1+partial_Y u2|^2,
    integral w J_f=0,
    integral w Q_f=integral w |D_X u1+partial_Y u2|^2>=0.    (Z5)

This is a full weighted sibling proof, for every such complex field. It
uses the ACTUAL theta weight without a mode truncation; compact support
makes all operations legitimate. The same proof works for every smooth
positive f. The correction is prescribed, not a freely chosen constant.

The price is visible already before integration:

    Q_f-Q0=2q Re(partial_X u1 conjugate(u1))+q^2 |u1|^2
                      +2q Re(partial_Y u1 conjugate(u2)).  (Z6)

These terms cannot be suppressed when matching Z1. Nor may the actual
source profiles be treated as compactly supported fields without proving
the resulting boundary/limit identity. Z5 establishes positivity of Q_f,
not V. In particular it does not overcome the previously proved obstruction
to local storage depending only on the aggregate (P,P').

NEGATIVE CONTROL: f0(u)=exp(-u^2)-exp(-2u^2)/4 is positive and even with
strictly concave log f0(sqrt(s)), but its V0 has a negative four-node row
(FULL_V_RANK_TWO_INTAKE R9-R12). Z5 remains valid with f=f0. Consequently
the missing discriminating premise is the identification of the target with
this positive field energy and its boundary conditions. It is not merely
the existence of a weighted null identity.

## 4. Actual theta: differentiating a zero mean leaves a nonzero term

Primary source: Scott Linderman, STATS 305B, *Basics of Probability and
Statistics*, section "Fisher Information Matrix",
[lecture notes](https://slinderman.github.io/stats305b/lectures/01_distributions.html#fisher-information-matrix).
Quote: "The expected value of the score is zero".
HTML SHA256: c5f63559e04cc3d90b22f9ec05b66398789f005e9a7a40a8931ce153df9cf2e5.
The source gives the zero mean and the score-square/negative-expected-Hessian
identity under regularity. We check the relevant regularity for our density.

Let r=h*h and use the exact conditional density and score from R1,R6:

    p_t(s)=t h(ts)h(t(1-s))/r(t), 0<s<1, t=exp(2X),
    rho_t(s)=partial_X log p_t(s), I(t)=E_t rho_t^2.

All X derivatives below hold s fixed. Differentiating the normalization
twice gives

    E_t rho_t=0,
    0=partial_X(E_t rho_t)
     =E_t(partial_X rho_t)+E_t rho_t^2,
    E_t(partial_X rho_t)=-I(t).                            (Z7)

Domain check: on any compact X interval, the complete-source endpoint
expansion R2 and its differentiated remainders bound p_t times each needed
inverse endpoint power by an integrable exponential. Away from s=0,1 all
functions are smooth and positive. This justifies both derivatives under
the s-integral. No infinite X-integral or interchange at X=infinity is used.
The same endpoint expansion, or R6 with b0(u)=pi/(4u)-5/2+O(u), gives

    rho_t(s)=pi/(2ts)+O(1) as s decreases to 0.

Thus rho_t is not identically zero, and its positive density implies I(t)>0.
For every fixed finite X>=0 the right side in Z7 is STRICTLY negative.
This is the exact term lost by an invalid interchange of differentiating
with averaging against a changing probability law.

It is not a newly discovered error in the earlier project formulas: R7
already retained the score commutator. Z7 states a useful additional direct
consequence. It proves neither the sign of E_t(rho_t |z|^2) for arbitrary z,
nor a comparison of the full M and L. The Fisher quantity is already a
property of the given density; it is not a free positive contribution to V.

For the existing centered variable z=g-E_t g, E_t z=0 and E_t|z|^2=F.
That positive variance was already retained in L, which is SUBTRACTED in
V=M-L. Treating it as a newly available positive addition changes the target.

Control scope: the normalization identity holds for any sufficiently regular
positive probability family. No corresponding conditional lift for the
specific f0 control is assumed here. A zero-mean identity by itself has no
source-specific implication for V, irrespective of how that lift is chosen.

## 5. A second name for the quadratic part: carre du champ

Primary source: C. Ane and M. Ledoux, *On logarithmic Sobolev inequalities
for continuous time random walks on graphs*, PTRF 116 (2000), 573-602,
DOI 10.1007/s004409900042,
[author PDF](https://pages.stat.wisc.edu/~ane/publis/aneLedoux00.pdf).
Locators: section 3, proof of Proposition 3.1, pp.582-583, equation (3.3),
and sharpness on p.585. Quote: "(3.3) is sharp on the function f(x) = x".
PDF SHA256: 3efee45e54827478d569a11ccbc712a0921e5d26ccfe578ecc3261c5eff1105d.

Use tau for the paper's time, to avoid identifying it with our t=exp(2X).
The paper takes Lh(n)=h(n+1)-h(n) and P_tau with generator L/2. Thus
P_tau h(n)=E h(n+N), N Poisson with parameter tau/2. Its product defect is

    2 Gamma(h,k)=L(hk)-h Lk-k Lh,
    2 Gamma(h)(n)=(h(n+1)-h(n))^2,
    P_tau(h^2)-(P_tau h)^2<=tau P_tau Gamma(h).             (CD)

For h(n)=n, Gamma(h)=1/2 and the centered z=N-tau/2 has
E z=0 but E z^2=tau/2>0 for tau>0; CD is an equality. The proof integrates
the derivative of P_s((P_(tau-s)h)^2). This supplies a precise process-side
name for a quadratic defect which remains after averaging to zero.

Theta fit is only a structural analogue: our F=E_t|g-E_t g|^2 is the same
type of product defect, but E_t has not been identified with this semigroup.
No theta generator, time conversion or Gamma-to-full-loss comparison follows.
The score rho in Z7 is not asserted to be this generator. Complex covariance
in the actual target cannot be replaced by this single real Poisson example.
The generic existence of centered fluctuations supplies no distinguishing
hypothesis against f0; the actual operator and energy transfer remain unpaid.

## 6. Decision and exact next construction

The owner's structured-zero idea has a precise successful mathematical
example, Z2-Z3, and an exact version preserving the theta weight, Z4-Z6.
Z7 also shows literally how a derivative of a zero mean contains two
nonzero cancelling terms. None requires declaring zero unequal to zero.

The next bounded construction must supply the common map c -> u_c (or an
equivalent source-defined differential constraint) and an equality

    V[c]=integral f^2 |D_X u_(c,1)+partial_Y u_(c,2)|^2
                           + B[c], B[c]>=0,               (Z8)

or another explicitly stated positive form. Z8 is an UNPROVED candidate
interface, not a conclusion of this report. It must include every term of
Z6 and every boundary term. The map and boundary sign cannot be defined
by assuming V is already positive or tailored separately to each row's sign.
Because f0 also admits Z5, its failure of the proposed identification must
be made explicit when a map is actually offered.

No new bound on full V, actual negative V witness, Lean closure, canonical
admission or Proshka request is produced. Searches are bounded; the existing
negative-layer, null-boundary and local-state exclusions remain in force.
