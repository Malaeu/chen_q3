# Quick energy-transfer test on the actual conditional fields

Date: 2026-09-16. Base: `105062d6f55bd75b96d4c2485749e2f07022c891`.
STATUS: INDEPENDENTLY_REVIEWED_ANALYTIC_PREFLIGHT; exact scope and reviewed hash in the accompanying certificate.
Scope: an explicit primitive of the existing conditional fluctuation, its
Dirichlet gap, and its exact location in V=M-L. No RH, full-V sign, Lean or
canonical admission. This does not exclude other energy representations.

## P1. Exact inputs, with the mean retained separately

Use the full source and definitions of REPORT_2026-09-13_BROWNIAN_DILATION_CONDITIONAL.md
sections 1-4 and REPORT_2026-09-13_RESIDUAL_COMPENSATION_HUNT.md R1-R5.
For t=exp(2X), X>=0, and s in (0,1),

    p_t(s)=t h(ts)h(t(1-s))/r(t),  r=h*h,
    g_x(t,s)=a^(9/4) h(ats)h(at(1-s))/(h(ts)h(t(1-s))), a=exp(2x),
    g=sum_i c_i g_xi, b=sum_i c_i x_i g_xi,
    m=E_t g, beta=E_t b.

All families are finite, c_i complex, x_i in I=(-(log 2)/2,0).
p_t, g and b are reflection symmetric under s->1-s. For fixed t the
profiles extend continuously to both endpoints, by the full-source estimates
in R2-R3. In particular they are in L2(p_t ds).

Let H_t(s)=integral_0^s p_t(v)dv and q_t its inverse. Here H_t is a CDF,
not a Hankel operator, and q_t is a quantile, not f'/f. Positivity of p_t
makes H_t continuous and strictly increasing; symmetry gives
q_t(1-v)=1-q_t(v). Define, for v in [0,1],

    z_g(v)=g(t,q_t(v))-m,
    u_g(v)=integral_0^v z_g(w)dw,

and the same definitions for b. Values at v=0,1 are interpreted by limits.
The probability change of variables sends p_t ds exactly to dv. Therefore

    integral_0^1 z_g=0,
    u_g in H_0^1(0,1),  u_g'=z_g,
    Var_t(g)=integral_0^1 |u_g'|²=:E[u_g],
    Cov_t(g,b)=integral_0^1 conjugate(u_g')u_b'=:E(u_g,u_b).    (P1)

This is a source-defined linear map on the entire finite family. It uses
the conditional field, not a rough Brownian sample path. Its derivative
energy is finite on every fixed fibre without a new smoothness assumption.

## P2. Symmetry removes the first sine mode

z_g(1-v)=z_g(v), and its integral is zero. Hence

    u_g(1-v)=-u_g(v),   u_g(0)=u_g(1/2)=u_g(1)=0.

The same holds for u_b and every complex linear combination. In the
Dirichlet sine expansion only even indices n survive, since
sin(nπ(1-v))=(-1)^(n+1)sin(nπv). Parseval on H_0^1 yields

    E[u_g] = sum_(n even, n>=2) π²n² |a_n|²
           >=4π² sum_(n even, n>=2) |a_n|²
           =4π² integral_0^1 |u_g|².                         (P2)

The coefficient is sharp on the full antisymmetric H_0^1 subspace, by
u(v)=sin(2πv). We do not claim that this equality profile is attained by
the particular theta likelihood span, or that 4π² is optimal on that span.
The ordinary π² spectral statement is classical; its explicit sine basis
also appears in Habermann, Brownian bridge expansions, §2.1 [S1].

## P3. Where the energy actually occurs in the target

The complete source identity, with the physical weight and cutoff, becomes

    L[c]=2 integral_0^infinity f(X)²
             [X E[u_g]+Re E(u_g,u_b)] dX,                    (P3)
    M[c]=2 integral_0^infinity f(X)²
             [X (|m|²+E[u_g])+Re(conjugate(m)beta+E(u_g,u_b))] dX,
    V[c]=M[c]-L[c]
        =2 integral_0^infinity f(X)²
             [X |m|²+Re(conjugate(m)beta)] dX.               (P4)

These are exact equalities, with no integration by parts in X and no
discarded boundary. The original weighted L2 bounds for G,XG,B ensure
absolute integrability of all displayed terms; the mixed energy is bounded
by sqrt(Var_t(g)Var_t(b)). The means have the corresponding Jensen bounds.

P2 provides a LOWER bound on the variance energy appearing inside L. It
provides neither an upper bound on the complete mixed expression L nor a
lower bound M>=L. M itself has not been proved nonnegative. In P4 the
fluctuation energy cancels exactly, and the sign is in the means and their
node-weighted companion beta. The likelihood family links these means to
fluctuations, but P2 alone establishes no useful inequality for that link.

No prime-specific input is used in P1-P2: symmetry and probability
normalization suffice. The known Gaussian-deformed controls keep the same
p_t and multiply each g_x by a fibre-constant factor. Thus P1-P2 also hold
there, while earlier project results give negative full-V rows. This is a
reused discrimination test, not a new negative witness for the true source.

## P4. Cheap null-profile check on an exact energy identity

At the limiting node x=0, g_0=1, hence u_g=0. Nevertheless

    V(0,0)=2 integral_0^infinity X f(X)² dX>0.                (P5)

This endpoint is not in I; the mismatch is a legitimate limiting test.
As x->0 from I, g_x->1 on each fibre and Var_t(g_x)->0. For x in a fixed
compact interval [x_0,0], exp(2x_0)>1/2, the established full-source bound
g_x<=exp(π(1-exp(2x_0))t) and the theta decay of f² give an integrable
dominating function after multiplication by (1+X)f². Consequently

    integral_0^infinity (1+X)f² E[u_gx] dX ->0,
    integral_0^infinity (1+X)f² ||u_gx||² dX ->0,
    V(x,x)->V(0,0)>0.

The second limit uses P2; the last follows directly from the full-source
shift integral and its uniform tail bound. Therefore V cannot equal a
fixed finite linear combination of these two fluctuation-only energies.
This excludes that exact identification. It does NOT exclude a lower
comparison, a map retaining the means, singularly rescaled maps with
separately checked domains, or a different full-field energy.

## P5. What an admissible rebuild of V must accomplish

Changing coordinates with an invertible S on a finite row gives
W[d]=V[Sd], matrix W=S*KS. This preserves positivity in BOTH directions:
each old vector is Sd for some d. It may reveal a proof, but cannot erase
a negative direction. A common linear source map into a Hilbert space
also suffices if an independently proved identity V[c]=positive_energy(Tc)
holds for every original finite family, including all boundaries.

A different object W is useful only with a proved sufficient arrow back
to the original target, for example V[c]>=W[Tc]>=0 for all c. Positivity
of W alone is insufficient. This is not hypothetical: the already accepted
HANKEL_JORDAN_PREFLIGHT H2-H4 proves V(x,y)/(x+y) positive on reflected
positive nodes, but multiplying entries back by x+y does not generally
preserve positive matrices. Do not repeat that normalization as a solution.

Fast checks for a concrete proposed map, before deepening:

1. Write the complete matrix/energy identity, not only its diagonal.
2. Test its null profiles and boundary traces. A source-limit mismatch
   rejects an exact identity immediately, as P5 does for this named map.
3. Verify that the bound controls a subtracted quantity FROM ABOVE or a
   remaining quantity FROM BELOW, retaining the mixed term and mean part.
4. Check whether the same premise holds for a known negative control;
   if it does, identify the additional source relation actually being used.

Outcome: the actual conditional primitive has the proved P2 bound, but
this bound by itself does not pay the full-V transfer. No new full-V
positive budget or negative true-source witness is supplied. No new route
family, Proshka dispatch, goal or counter reset is selected by this report.
The exact remaining design question is to couple the mean sector in P4
to a source-derived positive energy; whether this is possible is OPEN.

## Source pins

- REPORT_2026-09-13_BROWNIAN_DILATION_CONDITIONAL.md:
  `8ea7ed0b70f57d271b09cb44f53156cd50b71aa6511bd1fd4077111ba5bef5ef`.
- REPORT_2026-09-13_RESIDUAL_COMPENSATION_HUNT.md:
  `7aaf8e43faa5bfd37954d6076db3acb1801325777bd9d989b25d75c9a9466c14`.
- REPORT_2026-09-15_HANKEL_JORDAN_PREFLIGHT.md:
  `c39016a5ba57aaa9e60f56682d11a9eebde9ee3202e4b2294c4e5beb156bc2c3`.
- [S1, Habermann §2.1](https://www.cambridge.org/core/journals/combinatorics-probability-and-computing/article/brownian-bridge-expansions-for-levy-area-approximations-and-particular-values-of-the-riemann-zeta-function/6C1D65580D064B415E14AF19DAE55517):
  classical sine basis and reciprocal eigenvalues. P1-P5 are direct
  calculations here, not claims attributed to that article.
