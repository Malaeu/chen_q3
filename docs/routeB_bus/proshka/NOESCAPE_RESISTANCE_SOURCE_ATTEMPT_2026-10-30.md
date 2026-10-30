# Resistance source attempt: endpoint envelope and literal-cell control

Continuation of SIGNED_CUT_ALIAS_RETURN_2026-10-30.md; original even CCM
matrix and carrier unchanged. This is an attempt to obtain the unpaid sign,
not a new definition of NOESCAPE. RH and T remain OPEN.

## A cheap positive-network bound collapses to a principal minor

For a real unit eigenvector c at lambda define w_ij=-A_ij c_i c_j,
D_i=sum_{j!=i}(w_ij)_+, N_i=sum_{j!=i}(-w_ij)_+, and
d_i=D_i-N_i=(A_ii-lambda)c_i². The last equality uses the exact eigenrelation.
Every off-diagonal entry is the full pole/archimedean/prime-power entry of
VARIATIONAL (6.1)-(6.2); the diagonal is eliminated exactly, not omitted.

Select a negative edge pq of magnitude alpha>0. Set a_p=1, a_q=0,
and all other a_i=t. There is no positive pq edge. The positive energy is

    D_p(1-t)²+D_q t².

For D_p+D_q>0 its minimum is E0=D_p D_q/(D_p+D_q), attained at
t=D_p/(D_p+D_q). All remaining negative energies are nonpositive. Thus
alpha>E0 would construct the same-carrier competitor in the preceding note.
This only needs degrees, avoiding an inverse of the positive network.

However, exact bottomness already implies the rescaled principal minor

    [[d_p, alpha], [alpha, d_q]] >= 0.

Because N_p,N_q>=alpha, its determinant gives

    alpha² <= d_p d_q <= (D_p-alpha)(D_q-alpha),
    hence alpha <= D_p D_q/(D_p+D_q).

Both factors are nonnegative: d_i>=0 and D_i>=N_i>=alpha. If a degree
vanishes, the corresponding d_i is negative, already impossible for a bottom.
Thus this cheap envelope, after discarding the other negative contributions,
cannot be stronger than the existing two-coordinate minimality test.
Its failure is not a new obstruction to RH: escape could still be used to
contradict a principal minor, but we have no source estimate doing that.

For connected endpoints the actual Dirichlet minimum 1/R is at most E0,
possibly strictly smaller. This calculation does not kill full resistance.
For endpoints in distinct positive components a component indicator has
zero positive energy; its contradiction uses full component stability,
not necessarily the same two-coordinate principal minor.

For arbitrary unit trials the correction remains sum_i a_i²c_i r_i,
bounded by ||r|| for these voltages. This applies to the explicit escaping
radical trials, but gives no signed margin from their residual bound alone.

Independent read-only exact_minimality_commutator review accepted the
endpoint calculation, factor signs, degeneracies and the distinction from
full resistance. No fixed-jet information entered this attempt, so it
cannot be presented as a source-specific escape contradiction.

## Next discrimination

Probe the full literal even matrices on bottom and first excited states.
The excited state has a known lower competitor, so failure of every single
edge test there exposes a limitation of this restricted mechanism on the
actual source. Finite numerical output is diagnostic only: it cannot kill
a cofinal implication under escape or prove T. Keep the residual and
precision beside every sign and retain every source matrix term.

## Same-parity displacement test: four sums, still an unpaid sign

The literal entries also give a structured amplitude choice without a
network inverse. Put x_i=i², F_i=i beta_i, X=diag(x_i), v_i=d_i and
u_i=d_i F_i. Then exactly

    [X,A]=u v^T-v u^T.

This is a consequence of VARIATIONAL (6.2), not discovery of a new
displacement law: CONFINE §6.2 already supplies the full linear-mode
rank-two commutator. X here acts inside the even block, unlike the first
derivative's even-to-odd map in CONFINE §6.4. No global positive commutator
is claimed (CONFINE §6.5 explicitly excludes that shortcut).

For an exact eigenvector define S0=v^T c, S_F=u^T c,
S_x=v^T Xc, S_Fx=u^T Xc. Directly,

    (A-lambda)Xc=v S_F-u S0,
    <Xc,(A-lambda)Xc>=S_x S_F-S0 S_Fx=:Delta.

If Delta<0, g with coefficients Xc/||Xc|| is an exact admissible competitor,
with energy difference Delta/||Xc||². A negative Delta itself ensures Xc!=0.
For a bottom, Delta>=0; furthermore Delta=0 implies (A-lambda)Xc=0 by PSD,
so v S_F-u S0=0. This last equality need not follow from stationarity alone.

For an arbitrary trial rho=c^T Ac and r=(A-rho)c,

    <Xc,(A-rho)Xc>=Delta+sum_i i^4 c_i r_i.

Its residual cost is <=m^4||r||, not <=||r||. Equivalently use the bounded
multiplier X/m² and compare Delta/m^4 with ||r||; normalization yields the
same competitor. The explicit escaping radical trials still have a
superpolynomial residual after this factor, but no lower bound on -Delta
has been established. They supply no strict sign by themselves.

S0=sqrt(L) f(-L/2) and S_x=-L² sqrt(L)/(4 pi²) f''(-L/2), with the latter
the interior trigonometric derivative. These are growing-window endpoint
data, not fixed theta-jet overlaps. Weak escape alone does not control them.
The beta sums keep every pole, archimedean and supported prime-power term.
Independent exact_minimality_commutator review checked the identity,
normalization, equality case and m^4 residual factor. The exact missing
input is a source-derived negative determinant (or another signed voltage
energy) under escape; this packaging by itself does not pay that input.

### Full source boundary balance for that determinant

Let b=L/2 and let f^(k) denote the derivative of the interior trigonometric
polynomial, not the derivative of its zero extension. Define

    P1=κ sum_i d_i i² c_i/(L²+16π²i²),
    P3=κ sum_i d_i i⁴ c_i/(L²+16π²i²),
    B_k=integral_0^L j(s) f^(k)(s-b) ds
        +sum_{2<=n<=m} Λ(n)/sqrt(n) f^(k)(log(n)-b),  k=1,3.

The exact sine sums give S_F=P1-L sqrt(L) B1/(2π²) and
S_Fx=P3+L³ sqrt(L) B3/(8π⁴). Consequently

    Delta=S_x P1-S0 P3
          +L^4/(8π^4) [ f''(-b) B1-f(-b) B3 ].

The two P terms are the full pole contribution in this even-sector identity.
No prime powers are removed: the n=m term is zero because the interior odd
derivatives vanish at b. At s=0 these derivatives are O(s), so the j(s)
singularity is integrable. Independent review checked every factor and sign.
This identifies a boundary/shift-correlation balance to estimate, but
weak fixed-jet escape controls none of its terms in the needed direction.

## Literal finite diagnostic outcome

The reproducible script ../thetagrade_2026-10-28/noescape_resistance_probe.py
and adjacent JSON use the full matrix_K and orthonormal parity compression,
70-decimal mpmath eigenpairs and grounded positive-network solves.

| m | max alpha R, bottom | max alpha R, first excited |
|---|---:|---:|
| 4 | 0.9958317138 | 0.8163395020 |
| 8 | 0.9914957547 | 0.9618687602 |
| 16 | 0.9725398170 | 0.8081849381 |

All positive graphs were connected. No tested state triggered a one-edge
overload. At m=16 the first excited state has a lower bottom by about
4.7334130203e-32, yet every one-edge score is below 0.809. Its i²-multiplier
energy numerator is positive, about 2.9774013190e-23 (bottom:5.1722181138e-29).
Thus the source diagnostics discriminate a genuine lower competitor from
these two restricted tests; mere non-bottomness does not make either fire.
Eigenpair residuals were below 3e-71, but matrix quadrature is not certified.
These are finite diagnostics, not a proof that these tests fail cofinally,
and the first excited sequence is not asserted to satisfy complete jet escape.

Outcome: the cheap endpoint envelope gives no independent escape input;
full one-edge resistance and the derivative determinant remain sufficient
tests with unpaid signs. A broader all-multiplier PSD reformulation would
merely restate minimum stability. The next Proshka question must demand an
actual source comparison using escape, or a rigorous obstruction to the
restricted comparison, rather than rename the same shifted-matrix positivity.
