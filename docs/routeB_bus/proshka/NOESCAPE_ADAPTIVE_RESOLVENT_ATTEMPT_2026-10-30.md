# Adaptive resolvent variation: complete kernel versus one-direction tests

Continuation after BOUNDARY; literal CCM, normalization, even carrier and T
unchanged. This is an own attempt and negative control, not a proof of T/RH.
Network and resolvent variations are candidates, not the only path to NOESCAPE.
Other competitors and quantitative moment estimates remain open. Each proposed
competitor must retain normalization, admissibility and the exact use of
minimality; the missing step is a negative sign from escape and actual CCM
coefficients. Generic test limitations do not exclude those other routes.

Prior turn made progress: completed BOUNDARY review and finite direct X budget,
committed and remotely verified bd1adc535574727c5f8381e3b9dc3a0f48f42e6b.

## Exact source rewrite

Use the same-parity displacement identity of NOESCAPE_RESISTANCE_SOURCE_ATTEMPT:
X=diag(i²), v_i=d_i, u_i=d_i F_i, [X,A]=uvᵀ−vuᵀ.
For a real exact unit eigenvector c, Ac=lambda c, set R_z=(X−zI)^−1,
U(z)=uᵀR_z c and V(z)=vᵀR_z c. Real z avoids all nodes i².
The matrix A remains the full source including pole, arch and all prime powers.
The diagonal disappears only through the exact eigenrelation.

Since [A,R_t]=R_t[X,A]R_t and
R_s R_t=(R_s−R_t)/(s−t), the exact bilinear energy is

    K(s,t)=cᵀR_s(A−lambda I)R_t c
          =[U(s)V(t)−V(s)U(t)]/(s−t),
    K(s,s)=V(s)U'(s)−U(s)V'(s).

Where V is nonzero, H=U/V gives K(s,s)=V(s)² H'(s).
A finite real combination y=sum_j alpha_j R_zj c stays in the SAME even
carrier. If alphaᵀK alpha<0, then g=y/||y|| is a strict competitor, with
energy difference alphaᵀK alpha/||y||². Negativity ensures y is nonzero.
This allows combinations; positivity of every diagonal is insufficient.

For an arbitrary unit trial rho=cᵀAc and r=(A−rho)c, add
cᵀR_s R_t r to the displayed divided difference. For amplitude
 a_i=sum_j alpha_j/(i²−z_j), the total correction is sum_i a_i² c_i r_i,
whose absolute value is at most ||a||_infinity² ||r||. Poles near nodes
can amplify this bound; superpolynomial small residual gives no strict sign.

## Completeness identifies the circular shortcut

If all c_i are nonzero, m+1 distinct external real shifts give an invertible
Cauchy matrix of vectors R_zj c. Thus full K is congruent to A−lambda I.
Finding its negative eigenvalue is exactly the original instability problem;
its positivity merely restates bottomness. No independent escape estimate
has appeared. For arbitrary amplitudes the same point is immediate from
L=diag(c)(A−lambda I)diag(c), the signed graph Laplacian.

If c has zeros, let S=supp(c), Z=S-complement and write
A−lambda I=[[C,E],[Eᵀ,F]] in these coordinate blocks. Multipliers and resolvents
span exactly S, so even their complete kernel cannot see E or F.
If C has a negative direction it is already a witness. Otherwise C>=0:
if Eᵀ ker C is nonzero, choose u in ker C and z with uᵀEz!=0;
(tu,z) has energy 2t uᵀEz+zᵀFz<0 for a suitable t.
If Eᵀker C=0, completing the square gives the remaining exact condition
F−EᵀC†E>=0. A negative direction z there yields x=−C†Ez.
Stationarity supplies only Cc_S=0 and Eᵀc_S=0, not these PSD conditions.
Any negative witness can be projected onto c-perp without changing its
quadratic form, because (A−lambda I)c=0.

## Exact control: every single real resolvent misses a descent

This control is SYNTHETIC, not a literal CCM matrix or an escaping family.
Take four nodes x=(0,1,4,9), d=(1,sqrt(2),sqrt(2),sqrt(2)),
P(z)=product_i(z−x_i), H(z)=z+z/(z²+1),

    c_i=−(x_i²+1)/(d_i P'(x_i)), F_i=H(x_i),
    A_ij=d_i d_j (F_i−F_j)/(x_i−x_j)  (i!=j),
    A_ii=−sum_(j!=i) A_ij c_j/c_i.

All c_i are nonzero, Ac=0, and the same rank-two displacement holds.
Partial fractions give V=(z²+1)/P, U=z(z²+2)/P, so U/V=H.
For every real nonnode z,

    H'(z)−7/8=(z²−3)²/[8(z²+1)²]>=0.

Every single resolvent direction therefore has strictly positive energy.
Nevertheless, the two vectors R_-2 c/V(-2), R_2 c/V(2) have energy Gram

    [[22/25,6/5],[6/5,22/25]], eigenvalues 52/25 and −8/25.

Their difference has energy −16/25, squared norm 349201/33750 and normalized
Rayleigh quotient −21600/349201<0. Scaling c to unit norm preserves the result.
This exactly disproves completeness of single-resolvent positivity even for
stationary vectors with the pinned displacement structure. It does not
exclude a source-specific implication using additional CCM information.
The exact SymPy replay is ../thetagrade_2026-10-28/noescape_rational_control.py.

A preliminary 80-dps literal m=4,8,16 scan also missed every first-excited
descent using 12 external shifts and all adjacent-node midpoints; those finite
floating observations are exploratory only and not used in the exact control.

## Remaining input and stopping condition

A genuinely new source property must select shifts/amplitudes using escape
and prove a strictly negative FULL Gram quadratic, with trial residual and
normalization costs if applicable. Computing the complete congruent matrix or
assuming an indefinite Gram is not that property. Nor does scalar monotonicity
establish matrix positivity. Zero-coordinate Schur terms cannot be discarded.
Return to the local shelf for the full divided-difference interaction before
selecting another mechanism. Do not infer high frequencies or mandatory nodes
from vanishing jet integrals. No new Proshka question has been sent.

Independent review: adaptive_amplitude_audit verified the resolvent signs,
trial correction, Cauchy-span limitations, and singular Schur alternatives.
Independent follow-up also verified the exact synthetic control, residues,
strict single-shift signs and negative two-shift Gram. Root SymPy assertions
all passed. This bounded PAPER result changes only the completeness claim
for the generic test; no CCM sign or NOESCAPE status changes.

## Shelf return: existing real-zero bridge, not a new escape theorem

The three searched dictionaries were divided-difference/Loewner kernels,
rational interpolation/real-rooted Lagrange numerators, and cyclic resolvent
observability/indefinite kernels. All ask.sh searches returned INCOMPLETE
(q3_docs freshness/local shelf failures), so no global absence is asserted.
Manual source reads found the existing G2 route. The generic theorem's comment
is: “Under the explicit nonnegativity premise on the exact source form, the
complexified source Lagrange polynomial has only real zeros.”
Locator: RankOneCorrectionLagrangeRealZeros.lean:39–63, below.

Its inputs include symmetry, full shifted-form PSD, commutator, TDxi,
normalization and a one-dimensional kernel. The polynomial in
RankOneCorrectionLagrangePolynomial.lean:12–22 clears the denominators of
sum_i xi_i/(lam_i−z). Our v-weighted numerator maps xi_i to d_i c_i,
but the generic theorem's other identities and the signed-mode/even-squared
CCM crosswalk still need verification; no direct import is claimed.
CCMFiniteWeilBottomSpectral.lean:40–75 obtains PSD from the full bottom
Rayleigh bound and separately requires simplicity. The synthetic nonbottom
control fails the PSD premise. Flat escaping trials are not exact bottoms.
Consequently this is an existing conditional bridge, not an independent
source estimate or new proof of NOESCAPE. No Lean build was needed or run.
Read-only alias researcher rational_kernel_alias located this match; root
read the actual definitions and theorem assumptions before recording it.

Source files (relative to repository) and SHA256:

- `q3.lean.aristotle/Q3/Proofs/RouteB/RankOneCorrectionLagrangePolynomial.lean`: `208c2aee2590e0bc013fe388933ec588fc16eff21c09d8c02b9662e58d8f4f93`.

- `q3.lean.aristotle/Q3/Proofs/RouteB/RankOneCorrectionLagrangeRealZeros.lean`: `0ba83859f37dd9285088892decb01ed75afe4d4a781784eda46579bddce5ce6e`.

- `q3.lean.aristotle/Q3/Proofs/RouteB/CCMFiniteWeilBottomSpectral.lean`: `4468d0a6e7c5b00cb5b2e51902cf58eb944a4a466ba93097aaa8aea1ddb84d3b`.

## Actual diagonal coupling: next source-specific target

The synthetic control freely completes its diagonal to enforce stationarity.
The literal matrix does not have that freedom. For real t define beta(t) by
the full source sine formula (CONFINE 6.2), with unchanged cutoff m, and set
F(x)=sqrt(x) beta(sqrt(x)), extended analytically at x=0. Let Loewner(F)
have divided differences off diagonal and F'(i²) on diagonal. With
D=diag(1,sqrt(2),...,sqrt(2)), direct differentiation of the full source gives

    A = D Loewner(F) D + diag(delta_i),
    delta_i = K_m(i,i)−beta'(i)
      = −C_L − integral_0^L [2j(s)cos(2pi i s/L)−1/sinh(s)] ds
        −2 sum_(2<=n<=m) Lambda(n)/sqrt(n) cos(2pi i log(n)/L),
    C_L=gamma+log(4pi tanh(L/2)).

For i>0, A_ii=K_m(i,i)+beta(i)/i and
2F'(i²)=beta'(i)+beta(i)/i; at zero F'(0)=beta'(0).
The pole derivative cancels in delta but remains in F and therefore in A.
The integral integrand tends to 1/2 at zero. All prime powers remain, and
here the endpoint n=m cosine term generally DOES NOT vanish. The identity
must not inherit the sine-moment endpoint omission.

This retains an actual source relation that the synthetic control does not
satisfy by construction. It supplies no sign: neither the Loewner part nor
delta is declared PSD. Source definitions checked directly: CCMFiniteWeilSourceMatrixN1.lean:40–101.
The next bounded question is whether this correlated
source diagonal and off-diagonal structure constrains the adaptive negative
Gram under escape, beyond generic rank-two algebra. Any proposed estimate
must return the full sum, not prove a stronger standalone sign by assumption.
Root 80-dps checks at m=4,8,16 and i=0,1,m agree to <2e−80; diagnostic only.
Independent adaptive_amplitude_audit source-factor review PASS: full K versus
even A factors, i=0 limit, pole cancellation and all prime terms verified.
This is an identity, not a signed estimate.

## Concrete two-direction test on the literal carrier

For two admissible real directions y_1,y_2, set G_ab=y_aᵀ(A−lambda I)y_b.
If G_11>0 and det G<0, y=G_12 y_1−G_11 y_2 has
yᵀ(A−lambda I)y=G_11 det G<0; normalize g=y/||y||.
For exact bottoms PSD forbids this; the unresolved source task is to force
this sign (or another competitor) from escape, without presuming it.
This candidate is sufficient, not mandatory for NOESCAPE.

Finite 80-dps diagnostic noescape_two_resolvent_probe.{py,json} uses the full
literal A and normalized R_z c directions, scanning all pairs among twelve
external shifts and the m adjacent-node midpoints. At m=4, first excited c,
z=(-0.016,0.5) gives det G≈−1.07669776e−6 and normalized energy shift
≈−2.45538144e−5 (actual spectral gap≈2.62511726e−5). The tested m=8,16 pairs
find no negative shift even on first excited states; all tested bottom pairs
are nonnegative. These are floating diagnostics, not interval certificates,
not control of all real pairs, and not statements about escaping bottoms.
They illustrate why testing larger families can matter, while proving no
eventual sign. No finite outcome substitutes for the required escape estimate.
