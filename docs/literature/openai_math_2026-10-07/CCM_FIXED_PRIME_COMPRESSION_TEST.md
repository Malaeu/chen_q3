# Fixed prime shift: a Gram defect survives the sparse Fourier band

2026-10-09. Root own test after Q10; independent read-only sparse_band_receiver audit PASS for F1-F4, constants, original constraints and endpoint projector; no defect found. This tests the cost of a proposed prime-factor/positive-square transfer, not the sign of the actual long-divisor source. Production N=m and L=log m remain fixed throughout each cell.

## Exact question

Combining divisors e and qe is an exact scalar operation. To convert it into an operator square one may want to treat shifts after Fourier compression as if their Gram products were unchanged. Test precisely E V_s^*V_s E=(E V_s^*E)(E V_s E), where s=log q for one fixed prime q and E is the ACTUAL three-constraint sparse-band projection. This is not the same as deleting an intermediate projection in a forward-only path, and failure of this identity does not refute the true signed pairing.

Use H=L2(0,L), (V_s f)(t)=1_(s<=t<=L) f(t-s), and F e_j=L^(-1/2)exp(2pi i jt/L), |j|<=M=floor(m^alpha), fixed0<alpha<1. Let P project onto the original constraints b,v_plus,v_minus in this band, E=F P F*, E_M=F F*. Then E<=E_M. The accepted sparse-band Gram matrix is >=I3/2 eventually, with ||v_plus||²>=m/2, ||v_minus||²>=1/2. See CCM_SPARSE_BAND_RECEIVER.md(4); no new zero or arithmetic hypothesis enters.

## F1. Original constrained edge direction

Let c=Pe_M/||Pe_M||, where e_M denotes the coefficient vector of the TOP retained Fourier mode (not zero mode). From the literal exponential coordinates and Omega=2pi M/L,

    |(vhat_plus)_M|², |(vhat_minus)_M|² <=L/(2pi²M²).

Consequently a=||(I-P)e_M||²<=2[(2M+1)^(-1)+L/(pi²M²)]<=1/M+L/M². For M>=L and a<1, normalization gives

    ||c-e_M||²=2(1-sqrt(1-a))<=2a<=4/M.               (F1)

The vector Fc satisfies all original constraints exactly. Only the comparison mode F e_M lacks them.

## F2. Actual loss into modes above the retained band

Set f0=F e_M. For each integer l>=1, direct integration over [s,L] gives the coefficient in the existing full L2 Fourier basis

    |<F e_(M+l), V_s f0>|=|sin(pi l s/L)|/(pi l).

Here F e_(M+l) denotes the same normalized Fourier function outside the test band; no enlarged production matrix is substituted. For 1<=l<=floor(L/(2s)), sin(pi l s/L)>=2l s/L. If L>=4s the number of these terms is at least L/(4s). Bessel's inequality therefore yields

    ||(I-E_M)V_s f0||² >= s/(pi² L).                 (F2)

No whole-line approximation, changed window, endpoint identification, or prime-distribution result is used. The original cutoff V_s is retained.

Since V_s is a contraction, F1-F2 imply, for M>=16pi² L/s in addition to the preceding conditions,

    ||(I-E)V_s Fc|| >= ||(I-E_M)V_s Fc||
       >= sqrt(s)/(pi sqrt(L))-2/sqrt(M)
       >= sqrt(s)/(2pi sqrt(L)).                    (F3)

For fixed q and alpha these conditions hold on every sufficiently late original cell; all parameters are fixed before m grows.

## F3. Exact Gram return and its lower bound

Define the positive compression defect

    D_s=E V_s^* (I-E) V_s E
       =E V_s^*V_s E-(E V_s^*E)(E V_s E) >=0.

Physical support is explicit: V_s^*V_s is multiplication by 1_[0,L-s], not the identity. From the actual unit vector Fc and F3,

    ||D_s|| >= <Fc,D_s Fc> >= (log q)/(4pi² log m).   (F4)

Thus no uniform O(m^(-delta)) operator-norm bound for this Gram defect holds for any fixed delta>0, even on M=floor(m^alpha) with arbitrarily small FIXED alpha>0. Exact Gram multiplicativity is false on the original projected space. The square root leakage is at least order1/sqrt(log m).

## Shelf comparison

Bounded alias follow-up checked the existing Q10 prime-factor identities and continuous translation compression. Three semantic queries returned ASK_STATUS: INCOMPLETE due to index freshness, not absence. Q10(3)-(5) retains the exact cutoff boundary but supplies no positive-square estimate; its accepted Q10-E only gives the conditional fixed 3/8 envelope. The present test quantifies one Gram defect, not Q10's separate forward-product defect. No new external theorem has been admitted.

## Scope and decision

This is an actual fixed-prime sparse-band geometric control. It is not a negative eigenvalue of C_comp, T_gtR or K_m, and does not show that the source-weighted sum of these defects is large: signed coefficients, cross terms and complementary positive credits could still compensate. It does not rule out a useful one-sided bound using D_s>=0 in the correct direction. No conclusion is drawn for forward-only V_s V_t products from this Gram identity.

A prime-factor square calculation must retain D_s and the physical endpoint projector, or prove a signed weighted return. Finite codimension of P and narrow relative bandwidth M/m do not alone make D_s polynomially small. Next source calculation must spend its positivity with the actual sign instead of replacing the compressed product by an exact shift product. Full-SP/RH remain OPEN; no new Pro question has been sent.

AUTOPSY: dropped=THEOREM_SHAPE; note=actual fixed-prime Gram multiplicativity has a positive defect at least log(q)/(4pi²log m) even on each fixed sparse band; signed source-weighted return remains open.


## Q-block continuation: exact precompression return (independent PASS)

Read-only long_positive_alias verified Q1-Q3, endpoints and actual-weight trace.
Reviewer report initially omitted B_1=1 for q>R; root corrected that report,
reviewer confirmed the correction. Q1 itself retained the term throughout.

Fix q and R with 2<=R<m. For each q-free integer r<=m set

    ell_R(r)=sum_(e|r,e>R) mu(e)log(r/e),
    A_r=sum_(e|r,e>R)mu(e),
    B_r=sum_(e|r,R/q<e<=R)mu(e),
    C_r=sum_(e|r,R/q<e<=R)mu(e)log(r/e).

All endpoint inequalities are literal. On H define X=q^(-1/2)V_(log q),
S=X(I-X)^(-1), J=X²(I-X)^(-2). The inverse is a FINITE polynomial:
V_(a log q)=0 almost everywhere once a log q>=L. Consequently
S=sum_(a>=1)X^a and J=sum_(a>=1)(a-1)X^a, with only finitely many
nonzero terms. All operations in this paragraph precede E.

Put

    Z=sum_(r<=m,q does not divide r) r^(-1/2) V_(log r)
       [ell_R(r)I+(log(q)A_r-C_r)S-log(q)B_r J].       (Q1)

Then the actual compressed long-divisor matrix, identified on ran E, is

    T_gtR=E(Z+Z*)E.                                  (Q2)

Proof: unique n=q^a r, forward semigroup V_t V_u=V_(t+u), and paired
coefficient ell_R(q^a r)=log(q)A_r-C_r-(a-1)log(q)B_r for a>=1.
Terms q^a r>m vanish by physical support; q^a r=m also has Q(L)=0,
matching the original endpoint. The a=0 term stays ell_R(r), not A_r. For r=1, B_1=1 when q>R
and B_1=0 when q<=R; the former retains the pure-q block -log(q)J.
Thus no tail, intermediate projection or weight substitution was dropped.
For an actual coefficient weight W=PWP>=0 the physical weight is FWF*,
and the original trace is exactly 2 Re Tr(FWF* Z).

For comparison only, the contraction identity

    I+S+S*=(I-X*)^(-1)(I-X*X)(I-X)^(-1)>=0             (Q3)

follows by multiplying on the left by I-X* and right by I-X.
Here X*X=q^(-1)1_[0,L-log q] keeps the physical endpoint. Q3 bounds
S+S* from BELOW by -I. It does not directly bound Q2 from above:
the r-dependent coefficient log(q)A_r-C_r has varying sign, the factor
V_(log r) remains, and the J term has its own signed coefficient.
For example q=2,R=3 gives this S coefficient -log(2) at r=5
and +log(3) at r=9 (for m>18 both first-shift terms lie inside the window).
These are coefficient checks, not signs of the corresponding operators.
No sign of these full weighted sums has been established. The Gram defect
D_s from F4 is absent in Q1-Q2 because no square or intermediate E was
introduced; its positivity alone therefore supplies no termwise credit
in this exact source representation.

This completes the proposed one-prime regrouping as an identity only.
The missing estimate is the upper bound on 2 Re Tr(FWF* Z) with the original
weight and all r terms retained. Q1-Q3 are not a new arithmetic estimate,
not a smaller exponent, and not evidence that every q-block approach fails.

AUTOPSY: dropped=THEOREM_SHAPE; note=precompression q-resolvent is exact but positive-real contraction identity does not supply the signed shifted source upper estimate; regrouping-only shortcut stalled, arithmetic target open.
