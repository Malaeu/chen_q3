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
