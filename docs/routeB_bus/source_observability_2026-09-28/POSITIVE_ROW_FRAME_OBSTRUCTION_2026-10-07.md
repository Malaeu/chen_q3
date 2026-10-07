# Positive-row sampling: direction and actual-source negative control

Root PAPER attempt, 2026-10-07; no RH/SP claim. This tests whether generic exponential-frame theorems can supply the Q7 mixed-Gram sign. Sources: Q7 equations13–20, exact G transform, formula and fixed derivative decay in `PROSHKA_NEGATIVE_GROWTH_PHASE_2026-10-06.md:19`, `DIRECT_THETA_LOCALIZATION_AUDIT_2026-10-06.md`, and the counted retained family in `HIGH_ZERO_TAIL_AUDIT_2026-10-06.md`.

## Correct direction, retaining rank deficiency

C=L0*, Gc=C*C, S=range(Gc), V=C(Gc^dagger)^(1/2), Z=Pcal V, Ebar=V*E0 V. For x=Gc^(1/2)z, v=Cz=Vx, V*V=I_S,

q0+r||v||² = x*(Z*Z+Ebar+rI_S-Gc|_S)x.

Hence the diagonal necessary test is the LOWER inequality Z*Z+Ebar+rI_S>=Gc|_S. On the Gc spectral space U_tau of eigenvalues >=tau it requires
lambda_min((Z|U_tau)*(Z|U_tau)+Ebar_U_tau)>=tau-r.
In particular sigma_min(Z|U_tau)^2+lambda_max(Ebar_U_tau)>=tau-r is necessary. This is not sufficient for Schur: the nonnegative b*(T+gI)^-1b must still be subtracted.

Shrinking Omega=Pcal C with C,E0 fixed decreases the diagonal energy; it cannot supply this sign. This comparison is algebraic, not a permissible variation of actual source rows. The generic cross-Gram contraction uses ROW Gram A=Pcal Pcal*, not Pcal*Pcal:
Z0=A^(dagger/2) Omega Gc^(dagger/2),
Z0*Z0=V* Pcal* A^dagger Pcal V<=I_S.
It is an upper bound with no lower observability content. These formulas were independently checked by answer10_pair_audit; root corrected the intermediate row/column Gram dimension label. They reorganize the known sign, not prove it.

## Actual carrier-wide obstruction

Let Pcal contain all retained positive critical and pair-sum rows, height T_z=m L², L=log m, with original multiplicities. For every fixed A>0 there are unit f_m in the original full complex V_m, for every sufficiently large original m, such that

||Pcal f_m||² <= C_A m^(-A).

Consequently no carrier-wide lower frame bound c m^(-B)I<=Pcal*Pcal, c>0 and fixed B, can hold eventually. This does NOT rule out a bound restricted to E=range C.

Proof. The exact nonzero source G has bilateral transform M_G(w)=-4xi(1/2+w); it vanishes at every actual retained zero parameter. G is smooth with all fixed-order L2 derivatives finite, and |G(t)|<=D exp[-(pi/2)exp(2|t|)]. Choose fixed smooth chi, equal to1 on [-1/4,1/4], supported in (-1/2,1/2), and put F_m(t)=chi(t/L)G(t). For L>=1, ||F_m^(s)||2<=C_s by Leibniz, independently of m. Its periodic extension is smooth because it vanishes near the endpoints.

Let p_m be its orthogonal Fourier projection onto modes |j|<=m on I=[-L/2,L/2], with the original phase convention. Periodic Parseval gives
||F_m-p_m||2 <= (L/[2pi(m+1)])^s ||F_m^(s)||2 <= C_s(L/m)^s.
The weighted physical cutoff error satisfies
integral exp(|t|/2)|F_m(t)-G(t)|dt <= C exp(-c sqrt(m)).
For every actual zero w, |Re w|<1/2, the full G transform is zero and therefore
|integral_I p_m(t) exp(wt)dt|
 <= m^(1/4)sqrt(L) C_s(L/m)^s + C exp(-c sqrt(m)) =: a_m,s.
This is uniform in the ordinate, since exp(i Im(w)t) has modulus1. Conjugation conventions do not change the bound.

A critical row contributes r_w times this squared bound. A normalized pair sum sqrt(r_w/2)(a_w+a_wdag) contributes at most 2r_w times it. Summing the original retained multiplicities costs O(T_z log T_z)=O(m L³). Thus
||Pcal p_m||² <= C_s m^(3/2-2s) L^(2s+4) + C m L³ exp(-2c sqrt(m)).
Also ||p_m||2 -> ||G||2>0. Normalize p_m. Given A choose an integer s with 2s>A+3/2, and absorb the fixed logarithmic power into the strict power margin. This proves the assertion on every late original cell.

The identical estimate applies to negative pair-difference rows C*: replacing a sum by a difference does not increase the triangle bound. Hence ||C* f_m||²=O_A(m^(-A)) for every A. If Q_tau=1_[tau,infinity)(CC*) is its carrier spectral projector, then

tau ||Q_tau f_m||² <= <f_m,CC* f_m> = ||C* f_m||².

For every fixed B and tau>=m^(-B), these near-null witnesses have superpolynomially small projection into the high negative-Gram space. This is one family of source-null directions, not a uniform theorem over their growing span, and supplies no positive sampling bound there.

No zeros off the critical line were assumed to exist. No equality between E and the full carrier was used. In fact the same transform-null source also makes the negative-row measurements small; this witness is not an exceptional Schur vector.

## Independent bounded check

growth_symbol_attempt checked the cutoff, periodic Parseval, original row normalizations, multiplicity sum, all-positive and negative-row conclusions, and spectral-threshold limitation. PASS. The same normalized sequence works for every fixed A, since s is only the proof order, not part of its definition. A more explicit physical tail bound is (2D0/pi)m^(-3/8)exp[-pi sqrt(m)/2]; the coarser bound used above suffices. This is a PAPER result; no Lean or floating test was used.

## Decision

Uniform polynomial positive-row sampling on the whole carrier is the wrong stronger theorem. Qualitative completeness in a different space cannot repair it. Retain only the direction-correct, weighted estimate on actual E, together with its regular-resolvent subtraction. No replacement mechanism or Q8 is selected by this calculation. The next search must distinguish near-null theta directions from E with a proved quantitative map, or provide direct signed compensation; it may not assume that separation.
