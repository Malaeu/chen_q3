# Fokas after the full CCM matrix: sign-certificate audit

Date: 2026-09-25. Base: ee99aacc. PAPER + explicitly labelled numerical diagnostics.
Consumer: first scalar sign of the unchanged selected Ferrers family, then the separate Schur/complement and ground-tracking requirements. No RH claim.

## Decision and exact source

The scalar Fokas remainder is not the spectral residual. The existing candidate Green identity retains the full matrix and both boundaries:
r = (rowScale/(theta0 theta4)) (K-aI) Gjoint.
Those local Lean candidates are untracked; they were inspected, not rebuilt or admitted here.
The committed FULL_SCALAR_SIGN_CHAIN verdict supplies an executable next mathematical test R1-R8. Use its entire quartic R3, not the sign of individual weights or a repeated representation identity.

The source recurrence J is distinct from K. Its energy E=Lambda+G equals the standard prolate chi; negative off-diagonal entries are the alternating-sign conjugation of the positive Legendre probe. The diagonal shift algebra is explicitly proved in D0Mode4PSWFLegendreRecurrenceCrosswalk.lean. No source family, Fourier cutoff m, Ferrers prefix N=6m-1, or splice5m is changed.

## New uniform refinement of the energy enclosure

For m>=2, N=6m-1, and p=0,2, keep EXACTLY the existing auxiliary J_m(t), 0<=t<=1/2. Let mu_k=1/(4k+1), G=(2pi m)^2. The existing R2 min-max argument gives Lambda_p(t)<20. The committed theorem mode4Jacobi_tail_separated_at_four_mul proves the needed separation for every q>=4m; mode4TailMap_mapsTo_and_contracts then preserves [0,1/2].

Normalize the source coefficients by sum mu_k |b_k|^2=1. Set r_(N+1)=t. The backwards equation is
r_q=L_q/(C_q-U_q r_(q+1)), with C_q-U_q r_(q+1)>=2G/3>0 and 0<r_q<=1/2.
Irreducibility implies b_N!=0; backwards propagation gives b_(q-1)=(C_q-U_q r_(q+1))*b_q/L_q!=0. This justifies ratios even at t=0.
There are exactly 2m steps q=4m,...,6m-1. Therefore
|b_N|<=2^(-2m)|b_(4m-1)|,
mu_N |b_N|^2 <= ((16m-3)/(24m-3))*4^(-2m).
Hellmann-Feynman gives lambda_p'(t)=u_N mu_N |b_N|^2<0. With |u_N|<=G/4 and interval length1/2:

    0 < |I_i(m)| <= (G/8)*((16m-3)/(24m-3))*4^(-2m), i=0,4.

This strengthens the previous G*4^(-m)/8 bound uniformly. It does not change the physical/source splice and does not prove a scalar sign. It is conditional on the same source spectral identification already used in R2, not a fresh admission of that identification. Independent read-only PAPER reviewer /root/sign_algebra_review checked indices, nonvanishing, finite spectral bound and both constants: no material findings. No Lean was run.

## Homogeneous scaling cross-check

See ALGEBRA.md and divided_difference_check.py. The recurrence difference is (e0-e4) times a polynomial divided difference. Consequently the full quartic contains (e0-e4)^4, in addition to kappa^4. Removing this scalar does not supply a sign or automatically improve relative conditioning. An independent reviewer checked the proof; 162 exact Fraction controls passed.

If X=||z||, Y=||Pi z|| and v is the unit companion of Pi z in the same rank-two plane, the same complete quartic equals X^2 Y^2 (Rayleigh(z)-Rayleigh(v)). The numerical evaluator checks both forms. K is Hermitian and theta=tr(Pi K Pi).

## Diagnostics and remaining proof obligation

The scripts use full K=W02-WR-Prime, all Fourier modes -m..m, actual two-energy intervals, and the Gaussian plane with the Q5 boundary 2G'(L/2)/sqrt(L). The removable WR endpoint is implemented with denominator derivative2; no use of the old probe's erroneous endpoint helper. High-precision calculations remain diagnostics: quadrature and eigenvalue outputs do not certify real-number enclosures.

The diagnostic results are:

| m | full central quartic p_c | D_minus with sharper Frobenius budget | D_minus with original analytic budget |
|---|---:|---:|---:|
|2| -26.1299554183 | 25.7749190177 | -28.1611616048 |
|4| -0.197731159056 | 0.197727473505 | 0.197311260964 |
|8| -2.94329407658e-7 | 2.94329407644e-7 | 2.94329406666e-7 |
|13| -7.12754759404e-11 | 7.12754759404e-11 | 7.12754759404e-11 |

m2 was repeated at70 and110 decimal digits; printed30-digit central/Frobenius results agree. A later equivalent moment-factorized K implementation reproduces those values. m13 reproduces the independently recorded selected-row Rayleigh value4.226091457621532e-16. Its companion Rayleigh is7.863214329022815e-14, so central tau is7.820953414446600e-14. These are diagnostics, not certified eigenvalue/ground statements.

For m13, the canonical full tail budget contribution is4.03032734199e-31 against |p_c|=7.12754759404e-11; energy-rectangle Taylor remainder is1.50183457141e-57. Thus at that tested cell neither R6 sensitivity nor tail budget is the bottleneck. This is a concrete positive check, not a family theorem.

### Budget distinction (material)

The initial numerical implementation chose g=||K||_F. The accepted B(m) instead fixes a larger explicit analytic Gamma_m. Replacing Gamma_m by g yields a NEW sharper B_g, not the same canonical TEST. Independent review of the original remainder proof confirms all its steps use only ||K||<=g, so the general statement is valid with the SAME source when Y>eta. The script now reports both budgets separately. A failed canonical test at m2 does not imply negative tau, and m2 need not belong to the final shifted cofinal schedule.

### Current first family-level gap

The finite tests do not establish the sign of the full central prime/archimedean quartic for all selected m. The energy enclosures, full-source identity and rigorous norm-budget implication do not themselves supply that signed center. This audit does not mark the family dead, nor prove an eventual complement floor or the following Schur step. No additional grid is proposed as a substitute for the missing family estimate.

## Strict finite reference-cell certificate

`arb_m2_certificate.py` uses python-flint0.8.0 at100 decimal digits. It verifies the rational energy brackets by LDL inertia counts, encloses the complete finite F and K with Arb arithmetic/certified analytic quadrature, and encloses the exact Gaussian plane with an explicit infinite-series tail bound. It then evaluates the entire quartic over the energy rectangle, avoiding a point-evaluation-to-interval leap.

- R3 on the whole rectangle: [-26.1300 +/-5.19e-5], strictly negative.
- Sharper full remainder margin: [25.77492 +/-8.05e-6], strictly positive.
- Original canonical-budget margin: [-28.1612 +/-5.29e-5]; this sufficient test fails in the reference cell.
- y_lower > eta_upper is explicitly certified (approximately2.39108 >0.00184321).

These statements certify finite algebra and its sharpened budget comparison. A source tau implication is conditional on the accepted source/tail identities being applicable at this cell. In particular m2 is not asserted to belong to the final selected tail; the earlier denominator proof has threshold M0>=64. No infinite-family, Schur-floor or ground-tracking result follows from this reference-cell certificate.

The universal budget statement used here is: for any g>=||K||, the same perturbation proof gives B_g=2g eta(2X+eta)+4gX^2 eta/Y, provided Y>eta. This is a new sharpened bound when g=||K||_F; it is not a claim that the previously fixed B was that small. The direct interval test evaluates P+R^2 B_g<0 over the entire rectangle, retaining both boundaries, the original projection plane and all finite prime terms.

The midpoint discrepancy between the first numerical script and Arb was checked: Arb uses the exact rational input rectangle midpoint, whereas the diagnostic used the midpoint of the numerical Robin endpoint eigenvalues. At IDENTICAL rational midpoint inputs, mpmath and Arb agree on -26.1299554182981073906327160445285. No containment check uses the numerical reference.

The m13 diagnostics were repeated at140/180 digits with all five decisive printed30-digit fields equal. No additional finite grid is treated as a substitute for the family estimate.
