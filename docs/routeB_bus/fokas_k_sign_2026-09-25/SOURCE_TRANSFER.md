# Transfer a reference ground certificate to the selected source

2026-09-26. Baseline 362e5d9e. PAPER conditional reduction, not a cofinal
ground-tracking certificate. Keep the literal full CCM matrix K_m throughout.

## The useful change

The positive complement certificate can be proved for a finite reference row.
To transfer ground tracking to the selected row, one does not have to transfer
that complement floor itself. Orthogonal projection onto the same ground
space is a contraction. Consequently the source-row error is not divided by
the tiny spectral gap.

Let zhat != 0 be a reference row, Z=||zhat||, qhat=zhat/Z, and let P0=uu*
be the orthogonal projection onto a simple ground state of this SAME K.
Suppose ||(I-P0)qhat|| <= alpha and a full row b satisfies

    ||b-zhat|| <= E < Z.

Set q=b/||b|| (an overall unit phase is harmless). Then

    ||(I-P0)q|| <= (Z alpha + E)/(Z-E).                 (T1)

Indeed, ||(I-P0)b|| <= Z alpha+E and ||b|| >= Z-E.
This is a direct triangle inequality, with no comparison of inverses or
perturbation of K. In particular K must NOT change between the two rows.

For the existing projected-ground transform normalized at the trial center,
the exact identity T(q,0)=sqrt(log m) q_0 and the finite Bessel bound give,
uniformly on any compact contained in |Im s|<=H,

    tracking_error <= |Xi(0)| m^(H/2)
                       (Z alpha+E)/(|zhat_0|-E),       (T2)

provided |zhat_0|>E. Normalizing b cancels exactly in this formula.
Alternatively use the selected-source center floor cCenter>0:

    log(m)|q_0|^2 >= cCenter,
    tracking_error <= |Xi(0)| m^(H/2) sqrt(log(m)/cCenter)
                       (Z alpha+E)/(Z-E).             (T3)

The source of this floor is the existing conditional theorem
`selectedFerrersFiniteCCMCenterCoefficient_eventually_inv_log_floor_of_modeAndChiRates`
in `G6N1SelectedFerrersCenterCoefficientFloor.lean:1081`. Its hmode and hchi
assumptions and its constructed port P must match the selected family.
Pointwise nonvanishing alone is insufficient. No new Lean admission is claimed.

## Exact source decomposition and the error paid by existing estimates

For the fixed matched port P, the consumed schedule is
`m_j=N_j=preAnchorTailStart(P)+j+2`, and the row is exactly
`selectedFerrersFiniteCCMRow P j`. Here N_j is the Fourier mode radius;
the auxiliary recurrence cutoff 6m-1 is a different index. The live source
crosswalk in `G6N1SelectedFerrersFiniteCCMSourceRow.lean:219` and
`G6N1SelectedFerrersFokasWindowResidual.lean:463` identifies the same
coefficient row up to a common phase. No diagonal parity correction remains;
the factor (-1)^k in the finite polynomial row is the Ferrers index phase.

Use the two-energy notation in the COUPLED_DEFECT_SIGN verdict (16): the
selected unnormalized Fourier row is a_m=kappa_m z(E0,E4)+e_m. Divide by
the nonzero common scalar kappa_m, and take zhat=z(c0,c4), where c_i are
the centers of the SAME Robin intervals. Thus

    b=a_m/kappa_m,
    E <= E_energy + E_tail,
    E_energy = sup_I ||z(E0,E4)-z(c0,c4)||,
    E_tail = ||e_m||/|kappa_m|.                         (T4)

The Ferrers splice at 5m is not a truncation: the selected series remains
infinite. The finite reference includes k=1,...,6m-1; terms k>=6m are paid
by E_tail. Neither splice nor original mode set -m,...,m is changed.

Under the accepted inputs and eventual thresholds of the
TWO_ENERGY_FULL_QUARTIC_SIGN verdict, equations (8), (11), (19), one has

    E_energy <= 150 C_A m^(13/4)/sqrt(log m) (8/25)^m,
    E_tail <= C_P m^(3/2) 210^(-m)
                  + 20 C_A m^(7/4) (2/225)^m,
    Z >= c_G sqrt(m)/(16 sqrt(log m)),  c_G>0.         (T5)

The last bound follows from Z>=||Pi zhat||>=y_minus and the cited y_minus
bound. These are reused PAPER suppliers with their hypotheses; this note
does not reprove their numerical constants or relax m>=10000. In particular
it does not apply those eventual bounds to the m8 certificate.

Let t=E/Z. Equation (T5) implies t->0 faster than any inverse power of m.
For t<=1/2, using 0<=alpha<=1,

    (Z alpha+E)/(Z-E) = (alpha+t)/(1-t)
                       <= alpha+4t.                  (T6)

Hence for every fixed H, the contribution of 4t in (T3) tends to zero.
Within this sufficient vector-norm route the remaining target is exactly

    m_j^(H/2) sqrt(log m_j) alpha_j -> 0
    for every fixed H>=0.                            (T7)

The independent-energy certificate gives alpha_j<=R_j/sqrt(1+R_j^2)
when its two spectral hypotheses hold for the reference qhat_j. Thus
superalgebraic decay of R_j is sufficient. Merely R_j->0 is not sufficient
for this bound on all complex compacts. Conversely failure of this sufficient
bound is not failure of locally uniform transform tracking: the transform
can retain cancellations lost by the vector norm.

## What this closes and what it leaves open

Closes a conditional source-preserving transfer: existing exponential
energy and Ferrers-tail errors need not be smaller than the ground spectral
gap. Their weighted contribution vanishes under the matched inputs above.

Still open: reference complement positivity at independent cuts on the
whole selected schedule; a noncircular ground upper bound at those cuts;
the central tracking rate (T7); the separate odd-sector/real-zero connection
and the other Goal058 convergence inputs. The finite m8 result alone
supplies none of these eventual spectral assertions.

An exact stopping criterion for this bounded test is the source transfer
proof plus a reviewed reference-rectangle check, and a diagnostic of whether
the next available cell supports decay. It is not a claim to have solved G1/G3.

## Diagnostic of the remaining rate

The existing full-matrix `schur_probe.run` was evaluated at m13 with 140
and 180 decimal digits in separate processes. The ground eigenvalue, gap,
and angle agree to all 40 displayed digits. Together with the earlier runs:

| reference m | ground projection error (numerical) |
|---|---:|
| 4 | 0.0308907298849 |
| 8 | 0.0553421606048 |
| 13 | 0.0605231651722 |

At m13 the numerical ground eigenvalue is about 7.92104e-31 and the next
gap about 6.40882e-28. Seven eigenvalues lie below the reference Rayleigh
energy. The rate (T7) has not been observed in these cells. Three cells
below the selected threshold neither prove nor disprove its eventual truth.
The m8 numerical error here is distinct from its rigorous upper bound
0.05536. The m13 computation is not an interval certificate.

Compact evidence with script hashes: `reference_tracking_diagnostic.json`.
Reproduce in a fresh Python process with the packet on sys.path:
`schur_probe.run(13, 140)` or `schur_probe.run(13, 180)`; inspect
`actual_lowest_full_K_eigenpair`. Raw full diagnostic outputs from this run
are retained at `/tmp/q3_m13_family_tracking_diagnostic_dps140.json` and
`/tmp/q3_m13_family_tracking_diagnostic.json` and are not required premises.

## Independent review

Read-only native reviewer `/root/sign_algebra_review` checked T1--T7,
the common scalar/phase, source splice, quoted bounds and exact conditional
center-floor theorem: no material PAPER findings. This review accepts the
conditional transfer only, not the still-missing spectral or convergence
premises. Numerical diagnostics remain explicitly noncertified.

## Reference-rectangle arithmetic check

`m8_reference_transfer_certificate.py` encloses the entire rational outer
Robin rectangle, not just its reference center. Arb Sturm counts at 140 dps
are (0,1) at the two endpoints for level 0 and (2,3) for level 2. The negative
last-diagonal Robin coefficient makes the eigenvalues monotone for
0<=t<=1/2. Numerical eigensolver values propose endpoints only; the four
exact rational endpoints are accepted by these interval counts.

At 100 and 140 dps for the remaining enclosures:

    E_energy < 1.900e-31,
    E_tail   < 4.186e-21  (CONDITIONAL on the geometric tail hypothesis),
    |zhat_0|-E_total > 2.5748,
    (Z*0.05536+E_total)/(|zhat_0|-E_total) < 0.09336.

The last number is the coefficient in (T2): multiply by
|Xi(0)| m^(H/2) for the normalized transform error. It is not the unit-row
ground angle. The existing strict same-K m8 ground certificate is reused
with dependency hashes. The 100-dps output explicitly records the separate
140-dps Sturm step needed to resolve its very narrow proposed endpoints.

The finite-prefix energy variation is certified unconditionally on this
rectangle. The infinite-tail estimate remains conditional: m8 lies below
the selected-source threshold, so these files do not assert a selected m8
row or establish any cofinal statement. The error-transfer test is favorable;
it leaves the central spectral rate, rather than energy uncertainty, unresolved.

Reproduce with the existing environment:

    .venv/bin/python docs/routeB_bus/fokas_k_sign_2026-09-25/m8_reference_transfer_certificate.py --dps 100
    .venv/bin/python docs/routeB_bus/fokas_k_sign_2026-09-25/m8_reference_transfer_certificate.py --dps 140

Independent code review: `/root/sign_algebra_review` reported no material
findings at final script SHA256
`1d592ddcd9bc169ca62189b773cc72f338f1df62fc750a3465fd4d5263873072`.
It independently executed the pure 100-dps certificate before the final
wording-only clarification of T2, then verified both final outputs and all
dependency hashes. Conditional-tail and no-cofinal limits remain unchanged.
