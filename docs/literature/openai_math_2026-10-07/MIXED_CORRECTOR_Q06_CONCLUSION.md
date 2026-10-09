# Mixed corrector Q6: exact constructions, no arithmetic gain

2026-10-09. Formal Q6 sent09:19UTC once in the living chat
`Совместная арифметическая оценка`; terminal observed09:59UTC.
The owner also directly added: «Ок строим смешанный корректор, у которого
остаток действительно положителен в нужном бюджете».
The rendered latest exchange is preserved in
PROSHKA_MIXED_CORRECTOR_OWNER_FOLLOWUP_DOM.txt; this is DOM provenance,
not original Markdown. Both downloadable originals are preserved unchanged.
The second self-labels Q05_FOLLOWUP_NOT_Q06; do not silently relabel it.
Root read all1136 and988 lines. RH/SP/MB34 and full energy remain OPEN.

## Pins and checks

- Request PROSHKA_MIXED_PRIME_CORRECTOR_Q06.txt:927186bytes,19128LF,
  SHA256 c99b4528d57ec57a8225dd369efdea3c11e27e32ce703702728bf1f783b67452.
- PROSHKA_VERDICT_MIXED_PRIME_CORRECTOR_Q06.md:80888bytes,1136LF,
  SHA256 15521352bd5851ad3bd39ecbc4ed0b76520d0c4ee326f78390676547c1405ce6.
- PROSHKA_MIXED_CORRECTOR_CONSTRUCTION_Q05_FOLLOWUP.md:67925bytes,988LF,
  SHA256 53b3915a97dff4f4aff86c504243b041cd5135d7b722b578017178c217d81c59.
- Q06_EXACT_CHECK.py is the unchanged first appendix,
  SHA256 5b0ad4b4a285481fe8b5d223abe40319298385c0c95ebfbf1410d27645b6d4fd.
  Root reproduced9840 exact diagnostics. Formal additive positive weights
  replace logarithms only in the finite operator diagnostic. The sign with
  true logarithms is established by the separate paper formulas.
- Q06_MIXED_CONSTRUCTION_CHECK.py is the unchanged second appendix,
  SHA256 7cfe31e83816edbfb0b11f661d7a69adbeeb18660ff98af643c4e651f5afda6c.
  It requires SymPy and the original Appendix A registration.json alongside
  the script; scratch reproduction uses /tmp, not a new repository dependency.

Independent q05_moment_audit MP1–MP29 PASS, including9840 diagnostics.
Root also reproduced all474 construction diagnostics using the existing
/Users/emalam/.local/share/uv/tools/demucs/bin/python environment.
Independent mobius_short_transfer construction audit PASS, including474
diagnostics. Qualification: for positive row mass, first fix one permitted
S-valuation pattern and apply the sixth-power-free lattice count outside S.
Here f_q=Z^-1 e_q has mu(n/q) at every q-divisible coordinate, not only
on smooth cofactors; its nonunit cofactors are removed by the profile.
Original attachment prose is preserved unchanged.

## MP5–MP19: the specific two-sweep class fails

On the full divisor-closed good-ideal family, A=D_log+C_Lambda annihilates
mu. K(B)_nm=B_nm/(log qn+log qm) off the unit pair, and
F(B)=C_Lambda* K(B)+K(B) C_Lambda. The explicit all-prime correction
Yp=log(qp)[-K(G)+K(FG)] gives G+N_Y=F²G in the late window.
Before that window the exact extra unit term is [G11-(FG)11]e1e1*.
MP8 retains both same-side orders and both opposite-side orders, including
repeated primes and all powers; the original w_P(nmde) and zero masks remain.

At an inactive nonunit coordinate n, MP10 expresses (F²G)nn as a full
square plus a positive integral of full squares. Choose a fixed good prime
r0, large primes q, and L=D=q_q q_r0/t0. Then the q column is inactive
but qr0 is active. Fixed local conditions on the original u,a rows kill
all other finitely many cofactors inside those squares. Fixed lattice
counting with sixth-power-free inclusion-exclusion gives positive row mass
of order U and amplifier mass of order P. Hence (F²G)qq >=c PU/[L log²L].
The unit-only budget vanishes on e_q, so its residual is strictly negative.
This canonical failure holds for every fixed nonzero annular W.

For the larger two-scalar class Yp=log(qp)[aK(G)+bK(FG)], a fixed narrow
profile gives the exact nonunit block K0[[-(1+a),-(a+b)c],[-(a+b)c,-bd]],
where c=l/(2h), d=l²/[h(x+h)], h=x+l and K0>0. If a>-1 or b>0,
a diagonal is negative. Otherwise A=-a>=1,B=-b>=0 and the determinant
is strictly negative because d/(4c²)=h/(x+h)<1.
Thus this entire two-scalar class fails as a universal profile-family
certificate. Do not strengthen this to every fixed wide W or every local
matrix correction. No diagnostic vector is substituted for mu.

## MC4–MC19: full elimination retains exactly the unknown energy

The divisor-zeta matrix Z satisfies Z A_p=D_p Z, Z mu=e1, e1*Z=e1*.
This is similarity for operators and congruence for forms, not unitarity.
For selected primes let D=sum Dp, F project onto its zero diagonal,
K=I-F, and Ghat=Z^-* G Z^-1. The explicit multiplier
Y=Z* Ddag[-K Ghat K/2-K Ghat F-tau K/2]Z, common to all selected primes,
leaves residual Z*[B e1e1*-F Ghat F+tau K]Z.
All cross blocks are genuinely eliminated; the remaining kernel block
is not estimated. A missing live top prime yields its exact negative
kernel witness, agreeing with the earlier short-prime obstruction.

With every prime included, F=e1e1* and Ghat11=E_M=mu*Gmu. Therefore

    residual = (B-E_M)e1e1* + tau Z*(I-e1e1*)Z.

The second term is a sum of divisor squares, but is exactly zero on mu.
Positivity holds iff B>=E_M, including equality. Increasing tau cannot
improve this source direction. Indeed the full unrestricted null-correction
space is exactly {N=N*:mu*Nmu=0}; the free certificate optimum is E_M.
This confirms the earlier unrestricted-certificate test, not a new bound.
It does not prohibit an explicitly structured certificate whose sign is
proved by an independent arithmetic argument.

## Unpaid term and complete return

MP24 is the full signed double-prime-power correlation, exactly E_M.
MC23 is the original two-column Mobius energy, also exactly E_M. Neither
has been bounded at B=C H U^-1/200+epsilon (1+T1)^A uniformly.
The old conditional bound P[U+U^1/6 L^5/6] remains; on L=D its power
deficit is eta-5rc0/6. The absolute envelope PUL is much weaker.
Insufficient upper bounds are not lower bounds or target counterexamples.

Original comparison and diagonal, raw principal rows, external-g boundary,
lower scales and two-shift returns remain as before. MP27/MC11 preserve
Doff=E_M-lambda R_H-Ddiag. The paid-return margin257/75000 is inherited,
not earned again. All common derivative profiles precede positive Sobolev.
Finite sixth-power inversion still costs5rc0/6: hypothetical eta1/200
leaves at least5887/1200000 before losses; theta1/250 would require losses
below1087/1200000. No antecedent has been proved, so no inverse/high gain.
P/M/R/high transport remain conditional. Linux Comparator is report-only;
no Mac Lean/Arb/Comparator rerun and no moving-Hecke uniformity imported.

## Decision

Do not tune the two scalar sweeps or increase transverse square penalties.
The next mathematical target is direct original MB34, retaining both mu
columns and exact Omega-lambda, or an independently paid source majorant.
Before another Pro request, a new bounded own arithmetic test must address
that estimate; another free multiplier existence argument changes nothing.
AUTOPSY: dropped=COUPLING; note=exact mixed elimination leaves the original source energy and does not pay its required uniform bound.
