# Q05 — full joint Fourier transfer, no arithmetic power gain

2026-10-21. Original received after owner unlocked Mac. Full987-line original
read, preserved byte-exact from Downloads:64150bytes, SHA256
9ccdfe1e6f02633e3fbac0c273b4d6a800bad6b3344fefe666805f9f74c4177a.
Request175378bytes,2741LF, SHA256
b893da00379ad6e45c14836686a9c7a3103590f639ac7c9b582a2090e3b95024.
Natural terminal response was observed2026-10-20 around21:55UTC. No resend,
interruption or Q06. Previous local retrieval blocker is resolved.

## Root verification

All187 exact controls reproduced with identical script and registration hashes
in ccm_joint_q05_checks/. These test finite algebra and deliberate model
failures, not actual CCM spectra or asymptotic cancellation. No Lean/Arb run.
The embedded result's independent_review=NOT_RUN is the author's original
record, preserved unchanged; separate review outcome belongs below.

Primary source checked live: Green–Tao arXiv0807.1736v4, introduction(1.1),
Theorem1.1 and its remarks, https://arxiv.org/html/0807.1736v4.
It supplies genuine Mobius linear-phase cancellation uniformly in theta,
for every FIXED logarithmic exponent, with ineffective constants. It does
not supply the desired polynomial cancellation or a growing-exponent rule.

New variation calculation retains fixed original P and both endpoint zeros:
A(m)=A'(m)=0. Thus disappearing terms at x=m/k preserve C1 regularity.
Euler comparison of g_x(u)=u log(u) A'(xu) gives
||B'_m(x)|| <= v_m x^(-3/2), v_m=36+14D1+4D2.
Together with b_m=40+16Omega, the actual Abel fee is
 a_m=b_m+2v_m=O_epsilon(m^(2epsilon)/log(m)^2).
All ordered products and intermediate projectors survive the exact identity
 G_D=int F_D(theta) Phi_D(theta)^*Phi_D(theta) dtheta.
The next sup-prefix times variation inequality loses source coupling.

Full direct return:
 ||T|| <=12 C_a a_m sqrt(m)/(log R)^a,
 hence exponent1/2+2epsilon, with fixed logarithmic savings only.
The squared return additionally costs sqrt(J). Trace averaging costs rank P
and gives X^(2+5epsilon)/log(X)^(2a+4), insufficient for Q01 AV.
No free cofinal subsequence or suppressed rank. Q02 error is not paid twice.
The inherited Q03 exponent3/8 remains CONDITIONAL on unchanged ZF78.

The outer Fourier sector is cheaply bounded by Parseval, but central Fejer
mass is not paid. Kernel mass alone is not a lower bound on actual energy.
The positive model a_n=exp(-sqrt(log(3+n))), B(x)=x^(-1/2) satisfies all fixed
logarithmic Fourier bounds and smooth variation, yet has nearly half-power
linear size. It rejects only the generic transfer implication after the
actual arithmetic is discarded. Its coefficients are NOT Mobius; it cannot
kill the original CCM route.

## Independent review

Read-only q05_audit returned bounded PAPER PASS: no material defect in
variation constants, both endpoint zeros, noncommutative Fejer identity,
Davenport-to-weight transfer, block/rank return and relaxed counterexample.
Use the explicit source equation(1.1) as the direct scalar supplier. This
acceptance supplies no new arithmetic exponent, AV or actual-Mobius no-go.

## Next mathematical fork

Stop tuning fixed log powers or Fourier cutoffs in this scalar-majorant
mechanism. Return before sup-times-variation, preferably before divisor
squaring, to the original one-sided form. Existing source-native alternatives
are being checked against the shelf to avoid repeating prior no-gain routes.
No new sufficient assumption is promoted to a supplier. CF22/PySR remain
PARKED_REOPENABLE; RH and eta(epsilon)->0 remain open.
