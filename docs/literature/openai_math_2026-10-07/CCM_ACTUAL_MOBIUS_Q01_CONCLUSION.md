# Actual-Mobius Q01: bounded acceptance, full target OPEN

20 October 2026. Native CCM goal remains ACTIVE. CF22/PySR PARKED_REOPENABLE.

## Accepted auxiliary result

With the original projector, all k summed first, and all cutoffs retained,

    B_(m,d) = sum_(dk<=m) log(k)/sqrt(dk) P Q_M(log(dk)) P,
    ||B_(m,d)|| <= (40+16 Omega_M)/sqrt(d).

This follows from the inherited L1 prefix error, the dimension-free factor-4
Hilbert return in Q10 section 6, and the inherited continuous identities.
The continuous and lower-endpoint returns cost 12/sqrt(d) and 8/sqrt(d);
the discretization costs (20+16 Omega_M)/sqrt(d).

The noncommutative Fejer window identity keeps every ordered pair and every
intermediate P. It gives T_{>R}^2 <= 2 J G_m, G_m >= 0. Its correlation diagonal
is bounded by (40+16 Omega_M)^2 log(m/R) P. This is a paid auxiliary diagonal,
not a bound for G_m or the full signed sum.

## Exact unpaid input and return

The actual signed off-diagonal O_m is still OPEN. The original verdict's AV
condition, averaged over m in [X,2X), would imply a cofinal bound with exponent
2 epsilon after rank, windows, short-divisor and archimedean returns. Positivity
of G_m selects one scale that works for every vector; no adaptive supremum is
interchanged with an average. AV itself has not been supplied.

Squaring and trace strengthen the original one-sided requirement. Failure of
AV cannot kill the original route. With magnitudes alone the displayed averaged
trace has an extra power X. Q10's bound on T does not bound its prefix-window G.
No improved full exponent, SP, G1/G3 or RH result is accepted.

## Verification and provenance

Request: PROSHKA_CCM_ACTUAL_MOBIUS_JOINT_Q01_2026-10-20.txt,
138159 bytes, SHA256 6f6349f862f6aa450d8b2017ac010bed08f4860f14b10bcd5e455311d21f334d.
Natural terminal response observed about 18:43 UTC; no interruption or resend.
Original: PROSHKA_CCM_ACTUAL_MOBIUS_JOINT_Q01_VERDICT_2026-10-20.md,
61446 bytes, 1027 LF, SHA256 f072574fc3c138be50ba683e3c21cdf66d5c0078ec160fcf212349f356b0b43e.
Downloaded original preserved byte-exact. Root read mathematical argument and
appendices and reproduced all 7021 exact algebra controls. The runnable script
and output are in ccm_actual_mobius_q01_checks/. Script SHA256:
23d4939d6a9d37be05cd033482c772e1d97bb8c435341a02760f365ab7db5f20.
These are rational algebra controls, not actual CCM sign certificates; no Lean
or Arb run. Original records its failed exploratory both-signs expectation.

Independent reviewer ccm_q01_return_review: bounded PAPER PASS for A-C,
conditional on inherited continuous identities and sparse witness. Reviewer
read DOM-extracted mathematical text and compared L1, Q10 and receiver sources;
this is not a second byte-provenance audit or a reproof of inherited inputs.
No material defect in full-k bound, matrix Fejer return, diagonal fee or AV return.

## Next attempt / backtrack

Do not further polish G without a new signed input. Return before Cauchy in d:
try a direct one-sided comparison of full B_(m,d) with actual coefficients.
First determine whether full-k cancellation plus summation by parts can improve
the exponent, including its total-variation and endpoint costs. If it only
recreates the known scalar-primitive barrier, record that failure, retain the
auxiliary lemma, and choose another source-specific mechanism. No Q02 sent.
