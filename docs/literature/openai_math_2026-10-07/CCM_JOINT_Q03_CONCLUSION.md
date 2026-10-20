# CCM Q03: complete conditional logarithmic improvement

2026-10-20. Native goal ACTIVE. CF22/PySR PARKED_REOPENABLE. RH OPEN.

## Accepted bounded PAPER result

Original N=m, L=log m, M=R=floor(m^epsilon), original three-condition P.
All prime powers, actual Mobius coefficients, mixed terms and endpoints remain.
For L>=4 and STRIP(a): every right zero has delta<=a, 1/8<=a<=1/2,

    P K_m P >= -E_a P,
    E_a = 2^18 C_z log(5+Omega_M) [m^a + m^(1/8)(1+L)^2].

C_z is an absolute local zero-count constant. With a=1/2 this uses the
classical strip. The a=3/8 version is CONDITIONAL ON THE SAME ZF78;
ZF78 was not proved in Q03. At fixed 0<epsilon<1/32 the full conditional
scalar T_{>R} price improves from m^(3/8)L^2 log(3L) to O_epsilon(m^(3/8)L).
This is a genuine logarithmic improvement, not a smaller power or eta->0.

The new mechanism is a weighted Laplace sampling estimate uniform in damping:
fixed-radius subharmonic disks for delta>=1/8 remove the old L^2 loss;
small disks cost L^2 only in the subordinate m^(1/8) sector. The apparent
rank factor cancels through (2M+1)/(LT)<=3/(4pi), T=2Omega_M+2.
The reflected zero pair is a signed product, not an absolute square.
The step 2Re(U conjugate(V))>=-|U|^2-|V|^2 still loses the needed joint
cancellation. Critical-line terms are nonnegative without assuming RH.

## Exact return and limits

Put D=P(A_arch-c_A I)P. Exact source identity:
P K_m P = D - T_{<=R} - T_{>R}.
Thus T_{>R} <= E_a P + D - T_{<=R}. Scalar payment adds the accepted
short-divisor fee and 50L+8 once. Returning to K cancels these exact terms;
there is no duplicated fee. Transfer to Q02 V costs F2 once if needed.
The inherited K-to-Weil source dictionary and sparse-band witness are not
reproved by this bounded audit. No zero, prime sum or CCM spectrum was
numerically evaluated here. No Lean/Arb run; no full exponent gain.

## Independent review and reproduction

Reviewer /root/ccm_q01_return_review: bounded PAPER PASS, no material defect.
Checked reflected normalization and H1 zero-extension regularity, sampling
constants, both height signs/multiplicity, tail, conditional strip, exact
returns, and absence of circular positivity. Source normalization agrees
with Suzuki §§3.2–3.3; literal source dictionary remains inherited.

Original received byte-exact, 68789 bytes, SHA256:
4086ff0fad9747752f039dbe856ab4a6ecd41bd7543295576da15aac47cb23cd.
Request SHA256:
664df558b602e914457885c6ba519c016ba8b35c0066c194430e6e0570490ac8.
Original: PROSHKA_CCM_JOINT_SIGNED_ARITHMETIC_Q03_VERDICT_2026-10-20.md.
Root read full original. Extracted scripts are unchanged in ccm_joint_q03_checks/.
Exact reproduction: 2536 rational/integer checks PASS.
Nine binary64 transform diagnostics PASS using existing .venv SciPy 1.16.3;
maximum observed error 2.788417451505779e-15. These are not interval certificates.
The JSON prior_attempt field refers to Proshka's unsuccessful 70-digit run,
not a local completed run. No installation performed.

## Branch evidence and next debt

Three own attempts retained: ONE_SIDED_PRIMITIVE_CONE_TEST,
ENDPOINT_SIGN_TEST, AFFINE_RETURN_TEST. None improved the full exponent.
ACTUAL_PRIME_BLOCK_OBSTRUCTION additionally proves an original uncentered
prime block has lambda_max >= c sqrt(m)/log^9(m) eventually. This kills
independent subpower payment of every raw block, not the full signed sum.

Next mathematical debt: control the actual reflected endpoint-map coupling
relative to the positive critical-line contribution, or another source-preserving
mechanism that yields eta(epsilon)->0. Individual map norms and all-pass
multipliers do not supply it. Do not promote this reformulation to a solution.
Owner has independently started a geometric question in the SAME Pro chat.
It was live at 20:19 UTC; do not interrupt or send Q04 while it runs.
Read its terminal result before selecting the next concrete attempt.
