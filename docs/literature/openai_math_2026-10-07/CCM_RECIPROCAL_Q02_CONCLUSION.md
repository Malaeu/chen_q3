# CCM reciprocal Q02: paid fast sector; joint slow source OPEN

20 October 2026. Native goal ACTIVE; CF22/PySR PARKED_REOPENABLE.

## Accepted bounded PAPER result

Use original N=m, L=log(m), M=R=floor(m^epsilon), three-condition P,
all actual Mobius coefficients, prime powers, mixed terms and endpoints.
Write T=C+E. With J=m^2, split E into the exact fast and slow reciprocal
harmonics plus Fourier remainder, as defined in original Q02 sections 4–5.
On each d-block D and t-tile [T,2T], fast means
h >= max(1,ceil(D^2(1+log D)/T)). No slow harmonic is discarded.

Set D1=2/L+4 Omega_M, D2=4 Omega_M/L+4 Omega_M^2,
K2=16/3+20 D1/9+4 D2/9, ND=ceil(log_2(m/R)), and V=C+E_slow.
Then

    ||T - V|| <= 32(1+D1) ND (1+2L) + K2/(pi^2 m^(3/2))
               = O_epsilon(m^epsilon log m).

The moving-cutoff reciprocal mean square retains max(T,d,e) in every pair
integral. The bound is uniform in the original space; no hidden rank factor
or interchange of adaptive W and averaging occurs.
The Fourier tail uses the continuous B2 primitive, not uniform approximation
of the discontinuous sawtooth. Its lower derivative endpoint is -A(d)/12.
Original P1=0 kills Q'(L)=-(2/L)11*, so A(m)=A'(m)=0.

## What remains unpaid

The one-sided estimate V <= C_epsilon m^eta(epsilon) P with eta -> 0
remains OPEN. This result pays a sector, not a new full exponent.
For d>m/2 the full k-sum vanishes and C+E cancel exactly. The k=2 shell
survives below m/2. Separately majorizing C and E_slow can lose this cancellation.
The exact Mellin recombination is -zeta'/zeta + zeta' U_R, initially only
in absolute convergence. No contour crossing or RH-free zero estimate is supplied.
Slow comparable-scale h=1 phases have only bounded variation; a general
coefficient example does not exclude cancellation of actual Mobius coefficients.

Short-divisor return costs m^(3epsilon/2) with displayed logarithms, once;
archimedean return is 50 log m+8. If the open V estimate were proved,
max(eta(epsilon),3epsilon/2), with logarithmic slack, would feed the receiver.
No full SP, cofinal improvement, G1/G3, CF22 or RH closure is claimed.
Inherited Q10 power 3/8 is not improved by the elementary full bound here.

## Verification and provenance

Request: PROSHKA_CCM_RECIPROCAL_ERROR_Q02_2026-10-20.txt,
93065 bytes; SHA256 21893c097ed643fef7c99ff9dbd148c0e05563da617a45dfe439063e6ef61198.
Sent once in the existing owner chat around 18:58 UTC; completed naturally
around 19:25 UTC. No interruption, resend or replacement chat.
Original: PROSHKA_CCM_RECIPROCAL_ERROR_Q02_VERDICT_2026-10-20.md,
64517 bytes; SHA256 4c8bf00e467a73903c861fcb30963a6e05c685f3ac0c215de73bb447671b7a4e.
Root read the full original including appendices. Independent read-only reviewer
ccm_q01_return_review found no material defect in (7), (11), (17), (22), (37),
empty-shell cancellation and Mellin return. Inherited Q01 inputs and the
sparse witness were not independently re-audited in this cycle.

Root reran both original scripts: 1580 exact controls passed, including
63 detections of a wrong Euler sign; six 45-digit numerical diagnostics
matched the original (max discrepancy 8.9683e-44). These six are not interval
certificates or CCM spectral experiments. Scripts and results are preserved in
ccm_reciprocal_q02_checks/. No Lean or Arb run in this cycle.

Own pre-answer attempts: CCM_Q02_DIRECT_ABEL_TEST.md and
CCM_Q02_LOW_RECIPROCAL_RANGE.md. The latter explicitly corrects the initial
upper-derivative warning using the actual endpoint projector.

## Next mathematical work

Backtrack before separate moduli of C and E_slow. Attack their actual signed
joint V, preserving empty-shell cancellation. Improving the already affordable
fast sector cannot by itself close the goal. No Q03 sent; no Pro response pending.
After three substantive no-gain attempts, or an established earlier impasse,
send the same living chat a concrete remaining mathematical question.
