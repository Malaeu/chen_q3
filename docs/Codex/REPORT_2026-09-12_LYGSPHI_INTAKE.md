# Lee–Yang sibling: exact theta spin lift excluded, general realization open

STATUS: ACCEPTED_PAPER_KILL_EXACT_THETA_ENTROPY_BINOMIAL_JOINT_LIFT.
GENERAL_PHI_GS_REALIZATION: OPEN. GLOBAL_IC: OPEN. GLOBAL_ODD2: OPEN.
ALL_ORDER_SOURCE_SIGN: OPEN. RH: OPEN. PX_RH_CLAIM: NOT_MADE.
Isolated mathematical evidence; no Lean or canonical admission.

## Receipt through GitHub

The completed response to REQ-2026-09-12-LYGSPHI was published by Proshka in
commit cdb3f2698e5e8bf494ecbddac54a319c6edd69ec and fetched directly from GitHub.
The isolated branch fast-forwarded without changing the canonical checkout.
The unchanged raw file is
`docs/routeB_bus/proshka/PROSHKA_RESPONSE_GOAL058_LYGSPHI_2026-09-12.md`:
56813 UTF-8 bytes, 907 LF, final LF, no CR, SHA-256
`630da77ed6a85d013e60078090be3135e737db0846194675b05af775cd238fb4`.

The original request is pinned at d6cbfa02d9604f2aeba2e70b6daaebff80c0859a,
89217 bytes / 1384 LF, SHA-256
`32d75bc0235c8aaa48c326e240b5e1123d914d0caf8ea568a86402adb0ae2e71`.
The original mathematical reasoning completed naturally: UI 26m25s.
Its raw `REPOSITORY_WRITES: 0` describes that original response; the subsequent
GitHub publication is a separate technical action, not a new proof attempt.

The owner explicitly changed this task's exchange to GitHub: full assignments
and responses in the repository; one short link/instruction in the existing
chat. The publication assignment is
`docs/routeB_bus/proshka/GITHUB_TASK_GOAL058_LYGSPHI_PUBLICATION.md`, commit
2a931ada80f418f85ea2cfe00922a43cc6ac78c9. The one-line notice was sent at
2026-09-12T20:55:18.980Z; natural UI reasoning was 5m44s. Proshka returned only
the commit and response path. Exact byte equality was then verified locally.
The earlier base64 retransmission was abandoned after its rendered length
failed the declared length; it has no mathematical counter effect.

## Accepted mathematical result

Keep the actual source and normalization `p = Phi/Z`, `Z = integral_R Phi =
xi(1/2) > 0`, and `M(h) = xi(1/2+h)/xi(1/2)`. The probability normalization
Z does not replace the physical L2 normalization A.

For integer k >= k0 = max(4, ceil(sqrt(gammaPhi+1))), where
`gammaPhi = -(log Phi)''(0) > 0`, set n = k^4 and delta = k^-3.
The precursor has positive equal observable weights delta and positive pair
couplings `J0 = k^-4 - gammaPhi*k^-6 >= k^-6`. Its ferromagnetism is valid.

The exact source reweighting instead produces

    Ptheta_k(sigma) = Phi(delta*S) / (C_k * binom(n,(n+S)/2)),
    S = sum_i sigma_i,  C_k = sum_{s=-n,-n+2,...,n} Phi(delta*s).

Its magnetization masses equal `Phi(delta*s)/C_k`. For THIS corrected family,
Theorem A proves weak convergence to p, uniform exponential moments for every
radius R, and locally uniform convergence of its entire field transforms to M.
The full-cell Riemann error is bounded by

    epsilon_R(k) = 2*k^-3*A_R + exp(-k)*W_(R+1),
    W_R = integral exp(R*abs(x))*Phi(x),
    A_R = integral exp(R*abs(x))*(abs(Phi'(x))+R*Phi(x)).

All integrals are finite by the accepted full-source inputs. The denominator
is bounded below by Z/2 eventually; the finitely many initial indices are
covered explicitly. No property of the precursor is transferred by this limit.

For a positive pair-Ising law, the four-cell conditional odds of spins i,j
are exactly `exp(4*J_ij)`, regardless of fixed surrounding spins or real fields.
For Ptheta_k with every other spin fixed to +1, Theorem C gives

    O_k = 2*k^4/(k^4-1) * Phi(k)*Phi(k-4*k^-3)/Phi(k-2*k^-3)^2
        < 4*(3/8)^11 < 1/10000,                         for every k >= 4.

The full theta-series envelope, not a finite-mode approximation, proves this.
Thus the conditional effective coupling is below `-log(10) < -2` at every
index. The exact corrected joint law is not a pair ferromagnet.

The binary elimination identity in raw equation (24) proves that local
log-supermodularity survives summation over hidden spins. Consequently the
same corrected visible joint law cannot be a marginal of a finite pair
ferromagnet, even with arbitrary real fields, or a limit of such marginals
on that fixed finite visible space. A factor-ten relative repair of all four
witness probabilities also fails the necessary odds inequality.

## Exact limit of the exclusion

The four witness configurations escape to magnetization k as k grows. Their
containing event has probability at most `B*exp(-k/2)`, where B is a uniform
exponential-moment bound. Their exact sign defect is therefore not a lower
bound on the absolute distance from the full class of ferromagnetic limits.

The result does not exclude another joint law with the needed magnetization
histogram, a different observable involving hidden spins, an admissible
asymptotic repair, or a general Griffiths–Simon realization of Phi/Z.
It supplies no negative witness for the actual Hankel matrices, K_-, or Weil
form, and proves no additional actual ODD2 region or all-order source sign.
The histogram and positive-cluster alternatives listed in the raw response
are unpaid interfaces; no experiment on them has been executed or assigned.

## Verification and counter decision

Parent read all 907 raw lines and independently checked the same-law limit,
normalizations, all-k theta envelope, conditional-odds identity, hidden-spin
elimination, and rare-event limitation. All four complete source frames were
byte-matched against committed source f40db276e8f3c4c4d47adec755e5fb72691a4999;
the raw Appendix A hashes and Git blobs match. Accepted dependencies retain
their original scope. No recursive archive or full physical-paper re-audit
is claimed. The physical papers motivate the construction; the exclusion is
proved by the displayed elementary argument.

Sole checker `/root/sibling5_check` independently accepted
`ACCEPT_KILL_EXACT_THETA_ENTROPY_BINOMIAL_JOINT_LIFT`; receipt SHA-256
`da7cb41bb53be24b6d4313834e39774f1d5f87b92f5b2135be74ba9b2f8e6df5`.
The checker independently replayed the verifier. Its Python SHA-256 is
`7745fa643285580ebc33695e34f437870df3745d9a97c2f56a5b408cf818dc35`;
stdout is 1461 bytes / 21 LF, SHA-256
`1b5272ef9a794a3e0286864adf3d06e8edef114eece85b293df4c767c668789b`.
The raw script and literal stdout also exactly match the parent's prior
execution. The nine rational comparisons and planted models pass. These
checks use zero source evaluations, quadratures, Hankel tests, or Lean runs;
the analytic argument, rather than these finite tests, supplies the result.

This is useful exclusion of one microscopic construction, with no new actual
source-sign supplier. After complete independent intake the agreed source-sign
no-delta counter is **2 -> 3**. Transport recovery does not add another attempt.
The owner-requested next step is joint brainstorming before another proof
attempt. This counter is not a declaration that the active goal is blocked,
and it does not prove impossibility of the broader Lee–Yang route.

AUTOPSY: dropped=SIGN; note=the exact source reweighting preserves the desired limit but destroys the required ferromagnetic conditional-odds sign in that same law.

The accepted input-to-consumer gap is an admissible ferromagnetic family
whose own magnetization transforms converge to the actual M. It remains open.

## Independent check of this intake summary

The sole checker returned CLEAN on the complete 130-line summary, SHA-256
`0680c199c535527a7b74e4fe478aff8d4891b29033d24d593a9eb8dc4e7f1430`.
The summary review receipt SHA-256 is
`d0bc055a1d770af68a8a97cfa35bd6855299d11f0a54f412559ed526af70c4f8`.
This receipt adds no mathematical claim or wider acceptance scope.
