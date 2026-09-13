# Nonzero residual coupling: second semantic hunt

STATUS: SOURCE_PINNED_BOUNDED_DISCOVERY.
CONSUMPTION: INCOMPLETE_NO_CONSUMABLE_TARGET (canonical theorem/consumer edge unbound).
Owner request: rerun semantic search for established constructions that compensate a nonzero residual as part of the whole energy, and explain how authors discover them.
Owner is root task 01a092ef-bf89-7693-aca8-42c3b691138a in its existing isolated math-worktree. Canonical task 01a084f4-7498-7021-bac2-91d184d58dc7 remains foreign ACTIVE, epoch 1. No canonical writes, proof admission, or new goal.
Base commit: 4702d6d505dd6f497c73bb575d802f9486cbd678 (remote checked unchanged).

## Exact object and source pins

The prior BRIEF_2026-09-13_RESIDUAL_COMPENSATION.md sections 1-3 fixes the complete theta density h, r=h*h, Phi(X)=exp(5X/2)r(exp(2X)), f=Phi/||Phi||_2, all weights and normalization. Retain that source verbatim.
For t=exp(2X), X>=0, s in (0,1):
 p_t(s)=t h(ts)h(t(1-s))/r(t),
 g_x(t,s)=a^(9/4)h(ats)h(at(1-s))/(h(ts)h(t(1-s))), a=exp(2x).
Every finite family x_i in I=(-log(2)/2,0), c_i complex is required.
 g=sum c_i g_xi; b=sum c_i x_i g_xi; Cg=E_t g; F=Var_t(g).
 V[c]=M[c]-L[c],
 M=2 integral f^2 [X E_t|g|^2+Re E_t(conj(g)b)] dX,
 L=2 integral f^2 [X F+Re Cov_t(g,b)] dX.
Neither M>=0 nor V>=0 is assumed. The target is a source-derived nonnegative representation of the WHOLE V, not L=0.

## Paid facts and exclusions

Prior HUNT R1-R9: covariance Green kernel; score rho=partial_X log p; derivative/averaging commutator; exact equal changes to M and L by conditional-mean-zero correction.
NULL_AND_GROUND_STATE_TEST N1/N2: full null identity with nonzero X=0 boundary; null identity is not L.
Same report G3-G6: Gaussian sibling is an exact square. Actual theta gives V=|sum c_i f(x_i)|^2/(2k)+E_k. For every fixed k>0 E_k has a negative finite row on I. Do not retry fixed-k positivity or claim a negative V witness.
User-pasted L_{-delta}>0 argument is an unreviewed lead, not an accepted premise here. Only the need to couple nonzero terms is used.

## Negative control

Phi_epsilon=exp(epsilon X^2)Phi, epsilon<0, has negative V rows under the accepted DEFORMED_SOURCE_ZERO_WITNESS report. The conditional law p_t and covariance identities survive. Its likelihood acquires exp(epsilon x^2)t^(epsilon x). Any usable criterion must name a source-specific equation/inequality failing or unpaid for that control. Generic covariance positivity, integration by parts, conservation and metric changes alone do not separate it.

## Own search rewrites (UNVERIFIED)

A: Seek a Bogomolny/calibration/energy-charge decomposition: the mixed term is an exact divergence or curvature coupling, and a source equation fixes its coefficient. Need full equality, boundary and a nonnegative surviving energy; no identification of our metaphor with a physical vortex.
B: Seek covariance-deficit or storage/dissipation certificates: an operator equation produces a positive block/Gram representation whose Schur complement or integrated dissipation equals V. Do not assume a positive square root of V or positive M. An auxiliary equivalent norm alone is insufficient.

## New dictionaries and bounded protocol

1. Bogomolny energy square topological bound vortex critical coupling.
2. Helffer Sjostrand covariance Brascamp Lieb deficit Hessian identity.
3. Kalman Yakubovich Popov positive real lemma storage spectral factorization.
First run registered ask.sh on these three NEW dictionaries; retain failures, then inspect local sources and knowledge. Prior queries are already receipted; do not repeat them. Existing Picone/ground-state and DMS hypocoercivity sources are controls, not new discoveries.
At most one read-only researcher plus the reserved independent reviewer; no descendants. Parent reads probability/control sources; researcher reads physics. At most one primary source per retained mechanism (up to three); a fourth only if required to validate a mapping. Stop at source-verified candidates, exact hypotheses/gaps, how construction is motivated, and one smallest next mathematical test. No numeric sweep or Proshka send in this search. No theorem closure counters updated for literature discovery.

## Source SHA256 manifest

- docs/Codex/BRIEF_2026-09-13_RESIDUAL_COMPENSATION.md: b45890155160eda8189a559459afd6cfb9d7818ad8d405c18244a5864895f60c
- docs/Codex/REPORT_2026-09-13_RESIDUAL_COMPENSATION_HUNT.md: 7aaf8e43faa5bfd37954d6076db3acb1801325777bd9d989b25d75c9a9466c14
- docs/Codex/REPORT_2026-09-13_NULL_AND_GROUND_STATE_TEST.md: 19ce3481523bfb3f3f9ba8be24f2c86dc2f1916d80f9535a451d010bceef0d95
- docs/Codex/REPORT_2026-09-13_DEFORMED_SOURCE_ZERO_WITNESS.md: 70163ec5703ea516b8a191f705a26034cc9914d875f8e74cee7544a0b496bb4c
