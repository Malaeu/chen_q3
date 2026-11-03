# Diagnostic cards

## A. Softening removes the resolved cutoff spikes at usable smoothing

HYPOTHESIS: on the tested finite grid, moderate Gaussian damping makes the
auxiliary sharp-subspace separator less intermittent, before stronger damping
pushes its gap below numerical resolution.
Evidence: SUMMARY.csv compares the same m and sector convention with the
pinned unsmoothed source. Source normalization and finite-census sensitivity
are checked separately. The matrix and the eigenvalue scale have changed;
a smaller absolute gap is not evidence for a weaker separator mechanism.
What kills it: a marginal cell fails MP replay; new zeros/tail change a gap
by its margin; or a properly normalized wider grid loses the apparent effect.
Handoff: seek a source-side, uniform-y gap comparison with explicit spectral
and subspace errors; finite critical-line partial-sum positivity cannot pay it.

## B. First-quartet damping approximately controls the negative level

HYPOTHESIS: the first off-axis quartet dominates the bottom-level response
to y in these windows, to percent accuracy relative to c8.
Evidence: DH and plant sweeps at310/450/600, c8..128. Relative mismatch from
the first-quartet damping is at most1.13% DH and0.323% plant. Separate isolated
quartet and fixed-vector data retain the non-scalar phase effect.
What kills it: another quartet becomes dominant; enlarged census, a wider
window range or a phase-sensitive regime gives a substantial mismatch.
Handoff: a quantitative perturbation estimate comparing the full source
bottom mode with the isolated quartet, with an explicit positive-background
bound. No dominance theorem is established here.

Finite algebraic check (not a global claim): if E=a+ib with a,b independent,
the isolated smoothed quartet is4rho [a b] M(theta)[a b]^T, where
M=[[cos(theta),−sin(theta)],[−sin(theta),−cos(theta)]], det M=−1.
It retains one positive and one negative level for every finite y. A tiny
computed negative below resolution is not a genuine crossing. The full
matrix includes the other zeros and need not obey that rank-two conclusion.

Kill switch: c32 near-floor gaps are left UNRESOLVED. No escalating precision
search for a favorable sign, no tail-free claim, no cofinal extrapolation.
