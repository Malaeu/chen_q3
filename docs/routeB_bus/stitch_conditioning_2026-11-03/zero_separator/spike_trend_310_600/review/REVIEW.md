# Final bounded trend review

No blocking implementation or bookkeeping issue found for the stated
finite numerical diagnostic. Reviewed this directory's scan_extended.py
(the generalized tiny-zeta-tail version), analyze_trend.py, all90 scan
receipts and the scalar aggregates. No source/eigensystem recomputation.

The counters independently replay: zeta14 YES and16 UNRESOLVED; plant30 NO;
DH30 NO. All15,073 sectors are represented exactly once by an evaluated
(371) or bounded (14,702) receipt. Dimensions q+r=m+1, nontrivial0<r<d,
and intersection with kappa>=1 check out. Every best-gap bracket is marked
resolved in width, with maximum width3.552297 numeric guards; a narrow
bracket around zero is not a resolved sign. Results are in VALIDATION.json.

The pruning logic remains valid at the level of exact finite identities:
||AQ||>=0 gives gap<=lambda_r. Necessary singular-minmax rejection gives
gap<=0 when the indicated negative magnitude cannot fit beneath lambda_r.
Such rejected sectors remain in the global upper bracket rather than
being assumed unable to improve a negative candidate. Tiny zeta levels
lambda_r<=guard are explicitly bounded and labeled
UNRESOLVED_TINY_SEPARATOR when no positive incumbent excludes them; this
avoids the previous assumption that a positive resolved incumbent must
always exist. The resulting final sign stays UNRESOLVED. Numerical guards
are heuristic source/spectral budgets, not interval enclosures.

For a fixed m and source, increasing kappa adds constraints, so J shrinks
and delta=||A|J|| cannot increase. Thus its literal maximum over kappa>=1
is delta at kappa=1, using strict gamma<T boundary conventions. This is a
different observable from max_kappa(lambda_r-delta). Zeta's first sector
is evaluated explicitly; controls use their separate kappa1 residual
receipts. The two observables must not be interchanged when discussing a
spike or a trend.

The fits are correctly labeled descriptive. The six bins are fixed,
nonoverlapping five-m blocks, and their medians are medians of BEST-PER-m
gaps, not medians over kappa. An independent replay gives medians
[.616327825783449,.012314266810501628,0,0,.06347546291896866,0], OLS
intercept5.003384008195404, slope−.8011086771892768, R².46914146626438646,
Theil–Sen slope−.05265345963409321. Leave-one-bin slopes range from
−1.03850899008 to+.03802400979. The zero entries are display/statistic
substitutions for censored numerical-floor gaps, with original brackets
and labels retained. They are not exact source zeros. The mismatch between
OLS/robust slope and sign-changing leave-one-bin sensitivity supports no
reliable asymptotic decay law. Delta-max's low R² similarly indicates that
this grid is dominated by oscillation. Fits supply no probabilistic or
continuum conclusion.

A wording qualification is essential: these data establish no positive
uniform margin at the current resolution. They do not prove the absence
of every positive uniform margin below the numerical floor, nor exact
closure or failure in the16 unresolved zeta cases. The rebound block is
real at this grid/resolution and rules out claiming monotone observed
closure, not an independently specified asymptotic theorem.

There is an exact structural reason planted delta spikes may closely track
zeta. With the same source normalization and frozen common zeta rows,
J_plant is a subspace of J_zeta whenever the planted quartet is included.
The planted source perturbation factors through that quartet's two real
Fourier rows. It therefore annihilates J_plant, so

    A_plant|J_plant = A_zeta|J_plant,
    delta_plant <= delta_zeta.

This applies to the literal source matrices if their definitions match
exactly; rounded/quadrature-assembled versions retain numerical error.
It does not imply equality of the optimized separator gaps, whose spectra
and ranks differ, or analogous behavior for DH. Thus delta-spike matching
alone is not a discriminator of the planted source.

Finally, MP768/1024 frame agreement tests arithmetic on the supplied decimal
nodes. It does not propagate zero-table uncertainty or certify source
quadrature/eigenvalue floors. Shifted LDL negative-count ranges were
intentionally omitted from the headline trend table; none should be
promoted to exact inertia by this review. Native frame orthogonality and
finite source/order checks remain numerical diagnostics.

DIAGNOSTIC_NEVER_A_PROOF. Route B=CHALLENGER/NOT_RH. No status promotion.
