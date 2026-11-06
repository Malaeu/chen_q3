# Independent read-only review

Reviewer: `/root/optimal_review` (reviewer role, GPT-6 Astra). Final verdict:
**No remaining material findings in the finite diagnostic scope.**

Reviewed Part A sign conversion, full Gram reuse, statistics and preregistration;
centered Mellin identity and elementary BV tail proof; Part B zero cells,
quadrature, permutations and convergence; assembled report and prediction scores.

Independent numerical checks:

- All 2,596 local integrals replayed from the final grid, maximum discrepancy 1.67e-16.
- All eight weighted heads replayed, maximum discrepancy 1.05e-16.
- All eight Spearman correlations and seeded 1,000-permutation p-values matched.
- Seven N=5000 optimal intensities recomputed directly at 30 decimal digits,
  maximum discrepancy 3.74e-13.
- Final convergence flags, six prediction outcomes, Brier score and all J3
  comparison rows match the artifacts.

Issues found and resolved before acceptance: source pinning for tail input;
undefined Part B coefficient reference; omitted Simpson-16 comparison; lost
convergence flag; missing next-zero metadata; synthetic zero-check report;
scaled versus relative convergence wording. Plot labels and Markdown table
headings were also corrected. No escalation was required.

Limits: the quadrature is not interval-certified; the independent tail bounds
are broad. The finite results establish no asymptotic statement or RH conclusion.
The review is not a Lean proof or semantic promotion of the RH route.
