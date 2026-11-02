# Density-matched Part A: independent saved-cell verification

DIAGNOSTIC_NEVER_A_PROOF

Archived result commit: 8acecc1574740c5163c2a4e8ef75049f6df84313. Mathematical source base: d26831357b6cb3b2b7d4a569d2031e454952b246.

Status: **PASS**; 15 cells replayed; no new eigenproblem. Saved source matrices, E, Q and U were used without rebuilding a matrix.

Zero counts and strict cutoffs were rechecked with 150-digit scalar arithmetic against the pinned zero tables. DH reflected off-line pairs are always included as complete real/imaginary row pairs. Raw singular values and full AQ norms were independently replayed with NumPy SVD; rank q was not selected by a floating tolerance. Signed counts include every saved eigenvalue below delta*(1+1e-6).

The exact density matches are q=8,18,29,41 at m=20,40,60,80. At m=120 the zeta target q=64 is impossible for a DH height cutoff: the off-line pair at gamma=114.16334273075698 raises q from63 directly to65. Both neighboring DH densities and both same-q zeta controls are verified. The extra m55 controls were also checked.

Maximum relative delta replay error: 6.31e-14; maximum relative sigma replay error: 1.21e-08. Explicit acceptance tolerances are2e-10 and2e-6 respectively; these are finite diagnostic checks, not interval certificates.

Full per-cell values, strict-count margins, kernel/orthogonality residuals and source-file hashes are in verification.json and verification.csv. Tiny signs of individual near-zero full eigenvalues are not certified, but the adaptive positive-threshold count is well separated from every saved eigenvalue.
