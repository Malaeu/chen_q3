# Initial independent diagnostic review

2026-11-04. Scope: read-only inspection of the experiment and existing outputs; writing review evidence only. No source edits, numerical matrix runs, commit, push, descendants, or status promotion. CHALLENGER_NOT_RH; PX_RH_CLAIM: NOT_MADE. Final exact-payload review remains pending.

## Material open finding

At reviewed matrix_probe.py SHA-256 `2308c8a4606600fc63208c010c7137c8228fa471e5cfbda98b7929af7390b004`, `--stage first` evaluates only the first admission cell per gamma. Existing cells m=21,139,762 have no positive-a detection. `--stage checkpoints` skips integers. Therefore these stages do not establish preregistered first matrix thresholds for gamma=50,200,800. A consecutive scan until the first trigger (or an explicit feasible cap with appropriately limited censoring) is still needed. The parent was informed immediately. No monotonicity across changing m is available from this code.

## Verified by inspection

- PREDICTIONS.md fixes m+1 physical even coordinates, literal A+Q, strict T_m admission, source quotient, factor four, exact-rational high-precision a=1/3, one-bin D3, and control thresholds before scoring.
- Physical gate integrates the full interval using the basis d_j*(-1)^j*cos(omega_j*x)/sqrt(L). The sign reproduces the source quotient. Real/imaginary quadratures form 4*(rr^T-ss^T); no conjugation, hidden half-interval, or normalization factor. Its independent analytic reference uses 80 digits and an entire sinc continuation. All 12 positive-a plus 4 a=0 cells pass the declared tolerance; a=0 gate scope is explicitly Q only.
- source_float.py retains the pinned zeta alpha=1/2 archimedean digamma/trigamma formulas, direct n=0 correction, geometric endpoint terms, k<m prime powers, divided-difference off-diagonal, scalar tails and rank-one even pole. It does not normalize, clip, replace A with a Gram matrix, or adjust its spectrum. Promoted real prime phases are an arithmetic change only. The unsuccessful float64 control evidence is preserved.
- rayleigh_pinned.py reconstructs the pinned source freshly, promotes the saved binary64 vector to MPFR, divides source and plant forms by the same squared norm, and uses 4*Re((sum v_j*c_j)^2). It labels this a Rayleigh witness, not full high-precision eigenvalue ordering or interval certification.
- corner_scan.py scans every integer m=16..3000 with high-precision exact-rational a values, evaluates the source direct n=0 formula and checks the source at m=80. Strict negatives are retained without a monotonicity assumption.
- Matrix eigenvectors are physical coefficient vectors; peak energy, centroid, top modes, residual, squared norm, bin and above-band flag are recorded. The current gamma14,a=1/20 first detected vector fails literal one-bin D3 (peak mode 5); the other two gamma14 first detections pass. This failure must remain visible.

## Cheap independent evidence checks

Only standard-library hashing and CSV consistency checks were run. Both packet inputs/analytic_source.py and the original pinned source have SHA-256 `4e26ed90c8ef7305699802c02490bb0cea0da26be49891c98d387b5210eb8f63`. The gate code hash and predictions hash match gate.json exactly. All 44,264 corners.csv rows were grouped into 16 cases: each integer sequence, tested count, first negative, and negative count agrees with corner_summary.json. The only finite corner threshold is (a=1/3,gamma=14) at m=208; all other positive-a corners are censored >3000. All a=0 corners remain nonnegative.

Reviewed immutable/base pins:

- PREDICTIONS.md SHA-256 `f9ee9a322f70e477825075916d481152c4bd52340450a5ce0af57ec370db498a`.
- Gate run code SHA-256 `882d17d55e99aa0e5718993f88974ca829e16f37d30b32e9a51c47ed072a3030`.
- gate.json SHA-256 `ac7998b40e3ef1789992b0441da4654cf30ea68f629f6fb6322508b603ad8481`.
- source_float.py SHA-256 `627579485355b2907fbb34c3ab91ca09ac067b84cc65aa163f5d36207bbe313e`.
- rayleigh_pinned.py SHA-256 `53fb9fea7f6d4fbdea51495bba71d60bb451f37acdc0c0f7173e6dd13adfb326`.
- corner_scan.py SHA-256 `ba0a3d2068ec724a54ce48ad31051d4df3d8a3f9b678f073de9c9b840b6f0e91`.
- corner_summary.json SHA-256 `d6e436699bc14f57dea11c1e7e8871c4f9c4618cde630f137cd1a59ee09fd419`.

The partial checkout's reported preregistration commit/push provenance remains parent-supplied; no Git-history certification is claimed by this reviewer. Existing source comparisons and gate results are numerical diagnostics, not certified enclosures or proof of positivity for all m.
