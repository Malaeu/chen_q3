# Literal zeta EVEN builder — diagnostic only

CHALLENGER_NOT_RH. DIAGNOSTIC_NEVER_A_PROOF. No route state change, zero-side Gram, eigenvalue clipping, or positive-semidefinite assumption is used.

`source_float.build(m)` returns `(A, meta)`, where A is the unplanted float64 `(m+1) x (m+1)` zeta EVEN matrix in the pinned physical basis with indices `0..m`. `source_float.corner(m)` returns the same unplanted A[0,0] without assembling A and caches integer results. No legacy plant or DH world enters either API. Run with `OPENBLAS_NUM_THREADS=2 OMP_NUM_THREADS=2`.

Source: `../../ground_state_zeros_2026-11-03/inputs/analytic_source.py`, Git blob `27bbaabbc5938b3157b5bc20f5e6db2f882122c0`, SHA256 `4e26ed90c8ef7305699802c02490bb0cea0da26be49891c98d387b5210eb8f63`. Both identities were recomputed from actual bytes. The source is unchanged. Every prime power k<m is retained. The alpha=1/2 archimedean branch, its direct special n=0 diagonal, geometric endpoint correction, analytic tail, and rank-one even pole all follow the source. Endpoint series are cut at the source's 256-bit cutoff 2^-304, below float64 resolution. Complex trigamma uses recurrence and a ten-term Bernoulli asymptotic; the maximum sampled discrepancy against fresh 280-bit FLINT complex trigamma was 3.56e-15.

The first pure float64 version failed the fixed unplanted floor at m=1000 and m=3000: -1.62e-12 and -6.64e-12. Its source is retained as `source_float64_initial.py` and failed reports have `initial_float64_` names and must not be used for scoring. The promoted builder computes prime phases, weights, and reductions in `np.longdouble`, with 64 mantissa bits on this platform, then rounds moments and the matrix to float64. This is precision promotion in the arithmetic, with no spectral adjustment. A platform whose longdouble equals float64 needs another precision implementation and must revalidate; the `float128` NumPy dtype label here does not mean a 113-bit mantissa.

Fresh unchanged source executions at 256 bits (about77 decimal digits; MPFR working296 bits and FLINT328 bits) compared to the final builder:

|m|max entry error|operator error|float64 lambda_min(A)|
|---:|---:|---:|---:|
|80|4.20e-15|4.25e-15|-2.57e-15|
|160|2.95e-15|2.98e-15|-3.75e-15|
|300|4.45e-15|4.47e-15|-5.00e-15|

Final source comparisons and benchmark details are in `validation_report.json`; `validate_builder.py` reproduces them and does no planting. The m80 source comparison passed before any benchmark. Benchmarks then followed m300, m1000, m3000 in that order. Final measured wall seconds (shared host, BLAS2):

|m|assembly|smallest eigenvalue|unplanted lambda_min|
|---:|---:|---:|---:|
|300|0.014|0.012|-5.00e-15|
|1000|0.750|0.207|-1.02e-14|
|3000|2.752|2.856|-1.41e-14|

Peak RSS was313.3MiB. Final comparison plus benchmark pass used14.54 CPU seconds. The initial failed pass used26.76 CPU seconds; helper validation used5.49 CPU seconds. A repeated promoted development pass and initial m80 check add roughly15 CPU seconds; the aggregate numerical work stayed below the initial180 CPU second allocation. Full repeated consecutive dense scans near3000 remain expensive despite a feasible individual cell.

`helper_validation.json` records exact float64 agreement of the scalar corner API with A[0,0] at16,80,160,300 and a five-second unplanted scalar scan over all2985 integers16..3000. The helper's fresh 256-bit pinned source Rayleigh evaluation was checked at m80 with e0.

`rayleigh_pinned.evaluate(m, fixed_float_vector, a=Fraction(1,3), gamma=800, bits=256)` freshly executes the unchanged pinned source, promotes the exact binary64 vector, and adds the prescribed Q analytically in MPFR. A rational string `'1/3'` is also accepted. The default full-source cap is1000; changing it is an explicit budget choice. This returns a fixed-vector Rayleigh witness, not a high-precision eigenvalue ordering computation or an interval certificate. Its planted branch has not been executed in this specialist lane; the independent Q gate and first-trigger confirmation belong to the parent.

Versions: Python3.12.14, NumPy2.3.5, SciPy1.17.0, gmpy2 2.3.2, python-flint0.9.0. Every final build reports its code SHA256 and source pins in metadata. No planted runs were performed here. The parent must still test the unplanted floor and a=0 controls at every actual matrix-grid cell.
