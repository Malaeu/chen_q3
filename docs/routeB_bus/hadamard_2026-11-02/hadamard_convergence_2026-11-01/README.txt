Hadamard N-convergence diagnostic, 2026-11-01

Literal matrix_K source family, even block, L=log(m), m=8,12,16.
Requested N: 8,12,16,20,24,28,32,40. Auxiliary N=36,44 supply N+4 ratios.
100 decimal digits, composite eight-panel Gauss-Legendre order96.
Validation independently recomputes all matrices/eigenvalues at140digits/order128.
Maximum relative eigenvalue discrepancy:1.0703355007671339e-37.

NO requested N reaches |lambda_N/lambda_(N+4)-1|<=1e-3 at ANY anchor.
At N40 those ratios are1.04535113927,12.9445061669,395.067059622.
No converged-N scan is warranted from this range. This is not a precision-floor failure.
All sampled eigenvalues positive and decrease in N. No interval certification.

The support-nesting min-max statement concerns the full support-constrained
variational infimum (with its form domain). Fixed finite Fourier carriers at
different L are not nested. Since N convergence fails here, observed positive
fixed-N derivatives cannot be called violations of that full-space statement.
Nor would a successive-value 1e-3 check alone certify derivative convergence.

Files:
convergence.py: literal source entries and compressed eigensolves.
convergence_dps100_gl96.json: full primary results and residuals.
convergence_dps140_gl128.json: independent precision/quadrature replay.
convergence_results.csv/json: consolidated values, ratios, precision comparisons.
summary.json: machine-readable result.
derivatives.py/anchor_derivatives.json: auxiliary N40/44 one-sided HF slopes.

Replay:
UV_CACHE_DIR=/tmp/rh-uv-cache uv run --with mpmath convergence.py 96 100
UV_CACHE_DIR=/tmp/rh-uv-cache uv run --with mpmath convergence.py 128 140
UV_CACHE_DIR=/tmp/rh-uv-cache uv run --with mpmath finalize.py
UV_CACHE_DIR=/tmp/rh-uv-cache uv run --with mpmath derivatives.py 96 100
