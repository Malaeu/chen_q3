# Optimized step residuals and prime response

DIAGNOSTIC_NEVER_A_PROOF / CHALLENGER / NOT_RH.

The uniform-grid predictor is computed in increment coordinates. If `a` is the Levinson lag-predictor vector, the physical residual has bin values `[-reversed(a),1]`. Thus it equals 1 on the terminal bin and is optimized against the entire preceding sampled history. Its autocorrelation is evaluated exactly for the piecewise constant profile by linear interpolation between discrete autocorrelation sums. All source arithmetic atoms through the finite support are retained; DH includes non-prime powers and signed coefficients.

`residual.py` uses mpmath at 90 digits. `budgets.csv` contains the arch, constant, both poles, arithmetic, and planted terms separately, alongside direct Toeplitz replay. `prime_correlations.csv` records Q at every active prime power; its reference weights are the zeta Lambda/sqrt(n), explicitly so named, even on the DH control profiles. `profiles.csv` contains every bin value. `gradient.csv` independently perturbs one arithmetic coefficient and reoptimizes. `shape.py` produces float64 summaries of the saved high-precision profiles. `arch_validate.py` directly integrates the physical arch form on three saved profiles and includes its infinite tail.

After a past block becomes indefinite, its stationary coefficient vector is still algebraically computable, but the variational infimum is -infinity. Such rows are labelled with nonzero `past_negative_index`. They are not positive prediction variances or minimizing residuals.

`hinges.py` fixes the old mesh history strictly below each non-grid prime threshold and varies only the target time. Sigma itself is continuous. The measured one-sided derivative difference is compared to `2 c_n beta_first` in increment coordinates, equivalently `-2 c_n+2 c_n sum(a_i)` in anchored point coordinates. This is a temporal derivative jump, whereas the arithmetic-coefficient derivative is `-Q(log n)`. The two are not interchangeable. Nearby shifted arithmetic hinges are excluded by choosing epsilon below one tenth of their distance; Richardson extrapolation uses epsilon and epsilon/2.

Hinge source evaluations and differences use mpmath at 80 digits; Toeplitz predictor solves use float64, with nine independent mpmath80 predictor checks. The long printed decimals in hinge CSVs do not certify that many accurate digits. `finish_hinges.py` attaches precision and signed-index labels and produces the summary.

Run from a checkout with the previously committed `suzuki_W_2026-11-02/prediction/scan.py` and its `dh_matrix.py` dependency:

```sh
uv run --with mpmath --with numpy --with scipy python residual.py
python shape.py
uv run --with mpmath --with numpy --with scipy python arch_validate.py
uv run --with mpmath --with numpy --with scipy python hinges.py
uv run --with mpmath --with numpy --with scipy python hinges.py --repair-near-grid
uv run --with mpmath --with numpy --with scipy python finish_hinges.py
```

See PREREGISTRATION.md and CARD_EULER_CONE.md. No source-sign estimate, continuum limit, or RH claim follows from these finite computations.

The first hinge table is retained as `hinges_initial.csv`. Its maximum absolute FD discrepancy was 1.25642e-4 at log163, which lies only about 2.00807e-7 above a mesh32 point. The original epsilon=gap/10 was too large relative to the archimedean cusp. A deterministic quality-triggered repair (`--repair-near-grid`) re-evaluates only rows with absolute FD discrepancy above 1e-8, using epsilon=min(1e-8,gap/10000,nearest_other_hinge_distance/100). This preserves the complete original data and controls the approach to the cusp instead of treating the discrepancy as arithmetic evidence. The repair is validation of the registered identity, not a new selected hypothesis.
