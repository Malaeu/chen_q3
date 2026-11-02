# Route B exploration cards

**DIAGNOSTIC_NEVER_A_PROOF. CHALLENGER / NOT_RH.** Predictions and kill switches were recorded before each new calculation. These finite experiments do not provide a cofinal bound.

## Card E: centered divisor transfer

**HYPOTHESIS:** on the literal zeta complement at κ=1.1, the ratio λmax(Gtilde|Jperp)/||q|Jperp|| grows proportionally to L and its maximizing vector peaks in the middle of the frequency band. The pinned preflight defines the centered operator in §7; §4 concerns a different uncentered test.

**Evidence:** all Λ(d), the lower continuum endpoint0 and the full output line are retained. The denominator is the operator norm, not q evaluated on the maximizing vector. With Ω=2πm/log m:

|m|ratio|ratio/L|physical Fourier peak t*|t*/Ω|
|---:|---:|---:|---:|---:|
|20|0.703273|0.234758|37.327106|0.889851|
|40|1.804438|0.489156|64.077357|0.940501|
|60|3.722057|0.909073|90.659203|0.984612|
|80|4.681407|1.068320|109.050046|0.950673|
|120|4.557159|0.951889|154.551045|0.981339|

**What kills it:** the middle-band prediction fails on every sampled cell. A stable proportional-to-L law over the complete requested range is not established; the last three ratio/L values alone are not an asymptotic result. The implementation survived an independent direct physical-output norm check, including its nonzero tail, the N=1 norm identity, positivity checks and a100-to160dps recomputation.

**What to give Proshka:** the literal centered form is now computable without an omitted output tail. In these cells the top direction is near the upper modal edge, not in the middle. Any proposed centered-transfer obstruction must address that direction and its full q energy. See `centered_divisor/RESULT.md`, `results.csv`, compact vectors and replay code. No boundedness or divergence theorem is inferred.

## Card F: non-prime-power arithmetic burden

**HYPOTHESIS:** DH's non-prime-power sector is a source-specific burden that distinguishes the required matched DH80 and DH120 cases; its deletion removes the negative120 complements when the carrier and complement are held fixed.

**Evidence:** on the original complement minimizers, the net non-prime-power arithmetic divided by original arch energy is0.428145 at DH80 q41 and0.943282/0.944419 at DH120 q63/q65. It is identically0 for zeta by Euler support. This uses signed evaluated terms, not absolute coefficients or capacity. Both coefficient-sign groups contribute harmful net loading at120.

The0.75 separator is retrospective calibration, explicitly not held-out validation. A separately preregistered new intervention removed only this arithmetic sector and recomputed the entire minimum on the unchanged complement:

|case|original minimum|minimum after NPP deletion|
|---|---:|---:|
|DH80 q41|+0.654360|+1.680222|
|DH120 q63|−1.547784|+1.708817|
|DH120 q65|−1.557015|+1.708801|

**What kills it:** a universal0.75 sign threshold is already falsified by the native DH55/80 controls. The intervention's specific sign-removal prediction passed, but the altered source is not asserted to retain a functional equation, zero set or quiet residual. This is not an Euler-function homotopy. The saved zero censuses and80dps altered eigensolves remain diagnostic.

**What to give Proshka:** a concrete mechanism check separates the obligatory density-matched positive80 and negative120 cases without using σmin. The additional harmful DH loading is concentrated at log(n)/log(m)≥1/2. Zeta lacks this sector altogether, so this does not supply its missing prime-block upper bound. Full sign/location splits, native controls, intervention code and falsifier are in `discriminator/RESULT.md`.

No further scan was used to tune either failed geometry prediction or the retrospective ratio threshold.

Reproduction prerequisite on a fresh checkout: run `python3 docs/routeB_bus/fake_worlds_2026-11-02/ledger_diff/unpack_cells.py` from the repository root (Python3.12+). It verifies and restores the previously committed lossless matched-cell archive. Then use the replay commands in each experiment's RESULT.md. No unpublished dense matrix is required.
