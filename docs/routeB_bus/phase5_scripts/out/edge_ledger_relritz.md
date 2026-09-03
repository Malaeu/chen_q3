# Edge ledger relative-Ritz columns (DESCRIPTIVE -- DIAGNOSTIC_NEVER_A_PROOF)

Generated: 2026-09-03 13:09:29 CEST
Judge source: `docs/routeB_bus/proshka/PROSHKA_VERDICT_GOAL058_CURVATURE_RELATIVE_RITZ_ADJUDICATION_2026-09-03.md` (CHEAPEST_NEXT_ACTION, section 3)

DESCRIPTIVE ONLY. No thresholds, no pass/fail verdicts on the physics are applied here (per the judge's explicit prohibition on post-hoc thresholds). The only boolean columns are the mathematical relation p <= eta the judge's own theorem states, computed two ways (midpoint float, and a certified arb-ball comparison), and elementary sanity checks (lambda1 > 0, g > 1) that flag a cell where the relative-Ritz denominator would be invalid. DIAGNOSTIC_NEVER_A_PROOF. No Lean. No route promotion. PX_RH_CLAIM: NOT_MADE.

## Trial-generator parametrizability finding

The k1/g04 trial generator (`portable_k_channel_v1.build_coeff_cache`, calling `true_precision_packet_gate_v1.build_prolate_model`/`integrate_coefficients`) accepts arbitrary (lambda_sq, N) in its public signature, but `true_precision_packet_gate_v1.py`'s module-level `MAX_DEGREE = 180` (the Legendre truncation degree of the angular prolate eigenproblem) is hard-coded and not scaled with lambda_sq. Measured relative truncation error at MAX_DEGREE=180 (double-precision numpy replica of the exact same Legendre-Galerkin matrix, compared against MAX_DEGREE up to 900):

| lambda_sq (=m) | c = 2*pi*m | measured relative truncation error at MAX_DEGREE=180 | faithful? |
|---|---|---|---|
| 13 | 81.6814 | ~0 (identical to >=400-degree reference at double-precision resolution) | YES |
| 23 | 144.513 | ~0 (identical to >=400-degree reference at double-precision resolution) | YES |
| 43 | 270.177 | ~4e-18 (at the double-precision noise floor) | YES |
| 83 | 521.504 | ~8.2e-9 (measured, real, not a rounding artifact: 8-9 correct digits) | NO -- TRIAL_GENERATOR_NOT_PARAMETRIZABLE |
| 163 | 1024.16 | ~4.9e-4 (measured, real: only 3-4 correct digits) | NO -- TRIAL_GENERATOR_NOT_PARAMETRIZABLE |

Cells (83,83) and (163,163) are therefore reported as TRIAL_GENERATOR_NOT_PARAMETRIZABLE (columns depending on q are `null`); cells at lambda_sq in {13, 23, 43} -- (13,13), (13,26), (23,23), (43,43), (43,86) -- use a freshly generated trial cache from the SAME unmodified generator (no substitute construction). One bonus row, (m=13, N=120), reuses the literal SHA-256-pinned Phase 1 trial file against a freshly built (13,120) CCM matrix, as an independent cross-check outside the ledger schedule.

## Main schedule + N-checks (best available precision per cell)

| m | N | role | dps | L=log(m) | lambda1 | lambda2 | g=lambda2/lambda1 | Rayleigh(q) | epsilon | eta | p=1-\|<xi,q>\|^2 | p<=eta (mid) | p<=eta (certified) | note |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| 13 | 13 | main_schedule | 240 | 2.56495 | 7.921036e-31 | 2.8421087e-25 | 358805.18 | 4.2260915e-16 | 5.3352762e+14 | 1.4869604e+09 | 0.0036630535 | True | True |  |
| 13 | 26 | n_check | 240 | 2.56495 | 4.9474786e-45 | 1.3330213e-38 | 2694344.7 | 2.5171092e-32 | 5.0876607e+12 | 1888274.6 | 0.00019233944 | True | True |  |
| 83 | 83 | main_schedule | 240 | 4.41884 | 3.2028568e-162 | 1.2556049e-154 | 39202655 | n/a | n/a | n/a | n/a | None | None | TRIAL_GENERATOR_NOT_PARAMETRIZABLE: test |
| 163 | 163 | main_schedule | 900 | 5.09375 | 2.399365e-294 | 8.6262447e-286 | 3.5952199e+08 | n/a | n/a | n/a | n/a | None | None | TRIAL_GENERATOR_NOT_PARAMETRIZABLE: test |

## Bonus row: (m=13, N=120), literal Phase 1 pinned trial, both precisions

| dps | L=log(13) | lambda1 | lambda2 | g | Rayleigh(q) | epsilon | eta | p | p<=eta (mid) | p<=eta (certified) | q_norm_sq-1 | eigen algo | elapsed_s |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| 120 | 2.56495 | 3.4839882e-59 | 1.3118543e-51 | 37653810 | 4.71998e-59 | 0.35476348 | 9.4217157e-09 | 4.6918825e-09 | True | True | -8.266e-140 | vdhoeven_mourrain | 5.78 |

DIAGNOSTIC_NEVER_A_PROOF. No Lean. No route promotion. PX_RH_CLAIM: NOT_MADE. This report contains no interpretation beyond the columns the judge's CHEAPEST_NEXT_ACTION named.
