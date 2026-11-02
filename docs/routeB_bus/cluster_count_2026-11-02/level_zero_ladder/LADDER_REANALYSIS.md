# Reversed lifted-level / own-zero re-analysis

Source: `Malaeu/chen_q3@9c6fa2a8032f5ab78993b8c1784ea122f22cd4a0`. DIAGNOSTIC_NEVER_A_PROOF. Saved eigenvectors only; no eigenproblem, matrix rebuild, or new Fourier-root search.

Lifted means the existing B=2 convention lambda_i >= m^(-2), with zero-based i. For every positive zeta ordinate below 1.5 Omega, use delta_k = half the smaller adjacent positive-zero gap (first uses its next gap), from the pinned zeros.csv. An own zero means rho > 0.1; this denotes nonvanishing under the requested tolerance, not an exact zero assertion.

The direct sinc transform is used. Each local maximum was located from a 128-panel scan with bounded scalar optimization; numerator and candidate maximum were reevaluated at 70 decimal digits, refining interior stationary maxima. All 1,179 classifications agree with the initial double-precision pass. This is floating numerical validation, not a certified global extremum enclosure.

| m | Lifted i | Zeros tested | Omega | Reversed pairs on own edges | Best possible own-edge bijection | Same pairs as secondary max-rho bijection |
|---:|---|---:|---:|---:|---:|---:|
| 16 | 10–16 | 11 | 36.2588811346 | 7/7 | 7/7 | 3/7 |
| 24 | 14–24 | 17 | 47.4493055883 | 11/11 | 11/11 | 0/11 |
| 32 | 18–32 | 23 | 58.0142098154 | 15/15 | 15/15 | 2/15 |
| 40 | 22–40 | 30 | 68.1310992711 | 19/19 | 19/19 | 1/19 |

The reversed pairs are i=m+1-k, k=1,...,q. They attain the optimal binary score for every m. There are many admissible own-zero bijections; the criterion does not uniquely recover the reverse order. The last column uses an explicitly stronger tie-break: among perfect own-edge matchings to the first q zeros, maximize sum rho. It is a fitted comparison, not a rejection of the binary optimum. Allowing selection among all tested zeros also gives q/q own edges.

The first-q comparison is stated explicitly: q is the number of lifted levels, not the number of zeros below Omega. The nearest-to-Omega endpoint is a different convention and cannot supply a square bijection of all q levels.

| m | q | gamma_q / Omega | Zero nearest Omega |
|---:|---:|---:|---|
| 16 | 7 | 1.12851577 | gamma_6 = 37.5861781588 |
| 24 | 11 | 1.11635609 | gamma_9 = 48.0051508812 |
| 32 | 15 | 1.12235510 | gamma_13 = 59.3470440026 |
| 40 | 19 | 1.11116203 | gamma_16 = 67.0798105295 |

## m=16: own-zero indices k

All k below refer to gamma_k; tested k=1,...,11.

| Level i | Own k (rho > 0.1) |
|---:|---|
| 10 | 4, 6–11 |
| 11 | 1–3, 5–11 |
| 12 | 1–11 |
| 13 | 1–11 |
| 14 | 1–11 |
| 15 | 1–11 |
| 16 | 1–5, 7–11 |

| Reversed i | k | rho |
|---:|---:|---:|
| 16 | 1 | 0.8923477088 |
| 15 | 2 | 0.9883080824 |
| 14 | 3 | 0.6144083686 |
| 13 | 4 | 0.6533856318 |
| 12 | 5 | 0.5184220298 |
| 11 | 6 | 0.6970406159 |
| 10 | 7 | 0.1507683682 |

## m=24: own-zero indices k

All k below refer to gamma_k; tested k=1,...,17.

| Level i | Own k (rho > 0.1) |
|---:|---|
| 14 | 10–12, 14–17 |
| 15 | 1, 6, 9–12, 14–17 |
| 16 | 1–12, 14–17 |
| 17 | 1–12, 14–17 |
| 18 | 1–12, 14–17 |
| 19 | 1–12, 14–17 |
| 20 | 1–12, 14–17 |
| 21 | 1–12, 14–17 |
| 22 | 1–12, 14–17 |
| 23 | 1–12, 14–17 |
| 24 | 1–2, 4–12, 14–17 |

| Reversed i | k | rho |
|---:|---:|---:|
| 24 | 1 | 0.9999944965 |
| 23 | 2 | 0.3299262349 |
| 22 | 3 | 0.9627951550 |
| 21 | 4 | 0.9612866260 |
| 20 | 5 | 0.9789864819 |
| 19 | 6 | 0.8523519001 |
| 18 | 7 | 0.6903636988 |
| 17 | 8 | 0.7550983548 |
| 16 | 9 | 0.8383456833 |
| 15 | 10 | 0.4767092253 |
| 14 | 11 | 0.5498453258 |

## m=32: own-zero indices k

All k below refer to gamma_k; tested k=1,...,23.

| Level i | Own k (rho > 0.1) |
|---:|---|
| 18 | 13–15, 17–23 |
| 19 | 9, 13–15, 17–23 |
| 20 | 1, 3–6, 8–15, 17–23 |
| 21 | 1–15, 17–23 |
| 22 | 1–15, 17–23 |
| 23 | 1–15, 17–23 |
| 24 | 1–15, 17–23 |
| 25 | 1–4, 6–15, 17–23 |
| 26 | 1–15, 17–23 |
| 27 | 1–15, 17–23 |
| 28 | 1–15, 17–23 |
| 29 | 1–15, 17–23 |
| 30 | 1–15, 17–23 |
| 31 | 1–15, 17–23 |
| 32 | 1–15, 17–23 |

| Reversed i | k | rho |
|---:|---:|---:|
| 32 | 1 | 0.9359868251 |
| 31 | 2 | 0.9920164279 |
| 30 | 3 | 0.9935159921 |
| 29 | 4 | 0.6134101625 |
| 28 | 5 | 0.9077601775 |
| 27 | 6 | 0.9769664174 |
| 26 | 7 | 0.6386266583 |
| 25 | 8 | 0.9656914494 |
| 24 | 9 | 0.5111251354 |
| 23 | 10 | 0.9915370155 |
| 22 | 11 | 0.9779729851 |
| 21 | 12 | 0.8986812802 |
| 20 | 13 | 0.4349977451 |
| 19 | 14 | 0.8164918523 |
| 18 | 15 | 0.2502007683 |

## m=40: own-zero indices k

All k below refer to gamma_k; tested k=1,...,30.

| Level i | Own k (rho > 0.1) |
|---:|---|
| 22 | 17–28, 30 |
| 23 | 17–28, 30 |
| 24 | 1–2, 4–7, 9–15, 17–28, 30 |
| 25 | 1–5, 7–28, 30 |
| 26 | 1–28, 30 |
| 27 | 1–28, 30 |
| 28 | 1–16, 18–28, 30 |
| 29 | 1–28, 30 |
| 30 | 1–13, 15–28, 30 |
| 31 | 1–16, 18–28, 30 |
| 32 | 1–16, 18–28, 30 |
| 33 | 1–16, 18–28, 30 |
| 34 | 1–28, 30 |
| 35 | 1–28, 30 |
| 36 | 1–28, 30 |
| 37 | 1–28, 30 |
| 38 | 1–28, 30 |
| 39 | 1–28, 30 |
| 40 | 1–28, 30 |

| Reversed i | k | rho |
|---:|---:|---:|
| 40 | 1 | 0.9416805158 |
| 39 | 2 | 0.9683672883 |
| 38 | 3 | 0.9976023723 |
| 37 | 4 | 0.9769397675 |
| 36 | 5 | 0.9713039153 |
| 35 | 6 | 0.9729713197 |
| 34 | 7 | 0.9848953651 |
| 33 | 8 | 0.8068876427 |
| 32 | 9 | 0.8671687554 |
| 31 | 10 | 0.5210454306 |
| 30 | 11 | 0.9306805296 |
| 29 | 12 | 0.9297200493 |
| 28 | 13 | 0.4554554646 |
| 27 | 14 | 0.7818044847 |
| 26 | 15 | 0.7524865044 |
| 25 | 16 | 0.7198546953 |
| 24 | 17 | 0.2723349304 |
| 23 | 18 | 0.5002094740 |
| 22 | 19 | 0.9863899632 |

## m=40, i=22: correction to the two-missed-zero premise

Among the first 19 zeros, the vector has rho <= 0.1 at k=1,...,16, and rho > 0.1 at THREE zeros:

| k | gamma_k | rho | gamma_k / Omega | gamma_k - Omega |
|---:|---:|---:|---:|---:|
| 17 | 69.546401711174 | 0.111677367720 | 1.020773222 | 1.415302440 |
| 18 | 72.067157674482 | 0.692188919092 | 1.057771832 | 3.936058403 |
| 19 | 75.704690699084 | 0.986389963214 | 1.111162032 | 7.573591428 |

All three lie above Omega = 68.131099271053. Gamma_17 is just above the requested 0.1 threshold, at rho = 0.111677367720262208..., so it cannot be discarded. Gamma_16 = 67.079810529494 is the nearest zero to Omega and has rho = 0.00447063875963. A previous count of two based on root proximity is not the result of this local-normalized amplitude criterion.

Full per-pair numerators, denominators, peak locations, and 70-digit rho values: `ladder_rho_validated.csv`. Reproduction: `reanalyse.py`, `validate_rho.py`, the four source cell JSON files and `zeros.csv`.
