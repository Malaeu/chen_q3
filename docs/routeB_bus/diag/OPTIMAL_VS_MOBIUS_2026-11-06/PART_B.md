# Part B — t-side zero localization

## Definitions and source convention

For each N in {500, 1000, 2000, 5000}, coefficients were loaded directly from the pinned archived `part_a_coefficients.csv` Git object (commit `ba5654b46adf84159702748b006699bafa0ed89b`, blob `7baa38bc0f5a9437e985f739aecb823ec2dedf1a`). The physical free coefficients are `c_opt = -stored_c` for n=2..N. The comparator is `a_n = mu(n) log(N/n)/log N`, also for n=2..N.

Both polynomials use the preregistered centering `D(s) = sum c_n (n^(-s) - 1/n)`, which gives `D(1)=0`. The intensity is `I_D(t)=|1-zeta(1/2+it)D(1/2+it)|^2`, and `Delta(t)=I_a(t)-I_opt(t)`. Positive W_j therefore means the taper has larger local squared error than the optimum.

## Zero cells, grid, and quadrature

mpmath was run at 20 decimal digits. The script found 649 positive zero ordinates at or below 1000 and computed one following zero for the last local gap. The unique sorted grid has 167937 points at the final refinement. Each zero cell uses midpoint boundaries, with the first cell starting at 0 and the final included cell ending at 1000; the first left half-cell is additionally split at t=1. The first minimum gap uses only its next gap. The local minimum gap for later zeros is the minimum of the preceding and following gaps.

Each half-cell initially used nested composite Simpson rules with 16 and 32 subdivisions. To resolve the unusually wide first left half-cell, t=0..1 is split explicitly and the rest of that half-cell is split into segments of width at most 1 before Simpson integration. Material discrepancy was pre-defined as a scaled absolute difference above 1e-06 for a weighted head (difference divided by max(1, |fine head|)), a scaled absolute difference above 1e-06 for a W_j (difference divided by max(1, max|W|)), or an absolute Spearman change above 0.001; the segmented grid is refined uniformly to 64 and, if needed, 128 subdivisions. The final measured convergence summary is `{"compared_intervals": [64, 128], "converged": true, "head_scaled_abs_max": 1.8897521629132608e-09, "local_spearman_abs_max": 0.0, "local_w_max_difference": {"N": 5000, "scaled_abs": 7.458728023580774e-07, "zero_index": 2}, "local_w_scaled_abs_max": 7.458728023580774e-07, "max_refinement_reached": false}`.

Zeta values were evaluated directly with `mpmath.zeta` at every unique grid point; the finite Dirichlet polynomials were evaluated in complex128. The quadrature and double-precision polynomial values are numerical diagnostics, not interval-certified enclosures.

## J3 — continuous head

R7 B §2 gives the exact Mellin–Parseval identity for the full-line norm of the centered residual. By conjugation symmetry, the computed one-sided head is `(1/pi) integral_0^1000 I_D(t)/(1/4+t^2) dt`. Values below are truncated heads only. The exact identity is not a claim that the finite head equals the complete norm; a separately derived tail bound is required, and the difference between a discrete norm and this head was not used as a tail estimate.

| N | D | Simpson 16 | Simpson 32 | final refinement |
|---:|:---|---:|---:|---:|
| 500 | optimal | 0.00711751077386 | 0.00711738541562 | 0.00711737767746 |
| 500 | Mobius taper | 0.0406597391816 | 0.0406596832619 | 0.0406596798639 |
| 1000 | optimal | 0.00628616825762 | 0.00628598346456 | 0.00628597256039 |
| 1000 | Mobius taper | 0.0338547888286 | 0.0338547158897 | 0.0338547116827 |
| 2000 | optimal | 0.005876370186 | 0.00587611534627 | 0.00587610104009 |
| 2000 | Mobius taper | 0.0283273521552 | 0.0283272972702 | 0.0283272937454 |
| 5000 | optimal | 0.00509690977505 | 0.00509627084235 | 0.00509623718782 |
| 5000 | Mobius taper | 0.0231445326416 | 0.0231444137525 | 0.0231444070125 |

The independently derived J3 tail bound is tracked outside this Part B computation and must be merged before treating these as full-line norm enclosures. No RH conclusion follows from this finite numerical head.

Sanity checks: `D(1)=0` by the centering identity (the code's maximum termwise residual is 0.0e+00); measured `max |Delta(gamma_j)| = 0.000e+00` on the zero-ordinate grid.

## J4 — zero-label permutation null

For each N, the observed Spearman correlations use W_j against `1/|zeta'(rho_j)|^2` and against the raw local minimum gap. The two-sided empirical permutation p-value is `(1 + count(|rho_perm| >= |rho_obs|))/1001`. The 1000 permutations use NumPy `default_rng(20261106)` and the same label permutations for both predictors and all N. A correlation within the central 95% null band is not evidence.

| N | variable | rho | null 95% | p |
|---:|:---|---:|:---:|---:|
| 500 | inverse_derivative_squared | 0.166122 | [-0.080845, 0.080838] | 0.000999 |
| 500 | raw_local_min_gap | 0.011285 | [-0.081871, 0.080291] | 0.7772 |
| 1000 | inverse_derivative_squared | 0.034011 | [-0.080281, 0.075014] | 0.4126 |
| 1000 | raw_local_min_gap | 0.084235 | [-0.081472, 0.076087] | 0.03297 |
| 2000 | inverse_derivative_squared | -0.041543 | [-0.073257, 0.075928] | 0.3227 |
| 2000 | raw_local_min_gap | 0.045885 | [-0.081347, 0.075131] | 0.2348 |
| 5000 | inverse_derivative_squared | -0.063990 | [-0.072670, 0.074418] | 0.1059 |
| 5000 | raw_local_min_gap | 0.040398 | [-0.078994, 0.078448] | 0.2987 |


The preregistered inverse-gap correlation is reported separately as descriptive secondary output. Since every local gap is positive and the reciprocal is a strictly decreasing transform, its Spearman rho is the negative of the raw-gap rho; no additional hypothesis test or p-value is attached.

| N | secondary variable | rho |
|---:|:---|---:|
| 500 | inverse local minimum gap | -0.011285 |
| 1000 | inverse local minimum gap | -0.084235 |
| 2000 | inverse local minimum gap | -0.045885 |
| 5000 | inverse local minimum gap | -0.040398 |

## Preregistered Part B prediction scores

- Q5: MISS — at N=5000, rho(W, 1/|zeta prime|^2)=-0.063990, p=0.1059; the preregistered thresholds were rho>=0.3 and p<0.01.
- Q6: MISS — at N=5000, raw-gap rho=0.040398 versus Q5 rho=-0.063990, p=0.2987; same nonzero sign and p<0.01 were required.
## Largest local improvements

### N=500

| rank W | zero j | gamma | W_j | abs zeta prime | previous gap | next gap | local min gap | rank inverse abs zeta prime |
|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| 1 | 1 | 14.134725142 | 0.315750033 | 0.793160433 | — | 6.8873145 | 6.8873145 | 1 |
| 2 | 528 | 847.971717640 | 0.250720665 | 2.03420261 | 1.7769477 | 0.51756354 | 0.51756354 | 102 |
| 3 | 388 | 664.244604652 | 0.2191788098 | 4.73406705 | 1.9480182 | 1.0981584 | 1.0981584 | 493 |
| 4 | 237 | 451.403308445 | 0.2158329982 | 5.24906307 | 1.2763627 | 2.5834294 | 1.2763627 | 534 |
| 5 | 116 | 263.573893905 | 0.2065931346 | 6.06340237 | 2.7688094 | 1.9839579 | 1.9839579 | 574 |
| 6 | 301 | 544.323890101 | 0.2055536892 | 7.01028116 | 2.476453 | 1.3129431 | 1.3129431 | 612 |
| 7 | 309 | 555.792020562 | 0.1996521786 | 3.78563867 | 2.0270484 | 1.1074558 | 1.1074558 | 392 |
| 8 | 645 | 994.404590571 | 0.1964926924 | 5.23914805 | 1.1900096 | 1.8007456 | 1.1900096 | 533 |
| 9 | 475 | 779.157076949 | 0.1629779658 | 7.19970167 | 1.8573284 | 1.1918481 | 1.1918481 | 617 |
| 10 | 540 | 863.189719772 | 0.1424046881 | 6.35806361 | 2.0186216 | 1.1511042 | 1.1511042 | 596 |
| 11 | 161 | 336.841850428 | 0.1380649368 | 5.48108631 | 2.6304956 | 1.4981424 | 1.4981424 | 546 |
| 12 | 477 | 782.137664391 | 0.1371799008 | 2.18918155 | 1.7887394 | 0.46027956 | 0.46027956 | 133 |
| 13 | 608 | 948.346646255 | 0.1231524884 | 4.60244032 | 1.2674632 | 1.8049664 | 1.2674632 | 482 |
| 14 | 565 | 894.886292321 | 0.1196344199 | 2.21084638 | 1.7671748 | 0.51162735 | 0.51162735 | 136 |
| 15 | 229 | 439.918442214 | 0.1187901768 | 3.50632893 | 1.2967036 | 1.764757 | 1.2967036 | 355 |
| 16 | 300 | 541.847437121 | 0.1177362411 | 4.47983995 | 1.2160469 | 2.476453 | 1.2160469 | 470 |
| 17 | 478 | 782.597943946 | 0.1118358032 | 2.08839153 | 0.46027956 | 1.6908787 | 0.46027956 | 106 |
| 18 | 265 | 493.314441582 | 0.1107859839 | 2.03255455 | 1.91562 | 0.64355622 | 0.64355622 | 101 |
| 19 | 186 | 375.825912767 | 0.1100453875 | 1.42675144 | 1.9610389 | 0.49817946 | 0.49817946 | 21 |
| 20 | 435 | 727.056403230 | 0.1095855841 | 6.18974935 | 2.4937893 | 1.3490784 | 1.3490784 | 585 |

### N=1000

| rank W | zero j | gamma | W_j | abs zeta prime | previous gap | next gap | local min gap | rank inverse abs zeta prime |
|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| 1 | 510 | 824.526293872 | 0.3230242444 | 9.27088234 | 2.3285364 | 1.5129935 | 1.5129935 | 645 |
| 2 | 379 | 650.668683891 | 0.3000037682 | 2.41994928 | 0.47116455 | 2.9808877 | 0.47116455 | 178 |
| 3 | 1 | 14.134725142 | 0.2394457847 | 0.793160433 | — | 6.8873145 | 6.8873145 | 1 |
| 4 | 321 | 572.419984132 | 0.2245670728 | 6.24062289 | 2.3688693 | 1.1946264 | 1.1946264 | 590 |
| 5 | 486 | 792.888652563 | 0.2182301508 | 1.64513872 | 0.46094495 | 1.5951393 | 0.46094495 | 52 |
| 6 | 528 | 847.971717640 | 0.1879757955 | 2.03420261 | 1.7769477 | 0.51756354 | 0.51756354 | 102 |
| 7 | 452 | 748.242754465 | 0.1753107015 | 2.28263988 | 0.56819084 | 2.4131959 | 0.56819084 | 147 |
| 8 | 640 | 988.992622371 | 0.173359311 | 8.70058761 | 2.236614 | 1.2312954 | 1.2312954 | 643 |
| 9 | 488 | 795.606596156 | 0.1689489333 | 5.54016604 | 1.1228043 | 1.6568739 | 1.1228043 | 553 |
| 10 | 477 | 782.137664391 | 0.1686585615 | 2.18918155 | 1.7887394 | 0.46027956 | 0.46027956 | 133 |
| 11 | 496 | 805.861635667 | 0.1571891369 | 7.38184987 | 1.0993966 | 2.2901793 | 1.0993966 | 620 |
| 12 | 166 | 344.661702940 | 0.1429872876 | 6.19876608 | 2.6068254 | 1.6861676 | 1.6861676 | 587 |
| 13 | 172 | 353.488900489 | 0.1391352588 | 6.39183182 | 1.6102515 | 2.5286745 | 1.6102515 | 597 |
| 14 | 79 | 198.015309676 | 0.1305787379 | 3.15790516 | 1.1388278 | 3.2494423 | 1.1388278 | 304 |
| 15 | 298 | 540.213166376 | 0.1283999386 | 1.19656995 | 1.7846402 | 0.41822387 | 0.41822387 | 9 |
| 16 | 137 | 297.979277062 | 0.1274096777 | 5.86614139 | 2.4060222 | 1.861049 | 1.861049 | 568 |
| 17 | 482 | 787.468463816 | 0.1266940511 | 5.50870603 | 1.0073164 | 2.5906285 | 1.0073164 | 550 |
| 18 | 281 | 515.435057167 | 0.1228902193 | 7.29403849 | 1.7660716 | 2.1546114 | 1.7660716 | 618 |
| 19 | 518 | 834.651915148 | 0.1214133653 | 9.6840472 | 1.6482742 | 2.041661 | 1.6482742 | 648 |
| 20 | 388 | 664.244604652 | 0.1199909807 | 4.73406705 | 1.9480182 | 1.0981584 | 1.0981584 | 493 |

### N=2000

| rank W | zero j | gamma | W_j | abs zeta prime | previous gap | next gap | local min gap | rank inverse abs zeta prime |
|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| 1 | 618 | 961.669572474 | 0.2775079152 | 9.07484931 | 2.2104037 | 1.5125142 | 1.5125142 | 644 |
| 2 | 317 | 566.698787683 | 0.2656602793 | 3.58629414 | 2.1927317 | 1.0329702 | 1.0329702 | 371 |
| 3 | 1 | 14.134725142 | 0.2093814952 | 0.793160433 | — | 6.8873145 | 6.8873145 | 1 |
| 4 | 314 | 562.559207616 | 0.1837556831 | 6.7792539 | 2.3184001 | 1.6016715 | 1.6016715 | 606 |
| 5 | 604 | 944.188035810 | 0.1747706332 | 7.51300209 | 2.1356942 | 1.1455267 | 1.1455267 | 624 |
| 6 | 213 | 415.455214996 | 0.1568200793 | 1.91610197 | 0.43640524 | 2.9324908 | 0.43640524 | 85 |
| 7 | 289 | 527.903641601 | 0.1558284237 | 2.17987275 | 2.8262559 | 0.50257225 | 0.50257225 | 129 |
| 8 | 486 | 792.888652563 | 0.1445880761 | 1.64513872 | 0.46094495 | 1.5951393 | 0.46094495 | 52 |
| 9 | 603 | 942.052341643 | 0.1363936156 | 6.279279 | 0.895342 | 2.1356942 | 0.895342 | 592 |
| 10 | 496 | 805.861635667 | 0.1359578787 | 7.38184987 | 1.0993966 | 2.2901793 | 1.0993966 | 620 |
| 11 | 288 | 525.077385687 | 0.1313703916 | 6.08007365 | 1.1168548 | 2.8262559 | 1.1168548 | 576 |
| 12 | 619 | 963.182086671 | 0.1290591336 | 1.77370155 | 1.5125142 | 0.38495352 | 0.38495352 | 63 |
| 13 | 379 | 650.668683891 | 0.1284812098 | 2.41994928 | 0.47116455 | 2.9808877 | 0.47116455 | 178 |
| 14 | 558 | 885.272304480 | 0.1279510779 | 4.12550464 | 1.0735614 | 1.5804975 | 1.0735614 | 437 |
| 15 | 524 | 842.041354207 | 0.1262852097 | 6.46849013 | 1.0049644 | 2.1248424 | 1.0049644 | 599 |
| 16 | 257 | 481.830339376 | 0.1253047284 | 4.5170619 | 2.8881578 | 1.0044434 | 1.0044434 | 472 |
| 17 | 273 | 504.499773313 | 0.116528194 | 3.14711431 | 2.223503 | 0.91545843 | 0.91545843 | 299 |
| 18 | 577 | 910.186334057 | 0.1155018989 | 4.35769108 | 1.8527904 | 1.0486174 | 1.0486174 | 462 |
| 19 | 151 | 321.160134309 | 0.1154766907 | 2.65116503 | 2.3070301 | 0.98442436 | 0.98442436 | 218 |
| 20 | 150 | 318.853104256 | 0.113958344 | 3.98788664 | 1.1182983 | 2.3070301 | 1.1182983 | 419 |

### N=5000

| rank W | zero j | gamma | W_j | abs zeta prime | previous gap | next gap | local min gap | rank inverse abs zeta prime |
|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| 1 | 400 | 679.742197883 | 0.1855610674 | 9.47921821 | 1.9417531 | 2.1527937 | 1.9417531 | 646 |
| 2 | 532 | 853.163112583 | 0.1748063642 | 6.21669518 | 2.5176641 | 0.93239914 | 0.93239914 | 588 |
| 3 | 1 | 14.134725142 | 0.156861284 | 0.793160433 | — | 6.8873145 | 6.8873145 | 1 |
| 4 | 482 | 787.468463816 | 0.1497346663 | 5.50870603 | 1.0073164 | 2.5906285 | 1.0073164 | 550 |
| 5 | 354 | 618.112831366 | 0.1434888122 | 5.53605337 | 2.574268 | 1.0716512 | 1.0716512 | 552 |
| 6 | 626 | 971.071491486 | 0.1318305897 | 6.52620993 | 0.94588093 | 2.1138698 | 0.94588093 | 600 |
| 7 | 619 | 963.182086671 | 0.1259124186 | 1.77370155 | 1.5125142 | 0.38495352 | 0.38495352 | 63 |
| 8 | 440 | 732.818052714 | 0.1236723312 | 7.17566104 | 1.4006978 | 1.9715905 | 1.4006978 | 616 |
| 9 | 491 | 799.654336211 | 0.1117256183 | 5.10897335 | 0.94676604 | 1.9499103 | 0.94676604 | 523 |
| 10 | 126 | 279.229250928 | 0.1059299574 | 3.44826319 | 0.9785074 | 3.2358638 | 0.9785074 | 344 |
| 11 | 507 | 820.721898444 | 0.1048711275 | 2.6556458 | 1.5172563 | 0.99155569 | 0.99155569 | 219 |
| 12 | 595 | 931.852740746 | 0.09891736946 | 5.42633388 | 0.84352941 | 2.5325661 | 0.84352941 | 542 |
| 13 | 343 | 602.579167886 | 0.09640409237 | 2.1166857 | 0.97703115 | 1.046451 | 0.97703115 | 115 |
| 14 | 334 | 590.660397517 | 0.09552598135 | 4.98771015 | 2.5207343 | 1.0654605 | 1.0654605 | 513 |
| 15 | 510 | 824.526293872 | 0.09337329799 | 9.27088234 | 2.3285364 | 1.5129935 | 1.5129935 | 645 |
| 16 | 169 | 349.316260871 | 0.09327487598 | 2.95168861 | 2.0435833 | 1.0921585 | 1.0921585 | 271 |
| 17 | 140 | 302.696749590 | 0.09306437784 | 2.84811367 | 1.0474241 | 2.1676218 | 1.0474241 | 258 |
| 18 | 621 | 965.055579624 | 0.0926384375 | 3.59426517 | 1.4885394 | 1.0551752 | 1.0551752 | 374 |
| 19 | 376 | 647.761753004 | 0.09224132808 | 3.05382741 | 1.4135614 | 1.0246479 | 1.0246479 | 286 |
| 20 | 77 | 195.265396680 | 0.08977449499 | 2.85013133 | 2.1856701 | 1.6110852 | 1.6110852 | 259 |

## Output files and truncations

- `per_zero.csv`: one row per N and zero gamma_j <= 1000, including |zeta'|, adjacent gaps, W_j, and both ranks.
- `t_grid.csv.gz`: every unique direct-zeta grid point, all four Delta profiles, and the two intensities per N.
- `part_b_j4.csv`: observed correlations, permutation p-values, and 95% null bands.
- `part_b_secondary.csv`: preregistered descriptive inverse-gap Spearman values, without extra p-value claims.
- `part_b_weighted_head.csv`: nested Simpson head values.
- `part_b_top20.csv`: top twenty W_j rows for each N.
- Eight PNG plots: W versus inverse derivative squared and Delta around the five largest W_j zeros, separately for each N.

Truncations: t is restricted to [0,1000]; zero ordinates are restricted to gamma<=1000 with one next neighbor for gap metadata; coefficient vectors contain only n=2..N; no uncomputed tail is inferred from discrete-minus-head. Q5/Q6 are localization diagnostics, not causal claims or RH evidence.
