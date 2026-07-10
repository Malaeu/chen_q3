alpha-Gate note: G3'(alpha) is RH-equivalent by alpha-Gate Equivalence; this gate MEASURES alpha, it does not claim to prove its bound.
# LadderLaw_v1

Route B TwoLevelSpectralLadder diagnostic gate. NOT RH. Phase 2 not run. Q3 mainline not touched.

## Headlines

1. Does Rayleigh excess alpha track the ground scale? YES
2. Is the same-parity tracking gap identified? YES
3. Does W_prime look decreasing? YES
4. Do rungs 4..6 match registered parity/scale? YES
5. Verdict code: LADDERLAW_PREFLIGHT_PASS, TRUNCATION_CONFIRMED

## T1 Rayleigh Table

| lambda_sq | mu1 | a1_raw/mu1 | alpha_raw/a1_raw | alpha_opt/lambda1_G | eta_raw^2/mu1 | alpha_opt/E |
|---:|---:|---:|---:|---:|---:|---:|
| 12 | `5.12201973e-54` | `1.759796922` | `0.4317526145` | `0.1167746241` | `0.9269759913` | `2.093067e+11` |
| 13 | `3.48398820e-59` | `1.542184826` | `0.3515692911` | `0.1048715396` | `0.6755784464` | `3.617590e+11` |
| 14 | `1.45981295e-64` | `1.63306746` | `0.3876554247` | `0.1232578912` | `0.5931168347` | `5.215740e+11` |

- alpha conventions are both carried: raw `a1_raw-mu1`, projected packet `a1_projected-mu1`, and opt `lambda1(G_even)-mu1`.
- Registered alpha/a1 window [0.08,0.45] passes for raw and opt at all three lambda values.

## T2 Parity And Tracking Gap

| lambda_sq | parity xi1,xi2,xi3 | simplicity gap mu2-mu1 | tracking gap even mu3-mu1 | k-overlaps |
|---:|---|---:|---:|---|
| 12 | `even,odd,even` | `4.03830299e-50` | `1.69321146e-46` | xi1_k1=1, xi2_k2_odd=0.99999999, xi2_k2_even=2.656e-15 |
| 13 | `even,odd,even` | `3.05556506e-55` | `1.31185430e-51` | xi1_k1=1, xi2_k2_odd=0.99999999, xi2_k2_even=2.731e-16 |
| 14 | `even,odd,even` | `1.66785629e-60` | `9.38433376e-57` | xi1_k1=1, xi2_k2_odd=1, xi2_k2_even=6.442e-16 |

Same-parity tracking gap is identified as `mu3-mu1` because xi1 is even, xi2 is odd, and xi3 is even.

## T3 W_prime Detector

`W_prime_without_b = sqrt(lambda) * sqrt(alpha / (mu3-mu1))`; b-scaled values are also reported. FIT_NOT_LAW.

| lambda_sq | W_raw_without_b | W_raw_with_b | W_opt_without_b | registered raw table pass |
|---:|---:|---:|---:|---|
| 12 | `2.82168871e-04` | `1.32465426e-04` | `1.17706055e-04` | `True` |
| 13 | `2.27853159e-04` | `1.06942316e-04` | `1.05917449e-04` | `True` |
| 14 | `1.91956971e-04` | `9.00773073e-05` | `9.04586967e-05` | `True` |

- raw W' slope vs lambda: `-5.00274`; opt W' slope vs lambda: `-3.40572`; FIT_NOT_LAW.
- raw alpha/E slope vs lambda: `8.67649`; projected alpha/E slope: `10.1225`; registered RH-regime proxy is 9+-2.

## T4 Rungs 4..6

| rung | mu | residual | parity | range pass | PSD pass |
|---:|---:|---:|---|---|---|
| 4 | `4.24957813e-48` | `1.06559475e-76` | `odd` | `True` | `True` |
| 5 | `1.09069940e-44` | `1.52743360e-68` | `even` | `True` | `True` |
| 6 | `2.01792833e-41` | `1.48383114e-60` | `odd` | `True` | `True` |

- mu5/mu4 = `2566.606308` pass `True`
- mu6/mu5 = `1850.123254` pass `True`

## T5 y Spectroscopy

- y_norm(13,120): `2.57915166848e-09`
- fraction of ||y||^2 on rungs 4..6: `0.999999885157` pass `True`
- Legacy c*_y reconstruction is recorded in JSON but is not a current objective failure.

## T6 Fresh y at N=90

- ||y||(13,90): `8.0852644385e-09`
- code: `TRUNCATION_CONFIRMED`
- residual: `6.50230085e-86`

## T7 RayleighLadderTracking Cross-check

| lambda_sq | measured 1-|<xi1,k1>|^2 | raw bound before tail | projected bound before tail | opt bound before tail |
|---:|---:|---:|---:|---:|
| 12 | `8.36116820e-09` | `2.29841040e-08` pass `True` | `1.49243479e-08` pass `True` | `3.99951186e-09` pass `False` |
| 14 | `3.85685373e-09` | `9.84790290e-09` pass `True` | `7.15781301e-09` pass `True` | `2.18693882e-09` pass `False` |

The diagnostic inequality passes for the actual raw/projected Rayleigh alpha before adding positive tail terms; opt alpha is reported separately and is too small for this crude lower-tail check.

## T8 PoissonParityLadder Status

- Exact Fourier/Hermite eigenbranches: PoissonParityLadder recorded as exact parity-ladder status.
- PSWF/prolate approximants: parity defect measured, not treated as exact; upper bound `9.76583918e-27`.

## Verdict

- codes: `['LADDERLAW_PREFLIGHT_PASS', 'TRUNCATION_CONFIRMED']`
- status: `complete`
- state update: `MidWindowMassBound` absorbed; G3 is `RayleighExcessBound alpha <= poly(lambda)*E`, not raw eta.
- addendum: `ladder_law_v1_addendum.md` records rung residual/PSD quotes, gap-slope `19.6819692055`, and the favorable W-prime slope miss.
- next: STOP and wait for Proshka review.
