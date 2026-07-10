# PortableKChannel_v1

## Headlines

1. Plancherel pass? YES
2. Old zero_sum_profile_v2 rows validated by portable K? NO
3. Crossover retest: `CROSSOVER_REFUTED`
4. k_edge slope re-registration: `11.265671665` pass `True`
5. Tail J=2000: `RUN`
6. Verdict code: `PLANCHEREL_PASS`, `CROSSOVER_REFUTED`

Diagnostic only: not RH, no Phase 2, no QW formula changes, no packet-definition changes, no Q3 mainline changes.

## R0 K Channel

| point | L | coeff file | coeff count |
| --- | ---: | --- | ---: |
| `lambda_sq_13_N_120` | `2.56494935746` | `out/portable_k_coeffs_lambda_sq_13_N_120.json` | 241 |
| `lambda_sq_12_N_120` | `2.48490664979` | `out/portable_k_coeffs_lambda_sq_12_N_120.json` | 241 |
| `lambda_sq_14_N_120` | `2.63905732962` | `out/portable_k_coeffs_lambda_sq_14_N_120.json` | 241 |
| `lambda_sq_13_N_90` | `2.56494935746` | `out/portable_k_coeffs_lambda_sq_13_N_90.json` | 181 |

## R1 Plancherel

| point | P_exact | |P-1| | code | planted fires |
| --- | ---: | ---: | --- | --- |
| `lambda_sq_13_N_120` | `1.0` | `2.220446e-16` | `PLANCHEREL_PASS` | `True` |
| `lambda_sq_12_N_120` | `1.0` | `0.0` | `PLANCHEREL_PASS` | `True` |
| `lambda_sq_14_N_120` | `1.0` | `2.220446e-16` | `PLANCHEREL_PASS` | `True` |
| `lambda_sq_13_N_90` | `1.0` | `2.220446e-16` | `PLANCHEREL_PASS` | `True` |

- retro first-10 max relative `|K|` diff vs `zero_sum_profile_v2`: `1.8023e+16`.
- old-profile agreement at tolerance `1e-6`: `False`.
- Plancherel verdict uses the closed-form coefficient identity `P=sum |c_n|^2`; planted scale violation is not renormalized.

## R2 Bug Localization

- old source: `out/dust_model_and_crossover_v1.json:D4_crossover_law.profiles`.
- garbage mass range: `[1.46300803037e-35, 1.60642191167e-35]`; lambda-independence around `1.8e-35` confirmed `False`.

| old profile | old L | old N | old peak gamma | 2|K_peak|^2 | old a1 |
| --- | ---: | ---: | ---: | ---: | ---: |
| `lambda_sq_12_N_120` | `2.48490664979` | 120 | `14.1347251417` | `1.60642191167e-35` | `9.01371456167e-54` |
| `lambda_sq_14_N_120` | `2.63905732962` | 120 | `14.1347251417` | `1.46300803037e-35` | `2.38397302841e-64` |
| `lambda_sq_13_N_90` | `2.56494935746` | 90 | `14.1347251417` | `1.52741333991e-35` | `5.9922657367e-59` |

## R3 Crossover Retest

- code: `CROSSOVER_REFUTED`.
- peak12 pass `False`; peak14 pass `False`; N-control physical `False`; nyquist `False`.
- S200 range pass `False`; rising pass `True`; no negative residuals `False`.

| point | peak gamma | S200/a1 | R200/a1 |
| --- | ---: | ---: | ---: |
| `lambda_sq_12_N_120` | `129.5787042` | `1.12361272005e+23` | `-1.12361272005e+23` |
| `lambda_sq_14_N_120` | `205.394697202` | `7.67976526651e+33` | `-7.67976526651e+33` |
| `lambda_sq_13_N_90` | `103.72553804` | `2.3920788061e+28` | `-2.3920788061e+28` |

## R4 k_edge Re-Registration

- derivation: BK psi^2=c(1-lambda_4) => lambda^11*E; RvM comparison gives lambda^9*E class for a1.
- measured slope `11.265671665`; target `11+-1`; pass `True`.

## R5 Tail

- S2000/a1 `6.51674713983e+29`; pass `False`; rising `True`.
- local p `1.22163466781`; pass `False`.
- C refit `UNKNOWN` vs `7.9e-29`; pass `False`.
- tail code `None`.
