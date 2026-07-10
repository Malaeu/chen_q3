# AnchorLockedKChannel_v1

## Headlines

1. Anchor reproduced? `YES`
2. Real Plancherel pass? `YES`
3. Standing ceiling: `PASS`
4. Crossover: `CROSSOVER_CONFIRMED`
5. Tail: `TAIL_FLATTENING_REFUTED`
6. Verdict codes: `ANCHOR_REPRODUCED`, `PLANCHEREL_REAL_PASS`, `CROSSOVER_CONFIRMED`, `TAIL_FLATTENING_REFUTED`

Diagnostic only: not RH, no Phase 2, no QW formula changes, no packet-definition changes, no Q3 mainline changes.

## Rollback

- Previous portable Plancherel entry: `VOID_TAUTOLOGICAL_JUDGE`.
- Previous crossover entry: `UNTESTED`.

## A0 Provenance Lock

| point | coeff file | sha256 | Sum |c|^2 | fields ok |
| --- | --- | --- | ---: | --- |
| `lambda_sq_13_N_120` | `out/portable_k_coeffs_lambda_sq_13_N_120.json` | `0e5239355c54103859b22d7f753d8cd6765c2c41bcd3ec7f86b20beccc907a88` | `1.0` | `True` |
| `lambda_sq_12_N_120` | `out/portable_k_coeffs_lambda_sq_12_N_120.json` | `ad85eecb6776eea3169ce75aa3e3db9474cac47943d0820192543e1bd7e4e238` | `1.0` | `True` |
| `lambda_sq_14_N_120` | `out/portable_k_coeffs_lambda_sq_14_N_120.json` | `f2ecc3e794728dceff933f2ced8b7e91593fc5d956a3a4d4a7522dda892bfecf` | `1.0` | `True` |
| `lambda_sq_13_N_90` | `out/portable_k_coeffs_lambda_sq_13_N_90.json` | `ca8f8b083b86da86d0c3716af6614cfc57007c33884d95352710ea2977b5671e` | `1.0` | `True` |

## A1 Anchor Reproduction

- anchor artifact: `out/zero_sum_profile_v2.json` sha256 `b15d27fad7f12e09ca8c3cf82027542b712c462d574e7a6a375587ef6449b9be`.
- max relative diff j<=10: `1.648431368e-49`; tolerance `1e-6`; code `ANCHOR_REPRODUCED`.

| j | gamma | archived | computed | rel diff |
| ---: | ---: | ---: | ---: | ---: |
| 1 | `14.134725141735` | `9.62894947161e-33` | `9.62894947161e-33` | `4.9478712e-51` |
| 2 | `21.022039638772` | `9.35157199631e-33` | `9.35157199631e-33` | `1.6527322e-50` |
| 3 | `25.010857580146` | `1.01109061131e-32` | `1.01109061131e-32` | `1.0171213e-50` |
| 4 | `30.42487612586` | `9.70076257906e-33` | `9.70076257906e-33` | `1.5657519e-49` |
| 5 | `32.935061587739` | `9.69432141869e-33` | `9.69432141869e-33` | `1.6484314e-49` |
| 6 | `37.586178158826` | `1.01102791023e-32` | `1.01102791023e-32` | `9.2306274e-50` |
| 7 | `40.918719012147` | `9.71118714234e-33` | `9.71118714234e-33` | `4.4597514e-51` |
| 8 | `43.327073280915` | `9.72810457535e-33` | `9.72810457535e-33` | `1.5381721e-50` |
| 9 | `48.005150881167` | `9.79085644399e-33` | `9.79085644399e-33` | `6.5781714e-50` |
| 10 | `49.773832477672` | `1.06182965373e-32` | `1.06182965373e-32` | `4.4033122e-50` |

## A2 Real Plancherel

| point | P | |P-1| | code | plant fires |
| --- | ---: | ---: | --- | --- |
| `lambda_sq_13_N_120` | `1.0000000000000002` | `2.220446049250313e-16` | `PLANCHEREL_REAL_PASS` | `True` |
| `lambda_sq_12_N_120` | `1.0000000000000002` | `2.220446049250313e-16` | `PLANCHEREL_REAL_PASS` | `True` |
| `lambda_sq_14_N_120` | `1.0000000000000002` | `2.220446049250313e-16` | `PLANCHEREL_REAL_PASS` | `True` |
| `lambda_sq_13_N_90` | `1.0000000000000002` | `2.220446049250313e-16` | `PLANCHEREL_REAL_PASS` | `True` |

- Method: real t-quadrature on symmetric t-ranges; coefficient identity not used for verdict.
- Planted violation perturbs one `Vhat_n(t)` stream by `1e-6`; coefficient-side plants do not count.

## A4 Crossover

| point | peak gamma | S200/a1 | R200/a1 |
| --- | ---: | ---: | ---: |
| `lambda_sq_12_N_120` | `153.024693811` | `0.532378861797` | `0.467621138203` |
| `lambda_sq_14_N_120` | `178.377407776` | `0.523285585406` | `0.476714414594` |
| `lambda_sq_13_N_90` | `167.184439978` | `0.564719291914` | `0.435280708086` |
- code: `CROSSOVER_CONFIRMED`.

## A5 Tail

| J | S_J/a1 | R_J/a1 | C |
| ---: | ---: | ---: | ---: |
| 500 | `0.714131074754` | `0.285868925246` | `8.17246421272e-29` |
| 750 | `0.826271041912` | `0.173728958088` | `7.29664221825e-29` |
| 1000 | `0.862028913756` | `0.137971086244` | `7.17562137355e-29` |
| 1500 | `0.86794256273` | `0.13205743727` | `8.08598531021e-29` |
| 2000 | `0.87059768426` | `0.12940231574` | `8.8641541999e-29` |
- local p: `2.58073526135`; pass `False`.
- C_refit: `7.91897346293e-29`; pass `True`.
- tail code: `TAIL_FLATTENING_REFUTED`.

## Actions Log

- Required actions log: `anchor_locked_k_channel_v1_actions_log.md`.
