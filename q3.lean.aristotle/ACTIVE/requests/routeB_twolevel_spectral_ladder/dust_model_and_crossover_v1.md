# DustModelAndCrossover_v1

## Headlines

1. Dust additive floor confirmed? NO
2. Zoned judge passes? YES
3. Early-zone first-zero relabel passes? YES
4. Crossover law status: `CROSSOVER_LAW_REFUTED`
5. D5/J=2000: `NOT_RUN`
6. Verdict code: `DUST_ADDITIVE_REFUTED`, `CROSSOVER_LAW_REFUTED`

Diagnostic only: not RH, no Phase 2, no QW formula changes, no packet-definition changes, no Q3 mainline changes.

## D1 Additivity

- registered dust floor `d=8.6e-33`; zero-consistent threshold `10d=8.6e-32`.
- raw all-block registered +-50% pass: `False`.
- dust-zone block count `3`; dust-zone blocks +-50% pass `True`.
- block median |Im K| vs block median |K| Spearman `0.657142857143`.
- code: `DUST_ADDITIVE_REFUTED`.

| gamma block | count | median |Im K| | median |K| | +-50% d pass | physical crossover? |
| --- | ---: | ---: | ---: | --- | --- |
| [14.0, 28.0) | 3 | `6.4820220665e-33` | `9.62894947161e-33` | `True` | `False` |
| [28.0, 56.0) | 8 | `9.0359192942e-33` | `9.75948050967e-33` | `True` | `False` |
| [56.0, 112.0) | 24 | `9.42977009894e-33` | `1.18807498517e-32` | `True` | `False` |
| [112.0, 224.0) | 57 | `6.22254905464e-32` | `2.42118503372e-31` | `False` | `True` |
| [224.0, 448.0) | 142 | `1.03478931692e-32` | `1.76124249149e-31` | `True` | `False` |
| [448.0, 896.0) | 266 | `1.53446547322e-33` | `8.62263518813e-32` | `False` | `False` |

## D2 Zoned Judge

- judged subset: `|K_j| >= 10d`, count `281`.
- realness circular MAD `0.0294657633569`.
- realness median `|Im/Re|` after phase fit `0.0411705796795`.
- realness registered pass `True`.
- j<=100 ZERO_CONSISTENT fraction `0.55` (55/100); registered pass `True`.
- code: `ZONED_JUDGE_PASS`.

## D3 Early-Zone Relabel

- j<=30 max `|K|=1.41580619354e-32`; median `|K|=1.12395961102e-32`.
- first-zero share `3.45123641453e-6` relabeled `<= 3.5e-6 (ZC)`; pass `True`.

| j | gamma | |K_j| upper bound |
| ---: | ---: | ---: |
| 1 | `14.1347251417` | `9.62894947161e-33` |
| 2 | `21.0220396388` | `9.35157199631e-33` |
| 3 | `25.0108575801` | `1.01109061131e-32` |
| 5 | `32.9350615877` | `9.69432141869e-33` |
| 10 | `49.7738324777` | `1.06182965373e-32` |
| 20 | `77.1448400689` | `1.12878364978e-32` |
| 30 | `101.317851006` | `1.41362936195e-32` |

## D4 Crossover Law

- code: `CROSSOVER_LAW_REFUTED`.
- peak(12,120) pass `False`; peak(14,120) pass `False`.
- N-control peak(13,90) `14.1347251417`; physical pass `False`; nyquist signature `False`.
- slope log(k_edge^2/E) vs log(lambda) `11.265671665`; registered 9+-2 pass `False`.

| anchor | peak gamma | expected 4pi lambda_sq | rel err | k_edge | C(J=200) |
| --- | ---: | ---: | ---: | ---: | ---: |
| `lambda_sq_12_N_120` | `14.1347251417` | `150.796447372` | `0.90626619` | `1.54637146774e-26` | `NEGATIVE_RESIDUAL` |
| `lambda_sq_13_N_120_source_v2` | `167.184439978` | `163.362817987` | `0.023393463` | `3.61872662868e-29` | `UNKNOWN` |
| `lambda_sq_14_N_120` | `14.1347251417` | `175.929188601` | `0.91965674` | `8.32446265445e-32` | `NEGATIVE_RESIDUAL` |
| `lambda_sq_13_N_90` | `14.1347251417` | `163.362817987` | `0.91347649` | `3.61872662868e-29` | `NEGATIVE_RESIDUAL` |
- `lambda_sq_12_N_120` ledger C(J=200): `NEGATIVE_RESIDUAL`; `R_J/a1=-1.78318774684e+18`.
- `lambda_sq_14_N_120` ledger C(J=200): `NEGATIVE_RESIDUAL`; `R_J/a1=-6.13987034897e+28`.

## D5 Tail

- status: `NOT_RUN`.
- reason: D5 objective says run only if D1-D2 pass; literal D1/D2 gate did not pass.

## State Policy

- Do not promote DISPLACED_PROFILE from this gate unless D1/D2 and D5 pass.
- The previous edge+ledger far-tail evidence remains diagnostic support, not RH closure.
