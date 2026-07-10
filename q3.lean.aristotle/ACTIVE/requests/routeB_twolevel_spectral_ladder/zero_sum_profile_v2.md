# ZeroSumProfile_v2

## Verdict

`CHANNEL_DUST_FLOOR`, `PARTIAL_DISPLACED_PROFILE`, `COMB_MECHANISM_REFUTED`, `PROFILE_FIT_OUT_OF_RANGE`

Diagnostic only: not RH, no Phase 2, no QW formula changes.

## P0 Identity Lock

- Object: channel B primary `k1_N=sum c_n V_n`; `K_N(gamma)=sum c_n Vhat_n(gamma)`.
- Transform: `Vhat_n(gamma)=lambda^{i gamma} L^{-1/2} * (exp(i(2pi n/L-gamma)L)-1)/(i(2pi n/L-gamma))`.
- Stable form: `expm1(z)/z`, exact limit `L` when denominator is small.
- Partial sum: `S_J=2*sum_{j<=J}|K_N(gamma_j)|^2`.
- Denominator: `a1_raw=<T k1_N,k1_N>=5.3729537354420237e-59` from `out/packet_truth_pull_v1.json:T0_T2_main.a1_raw`.
- Boundary/poles: already inside `tau/T`; no pole or boundary subtraction here.
- Channel C: secondary continuum E-integral gap only.
- Zero input: `mpmath.zetazero(j)`; K7 calibration only; no RH inference.

## P1 Profile j<=100

- argmax j: `62`, gamma `167.18443997817`.
- peak `|K|=7.6794750308e-31`; registered peak window pass `False`.
- first-zero share `2|K(g1)|^2/a1=3.45123641453e-6`; registered `3.5e-6`.
- median `|Im K|=1.51883755713e-32`.
- median `|Re K|=2.32950271705e-32`.
- median `|Im|/|Re|=0.65200076652`; dust pass `False`.

| gamma block | count | block sum / denom | max |K| | argmax j |
| --- | ---: | ---: | ---: | ---: |
| `[14.0,28.0)` | 3 | `1.05118712374e-5` | `1.01109061131e-32` | 3 |
| `[28.0,56.0)` | 8 | `2.92643675625e-5` | `1.06182965373e-32` | 10 |
| `[56.0,112.0)` | 24 | `0.000141372590408` | `1.56611149348e-32` | 34 |
| `[112.0,224.0)` | 57 | `0.282256211557` | `7.6794750308e-31` | 62 |

## P2 Extended Profile

| J | S_J/denom |
| ---: | ---: |
| 100 | `0.311932435916` |
| 200 | `0.506354401154` |
| 300 | `0.662883038035` |
| 400 | `0.682125092087` |
| 500 | `0.714131074754` |

| gamma block | count | block sum / denom | max |K| | argmax j |
| --- | ---: | ---: | ---: | ---: |
| `[14.0,28.0)` | 3 | `1.05118712374e-5` | `1.01109061131e-32` | 3 |
| `[28.0,56.0)` | 8 | `2.92643675625e-5` | `1.06182965373e-32` | 10 |
| `[56.0,112.0)` | 24 | `0.000141372590408` | `1.56611149348e-32` | 34 |
| `[112.0,224.0)` | 57 | `0.282256211557` | `7.6794750308e-31` | 62 |
| `[224.0,448.0)` | 142 | `0.264154083002` | `4.65981939662e-31` | 94 |
| `[448.0,896.0)` | 266 | `0.167539631366` | `3.17775169136e-31` | 247 |

- P2 code: `PARTIAL_DISPLACED_PROFILE`.
- S_500/denom: `0.714131074754`.
- strictly rising 400->500: `True`.

## P3 Comb Correlation

- all j corr `|K|` vs `T/gamma`: `0.127246108984`.
- all j corr `|K|` vs `L/gamma`: `0.077207252829`.
- post-peak corr `T/gamma`: `0.341320124854`.
- post-peak corr `L/gamma`: `0.369195801447`.
- expected `corr(T)>corr(L)`: `False`.
- comb code: `COMB_MECHANISM_REFUTED`.

## P4 Fit

- post-peak fit p: `1.39662985936`.
- registered `[1.7,2.5]`: `False`.
- label: `FIT_NOT_LAW`.

## Channel C Gap

| j | gamma | |K_B| | |K_C-K_B|/|K_B| |
| ---: | ---: | ---: | ---: |
| 1 | `14.134725141735` | `9.62894947161e-33` | `0.0531084803508` |
| 62 | `167.18443997817` | `7.6794750308e-31` | `0.00321842064586` |

## Selected Rows

| J | gamma_J | |K_N(gamma_J)| | S_J/denom |
| ---: | ---: | ---: | ---: |
| 1 | `14.134725141735` | `9.62894947161e-33` | `3.45123641453e-6` |
| 2 | `21.022039638772` | `9.35157199631e-33` | `6.70649983604e-6` |
| 5 | `32.935061587739` | `9.69432141869e-33` | `1.75130356488e-5` |
| 10 | `49.773832477672` | `1.06182965373e-32` | `3.61162112478e-5` |
| 20 | `77.144840068875` | `1.12878364978e-32` | `8.13774548673e-5` |
| 50 | `143.11184580762` | `2.47745839433e-32` | `0.000347698136662` |
| 100 | `236.52422966582` | `1.12712939036e-31` | `0.311932435916` |
| 200 | `396.38185422259` | `4.65216542317e-32` | `0.506354401154` |
| 300 | `541.8474371212` | `1.18580868524e-31` | `0.662883038035` |
| 400 | `679.74219788253` | `6.37623569423e-32` | `0.682125092087` |
| 500 | `811.18435884651` | `6.75878226945e-32` | `0.714131074754` |
