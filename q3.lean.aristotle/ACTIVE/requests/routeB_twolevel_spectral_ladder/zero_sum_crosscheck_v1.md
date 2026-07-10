# ZeroSumCrossCheck_v1

## Verdict

`SLOW_TAIL`

Route B diagnostic only: not RH, no Phase 2, no Q3 mainline edit.

## SymbolDiagonal Reclassification

- `SymbolDiagonalCrossCheck_v1`: `SYMBOL_MATCH -> TAUTOLOGICAL_CHANNEL`.
- Reason: the `rel_diff=2.3763e-91` match is the fingerprint of the same `tau` contraction, not an independent E5 zero-sum judge.

## Z0

- zeros: first 100 nontrivial zeta zeros via `mpmath.zetazero(j)`.
- recorded precision: at least 30 digits in JSON.
- K7: numerical calibration only; no RH inference.

## Z1

- `K(t) = int k1(u) u^{-it} d*u` with normalized tol_B `k1`.
- tol_B coefficients were rebuilt from the physical E-map using breakpoints `u=lambda/m`.
- Main zero sums use the exact finite-packet Mellin transform from those coefficients.
- self-test point: `t=1.0`.
- `K_dps40=(-0.84635116853220202 + 8.89182845114830235e-33j)`
- `K_dps80=(-0.84635116853220202 + 8.89182610341524235e-33j)`
- relative digits: `38.5558282727`; required `>=25`; pass `True`.

## Z2

- pairing convention: `+-gamma` is counted explicitly by `2|K(gamma_j)|^2`.
- `a1_raw=5.3729537354420237e-59` from `out/packet_truth_pull_v1.json:T0_T2_main.a1_raw`.
- `|K(gamma_1)|=9.62894947161e-33`; registered window `[3e-31,3e-30]`; pass `False`.
- `S_100/a1_raw=0.311932435916`.
- monotone up: `True`.
- max `S_J/a1_raw=0.311932435916`; no overshoot `>1.05`: `True`.
- decay fit `|K(gamma_j)| ~ gamma^(-p)`: `p=-2.10326328418`; registered `[0.5,1.5]`; `FIT_NOT_LAW`.

| J | gamma_J | |K(gamma_J)| | S_J/a1_raw |
| ---: | ---: | ---: | ---: |
| 1 | `14.134725141735` | `9.62894947161e-33` | `3.45123641453e-6` |
| 2 | `21.022039638772` | `9.35157199631e-33` | `6.70649983604e-6` |
| 5 | `32.935061587739` | `9.69432141869e-33` | `1.75130356488e-5` |
| 10 | `49.773832477672` | `1.06182965373e-32` | `3.61162112478e-5` |
| 20 | `77.144840068875` | `1.12878364978e-32` | `8.13774548673e-5` |
| 50 | `143.11184580762` | `2.47745839433e-32` | `0.000347698136662` |
| 100 | `236.52422966582` | `1.12712939036e-31` | `0.311932435916` |

## Interpretation

- The transform self-test passes and partial sums are monotone with no overshoot, but `S_100/a1_raw < 0.5`.
- Classification is `SLOW_TAIL`: E5 is opened into Z1-Z3 pen bookkeeping plus a required `StripTailZeroSumBound` / log-correction tail gate.
