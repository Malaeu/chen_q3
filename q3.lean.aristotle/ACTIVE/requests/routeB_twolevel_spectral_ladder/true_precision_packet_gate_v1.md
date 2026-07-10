# TruePrecisionPacketGate_v1

Route B TwoLevelSpectralLadder diagnostic only. Not RH. No Phase 2. One point `(lambda_sq,N)=(13,120)`.

## Verdict

- status: `complete`
- codes: `['EPS_SQUARE_LAW_CONFIRMED', 'LANDS_AT_MU1', 'Y_PHYSICAL', 'ETA_TRUE_MEASURED']`
- eps code: `EPS_SQUARE_LAW_CONFIRMED`
- y code: `Y_PHYSICAL`
- lambda1(A)/lambda1(B): `1.0`
- y(A)/y(B): `1.0`

## P0 Constructor Self-Test

- K1 dps40 vs dps80 pass: `True`; diff `2.326567e-41`
- planted node error caught: `True`; clean diff `6.8524287e-81`, planted diff `1.0e-20`

## P1-P3 Runs

| run | tol | dps | q | coeff maxdiff | max dust | lambda1(G_even) | lambda2(G_even) | 1-|<xi1,k1>| | ||y|| |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| `tol_A` | `1e-24` | 80 | 256 | `2.1277195e-69` | `9.7658392e-27` | `3.8921656e-59` | `2.0137065e-51` | `2.3459413e-9` | `2.5791517e-9` |
| `tol_B` | `1e-30` | 110 | 192 | `6.1237215e-34` | `9.7658392e-27` | `3.8921656e-59` | `2.0137065e-51` | `2.3459413e-9` | `2.5791517e-9` |

Dust rows:
- `tol_A`: k1=1.7192006e-30, k2_odd=1.5793085e-28, k2_even=9.7658392e-27
- `tol_B`: k1=1.7192006e-30, k2_odd=1.5793085e-28, k2_even=9.7658392e-27

## P4 Eta

- eta_true: `2.249633893e-30`
- closest class: `E^(1/2)` (`FIT_NOT_LAW`, one point only)

## P5 Free Pull

- ||y||(12,120): `MISSING`; status `MISSING`; source `out/nconv_anchor_lambda_sq_12_N_120.json,out/full_low_eig_lambda_sq_12_N_120.json,out/feshbach_lambda_sq_12_N_120.json`

## Stop

Stop after this report + handoff. Carry the verdict into `OperatorStaticSchurStabilityGate` on `S0_parity`.
