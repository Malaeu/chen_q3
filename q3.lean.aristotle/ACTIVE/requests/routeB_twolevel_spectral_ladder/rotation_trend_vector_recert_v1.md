# RotationTrend_and_VectorRecert_v1

Route B diagnostic only. Not RH. No Phase 2.

## Verdict

- status: `complete`
- codes: `['ROTATION_DECAYING(slope_-2)', 'LAMBDA1_CONVENTION_RESOLVED', 'VECTOR_RECERT_PASS']`
- door: `EXTEND_PACKET_NEXT`

## Part A Rotation Trend

| lambda_sq | theta | a1_raw | a2_raw | g12_raw | gamma | ground(raw 2x2) |
|---:|---:|---:|---:|---:|---:|---:|
| 12 | `8.797871453e-5` | `9.0137146e-54` | `2.7876852e-46` | `(1.882695e-50 - 1.7849269e-133j)` | `(-0.11523878 + 1.2450847e-111j)` | `7.742215e-54` |
| 13 | `6.411629221e-5` | `5.3729537e-59` | `2.2163767e-51` | `(1.1054322e-55 - 1.3641059e-136j)` | `(-0.11367046 - 8.6165085e-112j)` | `4.8216123e-59` |
| 14 | `5.876494568e-5` | `2.383973e-64` | `1.4958542e-56` | `(7.4139107e-61 - 1.1238115e-138j)` | `(-0.11233505 + 1.1903244e-111j)` | `2.0165169e-64` |

- trend code: `ROTATION_DECAYING(slope_-2)`
- best slope target: `slope_-2`
- decaying order theta12 > theta13 > theta14: `True`

## Lambda1 Convention Gap

- literal raw ordinary 2x2 ground at 13: `4.82161227735e-59`
- hybrid PacketTruth `a1_raw` with orthogonal `g12/a2` ground at 13: `4.54513935124e-59`
- TPPG value: `3.89216559799e-59`
- resolution: literal raw ordinary 2x2 uses raw k1/k2e/gamma-free entries; the earlier expected ~4.545e-59 is the hybrid a1_raw with PacketTruth orthogonal g12/a2 convention; TPPG 3.8922e-59 is the fully Gram-orthonormal parity-projected G_even ground.

## Part B Vector Recert

- method: `inverse_iteration_with_saved_xi_starts_and_T_solve`, dps `250`
- code: `VECTOR_RECERT_PASS`
- PSD threshold: `2.0142363e-51`
- fresh y: `2.57915166848e-9`
- fresh E_tail: `4.1204238e-60`
- fresh c*_y: `6.1942414e-43`
- fresh PSD pass: `True`
- planted PSD fires: `True`

| i | mu | residual |
|---:|---:|---:|
| 1 | `3.48398819933e-59` | `2.2913263e-83` |
| 2 | `3.05591339752e-55` | `9.6154924e-79` |
| 3 | `1.31185428457e-51` | `1.0146435e-74` |

## Stop

Stop after report + handoff.
