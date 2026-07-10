# R1SourceAudit_v1

Status: diagnostic only. Not a proof of RH. Not a Route B kill. Phase 2 was not run. No new lambda/N anchors were bought. Heavy compute was not run.

## Verdict

- verdict: `REGISTERED_MODEL_MISS_DENOMINATOR_FLAT`
- failure_code: `None`
- core convention: parity-block `2x2 even` denominator `lambda1(G_even)`
- auxiliary missing fields were marked `MISSING`; no model-three interpolation was invented.

## R0 Convention Lock

- old mixed-3x3 reference r1(14,120): `3.71e-37`
- parity-block 2x2-even r1(14,120): `3.32260932181e-37`
- factor max: `1.1165923`
- pass: `True`

## R1 Pull Table

| lambda_sq | N | lambda1(G_even) | lambda2(G_even) | S0_odd | theta1 | r1 | ||B m1|| | c* | ||y|| | nu_tail |
|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| 12 | 60 | `2.3162229e-29` | `4.4089182e-29` | `7.1125969e-50` | `9.1907269e-54` | `3.9679803e-25` | `1.1549409e-14` | `3.2112548e-13` | `1.1662075e-8` | `MISSING` |
| 12 | 90 | `1.5251422e-28` | `2.0063014e-28` | `4.4562985e-50` | `5.8806556e-54` | `3.855808e-26` | `3.2272931e-14` | `1.0821428e-10` | `1.6386798e-9` | `MISSING` |
| 12 | 120 | `3.4299233e-28` | `4.0569232e-28` | `4.0388152e-50` | `5.1220197e-54` | `1.4933336e-26` | `MISSING` | `MISSING` | `MISSING` | `MISSING` |
| 13 | 60 | `3.387113e-29` | `4.3483688e-29` | `8.5468768e-55` | `1.0135629e-58` | `2.9924095e-30` | `MISSING` | `MISSING` | `MISSING` | `MISSING` |
| 13 | 90 | `1.265798e-28` | `2.4392009e-28` | `3.5484916e-55` | `4.1905359e-59` | `3.3105882e-31` | `MISSING` | `MISSING` | `MISSING` | `MISSING` |
| 13 | 120 | `3.6653785e-28` | `5.1438549e-28` | `3.0559135e-55` | `3.4839882e-59` | `9.5051254e-32` | `MISSING` | `MISSING` | `2.5791514e-9` | `MISSING` |
| 14 | 60 | `2.5011433e-29` | `3.7583332e-29` | `2.281219e-59` | `2.8385852e-63` | `1.1349151e-34` | `MISSING` | `MISSING` | `MISSING` | `MISSING` |
| 14 | 90 | `1.161529e-28` | `2.7375411e-28` | `2.002162e-60` | `1.8422044e-64` | `1.5860167e-36` | `MISSING` | `MISSING` | `MISSING` | `3.9328973e-53` |
| 14 | 120 | `4.3935739e-28` | `5.8467035e-28` | `1.6680023e-60` | `1.459813e-64` | `3.3226093e-37` | `5.692875e-14` | `3.9054388` | `2.7974899e-9` | `3.2960935e-53` |

## R2 Slope Fits

Fits use natural `log(X)` vs `lambda_sq`. All are `FIT_NOT_LAW` diagnostics.

| field | N=90 slope | N=120 slope | registered read |
|---|---:|---:|---|
| lambda1(G_even) | `-0.136175197256 (-0.043345912 pi)` | `0.123802547546 (0.039407575 pi)` | flat model passes; old `-2pi` is refuted on these rows |
| r1 | `-11.9571029321 (-3.8060641 pi)` | `-12.2643482767 (-3.9038633 pi)` | close to registered `-4pi` |
| ||B m1|| | `INSUFFICIENT_DATA` | `INSUFFICIENT_DATA` | insufficient saved data |
| c* | `INSUFFICIENT_DATA` | `INSUFFICIENT_DATA` | insufficient saved data |
| ||y|| | `INSUFFICIENT_DATA` | `INSUFFICIENT_DATA` | insufficient saved data |

Classification:
- lambda1 flat both rows: `True`
- r1 slope `-4pi` both rows: `True`

## R3 N-Tail

| lambda_sq | r1(60) | r1(90) | r1(120) | rho | geometric r1_inf | tail |
|---:|---:|---:|---:|---:|---:|---:|
| 12 | `3.9679803e-25` | `3.855808e-26` | `1.4933336e-26` | `15.16376` | `1.3265365e-26` | `1.6679712e-27` |
| 13 | `2.9924095e-30` | `3.3105882e-31` | `9.5051254e-32` | `11.276548` | `7.2085609e-32` | `2.2965645e-32` |
| 14 | `1.1349151e-34` | `1.5860167e-36` | `3.3226093e-37` | `89.256212` | `3.1805507e-37` | `1.4205864e-38` |

## R4 Decision

- repaired-law reference r1(12,120): `2.7e-26`
- measured r1(12,120): `1.49333361287e-26`
- factor max: `1.8080354`
- repaired point pass: `True`
- watchpoint: `M1_Y_NORM_O1_NEAR_LAMBDA_SQ_19_21` for any future `lambda_sq>=18` anchor.

Interpretation: the prior `r1` stop was a registered denominator-model miss. On the saved grid, `lambda1(G_even)` is flat while `r1` inherits the approximately `-4pi` law from `theta1`; the old `lambda1(G) ~ exp(-2pi lambda_sq)` denominator model is not supported.

## Stop

Stop after this report and handoff. Do not pick the next gate locally.
