# SOFT_L2 AutocorrelationTailCheck report — (13,120)

Status: `TAIL_DOMINATED / DIAGNOSTIC_ONLY / NOT_RH`

Round-13 role:
`OPTIONAL_SOURCE_COMPACTNESS_SPATIAL_TIGHTNESS_DIAGNOSTIC`.  This check may
inform the spatial-tightness input of the optional
`SourceCompactnessToFullAutocorrelation` leaf.  It does not supply uniform
translation continuity and is not an input to L2.2.

For the persisted finite ground packet `ground_xi1_m13_N120`, the positive
tail half of the registered lag ledger was compared pointwise with

```text
|A(t)| <= e_L(L-t),  L/2 <= t <= L.
```

The edge majorant was evaluated directly from the same registered edge-profile
formula at each ledger depth; it was not interpolated.  Negative lags duplicate
the check by Hermitian symmetry.

| t/L | |A(t)| | e_L(L-t) | majorant / |A| | margin, orders |
|---:|---:|---:|---:|---:|
| 1/2 | 1.3615056e-5 | 1 | 7.34481e4 | 4.86598 |
| 2/3 | 3.8861059e-11 | 5.9445732e-2 | 1.52970e9 | 9.18461 |
| 5/6 | 6.0168504e-22 | 2.4399129e-6 | 4.05513e15 | 15.6080 |
| 1 | raw 1.91797e-81 | 0 | exact support endpoint | exact anchor |

Thus the verdict is `TAIL_DOMINATED`.  The worst non-endpoint reserve is
`4.865980566...` decimal orders, attained at `t=L/2`.

At `t=L`, compact support gives `A(L)=e_L(0)=0` exactly.  The raw lag-ledger
residue `1.92e-81` is retained in the machine record but excluded from the
judge as working-precision endpoint noise.  This finite-grid check is not an
asymptotic tail theorem and does not add a tail hypothesis to L2.2, consistently
with the Round-13 V1 ruling.

Map code: `FALSE_WALL_REMOVED_ROUND13`.

Artifacts:

- `SOFT_L2_AUTOCORRELATION_TAIL_CHECK_13_120.csv`
- `SOFT_L2_AUTOCORRELATION_TAIL_CHECK_13_120.json`
- `SOFT_L2_AUTOCORRELATION_TAIL_CHECK_13_120_LOG.png`
- `soft_l2_round13_measurements.py`
- `validate_soft_l2_round13_measurements.py`

`NOT_RH`.
