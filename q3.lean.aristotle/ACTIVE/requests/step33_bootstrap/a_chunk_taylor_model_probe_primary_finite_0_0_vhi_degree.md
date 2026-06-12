# Step33A.1-A Taylor Model Probe

Diagnostic only: sampled Arb/acb evidence for candidate Taylor/model
data.  This is not a Lean proof and does not emit payload declarations.

## Summary

- source: `raw_step22`
- cells checked: 1
- cells with sampled feasible degree: 0
- degrees: `18,20,22,24`
- fit samples: 65
- check samples: 241

## Cells

| family | row | d | chunk | feasible degrees | best margin degree |
| --- | ---: | ---: | ---: | --- | ---: |
| `primary_finite` | 0 | `0.00` | 0 | `-` | 24 |

## Best Degree Details

### primary_finite row 0 chunk 0

- chunk interval: `[-3.535346901998863369E-1, -3.535346901998863369E-1]`
- degree: `24`
- sampled max residual: `3.036379483829509951e-04`
- remainder candidate: `3.340017432212461054e-04`
- lower model integral: `-3.568916622923878901e-01`
- upper model integral: `-3.502116274279629682e-01`
- current chunk width: `0.000000000000000000e+00`
- model interval width: `6.680034864424921892e-03`
- extra chunk width needed: `6.680034864424921892e-03`
- lower margin: `-3.356972092501575577e-03`
- upper margin: `-3.323062771923346315e-03`
- required remainder cap: `-1.695466028911463056e-06`
- failure mode: `model_interval_wider_than_current_chunk_interval`
- fits sampled residual and integral: `False`

