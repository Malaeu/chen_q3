# Step33A.1-A Taylor Model Probe

Diagnostic only: sampled Arb/acb evidence for candidate Taylor/model
data.  This is not a Lean proof and does not emit payload declarations.

## Summary

- source: `raw_step22`
- cells checked: 1
- cells with sampled feasible degree: 0
- degrees: `16,20`
- fit samples: 17
- check samples: 61

## Degree Aggregates

| degree | parent total width | virtual total width | worst virtual chunk |
| ---: | ---: | ---: | ---: |
| 16 | `3.113516332435091531E-1` | `1.000000000000000000E-20` | 0 |
| 20 | `3.200592367387450191E-2` | `0.000000000000000000E-5` | None |

## Cells

| family | row | d | chunk | feasible degrees | best margin degree |
| --- | ---: | ---: | ---: | --- | ---: |
| `primary_finite` | 0 | `0.00` | 0 | `-` | 20 |

## Best Degree Details

### primary_finite row 0 chunk 0

- chunk interval: `[-3.535346901998863369E-1, -3.535346901998863369E-1]`
- degree: `20`
- sampled max residual: `1.454814712448840996E-3`
- remainder candidate: `1.600296183693725095E-3`
- lower model integral: `-3.693537816418000849E-1`
- upper model integral: `-3.373478579679255830E-1`
- current chunk width: `0.000000000000000000e+00`
- model interval width: `3.200592367387450191E-2`
- extra chunk width needed: `3.200592367387450343e-02`
- lower margin: `-1.581909144191379069e-02`
- upper margin: `-1.618683223196071275e-02`
- required remainder cap: `-1.838703950234887998e-05`
- failure mode: `model_interval_wider_than_current_chunk_interval`
- fits sampled residual and integral: `False`

#### Virtual Subchunk Summary

| degree | subchunks | total width | extra parent width | max sampled residual | failure mode |
| ---: | ---: | ---: | ---: | ---: | --- |
| 16 | 100 | `1.000000000000000000E-20` | `1.000000000000000000E-20` | `1.893260659781758254E-21` | `split_model_interval_wider_than_parent_chunk_interval` |
| 20 | 100 | `0.000000000000000000E-5` | `0.000000000000000000E+18` | `3.759273714159913374E-26` | `split_integral_center_mismatch` |

