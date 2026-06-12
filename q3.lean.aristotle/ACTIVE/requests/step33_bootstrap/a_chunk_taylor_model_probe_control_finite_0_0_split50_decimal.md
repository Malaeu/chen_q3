# Step33A.1-A Taylor Model Probe

Diagnostic only: sampled Arb/acb evidence for candidate Taylor/model
data.  This is not a Lean proof and does not emit payload declarations.

## Summary

- source: `raw_step22`
- cells checked: 1
- cells with sampled feasible degree: 0
- degrees: `12,16`
- fit samples: 17
- check samples: 81

## Degree Aggregates

| degree | parent total width | virtual total width | worst virtual chunk |
| ---: | ---: | ---: | ---: |
| 12 | `6.698052922695822871E-1` | `1.849680600000000000E-13` | 0 |
| 16 | `3.173397702696087729E-1` | `4.323000000000000000E-17` | 0 |

## Cells

| family | row | d | chunk | feasible degrees | best margin degree |
| --- | ---: | ---: | ---: | --- | ---: |
| `control_finite` | 0 | `0.00` | 0 | `-` | 16 |

## Best Degree Details

### control_finite row 0 chunk 0

- chunk interval: `[-3.887204663947871600E-1, -3.887204663947871600E-1]`
- degree: `16`
- sampled max residual: `1.442453501225494422E-2`
- remainder candidate: `1.586698851348043864E-2`
- lower model integral: `-5.428347431903619699E-1`
- upper model integral: `-2.254949729207531970E-1`
- current chunk width: `0.000000000000000000e+00`
- model interval width: `3.173397702696087729E-1`
- extra chunk width needed: `3.173397702696087452e-01`
- lower margin: `-1.541142767955748227e-01`
- upper margin: `-1.632254934740339503e-01`
- required remainder cap: `-4.555608339229577424e-04`
- failure mode: `model_interval_wider_than_current_chunk_interval`
- fits sampled residual and integral: `False`

#### Virtual Subchunk Summary

| degree | subchunks | total width | extra parent width | max sampled residual | failure mode |
| ---: | ---: | ---: | ---: | ---: | --- |
| 12 | 50 | `1.849680600000000000E-13` | `1.849680600000000000E-13` | `3.269075968025613488E-13` | `split_model_interval_wider_than_parent_chunk_interval` |
| 16 | 50 | `4.323000000000000000E-17` | `4.323000000000000000E-17` | `9.194107717725049780E-17` | `split_model_interval_wider_than_parent_chunk_interval` |

