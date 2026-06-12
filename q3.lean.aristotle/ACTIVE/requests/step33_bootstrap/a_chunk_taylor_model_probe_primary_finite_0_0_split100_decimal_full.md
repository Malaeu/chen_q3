# Step33A.1-A Taylor Model Probe

Diagnostic only: sampled Arb/acb evidence for candidate Taylor/model
data.  This is not a Lean proof and does not emit payload declarations.

## Summary

- source: `raw_step22`
- cells checked: 1
- cells with sampled feasible degree: 0
- degrees: `16`
- fit samples: 17
- check samples: 61

## Degree Aggregates

| degree | parent total width | virtual total width | worst virtual chunk |
| ---: | ---: | ---: | ---: |
| 16 | `3.113516332435091531E-1` | `1.000000000000000000E-20` | 0 |

## Cells

| family | row | d | chunk | feasible degrees | best margin degree |
| --- | ---: | ---: | ---: | --- | ---: |
| `primary_finite` | 0 | `0.00` | 0 | `-` | 16 |

## Best Degree Details

### primary_finite row 0 chunk 0

- chunk interval: `[-3.535346901998863369E-1, -3.535346901998863369E-1]`
- degree: `16`
- sampled max residual: `1.415234696561405241E-2`
- remainder candidate: `1.556758166217545766E-2`
- lower model integral: `-5.050576146715225556E-1`
- upper model integral: `-1.937059814280134025E-1`
- current chunk width: `0.000000000000000000e+00`
- model interval width: `3.113516332435091531E-1`
- extra chunk width needed: `3.113516332435091738e-01`
- lower margin: `-1.515229244716362333e-01`
- upper margin: `-1.598287087718729127e-01`
- required remainder cap: `-4.152892150118325581e-04`
- failure mode: `model_interval_wider_than_current_chunk_interval`
- fits sampled residual and integral: `False`

#### Virtual Subchunk Summary

| degree | subchunks | total width | extra parent width | max sampled residual | failure mode |
| ---: | ---: | ---: | ---: | ---: | --- |
| 16 | 100 | `1.000000000000000000E-20` | `1.000000000000000000E-20` | `1.893260659781758254E-21` | `split_model_interval_wider_than_parent_chunk_interval` |
