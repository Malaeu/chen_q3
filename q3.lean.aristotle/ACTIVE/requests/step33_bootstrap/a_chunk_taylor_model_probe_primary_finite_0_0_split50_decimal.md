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
| 12 | `6.105941038065165599E-1` | `1.686170800000000000E-13` | 0 |
| 16 | `2.892866741291894954E-1` | `3.941000000000000000E-17` | 0 |

## Cells

| family | row | d | chunk | feasible degrees | best margin degree |
| --- | ---: | ---: | ---: | --- | ---: |
| `primary_finite` | 0 | `0.00` | 0 | `-` | 16 |

## Best Degree Details

### primary_finite row 0 chunk 0

- chunk interval: `[-3.535346901998863369E-1, -3.535346901998863369E-1]`
- degree: `16`
- sampled max residual: `1.314939427859952252E-2`
- remainder candidate: `1.446433370645947477E-2`
- lower model integral: `-4.940251351143627267E-1`
- upper model integral: `-2.047384609851732313E-1`
- current chunk width: `0.000000000000000000e+00`
- model interval width: `2.892866741291894954E-1`
- extra chunk width needed: `2.892866741291895138e-01`
- lower margin: `-1.404904449144764311e-01`
- upper margin: `-1.487962292147130827e-01`
- required remainder cap: `-4.152892150118325581e-04`
- failure mode: `model_interval_wider_than_current_chunk_interval`
- fits sampled residual and integral: `False`

#### Virtual Subchunk Summary

| degree | subchunks | total width | extra parent width | max sampled residual | failure mode |
| ---: | ---: | ---: | ---: | ---: | --- |
| 12 | 50 | `1.686170800000000000E-13` | `1.686170800000000000E-13` | `2.980092889591301529E-13` | `split_model_interval_wider_than_parent_chunk_interval` |
| 16 | 50 | `3.941000000000000000E-17` | `3.941000000000000000E-17` | `8.381357699770360593E-17` | `split_model_interval_wider_than_parent_chunk_interval` |

