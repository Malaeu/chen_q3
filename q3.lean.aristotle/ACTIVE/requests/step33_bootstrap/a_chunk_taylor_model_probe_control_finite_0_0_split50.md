# Step33A.1-A Taylor Model Probe

Diagnostic only: sampled Arb/acb evidence for candidate Taylor/model
data.  This is not a Lean proof and does not emit payload declarations.

## Summary

- source: `raw_step22`
- cells checked: 1
- cells with sampled feasible degree: 0
- degrees: `12,16`
- fit samples: 25
- check samples: 81

## Cells

| family | row | d | chunk | feasible degrees | best margin degree |
| --- | ---: | ---: | ---: | --- | ---: |
| `control_finite` | 0 | `0.00` | 0 | `-` | 16 |

## Best Degree Details

### control_finite row 0 chunk 0

- chunk interval: `[-3.887204663947871600E-1, -3.887204663947871600E-1]`
- degree: `16`
- sampled max residual: `2.750405254570431612e-03`
- remainder candidate: `3.025445780027475207e-03`
- lower model integral: `-4.185613236356364175e-01`
- upper model integral: `-3.580524080350869220e-01`
- current chunk width: `0.000000000000000000e+00`
- model interval width: `6.050891560054949547e-02`
- extra chunk width needed: `6.050891560054949547e-02`
- lower margin: `-2.984085724084928337e-02`
- upper margin: `-3.066805835970021210e-02`
- required remainder cap: `-4.136005594254643647e-05`
- failure mode: `model_interval_wider_than_current_chunk_interval`
- fits sampled residual and integral: `False`

#### Virtual Subchunk Summary

| degree | subchunks | total width | extra parent width | max sampled residual | failure mode |
| ---: | ---: | ---: | ---: | ---: | --- |
| 12 | 50 | `3.103073353827312530e-14` | `3.103073353827312530e-14` | `5.273559366969493567e-14` | `split_model_interval_wider_than_parent_chunk_interval` |
| 16 | 50 | `2.553512956637860043e-15` | `2.553512956637860043e-15` | `8.326672684688674053e-16` | `split_model_interval_wider_than_parent_chunk_interval` |

