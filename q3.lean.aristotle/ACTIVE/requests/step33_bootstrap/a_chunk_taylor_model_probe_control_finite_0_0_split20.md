# Step33A.1-A Taylor Model Probe

Diagnostic only: sampled Arb/acb evidence for candidate Taylor/model
data.  This is not a Lean proof and does not emit payload declarations.

## Summary

- source: `raw_step22`
- cells checked: 1
- cells with sampled feasible degree: 0
- degrees: `12,16`
- fit samples: 33
- check samples: 121

## Cells

| family | row | d | chunk | feasible degrees | best margin degree |
| --- | ---: | ---: | ---: | --- | ---: |
| `control_finite` | 0 | `0.00` | 0 | `-` | 16 |

## Best Degree Details

### control_finite row 0 chunk 0

- chunk interval: `[-3.887204663947871600E-1, -3.887204663947871600E-1]`
- degree: `16`
- sampled max residual: `9.171540255614729631e-04`
- remainder candidate: `1.008869428117620259e-03`
- lower model integral: `-3.990387516650910626e-01`
- upper model integral: `-3.788613631027386575e-01`
- current chunk width: `0.000000000000000000e+00`
- model interval width: `2.017738856235240519e-02`
- extra chunk width needed: `2.017738856235240519e-02`
- lower margin: `-1.031828527030392850e-02`
- upper margin: `-9.859103292048476685e-03`
- required remainder cap: `-2.295909891277259017e-05`
- failure mode: `model_interval_wider_than_current_chunk_interval`
- fits sampled residual and integral: `False`

#### Virtual Subchunk Summary

| degree | subchunks | total width | extra parent width | max sampled residual | failure mode |
| ---: | ---: | ---: | ---: | ---: | --- |
| 12 | 20 | `1.366721347206834025e-09` | `1.366721347206834025e-09` | `1.238586622154258521e-09` | `split_model_interval_wider_than_parent_chunk_interval` |
| 16 | 20 | `1.278138705984588341e-11` | `1.278138705984588341e-11` | `1.161365448254514376e-11` | `split_model_interval_wider_than_parent_chunk_interval` |

