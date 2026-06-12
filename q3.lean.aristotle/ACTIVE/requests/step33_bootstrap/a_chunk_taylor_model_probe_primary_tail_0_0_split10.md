# Step33A.1-A Taylor Model Probe

Diagnostic only: sampled Arb/acb evidence for candidate Taylor/model
data.  This is not a Lean proof and does not emit payload declarations.

## Summary

- source: `raw_step22`
- cells checked: 1
- cells with sampled feasible degree: 0
- degrees: `8,12,16`
- fit samples: 33
- check samples: 121

## Cells

| family | row | d | chunk | feasible degrees | best margin degree |
| --- | ---: | ---: | ---: | --- | ---: |
| `primary_tail` | 0 | `0.00` | 0 | `-` | 16 |

## Best Degree Details

### primary_tail row 0 chunk 0

- chunk interval: `[1.088613911944200701E-29, 1.088613911944221150E-29]`
- degree: `16`
- sampled max residual: `2.706972321444108625e-40`
- remainder candidate: `2.977679553588519628e-40`
- lower model integral: `1.088613911647546635e-29`
- upper model integral: `1.088613912243082508e-29`
- current chunk width: `2.044899999999999842e-43`
- model interval width: `5.955358725355539522e-39`
- extra chunk width needed: `5.955154235355539304e-39`
- lower margin: `-2.966540441184851790e-39`
- upper margin: `-2.988613694594896309e-39`
- required remainder cap: `-1.093433191712654697e-42`
- failure mode: `model_interval_wider_than_current_chunk_interval`
- fits sampled residual and integral: `False`

#### Virtual Subchunk Summary

| degree | subchunks | total width | extra parent width | max sampled residual | failure mode |
| ---: | ---: | ---: | ---: | ---: | --- |
| 8 | 10 | `1.747601353813409114e-40` | `1.745556453813409175e-40` | `2.906573274702535569e-41` | `split_model_interval_wider_than_parent_chunk_interval` |
| 12 | 10 | `8.127531093083939011e-44` | `0.000000000000000000e+00` | `1.891752926838503046e-44` | `sampled_feasible` |
| 16 | 10 | `9.388699710976274375e-44` | `0.000000000000000000e+00` | `2.312142466135948167e-44` | `sampled_feasible` |

