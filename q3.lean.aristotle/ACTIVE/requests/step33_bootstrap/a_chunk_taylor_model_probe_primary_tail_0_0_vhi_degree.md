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
| `primary_tail` | 0 | `0.00` | 0 | `-` | 22 |

## Best Degree Details

### primary_tail row 0 chunk 0

- chunk interval: `[1.088613911944200701E-29, 1.088613911944221150E-29]`
- degree: `22`
- sampled max residual: `1.121038771459853657e-44`
- remainder candidate: `1.333142648605839229e-44`
- lower model integral: `1.088613911944197736e-29`
- upper model integral: `1.088613911944224361e-29`
- current chunk width: `2.044899999999999842e-43`
- model interval width: `2.662467082217152435e-43`
- extra chunk width needed: `6.175670822171525931e-44`
- lower margin: `-2.942726775082115849e-44`
- upper margin: `-3.222986467947079263e-44`
- required remainder cap: `1.008934894313868316e-44`
- failure mode: `model_interval_wider_than_current_chunk_interval`
- fits sampled residual and integral: `False`

