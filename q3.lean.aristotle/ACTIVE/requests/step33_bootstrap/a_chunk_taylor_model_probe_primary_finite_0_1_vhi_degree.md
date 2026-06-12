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
| `primary_finite` | 0 | `0.00` | 1 | `-` | 24 |

## Best Degree Details

### primary_finite row 0 chunk 1

- chunk interval: `[2.615058139399545823E-1, 2.615058139399545823E-1]`
- degree: `24`
- sampled max residual: `2.151057110211240797e-16`
- remainder candidate: `2.366162821232364975e-16`
- lower model integral: `2.615058139399515369e-01`
- upper model integral: `2.615058139399563109e-01`
- current chunk width: `0.000000000000000000e+00`
- model interval width: `4.773959005888173124e-15`
- extra chunk width needed: `4.773959005888173124e-15`
- lower margin: `-3.053113317719180486e-15`
- upper margin: `-1.720845688168992638e-15`
- required remainder cap: `-6.661338147750938996e-17`
- failure mode: `model_interval_wider_than_current_chunk_interval`
- fits sampled residual and integral: `False`

