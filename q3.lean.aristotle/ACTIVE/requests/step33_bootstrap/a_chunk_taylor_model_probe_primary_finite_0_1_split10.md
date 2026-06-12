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
| `primary_finite` | 0 | `0.00` | 1 | `-` | 16 |

## Best Degree Details

### primary_finite row 0 chunk 1

- chunk interval: `[2.615058139399545823E-1, 2.615058139399545823E-1]`
- degree: `16`
- sampled max residual: `4.562322741819002658e-15`
- remainder candidate: `5.018555016000903713e-15`
- lower model integral: `2.615058139399040193e-01`
- upper model integral: `2.615058139400043835e-01`
- current chunk width: `0.000000000000000000e+00`
- model interval width: `1.003641614261141513e-13`
- extra chunk width needed: `1.003641614261141513e-13`
- lower margin: `-5.057065877167588042e-14`
- upper margin: `-4.979350265443827084e-14`
- required remainder cap: `-3.885780586188047645e-17`
- failure mode: `model_interval_wider_than_current_chunk_interval`
- fits sampled residual and integral: `False`

#### Virtual Subchunk Summary

| degree | subchunks | total width | extra parent width | max sampled residual | failure mode |
| ---: | ---: | ---: | ---: | ---: | --- |
| 8 | 10 | `2.720046410331633524e-15` | `2.720046410331633524e-15` | `1.561251128379126385e-16` | `split_model_interval_wider_than_parent_chunk_interval` |
| 12 | 10 | `7.216449660063517513e-16` | `7.216449660063517513e-16` | `5.551115123125782702e-17` | `split_model_interval_wider_than_parent_chunk_interval` |
| 16 | 10 | `8.881784197001252323e-16` | `8.881784197001252323e-16` | `4.510281037539698445e-17` | `split_model_interval_wider_than_parent_chunk_interval` |

