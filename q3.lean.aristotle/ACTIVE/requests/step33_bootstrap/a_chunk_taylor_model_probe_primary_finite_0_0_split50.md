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
| `primary_finite` | 0 | `0.00` | 0 | `-` | 16 |

## Best Degree Details

### primary_finite row 0 chunk 0

- chunk interval: `[-3.535346901998863369E-1, -3.535346901998863369E-1]`
- degree: `16`
- sampled max residual: `2.507272469082610922e-03`
- remainder candidate: `2.757999715990872187e-03`
- lower model integral: `-3.807376479739739694e-01`
- upper model integral: `-3.255776536541565291e-01`
- current chunk width: `0.000000000000000000e+00`
- model interval width: `5.515999431981744028e-02`
- extra chunk width needed: `5.515999431981744028e-02`
- lower margin: `-2.720295777408765492e-02`
- upper margin: `-2.795703654572978536e-02`
- required remainder cap: `-3.770393858210652069e-05`
- failure mode: `model_interval_wider_than_current_chunk_interval`
- fits sampled residual and integral: `False`

#### Virtual Subchunk Summary

| degree | subchunks | total width | extra parent width | max sampled residual | failure mode |
| ---: | ---: | ---: | ---: | ---: | --- |
| 12 | 50 | `2.864375403532903874e-14` | `2.864375403532903874e-14` | `4.801714581503802037e-14` | `split_model_interval_wider_than_parent_chunk_interval` |
| 16 | 50 | `2.053912595556539600e-15` | `2.053912595556539600e-15` | `6.938893903907228378e-16` | `split_model_interval_wider_than_parent_chunk_interval` |

