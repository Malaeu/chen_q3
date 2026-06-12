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
| `primary_finite` | 0 | `0.00` | 0 | `-` | 16 |

## Best Degree Details

### primary_finite row 0 chunk 0

- chunk interval: `[-3.535346901998863369E-1, -3.535346901998863369E-1]`
- degree: `16`
- sampled max residual: `8.360776696360039395e-04`
- remainder candidate: `9.196854365996043985e-04`
- lower model integral: `-3.629408396223797739e-01`
- upper model integral: `-3.445471308903876873e-01`
- current chunk width: `0.000000000000000000e+00`
- model interval width: `1.839370873199208667e-02`
- extra chunk width needed: `1.839370873199208667e-02`
- lower margin: `-9.406149422493459422e-03`
- upper margin: `-8.987559309498627247e-03`
- required remainder cap: `-2.092950564974161012e-05`
- failure mode: `model_interval_wider_than_current_chunk_interval`
- fits sampled residual and integral: `False`

#### Virtual Subchunk Summary

| degree | subchunks | total width | extra parent width | max sampled residual | failure mode |
| ---: | ---: | ---: | ---: | ---: | --- |
| 12 | 20 | `1.245904657221075240e-09` | `1.245904657221075240e-09` | `1.129096593999179277e-09` | `split_model_interval_wider_than_parent_chunk_interval` |
| 16 | 20 | `1.165195717689471167e-11` | `1.165195717689471167e-11` | `1.058730880743041780e-11` | `split_model_interval_wider_than_parent_chunk_interval` |

