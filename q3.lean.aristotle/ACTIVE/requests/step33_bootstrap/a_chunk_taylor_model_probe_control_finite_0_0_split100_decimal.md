# Step33A.1-A Taylor Model Probe

Diagnostic only: sampled Arb/acb evidence for candidate Taylor/model
data.  This is not a Lean proof and does not emit payload declarations.

## Summary

- source: `raw_step22`
- cells checked: 1
- cells with sampled feasible degree: 0
- degrees: `16,20`
- fit samples: 17
- check samples: 61

## Degree Aggregates

| degree | parent total width | virtual total width | worst virtual chunk |
| ---: | ---: | ---: | ---: |
| 16 | `3.415444319874503922E-1` | `0.000000000000000000E-5` | None |
| 20 | `3.510934440513406027E-2` | `0.000000000000000000E-5` | None |

## Cells

| family | row | d | chunk | feasible degrees | best margin degree |
| --- | ---: | ---: | ---: | --- | ---: |
| `control_finite` | 0 | `0.00` | 0 | `-` | 20 |

## Best Degree Details

### control_finite row 0 chunk 0

- chunk interval: `[-3.887204663947871600E-1, -3.887204663947871600E-1]`
- degree: `20`
- sampled max residual: `1.595879291142457285E-3`
- remainder candidate: `1.755467220256703014E-3`
- lower model integral: `-4.060734404445802937E-1`
- upper model integral: `-3.709640960394462335E-1`
- current chunk width: `0.000000000000000000e+00`
- model interval width: `3.510934440513406027E-2`
- extra chunk width needed: `3.510934440513405891e-02`
- lower margin: `-1.735297404979313507e-02`
- upper margin: `-1.775637035534088914e-02`
- required remainder cap: `-2.016981527738770374e-05`
- failure mode: `model_interval_wider_than_current_chunk_interval`
- fits sampled residual and integral: `False`

#### Virtual Subchunk Summary

| degree | subchunks | total width | extra parent width | max sampled residual | failure mode |
| ---: | ---: | ---: | ---: | ---: | --- |
| 16 | 100 | `0.000000000000000000E-5` | `0.000000000000000000E+18` | `2.076852351050671186E-21` | `split_integral_center_mismatch` |
| 20 | 100 | `0.000000000000000000E-5` | `0.000000000000000000E+18` | `4.123814864666332397E-26` | `split_integral_center_mismatch` |

