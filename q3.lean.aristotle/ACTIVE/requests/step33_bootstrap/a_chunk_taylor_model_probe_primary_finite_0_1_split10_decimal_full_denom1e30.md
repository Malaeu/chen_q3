# Step33A.1-A Taylor Model Probe

Diagnostic only: sampled Arb/acb evidence for candidate Taylor/model
data.  This is not a Lean proof and does not emit payload declarations.

## Summary

- source: `raw_step22`
- cells checked: 1
- cells with sampled feasible degree: 0
- degrees: `16`
- fit samples: 17
- check samples: 81

## Degree Aggregates

| degree | parent total width | virtual total width | worst virtual chunk |
| ---: | ---: | ---: | ---: |
| 16 | `1.109195618453807312E-12` | `0.000000000000000000E-2` | None |

## Cells

| family | row | d | chunk | feasible degrees | best margin degree |
| --- | ---: | ---: | ---: | --- | ---: |
| `primary_finite` | 0 | `0.00` | 1 | `-` | 16 |

## Best Degree Details

### primary_finite row 0 chunk 1

- chunk interval: `[2.615058139399545823E-1, 2.615058139399545823E-1]`
- degree: `16`
- sampled max residual: `5.041798265699124143E-14`
- remainder candidate: `5.545978092269036558E-14`
- lower model integral: `2.615058139393924298E-1`
- upper model integral: `2.615058139405016255E-1`
- current chunk width: `0.000000000000000000e+00`
- model interval width: `1.109195618453807312E-12`
- extra chunk width needed: `1.109195618453807398e-12`
- lower margin: `-5.621614285189480142e-13`
- upper margin: `-5.470623953840458853e-13`
- required remainder cap: `-7.549516567451064278e-16`
- failure mode: `model_interval_wider_than_current_chunk_interval`
- fits sampled residual and integral: `False`

#### Virtual Subchunk Summary

| degree | subchunks | total width | extra parent width | max sampled residual | failure mode |
| ---: | ---: | ---: | ---: | ---: | --- |
| 16 | 10 | `0.000000000000000000E-2` | `0.000000000000000000E+18` | `1.252580481454165961E-28` | `split_integral_center_mismatch` |

