# Step33 A refined row recenter containment audit

Diagnostic only: refreshed finite-row target checked against imported A recenter containment.
No A CSV, ARadius, radius-floor, LDL, or global payload radius data is mutated.

## Summary

- block: `primary`
- family: `primary_finite`
- row: `0`
- distance: `0.00`
- status: `pass`

## Recenter inequality

```text
finiteRadius + tailRadius + |finiteMid - importedA| <= importedARadius
```

| target | finite mid | finite radius | tail radius | center error | required radius | imported radius | margin | excess |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| before | `1.233644453639219512E-1` | `4.700000000000000000E-18` | `1.329645459799432920E-18` | `1.000000000000000000E-19` | `6.129645459799432920E-18` | `7.116332121107148949E-18` | `9.866866613077160290E-19` | `0.000000000000000000E+0` |
| refreshed | `1.233644453639219512E-1` | `4.700000000000000000E-18` | `1.329645459799432920E-18` | `1.000000000000000000E-19` | `6.129645459799432920E-18` | `7.116332121107148949E-18` | `9.866866613077160290E-19` | `0.000000000000000000E+0` |

## Route conclusion

The refreshed finite-row interval still fits the existing imported A radius.
This row can use the interval-recenter receiver without global radius mutation.
This is not full A hbox closure; remaining rows/families still need the same check and Lean payload.
