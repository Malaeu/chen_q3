# Step33 A refined row recenter containment audit

Diagnostic only: refreshed finite-row target checked against imported A recenter containment.
No A CSV, ARadius, radius-floor, LDL, or global payload radius data is mutated.

## Summary

- block: `primary`
- family: `primary_finite`
- row: `0`
- distance: `0.00`
- status: `fail`

## Recenter inequality

```text
finiteRadius + tailRadius + |finiteMid - importedA| <= importedARadius
```

| target | finite mid | finite radius | tail radius | center error | required radius | imported radius | margin | excess |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| before | `1.233644453639219512E-1` | `4.700000000000000000E-18` | `1.329645459799432920E-18` | `1.000000000000000000E-19` | `6.129645459799432920E-18` | `7.116332121107148949E-18` | `9.866866613077160290E-19` | `0.000000000000000000E+0` |
| refreshed | `1.233644453639219536E-1` | `7.050000000000000000E-18` | `1.329645459799432920E-18` | `2.250000000000000000E-18` | `1.062964545979943292E-17` | `7.116332121107148949E-18` | `-3.513313338692283971E-18` | `3.513313338692283971E-18` |

## Route conclusion

The refreshed finite-row interval does not fit the existing imported A radius.
Do not widen global ARadius as a proof patch.
Report this row as the next exact refreshed-row containment blocker.
