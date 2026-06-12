# Step33 A chunk integral probe

Diagnostic only: external acb/Arb interval evidence, not a Lean proof.

## Summary

- source: `centered_receiver`
- families checked: 2
- rows checked: 4
- rows failed: 4
- worst excess: `7.902110587559563425E+1`
- full chunk rows: `True`

## Families

| family | rows | failed | worst excess |
| --- | ---: | ---: | ---: |
| `primary_finite` | 2 | 2 | `7.902110587559563425E+1` |
| `control_finite` | 2 | 2 | `7.523137907465061464E+1` |

## Worst failures

| family | idx | d | sign | lower excess | upper excess | excess |
| --- | ---: | ---: | --- | ---: | ---: | ---: |
| `primary_finite` | 0 | `0.00` | `positive` | `7.902110587559563425E+1` | `0.000000000000000000E+0` | `7.902110587559563425E+1` |
| `control_finite` | 0 | `0.00` | `positive` | `7.523137907465061464E+1` | `0.000000000000000000E+0` | `7.523137907465061464E+1` |
| `control_finite` | 1 | `0.25` | `negative` | `0.000000000000000000E+0` | `1.780869526361660547E+1` | `1.780869526361660547E+1` |
| `primary_finite` | 1 | `0.25` | `negative` | `0.000000000000000000E+0` | `1.616291113275570035E+1` | `1.616291113275570035E+1` |
