# Step33 A chunk integral probe

Diagnostic only: external acb/Arb interval evidence, not a Lean proof.

## Summary

- source: `raw_step22`
- families checked: 4
- rows checked: 4
- rows failed: 2
- worst excess: `2.866866607280471236E-19`
- full chunk rows: `True`

## Families

| family | rows | failed | worst excess |
| --- | ---: | ---: | ---: |
| `primary_finite` | 1 | 1 | `2.866866607280471236E-19` |
| `primary_tail` | 1 | 0 | `0.000000000000000000E+0` |
| `control_finite` | 1 | 0 | `0.000000000000000000E+0` |
| `control_tail` | 1 | 1 | `2.873474329584073090E-37` |

## Worst failures

| family | idx | d | sign | lower excess | upper excess | excess |
| --- | ---: | ---: | --- | ---: | ---: | ---: |
| `primary_finite` | 0 | `0.00` | `positive` | `0.000000000000000000E+0` | `2.866866607280471236E-19` | `2.866866607280471236E-19` |
| `control_tail` | 0 | `0.00` | `positive` | `0.000000000000000000E+0` | `2.873474329584073090E-37` | `2.873474329584073090E-37` |
