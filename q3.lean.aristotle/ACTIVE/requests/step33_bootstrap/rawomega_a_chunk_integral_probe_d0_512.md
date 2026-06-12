# Step33 A chunk integral probe

Diagnostic only: external acb/Arb interval evidence, not a Lean proof.

## Summary

- source: `raw_step22`
- families checked: 2
- rows checked: 2
- rows failed: 2
- rows absorbable by local target slack: 2
- worst excess: `2.866866607280471236E-19`
- full chunk rows: `True`

## Families

| family | rows | failed | slack-absorbable | worst excess |
| --- | ---: | ---: | ---: | ---: |
| `primary_finite` | 1 | 1 | 1 | `2.866866607280471236E-19` |
| `control_tail` | 1 | 1 | 1 | `2.871550136268279045E-37` |

## Worst failures

| family | idx | d | sign | lower excess | upper excess | excess | available slack | absorbable |
| --- | ---: | ---: | --- | ---: | ---: | ---: | ---: | --- |
| `primary_finite` | 0 | `0.00` | `positive` | `0.000000000000000000E+0` | `2.866866607280471236E-19` | `2.866866607280471236E-19` | `1.326048519512948610E-18` | `True` |
| `control_tail` | 0 | `0.00` | `positive` | `0.000000000000000000E+0` | `2.871550136268279045E-37` | `2.871550136268279045E-37` | `7.753281601564634378E-17` | `True` |

## Local target refresh candidates

These rows do not fit the current generated target interval, but the
excess is smaller than the already available payload slack.  Refreshing
the local raw-Omega arithmetic target for these rows would not require
A CSV, ARadius, radius-floor, or LDL changes.

| family | idx | suggested lower | suggested upper | slack after refresh |
| --- | ---: | ---: | ---: | ---: |
| `primary_finite` | 0 | `1.233644453639219465E-1` | `1.233644453639219558E-1` | `1.039361858784901486E-18` |
| `control_tail` | 0 | `2.390275099671697075E-18` | `2.390275099671697075E-18` | `7.753281601564634378E-17` |
