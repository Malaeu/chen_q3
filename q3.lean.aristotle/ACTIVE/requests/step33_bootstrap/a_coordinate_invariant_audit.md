# Step33A.1-A Coordinate-Invariant Audit

This is a non-mutating route audit. It reads the centered-receiver smoke
artifact and checks whether the remaining D option can be a simple
distance/frequency/sign/scale fix.

It does not edit A CSV, `ARadius`, radius-floor, LDL, `Q3.Main`, or proof payloads.

## Decision

- simple coordinate/frequency D map: `rejected`
- constant sign/scale fit: `rejected`
- recommendation: `No simple D theorem from d/frequency/sign/scale evidence. Choose B only if a Lean semantic theorem changes the receiver/assembler to raw Step22; otherwise choose C one-time recert/migration to the centered receiver convention.`

## Family Evidence

| family | window | d=0 receiver | d=0 target | d=0 error | -receiver error | ratio d=0 | ratio d=0.25 | ratio gap |
| --- | --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| primary_finite | -2.600000000000000000E+2..2.600000000000000000E+2 | -7.889774143023171231E+1 | 1.233644453639219510E-1 | 7.902110587559563426E+1 | 7.877437698486779036E+1 | -1.563599199769382369E-3 | -2.782002155726642679E-2 | 2.625642235749704442E-2 |
| control_finite | -2.600000000000000000E+2..2.600000000000000000E+2 | -7.520513017099183980E+1 | 2.624890365877484420E-2 | 7.523137907465061464E+1 | 7.517888126733306496E+1 | -3.490307589268635342E-4 | -2.813338629093975767E-2 | 2.778435553201289414E-2 |

## Interpretation

The `d = 0` row is invariant under any rewrite that only changes the
distance/frequency/cosine coordinate, because the cosine factor is already
`1`.  The observed mismatch is order `75-79`, so a pure coordinate theorem
cannot rescue the current imported raw Step22 targets.

A sign flip also fails at `d = 0`, and a constant scale fit is not stable
between `d = 0` and `d = 0.25`.  The remaining honest choices are:

- `B`: prove the Step33 receiver/assembler should semantically use raw Step22;
- `C`: recertify/migrate A-dependent finite data to the centered receiver convention.
