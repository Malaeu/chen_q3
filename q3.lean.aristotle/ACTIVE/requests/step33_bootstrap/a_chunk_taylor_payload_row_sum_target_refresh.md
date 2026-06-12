# Step33A.1-A Serialized Row-Sum Target Refresh

This audit compares serialized `chunkLower` / `chunkUpper` sums against
the current worklist targets and emits a probe-compatible local refresh.

## Verdict

- schema: `q3_psdpd_step33_a_chunk_integral_probe.v1`
- refresh rows: `71`
- preserved existing refresh rows: `71`
- additional serialized refresh rows: `0`
- serialized failure sides: `0`
- blocked rows: `0`
- worst extra needed slack: `0.000000000000000000E+0`

## Families

| family | refresh rows | blocked | slack-absorbable |
| --- | ---: | ---: | ---: |
| primary_finite | 13 | 0 | 13 |
| primary_tail | 21 | 0 | 21 |
| control_finite | 14 | 0 | 14 |
| control_tail | 23 | 0 | 23 |

## Route Guard

- local target refresh only; no A CSV / ARadius / radius-floor / LDL mutation
- generated arithmetic/worklist must be regenerated from this file before row-sum proof terms are trusted
- generated PayloadFin must still wait for Taylor/model analytic proof data
