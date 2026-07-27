# B0_VALUE_PROBE

Status: `DIAGNOSTIC_ONLY / FIT_NOT_LAW / NOT_RH`.
Verdict: `SAMPLED_INF_GT_DELTA_NO_COMPENSATION_DIAGNOSTIC`.

| m | N | |c0| | |B(0)| | source |
|---:|---:|---:|---:|---|
| 13 | 90 | `0.539977000704` | `0.864797966349` | persisted |
| 13 | 120 | `0.539977000704` | `0.864797966349` | persisted |
| 14 | 120 | `0.532997860528` | `0.865864388277` | persisted |
| 53 | 120 | `0.439500892195` | `0.875731518364` | persisted |
| 101 | 120 | `0.408399411048` | `0.877357575531` | persisted |
| 149 | 120 | `0.392468341889` | `0.877932145414` | fresh |
| 197 | 120 | `0.382082887529` | `0.878225951421` | fresh |
| 257 | 120 | `0.372907438694` | `0.878438550145` | fresh |

Fit:

```text
|B_(m,120)(0)| ~= exp(-0.157623068564) * m^(0.00543083895502)
alpha_if_decay = 0
R^2 = 0.920977570406
sampled min = 0.864797966349
sampled max = 0.878438550145
delta_diagnostic = 0.85
```

The finite sample supports an uncompensated S1 statement.  It is not a proof
of a uniform positive lower bound; the theorem-facing obligation remains an
explicit lower-bound input.
