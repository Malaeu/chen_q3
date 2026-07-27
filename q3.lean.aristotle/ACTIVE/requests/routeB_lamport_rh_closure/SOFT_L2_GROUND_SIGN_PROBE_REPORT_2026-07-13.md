# SOFT_L2 GroundSignProbe report

Status: `SIGN_CONSTANT / DIAGNOSTIC_ONLY / NOT_RH`

The registered judge was executed on 4096 equally spaced samples of every
packet used by the all-cell edge profile, restricted to the interior
`0.05L <= u <= 0.95L`.  Each packet was globally phase-oriented by making its
largest sampled absolute value positive real.  The judge is

```text
SIGN_CHANGING iff max(0,-min Re(q))/max Re(q) > 1e-6;
otherwise SIGN_CONSTANT.
```

All seven rows return `SIGN_CONSTANT`.  The two float64 rows have negative
extrema only at relative scale `5.39e-15` and `3.31e-15`, far below the
registered `1e-6` threshold; every other row has no sampled negative value.
The finite ground row `ground_xi1_m13_N120` has zero opposite-sign extremum,
zero significant negative samples, and maximum imaginary leakage relative to
the maximum absolute value `1.36e-16`.

## Provenance guard

The seven-row battery contains six trial/diagnostic `kTrial` packets and one
persisted full finite ground packet, `ground_xi1_m13_N120`.  Therefore the
aggregate result is an all-carrier numerical diagnostic, not a theorem that
all unsaved finite grounds have constant sign.  No trial row is promoted to a
ground selector.  A 4096-point grid also does not prove continuum positivity.

Artifacts:

- `SOFT_L2_GROUND_SIGN_PROBE.csv`
- `SOFT_L2_GROUND_SIGN_PROBE.json`
- `soft_l2_round13_measurements.py`
- `validate_soft_l2_round13_measurements.py`

`NOT_RH`.
