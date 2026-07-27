# SOFT_L2 micro lag ledgers — `(12,120)` and `(14,120)`

Status: `MEASURED / REGISTERED_PREDICTION_SUPPORTED / NOT_RH`

Authority and continuation context:
`SOFT_L2_PRO_VERDICT_ROUND11_PARITY_2026-07-13.md`, materialized verbatim.

## Source typing

The persisted full `xi1` eigenvector used by the earlier `(13,120)` ledger is
not available for these two cells.  The present diagnostic therefore uses:

```text
q      = persisted high-precision portable_k1_(m,120),
mu     = persisted mu1 from lambda_sq_(m)_N_120.json,
status = portable_k1 / mu1 diagnostic proxy,
         not a full-ground eigenvector certificate.
```

No exact finite-matrix `t=0` anchor is claimed for either new cell.

## Registered judge

On the pre-registered lag grid `t/L=k/6`, `k=-6,...,6`, score the outer half
`|t|>=L/2`:

```text
window and aggregate remainder have opposite real signs,
max |residual|/(|window|+|remainder|) < 1e-4.
```

The result is:

| cell | max outer relative residual | `t=0` raw residual | window at `t=L` | remainder at `t=L` | outcome |
|---|---:|---:|---:|---:|---|
| `(12,120)` | `2.2652159421e-6` | `3.8916948280e-54` | `-2.60903493036325` | `+2.60903493036325` | `SUPPORTED` |
| `(14,120)` | `4.50842271497e-7` | `9.2416007678e-65` | `-2.83438303809083` | `+2.83438303809083` | `SUPPORTED` |

The sign opposition holds at all eight registered outer-grid points in each
cell.  At `|t|=L`, the residuals are approximately `-3.08e-54` and
`-7.52e-65`, respectively.

Thus both cells reproduce the `(13,120)` outer-lag anti-cancellation pattern:
large window and aggregate non-window rows cancel to a residual numerically
near zero.

## Interpretation firewall

The aggregate remainder is defined as `residual-window`, so its algebraic sum
with the window row is not independent evidence.  The diagnostic observation
is the scale separation: on the outer half-grid, the residual is at most
`2.27e-6` of the combined component magnitude.  This does not prove the
Round-11 `CombinedResidualFactorization`, source continuity, UREL, component
smallness, or RH.  Nor are the new proxy ledgers promoted to exact ground-state
certificates.

Artifacts:

- `SOFT_L2_LAG_LEDGER_12_120.csv/.json`;
- `SOFT_L2_LAG_LEDGER_14_120.csv/.json`;
- `soft_l2_projection_measurements.py --micro-lag`.

```text
SOFT_L2_LAG_MICRO_LEDGERS_COMPLETE
REGISTERED_PREDICTION_SUPPORTED_12_120_14_120
NOT_RH
BUS_010_CREATED=false
```

Bus 010 was not created.
