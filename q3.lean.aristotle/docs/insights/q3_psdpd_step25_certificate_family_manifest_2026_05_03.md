# Step 25 -- Certificate-family manifest

## Goal

Turn interval-backed finite blocks into a managed certificate family.

This does not create new certificates.  It records:

- block parameters;
- midpoint/radius CSV paths;
- SHA256 hashes;
- Step 18 penalty-guard safe lower bounds;
- PASS/FAIL status;
- saved Step 18 output for audit.

## Files

- seed blocks:
  `docs/insights/q3_psdpd_family_blocks_seed.csv`
- manifest:
  `docs/insights/q3_psdpd_certificate_family_manifest.csv`
- summary:
  `docs/insights/q3_psdpd_certificate_family_manifest.json`
- Step 18 outputs:
  `docs/insights/q3_psdpd_family_step18_outputs/`

## Current family

| role | block_id | k | ell | delta | kappa | theta | status | Dtheta safe | Rkappa safe |
|---|---|---:|---:|---:|---:|---:|---|---:|---:|
| primary | `psdpd_L3_k11_ell030_delta025_theta1e4` | 11 | 0.30 | 0.25 | 3.25 | `1e-4` | PASS | `1.222859e-04` | `1.356922e-01` |
| control | `psdpd_L3_k9_ell030_delta025_theta1e5` | 9 | 0.30 | 0.25 | 3.075 | `1e-5` | PASS | `1.263692e-05` | `1.959064e-03` |

## Theorem meaning

Each PASS block proves a finite interval-backed penalty certificate:

\[
D_\theta+\tau Q^TQ\succ0,
\qquad
R_\kappa+\tau Q^TQ\succ0.
\]

Therefore, on the corresponding finite boundary-null space:

\[
C^\circ\succeq \theta R_\kappa^\circ\succ0.
\]

## Why this matters

Step 22 gave one proof-grade finite block.

Step 25 starts the transition from a single finite block to a certificate
family, which is the engineering side of the Step 23 exhaustion contract.

## Relationship to the compact manifest

The earlier compact manifest file

```text
docs/insights/q3_psdpd_step25_certificate_manifest.csv
```

records the same interval-backed blocks by directly consuming midpoint/radius
CSV files inside Python.

This family manifest is the audit-facing runner: it calls Step 18 in
`--mode radius`, stores stdout, writes a seed block list, and emits JSON.

Both rows agree on the safe lower bounds.

## Verdict

The primary and control blocks both PASS.  The next proof-facing task is not
another sweep, but a manifest consumer / `FiniteCert` ledger object that lets
the Step 23 theorem contract refer to manifest rows.
