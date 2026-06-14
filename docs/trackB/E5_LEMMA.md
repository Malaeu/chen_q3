# Track B E5' Lemma Status

Status: GAP_EXACTLY_NAMED / SAME_UNIT_ANALYTIC_MU_BRIDGE.  This is not a Lean
proof file and does not claim RH or full E5' closure.

## Target Lemma

For each active finite cell `K`, prove

```text
Edge_K(h) <= mu_K * Norm_K(h),  h in C_K cap ker(Q_K).
```

The finite matrix form is:

```text
mu_K * G_K - E_edge,K >= 0 on ker(Q_K).
```

The full-space penalty receiver is:

```text
mu_K * G_K - E_edge,K + tau_K * Q_K^T Q_K >= 0.
```

## Current Finite Certificate

The raw-edge finite PSD problem is certified for supplied thresholds by:

```text
scripts/trackb_raw_edge_interval_cert.py
trackB/certs/e5p_raw_edge_interval_cert_K2_K3_K35.json
```

| K | supplied mu | tau | cert type | verdict |
| ---: | ---: | ---: | --- | --- |
| 2 | `0.45` | `100000000` | Arb interval full-space penalty PSD | PASS |
| 3 | `0.51` | `100000000` | Arb interval full-space penalty PSD | PASS |
| 3.5 | `0.75` | `100000000` | Arb interval full-space penalty PSD | PASS |

This removes the float-only PSD blocker for these supplied constants.

## What Is Still Missing

The repository does not yet prove that the analytic E5' budget `mu_K` supplies
these constants in the same `G_K/Q_K` normalization, after all tail, boundary,
closure, quadrature, and finite-projection guards.

Required bridge:

```text
mu_2   >= 0.45
mu_3   >= 0.51
mu_3.5 >= 0.75
```

in the same units as the interval certificate.

## Old Reserve

The old Step32F LDL engine is reusable as a penalty/LDL pattern only.
It is not a free pre-edge E5' reserve.

```text
m_old = 0
```

## Lean Status

No Lean E5' theorem exists locally.  No Lean proof files were edited for this
node.  The likely future receiver is the generic penalty infrastructure in
`Q3/Proofs/PSD_PenaltyCertificate.lean`, after a stable payload/bridge exists.

## Verdict

```text
E5' proved: NO
finite raw-edge PSD for supplied mu: YES
old reserve reusable as E5' budget: NO
m_old: 0
terminal status: GAP_EXACTLY_NAMED
gap: SAME_UNIT_ANALYTIC_MU_BRIDGE
```
