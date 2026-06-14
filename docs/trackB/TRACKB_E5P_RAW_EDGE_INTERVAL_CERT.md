# Track B E5' Raw-Edge Interval Certificate

Status: FINITE_INTERVAL_CERT_PASS_FOR_SUPPLIED_MU / E5_STILL_GAP_MU_BRIDGE.
This is not a Lean proof file, not a Q3.Main edit, and not an E5' closure
claim.

## What This Certifies

For each active finite Track B cell, the script
`scripts/trackb_raw_edge_interval_cert.py` builds Arb interval matrices for

```text
mu * G_K - (P_edge,K - P0_edge,K) + tau * Q_K^T Q_K
```

on the full packet coefficient space.  Since the penalty term vanishes on
`ker(Q_K)`, a positive full-space lower eigenvalue proves the restricted
finite raw-edge domination for the supplied value of `mu`.

This only proves a finite statement for the supplied constants.  It does not
prove that the analytic E5' budget `mu_K` is equal to, or larger than, those
constants.

## Command

```bash
.venv/bin/python scripts/trackb_raw_edge_interval_cert.py \
  --K 2 3 3.5 \
  --mu 0.45 0.51 0.75 \
  --tau 100000000 \
  --ell 0.35 \
  --grid-delta 0.5 \
  --k-spline 5 \
  --arb-prec 192 \
  --out trackB/certs/e5p_raw_edge_interval_cert_K2_K3_K35.json
```

Python compile check:

```bash
.venv/bin/python -m py_compile scripts/trackb_raw_edge_interval_cert.py
```

## Matrix Sources

| matrix | source |
| --- | --- |
| `G_K` | exact centered B-spline rational inputs evaluated in Arb |
| `Q_K` | Arb intervals for `exp(+-u/2)` on rational centers |
| `P_edge,K` | Arb intervals for `log(p)`, `exp(-r log(p)/2)`, and B-spline shifts |
| `P0_edge,K` | exact piecewise-polynomial B-spline integral of `exp(a/2)` in Arb |

The certificate avoids a numerical nullspace basis `N_K` by using the full-space
penalty form `+ tau Q_K^T Q_K`.

## Results

Artifact:

```text
trackB/certs/e5p_raw_edge_interval_cert_K2_K3_K35.json
```

| K | raw edge | B_K | dim | kerQ if rank 2 | supplied mu | tau | edge shifts | interval min eigenvalue lower | cert verdict |
| ---: | --- | --- | ---: | ---: | ---: | ---: | ---: | ---: | --- |
| 2 | `[4,8]` | not used by raw-edge PSD cert | 16 | 14 | `9/20 = 0.45` | `100000000` | 441 | `0.0129205025641165041756244529888550415698384941606131420373443264160324450064242783099439232` | PASS |
| 3 | `[6,12]` | not used by raw-edge PSD cert | 24 | 22 | `51/100 = 0.51` | `100000000` | 14942 | `0.0123292749542153373865150679879004070578799322422451094887694119834991629981888736052152297` | PASS |
| 3.5 | `[7,14]` | not used by raw-edge PSD cert | 28 | 26 | `3/4 = 0.75` | `100000000` | 93162 | `0.0150616591834281164859458636664893080895405879259411551698018373140686699526777271522623609` | PASS |

## Interpretation

This upgrades the raw-edge Phase 4 status:

```text
old: float/probe raw-edge opnorm only
new: interval PSD finite certificate for supplied mu thresholds
```

The E5' node is still not closed because the repository still lacks the
same-unit analytic comparison

```text
budget_slack_K = mu_K - d_K >= 0
```

or, concretely for this certificate, a proof that the analytic `mu_K` budget in
the same `G_K/Q_K` normalization satisfies:

```text
mu_2   >= 0.45
mu_3   >= 0.51
mu_3.5 >= 0.75
```

after all tail, boundary, closure, quadrature, and finite-projection guards.

## Verdict

```text
finite raw-edge interval PSD for supplied mu: PASS
old reserve m_old: 0
Lean status: not ported
E5' closure status: GAP_EXACTLY_NAMED
remaining gap: SAME_UNIT_ANALYTIC_MU_BRIDGE
```
