# Track B Mu Budget Interface

Status: GAP_EXACTLY_NAMED / NORMALIZATION_INTERFACE.  This is documentation
only: no Lean proof, no Q3.Main edit, and no E5' closure claim.

## Purpose

This file fixes the comparison interface for Track B / E5'.  The LP quantities
`p_K` and `d_K` are useful finite optimization objects, but the scalar
`d_K-p_K` is not the E5' mu-budget.  It is a certificate/duality gap inside the
finite LP model.

The actual budget comparison is:

```text
budget_slack_K = mu_K - d_K
```

with guard terms, when present:

```text
usable_budget_slack_K =
  mu_K
  - d_K
  - closure_error_K
  - boundary_error_K
  - quadrature_error_K
  - finite_projection_error_K.
```

Current status: GAP.  The repository does not yet contain a same-unit proof
that the analytic `mu_K` ledger and the finite dual clamp `d_K` are in exactly
the same normalization.

## Quantity Ledger

| quantity | meaning | units / normalization | current status |
| --- | --- | --- | --- |
| `mu_K` | Allowed E5' edge-defect budget from the analytic ledger. | Must be in the same `G_K`-normalized raw-edge units as `d_K`. | GAP |
| `p_K` | Primal worst edge-defect Rayleigh value over the admissible finite K-cell cone. | Finite cone, `||v||_G=1`, after the current `ker Q` projection. | DOC / PROBE |
| `d_K` | Dual clamp or certificate level required to dominate the finite edge defect. | Same finite `G_K` units as `p_K` if the matrix convention is unchanged. | DOC / GAP |
| `certificate_gap_K` | `d_K - p_K`. | Finite optimization/certificate slack only. | DOC |
| `duality_gap_K` | Synonym for `certificate_gap_K` when the primal/dual relaxation is explicit. | Same as above. | DOC |
| `budget_slack_K` | `mu_K - d_K`. | Proof-relevant E5' margin, only after same-unit bridge. | GAP |
| `guards_K` | Closure, boundary, quadrature, interval, and finite-projection allowances. | Must be subtracted in the same units as `mu_K` and `d_K`. | GAP |

Do not use:

```text
d_K - p_K = mu_budget
```

Use:

```text
certificate_gap_K = d_K - p_K
budget_slack_K    = mu_K - d_K
```

## Same-Unit Comparator Tests

A future proof-grade comparison must pass all of these tests.

| test | required check | status |
| --- | --- | --- |
| raw-log coordinate | The same convention is used for `a=log n`, `xi`, and any `2*pi` scaling. | GAP |
| sign convention | The matrix called `D_K`, `E_edge,K`, or `P_edge-P0_edge` has the same positive-defect direction. | GAP |
| norm | The comparison uses the same `G_K` / `Norm_K` normalization. | GAP |
| kernel | The same `ker Q` projection or the same penalty form `+ tau Q^T Q` is used. | GAP |
| packet basis | The same packet grid, support, bandlimit, and `k_spline` basis are used. | GAP |
| inequality direction | The proof target is `Edge_K(h) <= mu_K * Norm_K(h)`, equivalently a restricted PSD domination. | DOC |
| guard accounting | Closure, boundary, quadrature, finite projection, and interval errors are included before declaring slack positive. | GAP |
| old reserve | No `m_old` is added unless a same-unit pre-edge ledger-support proof exists. | GAP, current `m_old=0` |

## Current Float Diagnostics

The current raw-edge probe gives only diagnostic thresholds.  These numbers are
not proof objects.

Command:

```bash
.venv/bin/python scripts/trackb_edge_operator_probe.py finiteop \
  --K 2 3 3.5 --ell 0.35 --grid-delta 0.5 --k-spline 5 \
  --p0-na 8001 --top 8
```

| K | float upper lambda | float two-sided opnorm | practical `mu_K` lower requirement in this finite model | proof-grade? |
| ---: | ---: | ---: | ---: | --- |
| 2 | `0.43707976289804495` | `0.4416718760986586` | about `0.44` | NO |
| 3 | `0.4976712109972619` | `0.49847340804127216` | about `0.50` | NO |
| 3.5 | `0.7349382268295058` | `0.734943076148279` | about `0.735` | NO |

These values can guide certificate search, but final E5' closure needs an
interval/rational PSD certificate or Lean-verifiable exact matrix inequality.

Current finite interval certificate for supplied thresholds:

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

This supplies finite interval PSD certificates for those input `mu` values.
It does not supply the analytic same-unit `mu_K` source.

## Correct Gate Logic

Finite LP/certificate health:

```text
certificate_gap_K = d_K - p_K.
```

This says whether the finite certificate has slack against the primal value,
after guards.  It does not say the E5' analytic budget is large enough.

E5' budget health:

```text
budget_slack_K = mu_K - d_K.
```

Track B can only use a positive budget verdict after:

```text
usable_budget_slack_K > 0
```

in a same-unit normalization with proof-grade guards.

## Required Bridge

The missing bridge is a theorem or certificate that identifies the analytic
`mu_K` budget with the finite raw-edge domination normalization used for `d_K`.

Acceptable proof-grade forms include one of:

```text
raw_edge_operator_K <= mu_K
```

in the local `G_K` normalization, or:

```text
mu_K * G_K - E_edge,K >= 0 on ker(Q_K),
```

or, using the repository's penalty convention:

```text
mu_K * G_K - E_edge,K + tau_K * Q_K^T Q_K >= 0.
```

Do not promote float eigenvalues, S3 closure bookkeeping, or `d_K-p_K` to this
bridge.

## Verdict

Current Track B / E5' budget state:

```text
mu_K source in same units: GAP
d_K finite dual clamp: DOC / PROBE
finite raw-edge PSD for supplied mu=(0.45,0.51,0.75): INTERVAL_CERT_PASS
certificate_gap_K = d_K - p_K: useful finite slack, not mu-budget
budget_slack_K = mu_K - d_K: the correct comparison, currently GAP
m_old: 0 unless a same-unit pre-edge reserve ledger is proved
```

Smallest useful next proof-producing patch after this cleanup:

```text
prove or source the same-unit analytic mu_K bridge, or reduce the supplied
finite mu thresholds to a proved analytic budget
```

because the naming interface is now pinned, and the active mathematical gap is
proof-grade domination rather than another float diagnostic.
