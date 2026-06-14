# Track B E5' Closure Goal

Status: IN_PROGRESS_TRACKB_E5P. Strategy/certificate documentation only:
no Lean proof files, no `Q3.Main` edit, no route mutation, and no RH claim.

## Mission

Close or kill the Track B / E5' edge-defect node by deciding the restricted
finite operator inequality

```text
Edge_K(h) <= mu_K * Norm_K(h),  h in C_K cap ker(Q).
```

The finite certificate target is

```text
mu_K * G_K - E_edge,K >= 0 on ker(Q_K),
```

or, only if a genuine same-space pre-edge reserve is proved,

```text
(m_old(K) + mu_K) * G_K - E_edge,K >= 0 on ker(Q_K).
```

## Current Verdict

```text
verdict: GAP_EXACTLY_NAMED_IN_PROGRESS
gap name: SAME_UNIT_ANALYTIC_MU_BRIDGE
old-reserve verdict: m_old(K)=0 unless a new pre-edge ledger-support proof is supplied
Lean status: READ_ONLY_MAP_CREATED; no Lean port yet
```

This is not a negative Track B kill yet. The precise open gap is that the repo
has a finite raw-edge operator instrument and a real penalty/LDL receiver
pattern.  It now also has an interval finite raw-edge PSD certificate for the
supplied thresholds `mu=(0.45,0.51,0.75)` on `K=2,3,3.5`.  It does not yet have
a same-normalization proof that the analytic `mu_K` budget is at least those
thresholds after all guards.

## Active K Cells

Current Track B executable cells from the existing docs and probes:

| K | raw edge | current role |
| ---: | --- | --- |
| `2` | `[4,8]` | S3/S4/S5C tested cell |
| `3` | `[6,12]` | S3/S4/S5C tested cell |
| `3.5` | `[7,14]` | witness/S4/S5C tested cell |

Old Step32F nearest self-cell:

| forced K | raw edge | verdict |
| ---: | --- | --- |
| `1.5` | `[3,6]` | old `L=3` same-cell stress only; not current Track B |

## Normalization Lock

Raw-log coordinate:

```text
a = r * log(p)
xi = a / (2*pi)
edge = [2K,4K]
```

Finite raw edge:

```text
E_edge,K = P_edge,K - P0_edge,K
```

where `P_edge,K` is the finite prime-power matrix over `log n in [2K,4K]`,
and `P0_edge,K` is the continuum model integral over the same raw-log interval
with density `exp(a/2) da`.

Norm/Gram:

```text
Norm_K(h) = c^T G_K c
ker(Q_K) = {c : Q_K c = 0}
```

The proof object is restricted PSD/operator domination on `ker(Q_K)`, not
pointwise positivity of the cosine weight

```text
W_K(xi) = sum_{log n in [2K,4K]} Lambda(n)/sqrt(n) * cos(xi log n).
```

## Old Reserve Status

Old Step32F proves exact rational penalty/LDL lower bounds for the old
coefficient cell:

```text
C = A - P
R = R_kappa = A - kappa * P0
D = D_theta = C - theta * R
D + tau_D Q^T Q >= dFloor * I
R + tau_R Q^T Q >= rFloor * I
```

It is live as an exact LDL receiver pattern, but it is not a free pre-edge
reserve for E5':

```text
m_old(K) = 0
```

unless a new ledger proves that the reserve is in the same current K-cell,
same packet basis, same `G/Q` normalization, and disjoint from the edge-prime
support already paid inside old `P`.

## Next Inequality

With current information, the next valid target is therefore

```text
mu_K * G_K - E_edge,K >= 0 on ker(Q_K).
```

Equivalent penalty-certificate shape:

```text
mu_K * G_K - E_edge,K + tau_K * Q_K^T Q_K >= 0
```

on the full coefficient space. This is the preferred bridge because it matches
the existing finite penalty receiver in `Q3/Proofs/PSD_PenaltyCertificate.lean`.

Current finite interval certificate artifact:

```text
trackB/certs/e5p_raw_edge_interval_cert_K2_K3_K35.json
```

It proves the penalty inequality for supplied finite thresholds:

```text
K=2:   mu=0.45, tau=100000000, interval min eigen lower > 0.0129205
K=3:   mu=0.51, tau=100000000, interval min eigen lower > 0.0123292
K=3.5: mu=0.75, tau=100000000, interval min eigen lower > 0.0150616
```

This is conditional on supplied `mu`; it is not yet the analytic E5' `mu_K`
comparison.

## Lean Status

No Lean edits are authorized before the proof contract and finite certificate
are stable. Current Lean work is read-only mapping only.

Candidate Lean receiver, once a rational/interval certificate exists:

```text
Q3.Proofs.PSD_PenaltyCertificate.quadForm_nonneg_on_boundaryNull_of_penalty_nonneg
Q3.Proofs.PSD_PenaltyCertificate.penalty_lower_bound_of_ratMatrixWeightedSquare_identity
```

No current Lean declaration names the Track B E5' finite object
`mu_K * G_K - E_edge,K`.

## DONE Conditions

Allowed terminal states:

```text
PROVED_MATH_AND_CERT
PROVED_FINITE_NEEDS_LEAN_PORT
PROVED_LEAN
FATAL_CURRENT_CLASS
GAP_EXACTLY_NAMED
```

Current active candidate terminal state, because Phase 4 produced a finite
interval PSD object only for supplied thresholds and the analytic `mu_K` bridge
is still missing:

```text
GAP_EXACTLY_NAMED: SAME_UNIT_ANALYTIC_MU_BRIDGE
```
