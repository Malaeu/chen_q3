# Track B E5p Lemma Audit: `mu_K_same_unit_bridge`

Status: `E5P_BRIDGE_SOURCE_GAP`.  Documentation/audit only: no Lean proof
files, no `Q3.Main` edit, no web proof evidence, and no E5p closure claim.

## Issue

GitHub issue #13 asks for the remaining bridge:

```text
For K in {2,3,3.5}, prove that the analytic E5p budget mu_K is in the same
G_K/Q_K/raw-edge units as the finite raw-edge certificate and satisfies

  mu_2   >= 0.45 + guards_2
  mu_3   >= 0.51 + guards_3
  mu_3.5 >= 0.75 + guards_3.5.
```

The finite side is already an interval certificate for supplied constants:

```text
mu * G_K - (P_edge,K - P0_edge,K) + tau * Q_K^T Q_K >= 0.
```

This file audits only the missing analytic source for `mu_K`.

## Commands Used

```bash
gh issue view 13 --json number,title,state,body,url,labels,author,updatedAt

rg -n -i \
  "inverse Dirichlet|Dirichlet expansion|mollifier|second moment|off-diagonal|Conrey|Ghosh|B_K|mu_K|mu budget|mu_budget|same-unit|Selberg extremal|Selberg|Vaaler|Beurling|Connes|adelic|class space|edge budget|Weil-side|raw-edge" \
  docs/trackB q3.lean.aristotle Q3 docs scripts trackB
```

No raw-edge PSD/eigenvalue search was run for this audit.

## Required Bridge Statement

Current target:

```text
mu_K >= mu_cert,K + transfer_guards_K
```

for the same raw-log packet object used by the finite certificate:

```text
mu_cert,2   = 0.45
mu_cert,3   = 0.51
mu_cert,3.5 = 0.75
```

and then:

```text
mu_K * G_K - E_edge,K + tau_K * Q_K^T Q_K >= 0
```

or the restricted `ker(Q_K)` equivalent.  The bridge must identify units:
raw-log coordinate, sign of `E_edge,K = P_edge,K - P0_edge,K`, packet basis,
`G_K` norm, boundary receiver, and transfer guards.

## Local Evidence By Route

| Route | Local source | Evidence found | Result |
| --- | --- | --- | --- |
| B: mollifier / atlas 028 | `docs/trackB/TRACKB_MOLLIFIER_S51_REVIVAL.md` | It records no Track B inverse Dirichlet expansion of the margin and no first/second moment formula for K-cell margins. | no usable `mu_K` source |
| A: Selberg extremals / atlas 009 | `docs/trackB/TRACKB_SELBERG_ROUTE_B_REPAIR.md`, `docs/trackB/b2_uncertainty_tax_preflight.md`, `docs/trackB/b2b_explicit_formula_route_gap.md` | Selberg gives a scalar hard-edge surplus `1/B_K` and a sharp tax, but not a PSD/cone-preserving operator bound in the Track B packet `G_K` norm. | no same-unit `mu_K` lower bound |
| C: Connes adelic/class-space | `q3.lean.aristotle/docs/insights/connes_zeta_spectral_triples_2026_01_29.md` | The note is architectural validation for a parallel Toeplitz/Weil route and explicitly says it is not directly wired into the Lean chain. It has no Track B K-cell constants. | not an E5p bridge source |

## Verdict

```text
E5P_BRIDGE_SOURCE_GAP
```

Reason:

```text
No current repository artifact defines an analytic mu_K source in the Track B
raw-edge G_K/Q_K normalization and proves the thresholds
0.45, 0.51, 0.75 plus transfer guards.
```

This is not `E5P_BRIDGE_THRESHOLD_FAIL`, because no same-unit analytic source
has been found to compare against the thresholds.  It is not
`E5P_BRIDGE_NORMALIZATION_GAP`, because the obstacle is earlier: the repository
does not yet provide the analytic `mu_K` object/lemma whose normalization could
be audited.

## Exact Remaining Obligation

One of the following must be supplied before E5p can close:

```text
1. A theorem defining analytic mu_K in raw-log Track B units and proving
   mu_K >= (0.45, 0.51, 0.75) + transfer_guards_K for K = 2,3,3.5.

2. A replacement finite certificate with lower supplied thresholds that are
   paid by an existing analytic budget source.

3. A fatal same-unit inequality, if a future analytic source is found but
   gives mu_K < mu_cert,K + transfer_guards_K for some active K.
```

Until then, the finite interval PSD certificate remains conditional on supplied
`mu` values and E5p remains open.
