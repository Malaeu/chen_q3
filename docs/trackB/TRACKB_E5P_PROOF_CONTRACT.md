# Track B E5' Proof Contract

Status: PROOF_CONTRACT_FIRST. This is the mandatory math/certificate contract
for E5'. It precedes any Lean integration. It does not prove RH and does not
edit the public route.

## Theorem Shape

For each active finite cell `K`, define a finite packet coefficient space
`V_K`, a cone-admissible packet class `C_K`, a boundary row matrix `Q_K`, a
Gram matrix `G_K`, and a raw-edge matrix `E_edge,K`. The E5' claim is:

```text
forall c in C_K with Q_K c = 0,
  c^T E_edge,K c <= mu_K * c^T G_K c.
```

Equivalently,

```text
mu_K * G_K - E_edge,K >= 0 on C_K cap ker(Q_K).
```

Because the current finite probes are already built on Hermitian-square packet
directions and then projected to `ker(Q_K)`, the certificate may prove the
stronger linear-space statement

```text
mu_K * G_K - E_edge,K >= 0 on ker(Q_K).
```

That stronger statement is acceptable and avoids cone-boundary ambiguity.

## Objects

### Packet Space `V_K`

`V_K` is the finite centered packet coefficient space used by the Track B
probe schedule. A coefficient vector `c` defines a compactly supported
B-spline packet/profile. The current executable implementation uses
`scripts/trackb_edge_operator_probe.py`, which imports the Step13 packet pilot.

The proof contract does not identify `V_K` with the older Step32F `L=3`,
`ell=0.3`, `k=11/9`, `n=23` cells unless a same-space ledger explicitly does so.

### Cone `C_K`

`C_K` is the finite cone of admissible Hermitian-square packet directions in
the corrected positive-definite/local packet sense. The finite PSD certificate
target may work on all of `ker(Q_K)`, in which case membership in `C_K` is used
only as a consumer condition.

Forbidden shortcut:

```text
Do not require pointwise W_K >= 0.
```

The allowed object is restricted operator domination.

### Boundary Kernel `ker(Q_K)`

`Q_K` contains the two boundary/normalization rows used by the finite packet
backend. The proof consumer condition is

```text
Q_K c = 0.
```

The penalty bridge may instead certify a full-space inequality after adding
`tau_K Q_K^T Q_K`.

### Gram/Norm Normalization

The norm is fixed as

```text
Norm_K(c) = c^T G_K c.
```

All comparison constants, including `mu_K` and any candidate `m_old(K)`, must
be in this `G_K` normalization. Euclidean floors from older certificates are
not directly comparable without a certified `G_K` bridge.

### Raw Edge

Raw-log coordinate:

```text
a = r * log(p),  xi = a/(2*pi).
```

The raw edge interval is

```text
[2K,4K].
```

The matrix is

```text
E_edge,K = P_edge,K - P0_edge,K.
```

For coefficient vector `c`,

```text
c^T P_edge,K c
```

is the finite prime-power sum over `log n in [2K,4K]`, and

```text
c^T P0_edge,K c
```

is the continuum model integral over `[2K,4K]` with density `exp(a/2) da`.

In Fourier notation this corresponds to the edge functional

```text
Edge_K(h) = < |hat h|^2, W_K >
W_K(xi) = sum_{log n in [2K,4K]} Lambda(n)/sqrt(n) cos(xi log n).
```

This notation is a bridge description only; the finite proof object is the
matrix inequality on `ker(Q_K)`.

## Certificate Theorem

### Penalty Form

If there exists `tau_K >= 0` such that

```text
M_K(tau_K) :=
  (m_old(K) + mu_K) * G_K - E_edge,K + tau_K * Q_K^T Q_K
```

is positive semidefinite on the full coefficient space, then

```text
c^T E_edge,K c <= (m_old(K) + mu_K) * c^T G_K c
```

for every `c` with `Q_K c = 0`.

Proof: for `Q_K c=0`, the penalty term vanishes, so

```text
0 <= c^T M_K(tau_K)c
  = (m_old(K)+mu_K)c^T G_K c - c^T E_edge,K c.
```

### Rational/Interval PSD Requirement

Float eigenvalues are diagnostics only. A final Phase 4 certificate must be one
of:

```text
exact rational LDL / weighted-square identity;
interval LDL/Cholesky with outward-rounded entry enclosures;
Lean-checked rational import equivalent to the penalty receiver.
```

The old buried matrix-Rayleigh artifact is not an allowed certificate.

## Edge True Bridge

The true analytic edge must be decomposed as

```text
Edge_true,K(c) = Edge_cell,K(c) + Tail_K(c) + Boundary_K(c).
```

Required bridge lemmas:

| lemma | statement | status |
| --- | --- | --- |
| Cell identity | `Edge_cell,K(c) = c^T E_edge,K c` for the finite packet cell and raw-log normalization. | SKETCH/implemented numerically |
| Tail bound | `Tail_K(c) <= tail_K * c^T G_K c` with proof-grade bound. | GAP unless supplied |
| Boundary null | `Boundary_K(c)=0` or bounded on `ker(Q_K)`. | numeric S3 bookkeeping only so far |
| Mu comparison | `tail_K + boundary_K + finite_mu_K <= mu_budget(K)` in the same units. | GAP |

If `mu_K` already includes cell, tail, and boundary allowances, the bridge must
state that explicitly and give its source.

## Old Reserve / Non-Circularity Ledger

Old Step32F lower-bound data can be used only if all checks pass:

```text
same K-cell;
same packet basis;
same G/Q normalization;
pre-edge support, meaning it has not already paid the prime support used by E_edge,K;
quantitative lower bound m_old(K) * G_K.
```

Current audit result:

```text
m_old(K)=0
```

because the recovered Step32F certificate proves positivity of old `C=A-P`
where old `P` already contains the relevant edge prime support. Treating this
as a free pre-edge reserve would double count.

## Lemma Ledger

| id | lemma | proof object |
| --- | --- | --- |
| L0 | Active finite cell and raw-log normalization fixed. | docs + script schedule |
| L1 | `G_K` is SPD on `ker(Q_K)`. | finite interval/rational check needed |
| L2 | `E_edge,K` equals finite raw edge cell. | exact construction/import needed |
| L3 | `m_old(K)=0` unless new pre-edge ledger is proved. | audit complete |
| L4 | `M_K(tau_K)` PSD full-space. | interval cert pass for supplied `mu=(0.45,0.51,0.75)`; analytic `mu_K` bridge still missing |
| L5 | Penalty PSD implies restricted domination. | existing Lean receiver likely reusable |
| L6 | `mu_K` source is same-unit and enough for finite+tail+boundary. | interface written; same-unit analytic bridge missing |

## Acceptance Criteria

`PROVED_MATH_AND_CERT`:

```text
L0-L6 are all closed outside Lean, with rational/interval certificate artifacts.
```

`PROVED_FINITE_NEEDS_LEAN_PORT`:

```text
L0-L5 are closed with proof-grade finite certificate, but the Lean wrapper is not ported.
```

`PROVED_LEAN`:

```text
L0-L6 are Lean-checked or imported through Lean-checked rational certificates.
```

`GAP_EXACTLY_NAMED`:

```text
the blocking missing object is named precisely, e.g.
SAME_UNIT_ANALYTIC_MU_BRIDGE.
```

`FATAL_CURRENT_CLASS`:

```text
the Phase 4 or fallback certificate search proves no admissible current-class
finite certificate can fit the mu budget.
```
