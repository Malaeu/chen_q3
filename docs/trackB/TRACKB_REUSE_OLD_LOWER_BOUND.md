# Track B Reuse Old Lower-Bound Engine

Status: DIAGNOSTIC_COMPLETE.  Strategy documentation only: no Lean proof files,
no `Q3.Main` change, no route mutation, and no RH-conditional input.

## Purpose

Test the hypothesis:

```text
The old Step32F one-third/lower-bound engine may already contain enough
quantitative reserve to dominate the raw Track B edge operator.
```

The historical reuse hypothesis was a reserve-augmented domination test:

```text
mu_K * G_K - E_edge,K + m_old(K) * G_K >= 0 on ker(Q),
```

where `E_edge,K = P_edge - P0_edge` in the same finite packet basis and the same
`G/Q` normalization.  This hypothesis is not active because the same-unit
pre-edge reserve ledger is missing and the current verdict is `m_old(K)=0`.

## Task 0 Gates

### Task 0A: Certificate Nature

The old Step32F lower-bound engine recovered here is not the buried
matrix-side Rayleigh artefact.

Guard:

```text
DEAD_MATRIX_RAYLEIGH means:
  18/18 NUMERICAL_INVALID,
  signal about 1e-13 versus A_tail noise about 3e-10,
  DO_NOT_RESURRECT.
```

This audit did not reuse that object.  The recovered certificate is the exact
rational Step32F penalty/LDL certificate:

```text
D + tau_D Q^TQ = dFloor*I + L_D diag(w_D) L_D^T
R + tau_R Q^TQ = rFloor*I + L_R diag(w_R) L_R^T
```

with Lean-checked rational matrix identities and nonnegative rational LDL
weights.

Task-0A verdict:

```text
ANALYTIC_LDL_CERTIFICATE
not TRACKB_REUSE_FATAL_BAD_OLD_CERT
not the buried float Rayleigh margin
```

Important limitation: it is an analytic/finite LDL certificate in the old
Step32F coefficient space, but it is not already a `d_K * G_K` certificate in
the current Track B K-cell.

### Task 0B: Noncircularity / Ledger Support

The old reserve is not a free pre-edge reserve for the current raw edge.

Reason:

```text
old C = A - P,
where P is the full finite prime-side matrix up to 2L.
```

In the nearest old self-cell `L=3`, the raw edge `[3,6]` is a subset of this
same full prime matrix `P`.  Therefore the old `C=A-P` certificate has already
paid the edge prime contribution on that support.  Adding `m_old` again as a
free reserve for the same `E_edge` would double-count.

The old certificate is also not a direct post-edge closure for E5p.  It proves
positivity of the full `A-P` block through the `Dtheta/Rkappa` split; it does
not prove the specific Track B ledger inequality

```text
mu_K*G_K - (P_edge - P0_edge) + m_old*G_K >= 0.
```

Task-0B verdict:

```text
POST_EDGE_OR_MIXED_FOR_OLD_SELF_CELL
TRACKB_REUSE_GAP_CIRCULARITY_OR_LEDGER_SUPPORT for using m_old as free edge budget
```

Consequence:

```text
Do not add m_old to mu_K unless a separate ledger decomposition proves that
the old reserve is pre-edge with respect to the current E_edge term.
```

## Sources Recovered

The relevant old certificate is the Step32F finite penalty lower-bound engine:

```text
Q3/Proofs/PSD_PenaltyCertificate.lean
Q3/Proofs/PSD_CenteredCoeffPayloadImport.lean
Q3/Proofs/PSD_CenteredCoeffPenaltyImport.lean
Q3/Proofs/PSD_CenteredCoeffPenaltyLDLImport.lean
q3.lean.aristotle/docs/insights/q3_psdpd_certificate_family_manifest.csv
q3.lean.aristotle/docs/insights/q3_psdpd_step32f_coeff_payload_import_plan.json
q3.lean.aristotle/scripts/q3_psdpd_step32f_primary_ldl_cert.py
```

The old algebraic split is:

```text
C = A - P
R = R_kappa = A - kappa * P0
D = D_theta = C - theta * R
  = (1 - theta) * A - P + theta * kappa * P0
C[v] = D[v] + theta * R[v].
```

The checked LDL receiver proves exact rational identities of the form:

```text
D + tau_D * Q^T Q = dFloor * I + L_D diag(w_D) L_D^T
R + tau_R * Q^T Q = rFloor * I + L_R diag(w_R) L_R^T
```

with nonnegative rational LDL weights.  Therefore, for all coefficient vectors
`v` with `Qv = 0`,

```text
D[v] >= dFloor * ||v||_2^2
R[v] >= rFloor * ||v||_2^2
C[v] >= (dFloor + theta*rFloor) * ||v||_2^2.
```

## Exact Old Statements

| block | old space | kappa | theta | tau_D | tau_R | dFloor | rFloor | m_I = dFloor + theta*rFloor |
| --- | --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| `primaryK11` | `L=3, ell=0.3, delta=0.25, k=11, n=23, kerQ=21` | `3.25` | `1e-4` | `501.187233627274` | `15848.9319246112` | `1.222859478322e-4` | `1.356922077819e-1` | `1.358551686104e-4` |
| `controlK9` | `L=3, ell=0.3, delta=0.25, k=9, n=23, kerQ=21` | `3.075` | `1e-5` | `63.0957344480194` | `100000` | `1.263692282187e-5` | `1.959064062525e-3` | `1.265651346249e-5` |

Status:

```text
PROVED: exact rational LDL certificates exist for these old Step32F D/R
        lower bounds in Lean.
SKETCH: the use of these floors as a Track B raw-edge reserve.
```

## Same-Space Audit

| check | current Track B S5C raw-edge cell | old Step32F lower-bound cell | verdict |
| --- | --- | --- | --- |
| K-cell | S5C uses `K=2,3,3.5`, edge `[2K,4K]`, `L=2K`. | Old blocks have fixed `L=3`, equivalent only to forced `K=1.5`. | `DIFFERENT_OPERATOR` |
| basis | S5C uses Step13 packet settings chosen for Track B, e.g. stable `ell=0.75/1.375`, `grid_delta=0.5`, `k=5`. | Old blocks use `ell=0.3`, `delta=0.25`, `k=11` or `k=9`, 23 centers. | `DIFFERENT_OPERATOR` |
| Gram normalization | S5C edge domination is measured as Loewner order against packet Gram `G`. | Old lower-bound receiver is against `euclideanEnergy`, i.e. `I`; no old certified `G` floor is stored in the certificate. | `NORMALIZATION_GAP` |
| ker-Q convention | Boundary rows are the same type of analytic null constraints, `exp(+u/2)` and `exp(-u/2)`. | Same convention, but on different centers. | compatible only after re-instantiation |
| sign convention | Current edge object is `E_edge = P_edge - P0_edge`. | Old certificate proves positivity of full `C=A-P`, not isolated edge. | `TRACKB_REUSE_GAP_NOT_EDGE_OPERATOR` |
| boundary-null convention | Both use `Qv=0`. | Same idea, different finite rows. | compatible only after re-instantiation |

Task-2 verdict:

```text
Current S5C K-cell: DIFFERENT_OPERATOR + NORMALIZATION_GAP.
Old L=3 self-cell: SAME_SPACE only if Track B is forced to K=1.5 and old
packet parameters.
Even in that old self-cell, Task 0B says the old C=A-P certificate is not a
free pre-edge reserve because P already contains the edge primes.
```

## Raw Edge Matrix In The Old Self-Cell

As a sanity check, I forced the raw Track B edge construction into the old
Step32F self-cell:

```text
K = 1.5
edge = [3, 6]
E_edge = P_edge - P0_edge
P_edge = finite prime-power sum over log n in [3,6]
P0_edge = integral over [3,6] with density exp(a/2)
comparison norm = generalized eigenvalues of N^T E_edge N vs N^T G N
```

Numerical result:

| block | G eig min | G eig max | m_G lower from old floor | edge eig min | edge eig max | edge opnorm | edge_max / m_G |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| `primaryK11` | `0.996851` | `1.003016` | `1.354467e-4` | `-1.104450` | `1.104029` | `1.104450` | `8151.02` |
| `controlK9` | `0.990471` | `1.009047` | `1.254303e-5` | `-1.084674` | `1.084199` | `1.084674` | `86438.36` |

The bridge from the old Euclidean floor to `G` used:

```text
G[v] <= lambda_max(N^T G N) * ||v||_2^2,
m_G >= m_I / lambda_max(N^T G N).
```

So even in the nearest old self-space, the certified old reserve is four to five
orders of magnitude smaller than the raw edge operator.

## Domination Test

For `mu_K = 0`, the requested domination test fails even under the
counterfactual assumption that the old floor may be treated as a free reserve:

```text
(m_old * G - E_edge) >= 0 on ker(Q)
```

because the largest generalized eigenvalue of `E_edge` is about `1.10`, while
the certified old reserve is only:

```text
primaryK11 m_G >= 1.354e-4
controlK9  m_G >= 1.254e-5
```

Equivalently, the missing reserve is:

```text
primaryK11: edge_max - m_G ~= 1.1038939
controlK9:  edge_max - m_G ~= 1.0841864
```

The test could only turn green if an external `mu_K` budget of order `1` in the
same `G` units were available.  That is not the old Step32F reserve.

Because of Task 0B, this numerical test is only a stress test.  It is not a
valid proof route by itself: the old `m_old` is not certified as pre-edge.

## Three-Part Certificate Check

The recovered old proof is not a three equal thirds certificate in the current
Track B sense.  Its actual quantitative structure is:

```text
C = D + theta*R,
D + tau_D Q^T Q >= dFloor*I,
R + tau_R Q^T Q >= rFloor*I.
```

This is reusable as a penalty/LDL pattern, but it does not decompose
`mu_K*G - E_edge` into old positive pieces.  In particular, the old pieces
prove positivity of the full `A-P` block; they do not isolate the edge-strip
prime defect.

## Verdict

```text
TRACKB_REUSE_GAP_NOT_EDGE_OPERATOR
TRACKB_REUSE_GAP_CIRCULARITY_OR_LEDGER_SUPPORT
```

Reason:

```text
The old lower-bound engine is real and certified, but it certifies full
C=A-P positivity in old Step32F cells.  It is not already a raw edge operator
domination certificate in the current Track B K-cells.

Moreover, in the old self-cell, C=A-P already contains the edge prime support
inside P, so m_old cannot be added to mu_K as a free pre-edge budget without a
new ledger-support proof.
```

Additional nearest-cell numerical verdict:

```text
TRACKB_REUSE_FATAL_INSUFFICIENT_RESERVE
```

Reason:

```text
When the old L=3 packet cell is forced into a K=1.5 raw-edge test, the raw
edge operator is about 1.10 in G-units, while the certified old reserve is
only 1e-4 to 1e-5 in G-units.
```

## Next Consequence

Do not build a new external lift from this old certificate.  The useful reuse is
only methodological:

```text
reuse the exact rational LDL / penalty receiver pattern,
not the old Step32F numerical reserve as the Track B edge reserve.
```

If Track B continues, the next finite certificate must target
`mu_K*G - E_edge` directly in the current K-cell, or switch to the
operator/prolate route already listed in the price table.
