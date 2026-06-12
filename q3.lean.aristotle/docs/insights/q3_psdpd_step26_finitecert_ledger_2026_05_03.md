# Step 26 -- FiniteCert ledger

## Summary

- source manifest: `q3.lean.aristotle/docs/insights/q3_psdpd_certificate_family_manifest.csv`
- total manifest rows: `2`
- accepted finite certs: `2`
- rejected rows: `0`

## Accepted certificates

| cert_id | role | k | ell | theta | Dtheta safe | Rkappa safe |
|---|---:|---:|---:|---:|---:|---:|
| `psdpd_family_v1:psdpd_L3_k11_ell030_delta025_theta1e4` | primary | 11 | 0.3 | `0.0001` | `1.2228594783222341e-04` | `1.3569220778185986e-01` |
| `psdpd_family_v1:psdpd_L3_k9_ell030_delta025_theta1e5` | control | 9 | 0.3 | `1e-05` | `1.2636922821866158e-05` | `1.9590640625247978e-03` |

## Theorem payload

Each accepted row is treated as a concrete finite predicate:

```text
FinitePenaltyCert(Dtheta, Rkappa, Q)
```

Through the Lean receiver `Q3.Proofs.FinitePenaltyCert`, this gives
finite boundary-null positivity:

\[
C^\circ\succeq \theta R_\kappa^\circ,
\qquad
R_\kappa^\circ\succ0.
\]

This ledger still does not prove the exhaustion theorem.  It supplies
the finite predicates that the Step 23 family/exhaustion contract will
quantify over.
