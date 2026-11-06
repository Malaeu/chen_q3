# STATUS: TRY_RAMANUJAN_GAUSSIAN_SOURCE_AUDIT_D

```yaml
OPERATIVE_CLASS: TRY_RAMANUJAN_GAUSSIAN_SOURCE_AUDIT_D
ARTIFACT_STATE: FROZEN_BEFORE_TEST
RH_PROVED: false
REQUEST_COMMIT: 9e1bedc95591b799bb91ce3bcc3cd99b3ce6b190
REQUEST_BLOB: cb37deef8713a4fe6cfec8f38269a74d41e408d6
WRITE_BRANCH: proshka_inbox_2026-10-31
RH_GAP: SOURCE_SPECIFIC_SIGNED_RAMANUJAN_RETURN
PROVED_STEPS: []
PROGRESS_CLASS: NO_PROGRESS
RH_SIGN_PROGRESS: NONE
KILLS: []
CLOSES: []
OPENS: []
COGNITIVE_OPERATOR: SCALE_AND_MELLIN_AUDIT
ROUTE_SCORE: 2
```

## Frozen specification

Preserve original mu, zeta, exact Gaussian and every prime power. First check the two distinct formulas in the pinned brief: G(alpha) uses exp(-(alpha/n)^2), while the displayed Hardy–Littlewood correction uses beta^rho; inspect whether powers, scaling, and convergence match before any transfer. Predictions: P1 the two normalizations are not interchangeable without alpha/beta reparameterization; P2 the original modular equality cannot be source-exact because Mellin residues at off-critical zeros need not vanish; P3 a finite Ramanujan expansion is algebraically exact but positivity alone does not supply the signed bound; P4 no unconditional RH-sign gain follows. Falsifiers: alpha=beta=sqrt(pi), Mellin transform at s, and an explicit finite n example. Do not silently repair frozen statements. All cofinal claims require proof, not DIAG.
