# Step 24 -- Lean penalty certificate receiver

## Goal

Formalize the generic finite-dimensional penalty theorem from Step 23:

```text
if M + tau Q^T Q is positive on the full coefficient space,
then M is positive on ker(Q).
```

This is the first Lean receiver for the Step 18--22 finite interval certificate
pipeline.  It deliberately avoids zeta, primes, Arch integrals, eigenvalues,
and interval arithmetic.

## Lean File

Added:

```text
Q3/Proofs/PSD_PenaltyCertificate.lean
```

The file defines:

```lean
quadForm       : Matrix ι ι ℝ -> (ι -> ℝ) -> ℝ
BoundaryNull   : Matrix ρ ι ℝ -> (ι -> ℝ) -> Prop
boundaryEnergy : Matrix ρ ι ℝ -> (ι -> ℝ) -> ℝ
penaltyForm    : Matrix ι ι ℝ -> Matrix ρ ι ℝ -> ℝ -> (ι -> ℝ) -> ℝ
```

with

```text
penaltyForm M Q tau v = quadForm M v + tau * ||Qv||^2.
```

## Closed Theorems

The core lemmas are:

```lean
boundaryEnergy_eq_zero_of_boundaryNull
penaltyForm_eq_quadForm_of_boundaryNull
quadForm_nonneg_on_boundaryNull_of_penalty_nonneg
quadForm_pos_on_boundaryNull_of_penalty_pos
quadForm_nonneg_on_boundaryNull_of_penalty_pos
two_penalty_guards_on_boundaryNull
```

The key theorem for the Step 18 guard is:

```lean
theorem quadForm_nonneg_on_boundaryNull_of_penalty_pos
    (hpen : forall v, v != 0 -> 0 < penaltyForm M Q tau v) :
    forall v, BoundaryNull Q v -> v != 0 -> 0 <= quadForm M v
```

The two-guard version matches the finite certificate pair:

```text
Dtheta + tau_D Q^TQ
Rkappa + tau_R Q^TQ.
```

## Verification

Ran:

```text
lake env lean Q3/Proofs/PSD_PenaltyCertificate.lean
```

Result: PASS.

Hole scan:

```text
no sorry / admit / exact?
```

## Integration Note

This theorem is intentionally standalone for now.  It is not imported into
`Q3.Main`, because the finite certificate family/exhaustion theorem is not yet
formalized and the public mainline still goes through the current orchestrator
route.

## Next Move

Step 25 should connect this receiver to a small certificate-data record:

```text
FinitePenaltyCert(D, R, Q, tau_D, tau_R)
```

and prove that such a record yields the Step 23 finite block conclusion:

```text
Dtheta >= 0 on ker(Q),
Rkappa > 0 on ker(Q).
```

After that, the analytic bridge can identify `Dtheta` and `Rkappa` with the
actual B-spline matrices from the interval CSV contract.
