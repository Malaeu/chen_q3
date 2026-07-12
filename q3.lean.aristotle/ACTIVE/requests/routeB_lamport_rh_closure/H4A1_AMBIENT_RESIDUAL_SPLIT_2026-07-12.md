# Route B H4a1 ambient/compressed residual split — revision 22

Status: `H4A1A_PROVED / EXACT_AMBIENT_RESIDUAL_CROSSWALK_OPEN / NOT_RH`

Progress class: `PROOF_PROGRESS + REPRESENTATION_PROGRESS + FALSIFICATION_PROGRESS`

This transaction proves the universal residual decomposition below H4a1.  It
does not identify a Route B operator domain, turn a quadratic form compression
into an operator compression, estimate the leakage, close H4a1/H4a/H4, create
Bus 010, or prove RH.

## 1. Three residual objects

For a linear operator `A`, projection/compression map `P`, vector `v`, and
scalar `mu`, define

```text
ambientResidual    = A v - mu v,
compressedResidual = P(A v) - mu v,
projectionLeakage  = A v - P(A v).
```

The first object lives in the full carrier.  The second sees only the
compressed action.  The third is exactly the component lost by compression.
These objects may not be aliased.

## 2. Exact algebraic split

Lean proves the identity

```text
A v - mu v
  = (P(A v) - mu v) + (A v - P(A v)).
```

This is theorem

```text
ambient_residual_eq_compressed_residual_add_leakage.
```

No idempotence, orthogonality, self-adjointness, or finite-dimensional
assumption is required for this additive identity.

If the compressed Ritz equation holds,

```text
P(A v) = mu v,
```

then only the compressed residual vanishes.  Lean derives

```text
ambientResidual = projectionLeakage,
||ambientResidual|| = ||projectionLeakage||.
```

The corresponding theorems are

```text
ambient_residual_eq_leakage_of_compressed_eigen,
ambient_residual_norm_eq_leakage_norm_of_compressed_eigen.
```

Verdict: `GENERIC_AMBIENT_COMPRESSED_RESIDUAL_SPLIT_LEAN`.

## 3. Mandatory anti-tautology falsifier

On `R x R`, take

```text
P(x,y) = (x,0),
A(x,y) = (y,x),
v      = (1,0),
mu     = 0.
```

The map `P` is idempotent and fixes `v`.  Moreover

```text
A v = (0,1),
P(A v) = 0 = mu v.
```

Thus the compressed residual is zero, while

```text
ambientResidual   = (0,1) != 0,
projectionLeakage = (0,1).
```

The executable theorem is

```text
compressed_residual_zero_ambient_residual_nonzero.
```

It rejects the invalid inference

```text
Ritz residual inside PEP is zero  ==>  ambient operator residual is zero.
```

## 4. Exact Route B residual obligation

The generic theorem intentionally leaves the exact instantiation open.  H4a1b
must pin, on one domain-safe carrier:

1. the full self-adjoint Route B operator `A` or a proved form-to-operator
   realization;
2. the exact finite/continuum projection `P`;
3. the normalized trial/Ritz vector `v` in the correct operator domain;
4. the exact Rayleigh/Ritz scalar `mu`;
5. the equality between the project residual namespace and
   `ambientResidual A v mu`;
6. the equality between the computable defect and `projectionLeakage A P v`;
7. the norm/rate estimate later consumed by H4a2.

D0.3 currently locks the finite Weil carrier and quarantines alternative
Schur/prolate pilots, but it does not supply this non-internal residual
crosswalk.  A form compression is not automatically an operator compression.

Residual exact stop:

```text
H4A1_EXACT_AMBIENT_RESIDUAL_CROSSWALK_MISSING
```

## 5. Projection source boundary

Official Mathlib distinguishes a projection into a submodule from its ambient
endomorphism and provides orthogonal-projection/Pythagorean refinements:

- https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra/Projection.html
- https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/InnerProductSpace/Projection/Basic.html

Those APIs can support the exact H4a1b instantiation once its carrier and
submodule are pinned.  Revision 22 does not invent them.

## 6. Honest DAG split

```text
H4a1 AmbientResidualIdentity                       OPEN / AND
|-- H4a1.0 H4a1DecompositionContract              PROVED
|-- H4a1a GenericAmbientCompressedResidualSplit   PROVED / LEAN
|-- H4a1b ExactRouteBAmbientResidualCrosswalk      OPEN / INELIGIBLE
`-- H4a1c H4a1Assembly                            OPEN / INELIGIBLE
```

`H4a1b` depends on `D0` and `H4a1a`.  The generic algebra cannot satisfy its
operator-domain, projection, form/operator, or leakage-rate obligations.

## 7. Lean and route boundary

Proof artifact:

```text
Q3/Proofs/RouteB/AmbientResidualSplit.lean
```

It compiles without `sorry`, `admit`, or `exact?`.  Every printed axiom set is
within the project allowance:

```text
propext, Classical.choice, Quot.sound.
```

Explicit nonclaims:

```text
NO_EXACT_ROUTE_B_OPERATOR_DOMAIN
NO_FORM_TO_OPERATOR_CROSSWALK
NO_EXACT_ROUTE_B_PROJECTION
NO_LEAKAGE_NORM_RATE
NO_H4A1_PARENT_CLOSURE
NO_H4A_PARENT_CLOSURE
NO_H4_PARENT_CLOSURE
NO_BUS_010
NO_RH
```

The canonical ACTIVE leaf remains `D0.7e.5a`, the stop remains
`D0_7E_WPRIME_CONSUMER_MISSING`, Bus 010 is absent, and Route B remains
`CHALLENGER / NOT_RH`.
