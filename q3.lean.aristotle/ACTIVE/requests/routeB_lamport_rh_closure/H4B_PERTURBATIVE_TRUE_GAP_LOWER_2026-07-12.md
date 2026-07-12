# Route B H4b perturbative true-gap lower — revision 28

Status: `H4B1_PROVED / EXACT_SAME_PARITY_FUCHS_GAP_OPEN / NOT_RH`

Progress class: `PROOF_PROGRESS + REPRESENTATION_PROGRESS + FALSIFICATION_PROGRESS`

This transaction proves only the universal endpoint-perturbation arithmetic
below `H4b SafeGapLower`.  It does not construct the Route B matrix, identify
the true same-parity eigenvalues, prove a Weyl/Hoffman--Wielandt estimate,
derive a Fuchs diagonal, close H4b/H4, create Bus 010, or prove RH.

## 1. Model and true endpoints are distinct

Write

```text
modelLow, modelHigh
trueLow,  trueHigh
```

for two different endpoint pairs.  The model pair may come from a diagonal or
other exactly solvable approximation.  The true pair must be the ordered
same-parity detector eigenvalues used by Contract v2.  They may not be aliased.

Assume one-sided endpoint control

```text
trueLow <= modelLow + errLow,
modelHigh - errHigh <= trueHigh,
```

and a surviving perturbation budget

```text
floor + errLow + errHigh <= modelHigh-modelLow.
```

Lean proves

```text
floor <= trueHigh-trueLow.
```

This is theorem

```text
true_gap_lower_of_endpoint_perturbation_budget.
```

## 2. Absolute perturbation and strict positivity

The symmetric hypotheses

```text
|trueLow-modelLow|   <= errLow,
|trueHigh-modelHigh| <= errHigh
```

imply the required one-sided bounds.  Lean packages this as

```text
true_gap_lower_of_abs_endpoint_perturbations.
```

If additionally `0<floor`, the true gap is strictly positive.  This is

```text
true_gap_pos_of_abs_endpoint_perturbations.
```

On a non-bottom filter, eventual endpoint controls and an eventual surviving
budget give the eventual true-gap lower bound pointwise on the same carrier:

```text
eventually_true_gap_lower_of_abs_endpoint_perturbations.
```

Verdict:

```text
GENERIC_PERTURBATIVE_TRUE_GAP_LOWER_LEAN.
```

## 3. Mandatory model-substitution guards

The executable theorem

```text
positive_model_gap_without_endpoint_control_does_not_force_true_gap
```

uses model endpoints `(0,1)` and collapsed true endpoints `(0,0)`.  The model
gap is positive while the true gap is not.  Therefore a model Fuchs gap alone
can never discharge H4b.

The second guard

```text
endpoint_errors_can_consume_entire_model_gap
```

sets endpoint-error budget equal to the whole model gap.  Both absolute
perturbation estimates hold, but the true gap is zero.  Strict positivity
therefore needs a strictly positive surviving floor.

These guards retain `MODEL_GAP_SUBSTITUTION` and prevent a perturbative theorem
name from being used as if its source hypotheses were already available.

## 4. Exact Route B obligation left open

H4b2 must still provide, on one common cofinal family/filter:

1. the exact parity-clean finite operator and its Gram convention;
2. ordered true endpoints corresponding to the required same-parity
   `mu1` and `mu3`, with multiplicities controlled;
3. a source-locked Fuchs-diagonal or other model pair;
4. absolute perturbation bounds for both selected endpoints, obtained from a
   legitimate operator/Frobenius estimate rather than fitted eigenvalues;
5. an error budget strictly smaller than the model separation;
6. the Contract-v2 lower envelope
   `c_Delta * lambda^r_Delta * exp(-4*pi*lambda^2)` for the surviving floor;
7. a Lean crosswalk showing that the resulting true gap is exactly the H0/H4
   detector gap and not a pilot/model gap.

The exact stop is

```text
H4B_EXACT_SAME_PARITY_FUCHS_GAP_INSTANTIATION_MISSING.
```

`SAFE_GAP_LOWER_NO_SOURCE`, `TRUE_GAP_LOWER_MISSING`,
`GROUND_SECTOR_MISMATCH`, and `MODEL_GAP_SUBSTITUTION` remain live.

## 5. Honest DAG split

```text
H4b SafeGapLower                                  OPEN / AND
|-- H4b.0 H4bDecompositionContract               PROVED
|-- H4b1 GenericPerturbativeTrueGapLower          PROVED / LEAN / GUARDS_LIVE
|-- H4b2 ExactSameParityFuchsGapInstantiation     OPEN / INELIGIBLE
`-- H4b3 H4bAssembly                              OPEN / INELIGIBLE
```

The generic theorem is a receiver for a future matrix perturbation theorem; it
does not certify that the exact Route B matrices meet its hypotheses.

## 6. Source boundary

Contract v2 names perturbation against a polynomially separated Fuchs
diagonal as the candidate H4b mechanism.  The local manuscript records the
Hoffman--Wielandt/Ky Fan Frobenius drift guard in
`full/sections/A3/matrix_guard.tex`, but that is not an exact Route B
same-parity instantiation.

Official Mathlib APIs inspected:

- https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Matrix/Spectrum.html
- https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra/Matrix/Gershgorin.html

They provide ordered Hermitian eigenvalues and Gershgorin localization.  They
do not select the Route B operator/family or prove the two required endpoint
drift bounds.

## 7. Lean and route boundary

Proof artifact:

```text
Q3/Proofs/RouteB/PerturbativeTrueGapLower.lean
```

It compiles without `sorry`, `admit`, or `exact?`; every printed axiom set is
within the project allowance:

```text
propext, Classical.choice, Quot.sound.
```

Explicit nonclaims:

```text
NO_EXACT_ROUTE_B_OPERATOR
NO_EXACT_SAME_PARITY_EIGENVALUE_SELECTION
NO_WEYL_OR_HOFFMAN_WIELANDT_SOURCE_INSTANTIATION
NO_FUCHS_DIAGONAL_SEPARATION_PROOF
NO_TRUE_GAP_RATE
NO_H4B_PARENT_CLOSURE
NO_H4_PARENT_CLOSURE
NO_BUS_010
NO_RH
```

The canonical ACTIVE leaf remains `D0.7e.5a`, the stop remains
`D0_7E_WPRIME_CONSUMER_MISSING`, Bus 010 is absent, and Route B remains
`CHALLENGER / NOT_RH`.
