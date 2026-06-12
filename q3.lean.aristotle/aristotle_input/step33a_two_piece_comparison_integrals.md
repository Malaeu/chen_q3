# Step33A two-piece comparison-integral assembler

Status: locally proved on 2026-06-01.  Do not submit this request unless a
future regression needs an external proof sketch.

Checked local theorem:

```lean
centeredBSplineArchKernelProfileFinitePart_bounds_of_two_piece_comparison_integrals
```

The local pass also added primary/control finite wrappers and matching
positive-tail-window two-piece comparison-integral wrappers.

## Goal

We are in PSD Step33A.1-A.  The active Lean target is now:

```lean
Step33ASignedChunkedComparisonIntegralPayload
```

The missing backend is a proof-producing chunked comparison-integral layer for
the Arch `A` integrand.  Please formalize the first reusable assembler lemma:
finite-window two-piece comparison integrals.

Target file:

```text
Q3/Proofs/PSD_CenteredCoeffAnalyticABoundsBackend.lean
```

## Exact theorem to prove

Add this theorem near the existing finite-part comparison/pointwise wrappers:

```lean
theorem centeredBSplineArchKernelProfileFinitePart_bounds_of_two_piece_comparison_integrals
    (k : Nat) (ell x T cut finiteLower finiteUpper : Real)
    (lowerLeft upperLeft lowerRight upperRight : Real -> Real)
    (hLeft : -T <= cut)
    (hRight : cut <= T)
    (hLowerLeftInt : IntegrableOn lowerLeft (Set.Icc (-T) cut))
    (hUpperLeftInt : IntegrableOn upperLeft (Set.Icc (-T) cut))
    (hLowerRightInt : IntegrableOn lowerRight (Set.Ioc cut T))
    (hUpperRightInt : IntegrableOn upperRight (Set.Ioc cut T))
    (hLowerLeft : forall t, t ∈ Set.Icc (-T) cut ->
      lowerLeft t <= centeredBSplineArchKernelProfileIntegrand k ell x t)
    (hUpperLeft : forall t, t ∈ Set.Icc (-T) cut ->
      centeredBSplineArchKernelProfileIntegrand k ell x t <= upperLeft t)
    (hLowerRight : forall t, t ∈ Set.Ioc cut T ->
      lowerRight t <= centeredBSplineArchKernelProfileIntegrand k ell x t)
    (hUpperRight : forall t, t ∈ Set.Ioc cut T ->
      centeredBSplineArchKernelProfileIntegrand k ell x t <= upperRight t)
    (hFiniteLower : finiteLower <=
      (∫ t in Set.Icc (-T) cut, lowerLeft t) +
        ∫ t in Set.Ioc cut T, lowerRight t)
    (hFiniteUpper :
      (∫ t in Set.Icc (-T) cut, upperLeft t) +
        ∫ t in Set.Ioc cut T, upperRight t <= finiteUpper) :
    finiteLower <=
      centeredBSplineArchKernelProfileFinitePart k ell x T ∧
    centeredBSplineArchKernelProfileFinitePart k ell x T <= finiteUpper := by
  ...
```

ASCII is intentional: use `->` in the source if that is easier, Lean accepts it.

## Available local lemmas

In the same file there is already:

```lean
theorem centeredBSplineArchKernelProfileFinitePart_bounds_of_comparison_integrals
    (k : Nat) (ell x T finiteLower finiteUpper : Real)
    (lowerF upperF : Real -> Real)
    (hLowerInt : IntegrableOn lowerF (Set.Icc (-T) T))
    (hUpperInt : IntegrableOn upperF (Set.Icc (-T) T))
    (hLower : forall t, t ∈ Set.Icc (-T) T ->
      lowerF t <= centeredBSplineArchKernelProfileIntegrand k ell x t)
    (hUpper : forall t, t ∈ Set.Icc (-T) T ->
      centeredBSplineArchKernelProfileIntegrand k ell x t <= upperF t)
    (hFiniteLower : finiteLower <= ∫ t in Set.Icc (-T) T, lowerF t)
    (hFiniteUpper : ∫ t in Set.Icc (-T) T, upperF t <= finiteUpper) :
    finiteLower <=
      centeredBSplineArchKernelProfileFinitePart k ell x T ∧
    centeredBSplineArchKernelProfileFinitePart k ell x T <= finiteUpper
```

There is also a pointwise two-piece version:

```lean
theorem centeredBSplineArchKernelProfileFinitePart_bounds_of_two_piece_pointwise_bounds
```

Use these if helpful, but do not weaken the target theorem.

## Suggested proof strategy

1. Define combined lower/upper functions:

```lean
let lowerF : Real -> Real := fun t => if t <= cut then lowerLeft t else lowerRight t
let upperF : Real -> Real := fun t => if t <= cut then upperLeft t else upperRight t
```

2. Prove `IntegrableOn lowerF (Set.Icc (-T) T)` and same for upperF from the
two adjacent interval integrability assumptions.

3. Prove pointwise comparison on `Set.Icc (-T) T` by splitting on `t <= cut`.

4. Prove the integral bounds by decomposing `Set.Icc (-T) T` into
`Set.Icc (-T) cut` and `Set.Ioc cut T`.

5. Feed the existing one-piece comparison-integral lemma.

## Policy

- No `sorry`, `admit`, `axiom`, or final `exact?`.
- Prefer explicit measure/integral lemmas over heavy `aesop`.
- If the exact theorem is too hard, return the smallest missing helper lemma
  with a Lean statement and a proof attempt.
- Do not edit `Q3.Main`.
- Do not touch `ARadius`, CSV, radius-floor, or generated global A radii.
